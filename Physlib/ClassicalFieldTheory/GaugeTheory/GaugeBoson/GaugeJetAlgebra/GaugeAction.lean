/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.GaugeJetAlgebra.JetDeriv
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.AdjointCoeff
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.MaurerCartan
public import Physlib.Relativity.IsLorentzDeriv
public import Physlib.Mathematics.MultisetAntidiagonal

/-!
# The gauge action on the gauge-boson jet algebra

## i. Overview

A jet of gauge transformations `U` acts on the gauge field by
`A_μ ↦ Ad_U A_μ + maurerCartan(U)_μ`, so on a component function `∂_s A_μ^φ` it acts affinely: the
linear part is the all-orders Leibniz convolution of the Taylor coefficients of `Ad(U⁻¹)`
against lower component functions, and the constant part is the Taylor coefficient of the
Maurer–Cartan form of `U⁻¹`. The action extends to the whole jet algebra as the
substitution homomorphism determined by this affine action on the generators.

The linear part is built from the adjoint Taylor coefficients `LocalGaugeData.adjointCoeff` of
the package, whose multiplicativity up to convolution is the Taylor–Leibniz theorem
`LocalGaugeData.evalLie_iteratedDeriv_adjoint`; it makes the transport multiplicative and
gives the cocycle identity for the Maurer–Cartan shift.

## ii. Key results

- `GaugeBoson.adjointTransport` : the adjoint Taylor coefficients on the target space.
- `GaugeJetAlgebra.transport` : the linear part of the gauge action on the component
  space.
- `GaugeJetAlgebra.mcShift` : the Maurer–Cartan shift.
- `GaugeJetAlgebra.repJet` : the action of the jet gauge group on the jet algebra.
- `GaugeJetAlgebra.repJet_iteratedJetDeriv_ofA` : the transformation law of the derivative
  generators, in the form used by `GaugeAlgebraRealization`.
- `GaugeJetAlgebra.complexRepJet` : the action on the complexified jet algebra.

## iii. Table of contents

- A. The transport on the component space
- B. The Maurer–Cartan shift
- C. The action of the jet gauge group
  - C.1. The transformation law of the generators
  - C.2. The complexified action

-/

@[expose] public section

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
variable {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
variable {jets : LocalGaugeData G 𝔤 G₀ 𝔤J}

set_option maxHeartbeats 1000000


open TensorProduct MvPowerSeries

/-!

## A. The transport on the component space

-/

namespace GaugeBoson

variable (jets) in
/-- The adjoint transport on the gauge-boson target space at `p` derivatives: the adjoint
  Taylor coefficient on the gauge-algebra factor, the identity on the spacetime index. -/
noncomputable def adjointTransport (U : G) (p : Multiset (Fin 1 ⊕ Fin 3)) :
    (GaugeBoson 𝔤) →ₗ[ℝ] (GaugeBoson 𝔤) :=
  (valLinEquiv 𝔤).symm.toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (jets.adjointCoeff U p) ∘ₗ
    (valLinEquiv 𝔤).toLinearMap

lemma adjointTransport_mk_tmul (U : G) (p : Multiset (Fin 1 ⊕ Fin 3))
    (v : Lorentz.CoVector) (a : 𝔤) :
    adjointTransport jets U p ⟨v ⊗ₜ[ℝ] a⟩ = ⟨v ⊗ₜ[ℝ] jets.adjointCoeff U p a⟩ := rfl

/-- The adjoint transport at the identity: only the base point survives. -/
lemma adjointTransport_one (p : Multiset (Fin 1 ⊕ Fin 3)) :
    adjointTransport jets 1 p = if p = 0 then LinearMap.id else 0 := by
  rw [adjointTransport, jets.adjointCoeff_one]
  rcases eq_or_ne p 0 with rfl | hp
  · rw [if_pos rfl, if_pos rfl, TensorProduct.map_id]
    refine LinearMap.ext fun v => ?_
    simp
  · rw [if_neg hp, if_neg hp]
    refine LinearMap.ext fun v => ?_
    rw [show TensorProduct.map (LinearMap.id (M := Lorentz.CoVector))
        (0 : 𝔤 →ₗ[ℝ] 𝔤) = 0 from by
      refine TensorProduct.ext' fun x a => ?_
      rw [TensorProduct.map_tmul, LinearMap.zero_apply, TensorProduct.tmul_zero]
      rfl]
    simp

/-- The adjoint transport of a product: the antidiagonal convolution of transports. -/
lemma adjointTransport_mul (U V : G) (p : Multiset (Fin 1 ⊕ Fin 3)) :
    adjointTransport jets (U * V) p
      = (p.antidiagonal.map fun r =>
          adjointTransport jets U r.1 ∘ₗ adjointTransport jets V r.2).sum := by
  refine LinearMap.ext fun v => ?_
  rw [Multiset.sum_linearMap_apply, Multiset.map_map]
  obtain ⟨m⟩ := v
  induction m using TensorProduct.induction_on with
  | zero =>
    rw [show (⟨0⟩ : (GaugeBoson 𝔤)) = 0 from rfl, map_zero]
    refine (Multiset.sum_eq_zero fun x hx => ?_).symm
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
    simp
  | tmul x a =>
    apply (valLinEquiv 𝔤).injective
    rw [adjointTransport_mk_tmul, map_multiset_sum, Multiset.map_map, valLinEquiv_apply,
      show ((⟨x ⊗ₜ[ℝ] jets.adjointCoeff (U * V) p a⟩ : (GaugeBoson 𝔤))).val
        = x ⊗ₜ[ℝ] jets.adjointCoeff (U * V) p a from rfl,
      jets.adjointCoeff_mul, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.tmul_sum, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply, LinearMap.comp_apply, adjointTransport_mk_tmul,
      valLinEquiv_apply]
  | add m₁ m₂ h₁ h₂ =>
    rw [show (⟨m₁ + m₂⟩ : (GaugeBoson 𝔤)) = (⟨m₁⟩ : (GaugeBoson 𝔤)) + ⟨m₂⟩ from rfl, map_add, h₁,
      h₂, ← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply]
    exact (map_add _ _ _).symm

/-- The dual transport carries a component covector to the component covector of the
  transported adjoint index: the spacetime slot is untouched. -/
lemma dualMap_adjointTransport_componentDual (U : G)
    (p : Multiset (Fin 1 ⊕ Fin 3)) (ω : Module.Dual ℝ Lorentz.CoVector)
    (φ : Module.Dual ℝ 𝔤) :
    (adjointTransport jets U p).dualMap ((componentDual 𝔤) ω φ)
      = (componentDual 𝔤) ω (φ ∘ₗ jets.adjointCoeff U p) := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨m⟩ := v
  induction m using TensorProduct.induction_on with
  | zero =>
    rw [show (⟨0⟩ : (GaugeBoson 𝔤)) = 0 from rfl, map_zero, map_zero]
  | tmul x a =>
    rw [LinearMap.dualMap_apply, adjointTransport_mk_tmul,
      componentDual_apply_val_tmul, componentDual_apply_val_tmul]
    rfl
  | add m₁ m₂ h₁ h₂ =>
    rw [show (⟨m₁ + m₂⟩ : (GaugeBoson 𝔤)) = (⟨m₁⟩ : (GaugeBoson 𝔤)) + ⟨m₂⟩ from rfl, map_add,
      map_add, h₁, h₂]

end GaugeBoson

namespace GaugeJetAlgebra

variable (jets) in
/-- The value of the transport on the derivative symbol at `s`: the all-orders Leibniz
  convolution of the dual adjoint transports against lower derivative symbols. -/
noncomputable def transportFun (U : G) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℝ (GaugeBoson 𝔤) →ₗ[ℝ] (GaugeBoson.JetComponentSpace 𝔤) :=
  (s.antidiagonal.map fun p =>
    (TensorProduct.mk ℝ DerivAlgebraReal (Module.Dual ℝ (GaugeBoson 𝔤))
        (DerivAlgebraReal.basisMultiset p.2)).comp
      ((GaugeBoson.adjointTransport jets U p.1).dualMap)).sum

variable (jets) in
/-- The linear part of the gauge action on the jet component space: on a component
  function `∂_s A^ψ` it is the all-orders Leibniz convolution of the Taylor coefficients
  of the adjoint action of `U` against the lower component functions. -/
noncomputable def transport (U : G) :
    (GaugeBoson.JetComponentSpace 𝔤) →ₗ[ℝ] (GaugeBoson.JetComponentSpace 𝔤) :=
  TensorProduct.lift (DerivAlgebraReal.basisMultiset.constr ℝ (transportFun jets U))

lemma transport_basis_tmul (U : G) (s : Multiset (Fin 1 ⊕ Fin 3))
    (ψ : Module.Dual ℝ (GaugeBoson 𝔤)) :
    transport jets U (DerivAlgebraReal.basisMultiset s ⊗ₜ[ℝ] ψ)
      = (s.antidiagonal.map fun p =>
          DerivAlgebraReal.basisMultiset p.2 ⊗ₜ[ℝ]
            (GaugeBoson.adjointTransport jets U p.1).dualMap ψ).sum := by
  rw [transport, TensorProduct.lift.tmul, Module.Basis.constr_basis, transportFun,
    Multiset.sum_linearMap_apply, Multiset.map_map]
  rfl

/-- Two maps out of the jet component space agree if they agree on the components
  `∂_s A^ψ` with `s` a derivative multiset and `ψ` an arbitrary covector. -/
lemma _root_.GaugeBoson.JetComponentSpace.ext_of_basis
    {M : Type*} [AddCommMonoid M] [Module ℝ M]
    {F G : (GaugeBoson.JetComponentSpace 𝔤) →ₗ[ℝ] M}
    (h : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℝ (GaugeBoson 𝔤)),
      F (DerivAlgebraReal.basisMultiset s ⊗ₜ[ℝ] ψ)
        = G (DerivAlgebraReal.basisMultiset s ⊗ₜ[ℝ] ψ)) : F = G := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul a ψ =>
    have ha : a ∈ Submodule.span ℝ
        (Set.range DerivAlgebraReal.basisMultiset) := by
      rw [DerivAlgebraReal.basisMultiset.span_eq]; trivial
    induction ha using Submodule.span_induction with
    | mem b hb => obtain ⟨s, rfl⟩ := hb; exact h s ψ
    | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero]
    | add b c _ _ hb hc => rw [TensorProduct.add_tmul, map_add, map_add, hb, hc]
    | smul c b _ hb => rw [← TensorProduct.smul_tmul', map_smul, map_smul, hb]

/-- The transport of the identity is the identity. -/
lemma transport_one : transport jets (1 : G) = LinearMap.id := by
  refine GaugeBoson.JetComponentSpace.ext_of_basis fun s ψ => ?_
  rw [transport_basis_tmul,
    Multiset.map_congr rfl (fun p hp => by rw [GaugeBoson.adjointTransport_one]),
    Multiset.sum_antidiagonal_eq_of_fst_ne_zero s
      (fun p => DerivAlgebraReal.basisMultiset p.2 ⊗ₜ[ℝ]
        ((if p.1 = 0 then LinearMap.id else 0) :
          (GaugeBoson 𝔤) →ₗ[ℝ] (GaugeBoson 𝔤)).dualMap ψ)
      (fun p _ hp => by
        rw [if_neg hp, show ((0 : (GaugeBoson 𝔤) →ₗ[ℝ] (GaugeBoson 𝔤))).dualMap ψ = 0 from
            LinearMap.ext fun v => by simp, TensorProduct.tmul_zero]),
    if_pos rfl, LinearMap.id_apply,
    show (LinearMap.id : (GaugeBoson 𝔤) →ₗ[ℝ] (GaugeBoson 𝔤)).dualMap ψ = ψ from
      LinearMap.ext fun v => rfl]

/-- The transport is an anti-homomorphism: the transport of a product is the reverse
  composite. Composed with the inverse, it becomes the linear part of the gauge
  representation. -/
lemma transport_mul (U V : G) :
    transport jets (U * V) = transport jets V ∘ₗ transport jets U := by
  refine GaugeBoson.JetComponentSpace.ext_of_basis fun s ψ => ?_
  have hdual : ∀ (p : Multiset (Fin 1 ⊕ Fin 3) × Multiset (Fin 1 ⊕ Fin 3)),
      (GaugeBoson.adjointTransport jets (U * V) p.1).dualMap ψ
        = (p.1.antidiagonal.map fun r =>
            (GaugeBoson.adjointTransport jets V r.2).dualMap
              ((GaugeBoson.adjointTransport jets U r.1).dualMap ψ)).sum := by
    intro p
    rw [GaugeBoson.adjointTransport_mul]
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.dualMap_apply, Multiset.sum_linearMap_apply, Multiset.map_map,
      map_multiset_sum, Multiset.map_map, Multiset.sum_linearMap_apply, Multiset.map_map]
    rfl
  have hLHS : transport jets (U * V) (DerivAlgebraReal.basisMultiset s ⊗ₜ[ℝ] ψ)
      = (s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            DerivAlgebraReal.basisMultiset p.2 ⊗ₜ[ℝ]
              (GaugeBoson.adjointTransport jets V q.2).dualMap
                ((GaugeBoson.adjointTransport jets U q.1).dualMap ψ)).sum).sum := by
    rw [transport_basis_tmul]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [hdual p, Multiset.tmul_sum, Multiset.map_map]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => rfl)
  have hRHS : (transport jets V ∘ₗ transport jets U)
        (DerivAlgebraReal.basisMultiset s ⊗ₜ[ℝ] ψ)
      = (s.antidiagonal.map fun p =>
          (p.2.antidiagonal.map fun q =>
            DerivAlgebraReal.basisMultiset q.2 ⊗ₜ[ℝ]
              (GaugeBoson.adjointTransport jets V q.1).dualMap
                ((GaugeBoson.adjointTransport jets U p.1).dualMap ψ)).sum).sum := by
    rw [LinearMap.comp_apply, transport_basis_tmul, map_multiset_sum, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    exact transport_basis_tmul V p.2 _
  rw [hLHS, hRHS]
  exact Multiset.sum_antidiagonal_assoc s fun a b c =>
    DerivAlgebraReal.basisMultiset c ⊗ₜ[ℝ]
      (GaugeBoson.adjointTransport jets V b).dualMap
        ((GaugeBoson.adjointTransport jets U a).dualMap ψ)

end GaugeJetAlgebra

/-!

## B. The Maurer–Cartan shift

-/

namespace GaugeJetAlgebra

variable (jets) in
/-- The Taylor coefficient of the Maurer–Cartan form of `U` at the derivative multiset
  `s`, packaged as a gauge boson: the spacetime index runs over the coordinate
  directions, the adjoint index over the base-point Taylor coefficients of the
  Maurer–Cartan form. -/
noncomputable def mcBosonCoeff (U : G) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    (GaugeBoson 𝔤) :=
  ⟨∑ μ, Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
    jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan U μ))⟩

@[simp]
lemma mcBosonCoeff_one (s : Multiset (Fin 1 ⊕ Fin 3)) : mcBosonCoeff jets 1 s = 0 := by
  rw [show (0 : (GaugeBoson 𝔤)) = ⟨0⟩ from rfl, mcBosonCoeff]
  congr 1
  refine Finset.sum_eq_zero fun μ _ => ?_
  rw [show jets.maurerCartan 1 μ = 0 from jets.maurerCartan_one μ, map_zero,
    map_zero, TensorProduct.tmul_zero]

/-- The Maurer–Cartan Taylor coefficients of a product: the cocycle identity, with the
  adjoint transport convoluted in by the Taylor–Leibniz theorem. -/
lemma mcBosonCoeff_mul (U V : G) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    mcBosonCoeff jets (U * V) s
      = mcBosonCoeff jets U s
        + (s.antidiagonal.map fun p =>
            GaugeBoson.adjointTransport jets U p.1 (mcBosonCoeff jets V p.2)).sum := by
  apply (GaugeBoson.valLinEquiv 𝔤).injective
  have hE : ∀ (W : G) (t : Multiset (Fin 1 ⊕ Fin 3)),
      (GaugeBoson.valLinEquiv 𝔤) (mcBosonCoeff jets W t)
        = ∑ μ, Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
            jets.evalLie (jets.iteratedDeriv t
              (jets.maurerCartan W μ)) := fun W t => rfl
  have hB : ∀ p q : Multiset (Fin 1 ⊕ Fin 3),
      (GaugeBoson.valLinEquiv 𝔤) (GaugeBoson.adjointTransport jets U p (mcBosonCoeff jets V q))
        = ∑ μ, Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
            jets.adjointCoeff U p (jets.evalLie
              (jets.iteratedDeriv q (jets.maurerCartan V μ))) := by
    intro p q
    rw [show (GaugeBoson.valLinEquiv 𝔤) (GaugeBoson.adjointTransport jets U p
      (mcBosonCoeff jets V q))
        = TensorProduct.map LinearMap.id (jets.adjointCoeff U p)
            ((GaugeBoson.valLinEquiv 𝔤) (mcBosonCoeff jets V q)) from by
        rw [GaugeBoson.adjointTransport]
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          LinearEquiv.apply_symm_apply],
      hE, map_sum]
    exact Finset.sum_congr rfl fun μ _ => by
      rw [TensorProduct.map_tmul, LinearMap.id_apply]
  have hA : (GaugeBoson.valLinEquiv 𝔤) (mcBosonCoeff jets (U * V) s)
      = ∑ μ, (Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
          jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan U μ))
        + (s.antidiagonal.map fun p =>
            Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
              jets.adjointCoeff U p.1 (jets.evalLie
                (jets.iteratedDeriv p.2 (jets.maurerCartan V μ)))).sum) := by
    rw [hE]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [show jets.maurerCartan (U * V) μ
        = jets.maurerCartan U μ + jets.adjoint U (jets.maurerCartan V μ) from
        jets.maurerCartan_cocycle U V μ,
      map_add, map_add,
      show jets.adjoint U (jets.maurerCartan V μ)
        = jets.adjoint U (jets.maurerCartan V μ) from rfl,
      jets.evalLie_iteratedDeriv_adjoint, TensorProduct.tmul_add,
      Multiset.tmul_sum, Multiset.map_map]
    exact congrArg (fun z => _ + z)
      (congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => rfl))
  rw [hA, Finset.sum_add_distrib, map_add, map_multiset_sum, Multiset.map_map, ← hE,
    ← Multiset.sum_map_finsetSum]
  congr 1

variable (jets) in
/-- The Maurer–Cartan shift: the linear functional on the component space pairing a
  component `∂_s A^ψ` with the Taylor coefficient of the Maurer–Cartan form of `U`. It is
  the constant part of the affine gauge action. -/
noncomputable def mcShift (U : G) : (GaugeBoson.JetComponentSpace 𝔤) →ₗ[ℝ] ℝ :=
  TensorProduct.lift (DerivAlgebraReal.basisMultiset.constr ℝ fun s =>
    Module.Dual.eval ℝ (GaugeBoson 𝔤) (mcBosonCoeff jets U s))

lemma mcShift_basis_tmul (U : G) (s : Multiset (Fin 1 ⊕ Fin 3))
    (ψ : Module.Dual ℝ (GaugeBoson 𝔤)) :
    mcShift jets U (DerivAlgebraReal.basisMultiset s ⊗ₜ[ℝ] ψ)
      = ψ (mcBosonCoeff jets U s) := by
  rw [mcShift, TensorProduct.lift.tmul, Module.Basis.constr_basis]
  rfl

@[simp]
lemma mcShift_one : mcShift jets (1 : G) = 0 := by
  refine GaugeBoson.JetComponentSpace.ext_of_basis fun s ψ => ?_
  rw [mcShift_basis_tmul, mcBosonCoeff_one, map_zero, LinearMap.zero_apply]

/-- The cocycle identity for the Maurer–Cartan shift. -/
lemma mcShift_mul (U V : G) :
    mcShift jets (U * V) = mcShift jets V ∘ₗ transport jets U + mcShift jets U := by
  refine GaugeBoson.JetComponentSpace.ext_of_basis fun s ψ => ?_
  rw [LinearMap.add_apply, LinearMap.comp_apply, mcShift_basis_tmul, mcBosonCoeff_mul,
    map_add, add_comm]
  congr 1
  · rw [map_multiset_sum, Multiset.map_map, transport_basis_tmul, map_multiset_sum,
      Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [Function.comp_apply, Function.comp_apply, mcShift_basis_tmul]
    rfl
  · exact (mcShift_basis_tmul U s ψ).symm

/-!

## C. The action of the jet gauge group

-/

variable (jets) in
/-- The affine action of a jet of gauge transformations on the generators of the jet
  algebra: the transported component plus the Maurer–Cartan shift, both of `U⁻¹` — the
  contragredient convention for an action on component functions. -/
noncomputable def gaugeGen (U : G) :
    (GaugeBoson.JetComponentSpace 𝔤) →ₗ[ℝ] (GaugeJetAlgebra 𝔤) :=
  (SymmetricAlgebra.ι ℝ (GaugeBoson.JetComponentSpace 𝔤)).comp (transport jets U⁻¹)
    + (Algebra.linearMap ℝ (GaugeJetAlgebra 𝔤)).comp (mcShift jets U⁻¹)

lemma gaugeGen_apply (U : G) (x : (GaugeBoson.JetComponentSpace 𝔤)) :
    gaugeGen jets U x = SymmetricAlgebra.ι ℝ _ (transport jets U⁻¹ x)
      + algebraMap ℝ (GaugeJetAlgebra 𝔤) (mcShift jets U⁻¹ x) := rfl

variable (jets) in
/-- The action of the jet gauge group on the gauge-boson jet algebra: the substitution
  homomorphism determined by the affine action on the generators, `∂_s A^ψ` going to its
  transported convolution plus the Maurer–Cartan shift of `U⁻¹`. -/
noncomputable def repJet : Representation ℝ G (GaugeJetAlgebra 𝔤) where
  toFun U := (SymmetricAlgebra.lift (gaugeGen jets U)).toLinearMap
  map_one' := by
    suffices h : SymmetricAlgebra.lift (gaugeGen jets 1) = AlgHom.id ℝ (GaugeJetAlgebra 𝔤) by
      rw [h]; rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    show SymmetricAlgebra.lift (gaugeGen jets 1) (SymmetricAlgebra.ι ℝ _ x)
      = AlgHom.id ℝ (GaugeJetAlgebra 𝔤) (SymmetricAlgebra.ι ℝ _ x)
    rw [SymmetricAlgebra.lift_ι_apply, gaugeGen_apply, inv_one, transport_one,
      mcShift_one, LinearMap.id_apply, LinearMap.zero_apply, map_zero, add_zero]
    rfl
  map_mul' U V := by
    suffices h : SymmetricAlgebra.lift (gaugeGen jets (U * V))
        = (SymmetricAlgebra.lift (gaugeGen jets U)).comp (SymmetricAlgebra.lift
          (gaugeGen jets V)) by
      rw [h]; rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    show SymmetricAlgebra.lift (gaugeGen jets (U * V)) (SymmetricAlgebra.ι ℝ _ x)
      = ((SymmetricAlgebra.lift (gaugeGen jets U)).comp (SymmetricAlgebra.lift (gaugeGen jets V)))
          (SymmetricAlgebra.ι ℝ _ x)
    rw [SymmetricAlgebra.lift_ι_apply, gaugeGen_apply, AlgHom.comp_apply,
      SymmetricAlgebra.lift_ι_apply, gaugeGen_apply, map_add,
      SymmetricAlgebra.lift_ι_apply, gaugeGen_apply, AlgHom.commutes,
      mul_inv_rev, transport_mul, mcShift_mul, LinearMap.comp_apply,
      LinearMap.add_apply, LinearMap.comp_apply, map_add, add_assoc]

variable (jets) in
/-- The action of `U` as an algebra homomorphism: a jet of gauge transformations acts on
  a Lagrangian term factor by factor. -/
noncomputable def repJetAlgHom (U : G) :
    (GaugeJetAlgebra 𝔤) →ₐ[ℝ] (GaugeJetAlgebra 𝔤) :=
  SymmetricAlgebra.lift (gaugeGen jets U)

@[simp]
lemma repJet_ι (U : G) (x : (GaugeBoson.JetComponentSpace 𝔤)) :
    repJet jets U (SymmetricAlgebra.ι ℝ _ x)
      = SymmetricAlgebra.ι ℝ _ (transport jets U⁻¹ x)
        + algebraMap ℝ (GaugeJetAlgebra 𝔤) (mcShift jets U⁻¹ x) := by
  rw [show repJet jets U (SymmetricAlgebra.ι ℝ _ x)
      = SymmetricAlgebra.lift (gaugeGen jets U) (SymmetricAlgebra.ι ℝ _ x) from rfl,
    SymmetricAlgebra.lift_ι_apply, gaugeGen_apply]

@[simp]
lemma repJet_apply_one (U : G) :
    repJet jets U (1 : (GaugeJetAlgebra 𝔤)) = 1 := by
  rw [show repJet jets U (1 : (GaugeJetAlgebra 𝔤))
    = SymmetricAlgebra.lift (gaugeGen jets U) 1 from rfl, map_one]

lemma repJet_apply_mul (U : G) (x y : (GaugeJetAlgebra 𝔤)) :
    repJet jets U (x * y) = repJet jets U x * repJet jets U y := by
  rw [show repJet jets U (x * y)
    = SymmetricAlgebra.lift (gaugeGen jets U) (x * y) from rfl, map_mul]
  rfl

@[simp]
lemma repJet_algebraMap (U : G) (r : ℝ) :
    repJet jets U (algebraMap ℝ (GaugeJetAlgebra 𝔤) r)
      = algebraMap ℝ (GaugeJetAlgebra 𝔤) r := by
  rw [show repJet jets U (algebraMap ℝ (GaugeJetAlgebra 𝔤) r)
    = SymmetricAlgebra.lift (gaugeGen jets U) (algebraMap ℝ (GaugeJetAlgebra 𝔤) r) from rfl,
    AlgHom.commutes]

/-!

### C.1. The transformation law of the generators

-/

/-- The component covector at `μ` picks the `μ`-th Maurer–Cartan Taylor coefficient out
  of the shift. -/
lemma componentDual_dualBasis_mcBosonCoeff (W : G)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    (GaugeBoson.componentDual 𝔤) (Lorentz.CoVector.basis.dualBasis μ) φ (mcBosonCoeff jets W s)
      = φ (jets.evalLie (jets.iteratedDeriv s
          (jets.maurerCartan W μ))) := by
  have hsum : mcBosonCoeff jets W s
      = ∑ ν, (⟨Lorentz.CoVector.basis ν ⊗ₜ[ℝ]
          jets.evalLie (jets.iteratedDeriv s
            (jets.maurerCartan W ν))⟩ : (GaugeBoson 𝔤)) := by
    apply (GaugeBoson.valLinEquiv 𝔤).injective
    rw [map_sum]
    rfl
  rw [hsum, map_sum]
  rw [Finset.sum_congr rfl fun ν _ => GaugeBoson.componentDual_apply_val_tmul _ _ _ _]
  rw [Finset.sum_congr rfl fun ν _ => by
    rw [Module.Basis.dualBasis_apply_self, ite_mul, one_mul, zero_mul]]
  rw [Finset.sum_ite_eq' Finset.univ μ
    (fun ν => φ (jets.evalLie (jets.iteratedDeriv s
      (jets.maurerCartan W ν)))), if_pos (Finset.mem_univ μ)]

/-- The transformation law of the derivative generators, in the form used by
  `GaugeAlgebraRealization`: a jet of gauge transformations acts on `∂_s A_μ^φ` by the all-orders
  Leibniz convolution of the adjoint Taylor coefficients of `U⁻¹` against lower
  generators, plus the Taylor coefficient of the Maurer–Cartan form of `U⁻¹`. -/
theorem repJet_iteratedJetDeriv_ofA (U : G)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    repJet jets U ((iteratedJetDeriv 𝔤) s ((ofA 𝔤) μ φ))
      = (s.antidiagonal.map fun p =>
          (iteratedJetDeriv 𝔤) p.2 ((ofA 𝔤) μ (jets.adjointDualCoeff U⁻¹ p.1 φ))).sum
        + algebraMap ℝ (GaugeJetAlgebra 𝔤)
            (φ (jets.evalLie (jets.iteratedDeriv s
              (jets.maurerCartan U⁻¹ μ)))) := by
  rw [iteratedJetDeriv_ofA, repJet_ι, transport_basis_tmul, mcShift_basis_tmul,
    componentDual_dualBasis_mcBosonCoeff, map_multiset_sum, Multiset.map_map]
  congr 1
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
  rw [Function.comp_apply, GaugeBoson.dualMap_adjointTransport_componentDual,
    iteratedJetDeriv_ofA]
  rfl

/-!

### C.2. The complexified action

-/

variable (jets) in
/-- The action of the jet gauge group on the complexified gauge-boson jet algebra, by
  base change. -/
noncomputable def complexRepJet :
    Representation ℂ G (ℂ ⊗[ℝ] (GaugeJetAlgebra 𝔤)) where
  toFun U := LinearMap.baseChange ℂ (repJet jets U)
  map_one' := by
    rw [map_one, Module.End.one_eq_id, LinearMap.baseChange_id, Module.End.one_eq_id]
  map_mul' U V := by
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp, Module.End.mul_eq_comp]

@[simp]
lemma complexRepJet_tmul (U : G) (z : ℂ) (x : (GaugeJetAlgebra 𝔤)) :
    complexRepJet jets U (z ⊗ₜ[ℝ] x) = z ⊗ₜ[ℝ] repJet jets U x := rfl

lemma complexRepJet_apply_mul (U : G)
    (x y : ℂ ⊗[ℝ] (GaugeJetAlgebra 𝔤)) :
    complexRepJet jets U (x * y)
      = complexRepJet jets U x * complexRepJet jets U y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, add_mul]
  | tmul z₁ a₁ =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, mul_add]
    | tmul z₂ a₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, complexRepJet_tmul,
        complexRepJet_tmul, complexRepJet_tmul,
        repJet_apply_mul, Algebra.TensorProduct.tmul_mul_tmul]

/-- The iterated complexified derivative of a real element is the complexification of the
  iterated real derivative. -/
lemma iteratedD_complexJetDeriv_one_tmul (s : Multiset (Fin 1 ⊕ Fin 3))
    (x : (GaugeJetAlgebra 𝔤)) :
    Lorentz.iteratedD (complexJetDeriv 𝔤) complexJetDeriv_comm s ((1 : ℂ) ⊗ₜ[ℝ] x)
      = (1 : ℂ) ⊗ₜ[ℝ] (iteratedJetDeriv 𝔤) s x := by
  induction s using Multiset.induction_on generalizing x with
  | empty => rw [Lorentz.iteratedD_zero, iteratedJetDeriv_zero]; rfl
  | cons μ s ih =>
    rw [Lorentz.iteratedD_cons, LinearMap.comp_apply, ih, complexJetDeriv_tmul,
      iteratedJetDeriv_cons, LinearMap.comp_apply]

/-- A real scalar in the complexified jet algebra is the corresponding complex scalar. -/
lemma one_tmul_algebraMap (r : ℝ) :
    (1 : ℂ) ⊗ₜ[ℝ] (algebraMap ℝ (GaugeJetAlgebra 𝔤) r)
      = algebraMap ℂ (ℂ ⊗[ℝ] (GaugeJetAlgebra 𝔤)) ((r : ℝ) : ℂ) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    Algebra.algebraMap_eq_smul_one,
    show ((r : ℝ) • ((1 : ℂ) ⊗ₜ[ℝ] (1 : (GaugeJetAlgebra 𝔤))))
      = (((r : ℝ) : ℂ)) • ((1 : ℂ) ⊗ₜ[ℝ] (1 : (GaugeJetAlgebra 𝔤))) from
      (algebraMap_smul ℂ r _).symm, Algebra.TensorProduct.one_def]

/-- The transformation law of the derivative generators on the complexification: the
  form consumed by the laws of a `GaugeAlgebraRealization`. -/
theorem complexRepJet_iteratedD_one_tmul_ofA (U : G)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    complexRepJet jets U (Lorentz.iteratedD (complexJetDeriv 𝔤) complexJetDeriv_comm s
        ((1 : ℂ) ⊗ₜ[ℝ] (ofA 𝔤) μ φ))
      = (s.antidiagonal.map fun p =>
          Lorentz.iteratedD (complexJetDeriv 𝔤) complexJetDeriv_comm p.2
            ((1 : ℂ) ⊗ₜ[ℝ] (ofA 𝔤) μ (jets.adjointDualCoeff U⁻¹ p.1 φ))).sum
        + algebraMap ℂ (ℂ ⊗[ℝ] (GaugeJetAlgebra 𝔤))
            (((φ (jets.evalLie (jets.iteratedDeriv s
              (jets.maurerCartan U⁻¹ μ))) : ℝ)) : ℂ) := by
  rw [iteratedD_complexJetDeriv_one_tmul, complexRepJet_tmul,
    repJet_iteratedJetDeriv_ofA, TensorProduct.tmul_add, Multiset.tmul_sum,
    Multiset.map_map, one_tmul_algebraMap]
  congr 1
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => by
    rw [Function.comp_apply, iteratedD_complexJetDeriv_one_tmul])

end GaugeJetAlgebra

