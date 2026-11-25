/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.JetDeriv
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.AdjointCoeff
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SymmetrizedMaurerCartan
public import PhyslibAlpha.Relativity.IsLorentzDeriv

/-!
# The gauge action on the gauge-boson jet algebra

The affine action of the gauge jets on the gauge field, extended to its jet algebra.

## i. Overview

A jet of gauge transformations `U` acts on the gauge field by
`A_μ ↦ Ad_U A_μ + maurerCartan(U)_μ`, so on a component function `∂_s A_μ^φ` it acts affinely.
The linear part is the all-orders Leibniz convolution of the Taylor coefficients of `Ad(U⁻¹)`
against lower component functions, and the constant part is the Taylor coefficient of the
Maurer–Cartan form of `U⁻¹`. The action extends to the whole jet algebra as the
substitution homomorphism determined by this affine action on the generators.

The linear part is built from the adjoint Taylor coefficients `GlobalGaugeGroup.adjointCoeff` of
the gauge group, whose multiplicativity up to convolution is the Taylor–Leibniz theorem
`GlobalGaugeGroup.evalLie_iteratedDerivJ_adjointJ`. It makes the transport
multiplicative and gives the cocycle identity for the Maurer–Cartan shift.

## ii. Key results

- `GaugeBoson.adjointTransport` : the adjoint Taylor coefficients on the target space.
- `LocalGaugeFieldAlgebra.transport` : the linear part of the gauge action on the component
  space.
- `LocalGaugeFieldAlgebra.maurerCartanShift` : the Maurer–Cartan shift.
- `LocalGaugeFieldAlgebra.repJet` : the action of the jet gauge group on the jet algebra.
- `LocalGaugeFieldAlgebra.repJet_iteratedJetDeriv_ofA` : the transformation law of the derivative
  generators.
- `LocalGaugeFieldAlgebra.complexRepJet` : the action on the complexified jet algebra.

## iii. Table of contents

- A. The transport on the component space
- B. The Maurer–Cartan shift
- C. The action of the jet gauge group
  - C.1. The transformation law of the generators
  - C.2. The complexified action

## iv. References

* None.

-/

@[expose] public section

set_option linter.unusedSectionVars false

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ}


open TensorProduct MvPowerSeries

/-!

## A. The transport on the component space

-/

namespace GaugeBoson

variable (G) in
/-- The adjoint transport on the gauge-boson target space at `p` derivatives, the adjoint
  Taylor coefficient on the gauge-algebra factor, the identity on the spacetime index. -/
noncomputable def adjointTransport (U : G.gaugeJetGroup) (p : Multiset (Fin 1 ⊕ Fin 3)) :
    (GaugeBoson G) →ₗ[ℝ] (GaugeBoson G) :=
  (valLinEquiv G).symm.toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (G.adjointCoeff U p) ∘ₗ
    (valLinEquiv G).toLinearMap

lemma adjointTransport_mk_tmul (U : G.gaugeJetGroup) (p : Multiset (Fin 1 ⊕ Fin 3))
    (v : Lorentz.CoVector) (a : G.lieSubalgebra) :
    adjointTransport G U p ⟨v ⊗ₜ[ℝ] a⟩ = ⟨v ⊗ₜ[ℝ] G.adjointCoeff U p a⟩ := rfl

/-- The adjoint transport at the identity. Only the base point survives. -/
lemma adjointTransport_one (p : Multiset (Fin 1 ⊕ Fin 3)) :
    adjointTransport G 1 p = if p = 0 then LinearMap.id else 0 := by
  rw [adjointTransport, G.adjointCoeff_one]
  rcases eq_or_ne p 0 with rfl | hp
  · rw [ite_eq_left rfl, ite_eq_left rfl, TensorProduct.map_id]
    refine LinearMap.ext fun v => ?_
    simp
  · rw [ite_eq_right hp, ite_eq_right hp]
    refine LinearMap.ext fun v => ?_
    rw [show TensorProduct.map (LinearMap.id (M := Lorentz.CoVector))
        (0 : G.lieSubalgebra →ₗ[ℝ] G.lieSubalgebra) = 0 from by
      refine TensorProduct.ext' fun x a => ?_
      rw [TensorProduct.map_tmul, LinearMap.zero_apply, TensorProduct.tmul_zero]
      rfl]
    simp

/-- The adjoint transport of a product is the antidiagonal convolution of transports. -/
lemma adjointTransport_mul (U V : G.gaugeJetGroup) (p : Multiset (Fin 1 ⊕ Fin 3)) :
    adjointTransport G (U * V) p
      = (p.antidiagonal.map fun r =>
          adjointTransport G U r.1 ∘ₗ adjointTransport G V r.2).sum := by
  refine LinearMap.ext fun v => ?_
  rw [Multiset.sum_linearMap_apply, Multiset.map_map]
  obtain ⟨m⟩ := v
  induction m using TensorProduct.inductionOn with
  | tmul x a =>
    apply (valLinEquiv G).injective
    rw [adjointTransport_mk_tmul, map_multiset_sum, Multiset.map_map, valLinEquiv_apply,
      show ((⟨x ⊗ₜ[ℝ] G.adjointCoeff (U * V) p a⟩ : (GaugeBoson G))).val
        = x ⊗ₜ[ℝ] G.adjointCoeff (U * V) p a from rfl,
      G.adjointCoeff_mul, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.tmul_sum, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply, LinearMap.comp_apply, adjointTransport_mk_tmul,
      valLinEquiv_apply]
  | add m₁ m₂ h₁ h₂ =>
    rw [show (⟨m₁ + m₂⟩ : (GaugeBoson G)) = (⟨m₁⟩ : (GaugeBoson G)) + ⟨m₂⟩ from rfl, map_add, h₁,
      h₂, ← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply]
    exact (map_add _ _ _).symm

/-- The dual transport carries a component covector to the component covector of the
  transported adjoint index. The spacetime slot is untouched. -/
lemma dualMap_adjointTransport_componentDual (U : G.gaugeJetGroup)
    (p : Multiset (Fin 1 ⊕ Fin 3)) (ω : Module.Dual ℝ Lorentz.CoVector)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    (adjointTransport G U p).dualMap ((componentDual G) ω φ)
      = (componentDual G) ω (φ ∘ₗ G.adjointCoeff U p) := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨m⟩ := v
  induction m using TensorProduct.inductionOn with
  | tmul x a =>
    rw [LinearMap.dualMap_apply, adjointTransport_mk_tmul,
      componentDual_apply_val_tmul, componentDual_apply_val_tmul]
    rfl
  | add m₁ m₂ h₁ h₂ =>
    rw [show (⟨m₁ + m₂⟩ : (GaugeBoson G)) = (⟨m₁⟩ : (GaugeBoson G)) + ⟨m₂⟩ from rfl, map_add,
      map_add, h₁, h₂]

end GaugeBoson

namespace LocalGaugeFieldAlgebra

variable (G) in
/-- The value of the transport on the derivative symbol at `s`, the all-orders Leibniz
  convolution of the dual adjoint transports against lower derivative symbols. -/
noncomputable def transportFun (U : G.gaugeJetGroup) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℝ (GaugeBoson G) →ₗ[ℝ] (GaugeBoson.FieldDerivSpace G) :=
  (s.antidiagonal.map fun p =>
    (TensorProduct.mk ℝ SpaceTimeDerivAlgebraℝ (Module.Dual ℝ (GaugeBoson G))
        (SpaceTimeDerivAlgebraℝ.basisMultiset p.2)).comp
      ((GaugeBoson.adjointTransport G U p.1).dualMap)).sum

variable (G) in
/-- The linear part of the gauge action on the field-derivative space. On a component
  function `∂_s A^ψ` it is the all-orders Leibniz convolution of the Taylor coefficients
  of the adjoint action of `U` against the lower component functions. -/
noncomputable def transport (U : G.gaugeJetGroup) :
    (GaugeBoson.FieldDerivSpace G) →ₗ[ℝ] (GaugeBoson.FieldDerivSpace G) :=
  TensorProduct.lift (SpaceTimeDerivAlgebraℝ.basisMultiset.constr ℝ (transportFun G U))

lemma transport_basis_tmul (U : G.gaugeJetGroup) (s : Multiset (Fin 1 ⊕ Fin 3))
    (ψ : Module.Dual ℝ (GaugeBoson G)) :
    transport G U (SpaceTimeDerivAlgebraℝ.basisMultiset s ⊗ₜ[ℝ] ψ)
      = (s.antidiagonal.map fun p =>
          SpaceTimeDerivAlgebraℝ.basisMultiset p.2 ⊗ₜ[ℝ]
            (GaugeBoson.adjointTransport G U p.1).dualMap ψ).sum := by
  rw [transport, TensorProduct.lift.tmul, Module.Basis.constr_basis, transportFun,
    Multiset.sum_linearMap_apply, Multiset.map_map]
  rfl

/-- Two maps out of the field-derivative space agree if they agree on the components
  `∂_s A^ψ` with `s` a derivative multiset and `ψ` an arbitrary covector. -/
lemma _root_.GaugeBoson.FieldDerivSpace.ext_of_basis
    {M : Type*} [AddCommMonoid M] [Module ℝ M]
    {F₁ F₂ : (GaugeBoson.FieldDerivSpace G) →ₗ[ℝ] M}
    (h : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℝ (GaugeBoson G)),
      F₁ (SpaceTimeDerivAlgebraℝ.basisMultiset s ⊗ₜ[ℝ] ψ)
        = F₂ (SpaceTimeDerivAlgebraℝ.basisMultiset s ⊗ₜ[ℝ] ψ)) : F₁ = F₂ := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul a ψ =>
    have ha : a ∈ Submodule.span ℝ
        (Set.range SpaceTimeDerivAlgebraℝ.basisMultiset) := by
      rw [SpaceTimeDerivAlgebraℝ.basisMultiset.span_eq]; trivial
    induction ha using Submodule.span_induction with
    | mem b hb => obtain ⟨s, rfl⟩ := hb; exact h s ψ
    | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero]
    | add b c _ _ hb hc => rw [TensorProduct.add_tmul, map_add, map_add, hb, hc]
    | smul c b _ hb => rw [← TensorProduct.smul_tmul', map_smul, map_smul, hb]

/-- The transport of the identity is the identity. -/
lemma transport_one : transport G (1 : G.gaugeJetGroup) = LinearMap.id := by
  refine GaugeBoson.FieldDerivSpace.ext_of_basis fun s ψ => ?_
  rw [transport_basis_tmul,
    Multiset.map_congr rfl (fun p hp => by rw [GaugeBoson.adjointTransport_one]),
    Multiset.sum_antidiagonal_eq_of_fst_ne_zero s
      (fun p => SpaceTimeDerivAlgebraℝ.basisMultiset p.2 ⊗ₜ[ℝ]
        ((if p.1 = 0 then LinearMap.id else 0) :
          (GaugeBoson G) →ₗ[ℝ] (GaugeBoson G)).dualMap ψ)
      (fun p _ hp => by
        rw [ite_eq_right hp, show ((0 : (GaugeBoson G) →ₗ[ℝ] (GaugeBoson G))).dualMap ψ = 0 from
            LinearMap.ext fun v => by simp, TensorProduct.tmul_zero]),
    ite_eq_left rfl, LinearMap.id_apply,
    show (LinearMap.id : (GaugeBoson G) →ₗ[ℝ] (GaugeBoson G)).dualMap ψ = ψ from
      LinearMap.ext fun v => rfl]

/-- The transport is an anti-homomorphism. The transport of a product is the reverse
  composite. Composed with the inverse, it becomes the linear part of the gauge
  representation. -/
lemma transport_mul (U V : G.gaugeJetGroup) :
    transport G (U * V) = transport G V ∘ₗ transport G U := by
  refine GaugeBoson.FieldDerivSpace.ext_of_basis fun s ψ => ?_
  have hdual : ∀ (p : Multiset (Fin 1 ⊕ Fin 3) × Multiset (Fin 1 ⊕ Fin 3)),
      (GaugeBoson.adjointTransport G (U * V) p.1).dualMap ψ
        = (p.1.antidiagonal.map fun r =>
            (GaugeBoson.adjointTransport G V r.2).dualMap
              ((GaugeBoson.adjointTransport G U r.1).dualMap ψ)).sum := by
    intro p
    rw [GaugeBoson.adjointTransport_mul]
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.dualMap_apply, Multiset.sum_linearMap_apply, Multiset.map_map,
      map_multiset_sum, Multiset.map_map, Multiset.sum_linearMap_apply, Multiset.map_map]
    rfl
  have hLHS : transport G (U * V) (SpaceTimeDerivAlgebraℝ.basisMultiset s ⊗ₜ[ℝ] ψ)
      = (s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            SpaceTimeDerivAlgebraℝ.basisMultiset p.2 ⊗ₜ[ℝ]
              (GaugeBoson.adjointTransport G V q.2).dualMap
                ((GaugeBoson.adjointTransport G U q.1).dualMap ψ)).sum).sum := by
    rw [transport_basis_tmul]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [hdual p, Multiset.tmul_sum, Multiset.map_map]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => rfl)
  have hRHS : (transport G V ∘ₗ transport G U)
        (SpaceTimeDerivAlgebraℝ.basisMultiset s ⊗ₜ[ℝ] ψ)
      = (s.antidiagonal.map fun p =>
          (p.2.antidiagonal.map fun q =>
            SpaceTimeDerivAlgebraℝ.basisMultiset q.2 ⊗ₜ[ℝ]
              (GaugeBoson.adjointTransport G V q.1).dualMap
                ((GaugeBoson.adjointTransport G U p.1).dualMap ψ)).sum).sum := by
    rw [LinearMap.comp_apply, transport_basis_tmul, map_multiset_sum, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    exact transport_basis_tmul V p.2 _
  rw [hLHS, hRHS]
  exact Multiset.sum_antidiagonal_assoc s fun a b c =>
    SpaceTimeDerivAlgebraℝ.basisMultiset c ⊗ₜ[ℝ]
      (GaugeBoson.adjointTransport G V b).dualMap
        ((GaugeBoson.adjointTransport G U a).dualMap ψ)

end LocalGaugeFieldAlgebra

/-!

## B. The Maurer–Cartan shift

-/

namespace LocalGaugeFieldAlgebra

variable (G) in
/-- The Taylor coefficient of the Maurer–Cartan form of `U` at the derivative multiset
  `s`, packaged as a gauge boson. The spacetime index runs over the coordinate
  directions, and the adjoint index over the base-point Taylor coefficients of the
  Maurer–Cartan form. -/
noncomputable def maurerCartanBosonCoeff (U : G.gaugeJetGroup) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    (GaugeBoson G) :=
  ⟨∑ μ, Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
    G.evalLie (G.iteratedDerivJ s (-G.maurerCartan U μ))⟩

@[simp]
lemma maurerCartanBosonCoeff_one (s : Multiset (Fin 1 ⊕ Fin 3)) :
    maurerCartanBosonCoeff G 1 s = 0 := by
  rw [show (0 : (GaugeBoson G)) = ⟨0⟩ from rfl, maurerCartanBosonCoeff]
  congr 1
  refine Finset.sum_eq_zero fun μ _ => ?_
  rw [show (-G.maurerCartan 1 μ) = 0 from neg_eq_zero.mpr (G.maurerCartan_one μ), map_zero,
    map_zero, TensorProduct.tmul_zero]

/-- The Maurer–Cartan Taylor coefficients of a product, given by the cocycle identity with the
  adjoint transport convoluted in by the Taylor–Leibniz theorem. -/
lemma maurerCartanBosonCoeff_mul (U V : G.gaugeJetGroup) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    maurerCartanBosonCoeff G (U * V) s
      = maurerCartanBosonCoeff G U s
        + (s.antidiagonal.map fun p =>
            GaugeBoson.adjointTransport G U p.1 (maurerCartanBosonCoeff G V p.2)).sum := by
  apply (GaugeBoson.valLinEquiv G).injective
  have hE : ∀ (W : G.gaugeJetGroup) (t : Multiset (Fin 1 ⊕ Fin 3)),
      (GaugeBoson.valLinEquiv G) (maurerCartanBosonCoeff G W t)
        = ∑ μ, Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
            G.evalLie (G.iteratedDerivJ t
              (-G.maurerCartan W μ)) := fun W t => rfl
  have hB : ∀ p q : Multiset (Fin 1 ⊕ Fin 3),
      (GaugeBoson.valLinEquiv G) (GaugeBoson.adjointTransport G U p (maurerCartanBosonCoeff G V q))
        = ∑ μ, Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
            G.adjointCoeff U p (G.evalLie
              (G.iteratedDerivJ q (-G.maurerCartan V μ))) := by
    intro p q
    rw [show (GaugeBoson.valLinEquiv G) (GaugeBoson.adjointTransport G U p
      (maurerCartanBosonCoeff G V q))
        = TensorProduct.map LinearMap.id (G.adjointCoeff U p)
            ((GaugeBoson.valLinEquiv G) (maurerCartanBosonCoeff G V q)) from by
        rw [GaugeBoson.adjointTransport]
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          LinearEquiv.apply_symm_apply],
      hE, map_sum]
    exact Finset.sum_congr rfl fun μ _ => by
      rw [TensorProduct.map_tmul, LinearMap.id_apply]
  have hA : (GaugeBoson.valLinEquiv G) (maurerCartanBosonCoeff G (U * V) s)
      = ∑ μ, (Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
          G.evalLie (G.iteratedDerivJ s
            (-G.maurerCartan U μ))
        + (s.antidiagonal.map fun p =>
            Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
              G.adjointCoeff U p.1 (G.evalLie
                (G.iteratedDerivJ p.2
                  (-G.maurerCartan V μ)))).sum) := by
    rw [hE]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [show (-G.maurerCartan (U * V) μ)
        = -G.maurerCartan U μ + G.adjointJ U
          (-G.maurerCartan V μ) from
        by rw [G.maurerCartan_cocycle, neg_add, map_neg],
      map_add, map_add, G.evalLie_iteratedDerivJ_adjointJ, TensorProduct.tmul_add,
      Multiset.tmul_sum, Multiset.map_map]
    exact congrArg (fun z => _ + z)
      (congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => rfl))
  rw [hA, Finset.sum_add_distrib, map_add, map_multiset_sum, Multiset.map_map, ← hE,
    ← Multiset.sum_map_finsetSum]
  congr 1

variable (G) in
/-- The Maurer–Cartan shift, the linear functional on the component space pairing a
  component `∂_s A^ψ` with the Taylor coefficient of the Maurer–Cartan form of `U`. It is
  the constant part of the affine gauge action. -/
noncomputable def maurerCartanShift (U : G.gaugeJetGroup) :
    (GaugeBoson.FieldDerivSpace G) →ₗ[ℝ] ℝ :=
  TensorProduct.lift (SpaceTimeDerivAlgebraℝ.basisMultiset.constr ℝ fun s =>
    Module.Dual.eval ℝ (GaugeBoson G) (maurerCartanBosonCoeff G U s))

lemma maurerCartanShift_basis_tmul (U : G.gaugeJetGroup) (s : Multiset (Fin 1 ⊕ Fin 3))
    (ψ : Module.Dual ℝ (GaugeBoson G)) :
    maurerCartanShift G U (SpaceTimeDerivAlgebraℝ.basisMultiset s ⊗ₜ[ℝ] ψ)
      = ψ (maurerCartanBosonCoeff G U s) := by
  rw [maurerCartanShift, TensorProduct.lift.tmul, Module.Basis.constr_basis]
  rfl

@[simp]
lemma maurerCartanShift_one : maurerCartanShift G (1 : G.gaugeJetGroup) = 0 := by
  refine GaugeBoson.FieldDerivSpace.ext_of_basis fun s ψ => ?_
  rw [maurerCartanShift_basis_tmul, maurerCartanBosonCoeff_one, map_zero, LinearMap.zero_apply]

/-- The cocycle identity for the Maurer–Cartan shift. -/
lemma maurerCartanShift_mul (U V : G.gaugeJetGroup) :
    maurerCartanShift G (U * V) =
      maurerCartanShift G V ∘ₗ transport G U + maurerCartanShift G U := by
  refine GaugeBoson.FieldDerivSpace.ext_of_basis fun s ψ => ?_
  rw [LinearMap.add_apply, LinearMap.comp_apply, maurerCartanShift_basis_tmul,
    maurerCartanBosonCoeff_mul, map_add, add_comm]
  congr 1
  · rw [map_multiset_sum, Multiset.map_map, transport_basis_tmul, map_multiset_sum,
      Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [Function.comp_apply, Function.comp_apply, maurerCartanShift_basis_tmul]
    rfl
  · exact (maurerCartanShift_basis_tmul U s ψ).symm

/-!

## C. The action of the jet gauge group

-/

variable (G) in
/-- The affine action of a jet of gauge transformations on the generators of the jet
  algebra, the transported component plus the Maurer–Cartan shift, both of `U⁻¹` — the
  contragredient convention for an action on component functions. -/
noncomputable def gaugeGeneratorMap (U : G.gaugeJetGroup) :
    (GaugeBoson.FieldDerivSpace G) →ₗ[ℝ] (LocalGaugeFieldAlgebra G) :=
  (SymmetricAlgebra.ι ℝ (GaugeBoson.FieldDerivSpace G)).comp (transport G U⁻¹)
    + (Algebra.linearMap ℝ (LocalGaugeFieldAlgebra G)).comp (maurerCartanShift G U⁻¹)

lemma gaugeGeneratorMap_apply (U : G.gaugeJetGroup) (x : (GaugeBoson.FieldDerivSpace G)) :
    gaugeGeneratorMap G U x = SymmetricAlgebra.ι ℝ _ (transport G U⁻¹ x)
      + algebraMap ℝ (LocalGaugeFieldAlgebra G) (maurerCartanShift G U⁻¹ x) := rfl

variable (G) in
/-- The action of the jet gauge group on the gauge-boson jet algebra, the substitution
  homomorphism determined by the affine action on the generators, `∂_s A^ψ` going to its
  transported convolution plus the Maurer–Cartan shift of `U⁻¹`. -/
noncomputable def repJet : Representation ℝ G.gaugeJetGroup (LocalGaugeFieldAlgebra G) where
  toFun U := (SymmetricAlgebra.lift (gaugeGeneratorMap G U)).toLinearMap
  map_one' := by
    suffices h :
        SymmetricAlgebra.lift (gaugeGeneratorMap G 1) = AlgHom.id ℝ (LocalGaugeFieldAlgebra G) by
      rw [h]; rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    show SymmetricAlgebra.lift (gaugeGeneratorMap G 1) (SymmetricAlgebra.ι ℝ _ x)
      = AlgHom.id ℝ (LocalGaugeFieldAlgebra G) (SymmetricAlgebra.ι ℝ _ x)
    rw [SymmetricAlgebra.lift_ι_apply, gaugeGeneratorMap_apply, inv_one, transport_one,
      maurerCartanShift_one, LinearMap.id_apply, LinearMap.zero_apply, map_zero, add_zero]
    rfl
  map_mul' U V := by
    suffices h : SymmetricAlgebra.lift (gaugeGeneratorMap G (U * V))
        = (SymmetricAlgebra.lift (gaugeGeneratorMap G U)).comp (SymmetricAlgebra.lift
          (gaugeGeneratorMap G V)) by
      rw [h]; rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    show SymmetricAlgebra.lift (gaugeGeneratorMap G (U * V)) (SymmetricAlgebra.ι ℝ _ x)
      = ((SymmetricAlgebra.lift (gaugeGeneratorMap G U)).comp
          (SymmetricAlgebra.lift (gaugeGeneratorMap G V))) (SymmetricAlgebra.ι ℝ _ x)
    rw [SymmetricAlgebra.lift_ι_apply, gaugeGeneratorMap_apply, AlgHom.comp_apply,
      SymmetricAlgebra.lift_ι_apply, gaugeGeneratorMap_apply, map_add,
      SymmetricAlgebra.lift_ι_apply, gaugeGeneratorMap_apply, AlgHom.commutes,
      mul_inv_rev, transport_mul, maurerCartanShift_mul, LinearMap.comp_apply,
      LinearMap.add_apply, LinearMap.comp_apply, map_add, add_assoc]

variable (G) in
/-- The action of `U` as an algebra homomorphism. A jet of gauge transformations acts on
  a Lagrangian term factor by factor. -/
noncomputable def repJetAlgHom (U : G.gaugeJetGroup) :
    (LocalGaugeFieldAlgebra G) →ₐ[ℝ] (LocalGaugeFieldAlgebra G) :=
  SymmetricAlgebra.lift (gaugeGeneratorMap G U)

@[simp]
lemma repJet_ι (U : G.gaugeJetGroup) (x : (GaugeBoson.FieldDerivSpace G)) :
    repJet G U (SymmetricAlgebra.ι ℝ _ x)
      = SymmetricAlgebra.ι ℝ _ (transport G U⁻¹ x)
        + algebraMap ℝ (LocalGaugeFieldAlgebra G) (maurerCartanShift G U⁻¹ x) := by
  rw [show repJet G U (SymmetricAlgebra.ι ℝ _ x)
      = SymmetricAlgebra.lift (gaugeGeneratorMap G U) (SymmetricAlgebra.ι ℝ _ x) from rfl,
    SymmetricAlgebra.lift_ι_apply, gaugeGeneratorMap_apply]

@[simp]
lemma repJet_apply_one (U : G.gaugeJetGroup) :
    repJet G U (1 : (LocalGaugeFieldAlgebra G)) = 1 := by
  rw [show repJet G U (1 : (LocalGaugeFieldAlgebra G))
    = SymmetricAlgebra.lift (gaugeGeneratorMap G U) 1 from rfl, map_one]

lemma repJet_apply_mul (U : G.gaugeJetGroup) (x y : (LocalGaugeFieldAlgebra G)) :
    repJet G U (x * y) = repJet G U x * repJet G U y := by
  rw [show repJet G U (x * y)
    = SymmetricAlgebra.lift (gaugeGeneratorMap G U) (x * y) from rfl, map_mul]
  rfl

@[simp]
lemma repJet_algebraMap (U : G.gaugeJetGroup) (r : ℝ) :
    repJet G U (algebraMap ℝ (LocalGaugeFieldAlgebra G) r)
      = algebraMap ℝ (LocalGaugeFieldAlgebra G) r := by
  rw [show repJet G U (algebraMap ℝ (LocalGaugeFieldAlgebra G) r)
    = SymmetricAlgebra.lift (gaugeGeneratorMap G U)
      (algebraMap ℝ (LocalGaugeFieldAlgebra G) r) from rfl,
    AlgHom.commutes]

/-!

### C.1. The transformation law of the generators

-/

/-- The component covector at `μ` picks the `μ`-th Maurer–Cartan Taylor coefficient out
  of the shift. -/
lemma componentDual_dualBasis_maurerCartanBosonCoeff (W : G.gaugeJetGroup)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    (GaugeBoson.componentDual G) (Lorentz.CoVector.basis.dualBasis μ) φ
        (maurerCartanBosonCoeff G W s)
      = φ (G.evalLie (G.iteratedDerivJ s
          (-G.maurerCartan W μ))) := by
  have hsum : maurerCartanBosonCoeff G W s
      = ∑ ν, (⟨Lorentz.CoVector.basis ν ⊗ₜ[ℝ]
          G.evalLie (G.iteratedDerivJ s
            (-G.maurerCartan W ν))⟩ : (GaugeBoson G)) := by
    apply (GaugeBoson.valLinEquiv G).injective
    rw [map_sum]
    rfl
  rw [hsum, map_sum]
  rw [Finset.sum_congr rfl fun ν _ => GaugeBoson.componentDual_apply_val_tmul _ _ _ _]
  rw [Finset.sum_congr rfl fun ν _ => by
    rw [Module.Basis.dualBasis_apply_self, ite_mul, one_mul, zero_mul]]
  rw [Finset.sum_ite_eq' Finset.univ μ
    (fun ν => φ (G.evalLie (G.iteratedDerivJ s
      (-G.maurerCartan W ν)))), ite_eq_left (Finset.mem_univ μ)]

/-- The transformation law of the derivative generators. A jet of gauge transformations acts on
  `∂_s A_μ^φ` by the all-orders
  Leibniz convolution of the adjoint Taylor coefficients of `U⁻¹` against lower
  generators, plus the Taylor coefficient of the Maurer–Cartan form of `U⁻¹`. -/
lemma repJet_iteratedJetDeriv_ofA (U : G.gaugeJetGroup)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    repJet G U ((iteratedJetDeriv G) s ((ofA G) μ φ))
      = (s.antidiagonal.map fun p =>
          (iteratedJetDeriv G) p.2 ((ofA G) μ (G.adjointDualCoeff U⁻¹ p.1 φ))).sum
        + algebraMap ℝ (LocalGaugeFieldAlgebra G)
            (φ (G.evalLie (G.iteratedDerivJ s
              (-G.maurerCartan U⁻¹ μ)))) := by
  rw [iteratedJetDeriv_ofA, repJet_ι, transport_basis_tmul, maurerCartanShift_basis_tmul,
    componentDual_dualBasis_maurerCartanBosonCoeff, map_multiset_sum, Multiset.map_map]
  congr 1
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
  rw [Function.comp_apply, GaugeBoson.dualMap_adjointTransport_componentDual,
    iteratedJetDeriv_ofA]
  rfl

/-!

### C.2. The complexified action

-/

variable (G) in
/-- The action of the jet gauge group on the complexified gauge-boson jet algebra, by
  base change. -/
noncomputable def complexRepJet :
    Representation ℂ G.gaugeJetGroup (ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra G)) where
  toFun U := LinearMap.baseChange ℂ (repJet G U)
  map_one' := by
    rw [map_one, Module.End.one_eq_id, LinearMap.baseChange_id, Module.End.one_eq_id]
  map_mul' U V := by
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp, Module.End.mul_eq_comp]

@[simp]
lemma complexRepJet_tmul (U : G.gaugeJetGroup) (z : ℂ) (x : (LocalGaugeFieldAlgebra G)) :
    complexRepJet G U (z ⊗ₜ[ℝ] x) = z ⊗ₜ[ℝ] repJet G U x := rfl

variable (G) in
/-- The action of a jet on the complexified gauge-boson jet algebra, as an algebra
  endomorphism, the base change of `repJetAlgHom`. -/
noncomputable def complexRepJetAlgHom (U : G.gaugeJetGroup) :
    ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra G) →ₐ[ℂ] ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra G) :=
  Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (repJetAlgHom G U)

lemma complexRepJet_apply (U : G.gaugeJetGroup) (x : ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra G)) :
    complexRepJet G U x = complexRepJetAlgHom G U x := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | tmul z a => rfl

lemma complexRepJet_apply_mul (U : G.gaugeJetGroup)
    (x y : ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra G)) :
    complexRepJet G U (x * y)
      = complexRepJet G U x * complexRepJet G U y := by
  rw [complexRepJet_apply, complexRepJet_apply, complexRepJet_apply, map_mul]

/-- The iterated complexified derivative of a real element is the complexification of the
  iterated real derivative. -/
lemma iteratedD_complexJetDeriv_one_tmul (s : Multiset (Fin 1 ⊕ Fin 3))
    (x : (LocalGaugeFieldAlgebra G)) :
    Lorentz.iteratedD (complexJetDeriv G) complexJetDeriv_comm s ((1 : ℂ) ⊗ₜ[ℝ] x)
      = (1 : ℂ) ⊗ₜ[ℝ] (iteratedJetDeriv G) s x := by
  induction s using Multiset.induction_on generalizing x with
  | empty => rw [Lorentz.iteratedD_zero, iteratedJetDeriv_zero]; rfl
  | cons μ s ih =>
    rw [Lorentz.iteratedD_cons, LinearMap.comp_apply, ih, complexJetDeriv_tmul,
      iteratedJetDeriv_cons, LinearMap.comp_apply]

/-- A real scalar in the complexified jet algebra is the corresponding complex scalar. -/
lemma one_tmul_algebraMap (r : ℝ) :
    (1 : ℂ) ⊗ₜ[ℝ] (algebraMap ℝ (LocalGaugeFieldAlgebra G) r)
      = algebraMap ℂ (ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra G)) ((r : ℝ) : ℂ) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    Algebra.algebraMap_eq_smul_one,
    show ((r : ℝ) • ((1 : ℂ) ⊗ₜ[ℝ] (1 : (LocalGaugeFieldAlgebra G))))
      = (((r : ℝ) : ℂ)) • ((1 : ℂ) ⊗ₜ[ℝ] (1 : (LocalGaugeFieldAlgebra G))) from
      (algebraMap_smul ℂ r _).symm, Algebra.TensorProduct.one_def]

/-- The transformation law of the derivative generators on the complexification, in the
  form of `GaugeBoson.TransformsAsGaugeField`. -/
lemma complexRepJet_iteratedD_one_tmul_ofA (U : G.gaugeJetGroup)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    complexRepJet G U (Lorentz.iteratedD (complexJetDeriv G) complexJetDeriv_comm s
        ((1 : ℂ) ⊗ₜ[ℝ] (ofA G) μ φ))
      = (s.antidiagonal.map fun p =>
          Lorentz.iteratedD (complexJetDeriv G) complexJetDeriv_comm p.2
            ((1 : ℂ) ⊗ₜ[ℝ] (ofA G) μ (G.adjointDualCoeff U⁻¹ p.1 φ))).sum
        + algebraMap ℂ (ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra G))
            (((φ (G.evalLie (G.iteratedDerivJ s
              (-G.maurerCartan U⁻¹ μ))) : ℝ)) : ℂ) := by
  rw [iteratedD_complexJetDeriv_one_tmul, complexRepJet_tmul,
    repJet_iteratedJetDeriv_ofA, TensorProduct.tmul_add, Multiset.tmul_sum,
    Multiset.map_map, one_tmul_algebraMap]
  congr 1
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => by
    rw [Function.comp_apply, iteratedD_complexJetDeriv_one_tmul])

end LocalGaugeFieldAlgebra

