/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module


public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Pre.Basic
public import Physlib.Relativity.IsLorentzDeriv
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
/-!
# The jet component space of a matter field

## i. Overview

For a matter field valued in a complex vector space `V`, the *jet component space* is the
span of the derivative symbols `∂_s ψ_α` and their conjugates `∂_s ψ̄_α`: the local
coordinate functions on the space of jets of the field. This file defines that space and
the structure on it that does not involve a gauge group: the Lorentz action, the jet
derivative, functoriality in `V` and the mass-weight scaling. The action of a gauge group
is in `Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.JetComponentSpace.GaugeAction`.

## ii. Key results

- `JetComponentSpace` : the space of component functions.
- `JetComponentSpace.repLorentzGroup` : the Lorentz action on the component space.
- `JetComponentSpace.jetDeriv` : the shift `∂_s ψ_α ↦ ∂_{s + {μ}} ψ_α` of the label.
- `JetComponentSpace.jetDeriv_comm` : the shifts in different directions commute.
- `JetComponentSpace.repLorentzGroup_jetDeriv` : the shift is a Lorentz vector.
- `JetComponentSpace.comap` : functoriality, contravariant in the target space.
- `JetComponentSpace.comapEquiv` : a relabelling of the target space relabels the
  component functions.
- `JetComponentSpace.massWeightScale` : the mass-weight scaling.
- `JetComponentSpace.comap_comp_massWeightScale` : the scaling is natural in the target
  space, hence blind to which part of it a component function came from.
- `JetComponentSpace.fstPiEquiv`, `JetComponentSpace.sndPiEquiv` : the two halves of the
  component space of a finite product of target spaces split.

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} {M : MatterField jets}


/-- The space of component functions of the matter field `M`: the span of the symbols
`∂_s ψ_α` and their conjugates `∂_s ψ̄_α`, where `α` runs over the target space `M.V`. The
first factor holds the unconjugated symbols, the second the conjugate ones; in each,
`DerivAlgebraComplex` carries the derivative label `s` and the dual factor the target
component `α`.

Only `M.V` enters the space itself; the field's Lorentz and gauge representations and its
mass weight enter the structure carried on it below. Taking the whole matter field rather
than its value space is what lets that structure be read off `M` instead of being supplied
by hand at each use. -/
abbrev JetComponentSpace (M : MatterField jets) : Type :=
  (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ M.V) ×
  (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule M.V))

/-!

## The Lorentz action on the component space

-/

/-- **The Lorentz action on the jet component space.** Under a Lorentz transformation a
matter field transforms as `ψ(x) ↦ ρ(Λ) ψ(Λ⁻¹ x)`, so a derivative symbol `∂_s ψ_α` is
acted on in *both* of its labels: the derivative multiset `s` by the Lorentz action on
covectors, extended to `DerivAlgebraComplex`, and the target index `α` by the
contragredient of `ρ`.

Unlike the gauge action, this needs no fibrewise-linearity or finite-dimensionality
hypothesis: the two labels transform independently, so the action is simply a tensor
product of representations. The conjugate half is the same with `ρ` replaced by its
conjugate, the symbols `∂_s ψ̄_α` transforming by `star` of the spinor matrix. -/
noncomputable def JetComponentSpace.repLorentzGroup (M : MatterField jets) :
    Representation ℂ SL(2,ℂ) (JetComponentSpace M) :=
  (DerivAlgebraComplex.repLorentzGroup.tprod M.repLorentz.dual).prod
    (DerivAlgebraComplex.repLorentzGroup.tprod M.repLorentz.conj.dual)

@[simp]
lemma JetComponentSpace.repLorentzGroup_fst (Λ : SL(2,ℂ)) (x : JetComponentSpace M) :
    (JetComponentSpace.repLorentzGroup M Λ x).1
      = (DerivAlgebraComplex.repLorentzGroup.tprod M.repLorentz.dual) Λ x.1 := rfl

@[simp]
lemma JetComponentSpace.repLorentzGroup_snd (Λ : SL(2,ℂ)) (x : JetComponentSpace M) :
    (JetComponentSpace.repLorentzGroup M Λ x).2
      = (DerivAlgebraComplex.repLorentzGroup.tprod M.repLorentz.conj.dual) Λ x.2 := rfl

/-- On a pure symbol the Lorentz action is diagonal in the two labels: the derivative
label transforms in `DerivAlgebraComplex`, the target index contragrediently. -/
@[simp]
lemma JetComponentSpace.repLorentzGroup_fst_tmul (Λ : SL(2,ℂ)) (a : DerivAlgebraComplex)
    (φ : Module.Dual ℂ M.V)
    (y : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule M.V)) :
    (JetComponentSpace.repLorentzGroup M Λ (a ⊗ₜ[ℂ] φ, y)).1
      = DerivAlgebraComplex.repLorentzGroup Λ a ⊗ₜ[ℂ] (φ ∘ₗ M.repLorentz Λ⁻¹) := rfl

/-!

## The jet derivative

-/

/-- the derivative of components in the jet component space,
  in the direction `μ`: the shift `∂_s ψ_α ↦ ∂_{s + {μ}} ψ_α` of the derivative label,
  and likewise on the conjugate components.

  This is right multiplication by the degree-one element `∂_μ` on the
  `DerivAlgebraComplex` factor, leaving the target index untouched. It uses a basis of
  the Lorentz covectors — that is what the index `μ` is — but no basis of `V`. -/
noncomputable def JetComponentSpace.jetDeriv (μ : Fin 1 ⊕ Fin 3) :
    JetComponentSpace M →ₗ[ℂ] JetComponentSpace M :=
  LinearMap.prodMap
    (TensorProduct.map
      (LinearMap.mulRight ℂ (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
      LinearMap.id)
    (TensorProduct.map
      (LinearMap.mulRight ℂ (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
      LinearMap.id)

@[simp]
lemma JetComponentSpace.jetDeriv_fst_tmul (μ : Fin 1 ⊕ Fin 3)
    (a : DerivAlgebraComplex) (φ : Module.Dual ℂ M.V)
    (y : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule M.V)) :
    (JetComponentSpace.jetDeriv μ (a ⊗ₜ[ℂ] φ, y)).1
      = (a * DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))) ⊗ₜ[ℂ] φ := rfl

@[simp]
lemma JetComponentSpace.jetDeriv_snd_tmul (μ : Fin 1 ⊕ Fin 3)
    (x : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ M.V)
    (a : DerivAlgebraComplex) (φ : Module.Dual ℂ (ConjModule M.V)) :
    (JetComponentSpace.jetDeriv μ (x, a ⊗ₜ[ℂ] φ)).2
      = (a * DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))) ⊗ₜ[ℂ] φ := rfl

/-- **Total derivatives commute.** Mixed partials agree because the derivative labels
  live in a *symmetric* algebra; no basis of `V` is involved. -/
lemma JetComponentSpace.jetDeriv_comm (μ ν : Fin 1 ⊕ Fin 3) :
    (JetComponentSpace.jetDeriv (M := M) μ).comp (JetComponentSpace.jetDeriv ν)
      = (JetComponentSpace.jetDeriv (M := M) ν).comp (JetComponentSpace.jetDeriv μ) := by
  have hmul : ∀ b c : DerivAlgebraComplex,
      (LinearMap.mulRight ℂ b).comp (LinearMap.mulRight ℂ c)
        = LinearMap.mulRight ℂ (c * b) :=
    fun b c => LinearMap.ext fun x => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply, mul_assoc]
  rw [JetComponentSpace.jetDeriv, JetComponentSpace.jetDeriv, LinearMap.prodMap_comp,
    LinearMap.prodMap_comp, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp, hmul, hmul, mul_comm]

/-- The element being multiplied in is the degree-one derivative symbol `∂_μ`, the image
  of the dual basis covector under `SymmetricAlgebra.ι`. -/
lemma JetComponentSpace.jetDeriv_eq_ι (μ : Fin 1 ⊕ Fin 3) :
    JetComponentSpace.jetDeriv (M := M) μ
      = LinearMap.prodMap
        (TensorProduct.map
          (LinearMap.mulRight ℂ (SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule)
            (Lorentz.complexCoBasis.dualBasis μ))) LinearMap.id)
        (TensorProduct.map
          (LinearMap.mulRight ℂ (SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule)
            (Lorentz.complexCoBasis.dualBasis μ))) LinearMap.id) := by
  rw [JetComponentSpace.jetDeriv, DerivAlgebraComplex.basis_singleton]

@[simp]
lemma JetComponentSpace.jetDeriv_fst (μ : Fin 1 ⊕ Fin 3) (v : JetComponentSpace M) :
    (JetComponentSpace.jetDeriv μ v).1
      = TensorProduct.map
        (LinearMap.mulRight ℂ (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
        LinearMap.id v.1 := rfl

@[simp]
lemma JetComponentSpace.jetDeriv_snd (μ : Fin 1 ⊕ Fin 3) (v : JetComponentSpace M) :
    (JetComponentSpace.jetDeriv μ v).2
      = TensorProduct.map
        (LinearMap.mulRight ℂ (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
        LinearMap.id v.2 := rfl

/-!

## Lorentz covariance of the jet derivative

-/

/-- The covariance of the derivative-symbol multiplication on one tensor factor of the
  component space, for an arbitrary representation on the other factor. -/
private lemma repLorentzGroup_tprod_mulRight_jetSymbol {W : Type*} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ SL(2,ℂ) W) (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (w : DerivAlgebraComplex ⊗[ℂ] W) :
    (DerivAlgebraComplex.repLorentzGroup.tprod ρ) Λ
      (TensorProduct.map
        (LinearMap.mulRight ℂ (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
        LinearMap.id w) =
    ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
      TensorProduct.map
        (LinearMap.mulRight ℂ (DerivAlgebraComplex.basis ({a} : Multiset (Fin 1 ⊕ Fin 3))))
        LinearMap.id ((DerivAlgebraComplex.repLorentzGroup.tprod ρ) Λ w) := by
  have hsym : DerivAlgebraComplex.repLorentzGroup Λ
      (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        DerivAlgebraComplex.basis ({a} : Multiset (Fin 1 ⊕ Fin 3)) := by
    rw [DerivAlgebraComplex.basis_singleton, DerivAlgebraComplex.repLorentzGroup_apply_ι,
      Lorentz.CoℂModule.SL2CRep_dual_dualBasis, map_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [map_smul, DerivAlgebraComplex.basis_singleton]
  have hrep : ∀ (q : DerivAlgebraComplex) (f : W),
      (DerivAlgebraComplex.repLorentzGroup.tprod ρ) Λ (q ⊗ₜ[ℂ] f) =
        (DerivAlgebraComplex.repLorentzGroup Λ q) ⊗ₜ[ℂ] (ρ Λ f) := fun _ _ => rfl
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [map_add, smul_add]
  | tmul q f =>
    rw [TensorProduct.map_tmul, LinearMap.mulRight_apply, LinearMap.id_apply, hrep, hrep,
      DerivAlgebraComplex.repLorentzGroup_apply_mul, hsym, Finset.mul_sum,
      TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun a _ => by
      rw [TensorProduct.map_tmul, LinearMap.mulRight_apply, LinearMap.id_apply,
        mul_smul_comm, TensorProduct.smul_tmul']

/-- **The jet derivative is a Lorentz vector on the component space.** Appending `∂_μ` and
  then acting is acting and then appending the transformed `∂_μ`, which is a combination of
  the `∂_a`. Both halves of the component space are covered by the same argument: the
  derivative label lives in the first tensor factor, and what sits in the second factor —
  `M.repLorentz.dual` or `M.repLorentz.conj.dual` — plays no role. -/
lemma JetComponentSpace.repLorentzGroup_jetDeriv (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (v : JetComponentSpace M) :
    JetComponentSpace.repLorentzGroup M Λ (JetComponentSpace.jetDeriv μ v) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        JetComponentSpace.jetDeriv a (JetComponentSpace.repLorentzGroup M Λ v) := by
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sum, Prod.smul_fst, JetComponentSpace.repLorentzGroup_fst,
      JetComponentSpace.jetDeriv_fst]
    exact repLorentzGroup_tprod_mulRight_jetSymbol _ Λ μ v.1
  · simp only [Prod.snd_sum, Prod.smul_snd, JetComponentSpace.repLorentzGroup_snd,
      JetComponentSpace.jetDeriv_snd]
    exact repLorentzGroup_tprod_mulRight_jetSymbol _ Λ μ v.2

/-!

## Functoriality in the target space

-/

variable {N : MatterField jets}

/-- **The component space is contravariant in the target space.** A linear map `f : M.V →ₗ N.V`
  of target spaces pulls the component functions of the field `N` back to component
  functions of the field `M`: a component function is a *covector* on the target, so it
  transposes. The derivative label is untouched, and the conjugate half transposes the
  conjugate of `f`. -/
noncomputable def JetComponentSpace.comap (f : M.V →ₗ[ℂ] N.V) :
    JetComponentSpace N →ₗ[ℂ] JetComponentSpace M :=
  LinearMap.prodMap
    (TensorProduct.map LinearMap.id (Module.Dual.transpose f))
    (TensorProduct.map LinearMap.id (Module.Dual.transpose (ConjModule.map f)))

@[simp]
lemma JetComponentSpace.comap_fst_tmul (f : M.V →ₗ[ℂ] N.V) (a : DerivAlgebraComplex)
    (φ : Module.Dual ℂ N.V) (y : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule N.V)) :
    (JetComponentSpace.comap f (a ⊗ₜ[ℂ] φ, y)).1 = a ⊗ₜ[ℂ] (φ ∘ₗ f) := rfl

@[simp]
lemma JetComponentSpace.comap_snd_tmul (f : M.V →ₗ[ℂ] N.V)
    (x : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ N.V) (a : DerivAlgebraComplex)
    (φ : Module.Dual ℂ (ConjModule N.V)) :
    (JetComponentSpace.comap f (x, a ⊗ₜ[ℂ] φ)).2 = a ⊗ₜ[ℂ] (φ ∘ₗ ConjModule.map f) := rfl

@[simp]
lemma JetComponentSpace.comap_id :
    JetComponentSpace.comap (LinearMap.id : M.V →ₗ[ℂ] M.V) = LinearMap.id := by
  rw [JetComponentSpace.comap,
    show Module.Dual.transpose (LinearMap.id : M.V →ₗ[ℂ] M.V) = LinearMap.id from rfl,
    show ConjModule.map (LinearMap.id : M.V →ₗ[ℂ] M.V) = LinearMap.id from rfl,
    show Module.Dual.transpose (LinearMap.id : ConjModule M.V →ₗ[ℂ] ConjModule M.V)
      = LinearMap.id from rfl, TensorProduct.map_id, TensorProduct.map_id]
  rfl

/-- Functoriality: pulling back along `g ∘ f` is pulling back along `g` and then along `f`.
  The order reverses, as it must for a contravariant construction. -/
lemma JetComponentSpace.comap_comp {P : MatterField jets}
    (f : M.V →ₗ[ℂ] N.V) (g : N.V →ₗ[ℂ] P.V) :
    JetComponentSpace.comap (g.comp f)
      = (JetComponentSpace.comap f).comp (JetComponentSpace.comap g) := by
  rw [JetComponentSpace.comap, JetComponentSpace.comap, JetComponentSpace.comap,
    LinearMap.prodMap_comp, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    LinearMap.id_comp]
  rfl

/-- A relabelling of the target space relabels the component functions. An isomorphism
  `e : M.V ≃ₗ N.V` of target spaces identifies the two component spaces, contravariantly: the
  component functions of the field `N` become those of the field `M`. This is
  `comap` upgraded to an equivalence, the two directions being mutually inverse by
  functoriality. -/
noncomputable def JetComponentSpace.comapEquiv (e : M.V ≃ₗ[ℂ] N.V) :
    JetComponentSpace N ≃ₗ[ℂ] JetComponentSpace M :=
  LinearEquiv.ofLinearMap (JetComponentSpace.comap e.toLinearMap)
    (JetComponentSpace.comap e.symm.toLinearMap)
    (by rw [← JetComponentSpace.comap_comp, show e.symm.toLinearMap.comp e.toLinearMap
        = LinearMap.id from LinearMap.ext fun v => e.symm_apply_apply v,
      JetComponentSpace.comap_id])
    (by rw [← JetComponentSpace.comap_comp, show e.toLinearMap.comp e.symm.toLinearMap
        = LinearMap.id from LinearMap.ext fun w => e.apply_symm_apply w,
      JetComponentSpace.comap_id])

@[simp]
lemma JetComponentSpace.comapEquiv_apply (e : M.V ≃ₗ[ℂ] N.V) (x : JetComponentSpace N) :
    JetComponentSpace.comapEquiv e x = JetComponentSpace.comap e.toLinearMap x := rfl

/-- **An equivariant map of target spaces gives an equivariant pullback.** If `f : M.V →ₗ N.V`
  intertwines the two Lorentz representations then `comap f` intertwines the induced actions on
  the component spaces, in the opposite direction. Component functions are covectors, so
  the unconjugated half transposes `f` against the contragredient action and the conjugate
  half against its conjugate; both reduce to equivariance of `f` at `Λ⁻¹`. -/
lemma JetComponentSpace.comap_comp_repLorentzGroup (f : M.V →ₗ[ℂ] N.V)
    (hf : ∀ Λ : SL(2,ℂ), f.comp (M.repLorentz Λ) = (N.repLorentz Λ).comp f)
    (Λ : SL(2,ℂ)) :
    (JetComponentSpace.comap f).comp (JetComponentSpace.repLorentzGroup N Λ)
      = (JetComponentSpace.repLorentzGroup M Λ).comp (JetComponentSpace.comap f) := by
  have hdual : (Module.Dual.transpose (R := ℂ) f).comp (N.repLorentz.dual Λ)
      = (M.repLorentz.dual Λ).comp (Module.Dual.transpose f) :=
    LinearMap.ext fun ψ =>
      LinearMap.ext fun v => (congrArg ψ (LinearMap.congr_fun (hf Λ⁻¹) v)).symm
  have hconj : (Module.Dual.transpose (R := ℂ) (ConjModule.map (k := ℂ) f)).comp
        (N.repLorentz.conj.dual Λ)
      = (M.repLorentz.conj.dual Λ).comp
        (Module.Dual.transpose (ConjModule.map (k := ℂ) f)) :=
    LinearMap.ext fun ψ => LinearMap.ext fun v =>
      (congrArg ψ (LinearMap.congr_fun (hf Λ⁻¹)
        ((conjEquiv (k := ℂ) (M := M.V)).symm v))).symm
  show (LinearMap.prodMap (TensorProduct.map LinearMap.id (Module.Dual.transpose f))
        (TensorProduct.map LinearMap.id
          (Module.Dual.transpose (ConjModule.map (k := ℂ) f)))).comp
      (LinearMap.prodMap
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ) (N.repLorentz.dual Λ))
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ) (N.repLorentz.conj.dual Λ)))
    = (LinearMap.prodMap
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ) (M.repLorentz.dual Λ))
        (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup Λ) (M.repLorentz.conj.dual Λ))).comp
      (LinearMap.prodMap (TensorProduct.map LinearMap.id (Module.Dual.transpose f))
        (TensorProduct.map LinearMap.id
          (Module.Dual.transpose (ConjModule.map (k := ℂ) f))))
  rw [LinearMap.prodMap_comp, LinearMap.prodMap_comp, ← TensorProduct.map_comp,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    LinearMap.id_comp, LinearMap.comp_id, hdual, hconj]

/-- **The pullback commutes with the jet derivative.** The two act on different tensor
  factors — the derivative label and the target index — so an inclusion of species is a map
  of differential algebras. -/
lemma JetComponentSpace.comap_jetDeriv (f : M.V →ₗ[ℂ] N.V) (μ : Fin 1 ⊕ Fin 3) :
    (JetComponentSpace.comap f).comp (JetComponentSpace.jetDeriv μ)
      = (JetComponentSpace.jetDeriv μ).comp (JetComponentSpace.comap f) := by
  rw [JetComponentSpace.comap, JetComponentSpace.jetDeriv, JetComponentSpace.jetDeriv,
    LinearMap.prodMap_comp, LinearMap.prodMap_comp, ← TensorProduct.map_comp,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp, ← TensorProduct.map_comp]
  simp only [LinearMap.comp_id, LinearMap.id_comp]

/-!

## The mass-weight scaling

The mass dimension is tracked multiplicatively, through a scaling action: for a field of
*mass weight* `w` — twice the mass dimension, kept integral so that fermions of dimension
`3/2` carry weight `3` — the generator `∂_s φ_α` scales by `c ^ (w + 2 |s|)`, one factor
of `c ^ 2` per derivative. The scaling on the component space below lifts functorially to
the bosonic and fermionic algebras, where it defines their mass-dimension grading.

-/

/-- The mass-weight scaling on the jet component space of a field of mass weight `w`
  (twice the mass dimension): the generator `∂_s φ_α` and its conjugate are scaled by
  `c ^ (w + 2 |s|)`, through the derivative-degree scaling `DerivAlgebraComplex.gradeScale`
  on the derivative label. -/
noncomputable def JetComponentSpace.massWeightScale (w : ℕ) (c : ℂ) :
    JetComponentSpace M →ₗ[ℂ] JetComponentSpace M :=
  c ^ w • LinearMap.prodMap
    (TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap LinearMap.id)
    (TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap LinearMap.id)

/-- On an unconjugated component function `∂_s φ_α` the mass-weight scaling is
  multiplication by `c ^ (w + 2 |s|)`. -/
lemma JetComponentSpace.massWeightScale_fst_basis_tmul (w : ℕ) (c : ℂ)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ M.V)
    (y : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule M.V)) :
    (JetComponentSpace.massWeightScale w c
        ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, y) : JetComponentSpace M)).1
      = c ^ (w + 2 * Multiset.card s) • (DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) := by
  simp only [massWeightScale, LinearMap.smul_apply, Prod.smul_fst, LinearMap.prodMap_apply,
    TensorProduct.map_tmul, AlgHom.toLinearMap_apply, DerivAlgebraComplex.gradeScale_basis,
    LinearMap.id_apply, TensorProduct.smul_tmul', ← pow_mul, pow_add, mul_smul,
    mul_comm 2 (Multiset.card s)]

@[simp]
lemma JetComponentSpace.massWeightScale_fst (w : ℕ) (c : ℂ) (v : JetComponentSpace M) :
    (JetComponentSpace.massWeightScale w c v).1
      = c ^ w • TensorProduct.map
          (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap LinearMap.id v.1 := rfl

@[simp]
lemma JetComponentSpace.massWeightScale_snd (w : ℕ) (c : ℂ) (v : JetComponentSpace M) :
    (JetComponentSpace.massWeightScale w c v).2
      = c ^ w • TensorProduct.map
          (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap LinearMap.id v.2 := rfl

/-- The derivative-degree scaling intertwines multiplication by a single derivative
  symbol up to one factor of the scaling parameter, on either half of the component
  space. -/
private lemma gradeScale_map_mulRight_basis {W : Type*} [AddCommGroup W] [Module ℂ W]
    (c : ℂ) (μ : Fin 1 ⊕ Fin 3) (x : DerivAlgebraComplex ⊗[ℂ] W) :
    TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap LinearMap.id
      (TensorProduct.map (LinearMap.mulRight ℂ
        (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3)))) LinearMap.id x)
    = c ^ 2 • TensorProduct.map (LinearMap.mulRight ℂ
        (DerivAlgebraComplex.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3)))) LinearMap.id
        (TensorProduct.map (DerivAlgebraComplex.gradeScale (c ^ 2)).toLinearMap
          LinearMap.id x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add a b ha hb => simp only [map_add, ha, hb, smul_add]
  | tmul a y =>
    simp only [TensorProduct.map_tmul, LinearMap.mulRight_apply, LinearMap.id_apply,
      AlgHom.toLinearMap_apply, map_mul, DerivAlgebraComplex.gradeScale_basis,
      Multiset.card_singleton, pow_one, mul_smul_comm, TensorProduct.smul_tmul']

/-- **The total derivative carries mass weight two** on the component space: the scaling
  intertwines the derivative shift up to a factor `c ^ 2`. -/
lemma JetComponentSpace.massWeightScale_jetDeriv (w : ℕ) (c : ℂ) (μ : Fin 1 ⊕ Fin 3) :
    (JetComponentSpace.massWeightScale (M := M) w c).comp (JetComponentSpace.jetDeriv μ)
      = c ^ 2 • (JetComponentSpace.jetDeriv μ).comp
          (JetComponentSpace.massWeightScale w c) := by
  have key := fun {W : Type _} [AddCommGroup W] [Module ℂ W]
      (x : DerivAlgebraComplex ⊗[ℂ] W) => gradeScale_map_mulRight_basis c μ x
  refine LinearMap.ext fun v => Prod.ext ?_ ?_
  · simp only [LinearMap.comp_apply, LinearMap.smul_apply, Prod.smul_fst,
      JetComponentSpace.massWeightScale_fst, JetComponentSpace.jetDeriv_fst, map_smul]
    exact (congrArg (fun z : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ M.V => c ^ w • z)
      (key v.1)).trans (smul_comm _ _ _)
  · simp only [LinearMap.comp_apply, LinearMap.smul_apply, Prod.smul_snd,
      JetComponentSpace.massWeightScale_snd, JetComponentSpace.jetDeriv_snd, map_smul]
    exact (congrArg (fun z : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule M.V) =>
      c ^ w • z) (key v.2)).trans (smul_comm _ _ _)

/-- **The mass-weight scaling is natural in the target space.** It commutes with every
  pullback, acting as it does on the derivative label and not on the target index. So the
  scaling cannot see which part of a target space a component function came from: in
  `JetComponentSpace (∀ i, V i)`, where a species enters through
  `comap (LinearMap.proj i)`, every species is scaled by the same weight. This is why the
  generator space of a multi-species theory, `GaugeFieldData.FermionGenerators`, records
  the weights on a direct sum, one per species, rather than on a single component space of
  the product. -/
lemma JetComponentSpace.comap_comp_massWeightScale (f : M.V →ₗ[ℂ] N.V) (w : ℕ) (c : ℂ) :
    (JetComponentSpace.comap f).comp (JetComponentSpace.massWeightScale w c)
      = (JetComponentSpace.massWeightScale w c).comp (JetComponentSpace.comap f) := by
  simp only [JetComponentSpace.comap, JetComponentSpace.massWeightScale,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.prodMap_comp,
    ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]

/-!

## The dual and the conjugate of a finite product

The component space of a direct sum of matter fields splits, and both halves split for the
same two reasons: the dual of a finite product is the product of the duals, and conjugation
commutes with products. Neither statement mentions a matter field, so both are recorded
here, on a bare family of modules; the splitting they add up to is
`MatterField.jetComponentSpacePiEquiv`, downstream where `MatterField.pi` is available. The
index type must be finite — the dual of an infinite product is strictly larger than the
product of the duals, and `TensorProduct.piRight` is an equivalence only in the finite case.

-/

section Pi

variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
  [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]

/-- A pair of families is the same thing as a family of pairs. This is the last step of
  the splitting of a component space over a product of target spaces: the two halves split
  separately into families, and this puts the two families back together index by index.
  Everything is the identity on underlying data, so every law is `rfl`. -/
def prodPiEquiv {A B : ι → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] :
    ((∀ i, A i) × (∀ i, B i)) ≃ₗ[ℂ] ∀ i, (A i × B i) where
  toFun p i := (p.1 i, p.2 i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := (fun i => (f i).1, fun i => (f i).2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The unconjugated half of the component space of a finite direct sum splits.** The
  symbols `∂_s ψ_α` of a `(∀ i, E i)`-valued field are the families, over the index, of
  the symbols of the summands: the dual distributes over the finite product and the
  derivative label is untouched. -/
noncomputable def JetComponentSpace.fstPiEquiv :
    (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (∀ i, E i))
      ≃ₗ[ℂ] ∀ i, DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (E i) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ DerivAlgebraComplex)
      (LinearMap.lsum ℂ E ℂ).symm).trans
    (TensorProduct.piRight ℂ ℂ DerivAlgebraComplex fun i => Module.Dual ℂ (E i))

/-- On a pure symbol the splitting restricts the target index to one summand: the
  component `∂_s ψ_α` of the direct sum in the summand `i` is `∂_s` of the covector `φ`
  precomposed with the inclusion of that summand. -/
@[simp]
lemma JetComponentSpace.fstPiEquiv_tmul (a : DerivAlgebraComplex)
    (φ : Module.Dual ℂ (∀ i, E i)) (i : ι) :
    fstPiEquiv E (a ⊗ₜ[ℂ] φ) i = a ⊗ₜ[ℂ] (φ ∘ₗ LinearMap.single ℂ E i) := rfl

/-- **The conjugate half of the component space of a finite direct sum splits**, by the
  same argument applied to the conjugate modules, using that conjugation commutes with
  products. -/
noncomputable def JetComponentSpace.sndPiEquiv :
    (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule (∀ i, E i)))
      ≃ₗ[ℂ] ∀ i, DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule (E i)) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ DerivAlgebraComplex)
      (((ConjModule.piEquiv (k := ℂ) E).symm.dualMap).trans
        (LinearMap.lsum ℂ (fun i => ConjModule (E i)) ℂ).symm)).trans
    (TensorProduct.piRight ℂ ℂ DerivAlgebraComplex fun i => Module.Dual ℂ (ConjModule (E i)))

/-- On a pure conjugate symbol the splitting again restricts the target index to one
  summand, the inclusion being read through the conjugation. -/
@[simp]
lemma JetComponentSpace.sndPiEquiv_tmul (a : DerivAlgebraComplex)
    (ψ : Module.Dual ℂ (ConjModule (∀ i, E i))) (i : ι) :
    sndPiEquiv E (a ⊗ₜ[ℂ] ψ) i
      = a ⊗ₜ[ℂ] (ψ ∘ₗ ConjModule.map (k := ℂ) (LinearMap.single ℂ E i)) := rfl

/-- The splitting sends the family supported on one summand back to the pullback along
  the projection onto that summand: a component function of the summand `i`, read as a
  component function of the whole, is `φ ∘ proj i`. -/
lemma JetComponentSpace.fstPiEquiv_symm_single (i : ι)
    (z : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (E i)) :
    (fstPiEquiv E).symm (Pi.single i z)
      = TensorProduct.map LinearMap.id (Module.Dual.transpose (LinearMap.proj i)) z := by
  refine (fstPiEquiv E).injective (funext fun j => ?_)
  rw [LinearEquiv.apply_symm_apply]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a φ =>
      rw [TensorProduct.map_tmul, fstPiEquiv_tmul, LinearMap.id_apply]
      by_cases hij : i = j
      · subst hij
        rw [Pi.single_eq_same]
        exact congrArg (fun ψ => a ⊗ₜ[ℂ] ψ)
          (LinearMap.ext fun v => (congrArg φ (Pi.single_eq_same i v)).symm)
      · have h0 : (Module.Dual.transpose (LinearMap.proj i) φ).comp
            (LinearMap.single ℂ E j) = 0 :=
          LinearMap.ext fun v => (congrArg φ (Pi.single_eq_of_ne hij v)).trans (map_zero φ)
        rw [Pi.single_eq_of_ne (Ne.symm hij), h0, TensorProduct.tmul_zero]
  | add x y hx hy =>
      simp only [Pi.single_add, Pi.add_apply, map_add, hx, hy]

/-- The conjugate half of the splitting behaves in the same way, the projection read
  through the conjugation. -/
lemma JetComponentSpace.sndPiEquiv_symm_single (i : ι)
    (z : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule (E i))) :
    (sndPiEquiv E).symm (Pi.single i z)
      = TensorProduct.map LinearMap.id
          (Module.Dual.transpose (ConjModule.map (k := ℂ) (LinearMap.proj i))) z := by
  refine (sndPiEquiv E).injective (funext fun j => ?_)
  rw [LinearEquiv.apply_symm_apply]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a φ =>
      rw [TensorProduct.map_tmul, sndPiEquiv_tmul, LinearMap.id_apply]
      by_cases hij : i = j
      · subst hij
        rw [Pi.single_eq_same]
        exact congrArg (fun ψ => a ⊗ₜ[ℂ] ψ)
          (LinearMap.ext fun v => (congrArg φ (Pi.single_eq_same i v)).symm)
      · have h0 : (Module.Dual.transpose
            (ConjModule.map (k := ℂ) (LinearMap.proj i)) φ).comp
            (ConjModule.map (k := ℂ) (LinearMap.single ℂ E j)) = 0 :=
          LinearMap.ext fun v => (congrArg φ (Pi.single_eq_of_ne hij v)).trans (map_zero φ)
        rw [Pi.single_eq_of_ne (Ne.symm hij), h0, TensorProduct.tmul_zero]
  | add x y hx hy =>
      simp only [Pi.single_add, Pi.add_apply, map_add, hx, hy]
end Pi
