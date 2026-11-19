/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module


public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.InfinitesimalAction
/-!
# The field-derivative space of a matter field

The span of the derivative symbols of a matter field and their conjugates, with its Lorentz
action, jet derivative and mass-weight scaling.

## i. Overview

For a matter field valued in a complex vector space `V`, the field-derivative space is the span
of the derivative symbols `∂_s ψ_α` and their conjugates `∂_s ψ̄_α`, the local coordinate
functions on the space of jets of the field. This file defines that space and the structure on
it that does not involve a gauge group. This is the Lorentz action, the jet derivative,
functoriality in `V` and the mass-weight scaling. The action of the gauge group is in
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.FieldDerivSpace.GaugeAction`.

## ii. Key results

- `FieldDerivSpace` : the space of component functions of the matter field `M`, the span of the
  symbols `∂_s ψ_α` and their conjugates `∂_s ψ̄_α`, where `α` runs over the target space `M.V`
- `FieldDerivSpace.repLorentzGroup` : the Lorentz action on the field-derivative space
- `FieldDerivSpace.jetDeriv` : the derivative of components in the field-derivative space, in the
  direction `μ`, the shift `∂_s ψ_α ↦ ∂_{s + {μ}} ψ_α` of the derivative label, and likewise on the
  conjugate components
- `FieldDerivSpace.jetDeriv_comm` : total derivatives commute
- `FieldDerivSpace.repLorentzGroup_jetDeriv` : the jet derivative is a Lorentz vector on the
  component space
- `FieldDerivSpace.comap` : the component space is contravariant in the target space
- `FieldDerivSpace.comapEquiv` : a relabelling of the target space relabels the component
  functions
- `FieldDerivSpace.massWeightScale` : the mass-weight scaling on the field-derivative space of a
  field of mass weight `w` (twice the mass dimension), scaling the generator `∂_s φ_α` and its
  conjugate by `c ^ (w + 2 |s|)`, through the derivative-degree scaling
  `SpaceTimeDerivAlgebraℂ.gradeScale` on the derivative label
- `FieldDerivSpace.comap_comp_massWeightScale` : the mass-weight scaling is natural in the target
  space
- `FieldDerivSpace.fstPiEquiv` : the unconjugated half of the component space of a finite direct
  sum splits
- `FieldDerivSpace.sndPiEquiv` : the conjugate half of the component space of a finite direct sum
  splits, by the same argument applied to the conjugate modules, using that conjugation commutes
  with products

## iii. Table of contents

- A. The Lorentz action on the component space
- B. The jet derivative
- C. Lorentz covariance of the jet derivative
- D. Functoriality in the target space
- E. The mass-weight scaling
- F. The dual and the conjugate of a finite product

## iv. References

* None.

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ} {M : G.MatterField}


/-- The space of component functions of the matter field `M`, the span of the symbols
`∂_s ψ_α` and their conjugates `∂_s ψ̄_α`, where `α` runs over the target space `M.V`. The
first factor holds the unconjugated symbols, the second the conjugate ones; in each,
`SpaceTimeDerivAlgebraℂ` carries the derivative label `s` and the dual factor the target
component `α`.

Only `M.V` enters the space itself; the field's Lorentz and gauge representations and its
mass weight enter the structure carried on it below. Taking the whole matter field rather
than its value space is what lets that structure be read off `M` instead of being supplied
by hand at each use. -/
abbrev FieldDerivSpace (M : G.MatterField) : Type :=
  (SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ M.V) ×
  (SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (ConjModule M.V))

/-!

## A. The Lorentz action on the component space

-/

/-- The Lorentz action on the field-derivative space. Under a Lorentz transformation a
matter field transforms as `ψ(x) ↦ ρ(Λ) ψ(Λ⁻¹ x)`, so a derivative symbol `∂_s ψ_α` is
acted on in both of its labels, the derivative multiset `s` by the Lorentz action on
covectors, extended to `SpaceTimeDerivAlgebraℂ`, and the target index `α` by the
contragredient of `ρ`.

Unlike the gauge action, this needs no fibrewise-linearity or finite-dimensionality
hypothesis. The two labels transform independently, so the action is simply a tensor
product of representations. The conjugate half is the same with `ρ` replaced by its
conjugate, the symbols `∂_s ψ̄_α` transforming by `star` of the spinor matrix. -/
noncomputable def FieldDerivSpace.repLorentzGroup (M : G.MatterField) :
    Representation ℂ SL(2,ℂ) (FieldDerivSpace M) :=
  (SpaceTimeDerivAlgebraℂ.repLorentzGroup.tprod M.repLorentz.dual).prod
    (SpaceTimeDerivAlgebraℂ.repLorentzGroup.tprod M.repLorentz.conj.dual)

@[simp]
lemma FieldDerivSpace.repLorentzGroup_fst (Λ : SL(2,ℂ)) (x : FieldDerivSpace M) :
    (FieldDerivSpace.repLorentzGroup M Λ x).1
      = (SpaceTimeDerivAlgebraℂ.repLorentzGroup.tprod M.repLorentz.dual) Λ x.1 := rfl

@[simp]
lemma FieldDerivSpace.repLorentzGroup_snd (Λ : SL(2,ℂ)) (x : FieldDerivSpace M) :
    (FieldDerivSpace.repLorentzGroup M Λ x).2
      = (SpaceTimeDerivAlgebraℂ.repLorentzGroup.tprod M.repLorentz.conj.dual) Λ x.2 := rfl

/-!

## B. The jet derivative

-/

/-- The derivative of components in the field-derivative space,
  in the direction `μ`, the shift `∂_s ψ_α ↦ ∂_{s + {μ}} ψ_α` of the derivative label,
  and likewise on the conjugate components.

  This is right multiplication by the degree-one element `∂_μ` on the
  `SpaceTimeDerivAlgebraℂ` factor, leaving the target index untouched. It uses a basis of
  the Lorentz covectors — that is what the index `μ` is — but no basis of `V`. -/
noncomputable def FieldDerivSpace.jetDeriv (μ : Fin 1 ⊕ Fin 3) :
    FieldDerivSpace M →ₗ[ℂ] FieldDerivSpace M :=
  LinearMap.prodMap
    (TensorProduct.map
      (LinearMap.mulRight ℂ (SpaceTimeDerivAlgebraℂ.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
      LinearMap.id)
    (TensorProduct.map
      (LinearMap.mulRight ℂ (SpaceTimeDerivAlgebraℂ.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
      LinearMap.id)

@[simp]
lemma FieldDerivSpace.jetDeriv_fst_tmul (μ : Fin 1 ⊕ Fin 3)
    (a : SpaceTimeDerivAlgebraℂ) (φ : Module.Dual ℂ M.V)
    (y : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (ConjModule M.V)) :
    (FieldDerivSpace.jetDeriv μ (a ⊗ₜ[ℂ] φ, y)).1
      = (a * SpaceTimeDerivAlgebraℂ.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))) ⊗ₜ[ℂ] φ := rfl

@[simp]
lemma FieldDerivSpace.jetDeriv_snd_tmul (μ : Fin 1 ⊕ Fin 3)
    (x : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ M.V)
    (a : SpaceTimeDerivAlgebraℂ) (φ : Module.Dual ℂ (ConjModule M.V)) :
    (FieldDerivSpace.jetDeriv μ (x, a ⊗ₜ[ℂ] φ)).2
      = (a * SpaceTimeDerivAlgebraℂ.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))) ⊗ₜ[ℂ] φ := rfl

/-- Total derivatives commute. Mixed partials agree because the derivative labels
  live in a *symmetric* algebra; no basis of `V` is involved. -/
lemma FieldDerivSpace.jetDeriv_comm (μ ν : Fin 1 ⊕ Fin 3) :
    (FieldDerivSpace.jetDeriv (M := M) μ).comp (FieldDerivSpace.jetDeriv ν)
      = (FieldDerivSpace.jetDeriv (M := M) ν).comp (FieldDerivSpace.jetDeriv μ) := by
  have hmul : ∀ b c : SpaceTimeDerivAlgebraℂ,
      (LinearMap.mulRight ℂ b).comp (LinearMap.mulRight ℂ c)
        = LinearMap.mulRight ℂ (c * b) :=
    fun b c => LinearMap.ext fun x => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply, mul_assoc]
  rw [FieldDerivSpace.jetDeriv, FieldDerivSpace.jetDeriv, LinearMap.prodMap_comp,
    LinearMap.prodMap_comp, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp, hmul, hmul, mul_comm]

@[simp]
lemma FieldDerivSpace.jetDeriv_fst (μ : Fin 1 ⊕ Fin 3) (v : FieldDerivSpace M) :
    (FieldDerivSpace.jetDeriv μ v).1
      = TensorProduct.map
        (LinearMap.mulRight ℂ (SpaceTimeDerivAlgebraℂ.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
        LinearMap.id v.1 := rfl

@[simp]
lemma FieldDerivSpace.jetDeriv_snd (μ : Fin 1 ⊕ Fin 3) (v : FieldDerivSpace M) :
    (FieldDerivSpace.jetDeriv μ v).2
      = TensorProduct.map
        (LinearMap.mulRight ℂ (SpaceTimeDerivAlgebraℂ.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
        LinearMap.id v.2 := rfl

/-!

## C. Lorentz covariance of the jet derivative

-/

/-- The covariance of the derivative-symbol multiplication on one tensor factor of the
  component space, for an arbitrary representation on the other factor. -/
private lemma repLorentzGroup_tprod_mulRight_jetSymbol {W : Type*} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ SL(2,ℂ) W) (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (w : SpaceTimeDerivAlgebraℂ ⊗[ℂ] W) :
    (SpaceTimeDerivAlgebraℂ.repLorentzGroup.tprod ρ) Λ
      (TensorProduct.map
        (LinearMap.mulRight ℂ (SpaceTimeDerivAlgebraℂ.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))))
        LinearMap.id w) =
    ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
      TensorProduct.map
        (LinearMap.mulRight ℂ (SpaceTimeDerivAlgebraℂ.basis ({a} : Multiset (Fin 1 ⊕ Fin 3))))
        LinearMap.id ((SpaceTimeDerivAlgebraℂ.repLorentzGroup.tprod ρ) Λ w) := by
  have hsym : SpaceTimeDerivAlgebraℂ.repLorentzGroup Λ
      (SpaceTimeDerivAlgebraℂ.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3))) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        SpaceTimeDerivAlgebraℂ.basis ({a} : Multiset (Fin 1 ⊕ Fin 3)) := by
    rw [SpaceTimeDerivAlgebraℂ.basis_singleton, SpaceTimeDerivAlgebraℂ.repLorentzGroup_apply_ι,
      Lorentz.ComplexCoVector.SL2CRep_dual_dualBasis, map_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [map_smul, SpaceTimeDerivAlgebraℂ.basis_singleton]
  have hrep : ∀ (q : SpaceTimeDerivAlgebraℂ) (f : W),
      (SpaceTimeDerivAlgebraℂ.repLorentzGroup.tprod ρ) Λ (q ⊗ₜ[ℂ] f) =
        (SpaceTimeDerivAlgebraℂ.repLorentzGroup Λ q) ⊗ₜ[ℂ] (ρ Λ f) := fun _ _ => rfl
  induction w using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [map_add, smul_add]
  | tmul q f =>
    rw [TensorProduct.map_tmul, LinearMap.mulRight_apply, LinearMap.id_apply, hrep, hrep,
      SpaceTimeDerivAlgebraℂ.repLorentzGroup_apply_mul, hsym, Finset.mul_sum,
      TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun a _ => by
      rw [TensorProduct.map_tmul, LinearMap.mulRight_apply, LinearMap.id_apply,
        mul_smul_comm, TensorProduct.smul_tmul']

/-- The jet derivative is a Lorentz vector on the component space. Appending `∂_μ` and
  then acting is acting and then appending the transformed `∂_μ`, which is a combination of
  the `∂_a`. Both halves of the component space are covered by the same argument. The
  derivative label lives in the first tensor factor, and what sits in the second factor —
  `M.repLorentz.dual` or `M.repLorentz.conj.dual` — plays no role. -/
lemma FieldDerivSpace.repLorentzGroup_jetDeriv (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (v : FieldDerivSpace M) :
    FieldDerivSpace.repLorentzGroup M Λ (FieldDerivSpace.jetDeriv μ v) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        FieldDerivSpace.jetDeriv a (FieldDerivSpace.repLorentzGroup M Λ v) := by
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sum, Prod.smul_fst, FieldDerivSpace.repLorentzGroup_fst,
      FieldDerivSpace.jetDeriv_fst]
    exact repLorentzGroup_tprod_mulRight_jetSymbol _ Λ μ v.1
  · simp only [Prod.snd_sum, Prod.smul_snd, FieldDerivSpace.repLorentzGroup_snd,
      FieldDerivSpace.jetDeriv_snd]
    exact repLorentzGroup_tprod_mulRight_jetSymbol _ Λ μ v.2

/-!

## D. Functoriality in the target space

-/

variable {N : G.MatterField}

/-- The component space is contravariant in the target space. A linear map `f : M.V →ₗ N.V`
  of target spaces pulls the component functions of the field `N` back to component
  functions of the field `M`. A component function is a covector on the target, so it
  transposes. The derivative label is untouched, and the conjugate half transposes the
  conjugate of `f`. -/
noncomputable def FieldDerivSpace.comap (f : M.V →ₗ[ℂ] N.V) :
    FieldDerivSpace N →ₗ[ℂ] FieldDerivSpace M :=
  LinearMap.prodMap
    (TensorProduct.map LinearMap.id (Module.Dual.transpose f))
    (TensorProduct.map LinearMap.id (Module.Dual.transpose (ConjModule.map f)))

@[simp]
lemma FieldDerivSpace.comap_fst_tmul (f : M.V →ₗ[ℂ] N.V) (a : SpaceTimeDerivAlgebraℂ)
    (φ : Module.Dual ℂ N.V) (y : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (ConjModule N.V)) :
    (FieldDerivSpace.comap f (a ⊗ₜ[ℂ] φ, y)).1 = a ⊗ₜ[ℂ] (φ ∘ₗ f) := rfl

@[simp]
lemma FieldDerivSpace.comap_snd_tmul (f : M.V →ₗ[ℂ] N.V)
    (x : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ N.V) (a : SpaceTimeDerivAlgebraℂ)
    (φ : Module.Dual ℂ (ConjModule N.V)) :
    (FieldDerivSpace.comap f (x, a ⊗ₜ[ℂ] φ)).2 = a ⊗ₜ[ℂ] (φ ∘ₗ ConjModule.map f) := rfl

@[simp]
lemma FieldDerivSpace.comap_id :
    FieldDerivSpace.comap (LinearMap.id : M.V →ₗ[ℂ] M.V) = LinearMap.id := by
  rw [FieldDerivSpace.comap,
    show Module.Dual.transpose (LinearMap.id : M.V →ₗ[ℂ] M.V) = LinearMap.id from rfl,
    show ConjModule.map (LinearMap.id : M.V →ₗ[ℂ] M.V) = LinearMap.id from rfl,
    show Module.Dual.transpose (LinearMap.id : ConjModule M.V →ₗ[ℂ] ConjModule M.V)
      = LinearMap.id from rfl, TensorProduct.map_id, TensorProduct.map_id]
  rfl

/-- Functoriality. Pulling back along `g ∘ f` is pulling back along `g` and then along `f`.
  The order reverses, as it must for a contravariant construction. -/
lemma FieldDerivSpace.comap_comp {P : G.MatterField}
    (f : M.V →ₗ[ℂ] N.V) (g : N.V →ₗ[ℂ] P.V) :
    FieldDerivSpace.comap (g.comp f)
      = (FieldDerivSpace.comap f).comp (FieldDerivSpace.comap g) := by
  rw [FieldDerivSpace.comap, FieldDerivSpace.comap, FieldDerivSpace.comap,
    LinearMap.prodMap_comp, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    LinearMap.id_comp]
  rfl

/-- A relabelling of the target space relabels the component functions. An isomorphism
  `e : M.V ≃ₗ N.V` of target spaces identifies the two component spaces, contravariantly, so the
  component functions of the field `N` become those of the field `M`. This is
  `comap` upgraded to an equivalence, the two directions being mutually inverse by
  functoriality. -/
noncomputable def FieldDerivSpace.comapEquiv (e : M.V ≃ₗ[ℂ] N.V) :
    FieldDerivSpace N ≃ₗ[ℂ] FieldDerivSpace M :=
  LinearEquiv.ofLinearMap (FieldDerivSpace.comap e.toLinearMap)
    (FieldDerivSpace.comap e.symm.toLinearMap)
    (by rw [← FieldDerivSpace.comap_comp, show e.symm.toLinearMap.comp e.toLinearMap
        = LinearMap.id from LinearMap.ext fun v => e.symm_apply_apply v,
      FieldDerivSpace.comap_id])
    (by rw [← FieldDerivSpace.comap_comp, show e.toLinearMap.comp e.symm.toLinearMap
        = LinearMap.id from LinearMap.ext fun w => e.apply_symm_apply w,
      FieldDerivSpace.comap_id])

@[simp]
lemma FieldDerivSpace.comapEquiv_apply (e : M.V ≃ₗ[ℂ] N.V) (x : FieldDerivSpace N) :
    FieldDerivSpace.comapEquiv e x = FieldDerivSpace.comap e.toLinearMap x := rfl

/-- An equivariant map of target spaces gives an equivariant pullback. If `f : M.V →ₗ N.V`
  intertwines the two Lorentz representations then `comap f` intertwines the induced actions on
  the component spaces, in the opposite direction. Component functions are covectors, so
  the unconjugated half transposes `f` against the contragredient action and the conjugate
  half against its conjugate; both reduce to equivariance of `f` at `Λ⁻¹`. -/
lemma FieldDerivSpace.comap_comp_repLorentzGroup (f : M.V →ₗ[ℂ] N.V)
    (hf : ∀ Λ : SL(2,ℂ), f.comp (M.repLorentz Λ) = (N.repLorentz Λ).comp f)
    (Λ : SL(2,ℂ)) :
    (FieldDerivSpace.comap f).comp (FieldDerivSpace.repLorentzGroup N Λ)
      = (FieldDerivSpace.repLorentzGroup M Λ).comp (FieldDerivSpace.comap f) := by
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
        (TensorProduct.map (SpaceTimeDerivAlgebraℂ.repLorentzGroup Λ) (N.repLorentz.dual Λ))
        (TensorProduct.map (SpaceTimeDerivAlgebraℂ.repLorentzGroup Λ) (N.repLorentz.conj.dual Λ)))
    = (LinearMap.prodMap
        (TensorProduct.map (SpaceTimeDerivAlgebraℂ.repLorentzGroup Λ) (M.repLorentz.dual Λ))
        (TensorProduct.map (SpaceTimeDerivAlgebraℂ.repLorentzGroup Λ)
          (M.repLorentz.conj.dual Λ))).comp
      (LinearMap.prodMap (TensorProduct.map LinearMap.id (Module.Dual.transpose f))
        (TensorProduct.map LinearMap.id
          (Module.Dual.transpose (ConjModule.map (k := ℂ) f))))
  rw [LinearMap.prodMap_comp, LinearMap.prodMap_comp, ← TensorProduct.map_comp,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    LinearMap.id_comp, LinearMap.comp_id, hdual, hconj]

/-- The pullback commutes with the jet derivative. The two act on different tensor
  factors — the derivative label and the target index — so an inclusion of species is a map
  of differential algebras. -/
lemma FieldDerivSpace.comap_jetDeriv (f : M.V →ₗ[ℂ] N.V) (μ : Fin 1 ⊕ Fin 3) :
    (FieldDerivSpace.comap f).comp (FieldDerivSpace.jetDeriv μ)
      = (FieldDerivSpace.jetDeriv μ).comp (FieldDerivSpace.comap f) := by
  rw [FieldDerivSpace.comap, FieldDerivSpace.jetDeriv, FieldDerivSpace.jetDeriv,
    LinearMap.prodMap_comp, LinearMap.prodMap_comp, ← TensorProduct.map_comp,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp, ← TensorProduct.map_comp]
  simp only [LinearMap.comp_id, LinearMap.id_comp]

/-!

## E. The mass-weight scaling

The mass dimension is tracked multiplicatively, through a scaling action: for a field of
*mass weight* `w` — twice the mass dimension, kept integral so that fermions of dimension
`3/2` carry weight `3` — the generator `∂_s φ_α` scales by `c ^ (w + 2 |s|)`, one factor
of `c ^ 2` per derivative. The scaling on the component space below lifts functorially to
the bosonic and fermionic algebras, where it defines their mass-dimension grading.

-/

/-- The mass-weight scaling on the field-derivative space of a field of mass weight `w`
  (twice the mass dimension). The generator `∂_s φ_α` and its conjugate are scaled by
  `c ^ (w + 2 |s|)`, through the derivative-degree scaling `SpaceTimeDerivAlgebraℂ.gradeScale`
  on the derivative label. -/
noncomputable def FieldDerivSpace.massWeightScale (w : ℕ) (c : ℂ) :
    FieldDerivSpace M →ₗ[ℂ] FieldDerivSpace M :=
  c ^ w • LinearMap.prodMap
    (TensorProduct.map (SpaceTimeDerivAlgebraℂ.gradeScale (c ^ 2)).toLinearMap LinearMap.id)
    (TensorProduct.map (SpaceTimeDerivAlgebraℂ.gradeScale (c ^ 2)).toLinearMap LinearMap.id)

/-- On an unconjugated component function `∂_s φ_α` the mass-weight scaling is
  multiplication by `c ^ (w + 2 |s|)`. -/
lemma FieldDerivSpace.massWeightScale_fst_basis_tmul (w : ℕ) (c : ℂ)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ M.V)
    (y : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (ConjModule M.V)) :
    (FieldDerivSpace.massWeightScale w c
        ((SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ, y) : FieldDerivSpace M)).1
      = c ^ (w + 2 * Multiset.card s) • (SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ) := by
  simp only [massWeightScale, LinearMap.smul_apply, Prod.smul_fst, LinearMap.prodMap_apply,
    TensorProduct.map_tmul, AlgHom.toLinearMap_apply, SpaceTimeDerivAlgebraℂ.gradeScale_basis,
    LinearMap.id_apply, TensorProduct.smul_tmul', ← pow_mul, pow_add, mul_smul,
    mul_comm 2 (Multiset.card s)]

@[simp]
lemma FieldDerivSpace.massWeightScale_fst (w : ℕ) (c : ℂ) (v : FieldDerivSpace M) :
    (FieldDerivSpace.massWeightScale w c v).1
      = c ^ w • TensorProduct.map
          (SpaceTimeDerivAlgebraℂ.gradeScale (c ^ 2)).toLinearMap LinearMap.id v.1 := rfl

@[simp]
lemma FieldDerivSpace.massWeightScale_snd (w : ℕ) (c : ℂ) (v : FieldDerivSpace M) :
    (FieldDerivSpace.massWeightScale w c v).2
      = c ^ w • TensorProduct.map
          (SpaceTimeDerivAlgebraℂ.gradeScale (c ^ 2)).toLinearMap LinearMap.id v.2 := rfl

/-- The derivative-degree scaling intertwines multiplication by a single derivative
  symbol up to one factor of the scaling parameter, on either half of the component
  space. -/
private lemma gradeScale_map_mulRight_basis {W : Type*} [AddCommGroup W] [Module ℂ W]
    (c : ℂ) (μ : Fin 1 ⊕ Fin 3) (x : SpaceTimeDerivAlgebraℂ ⊗[ℂ] W) :
    TensorProduct.map (SpaceTimeDerivAlgebraℂ.gradeScale (c ^ 2)).toLinearMap LinearMap.id
      (TensorProduct.map (LinearMap.mulRight ℂ
        (SpaceTimeDerivAlgebraℂ.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3)))) LinearMap.id x)
    = c ^ 2 • TensorProduct.map (LinearMap.mulRight ℂ
        (SpaceTimeDerivAlgebraℂ.basis ({μ} : Multiset (Fin 1 ⊕ Fin 3)))) LinearMap.id
        (TensorProduct.map (SpaceTimeDerivAlgebraℂ.gradeScale (c ^ 2)).toLinearMap
          LinearMap.id x) := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb, smul_add]
  | tmul a y =>
    simp only [TensorProduct.map_tmul, LinearMap.mulRight_apply, LinearMap.id_apply,
      AlgHom.toLinearMap_apply, map_mul, SpaceTimeDerivAlgebraℂ.gradeScale_basis,
      Multiset.card_singleton, pow_one, mul_smul_comm, TensorProduct.smul_tmul']

/-- The total derivative carries mass weight two on the component space. The scaling
  intertwines the derivative shift up to a factor `c ^ 2`. -/
lemma FieldDerivSpace.massWeightScale_jetDeriv (w : ℕ) (c : ℂ) (μ : Fin 1 ⊕ Fin 3) :
    (FieldDerivSpace.massWeightScale (M := M) w c).comp (FieldDerivSpace.jetDeriv μ)
      = c ^ 2 • (FieldDerivSpace.jetDeriv μ).comp
          (FieldDerivSpace.massWeightScale w c) := by
  have key := fun {W : Type _} [AddCommGroup W] [Module ℂ W]
      (x : SpaceTimeDerivAlgebraℂ ⊗[ℂ] W) => gradeScale_map_mulRight_basis c μ x
  refine LinearMap.ext fun v => Prod.ext ?_ ?_
  · simp only [LinearMap.comp_apply, LinearMap.smul_apply, Prod.smul_fst,
      FieldDerivSpace.massWeightScale_fst, FieldDerivSpace.jetDeriv_fst, map_smul]
    exact (congrArg (fun z : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ M.V => c ^ w • z)
      (key v.1)).trans (smul_comm _ _ _)
  · simp only [LinearMap.comp_apply, LinearMap.smul_apply, Prod.smul_snd,
      FieldDerivSpace.massWeightScale_snd, FieldDerivSpace.jetDeriv_snd, map_smul]
    exact (congrArg (fun z : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (ConjModule M.V) =>
      c ^ w • z) (key v.2)).trans (smul_comm _ _ _)

/-- The mass-weight scaling is natural in the target space. It commutes with every
  pullback, acting as it does on the derivative label and not on the target index. So the
  scaling cannot see which part of a target space a component function came from. In
  `FieldDerivSpace (∀ i, V i)`, where a species enters through
  `comap (LinearMap.proj i)`, every species is scaled by the same weight. This is why the
  generator space of a multi-species theory, `GaugeFieldData.FermionGenerators`, records
  the weights on a direct sum, one per species, rather than on a single component space of
  the product. -/
lemma FieldDerivSpace.comap_comp_massWeightScale (f : M.V →ₗ[ℂ] N.V) (w : ℕ) (c : ℂ) :
    (FieldDerivSpace.comap f).comp (FieldDerivSpace.massWeightScale w c)
      = (FieldDerivSpace.massWeightScale w c).comp (FieldDerivSpace.comap f) := by
  simp only [FieldDerivSpace.comap, FieldDerivSpace.massWeightScale,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.prodMap_comp,
    ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]

/-!

## F. The dual and the conjugate of a finite product

The component space of a direct sum of matter fields splits, and both halves split for the same two
reasons: the dual of a finite product is the product of the duals, and conjugation commutes with
products. Neither statement mentions a matter field, so both are recorded here, on a bare family of
modules; the splitting they add up to is
`GlobalGaugeGroup.MatterField.fieldDerivSpacePiEquiv`, downstream where
`GlobalGaugeGroup.MatterField.pi` is available. The index type must be finite — the dual of an
infinite product is strictly larger than the product of the duals, and `TensorProduct.piRight` is an
equivalence only in the finite case.

-/

section Pi

variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
  [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]

/-- A pair of families is the same thing as a family of pairs. This is the last step of
  the splitting of a component space over a product of target spaces. The two halves split
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

/-- The unconjugated half of the component space of a finite direct sum splits. The
  symbols `∂_s ψ_α` of a `(∀ i, E i)`-valued field are the families, over the index, of
  the symbols of the summands, since the dual distributes over the finite product and the
  derivative label is untouched. -/
noncomputable def FieldDerivSpace.fstPiEquiv :
    (SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (∀ i, E i))
      ≃ₗ[ℂ] ∀ i, SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (E i) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ SpaceTimeDerivAlgebraℂ)
      (LinearMap.lsum ℂ E ℂ).symm).trans
    (TensorProduct.piRight ℂ ℂ SpaceTimeDerivAlgebraℂ fun i => Module.Dual ℂ (E i))

/-- On a pure symbol the splitting restricts the target index to one summand. The
  component `∂_s ψ_α` of the direct sum in the summand `i` is `∂_s` of the covector `φ`
  precomposed with the inclusion of that summand. -/
@[simp]
lemma FieldDerivSpace.fstPiEquiv_tmul (a : SpaceTimeDerivAlgebraℂ)
    (φ : Module.Dual ℂ (∀ i, E i)) (i : ι) :
    fstPiEquiv E (a ⊗ₜ[ℂ] φ) i = a ⊗ₜ[ℂ] (φ ∘ₗ LinearMap.single ℂ E i) := rfl

/-- The conjugate half of the component space of a finite direct sum splits, by the
  same argument applied to the conjugate modules, using that conjugation commutes with
  products. -/
noncomputable def FieldDerivSpace.sndPiEquiv :
    (SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (ConjModule (∀ i, E i)))
      ≃ₗ[ℂ] ∀ i, SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (ConjModule (E i)) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ SpaceTimeDerivAlgebraℂ)
      (((ConjModule.piEquiv (k := ℂ) E).symm.dualMap).trans
        (LinearMap.lsum ℂ (fun i => ConjModule (E i)) ℂ).symm)).trans
    (TensorProduct.piRight ℂ ℂ SpaceTimeDerivAlgebraℂ fun i => Module.Dual ℂ (ConjModule (E i)))

/-- On a pure conjugate symbol the splitting again restricts the target index to one
  summand, the inclusion being read through the conjugation. -/
@[simp]
lemma FieldDerivSpace.sndPiEquiv_tmul (a : SpaceTimeDerivAlgebraℂ)
    (ψ : Module.Dual ℂ (ConjModule (∀ i, E i))) (i : ι) :
    sndPiEquiv E (a ⊗ₜ[ℂ] ψ) i
      = a ⊗ₜ[ℂ] (ψ ∘ₗ ConjModule.map (k := ℂ) (LinearMap.single ℂ E i)) := rfl

/-- The splitting sends the family supported on one summand back to the pullback along
  the projection onto that summand. A component function of the summand `i`, read as a
  component function of the whole, is `φ ∘ proj i`. -/
lemma FieldDerivSpace.fstPiEquiv_symm_single (i : ι)
    (z : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (E i)) :
    (fstPiEquiv E).symm (Pi.single i z)
      = TensorProduct.map LinearMap.id (Module.Dual.transpose (LinearMap.proj i)) z := by
  refine (fstPiEquiv E).injective (funext fun j => ?_)
  rw [LinearEquiv.apply_symm_apply]
  induction z using TensorProduct.inductionOn with
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
lemma FieldDerivSpace.sndPiEquiv_symm_single (i : ι)
    (z : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (ConjModule (E i))) :
    (sndPiEquiv E).symm (Pi.single i z)
      = TensorProduct.map LinearMap.id
          (Module.Dual.transpose (ConjModule.map (k := ℂ) (LinearMap.proj i))) z := by
  refine (sndPiEquiv E).injective (funext fun j => ?_)
  rw [LinearEquiv.apply_symm_apply]
  induction z using TensorProduct.inductionOn with
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
