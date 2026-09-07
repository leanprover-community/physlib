/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Physlib.Meta.TODO.Basic
public import Physlib.Relativity.SL2C.Basic
public import Physlib.Meta.Informal.Basic
public import Physlib.Meta.TODO.Basic
/-!

## Dual left handed Weyl fermions


In this file we define dual Left handed Weyl fermions.
These sit in the dual of the fundamental representation of `SL(2,ℂ)`,
and we consider them to have down indices `ψ_α` with `α = 1,2`.

### References

A good reference for the material in this file is:
https://particle.physics.ucdavis.edu/modernsusy/slides/slideimages/spinorfeynrules.pdf
Although a different index convention is used there.

-/

@[expose] public section

namespace Fermion
noncomputable section


/-- The module in which dual-left handed fermions live. This is equivalent to `Fin 2 → ℂ`. -/
structure DualLeftHandedWeyl where
  /-- The underlying value in `Fin 2 → ℂ`. -/
  val : Fin 2 → ℂ

namespace DualLeftHandedWeyl
open Module Matrix
open MatrixGroups
open Complex
open TensorProduct

/-!

## Underlying module structure

-/

/-- The equivalence between `DualLeftHandedWeyl` and `Fin 2 → ℂ`. -/
def toFin2ℂFun : DualLeftHandedWeyl ≃ (Fin 2 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `DualLeftHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommMonoid DualLeftHandedWeyl := Equiv.addCommMonoid toFin2ℂFun

/-- The instance of `AddCommGroup` on `DualLeftHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommGroup DualLeftHandedWeyl := Equiv.addCommGroup toFin2ℂFun

/-- The instance of `Module` on `DualLeftHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : Module ℂ DualLeftHandedWeyl := Equiv.module ℂ toFin2ℂFun

/-- The linear equivalence between `DualLeftHandedWeyl` and `(Fin 2 → ℂ)`. -/
@[simps!]
def toFin2ℂEquiv : DualLeftHandedWeyl ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := toFin2ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin2ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The underlying element of `Fin 2 → ℂ` of a element in `DualLeftHandedWeyl` defined
  through the linear equivalence `toFin2ℂEquiv`. -/
abbrev toFin2ℂ (ψ : DualLeftHandedWeyl) := toFin2ℂEquiv ψ

lemma toFin2ℂ_eq_val (ψ : DualLeftHandedWeyl) : ψ.toFin2ℂ = ψ.val := rfl

/-!

## Basis

-/

/-- The standard basis on dual-left-handed Weyl fermions. -/
def basis : Basis (Fin 2) ℂ DualLeftHandedWeyl := Basis.ofEquivFun
  (Equiv.linearEquiv ℂ DualLeftHandedWeyl.toFin2ℂFun)

lemma basis_apply (i j : Fin 2) : (basis i).1 j = if j = i then 1 else 0 := by
  simp only [basis, Equiv.linearEquiv, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, Basis.coe_ofEquivFun,
    LinearEquiv.symm_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.coe_mk,
    Equiv.addEquiv_symm_apply]
  change Pi.single i 1 j = _
  simp [Pi.single_apply]

lemma eq_sum_basis (ψ : DualLeftHandedWeyl) : ψ = ∑ i, ψ.1 i • basis i := by
  conv_lhs => rw [← basis.sum_repr ψ]
  rfl

lemma basis_val (i : Fin 2) : (basis i).val = Pi.single i 1 := by
  ext j
  simp [basis_apply, Pi.single_apply]

/-!

## Representation

-/

/-- The vector space ℂ^2 carrying the representation of SL(2,C) given by
    M → (M⁻¹)ᵀ. In index notation corresponds to a left-handed Weyl fermion with indices ψ_a. -/
def rep : Representation ℂ SL(2,ℂ) DualLeftHandedWeyl where
  toFun := fun M => {
    toFun := fun (ψ : DualLeftHandedWeyl) =>
      DualLeftHandedWeyl.toFin2ℂEquiv.symm ((M.1⁻¹)ᵀ *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp [mulVec_add]
    map_smul' := by
      intro r ψ
      simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' := fun M N => by
    ext1 x
    simp only [SpecialLinearGroup.coe_mul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply,
      LinearEquiv.apply_symm_apply, mulVec_mulVec, EmbeddingLike.apply_eq_iff_eq]
    refine (congrFun (congrArg _ ?_) _)
    rw [Matrix.mul_inv_rev]
    exact transpose_mul _ _

lemma rep_apply_eq_sum_basis (M : SL(2,ℂ)) (ψ : DualLeftHandedWeyl) :
    rep M ψ = ∑ i, (∑ j, M.1⁻¹ j i * ψ.1 j) • basis i := by
  rw [eq_sum_basis (rep M ψ)]
  rfl

lemma rep_apply_basis (M : SL(2,ℂ)) (i : Fin 2) :
    rep M (basis i) = ∑ j, M.1⁻¹ i j • basis j := by
  rw [rep_apply_eq_sum_basis]
  congr
  funext j
  simp [basis_apply]

lemma rep_toMatrix (M : SL(2,ℂ)) : (LinearMap.toMatrix basis basis) (rep M) = (M.1⁻¹)ᵀ := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [basis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change ((M.1⁻¹)ᵀ *ᵥ (Pi.single j 1)) i = _
  simp

lemma rep_apply_basis_repr (M : SL(2,ℂ)) (i j : Fin 2) :
    basis.repr (rep M (basis i)) j = M.1⁻¹ i j := by
  fin_cases j <;> simp [rep_apply_basis]

end DualLeftHandedWeyl

end
end Fermion
