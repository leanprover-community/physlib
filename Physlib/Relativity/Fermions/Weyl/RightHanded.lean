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

## Right handed Weyl fermions


In this file we define Right handed Weyl fermions.
These sit in the conjugate representation of `SL(2,ℂ)`,
and we consider them to have up indices `ψ^{\dot α}` with `α = 1,2`.

-/

@[expose] public section

namespace Fermion
noncomputable section

/-- The module in which right handed fermions live. This is equivalent to `Fin 2 → ℂ`. -/
structure RightHandedWeyl where
  /-- The underlying value in `Fin 2 → ℂ`. -/
  val : Fin 2 → ℂ

namespace RightHandedWeyl
open Module Matrix
open MatrixGroups
open Complex
open TensorProduct

/-!

## Underlying module structure

-/

/-- The equivalence between `RightHandedWeyl` and `Fin 2 → ℂ`. -/
def toFin2ℂFun : RightHandedWeyl ≃ (Fin 2 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `RightHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommMonoid RightHandedWeyl := Equiv.addCommMonoid toFin2ℂFun

/-- The instance of `AddCommGroup` on `RightHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommGroup RightHandedWeyl := Equiv.addCommGroup toFin2ℂFun

/-- The additive equivalence between `RightHandedWeyl` and `Fin 2 → ℂ`. -/
def toFin2ℂAddEquiv : RightHandedWeyl ≃+ (Fin 2 → ℂ) :=
  { toFin2ℂFun with map_add' _ _ := rfl }

/-- The instance of `Module` on `RightHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : Module ℂ RightHandedWeyl := AddEquiv.module ℂ toFin2ℂAddEquiv

/-- The linear equivalence between `RightHandedWeyl` and `(Fin 2 → ℂ)`. -/
@[simps!]
def toFin2ℂEquiv : RightHandedWeyl ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := toFin2ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin2ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The underlying element of `Fin 2 → ℂ` of a element in `RightHandedWeyl` defined
  through the linear equivalence `toFin2ℂEquiv`. -/
abbrev toFin2ℂ (ψ : RightHandedWeyl) := toFin2ℂEquiv ψ

lemma toFin2ℂ_eq_val (ψ : RightHandedWeyl) : ψ.toFin2ℂ = ψ.val := rfl

/-!

## Basis

-/

/-- The standard basis on right-handed Weyl fermions. -/
def basis : Basis (Fin 2) ℂ RightHandedWeyl := Basis.ofEquivFun
  (AddEquiv.linearEquiv ℂ RightHandedWeyl.toFin2ℂAddEquiv)

lemma basis_apply (i j : Fin 2) : (basis i).1 j = if j = i then 1 else 0 := by
  simp only [basis, AddEquiv.linearEquiv, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, Basis.coe_ofEquivFun,
    LinearEquiv.symm_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.coe_mk]
  change Pi.single i 1 j = _
  simp [Pi.single_apply]

lemma eq_sum_basis (ψ : RightHandedWeyl) : ψ = ∑ i, ψ.1 i • basis i := by
  conv_lhs => rw [← basis.sum_repr ψ]
  rfl

lemma basis_val (i : Fin 2) : (basis i).val = Pi.single i 1 := by
  ext j
  simp [basis_apply, Pi.single_apply]

/-!

## Representation

-/

/-- The vector space ℂ^2 carrying the conjugate representation of SL(2,C).
  In index notation corresponds to a Weyl fermion with indices ψ^{dot a}. -/
def rep : Representation ℂ SL(2,ℂ) RightHandedWeyl where
  toFun := fun M => {
    toFun := fun (ψ : RightHandedWeyl) =>
      RightHandedWeyl.toFin2ℂEquiv.symm (M.1.map star *ᵥ ψ.toFin2ℂ),
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
    simp only [SpecialLinearGroup.coe_mul, RCLike.star_def, Matrix.map_mul, LinearMap.coe_mk,
      AddHom.coe_mk, Module.End.mul_apply, LinearEquiv.apply_symm_apply, mulVec_mulVec]

lemma rep_apply (M : SL(2,ℂ)) (ψ : RightHandedWeyl) : rep M ψ = ⟨M.1.map star *ᵥ ψ.1⟩ := rfl

lemma rep_apply_eq_sum_basis (M : SL(2,ℂ)) (ψ : RightHandedWeyl) :
    rep M ψ = ∑ i, (∑ j, M.1.map star i j * ψ.1 j) • basis i := by
  rw [eq_sum_basis (rep M ψ)]
  rfl

lemma rep_apply_basis (M : SL(2,ℂ)) (i : Fin 2) :
    rep M (basis i) = ∑ j, M.1.map star j i • basis j := by
  rw [rep_apply_eq_sum_basis]
  congr
  funext j
  simp [basis_apply]

lemma rep_toMatrix (M : SL(2,ℂ)) : (LinearMap.toMatrix basis basis) (rep M) = M.1.map star := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [basis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change (M.1.map star *ᵥ (Pi.single j 1)) i = _
  simp

lemma rep_apply_basis_repr (M : SL(2,ℂ)) (i j : Fin 2) :
    basis.repr (rep M (basis i)) j = star (M.1 j i) := by
  fin_cases j <;> simp [rep_apply_basis]


end RightHandedWeyl

end
end Fermion
