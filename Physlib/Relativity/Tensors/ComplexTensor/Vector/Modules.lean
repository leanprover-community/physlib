/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolai Kashcheev, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.SL2C.Basic
/-!

## Modules associated with complex Lorentz vectors

We define the modules underlying complex Lorentz vectors.
These definitions are preludes to the definitions of
`Lorentz.complexContr` and `Lorentz.complexCo`.

-/

@[expose] public section

namespace Lorentz

noncomputable section
open Matrix
open MatrixGroups
open Complex

/-- The module for contravariant (up-index) complex Lorentz vectors. -/
structure ComplexVector where
  /-- The underlying value as a vector `Fin 1 ⊕ Fin 3 → ℂ`. -/
  val : Fin 1 ⊕ Fin 3 → ℂ

namespace ComplexVector

/-- The equivalence between `ComplexVector` and `Fin 1 ⊕ Fin 3 → ℂ`. -/
def toFin13ℂFun : ComplexVector ≃ (Fin 1 ⊕ Fin 3 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `ComplexVector` defined via its equivalence
  with `Fin 1 ⊕ Fin 3 → ℂ`. -/
instance : AddCommMonoid ComplexVector := Equiv.addCommMonoid toFin13ℂFun

/-- The instance of `AddCommGroup` on `ComplexVector` defined via its equivalence
  with `Fin 1 ⊕ Fin 3 → ℂ`. -/
instance : AddCommGroup ComplexVector := Equiv.addCommGroup toFin13ℂFun

/-- The additive equivalence between `ComplexVector` and `Fin 1 ⊕ Fin 3 → ℂ`. -/
def toFin13ℂAddEquiv : ComplexVector ≃+ (Fin 1 ⊕ Fin 3 → ℂ) :=
  { toFin13ℂFun with map_add' _ _ := rfl }

/-- The instance of `Module` on `ComplexVector` defined via its equivalence
  with `Fin 1 ⊕ Fin 3 → ℂ`. -/
instance : Module ℂ ComplexVector := AddEquiv.module ℂ toFin13ℂAddEquiv

@[ext]
lemma ext (ψ ψ' : ComplexVector) (h : ψ.val = ψ'.val) : ψ = ψ' := by
  cases ψ
  cases ψ'
  subst h
  rfl

@[simp]
lemma val_add (ψ ψ' : ComplexVector) : (ψ + ψ').val = ψ.val + ψ'.val := rfl

@[simp]
lemma val_smul (r : ℂ) (ψ : ComplexVector) : (r • ψ).val = r • ψ.val := rfl

/-- The linear equivalence between `ComplexVector` and `(Fin 1 ⊕ Fin 3 → ℂ)`. -/
@[simps!]
def toFin13ℂEquiv : ComplexVector ≃ₗ[ℂ] (Fin 1 ⊕ Fin 3 → ℂ) :=
  AddEquiv.linearEquiv ℂ toFin13ℂAddEquiv

/-- The underlying element of `Fin 1 ⊕ Fin 3 → ℂ` of a element in `ComplexVector` defined
  through the linear equivalence `toFin13ℂEquiv`. -/
abbrev toFin13ℂ (ψ : ComplexVector) := toFin13ℂEquiv ψ

/-- The representation of the Lorentz group on `ComplexVector`. -/
def lorentzGroupRep : Representation ℂ (LorentzGroup 3) ComplexVector where
  toFun M := {
      toFun := fun v => toFin13ℂEquiv.symm (LorentzGroup.toComplex M *ᵥ v.toFin13ℂ),
      map_add' := by
        intro ψ ψ'
        simp [mulVec_add]
      map_smul' := by
        intro r ψ
        simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' M N := by
    ext i
    simp

/-- The representation of the SL(2, ℂ) on `ComplexVector` induced by the representation of the
  Lorentz group. -/
def SL2CRep : Representation ℂ SL(2, ℂ) ComplexVector :=
  MonoidHom.comp lorentzGroupRep Lorentz.SL2C.toLorentzGroup

end ComplexVector

/-- The module for covariant (up-index) complex Lorentz vectors. -/
structure ComplexCoVector where
  /-- The underlying value as a vector `Fin 1 ⊕ Fin 3 → ℂ`. -/
  val : Fin 1 ⊕ Fin 3 → ℂ

namespace ComplexCoVector

/-- The equivalence between `ComplexCoVector` and `Fin 1 ⊕ Fin 3 → ℂ`. -/
def toFin13ℂFun : ComplexCoVector ≃ (Fin 1 ⊕ Fin 3 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `ComplexCoVector` defined via its equivalence
  with `Fin 1 ⊕ Fin 3 → ℂ`. -/
instance : AddCommMonoid ComplexCoVector := Equiv.addCommMonoid toFin13ℂFun

/-- The instance of `AddCommGroup` on `ComplexCoVector` defined via its equivalence
  with `Fin 1 ⊕ Fin 3 → ℂ`. -/
instance : AddCommGroup ComplexCoVector := Equiv.addCommGroup toFin13ℂFun

/-- The additive equivalence between `ComplexCoVector` and `Fin 1 ⊕ Fin 3 → ℂ`. -/
def toFin13ℂAddEquiv : ComplexCoVector ≃+ (Fin 1 ⊕ Fin 3 → ℂ) :=
  { toFin13ℂFun with map_add' _ _ := rfl }

/-- The instance of `Module` on `ComplexCoVector` defined via its equivalence
  with `Fin 1 ⊕ Fin 3 → ℂ`. -/
instance : Module ℂ ComplexCoVector := AddEquiv.module ℂ toFin13ℂAddEquiv

@[ext]
lemma ext (ψ ψ' : ComplexCoVector) (h : ψ.val = ψ'.val) : ψ = ψ' := by
  cases ψ
  cases ψ'
  subst h
  rfl

@[simp]
lemma val_add (ψ ψ' : ComplexCoVector) : (ψ + ψ').val = ψ.val + ψ'.val := rfl

@[simp]
lemma val_smul (r : ℂ) (ψ : ComplexCoVector) : (r • ψ).val = r • ψ.val := rfl

/-- The linear equivalence between `ComplexCoVector` and `(Fin 1 ⊕ Fin 3 → ℂ)`. -/
@[simps!]
def toFin13ℂEquiv : ComplexCoVector ≃ₗ[ℂ] (Fin 1 ⊕ Fin 3 → ℂ) :=
  AddEquiv.linearEquiv ℂ toFin13ℂAddEquiv

/-- The underlying element of `Fin 1 ⊕ Fin 3 → ℂ` of a element in `ComplexCoVector` defined
  through the linear equivalence `toFin13ℂEquiv`. -/
abbrev toFin13ℂ (ψ : ComplexCoVector) := toFin13ℂEquiv ψ

/-- The representation of the Lorentz group on `ComplexCoVector`. -/
def lorentzGroupRep : Representation ℂ (LorentzGroup 3) ComplexCoVector where
  toFun M := {
      toFun := fun v => toFin13ℂEquiv.symm ((LorentzGroup.toComplex M)⁻¹ᵀ *ᵥ v.toFin13ℂ),
      map_add' := by
        intro ψ ψ'
        simp [mulVec_add]
      map_smul' := by
        intro r ψ
        simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' M N := by
    ext1 x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply,
      LinearEquiv.apply_symm_apply, mulVec_mulVec, EmbeddingLike.apply_eq_iff_eq]
    refine (congrFun (congrArg _ ?_) _)
    simp only [_root_.map_mul]
    rw [Matrix.mul_inv_rev]
    exact transpose_mul _ _

/-- The representation of the SL(2, ℂ) on `ComplexCoVector` induced by the representation of the
  Lorentz group. -/
def SL2CRep : Representation ℂ SL(2, ℂ) ComplexCoVector :=
  MonoidHom.comp lorentzGroupRep Lorentz.SL2C.toLorentzGroup

end ComplexCoVector

end
end Lorentz
