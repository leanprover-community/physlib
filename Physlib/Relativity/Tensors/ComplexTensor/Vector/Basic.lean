/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolai Kashcheev, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Modules
/-!

# Complex Lorentz vectors

We define complex Lorentz vectors in 4d space-time as representations of SL(2, C).

-/

@[expose] public section

noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct

namespace Lorentz

/-- The standard basis of complex contravariant Lorentz vectors. -/
def ComplexVector.basis : Basis (Fin 1 ⊕ Fin 3) ℂ ComplexVector :=
  Basis.ofEquivFun ComplexVector.toFin13ℂEquiv

@[simp]
lemma ComplexVector.basis_toFin13ℂ (i :Fin 1 ⊕ Fin 3) :
    (ComplexVector.basis i).toFin13ℂ = Pi.single i 1 := by
  simp only [ComplexVector.basis, Basis.coe_ofEquivFun]
  rfl

@[simp]
lemma ComplexVector.basis_ρ_apply (M : SL(2,ℂ)) (i j : Fin 1 ⊕ Fin 3) :
    (LinearMap.toMatrix ComplexVector.basis ComplexVector.basis) (ComplexVector.SL2CRep M) i j =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M)) i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [ComplexVector.basis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change (((LorentzGroup.toComplex (SL2C.toLorentzGroup M))) *ᵥ (Pi.single j 1)) i = _
  simp

lemma ComplexVector.basis_ρ_val (M : SL(2,ℂ)) (v : ComplexVector) :
    ((ComplexVector.SL2CRep M) v).val =
    LorentzGroup.toComplex (SL2C.toLorentzGroup M) *ᵥ v.val := by
  rfl

/-- The standard basis of complex contravariant Lorentz vectors indexed by `Fin 4`. -/
def ComplexVector.basisFin4 : Basis (Fin 4) ℂ ComplexVector :=
  Basis.reindex ComplexVector.basis finSumFinEquiv

lemma ComplexVector.basisFin4_eq_reindex :
    ComplexVector.basisFin4 = ComplexVector.basis.reindex finSumFinEquiv :=
  rfl

lemma ComplexVector.basis_reindex_apply_eq_fin4 (j : Fin 4) :
    (ComplexVector.basis.reindex finSumFinEquiv) j = ComplexVector.basisFin4 j :=
  rfl

@[simp]
lemma ComplexVector.basisFin4_apply_zero :
    ComplexVector.basisFin4 0 = ComplexVector.basis (Sum.inl 0) := by
  simp only [ComplexVector.basisFin4, Basis.reindex_apply]
  rfl

@[simp]
lemma ComplexVector.basisFin4_apply_one :
    ComplexVector.basisFin4 1 = ComplexVector.basis (Sum.inr 0) := by
  simp only [ComplexVector.basisFin4, Basis.reindex_apply]
  rfl

@[simp]
lemma ComplexVector.basisFin4_apply_two :
    ComplexVector.basisFin4 2 = ComplexVector.basis (Sum.inr 1) := by
  simp only [ComplexVector.basisFin4, Basis.reindex_apply]
  rfl

@[simp]
lemma ComplexVector.basisFin4_apply_three :
    ComplexVector.basisFin4 3 = ComplexVector.basis (Sum.inr 2) := by
  simp only [ComplexVector.basisFin4, Basis.reindex_apply]
  rfl

@[simp]
lemma ComplexVector.basisFin4_apply_succ (i : Fin 3) :
    ComplexVector.basisFin4 i.succ = ComplexVector.basis (Sum.inr i) := by
  simp only [ComplexVector.basisFin4, Basis.reindex_apply]
  congr 1
  fin_cases i <;> decide

/-- The standard basis of complex covariant Lorentz vectors. -/
def ComplexCoVector.basis : Basis (Fin 1 ⊕ Fin 3) ℂ ComplexCoVector :=
  Basis.ofEquivFun ComplexCoVector.toFin13ℂEquiv

@[simp]
lemma ComplexCoVector.basis_toFin13ℂ (i :Fin 1 ⊕ Fin 3) :
    (ComplexCoVector.basis i).toFin13ℂ = Pi.single i 1 := by
  simp only [ComplexCoVector.basis, Basis.coe_ofEquivFun]
  rfl

@[simp]
lemma ComplexCoVector.basis_ρ_apply (M : SL(2,ℂ)) (i j : Fin 1 ⊕ Fin 3) :
    (LinearMap.toMatrix ComplexCoVector.basis ComplexCoVector.basis)
      (ComplexCoVector.SL2CRep M) i j =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [ComplexCoVector.basis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply,
    transpose_apply]
  change ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ *ᵥ (Pi.single j 1)) i = _
  simp

lemma ComplexCoVector.SL2CRep_val (M : SL(2,ℂ)) (v : ComplexCoVector) :
    ((ComplexCoVector.SL2CRep M) v).val =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ *ᵥ v.val := by
  rfl

/-- The standard basis of complex covariant Lorentz vectors indexed by `Fin 4`. -/
def ComplexCoVector.basisFin4 : Basis (Fin 4) ℂ ComplexCoVector :=
  Basis.reindex ComplexCoVector.basis finSumFinEquiv

lemma ComplexCoVector.basisFin4_eq_reindex :
    ComplexCoVector.basisFin4 = ComplexCoVector.basis.reindex finSumFinEquiv :=
  rfl

lemma ComplexCoVector.basis_reindex_apply_eq_fin4 (j : Fin 4) :
    (ComplexCoVector.basis.reindex finSumFinEquiv) j = ComplexCoVector.basisFin4 j :=
  rfl

@[simp]
lemma ComplexCoVector.basisFin4_apply_zero :
    ComplexCoVector.basisFin4 0 = ComplexCoVector.basis (Sum.inl 0) := by
  simp only [ComplexCoVector.basisFin4, Basis.reindex_apply]
  rfl

@[simp]
lemma ComplexCoVector.basisFin4_apply_one :
    ComplexCoVector.basisFin4 1 = ComplexCoVector.basis (Sum.inr 0) := by
  simp only [ComplexCoVector.basisFin4, Basis.reindex_apply]
  rfl

@[simp]
lemma ComplexCoVector.basisFin4_apply_two :
    ComplexCoVector.basisFin4 2 = ComplexCoVector.basis (Sum.inr 1) := by
  simp only [ComplexCoVector.basisFin4, Basis.reindex_apply]
  rfl

@[simp]
lemma ComplexCoVector.basisFin4_apply_three :
    ComplexCoVector.basisFin4 3 = ComplexCoVector.basis (Sum.inr 2) := by
  simp only [ComplexCoVector.basisFin4, Basis.reindex_apply]
  rfl

/-!

## Relation to real

-/

/-- The semilinear map including real Lorentz vectors into complex contravariant
  lorentz vectors. -/
def inclCongrRealLorentz : ContrMod 3 →ₛₗ[Complex.ofRealHom] ComplexVector where
  toFun v := {val := ofReal ∘ v.toFin1dℝ}
  map_add' x y := by
    apply Lorentz.ComplexVector.ext
    rw [Lorentz.ComplexVector.val_add]
    funext i
    simp only [Function.comp_apply, Pi.add_apply, map_add]
    simp only [ofReal_add]
  map_smul' c x := by
    apply Lorentz.ComplexVector.ext
    rw [Lorentz.ComplexVector.val_smul]
    funext i
    simp only [Function.comp_apply, ofRealHom_eq_coe, Pi.smul_apply, _root_.map_smul]
    simp only [smul_eq_mul, ofReal_mul]

lemma inclCongrRealLorentz_val (v : ContrMod 3) :
    (inclCongrRealLorentz v).val = ofRealHom ∘ v.toFin1dℝ := rfl

lemma ComplexVector.basis_of_real (i : Fin 1 ⊕ Fin 3) :
    (ComplexVector.basis i) = inclCongrRealLorentz (ContrMod.stdBasis i) := by
  apply Lorentz.ComplexVector.ext
  simp only [ComplexVector.basis, Basis.coe_ofEquivFun, inclCongrRealLorentz,
    LinearMap.coe_mk, AddHom.coe_mk]
  ext j
  simp only [Function.comp_apply]
  change (Pi.single i 1) j = _
  by_cases h : i = j
  · subst h
    rw [ContrMod.toFin1dℝ, ContrMod.stdBasis_toFin1dℝEquiv_apply_same]
    simp
  · rw [ContrMod.toFin1dℝ, ContrMod.stdBasis_toFin1dℝEquiv_apply_ne h]
    simp [h]

lemma inclCongrRealLorentz_ρ (M : SL(2, ℂ)) (v : ContrMod 3) :
    (ComplexVector.SL2CRep M) (inclCongrRealLorentz v) =
    inclCongrRealLorentz (ContrMod.rep (SL2C.toLorentzGroup M) v) := by
  apply Lorentz.ComplexVector.ext
  rw [ComplexVector.basis_ρ_val, inclCongrRealLorentz_val, inclCongrRealLorentz_val]
  rw [LorentzGroup.toComplex_mulVec_ofReal]
  rfl

lemma SL2CRep_ρ_basis (M : SL(2, ℂ)) (i : Fin 1 ⊕ Fin 3) :
    (ComplexVector.SL2CRep M) (ComplexVector.basis i) =
    ∑ j, (SL2C.toLorentzGroup M).1 j i •
    ComplexVector.basis j := by
  rw [ComplexVector.basis_of_real, inclCongrRealLorentz_ρ]
  rw [Contr.ρ_stdBasis, map_sum]
  apply congrArg
  funext j
  simp only [LinearMap.map_smulₛₗ, ofRealHom_eq_coe, coe_smul]
  rw [ComplexVector.basis_of_real]

/-- The semilinear map including real Lorentz co-vectors into complex covariant
  Lorentz vectors. -/
def inclCoRealLorentz : CoMod 3 →ₛₗ[Complex.ofRealHom] ComplexCoVector where
  toFun v := { val := ofReal ∘ v.toFin1dℝ }
  map_add' x y := by
    ext i
    rw [ComplexCoVector.val_add]
    simp only [Function.comp_apply, Pi.add_apply, map_add]
    simp only [ofReal_add]
  map_smul' c x := by
    ext i
    rw [ComplexCoVector.val_smul]
    simp only [Function.comp_apply, ofRealHom_eq_coe, Pi.smul_apply, _root_.map_smul]
    simp only [smul_eq_mul, ofReal_mul]

lemma inclCoRealLorentz_val (v : CoMod 3) :
    (inclCoRealLorentz v).val = ofRealHom ∘ v.toFin1dℝ := rfl

lemma ComplexCoVector.basis_of_real (i : Fin 1 ⊕ Fin 3) :
    (ComplexCoVector.basis i) = inclCoRealLorentz (CoMod.stdBasis i) := by
  apply ComplexCoVector.ext
  simp only [ComplexCoVector.basis, Basis.coe_ofEquivFun, inclCoRealLorentz,
    LinearMap.coe_mk, AddHom.coe_mk]
  ext j
  simp only [Function.comp_apply]
  change (Pi.single i 1) j = _
  by_cases h : i = j
  · subst h
    rw [CoMod.toFin1dℝ, CoMod.stdBasis_toFin1dℝEquiv_apply_same]
    simp
  · rw [CoMod.toFin1dℝ, CoMod.stdBasis_toFin1dℝEquiv_apply_ne h]
    simp [h]

lemma inclCoRealLorentz_ρ (M : SL(2, ℂ)) (v : CoMod 3) :
    (ComplexCoVector.SL2CRep M) (inclCoRealLorentz v) =
    inclCoRealLorentz (CoMod.rep (SL2C.toLorentzGroup M) v) := by
  ext i
  rw [ComplexCoVector.SL2CRep_val, inclCoRealLorentz_val, inclCoRealLorentz_val]
  change ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ *ᵥ
      (ofRealHom ∘ v.toFin1dℝ)) i =
    (ofRealHom ∘ ((LorentzGroup.transpose (SL2C.toLorentzGroup M)⁻¹).1 *ᵥ
      v.toFin1dℝ)) i
  rw [LorentzGroup.toComplex_inv]
  change (LorentzGroup.toComplex (LorentzGroup.transpose (SL2C.toLorentzGroup M)⁻¹) *ᵥ
      (ofRealHom ∘ v.toFin1dℝ)) i =
    (ofRealHom ∘ ((LorentzGroup.transpose (SL2C.toLorentzGroup M)⁻¹).1 *ᵥ
      v.toFin1dℝ)) i
  rw [LorentzGroup.toComplex_mulVec_ofReal]

end Lorentz
end
