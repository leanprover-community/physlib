/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolai Kashcheev, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Pre.Modules
public import Physlib.Mathematics.RepresentationDual
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
def complexContrBasis : Basis (Fin 1 ⊕ Fin 3) ℂ ContrℂModule :=
  Basis.ofEquivFun ContrℂModule.toFin13ℂEquiv

@[simp]
lemma complexContrBasis_toFin13ℂ (i :Fin 1 ⊕ Fin 3) :
    (complexContrBasis i).toFin13ℂ = Pi.single i 1 := by
  simp only [complexContrBasis, Basis.coe_ofEquivFun]
  rfl

@[simp]
lemma complexContrBasis_ρ_apply (M : SL(2,ℂ)) (i j : Fin 1 ⊕ Fin 3) :
    (LinearMap.toMatrix complexContrBasis complexContrBasis) (ContrℂModule.SL2CRep M) i j =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M)) i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [complexContrBasis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change (((LorentzGroup.toComplex (SL2C.toLorentzGroup M))) *ᵥ (Pi.single j 1)) i = _
  simp

lemma complexContrBasis_ρ_val (M : SL(2,ℂ)) (v : ContrℂModule) :
    ((ContrℂModule.SL2CRep M) v).val =
    LorentzGroup.toComplex (SL2C.toLorentzGroup M) *ᵥ v.val := by
  rfl

/-- The standard basis of complex contravariant Lorentz vectors indexed by `Fin 4`. -/
def complexContrBasisFin4 : Basis (Fin 4) ℂ ContrℂModule :=
  Basis.reindex complexContrBasis finSumFinEquiv

lemma complexContrBasisFin4_eq_reindex :
    complexContrBasisFin4 = complexContrBasis.reindex finSumFinEquiv :=
  rfl

lemma complexContrBasis_reindex_apply_eq_fin4 (j : Fin 4) :
    (complexContrBasis.reindex finSumFinEquiv) j = complexContrBasisFin4 j :=
  rfl

@[simp]
lemma complexContrBasisFin4_apply_zero :
    complexContrBasisFin4 0 = complexContrBasis (Sum.inl 0) := by
  simp only [complexContrBasisFin4, Basis.reindex_apply]
  rfl

@[simp]
lemma complexContrBasisFin4_apply_one :
    complexContrBasisFin4 1 = complexContrBasis (Sum.inr 0) := by
  simp only [complexContrBasisFin4, Basis.reindex_apply]
  rfl

@[simp]
lemma complexContrBasisFin4_apply_two :
    complexContrBasisFin4 2 = complexContrBasis (Sum.inr 1) := by
  simp only [complexContrBasisFin4, Basis.reindex_apply]
  rfl

@[simp]
lemma complexContrBasisFin4_apply_three :
    complexContrBasisFin4 3 = complexContrBasis (Sum.inr 2) := by
  simp only [complexContrBasisFin4, Basis.reindex_apply]
  rfl

@[simp]
lemma complexContrBasisFin4_apply_succ (i : Fin 3) :
    complexContrBasisFin4 i.succ = complexContrBasis (Sum.inr i) := by
  simp only [complexContrBasisFin4, Basis.reindex_apply]
  congr 1
  fin_cases i <;> decide

/-- The standard basis of complex covariant Lorentz vectors. -/
def complexCoBasis : Basis (Fin 1 ⊕ Fin 3) ℂ CoℂModule :=
  Basis.ofEquivFun CoℂModule.toFin13ℂEquiv

@[simp]
lemma complexCoBasis_toFin13ℂ (i :Fin 1 ⊕ Fin 3) : (complexCoBasis i).toFin13ℂ = Pi.single i 1 := by
  simp only [complexCoBasis, Basis.coe_ofEquivFun]
  rfl

@[simp]
lemma complexCoBasis_ρ_apply (M : SL(2,ℂ)) (i j : Fin 1 ⊕ Fin 3) :
    (LinearMap.toMatrix complexCoBasis complexCoBasis) (CoℂModule.SL2CRep M) i j =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [complexCoBasis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply, transpose_apply]
  change ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ *ᵥ (Pi.single j 1)) i = _
  simp

lemma CoℂModule.SL2CRep_val (M : SL(2,ℂ)) (v : CoℂModule) :
    ((CoℂModule.SL2CRep M) v).val =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ *ᵥ v.val := by
  rfl

/-- The dual of the complex covector representation on the dual basis: dual covectors
  transform contravariantly, by the columns of the (complexified) Lorentz matrix. The
  complex analogue of `Lorentz.CoVector.sl2Rep_dual_dualBasis`. -/
lemma CoℂModule.SL2CRep_dual_dualBasis (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) :
    Lorentz.CoℂModule.SL2CRep.dual Λ (Lorentz.complexCoBasis.dualBasis μ) =
      ∑ j, (((Lorentz.SL2C.toLorentzGroup Λ).1 j μ : ℝ) : ℂ) •
        Lorentz.complexCoBasis.dualBasis j := by
  refine Representation.dual_apply_dualBasis _ _ _ _
    (Matrix.of fun l j => (((Lorentz.SL2C.toLorentzGroup Λ).1 j l : ℝ) : ℂ))
    (fun j => ?_)
  have hexp : Lorentz.CoℂModule.SL2CRep Λ⁻¹ (Lorentz.complexCoBasis j) =
      ∑ l, (LinearMap.toMatrix Lorentz.complexCoBasis Lorentz.complexCoBasis
        (Lorentz.CoℂModule.SL2CRep Λ⁻¹)) l j • Lorentz.complexCoBasis l := by
    conv_lhs => rw [← Lorentz.complexCoBasis.sum_repr
      (Lorentz.CoℂModule.SL2CRep Λ⁻¹ (Lorentz.complexCoBasis j))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [LinearMap.toMatrix_apply]
  rw [hexp]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  rw [Lorentz.complexCoBasis_ρ_apply, map_inv, Matrix.transpose_apply,
    ← LorentzGroup.toComplex_inv, Matrix.inv_inv_of_invertible]
  rfl

/-- The standard basis of complex covariant Lorentz vectors indexed by `Fin 4`. -/
def complexCoBasisFin4 : Basis (Fin 4) ℂ CoℂModule :=
  Basis.reindex complexCoBasis finSumFinEquiv

lemma complexCoBasisFin4_eq_reindex :
    complexCoBasisFin4 = complexCoBasis.reindex finSumFinEquiv :=
  rfl

lemma complexCoBasis_reindex_apply_eq_fin4 (j : Fin 4) :
    (complexCoBasis.reindex finSumFinEquiv) j = complexCoBasisFin4 j :=
  rfl

@[simp]
lemma complexCoBasisFin4_apply_zero :
    complexCoBasisFin4 0 = complexCoBasis (Sum.inl 0) := by
  simp only [complexCoBasisFin4, Basis.reindex_apply]
  rfl

@[simp]
lemma complexCoBasisFin4_apply_one :
    complexCoBasisFin4 1 = complexCoBasis (Sum.inr 0) := by
  simp only [complexCoBasisFin4, Basis.reindex_apply]
  rfl

@[simp]
lemma complexCoBasisFin4_apply_two :
    complexCoBasisFin4 2 = complexCoBasis (Sum.inr 1) := by
  simp only [complexCoBasisFin4, Basis.reindex_apply]
  rfl

@[simp]
lemma complexCoBasisFin4_apply_three :
    complexCoBasisFin4 3 = complexCoBasis (Sum.inr 2) := by
  simp only [complexCoBasisFin4, Basis.reindex_apply]
  rfl

/-!

## Relation to real

-/

/-- The semilinear map including real Lorentz vectors into complex contravariant
  lorentz vectors. -/
def inclCongrRealLorentz : ContrMod 3 →ₛₗ[Complex.ofRealHom] ContrℂModule where
  toFun v := {val := ofReal ∘ v.toFin1dℝ}
  map_add' x y := by
    apply Lorentz.ContrℂModule.ext
    rw [Lorentz.ContrℂModule.val_add]
    funext i
    simp only [Function.comp_apply, Pi.add_apply, map_add]
    simp only [ofReal_add]
  map_smul' c x := by
    apply Lorentz.ContrℂModule.ext
    rw [Lorentz.ContrℂModule.val_smul]
    funext i
    simp only [Function.comp_apply, ofRealHom_eq_coe, Pi.smul_apply, _root_.map_smul]
    simp only [smul_eq_mul, ofReal_mul]

lemma inclCongrRealLorentz_val (v : ContrMod 3) :
    (inclCongrRealLorentz v).val = ofRealHom ∘ v.toFin1dℝ := rfl

lemma complexContrBasis_of_real (i : Fin 1 ⊕ Fin 3) :
    (complexContrBasis i) = inclCongrRealLorentz (ContrMod.stdBasis i) := by
  apply Lorentz.ContrℂModule.ext
  simp only [complexContrBasis, Basis.coe_ofEquivFun, inclCongrRealLorentz,
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
    (ContrℂModule.SL2CRep M) (inclCongrRealLorentz v) =
    inclCongrRealLorentz (ContrMod.rep (SL2C.toLorentzGroup M) v) := by
  apply Lorentz.ContrℂModule.ext
  rw [complexContrBasis_ρ_val, inclCongrRealLorentz_val, inclCongrRealLorentz_val]
  rw [LorentzGroup.toComplex_mulVec_ofReal]
  rfl

lemma SL2CRep_ρ_basis (M : SL(2, ℂ)) (i : Fin 1 ⊕ Fin 3) :
    (ContrℂModule.SL2CRep M) (complexContrBasis i) =
    ∑ j, (SL2C.toLorentzGroup M).1 j i •
    complexContrBasis j := by
  rw [complexContrBasis_of_real, inclCongrRealLorentz_ρ]
  rw [Contr.ρ_stdBasis, map_sum]
  apply congrArg
  funext j
  simp only [LinearMap.map_smulₛₗ, ofRealHom_eq_coe, coe_smul]
  rw [complexContrBasis_of_real]

/-- The semilinear map including real Lorentz co-vectors into complex covariant
  Lorentz vectors. -/
def inclCoRealLorentz : CoMod 3 →ₛₗ[Complex.ofRealHom] CoℂModule where
  toFun v := { val := ofReal ∘ v.toFin1dℝ }
  map_add' x y := by
    ext i
    rw [CoℂModule.val_add]
    simp only [Function.comp_apply, Pi.add_apply, map_add]
    simp only [ofReal_add]
  map_smul' c x := by
    ext i
    rw [CoℂModule.val_smul]
    simp only [Function.comp_apply, ofRealHom_eq_coe, Pi.smul_apply, _root_.map_smul]
    simp only [smul_eq_mul, ofReal_mul]

lemma inclCoRealLorentz_val (v : CoMod 3) :
    (inclCoRealLorentz v).val = ofRealHom ∘ v.toFin1dℝ := rfl

lemma complexCoBasis_of_real (i : Fin 1 ⊕ Fin 3) :
    (complexCoBasis i) = inclCoRealLorentz (CoMod.stdBasis i) := by
  apply CoℂModule.ext
  simp only [complexCoBasis, Basis.coe_ofEquivFun, inclCoRealLorentz,
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
    (CoℂModule.SL2CRep M) (inclCoRealLorentz v) =
    inclCoRealLorentz (CoMod.rep (SL2C.toLorentzGroup M) v) := by
  ext i
  rw [CoℂModule.SL2CRep_val, inclCoRealLorentz_val, inclCoRealLorentz_val]
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
