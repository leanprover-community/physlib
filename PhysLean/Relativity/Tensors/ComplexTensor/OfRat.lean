/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.ComplexTensor.Basic
import PhysLean.Mathematics.RatComplexNum
import PhysLean.Relativity.Tensors.Dual
/-!

# Basis for tensors in a tensor species

-/

open Module IndexNotation
open CategoryTheory
open MonoidalCategory

namespace complexLorentzTensor
open OverColor
open PhysLean.RatComplexNum
open PhysLean

open TensorSpecies
open Tensor

/--A complex Lorentz tensor from a map
  `(Π j, Fin (complexLorentzTensor.repDim (c j))) → RatComplexNum`. All
  complex Lorentz tensors with rational coefficients with respect to the basis are of this
  form. -/
noncomputable def ofRat {n : ℕ} {c : Fin n → complexLorentzTensor.Color} :
    ((ComponentIdx (S := complexLorentzTensor) c) → RatComplexNum) →ₛₗ[toComplexNum] ℂT(c) where
  toFun f := (Tensor.basis c).repr.symm <|
    (Finsupp.linearEquivFunOnFinite ℂ ℂ
    ((j : Fin n) → Fin (complexLorentzTensor.repDim (c j)))).symm <|
    (fun j => toComplexNum (f j))
  map_add' f f1 := by
    apply (Tensor.basis _).repr.injective
    ext b
    simp
  map_smul' r f := by
    apply (Tensor.basis _).repr.injective
    ext b
    simp

@[simp]
lemma ofRat_basis_repr_apply {n : ℕ} {c : Fin n → complexLorentzTensor.Color}
    (f : (ComponentIdx c) → RatComplexNum)
    (b :(ComponentIdx c)) :
  (Tensor.basis c).repr (ofRat f) b = toComplexNum (f b) := by
  simp [ofRat]

lemma basis_eq_ofRat {n : ℕ} {c : Fin n → complexLorentzTensor.Color}
    (b : (ComponentIdx c)) :
    Tensor.basis c b
    = ofRat (fun b' => if b = b' then ⟨1, 0⟩ else ⟨0, 0⟩) := by
  apply (Tensor.basis c).repr.injective
  simp only [Basis.repr_self]
  ext b'
  simp only [ofRat_basis_repr_apply]
  rw [Finsupp.single_apply, toComplexNum]
  simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  split
  simp only [Rat.cast_one, Rat.cast_zero, zero_mul, add_zero]
  simp

lemma contr_basis_ratComplexNum {c : complexLorentzTensor.Color}
    (i : Fin (complexLorentzTensor.repDim c))
    (j : Fin (complexLorentzTensor.repDim (complexLorentzTensor.τ c))) :
    complexLorentzTensor.castToField
      ((complexLorentzTensor.contr.app (Discrete.mk c)).hom
      (complexLorentzTensor.basis c i ⊗ₜ
      complexLorentzTensor.basis (complexLorentzTensor.τ c) j))
      = toComplexNum (if i.val = j.val then 1 else 0) := by
  match c with
  | Color.upL =>
    change Fermion.leftAltContraction.hom (Fermion.leftBasis i ⊗ₜ Fermion.altLeftBasis j) = _
    rw [Fermion.leftAltContraction_basis]
    simp
  | Color.downL =>
    change Fermion.altLeftContraction.hom (Fermion.altLeftBasis i ⊗ₜ Fermion.leftBasis j) = _
    rw [Fermion.altLeftContraction_basis]
    simp
  | Color.upR =>
    change Fermion.rightAltContraction.hom (Fermion.rightBasis i ⊗ₜ Fermion.altRightBasis j) = _
    rw [Fermion.rightAltContraction_basis]
    simp
  | Color.downR =>
    change Fermion.rightAltContraction.hom (Fermion.rightBasis i ⊗ₜ Fermion.altRightBasis j) = _
    rw [Fermion.rightAltContraction_basis]
    simp
  | Color.up =>
    change Lorentz.contrCoContraction.hom
      (Lorentz.complexContrBasisFin4 i ⊗ₜ Lorentz.complexCoBasisFin4 j) = _
    rw [Lorentz.contrCoContraction_basis]
    simp
  | Color.down =>
    change Lorentz.contrCoContraction.hom
      (Lorentz.complexContrBasisFin4 i ⊗ₜ Lorentz.complexCoBasisFin4 j) = _
    rw [Lorentz.contrCoContraction_basis]
    simp
open TensorSpecies
open Tensor

lemma prodT_ofRat_ofRat {n n1 : ℕ} {c : Fin n → complexLorentzTensor.Color}
    (f : (ComponentIdx c) → RatComplexNum)
    {c1 : Fin n1 → complexLorentzTensor.Color}
    (f1 : (ComponentIdx c1) → RatComplexNum) :
    (prodT (ofRat f) (ofRat f1)) =
    ((ofRat (fun b => f (ComponentIdx.prodEquiv b).1 *
      f1 (ComponentIdx.prodEquiv b).2))) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [prodT_basis_repr_apply]
  simp only [ofRat_basis_repr_apply, map_mul]

lemma contrT_ofRat_eq_sum_dropPairSection {n : ℕ} {c : Fin (n + 1 + 1) → complexLorentzTensor.Color}
    {i j : Fin (n + 1 + 1)} {h : i ≠ j ∧ complexLorentzTensor.τ (c i) = c j }
    (f : (ComponentIdx c) → RatComplexNum) :
  (contrT n i j h (ofRat f)) = ((ofRat (fun b =>
    (∑ x : ComponentIdx.DropPairSection b,
      f x.1 * if (x.1 i).1 = (x.1 j).1 then 1 else 0)))) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [contrT_basis_repr_apply]
  conv_lhs =>
    enter [2, x]
    rw [contr_basis_ratComplexNum]
    simp only [Nat.succ_eq_add_one, Finset.univ_eq_attach,
    ofRat_basis_repr_apply, Fin.val_cast, mul_one,
    mul_zero, Function.comp_apply]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  rw [← map_sum PhysLean.RatComplexNum.toComplexNum]
  erw [ofRat_basis_repr_apply]

open ComponentIdx
lemma contrT_ofRat {n : ℕ} {c : Fin (n + 1 + 1) → complexLorentzTensor.Color}
    {i j : Fin (n + 1 + 1)} {h : i ≠ j ∧ complexLorentzTensor.τ (c i) = c j }
    (f : (ComponentIdx c) → RatComplexNum) :
  (contrT n i j h (ofRat f)) = ((ofRat (fun b =>
    (∑ x : Fin (complexLorentzTensor.repDim (c i)),
      f (DropPairSection.ofFinEquiv h.1 b (x, Fin.cast (by simp [← h.2]) x)))))) := by
  rw [contrT_ofRat_eq_sum_dropPairSection]
  congr
  funext b
  rw [← (DropPairSection.ofFinEquiv h.1 b).sum_comp]
  rw [Fintype.sum_prod_type]
  congr
  funext x
  rw [Finset.sum_eq_single (Fin.cast (by simp [← h.2]) x)]
  · simp
  · intro y _ hy
    rw [if_neg]
    · simp
    · simp only [DropPairSection.ofFinEquiv_apply_fst, DropPairSection.ofFinEquiv_apply_snd]
      rw [@Fin.ne_iff_vne] at hy
      simp only [Fin.val_cast, ne_eq] at hy
      exact fun a => hy ((Eq.symm a))
  · simp

lemma permT_ofRat {n m : ℕ} {c : Fin n → complexLorentzTensor.Color}
    {c1 : Fin m → complexLorentzTensor.Color}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ)
    (f : ComponentIdx c → RatComplexNum) :
    (permT σ h ((ofRat f))) =
    ((ofRat (fun b => f (fun i => Fin.cast (by simp [PermCond.inv_perserve_color])
      (b (h.inv σ i)))))) := by
  apply (Tensor.basis _).repr.injective
  ext b
  simp only [permT_basis_repr_symm_apply, ofRat_basis_repr_apply]

end complexLorentzTensor
