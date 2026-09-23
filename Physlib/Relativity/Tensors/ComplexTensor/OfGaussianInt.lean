/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
/-!

# Complex Lorentz tensors with Gaussian integer components

A complex Lorentz tensor whose components in the standard basis are Gaussian integers can be
written as `ofGaussianInt f` for a map `f` from component indices to `GaussianInt`. The
product, contraction and permutation of such tensors are again of this form, so identities
between them reduce to decidable equalities of Gaussian integers.

-/

@[expose] public section

open Module
open CategoryTheory
open MonoidalCategory

namespace complexLorentzTensor

open TensorSpecies
open Tensor

/-- A complex Lorentz tensor from a map
  `(Π j, Fin (complexLorentzTensor.repDim (c j))) → GaussianInt`. All complex Lorentz tensors
  with Gaussian integer coefficients with respect to the basis are of this form. -/
noncomputable def ofGaussianInt {n : ℕ} {c : Fin n → complexLorentzTensor.Color} :
    ((ComponentIdx (S := complexLorentzTensor) c) → GaussianInt) →ₛₗ[GaussianInt.toComplex]
      ℂT(c) where
  toFun f := ofComponents c (fun b => GaussianInt.toComplex (f b))
  map_add' f g := by
    rw [← map_add]
    congr 1
    funext b
    simp
  map_smul' r f := by
    rw [← LinearMap.map_smul]
    congr 1
    funext b
    simp

@[simp]
lemma ofGaussianInt_basis_repr_apply {n : ℕ} {c : Fin n → complexLorentzTensor.Color}
    (f : (ComponentIdx c) → GaussianInt)
    (b :(ComponentIdx c)) :
  (Tensor.basis c).repr (ofGaussianInt f) b = GaussianInt.toComplex (f b) := by
  rw [← componentMap_eq_repr]
  simp [ofGaussianInt]

lemma basis_eq_ofGaussianInt {n : ℕ} {c : Fin n → complexLorentzTensor.Color}
    (b : (ComponentIdx c)) :
    Tensor.basis c b
    = ofGaussianInt (fun b' => if b = b' then 1 else 0) := by
  apply (Tensor.basis c).repr.injective
  ext b'
  rw [Basis.repr_self, ofGaussianInt_basis_repr_apply, Finsupp.single_apply]
  split <;> simp

set_option backward.isDefEq.respectTransparency false in
lemma contr_basis_gaussianInt {c : complexLorentzTensor.Color}
    (i : Fin (complexLorentzTensor.repDim c))
    (j : Fin (complexLorentzTensor.repDim (complexLorentzTensor.τ c))) :
      ((complexLorentzTensor.contr c)
      (complexLorentzTensor.basis c i ⊗ₜ
      complexLorentzTensor.basis (complexLorentzTensor.τ c) j))
      = GaussianInt.toComplex (if i.val = j.val then 1 else 0) := by
  match c with
  | Color.upL =>
    change Fermion.leftDualContraction
      (Fermion.LeftHandedWeyl.basis i ⊗ₜ Fermion.DualLeftHandedWeyl.basis j) = _
    rw [Fermion.leftDualContraction_basis]
    simp
  | Color.downL =>
    change Fermion.dualLeftContraction
      (Fermion.DualLeftHandedWeyl.basis i ⊗ₜ Fermion.LeftHandedWeyl.basis j) = _
    rw [Fermion.dualLeftContraction_basis]
    simp
  | Color.upR =>
    change Fermion.rightDualContraction
      (Fermion.RightHandedWeyl.basis i ⊗ₜ Fermion.DualRightHandedWeyl.basis j) = _
    rw [Fermion.rightDualContraction_basis]
    simp
  | Color.downR =>
    change Fermion.rightDualContraction
      (Fermion.RightHandedWeyl.basis i ⊗ₜ Fermion.DualRightHandedWeyl.basis j) = _
    rw [Fermion.rightDualContraction_basis]
    simp
  | Color.up =>
    change Lorentz.contrCoContraction
      (Lorentz.complexContrBasisFin4 i ⊗ₜ Lorentz.complexCoBasisFin4 j) = _
    rw [Lorentz.contrCoContraction_basis]
    simp
  | Color.down =>
    change Lorentz.contrCoContraction
      (Lorentz.complexContrBasisFin4 i ⊗ₜ Lorentz.complexCoBasisFin4 j) = _
    rw [Lorentz.contrCoContraction_basis]
    simp
open TensorSpecies
open Tensor

lemma prodT_ofGaussianInt_ofGaussianInt {n n1 : ℕ} {c : Fin n → complexLorentzTensor.Color}
    (f : (ComponentIdx c) → GaussianInt)
    {c1 : Fin n1 → complexLorentzTensor.Color}
    (f1 : (ComponentIdx c1) → GaussianInt) :
    (prodT (ofGaussianInt f) (ofGaussianInt f1)) =
    ((ofGaussianInt (fun b => f (ComponentIdx.prod b).1 *
      f1 (ComponentIdx.prod b).2))) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [prodT_basis_repr_apply]
  simp only [ofGaussianInt_basis_repr_apply, map_mul]

lemma contrT_ofGaussianInt_eq_sum_dropPairSection {n : ℕ}
    {c : Fin (n + 1 + 1) → complexLorentzTensor.Color}
    {i j : Fin (n + 1 + 1)} {h : i ≠ j ∧ complexLorentzTensor.τ (c i) = c j }
    (f : (ComponentIdx c) → GaussianInt) :
  (contrT n i j h (ofGaussianInt f)) = ((ofGaussianInt (fun b =>
    (∑ x : ComponentIdx.DropPairSection b,
      f x.1 * if (x.1 i).1 = (x.1 j).1 then 1 else 0)))) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [contrT_basis_repr_apply]
  conv_lhs =>
    enter [2, x]
    rw [contr_basis_gaussianInt]
    simp only [Nat.succ_eq_add_one, Finset.univ_eq_attach,
    ofGaussianInt_basis_repr_apply, Fin.val_cast, mul_one,
    mul_zero, Function.comp_apply]
    rw [← GaussianInt.toComplex.map_mul]
  rw [← map_sum GaussianInt.toComplex]
  rw [ofGaussianInt_basis_repr_apply]
  simp [basisIdxCongr_eq_cast]

open ComponentIdx
lemma contrT_ofGaussianInt {n : ℕ} {c : Fin (n + 1 + 1) → complexLorentzTensor.Color}
    {i j : Fin (n + 1 + 1)} {h : i ≠ j ∧ complexLorentzTensor.τ (c i) = c j }
    (f : (ComponentIdx c) → GaussianInt) :
  (contrT n i j h (ofGaussianInt f)) = ((ofGaussianInt (fun b =>
    (∑ x : Fin (complexLorentzTensor.repDim (c i)),
      f (DropPairSection.ofFinEquiv h.1 b (x, Fin.cast (by
        simp [← h.2, complexLorentzTensor.repDim_tau]) x)))))) := by
  rw [contrT_ofGaussianInt_eq_sum_dropPairSection]
  congr
  funext b
  rw [← (DropPairSection.ofFinEquiv h.1 b).sum_comp]
  rw [Fintype.sum_prod_type]
  congr
  funext x
  rw [Finset.sum_eq_single (Fin.cast (by simp [← h.2, repDim_tau]) x)]
  · simp
  · intro y _ hy
    rw [ite_eq_right]
    · simp
    · simp only [DropPairSection.ofFinEquiv_apply_fst, DropPairSection.ofFinEquiv_apply_snd]
      rw [@Fin.ne_iff_vne] at hy
      simp only [Fin.val_cast, ne_eq] at hy
      exact fun a => hy ((Eq.symm a))
  · simp

lemma permT_ofGaussianInt {n m : ℕ} {c : Fin n → complexLorentzTensor.Color}
    {c1 : Fin m → complexLorentzTensor.Color}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ)
    (f : ComponentIdx c → GaussianInt) :
    (permT σ h ((ofGaussianInt f))) =
    ((ofGaussianInt (fun b => f (fun i => Fin.cast (by simp [IsReindexing.inv_perserve_color])
      (b (h.inv σ i)))))) := by
  apply (Tensor.basis _).repr.injective
  ext b
  simp only [permT_basis_repr_symm_apply, ofGaussianInt_basis_repr_apply]
  congr
  ext i
  simp [basisIdxCongr_eq_cast]

end complexLorentzTensor
