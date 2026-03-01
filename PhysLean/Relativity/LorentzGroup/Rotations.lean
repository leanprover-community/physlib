/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.LorentzGroup.Boosts.Generalized
/-!
# Rotations

In this module we define rotations of in the Lorentz group.

-/

noncomputable section

namespace LorentzGroup

/-- The subgroup of rotations of the Lorentz group. -/
def Rotations (d) : Subgroup (LorentzGroup d) where
  carrier Λ := Λ.1 (Sum.inl 0) (Sum.inl 0) = 1 ∧ IsProper Λ
  mul_mem' {Λ₁ Λ₂} h1 h2 := by
    constructor
    · rw [← toVector_timeComponent]
      rw [toVector_mul]
      have h : toVector Λ₂ = Lorentz.Vector.basis (Sum.inl 0) := by
        rw [toVector_eq_basis_iff_timeComponent_eq_one, h2.1]
      rw [h]
      simp [Lorentz.Vector.timeComponent]
      rw [Lorentz.Vector.smul_eq_mulVec]
      rw [Matrix.mulVec_eq_sum]
      simp only [Fin.isValue, Lorentz.Vector.basis_apply, op_smul_eq_smul, ite_smul, one_smul,
        zero_smul, Finset.sum_apply, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
        Sum.inl.injEq, Finset.sum_singleton, ↓reduceIte, Matrix.transpose_apply, reduceCtorEq,
        Pi.ofNat_apply, Finset.sum_const_zero, add_zero]
      rw [h1.1]
    · exact isProper_mul h1.2 h2.2
  one_mem' := by
    constructor
    · simp
    · simp
  inv_mem' {Λ} h := by
    constructor
    · simp [inv_eq_dual, minkowskiMatrix.dual_apply, h.1]
    · simpa [inv_eq_dual, IsProper] using h.2

lemma mem_rotations_iff {d} (Λ : LorentzGroup d) :
    Λ ∈ Rotations d ↔ Λ.1 (Sum.inl 0) (Sum.inl 0) = 1 ∧ IsProper Λ := by
  rfl

@[simp]
lemma transpose_mem_rotations {d} (Λ : LorentzGroup d) :
    transpose Λ ∈ Rotations d ↔ Λ ∈ Rotations d := by
  simp [mem_rotations_iff, LorentzGroup.transpose_val, IsProper]

/-- The group homomorphism from the special orthogonal group to the Lorentz group. -/
def ofSpecialOrthogonal {d} :
    Matrix.specialOrthogonalGroup (Fin d) ℝ ≃* Rotations d where
  toFun A := ⟨⟨Matrix.fromBlocks 1 0 0 A, by
    rw [LorentzGroup.mem_iff_dual_mul_self]
    simp only [minkowskiMatrix.dual, minkowskiMatrix.as_block, Matrix.fromBlocks_transpose,
      Matrix.transpose_one, Matrix.transpose_zero, Matrix.fromBlocks_multiply, mul_one,
      Matrix.mul_zero, add_zero, Matrix.zero_mul, Matrix.mul_one, neg_mul, one_mul, zero_add,
      Matrix.mul_neg, neg_zero, mul_neg, neg_neg]
    have ha := A.2
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff'] at ha
    rw [ha.1]
    simp⟩, by
      simp [mem_rotations_iff]
      have hA := A.2
      rw [Matrix.mem_specialOrthogonalGroup_iff] at hA
      exact hA.2⟩
  invFun Λ := ⟨fun i j => Λ.1.1 (Sum.inr i) (Sum.inr j),
    by
    match Λ with
    | ⟨Λ, h⟩ =>
    let M : Matrix (Fin d) (Fin d) ℝ := fun i j => Λ.1 (Sum.inr i) (Sum.inr j)
    have h1 : Matrix.fromBlocks 1 0 0 M = Λ.1 := by
      have h1 : LorentzGroup.toVector Λ = Lorentz.Vector.basis (Sum.inl 0) := by
        rw [LorentzGroup.toVector_eq_basis_iff_timeComponent_eq_one]
        exact h.1
      have h2 : LorentzGroup.toVector (LorentzGroup.transpose Λ) =
          Lorentz.Vector.basis (Sum.inl 0) := by
        rw [LorentzGroup.toVector_eq_basis_iff_timeComponent_eq_one]
        exact h.1
      funext i j
      match i, j with
      | .inl 0, .inl 0 => simp [h.1]
      | .inl 0, .inr j =>
        simp only [Fin.isValue, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
        trans (Lorentz.Vector.basis (Sum.inl 0)) (Sum.inr j)
        · simp
        rw [← h2]
        simp [LorentzGroup.transpose_val]
      | .inr i, .inl 0 =>
        simp only [Fin.isValue, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
        trans (Lorentz.Vector.basis (Sum.inl 0)) (Sum.inr i)
        · simp
        rw [← h1]
        simp
      | .inr i, .inr j => rfl
    · rw [Matrix.mem_specialOrthogonalGroup_iff]
      constructor
      · rw [Matrix.mem_orthogonalGroup_iff]
        have hΛ := Λ.2
        rw [mem_iff_self_mul_dual, ← h1] at hΛ
        simp [minkowskiMatrix.dual] at hΛ
        rw [minkowskiMatrix.as_block] at hΛ
        simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply] at hΛ
        ext i j
        trans (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 (M * M.transpose))
          (Sum.inr i) (Sum.inr j)
        · simp [M]
        · rw [hΛ, Matrix.one_apply, Matrix.one_apply]
          simp
      · trans Λ.1.det
        · rw [← h1]
          simp
        · exact h.2⟩
  map_mul' A B := by
    apply Subtype.ext
    simp only [Submonoid.coe_mul, MulMemClass.mk_mul_mk]
    apply Subtype.ext
    simp [Matrix.fromBlocks_multiply]
  left_inv Λ := by
    simp
  right_inv Λ := by
    match Λ with
    | ⟨Λ, h⟩ =>
    let M : Matrix (Fin d) (Fin d) ℝ := fun i j => Λ.1 (Sum.inr i) (Sum.inr j)
    have h1 : Matrix.fromBlocks 1 0 0 M = Λ.1 := by
      have h1 : LorentzGroup.toVector Λ = Lorentz.Vector.basis (Sum.inl 0) := by
        rw [LorentzGroup.toVector_eq_basis_iff_timeComponent_eq_one]
        exact h.1
      have h2 : LorentzGroup.toVector (LorentzGroup.transpose Λ) =
          Lorentz.Vector.basis (Sum.inl 0) := by
        rw [LorentzGroup.toVector_eq_basis_iff_timeComponent_eq_one]
        exact h.1
      funext i j
      match i, j with
      | .inl 0, .inl 0 => simp [h.1]
      | .inl 0, .inr j =>
        simp only [Fin.isValue, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
        trans (Lorentz.Vector.basis (Sum.inl 0)) (Sum.inr j)
        · simp
        rw [← h2]
        simp [LorentzGroup.transpose_val]
      | .inr i, .inl 0 =>
        simp only [Fin.isValue, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
        trans (Lorentz.Vector.basis (Sum.inl 0)) (Sum.inr i)
        · simp
        rw [← h1]
        simp
      | .inr i, .inr j => rfl
    apply Subtype.ext
    simp only
    exact eq_of_mulVec_eq (congrFun (congrArg Matrix.mulVec h1))

@[fun_prop]
lemma ofSpecialOrthogonal_continuous {d} :
    Continuous (ofSpecialOrthogonal : Matrix.specialOrthogonalGroup (Fin d) ℝ → Rotations d) := by
  simp only [ofSpecialOrthogonal, MulEquiv.coe_mk, Equiv.coe_fn_mk]
  fun_prop

@[fun_prop]
lemma ofSpecialOrthogonal_symm_continuous {d} :
    Continuous (ofSpecialOrthogonal.symm :
      Rotations d → Matrix.specialOrthogonalGroup (Fin d) ℝ) := by
  simp only [ofSpecialOrthogonal, MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk]
  apply Continuous.subtype_mk
  refine Continuous.matrix_submatrix ?_ Sum.inr Sum.inr
  fun_prop

lemma rotations_subset_restricted (d) : Rotations d ≤ LorentzGroup.restricted d := by
  intro Λ h
  constructor
  · exact h.2
  · simp [IsOrthochronous, h.1]

@[simp]
lemma toVector_rotation {d} (Λ : Rotations d) :
    LorentzGroup.toVector Λ.1= Lorentz.Vector.basis (Sum.inl 0) := by
  rw [LorentzGroup.toVector_eq_basis_iff_timeComponent_eq_one]
  exact Λ.2.1

end LorentzGroup

end
