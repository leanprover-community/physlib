/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.SpaceTime.Basic
/-!
# Boosts in the Lorentz group

-/

noncomputable section

open Matrix
open Complex
open ComplexConjugate

namespace LorentzGroup

variable {d : ℕ}
variable (Λ : LorentzGroup d)

/-- The Lorentz factor (aka gamma factor or Lorentz term). -/
def γ (β : ℝ) : ℝ := 1 / Real.sqrt (1 - β^2)

lemma γ_sq (β : ℝ) (hβ : |β| < 1) : (γ β)^2 = 1 / (1 - β^2) := by
  simp only [γ, one_div, inv_pow, _root_.inv_inj]
  refine Real.sq_sqrt ?_
  simp only [sub_nonneg, sq_le_one_iff_abs_le_one]
  exact le_of_lt hβ

@[simp]
lemma γ_zero : γ 0 = 1 := by simp [γ]

@[simp]
lemma γ_neg (β : ℝ) : γ (-β) = γ β := by simp [γ]

@[simp]
lemma γ_det_not_zero (β : ℝ) (hβ : |β| < 1) : (1 - β^2) ≠ 0 := by
  rw [abs_lt] at hβ
  by_contra hn
  have h1 : β ^ 2 = 1 := by linear_combination (norm := ring) (-hn)
  simp at h1
  aesop

/-- The Lorentz boost with in the space direction `i` with speed `β` with
  `|β| < 1`. -/
def boost (i : Fin d) (β : ℝ) (hβ : |β| < 1) : LorentzGroup d :=
  ⟨
  fun j k =>
    if k = Sum.inl 0 ∧ j = Sum.inl 0 then γ β
    else if k = Sum.inl 0 ∧ j = Sum.inr i then - γ β * β
    else if k = Sum.inr i ∧ j = Sum.inl 0 then - γ β * β
    else if k = Sum.inr i ∧ j = Sum.inr i then γ β else
    if j = k then 1 else 0, h⟩
where
  h := by
    rw [mem_iff_dual_mul_self]
    ext j k
    rw [Matrix.mul_apply]
    conv_lhs =>
      enter [2, x]
      rw [minkowskiMatrix.dual_apply]
    simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton]
    rw [minkowskiMatrix.inl_0_inl_0]
    simp only [Fin.isValue, and_true, reduceCtorEq, and_false, ↓reduceIte, neg_mul, mul_ite,
      mul_neg, mul_one, mul_zero, ite_mul, zero_mul, Sum.inr.injEq]
    conv_lhs =>
      enter [2, 2, x]
      rw [minkowskiMatrix.inr_i_inr_i]
    simp only [Fin.isValue, mul_neg, mul_one, neg_mul, neg_neg]
    have hb1 : √(1 - β ^ 2) ^ 2 = 1 - β ^ 2 := by
      refine Real.sq_sqrt ?_
      simp only [sub_nonneg, sq_le_one_iff_abs_le_one]
      exact le_of_lt hβ
    have hb2 : 1 - β ^ 2 ≠ 0 := by
      simp only [ne_eq, sub_ne_zero]
      by_contra h
      have hl : 1 ^ 2 = β ^ 2 := by
        rw [← h]
        simp
      rw [sq_eq_sq_iff_abs_eq_abs] at hl
      rw [← hl] at hβ
      simp at hβ
    by_cases hj : j = Sum.inl 0
    · subst hj
      simp only [Fin.isValue, ↓reduceIte, minkowskiMatrix.inl_0_inl_0, one_mul, true_and,
        reduceCtorEq, false_and]
      rw [Finset.sum_eq_single i]
      · simp only [Fin.isValue, and_true, ↓reduceIte]
        by_cases hk : k = Sum.inl 0
        · subst hk
          simp only [Fin.isValue, ↓reduceIte, one_apply_eq]
          ring_nf
          simp [γ]
          rw [hb1]
          field_simp
        · simp only [Fin.isValue, hk, ↓reduceIte]
          by_cases hk' : k = Sum.inr i
          · simp only [hk', ↓reduceIte, Fin.isValue, ne_eq, reduceCtorEq, not_false_eq_true,
            one_apply_ne]
            ring
          · simp only [hk', ↓reduceIte, Fin.isValue]
            rw [one_apply_ne fun a => hk (id (Eq.symm a))]
            rw [if_neg (by exact fun a => hk (id (Eq.symm a)))]
            rw [if_neg (by exact fun a => hk' (id (Eq.symm a)))]
            simp
      · intro b _ hb
        simp [hb]
      · simp
    · match j with
      | Sum.inl 0 => simp at hj
      | Sum.inr j =>
      rw [minkowskiMatrix.inr_i_inr_i, Finset.sum_eq_single j]
      · by_cases hj' : j = i
        · subst hj'
          conv_lhs =>
            enter [1, 1, 2]
            simp only [Fin.isValue]
          conv_lhs =>
            enter [2, 1, 1, 2]
            simp only [Fin.isValue]
          match k with
          | Sum.inl 0 =>
            simp only [Fin.isValue, ↓reduceIte, reduceCtorEq, neg_mul, one_mul, neg_neg, and_self,
              and_true, ne_eq, not_false_eq_true, one_apply_ne]
            ring
          | Sum.inr k =>
          by_cases hk : k = j
          · subst hk
            simp only [Fin.isValue, reduceCtorEq, ↓reduceIte, neg_mul, one_mul, neg_neg, and_true,
              and_self, one_apply_eq]
            ring_nf
            simp [γ]
            rw [hb1]
            field_simp
          · rw [one_apply]
            simp only [Fin.isValue, reduceCtorEq, ↓reduceIte, Sum.inr.injEq, hk, and_true, and_self,
              neg_mul, one_mul, neg_neg, zero_add]
            rw [if_neg (fun a => hk (id (Eq.symm a))), if_neg (fun a => hk (id (Eq.symm a)))]
        · conv_lhs =>
            enter [1, 1, 2]
            simp only [Fin.isValue]
          conv_lhs =>
            enter [2, 1, 1, 2]
            simp only [Fin.isValue]
          rw [one_apply]
          simp [hj']
      · intro b _ hb
        simp only [Fin.isValue, reduceCtorEq, false_and, ↓reduceIte, Sum.inr.injEq, neg_mul,
          one_mul, hb]
        match k with
        | Sum.inl 0 =>
          simp only [Fin.isValue, true_and, neg_neg, reduceCtorEq, false_and, ↓reduceIte,
            ite_eq_right_iff, neg_eq_zero, mul_eq_zero, or_self_left, and_imp]
          intro h1 h2
          subst h1 h2
          simp at hb
        | Sum.inr k =>
        simp only [Fin.isValue, reduceCtorEq, false_and, ↓reduceIte, Sum.inr.injEq, neg_neg]
        by_cases hb' : b = i
        · simp only [hb', and_true]
          subst hb'
          simp [Ne.symm hb]
        · simp [hb']
      · simp

@[simp]
lemma boost_transpose_eq_self (i : Fin d) {β : ℝ} (hβ : |β| < 1) :
    transpose (boost i β hβ) = boost i β hβ := by
  ext j k
  simp [transpose, boost]
  match j, k with
  | Sum.inl 0, Sum.inl 0 => rfl
  | Sum.inl 0, Sum.inr k =>
    simp
  | Sum.inr i, Sum.inl 0 =>
    simp
  | Sum.inr j, Sum.inr k =>
    simp only [Fin.isValue, reduceCtorEq, and_self, ↓reduceIte, Sum.inr.injEq, false_and, and_false]
    conv_lhs =>
      enter [1]
      rw [and_comm]
    conv_lhs =>
      enter [3, 1]
      rw [eq_comm]

@[simp]
lemma boost_transpose_matrix_eq_self (i : Fin d) {β : ℝ} (hβ : |β| < 1) :
    Matrix.transpose (boost i β hβ).1 = (boost i β hβ).1 := by
  rw [← transpose_val, boost_transpose_eq_self]

@[simp]
lemma boost_zero_eq_id (i : Fin d) : boost i 0 (by simp) = 1 := by
  ext j k
  simp only [boost, Fin.isValue, mul_zero, lorentzGroupIsGroup_one_coe]
  match j, k with
  | Sum.inl 0, Sum.inl 0 => simp [γ]
  | Sum.inl 0, Sum.inr k =>
    simp
  | Sum.inr i, Sum.inl 0 =>
    simp
  | Sum.inr j, Sum.inr k =>
    rw [one_apply]
    simp only [Fin.isValue, reduceCtorEq, and_self, ↓reduceIte, Sum.inr.injEq, false_and, and_false,
      ite_eq_right_iff, and_imp]
    intro h1 h2
    subst h1 h2
    simp

lemma boost_inverse (i : Fin d) {β : ℝ} (hβ : |β| < 1) :
    (boost i β hβ)⁻¹ = boost i (-β) (by simpa using hβ) := by
  rw [inv_eq_dual]
  ext j k
  simp only
  rw [minkowskiMatrix.dual_apply]
  match j, k with
  | Sum.inl 0, Sum.inl 0 =>
    rw [minkowskiMatrix.inl_0_inl_0]
    simp [boost]
  | Sum.inl 0, Sum.inr k =>
    rw [minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i]
    simp only [boost, Fin.isValue, neg_mul, reduceCtorEq, and_false, ↓reduceIte, Sum.inr.injEq,
      true_and, and_self, false_and, mul_ite, mul_neg, one_mul, mul_zero, mul_one, neg_neg,
      and_true]
    split
    · simp
    · simp
  | Sum.inr j, Sum.inl 0 =>
    rw [minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i]
    simp [boost]
  | Sum.inr j, Sum.inr k =>
    rw [minkowskiMatrix.inr_i_inr_i, minkowskiMatrix.inr_i_inr_i]
    simp only [boost, Fin.isValue, neg_mul, reduceCtorEq, and_self, ↓reduceIte, Sum.inr.injEq,
      false_and, and_false, mul_ite, one_mul, mul_one, mul_zero, mul_neg, neg_neg]
    split
    · simp
      rw [if_pos]
      simp_all [not_true_eq_false, imp_false, IsEmpty.forall_iff]
      simp_all only
    · rename_i h
      conv_rhs =>
        rw [if_neg (fun a => h (And.symm a))]
      split
      · rename_i h2
        rw [if_pos (Eq.symm h2)]
        simp
      · rename_i h2
        rw [if_neg (fun a => h2 (Eq.symm a))]
        simp

@[simp]
lemma boost_inl_0_inl_0 (i : Fin d) {β : ℝ} (hβ : |β| < 1) :
    (boost i β hβ).1 (Sum.inl 0) (Sum.inl 0) = γ β := by
  simp [boost]

@[simp]
lemma boost_inr_self_inr_self (i : Fin d) {β : ℝ} (hβ : |β| < 1) :
    (boost i β hβ).1 (Sum.inr i) (Sum.inr i) = γ β := by
  simp [boost]

@[simp]
lemma boost_inl_0_inr_self (i : Fin d) {β : ℝ} (hβ : |β| < 1) :
    (boost i β hβ).1 (Sum.inl 0) (Sum.inr i) = - γ β * β := by
  simp [boost]

@[simp]
lemma boost_inr_self_inl_0 (i : Fin d) {β : ℝ} (hβ : |β| < 1) :
    (boost i β hβ).1 (Sum.inr i) (Sum.inl 0) = - γ β * β := by
  simp [boost]

lemma boost_inl_0_inr_other {i j : Fin d} {β : ℝ} (hβ : |β| < 1) (hij : j ≠ i) :
    (boost i β hβ).1 (Sum.inl 0) (Sum.inr j) = 0 := by
  simp [boost, hij]

lemma boost_inr_other_inl_0 {i j : Fin d} {β : ℝ} (hβ : |β| < 1) (hij : j ≠ i) :
    (boost i β hβ).1 (Sum.inr j) (Sum.inl 0) = 0 := by
  simp [boost, hij]

lemma boost_inr_self_inr_other {i j : Fin d} {β : ℝ} (hβ : |β| < 1) (hij : j ≠ i) :
    (boost i β hβ).1 (Sum.inr i) (Sum.inr j) = 0 := by
  simp only [boost, Fin.isValue, neg_mul, reduceCtorEq, and_self, ↓reduceIte, and_true,
    Sum.inr.injEq, hij, ite_eq_right_iff, one_ne_zero, imp_false]
  exact id (Ne.symm hij)

lemma boost_inr_other_inr_self {i j : Fin d} {β : ℝ} (hβ : |β| < 1) (hij : j ≠ i) :
    (boost i β hβ).1 (Sum.inr j) (Sum.inr i) = 0 := by
  simp [boost, hij]

lemma boost_inr_other_inr {i j k : Fin d} {β : ℝ} (hβ : |β| < 1) (hij : j ≠ i) :
    (boost i β hβ).1 (Sum.inr j) (Sum.inr k) = if j = k then 1 else 0:= by
  simp [boost, hij]

lemma boost_inr_inr_other {i j k : Fin d} {β : ℝ} (hβ : |β| < 1) (hij : j ≠ i) :
    (boost i β hβ).1 (Sum.inr k) (Sum.inr j) = if j = k then 1 else 0:= by
  rw [← boost_transpose_eq_self]
  simp only [transpose, transpose_apply]
  rw [boost_inr_other_inr]
  exact hij
/-!

## Properties of boosts in the zero-direction

-/

@[simp]
lemma boost_zero_inl_0_inr_succ {d : ℕ} {β : ℝ} (hβ : |β| < 1) (i : Fin d) :
    (boost (0 : Fin d.succ) β hβ).1 (Sum.inl 0) (Sum.inr i.succ) = 0 := by
  rw [boost_inl_0_inr_other]
  simp

@[simp]
lemma boost_zero_inr_succ_inl_0{d : ℕ} {β : ℝ} (hβ : |β| < 1) (i : Fin d) :
    (boost (0 : Fin d.succ) β hβ).1 (Sum.inr i.succ) (Sum.inl 0) = 0 := by
  rw [boost_inr_other_inl_0]
  simp

@[simp]
lemma boost_zero_inl_0_inr_nat_succ {d : ℕ} {β : ℝ} (hβ : |β| < 1) (i : ℕ) (h : i + 1 < d + 1) :
    (boost (0 : Fin d.succ) β hβ).1 (Sum.inl 0) (Sum.inr ⟨i + 1, h⟩) = 0 := by
  rw [boost_inl_0_inr_other]
  simp

@[simp]
lemma boost_zero_inr_nat_succ_inl_0 {d : ℕ} {β : ℝ} (hβ : |β| < 1) (i : ℕ) (h : i + 1 < d + 1) :
    (boost (0 : Fin d.succ) β hβ).1 (Sum.inr ⟨i + 1, h⟩) (Sum.inl 0) = 0 := by
  rw [boost_inr_other_inl_0]
  simp

@[simp]
lemma boost_zero_inr_0_inr_succ {d : ℕ} {β : ℝ} (hβ : |β| < 1) (i : Fin d) :
    (boost (0 : Fin d.succ) β hβ).1 (Sum.inr 0) (Sum.inr i.succ) = 0 := by
  rw [boost_inr_self_inr_other]
  simp

@[simp]
lemma boost_zero_inr_succ_inr_0 {d : ℕ} {β : ℝ} (hβ : |β| < 1) (i : Fin d) :
    (boost (0 : Fin d.succ) β hβ).1 (Sum.inr i.succ) (Sum.inr 0) = 0 := by
  rw [boost_inr_other_inr_self]
  simp

@[simp]
lemma boost_zero_inr_0_inr_nat_succ {d : ℕ} {β : ℝ} (hβ : |β| < 1) (i : ℕ) (h : i + 1 < d + 1) :
    (boost (0 : Fin d.succ) β hβ).1 (Sum.inr 0) (Sum.inr ⟨i + 1, h⟩) = 0 := by
  rw [boost_inr_self_inr_other]
  simp

@[simp]
lemma boost_zero_inr_nat_succ_inr_0 {d : ℕ} {β : ℝ} (hβ : |β| < 1) (i : ℕ) (h : i + 1 < d + 1) :
    (boost (0 : Fin d.succ) β hβ).1 (Sum.inr ⟨i + 1, h⟩) (Sum.inr 0) = 0 := by
  rw [boost_inr_other_inr_self]
  simp

lemma boost_zero_inr_succ_inr_succ {d : ℕ} {β : ℝ} (hβ : |β| < 1) (i1 i2 : Fin d) :
    (boost (0 : Fin d.succ) β hβ).1 (Sum.inr i1.succ) (Sum.inr i2.succ) =
    if i1 = i2 then 1 else 0 := by
  rw [boost_inr_inr_other]
  simp only [Nat.succ_eq_add_one, Fin.succ_inj]
  congr 1
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)
  simp

end LorentzGroup

end
