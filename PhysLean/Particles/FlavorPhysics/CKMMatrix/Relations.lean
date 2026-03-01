/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.FlavorPhysics.CKMMatrix.Rows
/-!
# Relations for the CKM Matrix

This file contains a collection of relations and properties between the elements of the CKM
matrix.

-/

open Matrix Complex

noncomputable section

namespace CKMMatrix
open ComplexConjugate

section rows

/-- The absolute value squared of any row of a CKM matrix is `1`, in terms of `Vabs`. -/
lemma VAbs_sum_sq_row_eq_one (V : Quotient CKMMatrixSetoid) (i : Fin 3) :
    (VAbs i 0 V) ^ 2 + (VAbs i 1 V) ^ 2 + (VAbs i 2 V) ^ 2 = 1 := by
  obtain ⟨V, hV⟩ := Quot.exists_rep V
  subst hV
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV i) i
  simp only [mul_apply, star_apply, RCLike.star_def, Fin.sum_univ_three, Fin.isValue,
    one_apply_eq] at ht
  rw [mul_conj, mul_conj, mul_conj] at ht
  repeat rw [← Complex.sq_norm] at ht
  rw [← ofReal_inj]
  simpa using ht

/-- The absolute value squared of the first row of a CKM matrix is `1`, in terms of `norm`. -/
lemma fst_row_normalized_abs (V : CKMMatrix) :
    norm [V]ud ^ 2 + norm [V]us ^ 2 + norm [V]ub ^ 2 = 1 :=
  VAbs_sum_sq_row_eq_one ⟦V⟧ 0

/-- The absolute value squared of the second row of a CKM matrix is `1`, in terms of `norm`. -/
lemma snd_row_normalized_abs (V : CKMMatrix) :
    norm [V]cd ^ 2 + norm [V]cs ^ 2 + norm [V]cb ^ 2 = 1 :=
  VAbs_sum_sq_row_eq_one ⟦V⟧ 1

/-- The absolute value squared of the third row of a CKM matrix is `1`, in terms of `norm`. -/
lemma thd_row_normalized_abs (V : CKMMatrix) :
    norm [V]td ^ 2 + norm [V]ts ^ 2 + norm [V]tb ^ 2 = 1 :=
  VAbs_sum_sq_row_eq_one ⟦V⟧ 2

/-- The absolute value squared of the first row of a CKM matrix is `1`, in terms of `nomSq`. -/
lemma fst_row_normalized_normSq (V : CKMMatrix) :
    normSq [V]ud + normSq [V]us + normSq [V]ub = 1 := by
  repeat rw [← Complex.sq_norm]
  exact V.fst_row_normalized_abs

/-- The absolute value squared of the second row of a CKM matrix is `1`, in terms of `nomSq`. -/
lemma snd_row_normalized_normSq (V : CKMMatrix) :
    normSq [V]cd + normSq [V]cs + normSq [V]cb = 1 := by
  repeat rw [← Complex.sq_norm]
  exact V.snd_row_normalized_abs

/-- The absolute value squared of the third row of a CKM matrix is `1`, in terms of `nomSq`. -/
lemma thd_row_normalized_normSq (V : CKMMatrix) :
    normSq [V]td + normSq [V]ts + normSq [V]tb = 1 := by
  repeat rw [← Complex.sq_norm]
  exact V.thd_row_normalized_abs

lemma normSq_Vud_plus_normSq_Vus (V : CKMMatrix) :
    normSq [V]ud + normSq [V]us = 1 - normSq [V]ub := by
  linear_combination fst_row_normalized_normSq V

lemma VudAbs_sq_add_VusAbs_sq : VudAbs V ^ 2 + VusAbs V ^2 = 1 - VubAbs V ^2 := by
  linear_combination VAbs_sum_sq_row_eq_one V 0

lemma ud_us_ne_zero_iff_ub_ne_one (V : CKMMatrix) :
    [V]ud ≠ 0 ∨ [V]us ≠ 0 ↔ norm [V]ub ≠ 1 := by
  have h2 := V.fst_row_normalized_abs
  refine Iff.intro (fun h h1 => ?_) (fun h => ?_)
  · rw [h1] at h2
    simp only [Fin.isValue, one_pow, add_eq_right] at h2
    rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)] at h2
    simp_all
  · by_contra hn
    rw [not_or] at hn
    simp_all only [ne_eq, Decidable.not_not, norm_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero, zero_add, sq_eq_one_iff, false_or]
    have h1 := norm_nonneg [V]ub
    rw [h2] at h1
    refine (?_ : ¬ 0 ≤ (-1 : ℝ)) h1
    simp

lemma normSq_Vud_plus_normSq_Vus_ne_zero_ℝ {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0) :
    normSq [V]ud + normSq [V]us ≠ 0 := by
  rw [normSq_Vud_plus_normSq_Vus V]
  rw [ud_us_ne_zero_iff_ub_ne_one] at hb
  by_contra hn
  rw [← Complex.sq_norm] at hn
  have h2 : norm (V.1 0 2) ^2 = 1 := by
    linear_combination -(1 * hn)
  simp only [Fin.isValue, sq_eq_one_iff] at h2
  cases' h2 with h2 h2
  · exact hb h2
  · have h3 := norm_nonneg [V]ub
    rw [h2] at h3
    have h2 : ¬ 0 ≤ (-1 : ℝ) := by simp
    exact h2 h3

lemma VAbsub_ne_zero_Vud_Vus_ne_zero {V : Quotient CKMMatrixSetoid}
    (hV : VAbs 0 2 V ≠ 1) :(VudAbs V ^ 2 + VusAbs V ^ 2) ≠ 0 := by
  obtain ⟨V⟩ := V
  change VubAbs ⟦V⟧ ≠ 1 at hV
  simp only [VubAbs, VAbs, VAbs', Fin.isValue, Quotient.lift_mk] at hV
  rw [← ud_us_ne_zero_iff_ub_ne_one V] at hV
  simpa [← Complex.sq_norm] using (normSq_Vud_plus_normSq_Vus_ne_zero_ℝ hV)

lemma VAbsub_ne_zero_sqrt_Vud_Vus_ne_zero {V : Quotient CKMMatrixSetoid}
    (hV : VAbs 0 2 V ≠ 1) : √(VudAbs V ^ 2 + VusAbs V ^ 2) ≠ 0 := by
  obtain ⟨V⟩ := V
  rw [Real.sqrt_ne_zero (Left.add_nonneg (sq_nonneg _) (sq_nonneg _))]
  change VubAbs ⟦V⟧ ≠ 1 at hV
  simp only [VubAbs, VAbs, VAbs', Fin.isValue, Quotient.lift_mk] at hV
  rw [← ud_us_ne_zero_iff_ub_ne_one V] at hV
  simpa [← Complex.sq_norm] using (normSq_Vud_plus_normSq_Vus_ne_zero_ℝ hV)

lemma normSq_Vud_plus_normSq_Vus_ne_zero_ℂ {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0) :
    (normSq [V]ud : ℂ) + normSq [V]us ≠ 0 := by
  have h1 := normSq_Vud_plus_normSq_Vus_ne_zero_ℝ hb
  simp only [Fin.isValue, ne_eq] at h1
  rw [← ofReal_inj] at h1
  simp_all

lemma Vabs_sq_add_ne_zero {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0) :
    ((VudAbs ⟦V⟧ : ℂ) * ↑(VudAbs ⟦V⟧) + ↑(VusAbs ⟦V⟧) * ↑(VusAbs ⟦V⟧)) ≠ 0 := by
  have h1 := normSq_Vud_plus_normSq_Vus_ne_zero_ℂ hb
  rw [← Complex.sq_norm, ← Complex.sq_norm] at h1
  simp only [Fin.isValue, sq, ofReal_mul, ne_eq] at h1
  exact h1

section orthogonal

lemma fst_row_orthog_snd_row (V : CKMMatrix) :
    [V]cd * conj [V]ud + [V]cs * conj [V]us + [V]cb * conj [V]ub = 0 := by
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 1) 0
  simp only [Fin.isValue, mul_apply, star_apply, RCLike.star_def, Fin.sum_univ_three, ne_eq,
    one_ne_zero, not_false_eq_true, one_apply_ne] at ht
  exact ht

lemma fst_row_orthog_thd_row (V : CKMMatrix) :
    [V]td * conj [V]ud + [V]ts * conj [V]us + [V]tb * conj [V]ub = 0 := by
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 2) 0
  simp only [Fin.isValue, mul_apply, star_apply, RCLike.star_def, Fin.sum_univ_three, ne_eq,
    Fin.reduceEq, not_false_eq_true, one_apply_ne] at ht
  exact ht

lemma Vcd_mul_conj_Vud (V : CKMMatrix) :
    [V]cd * conj [V]ud = -[V]cs * conj [V]us - [V]cb * conj [V]ub := by
  linear_combination (V.fst_row_orthog_snd_row)

lemma Vcs_mul_conj_Vus (V : CKMMatrix) :
    [V]cs * conj [V]us = - [V]cd * conj [V]ud - [V]cb * conj [V]ub := by
  linear_combination V.fst_row_orthog_snd_row

end orthogonal

lemma VAbs_thd_eq_one_fst_eq_zero {V : Quotient CKMMatrixSetoid} {i : Fin 3} (hV : VAbs i 2 V = 1) :
    VAbs i 0 V = 0 := by
  have h := VAbs_sum_sq_row_eq_one V i
  rw [hV] at h
  simp only [Fin.isValue, one_pow, add_eq_right] at h
  nlinarith

lemma VAbs_thd_eq_one_snd_eq_zero {V : Quotient CKMMatrixSetoid} {i : Fin 3} (hV : VAbs i 2 V = 1) :
    VAbs i 1 V = 0 := by
  have h := VAbs_sum_sq_row_eq_one V i
  rw [hV] at h
  simp only [Fin.isValue, one_pow, add_eq_right] at h
  nlinarith

section crossProduct

lemma conj_Vtb_cross_product {V : CKMMatrix} {τ : ℝ}
    (hτ : [V]t = cexp (τ * I) • (conj [V]u ⨯₃ conj [V]c)) :
    conj [V]tb = cexp (- τ * I) * ([V]cs * [V]ud - [V]us * [V]cd) := by
  have h1 := congrFun hτ 2
  simp only [tRow, Fin.isValue, cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, tail_cons,
    head_cons, crossProduct, uRow, cRow, LinearMap.mk₂_apply, Pi.conj_apply, cons_val_one,
    cons_val_zero, Pi.smul_apply, smul_eq_mul] at h1
  apply congrArg conj at h1
  simp only [Fin.isValue, _root_.map_mul, map_sub, RingHomCompTriple.comp_apply,
    RingHom.id_apply] at h1
  rw [h1]
  simp only [← exp_conj, _root_.map_mul, conj_ofReal, conj_I, mul_neg, Fin.isValue, neg_mul]
  simp only [Fin.isValue, mul_eq_mul_left_iff, sub_left_inj, exp_ne_zero, or_false]
  exact mul_comm _ _

end crossProduct

lemma conj_Vtb_mul_Vud {V : CKMMatrix} {τ : ℝ}
    (hτ : [V]t = cexp (τ * I) • (conj [V]u ⨯₃ conj [V]c)) :
    cexp (τ * I) * conj [V]tb * conj [V]ud =
    [V]cs * (normSq [V]ud + normSq [V]us) + [V]cb * conj [V]ub * [V]us := by
  rw [conj_Vtb_cross_product hτ]
  simp only [neg_mul, exp_neg, Fin.isValue, ne_eq, exp_ne_zero, not_false_eq_true,
    mul_inv_cancel_left₀]
  have h2 : ([V]cs * [V]ud - [V]us * [V]cd) * conj [V]ud = [V]cs
      * [V]ud * conj [V]ud - [V]us * ([V]cd * conj [V]ud) := by
    ring
  rw [h2, V.Vcd_mul_conj_Vud]
  rw [normSq_eq_conj_mul_self, normSq_eq_conj_mul_self]
  simp only [Fin.isValue, neg_mul]
  ring

lemma conj_Vtb_mul_Vus {V : CKMMatrix} {τ : ℝ}
    (hτ : [V]t = cexp (τ * I) • (conj [V]u ⨯₃ conj [V]c)) :
    cexp (τ * I) * conj [V]tb * conj [V]us =
    - ([V]cd * (normSq [V]ud + normSq [V]us) + [V]cb * conj ([V]ub) * [V]ud) := by
  rw [conj_Vtb_cross_product hτ]
  simp only [neg_mul, exp_neg, Fin.isValue, ne_eq, exp_ne_zero, not_false_eq_true,
    mul_inv_cancel_left₀, neg_add_rev]
  have h2 : ([V]cs * [V]ud - [V]us * [V]cd) * conj [V]us = ([V]cs
      * conj [V]us) * [V]ud - [V]us * [V]cd * conj [V]us := by
    ring
  rw [h2, V.Vcs_mul_conj_Vus]
  rw [normSq_eq_conj_mul_self, normSq_eq_conj_mul_self]
  simp only [Fin.isValue, neg_mul]
  ring

lemma cs_of_ud_us_ub_cb_tb {V : CKMMatrix} (h : [V]ud ≠ 0 ∨ [V]us ≠ 0)
    {τ : ℝ} (hτ : [V]t = cexp (τ * I) • (conj ([V]u) ⨯₃ conj ([V]c))) :
    [V]cs = (- conj [V]ub * [V]us * [V]cb +
      cexp (τ * I) * conj [V]tb * conj [V]ud) / (normSq [V]ud + normSq [V]us) := by
  have h1 := normSq_Vud_plus_normSq_Vus_ne_zero_ℂ h
  rw [conj_Vtb_mul_Vud hτ]
  field_simp
  ring

lemma cd_of_ud_us_ub_cb_tb {V : CKMMatrix} (h : [V]ud ≠ 0 ∨ [V]us ≠ 0)
    {τ : ℝ} (hτ : [V]t = cexp (τ * I) • (conj ([V]u) ⨯₃ conj ([V]c))) :
    [V]cd = - (conj [V]ub * [V]ud * [V]cb + cexp (τ * I) * conj [V]tb * conj [V]us) /
      (normSq [V]ud + normSq [V]us) := by
  have h1 := normSq_Vud_plus_normSq_Vus_ne_zero_ℂ h
  rw [conj_Vtb_mul_Vus hτ]
  field_simp
  ring

end rows

section individual

lemma VAbs_ge_zero (i j : Fin 3) (V : Quotient CKMMatrixSetoid) : 0 ≤ VAbs i j V := by
  obtain ⟨V, hV⟩ := Quot.exists_rep V
  rw [← hV]
  exact norm_nonneg _

lemma VAbs_leq_one (i j : Fin 3) (V : Quotient CKMMatrixSetoid) : VAbs i j V ≤ 1 := by
  have h := VAbs_sum_sq_row_eq_one V i
  fin_cases j
  · change VAbs i 0 V ≤ 1
    nlinarith
  · change VAbs i 1 V ≤ 1
    nlinarith
  · change VAbs i 2 V ≤ 1
    nlinarith

end individual

section columns

lemma VAbs_sum_sq_col_eq_one (V : Quotient CKMMatrixSetoid) (i : Fin 3) :
    (VAbs 0 i V) ^ 2 + (VAbs 1 i V) ^ 2 + (VAbs 2 i V) ^ 2 = 1 := by
  obtain ⟨V, hV⟩ := Quot.exists_rep V
  subst hV
  have hV := V.prop
  rw [mem_unitaryGroup_iff'] at hV
  have ht := congrFun (congrFun hV i) i
  simp only [mul_apply, star_apply, RCLike.star_def, Fin.sum_univ_three, Fin.isValue,
    one_apply_eq] at ht
  rw [mul_comm, mul_conj, mul_comm, mul_conj, mul_comm, mul_conj] at ht
  repeat rw [← Complex.sq_norm] at ht
  rw [← ofReal_inj]
  simpa using ht

lemma thd_col_normalized_abs (V : CKMMatrix) :
    norm [V]ub ^ 2 + norm [V]cb ^ 2 + norm [V]tb ^ 2 = 1 := by
  have h1 := VAbs_sum_sq_col_eq_one ⟦V⟧ 2
  simp only [VAbs, VAbs', Fin.isValue, Quotient.lift_mk] at h1
  exact h1

lemma thd_col_normalized_normSq (V : CKMMatrix) :
    normSq [V]ub + normSq [V]cb + normSq [V]tb = 1 := by
  have h1 := V.thd_col_normalized_abs
  repeat rw [Complex.sq_norm] at h1
  exact h1

lemma cb_eq_zero_of_ud_us_zero {V : CKMMatrix} (h : [V]ud = 0 ∧ [V]us = 0) :
    [V]cb = 0 := by
  have h1 := fst_row_normalized_abs V
  rw [← thd_col_normalized_abs V] at h1
  simp only [Fin.isValue, h] at h1
  rw [add_assoc] at h1
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Fin.isValue,
    zero_add, add_assoc, left_eq_add] at h1
  rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)] at h1
  simp only [Fin.isValue, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    norm_eq_zero] at h1
  exact h1.1

lemma cs_of_ud_us_zero {V : CKMMatrix} (ha : ¬ ([V]ud ≠ 0 ∨ [V]us ≠ 0)) :
    VcsAbs ⟦V⟧ = √(1 - VcdAbs ⟦V⟧ ^ 2) := by
  have h1 := snd_row_normalized_abs V
  symm
  rw [Real.sqrt_eq_iff_eq_sq]
  · simp only [Fin.isValue, ne_eq, not_or, Decidable.not_not] at ha
    rw [cb_eq_zero_of_ud_us_zero ha] at h1
    simp only [Fin.isValue, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero] at h1
    simp only [VcdAbs, VAbs, VAbs', Fin.isValue, Quotient.lift_mk, VcsAbs]
    rw [← h1]
    ring
  · simp only [VcdAbs, Fin.isValue, sub_nonneg, sq_le_one_iff_abs_le_one]
    rw [@abs_le]
    have h1 := VAbs_leq_one 1 0 ⟦V⟧
    have h0 := VAbs_ge_zero 1 0 ⟦V⟧
    simp_all only [ne_eq, not_or, Decidable.not_not, and_true, ge_iff_le]
    have hn : -1 ≤ (0 : ℝ) := by simp
    exact hn.trans h0
  · exact VAbs_ge_zero _ _ ⟦V⟧

lemma VcbAbs_sq_add_VtbAbs_sq (V : Quotient CKMMatrixSetoid) :
    VcbAbs V ^ 2 + VtbAbs V ^ 2 = 1 - VubAbs V ^2 := by
  linear_combination (VAbs_sum_sq_col_eq_one V 2)

lemma cb_tb_ne_zero_iff_ub_ne_one (V : CKMMatrix) :
    [V]cb ≠ 0 ∨ [V]tb ≠ 0 ↔ norm [V]ub ≠ 1 := by
  have h2 := V.thd_col_normalized_abs
  refine Iff.intro (fun h h1 => ?_) (fun h => ?_)
  · rw [h1] at h2
    simp only [one_pow, Fin.isValue] at h2
    have h2 : norm (V.1 1 2) ^ 2 + norm (V.1 2 2) ^ 2 = 0 := by
      linear_combination h2
    rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)] at h2
    simp_all
  · by_contra hn
    rw [not_or] at hn
    simp only [Fin.isValue, ne_eq, Decidable.not_not] at hn
    simp_all only [ne_eq]
    simp only [Fin.isValue, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero, sq_eq_one_iff] at h2
    simp_all only [false_or]
    have h1 := norm_nonneg [V]ub
    rw [h2] at h1
    simp only [Left.nonneg_neg_iff] at h1
    have h2 : ¬ 1 ≤ (0 : ℝ) := by simp
    exact h2 h1

lemma VAbs_fst_col_eq_one_snd_eq_zero {V : Quotient CKMMatrixSetoid} {i : Fin 3}
    (hV : VAbs 0 i V = 1) : VAbs 1 i V = 0 := by
  have h := VAbs_sum_sq_col_eq_one V i
  rw [hV] at h
  simp only [one_pow, Fin.isValue] at h
  nlinarith

lemma VAbs_fst_col_eq_one_thd_eq_zero {V : Quotient CKMMatrixSetoid} {i : Fin 3}
    (hV : VAbs 0 i V = 1) : VAbs 2 i V = 0 := by
  have h := VAbs_sum_sq_col_eq_one V i
  rw [hV] at h
  simp only [one_pow, Fin.isValue] at h
  nlinarith

end columns

end CKMMatrix
end
