/-
Copyright (c) 2026 AMPS formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AMPS formalization contributors
-/
module

public import PhyslibAlpha.Relativity.BlackHole.AMPS.VacuumTest

/-!
# An approximate outgoing-number prediction with infinite occupation support

Physical early measurements and late occupation.

## i. Overview

Appendix A measures the vector error between a late projector and a scaled early
estimator. Here the late projector tests the entire occupation event, including all
partner occupations. The early estimator is a real multiple of a physical yes/no
projector, as in Eq. (A.1). Both act on one normalized state. The proof allows
arbitrary square-summable states and imposes no cutoff on either oscillator.

## ii. Key results

* `errorWeight_eq`
* `posterior_of_vector_error`

## iii. Table of contents

- A. Physical early measurements and late occupation
- B. Thresholding a self-adjoint early estimator for a coarse occupation event

## iv. References

* [ref: Almheiri2013]

## A. Physical early measurements and late occupation
-/

@[expose] public section

noncomputable section

namespace AMPS.Operational

open VacuumTest

variable {R : Type*} [Fintype R]

/-- Squared vector error on the original state, before dividing by the Born weight
of the target branch as in AMPS (A.3). The early basis diagonalizes its yes/no test. -/
def errorWeight (φ : R → Pair) (yes : R → Bool) (n : ℕ) (s : ℝ) : ℝ :=
  ∑ r, ‖hit n (φ r) - (if yes r then (s : ℂ) • φ r else 0)‖ ^ 2

private lemma row_error (x : Pair) (n : ℕ) (s : ℝ) :
    ‖hit n x - (s : ℂ) • x‖ ^ 2 =
      ‖hit n x‖ ^ 2 - 2 * s * ‖hit n x‖ ^ 2 + s ^ 2 * ‖x‖ ^ 2 := by
  have hz := hit_inner_miss n x x
  rw [inner_sub_right, sub_eq_zero] at hz
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, hz, inner_self_eq_norm_sq_to_K, norm_smul]
  simp [Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, ← Complex.ofReal_pow]
  ring

/-- The squared vector error uses the full Born distribution of the two commuting
measurements. The cross term is the probability that both tests return yes. -/
lemma errorWeight_eq (φ : R → Pair) (yes : R → Bool) (n : ℕ) (s : ℝ) :
    errorWeight φ yes n s = outgoingProbability φ n -
      2 * s * markedJointProbability yes φ n + s ^ 2 * markedProbability yes φ := by
  simp only [errorWeight, outgoingProbability, markedJointProbability, markedProbability,
    jointProbability, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  cases yes r with
  | false => simp
  | true => simpa using row_error (φ r) n s

/-- Conditional success is at least one minus the relative squared vector error.
This holds for every real estimator scale and any chosen early binary event. -/
lemma posterior_of_vector_error (φ : R → Pair) (yes : R → Bool) (n : ℕ) (s g : ℝ)
    (hp : 0 < outgoingProbability φ n)
    (herr : errorWeight φ yes n s ≤ g * outgoingProbability φ n) :
    (1 - g) * markedProbability yes φ ≤ markedJointProbability yes φ n := by
  let p := outgoingProbability φ n
  let a := markedProbability yes φ
  let b := markedJointProbability yes φ n
  have hab : b ≤ p := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _) (fun j _ _ => sq_nonneg ‖hit n (φ j)‖)
  have ha : 0 ≤ a := Finset.sum_nonneg fun j _ => sq_nonneg ‖φ j‖
  have hb : 0 ≤ b := Finset.sum_nonneg fun j _ => sq_nonneg ‖hit n (φ j)‖
  rw [errorWeight_eq] at herr
  change p - 2 * s * b + s ^ 2 * a ≤ g * p at herr
  apply le_of_mul_le_mul_right (a := p) _ hp
  change (1 - g) * a * p ≤ b * p
  nlinarith only [mul_le_mul_of_nonneg_left herr ha, sq_nonneg (s*a-b),
    mul_le_mul_of_nonneg_left hab hb]

/-- In a single arbitrary state with unbounded occupation support, a prediction
above the squeezed-vacuum prior forces rejection of the joint vacuum test. -/
lemma amps_full_support (φ : R → Pair) (yes : R → Bool) (n : ℕ) (s g : ℝ)
    (hnorm : ∑ r, ‖φ r‖ ^ 2 = 1) (hp : 0 < outgoingProbability φ n)
    (ha : 0 < markedProbability yes φ)
    (herr : errorWeight φ yes n s ≤ g * outgoingProbability φ n)
    {q : ℂ} (hq : q.normSq < 1) (hgap : 0 ≤ 1 - g - thermalNumberWeight q n) :
    markedProbability yes φ * (1-g-thermalNumberWeight q n) ^ 2 ≤
      1 - pairProbability (vacuum q hq) φ := by
  have h := (le_div_iff₀ ha).mpr (posterior_of_vector_error φ yes n s g hp herr)
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hgap (sub_le_sub_right h (thermalNumberWeight q n)) 2) ha.le).trans
    (conditional_number_discrepancy hq yes φ n hnorm ha)

/-! ## B. Thresholding a self-adjoint early estimator for a coarse occupation event -/

/-- Squared vector estimation error in an eigenbasis of a self-adjoint early estimator.
Each real eigenvalue is retained. The late event includes every partner occupation. -/
def spectralError (φ : R → Pair) (eigenvalue : R → ℝ) (n : ℕ) : ℝ :=
  ∑ r, ‖hit n (φ r) - (eigenvalue r : ℂ) • φ r‖ ^ 2

/-- The spectral projector of the early estimator on `[1/2,∞)`, in its eigenbasis. -/
def thresholdYes (eigenvalue : R → ℝ) (r : R) : Bool := decide (1 / 2 ≤ eigenvalue r)

/-- Born mass of a false positive or a false negative for a binary early readout and
an outgoing occupation event, including all partner occupations. -/
def disagreementWeight (φ : R → Pair) (yes : R → Bool) (n : ℕ) : ℝ :=
  ∑ r, if yes r then ‖φ r - hit n (φ r)‖ ^ 2 else ‖hit n (φ r)‖ ^ 2

private lemma row_error_sectors (x : Pair) (n : ℕ) (s : ℝ) :
    ‖hit n x - (s : ℂ) • x‖ ^ 2 =
      (1 - s) ^ 2 * ‖hit n x‖ ^ 2 + s ^ 2 * ‖x - hit n x‖ ^ 2 := by
  rw [row_error, ← hit_split_sq n x]
  ring

/-- Thresholding the estimator yields an actual binary readout. On every disagreeing
sector its squared estimation error per unit Born weight is at least `1/4`. -/
lemma threshold_disagreement_le (φ : R → Pair) (eigenvalue : R → ℝ) (n : ℕ) :
    disagreementWeight φ (thresholdYes eigenvalue) n ≤ 4 * spectralError φ eigenvalue n := by
  rw [disagreementWeight, spectralError, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  rw [row_error_sectors]
  let s := eigenvalue r
  let a := ‖hit n (φ r)‖ ^ 2
  let b := ‖φ r - hit n (φ r)‖ ^ 2
  have ha : 0 ≤ a := sq_nonneg _
  have hb : 0 ≤ b := sq_nonneg _
  change (if thresholdYes eigenvalue r then b else a) ≤ 4 * ((1 - s) ^ 2 * a + s ^ 2 * b)
  by_cases h : 1 / 2 ≤ s
  · have hyes : thresholdYes eigenvalue r = true := decide_eq_true h
    simp only [hyes, ite_true]
    have hs : 1 ≤ 4 * s ^ 2 := by nlinarith [sq_nonneg (s - 1/2)]
    nlinarith only [mul_le_mul_of_nonneg_right hs hb, mul_nonneg (sq_nonneg (1-s)) ha]
  · have hno : thresholdYes eigenvalue r = false := decide_eq_false h
    simp only [hno, Bool.false_eq_true, ite_false]
    have hs : 1 ≤ 4 * (1 - s) ^ 2 := by nlinarith [sq_nonneg (s - 1/2)]
    nlinarith only [mul_le_mul_of_nonneg_right hs ha, mul_nonneg (sq_nonneg s) hb]

/-- Disagreement is exactly the sum of the two marginals less twice the joint yes mass. -/
lemma disagreementWeight_eq (φ : R → Pair) (yes : R → Bool) (n : ℕ) :
    disagreementWeight φ yes n = outgoingProbability φ n + markedProbability yes φ -
      2 * markedJointProbability yes φ n := by
  have hid : disagreementWeight φ yes n = errorWeight φ yes n 1 := by
    apply Finset.sum_congr rfl
    intro r _
    cases yes r <;> simp [norm_sub_rev]
  rw [hid, errorWeight_eq]
  ring

private lemma bounded_vacuum_probability {q : ℂ} (hq : q.normSq < 1) (φ : R → Pair)
    (hnorm : ∑ r, ‖φ r‖ ^ 2 = 1) : pairProbability (vacuum q hq) φ ≤ 1 := by
  rw [pairProbability, EuclideanSpace.norm_sq_eq, ← hnorm]
  apply Finset.sum_le_sum
  intro r _
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  simpa [pairReadout, norm_vacuum] using norm_inner_le_norm (𝕜 := ℂ) (vacuum q hq) (φ r)

/-- Division-free vacuum bound for the whole number event. For event mass `p`, smooth
prior `h`, and unnormalized estimator error `E`, the squared positive part of
`p(1-h)-4E` bounds joint vacuum rejection. Individual Schmidt-branch weights do not enter. -/
lemma coarse_estimator_pair_test (φ : R → Pair) (eigenvalue : R → ℝ) (n : ℕ)
    (hnorm : ∑ r, ‖φ r‖ ^ 2 = 1) {q : ℂ} (hq : q.normSq < 1) :
    (max 0 (outgoingProbability φ n * (1 - thermalNumberWeight q n) -
      4 * spectralError φ eigenvalue n)) ^ 2 ≤ 1 - pairProbability (vacuum q hq) φ := by
  let yes := thresholdYes eigenvalue
  let p := outgoingProbability φ n
  let a := markedProbability yes φ
  let b := markedJointProbability yes φ n
  let h := thermalNumberWeight q n
  let E := spectralError φ eigenvalue n
  let L := 1 - pairProbability (vacuum q hq) φ
  have hL : 0 ≤ L := sub_nonneg.mpr (bounded_vacuum_probability hq φ hnorm)
  have hbp : b ≤ p := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _) (fun r _ _ => sq_nonneg ‖hit n (φ r)‖)
  have hba : b ≤ a := by
    apply Finset.sum_le_sum
    intro r _
    change ‖hit n (φ r)‖ ^ 2 ≤ ‖φ r‖ ^ 2
    linarith only [hit_split_sq n (φ r), sq_nonneg ‖φ r - hit n (φ r)‖]
  have ha : a ≤ 1 := by
    rw [← hnorm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun r _ _ =>
      sq_nonneg _)
  have hh0 : 0 ≤ h := mul_nonneg (sub_nonneg.mpr hq.le) (pow_nonneg (Complex.normSq_nonneg _) _)
  have hh1 : h ≤ 1 := (mul_le_of_le_one_right (sub_nonneg.mpr hq.le)
    (pow_le_one₀ (Complex.normSq_nonneg _) hq.le)).trans (sub_le_self _ (Complex.normSq_nonneg _))
  have herr : p + a - 2*b ≤ 4*E := by
    simpa only [disagreementWeight_eq, yes, p, a, b, E] using threshold_disagreement_le φ
      eigenvalue n
  have hgap : p * (1 - h) - 4*E ≤ b - a*h := by
    nlinarith only [herr, mul_nonneg hh0 (sub_nonneg.mpr hbp),
      mul_nonneg (sub_nonneg.mpr hh1) (sub_nonneg.mpr hba)]
  have htest : (b - a*h) ^ 2 ≤ a*L := binary_prediction_pair_test hq yes φ n hnorm
  change (max 0 (p * (1 - h) - 4*E)) ^ 2 ≤ L
  by_cases hpos : 0 ≤ p * (1 - h) - 4*E
  · rw [max_eq_right hpos]
    exact (pow_le_pow_left₀ hpos hgap 2).trans (htest.trans (mul_le_of_le_one_left hL ha))
  · simpa only [max_eq_left (le_of_not_ge hpos), zero_pow (by decide : 2 ≠ 0)] using hL

end AMPS.Operational
