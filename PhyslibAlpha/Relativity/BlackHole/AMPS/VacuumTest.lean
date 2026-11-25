/-
Copyright (c) 2026 AMPS formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AMPS formalization contributors
-/
module

public import PhyslibAlpha.Relativity.BlackHole.AMPS.Packet
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-!
# Early number prediction versus the smooth-pair projector

Binary pair-vacuum test and infalling measurements.

## i. Overview

The early register is measured in an orthonormal basis. Each outcome `r` gives a guess for
the occupation of the outgoing packet. The two oscillator occupations have no cutoff. The
conditional rows of the *original* state keep their Born weights, so both the prediction
error and the pair-test acceptance below are unconditional probabilities.

The test is the rank-one projector onto the specified two-mode squeezed state tensor the
identity on the early register. Its norm is bounded even where a number or energy moment
diverges. It tests the whole pair, a different observable from occupation of a single mode.

## ii. Key results

* `norm_vacuum`
* `correct_add_error`

## iii. Table of contents

- A. Binary pair-vacuum test and infalling measurements
- B. One early yes/no readout and one outgoing number outcome
- C. Spectral measurements of the two infalling oscillators

## iv. References

* [ref: Almheiri2013]

## A. Binary pair-vacuum test and infalling measurements
-/

@[expose] public section

noncomputable section

namespace AMPS.VacuumTest

open AMPS.Packet
open scoped InnerProductSpace

/-- Two full bosonic modes, with a trivial spectator to use the same packet coordinates. -/
abbrev Pair := lp (fun _ : ℕ × ℕ × Unit => ℂ) 2

/-- The normalized squeezed vacuum as a vector of the two-oscillator Hilbert space. -/
def vacuum (q : ℂ) (hq : q.normSq < 1) : Pair :=
  ⟨squeezed q, memℓp_gen (by simpa [Complex.sq_norm] using (squeezed_normalized hq).summable)⟩

lemma norm_vacuum {q : ℂ} (hq : q.normSq < 1) : ‖vacuum q hq‖ = 1 := by
  have hsum : HasSum (fun p => (squeezed q p).normSq) (‖vacuum q hq‖ ^ 2) := by
    simpa [Complex.sq_norm, vacuum] using (lp.hasSum_norm (p := 2) (by simp) (vacuum q hq))
  have hsq := hsum.unique (squeezed_normalized hq)
  nlinarith [norm_nonneg (vacuum q hq)]

/-- The actual outgoing number projector, leaving the partner untouched. -/
def hit (n : ℕ) (x : Pair) : Pair :=
  ⟨fun i => if i.1 = n then x i else 0,
    (lp.memℓp x).norm.mono (fun i => by split <;> simp_all)⟩

/-- In a sharp outgoing row only a single diagonal Schmidt coefficient of the vacuum
can contribute, regardless of the partner state. -/
private lemma inner_hit (q : ℂ) (hq : q.normSq < 1) (n : ℕ) (x : Pair) :
    inner ℂ (vacuum q hq) (hit n x) =
      inner ℂ (squeezed q (n, n, ())) (x (n, n, ())) := by
  rw [lp.inner_eq_tsum, tsum_eq_single (n, n, ())]
  · simp [vacuum, hit]
  · rintro ⟨k, m, ⟨⟩⟩ h
    by_cases hk : k = n
    · subst k
      have hm : n ≠ m := by rintro rfl; exact h rfl
      simp [vacuum, hit, squeezed, hm]
    · simp [hit, hk]

private lemma norm_inner_hit_le {q : ℂ} (hq : q.normSq < 1) (n : ℕ) (x : Pair) :
    ‖inner ℂ (vacuum q hq) (hit n x)‖ ≤ Real.sqrt (1 - q.normSq) * ‖x‖ := by
  rw [inner_hit]
  apply (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
  apply mul_le_mul _ (lp.norm_apply_le_norm (by simp) x _) (norm_nonneg _) (Real.sqrt_nonneg _)
  have hqn : ‖q‖ ≤ 1 := by nlinarith [Complex.sq_norm q, norm_nonneg q]
  simp only [squeezed, ite_true, norm_mul, Complex.norm_real, Real.norm_of_nonneg
    (Real.sqrt_nonneg _), norm_pow]
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (pow_le_one₀ (norm_nonneg q) hqn)

variable {R : Type*} [Fintype R]

/-- Applying the vacuum bra to the pair gives an amplitude on the untouched early register. -/
def pairReadout (v : Pair) (ψ : R → Pair) : EuclideanSpace ℂ R :=
  WithLp.toLp 2 (fun r => inner ℂ v (ψ r))

/-- Born probability of the smooth-pair projection in the original state. -/
def pairProbability (v : Pair) (ψ : R → Pair) : ℝ := ‖pairReadout v ψ‖ ^ 2

/-- Total Born probability that the guessed and actual outgoing occupation differ. -/
def errorProbability (guess : R → ℕ) (ψ : R → Pair) : ℝ :=
  ∑ r, ‖ψ r - hit (guess r) (ψ r)‖ ^ 2

/-- Total probability of a correct guess in the complete early basis measurement. -/
def correctProbability (guess : R → ℕ) (ψ : R → Pair) : ℝ :=
  ∑ r, ‖hit (guess r) (ψ r)‖ ^ 2

/-- The successful and erroneous records give orthogonal complementary alternatives. -/
lemma correct_add_error (guess : R → ℕ) (ψ : R → Pair) :
    correctProbability guess ψ + errorProbability guess ψ = ∑ r, ‖ψ r‖ ^ 2 := by
  rw [correctProbability, errorProbability, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  let z := hit (guess r) (ψ r)
  have horth : inner ℂ z (ψ r - z) = 0 := by
    rw [lp.inner_eq_tsum]
    calc
      _ = ∑' _ : ℕ × ℕ × Unit, (0 : ℂ) := by
        apply tsum_congr
        intro i
        change inner ℂ (if i.1 = guess r then ψ r i else 0)
          (ψ r i - (if i.1 = guess r then ψ r i else 0)) = 0
        by_cases h : i.1 = guess r <;> simp [h]
      _ = 0 := tsum_zero
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero z (ψ r - z) horth
  simpa [sq] using h.symm

private lemma hit_smooth (q : ℂ) (hq : q.normSq < 1) (n : ℕ) (u : ℂ) :
    hit n (u • vacuum q hq) = lp.single 2 (n, n, ()) (u * squeezed q (n, n, ())) := by
  apply lp.ext
  funext i
  obtain ⟨k, m, ⟨⟩⟩ := i
  by_cases hk : k = n
  · subst k
    by_cases hm : m = n
    · subst m
      simp [hit, vacuum, lp.coeFn_smul]
    · simp [hit, vacuum, lp.coeFn_smul, squeezed, Ne.symm hm, hm]
  · simp [hit, hk]

/-- Joint Born weight of early record `r` and outgoing occupation `n`, summed over
all occupations of the other mode. -/
def jointProbability (ψ : R → Pair) (r : R) (n : ℕ) : ℝ := ‖hit n (ψ r)‖ ^ 2

/-- Marginal probability of occupation `n` after summing over the complete early basis. -/
def outgoingProbability (ψ : R → Pair) (n : ℕ) : ℝ := ∑ r, jointProbability ψ r n

omit [Fintype R] in
/-- In an exactly smooth pair, every early record sees the same geometric occupation
law. This identity includes records of zero weight, with no conditioning by division. -/
lemma smooth_joint_probability {q : ℂ} (hq : q.normSq < 1) (u : R → ℂ) (r : R) (n : ℕ) :
    jointProbability (fun t => u t • vacuum q hq) r n =
      (u r).normSq * ((1 - q.normSq) * q.normSq ^ n) := by
  rw [jointProbability, hit_smooth, lp.norm_single (by norm_num), Complex.sq_norm,
    Complex.normSq_mul]
  simp [squeezed, Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt (sub_nonneg.mpr
    hq.le)]

/-- The joint law of a normalized exact squeezed pair is the product of the actual
early and outgoing marginal probabilities. -/
lemma smooth_record_independent {q : ℂ} (hq : q.normSq < 1) (u : R → ℂ)
    (hu : ∑ t, (u t).normSq = 1) (r : R) (n : ℕ) :
    jointProbability (fun t => u t • vacuum q hq) r n =
      ‖u r • vacuum q hq‖ ^ 2 * outgoingProbability (fun t => u t • vacuum q hq) n := by
  simp only [outgoingProbability, smooth_joint_probability, ← Finset.sum_mul, hu, one_mul,
    norm_smul, norm_vacuum, mul_one, Complex.sq_norm]

/-- AMPS §2 observes that even partial information about late occupation excludes
an exact vacuum. Here the information is an early record and occupation whose joint
probability differs from the product of their probabilities in the same state. -/
lemma informative_record_excludes_smooth {q : ℂ} (hq : q.normSq < 1) (ψ : R → Pair)
    (hnorm : ∑ t, ‖ψ t‖ ^ 2 = 1)
    (hinfo : ∃ r n, jointProbability ψ r n ≠ ‖ψ r‖ ^ 2 * outgoingProbability ψ n) :
    ¬ ∃ u : R → ℂ, ψ = fun t => u t • vacuum q hq := by
  rintro ⟨u, rfl⟩
  have hu : ∑ t, (u t).normSq = 1 := by
    simpa only [norm_smul, norm_vacuum, mul_one, Complex.sq_norm] using hnorm
  obtain ⟨r, n, h⟩ := hinfo
  exact h (smooth_record_independent hq u hu r n)

/-- In the exact factorized smooth state the guessing probability is a mixture of
thermal number weights, with early outcome probabilities `|u r|²`. -/
lemma smooth_guess_probability {q : ℂ} (hq : q.normSq < 1) (guess : R → ℕ) (u : R → ℂ) :
    correctProbability guess (fun r => u r • vacuum q hq) =
      ∑ r, (u r).normSq * ((1 - q.normSq) * q.normSq ^ guess r) := by
  unfold correctProbability
  apply Finset.sum_congr rfl
  intro r _
  exact smooth_joint_probability hq u r (guess r)

/-- No early guess outperforms always guessing zero when the pair is exactly smooth. -/
lemma optimal_smooth_guess {q : ℂ} (hq : q.normSq < 1) (guess : R → ℕ) (u : R → ℂ)
    (hu : ∑ r, (u r).normSq = 1) :
    correctProbability guess (fun r => u r • vacuum q hq) ≤ 1 - q.normSq ∧
    correctProbability (fun _ => 0) (fun r => u r • vacuum q hq) = 1 - q.normSq := by
  simp only [smooth_guess_probability hq]
  constructor
  · calc
      _ ≤ ∑ r, (u r).normSq * (1 - q.normSq) := by
        apply Finset.sum_le_sum
        intro r _
        exact mul_le_mul_of_nonneg_left
          (mul_le_of_le_one_right (sub_nonneg.mpr hq.le) (pow_le_one₀ (Complex.normSq_nonneg _)
            hq.le))
          (Complex.normSq_nonneg _)
      _ = 1 - q.normSq := by rw [← Finset.sum_mul, hu, one_mul]
  · simp [← Finset.sum_mul, hu]

/-- Complete-readout complementarity bound for any normalized state, with arbitrary
square-summable oscillator tails. The first term is the largest Schmidt amplitude of
the chosen vacuum, `sqrt(1-|q|²)`. No number or energy moment enters the error bound. -/
lemma prediction_pair_test {q : ℂ} (hq : q.normSq < 1) (guess : R → ℕ) (ψ : R → Pair)
    (hnorm : ∑ r, ‖ψ r‖ ^ 2 = 1) :
    Real.sqrt (pairProbability (vacuum q hq) ψ) ≤
      Real.sqrt (1 - q.normSq) + Real.sqrt (errorProbability guess ψ) := by
  let v := vacuum q hq
  let good := fun r => hit (guess r) (ψ r)
  let bad := fun r => ψ r - good r
  let K := Real.sqrt (1 - q.normSq)
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hgood : ‖pairReadout v good‖ ≤ K := by
    rw [← sq_le_sq₀ (norm_nonneg _) hK, EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ r, (K * ‖ψ r‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro r _
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_hit_le hq (guess r) (ψ r)) 2
      _ = K ^ 2 := by simp [mul_pow, ← Finset.mul_sum, hnorm]
  have hbad : ‖pairReadout v bad‖ ≤ Real.sqrt (errorProbability guess ψ) := by
    rw [EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt (Finset.sum_le_sum ?_)
    intro r _
    apply pow_le_pow_left₀ (norm_nonneg _)
    change ‖inner ℂ v (bad r)‖ ≤ ‖bad r‖
    simpa [v, norm_vacuum] using (norm_inner_le_norm (𝕜 := ℂ) v (bad r))
  have hdecomp : pairReadout v ψ = pairReadout v good + pairReadout v bad := by
    ext r : 1
    change inner ℂ v (ψ r) = inner ℂ v (good r) + inner ℂ v (ψ r - good r)
    rw [inner_sub_right]
    abel
  rw [pairProbability, Real.sqrt_sq (norm_nonneg _)]
  change ‖pairReadout v ψ‖ ≤ _
  rw [hdecomp]
  exact (norm_add_le _ _).trans (add_le_add hgood hbad)

/-- With a perfect early record, the vacuum passes with probability at most `1-|q|²`. -/
lemma perfect_record_pair_probability_le {q : ℂ} (hq : q.normSq < 1)
    (guess : R → ℕ) (ψ : R → Pair) (hnorm : ∑ r, ‖ψ r‖ ^ 2 = 1)
    (herr : errorProbability guess ψ = 0) : pairProbability (vacuum q hq) ψ ≤ 1 - q.normSq := by
  have h := prediction_pair_test hq guess ψ hnorm
  rw [herr, Real.sqrt_zero, add_zero] at h
  exact (Real.sqrt_le_sqrt_iff (sub_nonneg.mpr hq.le)).mp h

/-- The perfect-readout bound is attained. Guess zero on the product number vacuum
`|0,0⟩`; the overlap squared with the squeezed pair is exactly its first Schmidt weight. -/
lemma perfect_record_bound_attained {q : ℂ} (hq : q.normSq < 1) :
    ∃ ψ : Unit → Pair, (∑ r, ‖ψ r‖ ^ 2 = 1) ∧
      errorProbability (fun _ => 0) ψ = 0 ∧
      pairProbability (vacuum q hq) ψ = 1 - q.normSq := by
  let x : Pair := lp.single 2 (0, 0, ()) 1
  have hhit : hit 0 x = x := by
    apply lp.ext
    funext i
    obtain ⟨k, m, ⟨⟩⟩ := i
    by_cases hk : k = 0
    · simp [hit, hk]
    · simp [hit, hk, x]
  refine ⟨fun _ => x, ?_, ?_, ?_⟩
  · simp [x, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  · simp [errorProbability, hhit]
  · rw [pairProbability, EuclideanSpace.norm_sq_eq]
    simp [pairReadout, x, lp.inner_single_right, vacuum, squeezed, RCLike.inner_apply,
      Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (sub_nonneg.mpr
        hq.le)]

/-! ## B. One early yes/no readout and one outgoing number outcome -/

/-- Probability of outcome `n` in the outgoing marginal of the specified squeezed pair. -/
def thermalNumberWeight (q : ℂ) (n : ℕ) : ℝ := (1 - q.normSq) * q.normSq ^ n

/-- Born probability of the yes-subspace of an early binary measurement, expressed in
an eigenbasis of its projector. Multiple early labels may correspond to yes. -/
def markedProbability (marked : R → Bool) (ψ : R → Pair) : ℝ :=
  ∑ r ∈ Finset.univ.filter (fun r => marked r = true), ‖ψ r‖ ^ 2

/-- Joint probability of early yes and outgoing occupation `n`, in the same state. -/
def markedJointProbability (marked : R → Bool) (ψ : R → Pair) (n : ℕ) : ℝ :=
  ∑ r ∈ Finset.univ.filter (fun r => marked r = true), jointProbability ψ r n

/-- An exactly smooth pair has its geometric outgoing law on every selected early subspace,
including those of zero weight. -/
lemma smooth_marked_joint_probability {q : ℂ} (hq : q.normSq < 1) (marked : R → Bool)
    (u : R → ℂ) (n : ℕ) :
    markedJointProbability marked (fun r => u r • vacuum q hq) n =
      markedProbability marked (fun r => u r • vacuum q hq) * thermalNumberWeight q n := by
  simp only [markedJointProbability, markedProbability, thermalNumberWeight,
    smooth_joint_probability hq, norm_smul, norm_vacuum, mul_one, Complex.sq_norm, Finset.sum_mul]

/-- Outgoing occupation `n` is orthogonal to its complement for any two rows. -/
lemma hit_inner_miss (n : ℕ) (x y : Pair) : inner ℂ (hit n x) (y - hit n y) = 0 := by
  rw [lp.inner_eq_tsum]
  calc
    _ = ∑' _ : ℕ × ℕ × Unit, (0 : ℂ) := by
      apply tsum_congr
      intro i
      change inner ℂ (if i.1 = n then x i else 0)
        (y i - (if i.1 = n then y i else 0)) = 0
      by_cases h : i.1 = n <;> simp [h]
    _ = 0 := tsum_zero

/-- Squared norms of the two complementary outgoing-number projections sum to the row norm
  squared. -/
lemma hit_split_sq (n : ℕ) (x : Pair) :
    ‖hit n x‖ ^ 2 + ‖x - hit n x‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (hit n x) (x - hit n x) (hit_inner_miss n x x)
  simpa [sq] using h.symm

/-- The overlap cannot exceed the classical two-outcome overlap of the corresponding
number and complementary number measurements. -/
private lemma overlap_le_binary (n : ℕ) (v x : Pair) :
    ‖inner ℂ v x‖ ≤ ‖hit n v‖ * ‖hit n x‖ + ‖v - hit n v‖ * ‖x - hit n x‖ := by
  have hcross : inner ℂ (v - hit n v) (hit n x) = 0 :=
    inner_eq_zero_symm.mp (hit_inner_miss n x v)
  have heq : inner ℂ v x = inner ℂ (hit n v) (hit n x) +
      inner ℂ (v - hit n v) (x - hit n x) := by
    calc
      _ = inner ℂ (hit n v + (v - hit n v)) (hit n x + (x - hit n x)) := by simp
      _ = _ := by simp only [inner_add_left, inner_add_right, hit_inner_miss, hcross, add_zero,
        zero_add]
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm ..) (norm_inner_le_norm ..))

private lemma binary_weight_difference_sq {s t c d A F : ℝ}
    (hunit : c ^ 2 + d ^ 2 = 1) (hmass : s ^ 2 + t ^ 2 = A)
    (hover : F ^ 2 ≤ (c * s + d * t) ^ 2) :
    (s ^ 2 - A * c ^ 2) ^ 2 ≤ A * (A - F ^ 2) := by
  have horth : (d * s - c * t) ^ 2 + (c * s + d * t) ^ 2 = A := by
    calc
      _ = (s ^ 2 + t ^ 2) * (c ^ 2 + d ^ 2) := by ring
      _ = A := by rw [hunit, hmass, mul_one]
  have hsmall : (d * s - c * t) ^ 2 ≤ A - F ^ 2 := by linarith
  have hlarge : (d * s + c * t) ^ 2 ≤ A := by
    calc
      _ ≤ (d * s + c * t) ^ 2 + (c * s - d * t) ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg _)
      _ = (s ^ 2 + t ^ 2) * (c ^ 2 + d ^ 2) := by ring
      _ = A := by rw [hunit, hmass, mul_one]
  have hdiff : s ^ 2 - A * c ^ 2 = (d * s - c * t) * (d * s + c * t) := by
    rw [← hmass]
    linear_combination -(s ^ 2) * hunit
  rw [hdiff, mul_pow, mul_comm A]
  exact mul_le_mul hsmall hlarge (sq_nonneg _) ((sq_nonneg _).trans hsmall)

private lemma binary_row_difference_sq {q : ℂ} (hq : q.normSq < 1) (x : Pair) (n : ℕ) :
    (‖hit n x‖ ^ 2 - ‖x‖ ^ 2 * thermalNumberWeight q n) ^ 2 ≤
      ‖x‖ ^ 2 * (‖x‖ ^ 2 - ‖inner ℂ (vacuum q hq) x‖ ^ 2) := by
  let v := vacuum q hq
  have hc : ‖hit n v‖ ^ 2 = thermalNumberWeight q n := by
    simpa [v, jointProbability, thermalNumberWeight] using
      (smooth_joint_probability hq (fun _ : Unit => 1) () n)
  have hunit : ‖hit n v‖ ^ 2 + ‖v - hit n v‖ ^ 2 = 1 := by
    simpa [v, norm_vacuum] using hit_split_sq n v
  rw [← hc]
  exact binary_weight_difference_sq hunit (hit_split_sq n x)
    (pow_le_pow_left₀ (norm_nonneg _) (overlap_le_binary n v x) 2)

/-- Quantitative binary AMPS test. If early yes has Born probability `a` and its joint
probability with outgoing occupation `n` is `b`, the squared excess `(b-a hₙ)²` is at
most `a` times the rejection probability of the specified smooth pair. The outgoing
number event can be arbitrarily rare. Neither oscillator has an occupation cutoff. -/
lemma binary_prediction_pair_test {q : ℂ} (hq : q.normSq < 1) (marked : R → Bool)
    (ψ : R → Pair) (n : ℕ) (hnorm : ∑ r, ‖ψ r‖ ^ 2 = 1) :
    (markedJointProbability marked ψ n - markedProbability marked ψ * thermalNumberWeight q n) ^ 2 ≤
      markedProbability marked ψ * (1 - pairProbability (vacuum q hq) ψ) := by
  let S := Finset.univ.filter (fun r => marked r = true)
  let loss := fun r => ‖ψ r‖ ^ 2 - ‖inner ℂ (vacuum q hq) (ψ r)‖ ^ 2
  have hpos (r : R) : 0 ≤ loss r := by
    have h : ‖inner ℂ (vacuum q hq) (ψ r)‖ ≤ ‖ψ r‖ := by
      simpa [norm_vacuum] using norm_inner_le_norm (𝕜 := ℂ) (vacuum q hq) (ψ r)
    exact sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) h 2)
  have hsum : ∑ r, loss r = 1 - pairProbability (vacuum q hq) ψ := by
    simp only [loss, Finset.sum_sub_distrib, hnorm, pairProbability, EuclideanSpace.norm_sq_eq]
    rfl
  have hsub : (∑ r ∈ S, loss r) ≤ 1 - pairProbability (vacuum q hq) ψ := by
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hpos i)
  unfold markedProbability markedJointProbability jointProbability
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S (fun i _ => sq_nonneg ‖ψ i‖)
      (fun i _ => hpos i) (fun i _ => binary_row_difference_sq hq (ψ i) n)).trans
    (mul_le_mul_of_nonneg_left hsub (Finset.sum_nonneg (fun i _ => sq_nonneg ‖ψ i‖)))

/-- On a nonzero early branch the deviation of the *conditional* occupation probability
from the thermal value forces a loss of pair fidelity weighted by the branch probability. -/
lemma conditional_number_discrepancy {q : ℂ} (hq : q.normSq < 1) (marked : R → Bool)
    (ψ : R → Pair) (n : ℕ) (hnorm : ∑ r, ‖ψ r‖ ^ 2 = 1) (ha : 0 < markedProbability marked ψ) :
    markedProbability marked ψ *
        (markedJointProbability marked ψ n / markedProbability marked ψ - thermalNumberWeight q
          n) ^ 2 ≤
      1 - pairProbability (vacuum q hq) ψ := by
  have h := binary_prediction_pair_test hq marked ψ n hnorm
  let a := markedProbability marked ψ
  let b := markedJointProbability marked ψ n
  let w := thermalNumberWeight q n
  have heq : a * (a * (b/a - w) ^ 2) = (b - a * w) ^ 2 := by
    field_simp [show a ≠ 0 from ha.ne']
  apply le_of_mul_le_mul_left (a := a) _ ha
  rw [heq]
  exact h

/-! ## C. Spectral measurements of the two infalling oscillators -/

/-- Amplitudes in the simultaneous infalling number basis, with both occupations unbounded. -/
abbrev InfallingPair := lp (fun _ : ℕ × ℕ => ℂ) 2

/-- The joint zero-occupation vector in the infalling basis. -/
def infallingGround : InfallingPair := lp.single 2 (0, 0) 1

/-- Born mass of the occupation pair `k`, tracing over the complete early register. -/
def occupationWeight (φ : R → InfallingPair) (k : ℕ × ℕ) : ℝ := ∑ r, ‖φ r k‖ ^ 2

private lemma occupationWeight_nonneg (φ : R → InfallingPair) (k : ℕ × ℕ) :
    0 ≤ occupationWeight φ k := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private lemma hasSum_occupationWeight (φ : R → InfallingPair) :
    HasSum (occupationWeight φ) (∑ r, ‖φ r‖ ^ 2) := by
  unfold occupationWeight
  apply hasSum_sum
  intro r _
  simpa using lp.hasSum_norm (p := 2) (by simp) (φ r)

/-- Probability of the selected infalling occupation event at a single occupation. -/
def eventWeight (P : ℕ × ℕ → Prop) [DecidablePred P]
    (φ : R → InfallingPair) (k : ℕ × ℕ) : ℝ := if P k then occupationWeight φ k else 0

private lemma summable_eventWeight (P : ℕ × ℕ → Prop) [DecidablePred P]
    (φ : R → InfallingPair) : Summable (eventWeight P φ) := by
  apply Summable.of_nonneg_of_le _ _ (hasSum_occupationWeight φ).summable
  · intro k
    simp only [eventWeight]
    split <;> simp [occupationWeight_nonneg]
  · intro k
    simp only [eventWeight]
    split <;> simp [occupationWeight_nonneg]

/-- Probability of observing both infalling oscillators in their ground state. -/
def jointGroundProbability (φ : R → InfallingPair) : ℝ := occupationWeight φ (0, 0)

/-- Born probability for an ideal counter sensitive to any positive first-mode occupation. -/
def firstClickProbability (φ : R → InfallingPair) : ℝ :=
  ∑' k, eventWeight (fun k => k.1 ≠ 0) φ k

/-- Born probability for an ideal counter sensitive to any positive second-mode occupation. -/
def secondClickProbability (φ : R → InfallingPair) : ℝ :=
  ∑' k, eventWeight (fun k => k.2 ≠ 0) φ k

private lemma nonGround_tsum (φ : R → InfallingPair) (hnorm : ∑ r, ‖φ r‖ ^ 2 = 1) :
    ∑' k, eventWeight (fun k => k ≠ (0, 0)) φ k = 1 - jointGroundProbability φ := by
  have hsum : (∑' k, eventWeight (fun k => k = (0, 0)) φ k) +
      (∑' k, eventWeight (fun k => k ≠ (0, 0)) φ k) = 1 := by
    rw [← (summable_eventWeight _ φ).tsum_add (summable_eventWeight _ φ), ← hnorm,
      ← (hasSum_occupationWeight φ).tsum_eq]
    apply tsum_congr
    intro k
    by_cases h : k = (0, 0) <;> simp [eventWeight, h]
  simpa only [eventWeight, tsum_ite_eq, jointGroundProbability] using eq_sub_of_add_eq' hsum

/-- The joint ground probability is at most one in a normalized state. -/
lemma jointGroundProbability_le_one (φ : R → InfallingPair) (hnorm : ∑ r, ‖φ r‖ ^ 2 = 1) :
    jointGroundProbability φ ≤ 1 := by
  apply sub_nonneg.mp
  rw [← nonGround_tsum φ hnorm]
  apply tsum_nonneg
  intro k
  simp only [eventWeight]
  split <;> simp [occupationWeight_nonneg]

/-- Joint vacuum rejection implies a click in at least one of the two ideal counters,
with probability at least half the joint rejection probability for one of them. -/
lemma one_counter_clicks (φ : R → InfallingPair) (hnorm : ∑ r, ‖φ r‖ ^ 2 = 1) :
    (1 - jointGroundProbability φ) / 2 ≤ firstClickProbability φ ∨
      (1 - jointGroundProbability φ) / 2 ≤ secondClickProbability φ := by
  have hunion : 1 - jointGroundProbability φ ≤ firstClickProbability φ + secondClickProbability
    φ := by
    rw [← nonGround_tsum φ hnorm, firstClickProbability, secondClickProbability,
      ← (summable_eventWeight _ φ).tsum_add (summable_eventWeight _ φ)]
    apply Summable.tsum_le_tsum _ (summable_eventWeight _ φ)
      ((summable_eventWeight _ φ).add (summable_eventWeight _ φ))
    rintro ⟨n, m⟩
    by_cases hn : n = 0 <;> by_cases hm : m = 0 <;>
      simp [eventWeight, Prod.mk.injEq, hn, hm, occupationWeight_nonneg]
  by_cases h : (1 - jointGroundProbability φ) / 2 ≤ firstClickProbability φ
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- Spectral excitation energy above the vacuum in units with `ℏ = 1`. -/
def excitationEnergy (ω₁ ω₂ : ℝ) (k : ℕ × ℕ) : ℝ := ω₁ * k.1 + ω₂ * k.2

/-- Finite quadratic-form domain of the positive additive two-oscillator Hamiltonian:
its energy-weighted Born masses are summable. -/
def FiniteExcitationEnergy (ω₁ ω₂ : ℝ) (φ : R → InfallingPair) : Prop :=
  Summable (fun k => excitationEnergy ω₁ ω₂ k * occupationWeight φ k)

/-- Mean excitation energy, evaluated on states in `FiniteExcitationEnergy`. -/
def meanExcitationEnergy (ω₁ ω₂ : ℝ) (φ : R → InfallingPair) : ℝ :=
  ∑' k, excitationEnergy ω₁ ω₂ k * occupationWeight φ k

/-- Each occupied level costs at least the smaller carrier energy. Expectation is
therefore bounded below by that energy times the probability of joint vacuum rejection. -/
lemma mean_energy_ge_joint_rejection (φ : R → InfallingPair) {ωmin ω₁ ω₂ : ℝ}
    (hmin : 0 ≤ ωmin) (h₁ : ωmin ≤ ω₁) (h₂ : ωmin ≤ ω₂)
    (hnorm : ∑ r, ‖φ r‖ ^ 2 = 1) (hfinite : FiniteExcitationEnergy ω₁ ω₂ φ) :
    ωmin * (1 - jointGroundProbability φ) ≤ meanExcitationEnergy ω₁ ω₂ φ := by
  rw [← nonGround_tsum φ hnorm, ← tsum_mul_left, meanExcitationEnergy]
  apply Summable.tsum_le_tsum _ ((summable_eventWeight _ φ).mul_left _) hfinite
  rintro ⟨n, m⟩
  have hn : 0 ≤ ω₁ := hmin.trans h₁
  have hm : 0 ≤ ω₂ := hmin.trans h₂
  by_cases h : (n, m) = (0, 0)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp [eventWeight, excitationEnergy]
  · simp only [eventWeight, h, ne_eq, not_false_eq_true, ite_true]
    apply mul_le_mul_of_nonneg_right _ (occupationWeight_nonneg _ _)
    change ωmin ≤ ω₁ * (n : ℝ) + ω₂ * (m : ℝ)
    by_cases hzero : n = 0
    · subst n
      have hpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by simpa using h)
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hpos
      simpa using h₂.trans (le_mul_of_one_le_right hm hm')
    · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
      exact (h₁.trans (le_mul_of_one_le_right hn hn')).trans
        (le_add_of_nonneg_right (mul_nonneg hm (Nat.cast_nonneg _)))

/-- A change to infalling coordinates that sends the chosen smooth pair to the joint
ground vector identifies the two vacuum probabilities, also in the presence of an early register. -/
lemma jointGroundProbability_map (U : Pair →ₗᵢ[ℂ] InfallingPair) {q : ℂ} (hq : q.normSq < 1)
    (hground : U (vacuum q hq) = infallingGround) (ψ : R → Pair) :
    jointGroundProbability (fun r => U (ψ r)) = pairProbability (vacuum q hq) ψ := by
  rw [jointGroundProbability, occupationWeight, pairProbability, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro r _
  change ‖U (ψ r) (0, 0)‖ ^ 2 = ‖inner ℂ (vacuum q hq) (ψ r)‖ ^ 2
  rw [← U.inner_map_map, hground]
  simp [infallingGround, lp.inner_single_left, RCLike.inner_apply]

/-- A normalized vector killed by both infalling ladder operators is the squeezed
vacuum up to a phase. Its occupation tail is fixed by the operator equations. -/
lemma normalized_jointVacuum {q α β : ℂ} {x : Pair} (hq : q.normSq < 1)
    (hα : α ≠ 0) (hcoef : α * q + β = 0) (hnorm : ‖x‖ = 1)
    (ha : Packet.infalling α β (fun p => x p) = 0)
    (hb : Packet.partnerInfalling α β (fun p => x p) = 0) :
    ∃ phase : ℂ, ‖phase‖ = 1 ∧ x = phase • vacuum q hq := by
  let a : ℂ := Real.sqrt (1 - q.normSq)
  have hane : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast (Real.sqrt_pos.2 (sub_pos.mpr hq)).ne'
  let phase := x (0,0,()) / a
  have hphase : phase * a = x (0,0,()) := div_mul_cancel₀ _ hane
  have heq : x = phase • vacuum q hq := by
    apply lp.ext
    funext ⟨k,m,e⟩
    cases e
    have h := Packet.jointVacuum_coefficients hα hcoef ha hb k m ()
    change x (k,m,()) = if k = m then _ else _ at h
    rw [h]
    change _ = phase * squeezed q (k,m,())
    by_cases hkm : k = m
    · subst m
      simp only [squeezed, ite_true]
      change q ^ k * x (0,0,()) = phase * (a * q ^ k)
      rw [← hphase]
      ring
    · simp [squeezed, hkm]
  refine ⟨phase, ?_, heq⟩
  have hn := congrArg norm heq
  simpa [hnorm, norm_vacuum, norm_smul] using hn.symm

/-- For a unitary whose pullback of the infalling ground obeys both Bogoliubov
vacuum equations, the ground probability is derived from the squeezed pair
projector. The phase of the vacuum is immaterial. -/
lemma jointGroundProbability_of_pullback_vacuum (U : Pair ≃ₗᵢ[ℂ] InfallingPair)
    {q α β : ℂ} (hq : q.normSq < 1) (hα : α ≠ 0) (hcoef : α * q + β = 0)
    (ha : Packet.infalling α β (fun p => U.symm infallingGround p) = 0)
    (hb : Packet.partnerInfalling α β (fun p => U.symm infallingGround p) = 0)
    (ψ : R → Pair) :
    jointGroundProbability (fun r => U (ψ r)) = pairProbability (vacuum q hq) ψ := by
  have hnorm : ‖U.symm infallingGround‖ = 1 := by
    rw [U.symm.norm_map, infallingGround, lp.norm_single (by norm_num), norm_one]
  obtain ⟨phase, hnormphase, heq⟩ := normalized_jointVacuum hq hα hcoef hnorm ha hb
  rw [jointGroundProbability, occupationWeight, pairProbability, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro r _
  have hg : ‖U (ψ r) (0,0)‖ = ‖inner ℂ infallingGround (U (ψ r))‖ := by
    simp [infallingGround, lp.inner_single_left, RCLike.inner_apply]
  change ‖U (ψ r) (0,0)‖ ^ 2 = ‖inner ℂ (vacuum q hq) (ψ r)‖ ^ 2
  rw [hg, ← U.apply_symm_apply infallingGround, U.inner_map_map, heq, inner_smul_left]
  simp [hnormphase]

end AMPS.VacuumTest
