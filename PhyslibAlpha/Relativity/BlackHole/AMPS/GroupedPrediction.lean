/-
Copyright (c) 2026 AMPS formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AMPS formalization contributors
-/
module

public import PhyslibAlpha.Relativity.BlackHole.AMPS.Prediction

/-!
# Ensemble error for a degenerate occupation

Ensemble moments for a degenerate occupation.

## i. Overview

Appendix A of Almheiri, Marolf, Polchinski and Sully also considers sums of
its single-ray estimators. For a rank-`m` occupation projector the estimator
error needs contractions involving up to six state amplitudes. This file
computes the mean total squared vector error from the three contracted
moments. The inputs are the normalized complex-sphere moments from the
permutation formula in Harrow, arXiv:1308.6595, Proposition 6. The conclusion
weights the error by the state, and never divides by a fine-grained or
state-dependent event probability.

## ii. Key results

* `mean_error_of_moments`
* `mean_error_le_of_moments`

## iii. Table of contents

- A. Ensemble moments for a degenerate occupation

## iv. References

* [ref: Almheiri2013]
* [ref: Harrow2013SymmetricSubspace]

## A. Ensemble moments for a degenerate occupation
-/

@[expose] public section

noncomputable section

namespace AMPS.GroupedPrediction

open Prediction MeasureTheory
open scoped InnerProductSpace

variable {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I]
variable [Fintype J] [DecidableEq J]

/-- The late occupation projection on each state of an ensemble. -/
def selected (n : I → ℕ) (k : ℕ) (ψ : Wave I (EuclideanSpace ℂ J)) :
    Wave I (EuclideanSpace ℂ J) :=
  numberAction (fun j => if n j = k then 1 else 0) ψ

/-- The summed early estimator, applied to the amplitudes of that state. -/
def estimated (n : I → ℕ) (k : ℕ) (ψ : Wave I (EuclideanSpace ℂ J)) :
    Wave I (EuclideanSpace ℂ J) :=
  WithLp.toLp 2 (fun j => (occupationKernel n k ψ).toEuclideanLin (ψ j))

/-- Squared error of the entire event before normalization by its Born weight. -/
def error (n : I → ℕ) (k : ℕ) (ψ : Wave I (EuclideanSpace ℂ J)) : ℝ :=
  ‖selected n k ψ - estimated n k ψ‖ ^ 2

local notation "E" => (Fintype.card J : ℝ)
local notation "L" => (Fintype.card I : ℝ)
/-- The number of late basis states with the selected occupation. -/
def occupationRank (n : I → ℕ) (k : ℕ) : ℝ :=
  ((Finset.univ.filter (fun i => n i = k)).card : ℝ)

/-- The ensemble contractions needed for the whole occupation event. The degree-two
moment is its Born weight, the degree-four moment is the interference with the
early estimate, and the degree-six moment is the estimated squared norm. -/
structure EnsembleMoments (μ : Measure Ω) (n : I → ℕ) (k : ℕ)
    (ψ : Ω → Wave I (EuclideanSpace ℂ J)) : Prop where
  target_integrable : Integrable (fun ω => ‖selected n k (ψ ω)‖ ^ 2) μ
  overlap_integrable : Integrable (fun ω =>
    (inner ℂ (selected n k (ψ ω)) (estimated n k (ψ ω))).re) μ
  estimate_integrable : Integrable (fun ω => ‖estimated n k (ψ ω)‖ ^ 2) μ
  target_mean : (∫ ω, ‖selected n k (ψ ω)‖ ^ 2 ∂μ) = occupationRank n k / L
  overlap_mean : (∫ ω, (inner ℂ (selected n k (ψ ω)) (estimated n k (ψ ω))).re ∂μ) =
    occupationRank n k * (E + occupationRank n k) / (E * L + 1)
  estimate_mean : (∫ ω, ‖estimated n k (ψ ω)‖ ^ 2 ∂μ) =
    (L * (occupationRank n k * (E ^ 2 + E * (L + 2 * occupationRank n k) + occupationRank n k *
      L + 1))) /
      ((E * L + 1) * (E * L + 2))

/-- Exact mean error of the coarse event using the normalized moments. For rank
proportional to the late dimension the result has scale at most (L/E) in the
old-hole regime. This is a mean of total squared errors, with the event probability
included as a weight. -/
lemma mean_error_of_moments [Nonempty I] (μ : Measure Ω) (n : I → ℕ) (k : ℕ)
    (ψ : Ω → Wave I (EuclideanSpace ℂ J)) (h : EnsembleMoments μ n k ψ) :
    (∫ ω, error n k (ψ ω) ∂μ) =
      (occupationRank n k / L) *
        (E * L * (L ^ 2 - 1) + occupationRank n k * L * (L ^ 2 - 4) + L ^ 2 + 2) /
        ((E * L + 1) * (E * L + 2)) := by
  have hL : 0 < L := by exact_mod_cast Fintype.card_pos (α := I)
  have h₁ : 0 < E * L + 1 := by positivity
  have h₂ : 0 < E * L + 2 := by positivity
  simp only [error, norm_sub_sq (𝕜 := ℂ), RCLike.re_to_complex]
  have hdiff : Integrable (fun ω => ‖selected n k (ψ ω)‖ ^ 2 -
      2 * (inner ℂ (selected n k (ψ ω)) (estimated n k (ψ ω))).re) μ :=
    h.target_integrable.sub (h.overlap_integrable.const_mul 2)
  rw [integral_add hdiff h.estimate_integrable,
    integral_sub h.target_integrable (h.overlap_integrable.const_mul 2),
    integral_const_mul, h.target_mean, h.overlap_mean, h.estimate_mean]
  field_simp
  ring

/-- With early dimension at least the late dimension, the mean squared error
is at most twice the selected rank divided by the early dimension. Thus a large
occupation event need not be treated as exponentially many separate tests. -/
lemma mean_error_le_of_moments [Nonempty I] (μ : Measure Ω) (n : I → ℕ) (k : ℕ)
    (ψ : Ω → Wave I (EuclideanSpace ℂ J)) (h : EnsembleMoments μ n k ψ) (hEL : L ≤ E) :
    (∫ ω, error n k (ψ ω) ∂μ) ≤ 2 * occupationRank n k / E := by
  have hL : 1 ≤ L := by exact_mod_cast Fintype.card_pos (α := I)
  have hE : 0 < E := zero_lt_one.trans_le (hL.trans hEL)
  let m := occupationRank n k
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hmL : m ≤ L := by
    dsimp [m, occupationRank]
    exact_mod_cast Finset.card_filter_le Finset.univ (fun i => n i = k)
  rw [mean_error_of_moments μ n k ψ h]
  change (m / L) * _ / _ ≤ 2 * m / E
  by_cases hz : m = 0
  · simp [hz]
  have hm1 : 1 ≤ m := by
    have hnat : 0 < (Finset.univ.filter (fun i => n i = k)).card := by
      by_contra! hzero
      apply hz
      simpa [m, occupationRank] using Nat.eq_zero_of_le_zero hzero
    dsimp [m, occupationRank]
    exact_mod_cast hnat
  have hnum : E * L * (L ^ 2 - 1) + m * L * (L ^ 2 - 4) + L ^ 2 + 2 ≤
      2 * E * L ^ 3 := by
    have he : m * L ^ 3 ≤ E * L ^ 3 := by gcongr; exact hmL.trans hEL
    have hlarge : L ^ 2 ≤ E * L := by nlinarith [mul_le_mul_of_nonneg_right hEL (by positivity :
      0 ≤ L)]
    have hml : 1 ≤ m * L := one_le_mul_of_one_le_of_one_le hm1 hL
    nlinarith only [he, hlarge, hml]
  have hden : E ^ 2 * L ^ 2 ≤ (E * L + 1) * (E * L + 2) := by
    nlinarith [mul_nonneg hE.le (zero_le_one.trans hL)]
  calc
    _ ≤ (m / L) * (2 * E * L ^ 3) / ((E * L + 1) * (E * L + 2)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (by positivity)) (by positivity)
    _ ≤ (m / L) * (2 * E * L ^ 3) / (E ^ 2 * L ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by field_simp

private lemma error_integrable (μ : Measure Ω) (n : I → ℕ) (k : ℕ)
    (ψ : Ω → Wave I (EuclideanSpace ℂ J)) (h : EnsembleMoments μ n k ψ) :
    Integrable (fun ω => error n k (ψ ω)) μ := by
  simp_rw [error, norm_sub_sq (𝕜 := ℂ), RCLike.re_to_complex]
  exact (h.target_integrable.sub (h.overlap_integrable.const_mul 2)).add h.estimate_integrable

/-- In the old-hole regime the fraction of ensemble states with excessive grouped
error is bounded using the grouped moments. The probability samples radiation
states. The Born mass of the selected occupation is a separate random variable. -/
lemma group_error_tail [Nonempty I] (μ : Measure Ω) (n : I → ℕ) (k : ℕ)
    (ψ : Ω → Wave I (EuclideanSpace ℂ J)) (h : EnsembleMoments μ n k ψ)
    (hEL : L ≤ E) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ error n k (ψ ω)} ≤ (2 * occupationRank n k / E) / t := by
  have he : ∀ᵐ ω ∂μ, 0 ≤ error n k (ψ ω) :=
    Filter.Eventually.of_forall fun ω => sq_nonneg _
  have hb := mul_meas_ge_le_integral_of_nonneg he (error_integrable μ n k ψ h) t
  exact (le_div_iff₀ ht).mpr (by rw [mul_comm]; exact hb.trans (mean_error_le_of_moments μ n k ψ
    h hEL))

end AMPS.GroupedPrediction
