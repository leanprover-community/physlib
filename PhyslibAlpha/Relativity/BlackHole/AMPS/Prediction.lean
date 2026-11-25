/-
Copyright (c) 2026 AMPS formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AMPS formalization contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Predicting a late radiation branch from early radiation

Appendix A finite radiation estimates.

## i. Overview

In an orthonormal late basis, a pure early–late vector is a finite family of early
vectors. The Hilbert direct sum gives this expansion its physical norm. For a normalized
incoming vector the squared projected norm is the Born probability of that outcome. We compare
the
late basis projector with the early rank-one operator constructed from the state in
Almheiri, Marolf, Polchinski and Sully, arXiv:1207.3123v4, Appendix A, equations
(A.1)–(A.3). These are statements for each individual vector. The Haar average in
(A.4)–(A.6) requires a distribution on vectors.

## ii. Key results

* `earlyReadout_eq_smul_earlyProjector`
* `earlyProjector_idempotent`

## iii. Table of contents

- A. Appendix A finite radiation estimates

## iv. References

* [ref: Almheiri2013]
* [ref: Harrow2013SymmetricSubspace]

## A. Appendix A finite radiation estimates
-/

@[expose] public section

namespace AMPS.Prediction

open scoped InnerProductSpace
open WithLp
open scoped Pointwise

variable (I E : Type*) [Fintype I] [NormedAddCommGroup E]

/-- A joint pure-state amplitude in a fixed late basis, with the Hilbert direct-sum norm. -/
abbrev Wave := PiLp 2 (fun _ : I => E)

variable {I E} [DecidableEq I] [InnerProductSpace ℂ E]

/-- The late basis projector acts on its selected component and annihilates the others. -/
noncomputable def lateBranch (i : I) (ψ : Wave I E) : Wave I E :=
  toLp 2 (fun j => if j = i then ψ i else 0)

/-- The same early rank-one map acts on every late component of an arbitrary input.
The reference vector and scale are fixed before this map acts on the input. -/
noncomputable def earlyReadout (scale : ℝ) (u : E) (φ : Wave I E) : Wave I E :=
  toLp 2 (fun j => ((scale : ℂ) * ⟪u, φ j⟫_ℂ) • u)

/-- The physical early outcome is orthogonal projection onto the ray of the early vector.
For a zero reference vector this is the zero map. -/
noncomputable def earlyProjector (u : E) (φ : Wave I E) : Wave I E :=
  toLp 2 (fun j => (ℂ ∙ u).starProjection (φ j))

omit [Fintype I] [DecidableEq I] in
/-- Rescaling the early orthogonal projection reproduces the AMPS readout.
For a nonzero reference and positive scale the two therefore give the same conditional ray. -/
lemma earlyReadout_eq_smul_earlyProjector (scale : ℝ) (u : E) (φ : Wave I E) :
    earlyReadout scale u φ = (((scale * ‖u‖ ^ 2 : ℝ) : ℂ)) • earlyProjector u φ := by
  ext j
  change ((scale : ℂ) * ⟪u, φ j⟫_ℂ) • u =
    (((scale * ‖u‖ ^ 2 : ℝ) : ℂ)) • (ℂ ∙ u).starProjection (φ j)
  rw [Complex.ofReal_mul, mul_smul, mul_smul]
  exact congrArg (fun x : E => (scale : ℂ) • x)
    (Submodule.smul_starProjection_singleton ℂ (v := u) (φ j)).symm

omit [Fintype I] [DecidableEq I] in
/-- The normalized rank-one early map is idempotent, including the zero-vector case. -/
lemma earlyProjector_idempotent (u : E) (φ : Wave I E) :
    earlyProjector u (earlyProjector u φ) = earlyProjector u φ := by
  ext j
  exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)

omit [DecidableEq I] in
/-- The normalized early map is self-adjoint on the full early–late Hilbert space. -/
lemma earlyProjector_symmetric (u : E) (φ χ : Wave I E) :
    ⟪earlyProjector u φ, χ⟫_ℂ = ⟪φ, earlyProjector u χ⟫_ℂ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact Submodule.inner_starProjection_left_eq_right _ _ _

/-- AMPS's early estimate of the selected late branch, with scale equal to the late dimension. -/
noncomputable def earlyBranch (i : I) (ψ : Wave I E) : Wave I E :=
  earlyReadout (Fintype.card I : ℝ) (ψ i) ψ

/-- Outgoing number is diagonal in the chosen number basis; degeneracies are allowed. -/
noncomputable def numberAction (n : I → ℂ) (ψ : Wave I E) : Wave I E :=
  toLp 2 (fun j => n j • ψ j)

omit [Fintype I] [InnerProductSpace ℂ E] in
@[simp] lemma lateBranch_apply (i j : I) (ψ : Wave I E) :
    lateBranch i ψ j = if j = i then ψ i else 0 := rfl

omit [DecidableEq I] in
@[simp] lemma earlyBranch_apply (i j : I) (ψ : Wave I E) :
    earlyBranch i ψ j = ((Fintype.card I : ℂ) * ⟪ψ i, ψ j⟫_ℂ) • ψ i := by
  simp [earlyBranch, earlyReadout]

omit [Fintype I] [InnerProductSpace ℂ E] in
/-- The late outcome has nonzero Born weight precisely when its component is nonzero. -/
lemma lateBranch_ne_zero_iff (i : I) (ψ : Wave I E) : lateBranch i ψ ≠ 0 ↔ ψ i ≠ 0 := by
  constructor
  · intro h hzero
    apply h
    ext j
    simp [hzero]
  · intro h hzero
    have hcoord := congrArg (fun x : Wave I E => x i) hzero
    exact h (by simpa using hcoord)

omit [Fintype I] in
/-- Postselecting any nonzero late branch gives a sharp outgoing number even before
  normalization. -/
lemma lateBranch_number_sharp (n : I → ℂ) (i : I) (ψ : Wave I E) :
    numberAction n (lateBranch i ψ) = n i • lateBranch i ψ := by
  ext j
  change n j • (if j = i then ψ i else 0) = n i • (if j = i then ψ i else 0)
  by_cases h : j = i <;> simp [h]

/-- An orthogonal, equally weighted early Gram row makes the early reconstruction exact.
Only the row belonging to the measured outcome is needed. -/
lemma earlyBranch_eq_lateBranch (i : I) (ψ : Wave I E)
    (hgram : ∀ j, (Fintype.card I : ℂ) * ⟪ψ i, ψ j⟫_ℂ = if j = i then 1 else 0) :
    earlyBranch i ψ = lateBranch i ψ := by
  ext j
  simp only [lateBranch_apply, earlyBranch_apply, hgram]
  split <;> simp

omit [InnerProductSpace ℂ E] in
/-- The squared norm of the unnormalized projected state is its branch weight. -/
lemma norm_lateBranch_sq (i : I) (ψ : Wave I E) : ‖lateBranch i ψ‖ ^ 2 = ‖ψ i‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [lateBranch, apply_ite]

/-- In the ideal equal-weight case a single fine-grained outcome can be rare: its Born
weight is the reciprocal of the full late dimension. -/
lemma exact_branch_weight (i : I) (ψ : Wave I E)
    (hdiag : (Fintype.card I : ℂ) * ⟪ψ i, ψ i⟫_ℂ = 1) :
    ‖lateBranch i ψ‖ ^ 2 = 1 / (Fintype.card I : ℝ) := by
  have : Nonempty I := ⟨i⟩
  have hpos : (0 : ℝ) < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [inner_self_eq_norm_sq_to_K] at hdiag
  have hreal : (Fintype.card I : ℝ) * ‖ψ i‖ ^ 2 = 1 := by
    simpa [Complex.mul_re, ← Complex.ofReal_pow] using congrArg Complex.re hdiag
  rw [norm_lateBranch_sq, eq_div_iff hpos.ne', mul_comm]
  exact hreal

/-- The squared relative prediction error as a sum of squared errors in the Gram row.
The diagonal term is the normalization error and all remaining terms are cross overlaps. -/
noncomputable def gramError (i : I) (ψ : Wave I E) : ℝ :=
  ∑ j, ‖(if j = i then (1 : ℂ) else 0) -
    (Fintype.card I : ℂ) * ⟪ψ i, ψ j⟫_ℂ‖ ^ 2

/-- Appendix A.3 before division, valid also for a zero-weight branch. -/
lemma prediction_distance_sq (i : I) (ψ : Wave I E) :
    ‖lateBranch i ψ - earlyBranch i ψ‖ ^ 2 = gramError i ψ * ‖ψ i‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, gramError, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  have htarget : lateBranch i ψ j = (if j = i then (1 : ℂ) else 0) • ψ i := by
    by_cases h : j = i <;> simp [h]
  simp only [PiLp.sub_apply, htarget, earlyBranch_apply, ← sub_smul, norm_smul, mul_pow]

/-- AMPS A.3 for a nonzero projected component. -/
lemma relative_prediction_error (i : I) (ψ : Wave I E) (h : ψ i ≠ 0) :
    ‖lateBranch i ψ - earlyBranch i ψ‖ ^ 2 / ‖lateBranch i ψ‖ ^ 2 = gramError i ψ := by
  rw [prediction_distance_sq, norm_lateBranch_sq]
  exact mul_div_cancel_right₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr h))

/-- A sample whose Gram error is at most ε² has relative Hilbert-space error at most ε. -/
lemma prediction_distance_le (i : I) (ψ : Wave I E) {ε : ℝ} (hε : 0 ≤ ε)
    (hgram : gramError i ψ ≤ ε ^ 2) :
    ‖earlyBranch i ψ - lateBranch i ψ‖ ≤ ε * ‖lateBranch i ψ‖ := by
  have hsq := mul_le_mul_of_nonneg_right hgram (sq_nonneg ‖ψ i‖)
  rw [← prediction_distance_sq, ← norm_lateBranch_sq, ← mul_pow, norm_sub_rev] at hsq
  exact le_of_sq_le_sq hsq (mul_nonneg hε (norm_nonneg _))

/-- Born weight of disagreeing yes/no outcomes for the early ray and the selected late
basis projector. At late label `i` the error is an early no; at all other labels it is
an early yes. The independent tensor factors allow both outcomes to be read jointly. -/
noncomputable def rayDisagreement (u : E) (i : I) (ψ : Wave I E) : ℝ :=
  ∑ j, if j = i then ‖ψ j - earlyProjector u ψ j‖ ^ 2 else ‖earlyProjector u ψ j‖ ^ 2

/-- For a normalized input the mismatch probability of the two commuting projectors
is their squared vector difference. This holds for an arbitrary early ray. -/
lemma rayDisagreement_eq_norm_sq (u : E) (i : I) (ψ : Wave I E) :
    rayDisagreement u i ψ = ‖lateBranch i ψ - earlyProjector u ψ‖ ^ 2 := by
  rw [rayDisagreement, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j = i <;> simp [PiLp.sub_apply, h]

omit [Fintype I] [DecidableEq I] in
/-- On a true late yes outcome, the early vector lies exactly in its own ray: the
physical Appendix A test has zero false-negative probability. -/
lemma ray_accepts_selected_component (i : I) (ψ : Wave I E) :
    earlyProjector (ψ i) ψ i = ψ i :=
  Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self _)

/-- The early yes marginal is the true-positive weight plus the false positives.
The selected late component always gives an early yes for this ray test. -/
lemma earlyYes_eq_lateYes_add_rayDisagreement (i : I) (ψ : Wave I E) :
    ‖earlyProjector (ψ i) ψ‖ ^ 2 = ‖ψ i‖ ^ 2 + rayDisagreement (ψ i) i ψ := by
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ = ∑ j, ((if j = i then ‖ψ i‖ ^ 2 else 0) +
        (if j = i then ‖ψ j - earlyProjector (ψ i) ψ j‖ ^ 2
         else ‖earlyProjector (ψ i) ψ j‖ ^ 2)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : j = i <;> simp [h, ray_accepts_selected_component]
    _ = _ := by rw [Finset.sum_add_distrib]; simp [rayDisagreement]

/-- Exact conversion of the Appendix A.3 vector error to yes/no measurement error.
The first term is the diagonal rescaling error of the paper's estimator. The second
is the physical probability of false positives times the squared scaling factor. -/
lemma gramError_eq_rescaling_add_disagreement (i : I) (ψ : Wave I E) :
    let s := (Fintype.card I : ℝ) * ‖ψ i‖ ^ 2
    gramError i ψ * ‖ψ i‖ ^ 2 =
      (1 - s) ^ 2 * ‖ψ i‖ ^ 2 + s ^ 2 * rayDisagreement (ψ i) i ψ := by
  let s := (Fintype.card I : ℝ) * ‖ψ i‖ ^ 2
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have diag (v : E) : ‖v - (s : ℂ) • v‖ ^ 2 = (1 - s) ^ 2 * ‖v‖ ^ 2 := by
    calc
      _ = ‖((1 - s : ℝ) : ℂ) • v‖ ^ 2 := by
        rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
      _ = _ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have scaled : earlyBranch i ψ = (s : ℂ) • earlyProjector (ψ i) ψ :=
    earlyReadout_eq_smul_earlyProjector _ _ _
  rw [← prediction_distance_sq, PiLp.norm_sq_eq_of_L2, scaled]
  calc
    _ = ∑ j, ((if j = i then (1 - s) ^ 2 * ‖ψ i‖ ^ 2 else 0) + s ^ 2 *
      (if j = i then ‖ψ j - earlyProjector (ψ i) ψ j‖ ^ 2
       else ‖earlyProjector (ψ i) ψ j‖ ^ 2)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j = i
      · subst j
        simpa [PiLp.sub_apply, PiLp.smul_apply, ray_accepts_selected_component] using diag (ψ i)
      · simp [PiLp.sub_apply, PiLp.smul_apply, hj, norm_smul, mul_pow,
          Real.norm_of_nonneg hs]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [rayDisagreement, s]

/-- On an early yes outcome, the conditional probability of a true late yes is at
least one minus the Appendix A.3 Gram error. This form clears the positive early
yes weight. The only branch-weight hypothesis is that the target component is live. -/
lemma ray_posterior_lower_bound (i : I) (ψ : Wave I E) (hlive : ψ i ≠ 0) :
    (1 - gramError i ψ) * (‖ψ i‖ ^ 2 + rayDisagreement (ψ i) i ψ) ≤ ‖ψ i‖ ^ 2 := by
  let p := ‖ψ i‖ ^ 2
  let d := rayDisagreement (ψ i) i ψ
  let g := gramError i ψ
  let s := (Fintype.card I : ℝ) * p
  have hp : 0 < p := pow_pos (norm_pos_iff.mpr hlive) _
  have he : g * p = (1 - s) ^ 2 * p + s ^ 2 * d :=
    gramError_eq_rescaling_add_disagreement i ψ
  have hprod : p * 0 ≤ p * (g * (p + d) - d) := by
    calc
      _ = 0 := mul_zero _
      _ ≤ (p - s * (p + d)) ^ 2 := sq_nonneg _
      _ = _ := by linear_combination -(p + d) * he
  change (1 - g) * (p + d) ≤ p
  nlinarith only [le_of_mul_le_mul_left hprod hp]

/-- If A.3 is at most ε², the scaled root mismatch is at most ε times the selected
branch norm. The statement also covers zero-weight branches. -/
lemma rayDisagreement_bound (i : I) (ψ : Wave I E) {ε : ℝ} (hε : 0 ≤ ε)
    (hgram : gramError i ψ ≤ ε ^ 2) :
    ((Fintype.card I : ℝ) * ‖ψ i‖ ^ 2) * Real.sqrt (rayDisagreement (ψ i) i ψ) ≤
      ε * ‖ψ i‖ := by
  have hD : 0 ≤ rayDisagreement (ψ i) i ψ := by
    rw [rayDisagreement_eq_norm_sq]
    positivity
  have h := mul_le_mul_of_nonneg_right hgram (sq_nonneg ‖ψ i‖)
  rw [gramError_eq_rescaling_add_disagreement] at h
  have hscaled := (le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) (sq_nonneg ‖ψ i‖))).trans h
  apply le_of_sq_le_sq _ (mul_nonneg hε (norm_nonneg _))
  simpa only [mul_pow, Real.sq_sqrt hD] using hscaled

/-- A.3 controls the calibration factor of the paper's rank-one estimator at the
same time as the cross overlaps. -/
lemma gramError_controls_scale (i : I) (ψ : Wave I E) {ε : ℝ} (hε : 0 ≤ ε)
    (hgram : gramError i ψ ≤ ε ^ 2) :
    1 - ε ≤ (Fintype.card I : ℝ) * ‖ψ i‖ ^ 2 := by
  let entry (j : I) : ℂ := (if j = i then 1 else 0) -
    (Fintype.card I : ℂ) * ⟪ψ i, ψ j⟫_ℂ
  have hone : ‖entry i‖ ^ 2 ≤ gramError i ψ :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖entry j‖) (Finset.mem_univ i)
  have hdiag : entry i = ((1 - (Fintype.card I : ℝ) * ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
    simp [entry, inner_self_eq_norm_sq_to_K]
  rw [hdiag, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hone
  linarith [le_of_sq_le_sq (hone.trans hgram) hε]

/-- For ε < 1, the fraction of root error relative to the target branch norm is at
most ε/(1−ε). No separate branch-weight or calibration hypothesis is needed. -/
lemma rayDisagreement_relative_bound (i : I) (ψ : Wave I E) {ε : ℝ} (hε : 0 ≤ ε)
    (hgram : gramError i ψ ≤ ε ^ 2) :
    (1 - ε) * Real.sqrt (rayDisagreement (ψ i) i ψ) ≤ ε * ‖ψ i‖ :=
  (mul_le_mul_of_nonneg_right (gramError_controls_scale i ψ hε hgram)
    (Real.sqrt_nonneg _)).trans (rayDisagreement_bound i ψ hε hgram)

/-- The square root of the physical yes/no error is at most ε/(1−ε) times the
selected component norm whenever the Appendix A.3 Gram error is at most ε². -/
lemma rayDisagreement_sqrt_le (i : I) (ψ : Wave I E) {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : ε < 1) (hgram : gramError i ψ ≤ ε ^ 2) :
    Real.sqrt (rayDisagreement (ψ i) i ψ) ≤ ε * ‖ψ i‖ / (1 - ε) := by
  apply (le_div_iff₀ (sub_pos.mpr hsmall)).2
  simpa only [mul_comm (Real.sqrt _)] using rayDisagreement_relative_bound i ψ hε hgram

/-- Spectral decomposition of the finite outgoing number observable; different basis
vectors may share the same occupation. -/
lemma numberAction_eq_sum (n : I → ℂ) (ψ : Wave I E) :
    numberAction n ψ = ∑ i, n i • lateBranch i ψ := by
  ext j
  change n j • ψ j = (∑ i, n i • lateBranch i ψ) j
  simp [smul_ite]

/-- Turning approximate projection predictions into a number-amplitude prediction costs
the absolute values of the occupied number eigenvalues. Thus good individual projection
errors alone give no dimension-independent bound for an unbounded number observable. -/
lemma number_prediction_distance_le (n : I → ℂ) (ψ : Wave I E) (ε : I → ℝ)
    (hε : ∀ i, 0 ≤ ε i) (hgram : ∀ i, gramError i ψ ≤ ε i ^ 2) :
    ‖numberAction n ψ - ∑ i, n i • earlyBranch i ψ‖ ≤
      ∑ i, ‖n i‖ * ε i * ‖lateBranch i ψ‖ := by
  rw [numberAction_eq_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖n i • lateBranch i ψ - n i • earlyBranch i ψ‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← smul_sub, norm_smul, norm_sub_rev, mul_assoc]
      exact mul_le_mul_of_nonneg_left (prediction_distance_le i ψ (hε i) (hgram i)) (norm_nonneg _)

/-- The expanded Gram-row formula isolates precisely the second and fourth moments
used in the Appendix A ensemble calculation. -/
lemma gramError_expand (i : I) (ψ : Wave I E) :
    gramError i ψ = 1 - 2 * (Fintype.card I : ℝ) * ‖ψ i‖ ^ 2 +
      (Fintype.card I : ℝ) ^ 2 * ∑ j, ‖⟪ψ i, ψ j⟫_ℂ‖ ^ 2 := by
  have h (j : I) :
      ‖(if j = i then (1 : ℂ) else 0) - (Fintype.card I : ℂ) * ⟪ψ i, ψ j⟫_ℂ‖ ^ 2 =
        (if j = i then 1 - 2 * (Fintype.card I : ℝ) * ‖ψ i‖ ^ 2 else 0) +
          (Fintype.card I : ℝ) ^ 2 * ‖⟪ψ i, ψ j⟫_ℂ‖ ^ 2 := by
    by_cases hji : j = i
    · subst j
      simp [inner_self_eq_norm_sq_to_K, Complex.sq_norm, Complex.normSq_apply,
        ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im]
      ring
    · simp [hji, mul_pow]
  unfold gramError
  simp_rw [h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

section Moments

open MeasureTheory

variable {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
local notation "L" => (Fintype.card I : ℝ)
local notation "D" => (Fintype.card J : ℝ)

/-- Exact ensemble mean of the *samplewise relative error* given the normalized complex
unit-sphere second moment and contracted fourth moment. AMPS use their leading-order forms;
the result here is (L²−1)/(DL+1), with leading term L/D. The hypotheses display the
probabilistic inputs explicitly: this statement does not construct Haar measure or prove
its moments. The exact normalization follows from the second symmetric-tensor moment,
Harrow, arXiv:1308.6595, Proposition 6. The branch is required to have nonzero weight almost
  surely. -/
lemma mean_relative_error_of_moments (i : I) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ψ : Ω → Wave I (EuclideanSpace ℂ J))
    (hbranch : ∀ᵐ ω ∂μ, ψ ω i ≠ 0)
    (hw : Integrable (fun ω => ‖ψ ω i‖ ^ 2) μ)
    (hg : Integrable (fun ω => ∑ j, ‖⟪ψ ω i, ψ ω j⟫_ℂ‖ ^ 2) μ)
    (hsecond : ∫ ω, ‖ψ ω i‖ ^ 2 ∂μ = 1 / L)
    (hfourth : ∫ ω, (∑ j, ‖⟪ψ ω i, ψ ω j⟫_ℂ‖ ^ 2) ∂μ = (D + L) / (L * (D * L + 1))) :
    ∫ ω, ‖lateBranch i (ψ ω) - earlyBranch i (ψ ω)‖ ^ 2 / ‖lateBranch i (ψ ω)‖ ^ 2 ∂μ =
      (L ^ 2 - 1) / (D * L + 1) := by
  have hdim : (0 : ℝ) < L := by
    have : Nonempty I := ⟨i⟩
    exact_mod_cast Fintype.card_pos
  have hdenom : (0 : ℝ) < D * L + 1 := by positivity
  have hsub : Integrable (fun ω => (1 : ℝ) - (2 * L) * ‖ψ ω i‖ ^ 2) μ :=
    (integrable_const (1 : ℝ)).sub (hw.const_mul (2 * L))
  calc
    _ = ∫ ω, (1 - 2 * L * ‖ψ ω i‖ ^ 2 + L ^ 2 * ∑ j, ‖⟪ψ ω i, ψ ω j⟫_ℂ‖ ^ 2) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hbranch] with ω hω
      rw [relative_prediction_error i (ψ ω) hω, gramError_expand]
    _ = _ := by
      rw [integral_add hsub (hg.const_mul (L ^ 2)),
        integral_sub (integrable_const (1 : ℝ)) (hw.const_mul (2 * L)), integral_const_mul,
        integral_const_mul, hsecond, hfourth]
      simp only [integral_const, probReal_univ, one_smul]
      field_simp
      ring

/-- For a fixed late branch and a positive allowed relative squared error, bound the
fraction of states for which the Appendix A estimator exceeds the tolerance. The measure
here samples states, whereas the ray test within each state has its own Born weights. -/
lemma probability_of_large_ray_error (i : I) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ψ : Ω → Wave I (EuclideanSpace ℂ J))
    (hbranch : ∀ᵐ ω ∂μ, ψ ω i ≠ 0)
    (hw : Integrable (fun ω => ‖ψ ω i‖ ^ 2) μ)
    (hg : Integrable (fun ω => ∑ j, ‖⟪ψ ω i, ψ ω j⟫_ℂ‖ ^ 2) μ)
    (hsecond : ∫ ω, ‖ψ ω i‖ ^ 2 ∂μ = 1 / L)
    (hfourth : ∫ ω, (∑ j, ‖⟪ψ ω i, ψ ω j⟫_ℂ‖ ^ 2) ∂μ = (D + L) / (L * (D * L + 1))) {t : ℝ}
    (ht : 0 < t) :
    μ.real {ω | t ≤ gramError i (ψ ω)} ≤ ((L ^ 2 - 1) / (D * L + 1)) / t := by
  have hint : Integrable (fun ω => gramError i (ψ ω)) μ := by
    simp_rw [gramError_expand]
    exact (((integrable_const (1 : ℝ)).sub (hw.const_mul (2 * L))).add (hg.const_mul (L ^ 2)))
  have hpos : ∀ᵐ ω ∂μ, 0 ≤ gramError i (ψ ω) :=
    Filter.Eventually.of_forall fun ω => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hm := mul_meas_ge_le_integral_of_nonneg hpos hint t
  have heq : (∫ ω, gramError i (ψ ω) ∂μ) = (L ^ 2 - 1) / (D * L + 1) := by
    rw [← mean_relative_error_of_moments i μ ψ hbranch hw hg hsecond hfourth]
    apply integral_congr_ae
    filter_upwards [hbranch] with ω hω
    exact (relative_prediction_error i (ψ ω) hω).symm
  exact (le_div_iff₀ ht).mpr (by rw [mul_comm]; exact hm.trans_eq heq)

end Moments

section Coordinates

variable {J : Type*} [Fintype J]

/-- Matrix on the early radiation alone. Its entries depend on the reference early vector
and on no spectator coordinate. -/
noncomputable def earlyKernel (scale : ℝ) (u : EuclideanSpace ℂ J) : Matrix J J ℂ :=
  fun a b => (scale : ℂ) * u a * star (u b)

omit [Fintype I] [DecidableEq I] in
/-- The same early matrix acts at every value of the spectator index. Here the spectator is
the outgoing basis, but the formula applies to any finite independent spectator. -/
lemma earlyReadout_coordinates (scale : ℝ) (u : EuclideanSpace ℂ J)
    (φ : Wave I (EuclideanSpace ℂ J)) (j : I) (a : J) :
    earlyReadout scale u φ j a = ∑ b, earlyKernel scale u a b * φ j b := by
  change (((scale : ℂ) * ⟪u, φ j⟫_ℂ) * u a) = _
  rw [PiLp.inner_apply, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  simp only [earlyKernel, RCLike.inner_apply', Complex.star_def]
  ring

omit [DecidableEq I] in
/-- Evaluated on the outgoing state, this early matrix is exactly the AMPS predictor. -/
lemma earlyBranch_coordinates (i : I) (ψ : Wave I (EuclideanSpace ℂ J)) (j : I) (a : J) :
    earlyBranch i ψ j a =
      ∑ b, earlyKernel (Fintype.card I : ℝ) (ψ i) a b * ψ j b :=
  earlyReadout_coordinates _ _ _ _ _

/-- One early matrix predicts the full eigenspace of a possibly degenerate outgoing
occupation number. It sums the rank-one Appendix A readouts for every late basis
vector with the chosen occupation. -/
noncomputable def occupationKernel (n : I → ℕ) (k : ℕ) (ψ : Wave I (EuclideanSpace ℂ J)) :
    Matrix J J ℂ :=
  ∑ i ∈ Finset.univ.filter (fun i => n i = k), earlyKernel (Fintype.card I : ℝ) (ψ i)

omit [DecidableEq I] [Fintype J] in
/-- The summed Appendix A estimator is Hermitian and hence has a real spectrum and an
orthonormal eigenbasis. Thresholding its eigenvalues defines a projective early test. -/
lemma occupationKernel_isHermitian (n : I → ℕ) (k : ℕ) (ψ : Wave I (EuclideanSpace ℂ J)) :
    (occupationKernel n k ψ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  simp only [occupationKernel, Matrix.sum_apply, star_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [earlyKernel, star_mul, mul_assoc, mul_comm]

omit [DecidableEq I] in
/-- The same early matrix acts on every late row, producing precisely the sum of the
Appendix A estimators associated to the selected occupation. -/
lemma occupationKernel_action [DecidableEq J] (n : I → ℕ) (k : ℕ)
    (ψ : Wave I (EuclideanSpace ℂ J)) :
    (toLp 2 (fun j => (occupationKernel n k ψ).toEuclideanLin (ψ j)) :
      Wave I (EuclideanSpace ℂ J)) =
      ∑ i ∈ Finset.univ.filter (fun i => n i = k), earlyBranch i ψ := by
  ext j a
  change (∑ b, occupationKernel n k ψ a b * ψ j b) =
    (WithLp.ofLp ((WithLp.ofLp (∑ i ∈ Finset.univ.filter (fun i => n i = k),
      earlyBranch i ψ)) j)) a
  simp only [WithLp.ofLp_sum, Finset.sum_apply, occupationKernel, Matrix.sum_apply,
    Finset.sum_mul, earlyBranch_coordinates]
  rw [Finset.sum_comm]

/-- Samplewise coarse-projector estimate for the last sentence of Appendix A. Each
selected late row contributes its own Gram error and branch weight. A highly
degenerate occupation can have many such contributions. -/
lemma occupationKernel_error_le [DecidableEq J] (n : I → ℕ) (k : ℕ)
    (ψ : Wave I (EuclideanSpace ℂ J)) (ε : I → ℝ)
    (hε : ∀ i, n i = k → 0 ≤ ε i) (hgram : ∀ i, n i = k → gramError i ψ ≤ ε i ^ 2) :
    ‖numberAction (fun j => if n j = k then 1 else 0) ψ -
      toLp 2 (fun j => (occupationKernel n k ψ).toEuclideanLin (ψ j))‖ ≤
      ∑ i ∈ Finset.univ.filter (fun i => n i = k), ε i * ‖lateBranch i ψ‖ := by
  let S := Finset.univ.filter (fun i => n i = k)
  have late : numberAction (fun j => if n j = k then 1 else 0) ψ = ∑ i ∈ S, lateBranch i ψ := by
    rw [numberAction_eq_sum]
    simp [S, Finset.sum_filter, ite_smul]
  rw [occupationKernel_action, late, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  refine Finset.sum_le_sum fun i hi => ?_
  have hk := (Finset.mem_filter.mp hi).2
  rw [norm_sub_rev]
  exact prediction_distance_le i ψ (hε i hk) (hgram i hk)

/-- For equally weighted, orthogonal early components, the early matrix reproduces the
outgoing occupation projector on the entire joint state without access to any late index. -/
lemma occupationKernel_predicts (n : I → ℕ) (k : ℕ) (ψ : Wave I (EuclideanSpace ℂ J))
    (hgram : ∀ i, n i = k → ∀ j, (Fintype.card I : ℂ) * ⟪ψ i, ψ j⟫_ℂ =
      if j = i then 1 else 0) (j : I) (a : J) :
    ∑ b, occupationKernel n k ψ a b * ψ j b = if n j = k then ψ j a else 0 := by
  classical
  let S := Finset.univ.filter (fun i => n i = k)
  have hsum (b : J) : occupationKernel n k ψ a b =
      ∑ i ∈ S, earlyKernel (Fintype.card I : ℝ) (ψ i) a b := by
    simp [occupationKernel, S, Matrix.sum_apply]
  simp_rw [hsum, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i ∈ S, (if j = i then ψ i a else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← earlyBranch_coordinates, earlyBranch_eq_lateBranch i ψ
        (hgram i (Finset.mem_filter.mp hi).2), lateBranch_apply]
      split <;> rfl
    _ = _ := by
      by_cases hj : n j = k <;> simp [S, hj]

end Coordinates

end AMPS.Prediction
