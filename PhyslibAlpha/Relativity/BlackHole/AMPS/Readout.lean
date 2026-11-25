/-
Copyright (c) 2026 AMPS formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AMPS formalization contributors
-/
module

public import PhyslibAlpha.Relativity.BlackHole.AMPS.Experiment

/-!
# A common-state realization of the AMPS binary readout

One state and its two Born weights.

## i. Overview

A finite late basis is encoded by distinct outgoing and partner occupation pairs.
The freely chosen amplitudes give a vector in the full two-oscillator Hilbert
space at each early record. The number event sums over every partner occupation.
For the single early ray of interest, choose the early basis with that ray at
one coordinate. Thus the same amplitudes determine both probabilities entering
the finite-error AMPS comparison. The compared squeezed vacuum retains its
entire infinite occupation tail.

## ii. Key results

* `embed_sub_smul`
* `norm_embed_sq`

## iii. Table of contents

- A. One state and its two Born weights

## iv. References

* [ref: Almheiri2013]

## A. One state and its two Born weights
-/

@[expose] public section

noncomputable section

namespace AMPS.Readout

open Prediction VacuumTest Experiment
open scoped InnerProductSpace

variable {I R : Type*} [Fintype I] [Fintype R]

/-- Place a finite family of late amplitudes at distinct oscillator basis states. -/
def embed (label : I ↪ ℕ × ℕ × Unit) (x : I → ℂ) : Pair :=
  ∑ j, lp.single 2 (label j) (x j)

private lemma embed_apply (label : I ↪ ℕ × ℕ × Unit) (x : I → ℂ) (j : I) :
    embed label x (label j) = x j := by
  classical
  unfold embed
  rw [lp.coeFn_sum, Finset.sum_apply, Finset.sum_eq_single j]
  · exact lp.single_apply_self ..
  · intro k _ h
    exact lp.single_apply_ne _ _ _ (fun he => h (label.injective he.symm))
  · simp

/-- Linear operations on a finite occupation array commute with its embedding. -/
lemma embed_sub_smul (label : I ↪ ℕ × ℕ × Unit) (a : ℂ) (x y : I → ℂ) :
    embed label x - a • embed label y = embed label (fun j => x j - a * y j) := by
  classical
  simp only [embed, Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply lp.ext
  funext i
  change (lp.single (E := fun _ : ℕ × ℕ × Unit => ℂ) 2 (label j) (x j) : Pair) i -
    a * (lp.single 2 (label j) (y j) : Pair) i =
    (lp.single 2 (label j) (x j - a * y j) : Pair) i
  by_cases h : i = label j
  · subst i
    simp only [lp.single_apply_self]
  · simp only [lp.single_apply_ne _ _ _ h, mul_zero, sub_zero]

/-- The encoding preserves the squared norm, including for unnormalized rows. -/
lemma norm_embed_sq (label : I ↪ ℕ × ℕ × Unit) (x : I → ℂ) :
    ‖embed label x‖ ^ 2 = ∑ j, ‖x j‖ ^ 2 := by
  have h : inner ℂ (embed label x) (embed label x) = ∑ j, inner ℂ (x j) (x j) := by
    calc
      _ = inner ℂ (embed label x) (∑ j, lp.single 2 (label j) (x j) : Pair) := rfl
      _ = _ := by simp only [inner_sum, lp.inner_single_right, embed_apply]
  rw [@norm_sq_eq_re_inner ℂ, h]
  simp only [map_sum, ← norm_sq_eq_re_inner]

/-- Outgoing number projection keeps exactly the encoded labels in the selected occupation. -/
lemma hit_embed (label : I ↪ ℕ × ℕ × Unit) (x : I → ℂ) (n : ℕ) :
    hit n (embed label x) = embed label (fun j => if (label j).1 = n then x j else 0) := by
  classical
  apply lp.ext
  funext k
  change (if k.1 = n then embed label x k else 0) = _
  simp only [embed, lp.coeFn_sum, Finset.sum_apply]
  by_cases hk : k.1 = n
  · rw [ite_eq_left hk]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : k = label j
    · subst k
      rw [ite_eq_left hk]
    · rw [lp.single_apply_ne _ _ _ h, lp.single_apply_ne _ _ _ h]
  · rw [ite_eq_right hk]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases h : k = label j
    · subst k
      rw [ite_eq_right hk, lp.single_zero]
      rfl
    · exact lp.single_apply_ne _ _ _ h

/-- Conditional pair amplitude at each early record of the prepared state. -/
def rows (label : I ↪ ℕ × ℕ × Unit) (ψ : Wave I (EuclideanSpace ℂ R)) (r : R) : Pair :=
  embed label (fun j => ψ j r)

lemma row_mass (label : I ↪ ℕ × ℕ × Unit) (ψ : Wave I (EuclideanSpace ℂ R)) :
    ∑ r, ‖rows label ψ r‖ ^ 2 = ‖ψ‖ ^ 2 := by
  simp only [rows, norm_embed_sq, PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm]

variable [DecidableEq R]

omit [Fintype I] in
/-- The early projector is diagonal in a basis aligned with its ray. -/
private lemma ray_norm (ψ : Wave I (EuclideanSpace ℂ R)) (i : I) (r : R)
    (halign : ℂ ∙ ψ i = ℂ ∙ EuclideanSpace.single r (1 : ℂ)) (j : I) :
    ‖earlyProjector (ψ i) ψ j‖ = ‖ψ j r‖ := by
  change ‖(ℂ ∙ ψ i).starProjection (ψ j)‖ = _
  have hproj := congrArg (fun K : Submodule ℂ (EuclideanSpace ℂ R) => K.starProjection) halign
  rw [show (ℂ ∙ ψ i).starProjection = _ from hproj, Submodule.starProjection_unit_singleton]
  · simp [EuclideanSpace.inner_single_left, norm_smul, EuclideanSpace.single]
  · simp [EuclideanSpace.single]

/-- In the aligned early basis, the actual early yes probability is the finite
early-ray marginal of exactly the same state. -/
lemma marked_eq_ray (label : I ↪ ℕ × ℕ × Unit) (ψ : Wave I (EuclideanSpace ℂ R))
    (i : I) (r : R) (halign : ℂ ∙ ψ i = ℂ ∙ EuclideanSpace.single r (1 : ℂ)) :
    markedProbability (fun t => decide (t = r)) (rows label ψ) =
      ‖earlyProjector (ψ i) ψ‖ ^ 2 := by
  rw [markedProbability, PiLp.norm_sq_eq_of_L2]
  simp [rows, norm_embed_sq, ray_norm ψ i r halign, Finset.sum_filter]

/-- Joint early yes and outgoing number probability. Distinct late states may
carry the same outgoing occupation and differ only on the partner. -/
lemma markedJoint_eq_rayNumberJoint (label : I ↪ ℕ × ℕ × Unit)
    (ψ : Wave I (EuclideanSpace ℂ R)) (i : I) (r : R)
    (halign : ℂ ∙ ψ i = ℂ ∙ EuclideanSpace.single r (1 : ℂ)) :
    markedJointProbability (fun t => decide (t = r)) (rows label ψ) (label i).1 =
      rayNumberJoint ψ (fun j => (label j).1) i := by
  simp [markedJointProbability, jointProbability, rows, hit_embed, norm_embed_sq,
    rayNumberJoint, ray_norm ψ i r halign, Finset.sum_filter, apply_ite]

/-- The finite-support state in the full pair space obeys the AMPS probability
bound from its own Gram error. Both matched Born probabilities follow from the
encoding and the choice of early basis for this one binary test. -/
lemma amps_embedded_readout [DecidableEq I] (label : I ↪ ℕ × ℕ × Unit)
    (ψ : Wave I (EuclideanSpace ℂ R)) (i : I) (r : R) (hlive : ψ i ≠ 0)
    (halign : ℂ ∙ ψ i = ℂ ∙ EuclideanSpace.single r (1 : ℂ)) (hnorm : ‖ψ‖ = 1)
    {q : ℂ} (hq : q.normSq < 1)
    (hgap : 0 ≤ 1 - gramError i ψ - thermalNumberWeight q (label i).1) :
    markedProbability (fun t => decide (t = r)) (rows label ψ) *
        (1 - gramError i ψ - thermalNumberWeight q (label i).1) ^ 2 ≤
      1 - pairProbability (vacuum q hq) (rows label ψ) := by
  exact amps_of_relative_prediction ψ (fun j => (label j).1) i hlive hq _ _
    (by rw [row_mass, hnorm, one_pow]) (marked_eq_ray label ψ i r halign)
    (markedJoint_eq_rayNumberJoint label ψ i r halign) hgap

/-- Embedding of the finite diagonal occupation basis into the full number basis. -/
def diagonal (N : ℕ) : Fin (N + 1) ↪ ℕ × ℕ × Unit where
  toFun j := (j, j, ())
  inj' := fun _ _ h => Fin.ext (congrArg Prod.fst h)

/-- Unnormalized projection of the squeezed state onto the selected finite diagonal. -/
def cutoff (q : ℂ) (hq : q.normSq < 1) (N : ℕ) : Pair :=
  embed (diagonal N) (fun j => vacuum q hq (diagonal N j))

/-- Restrict the squeezed vacuum to the diagonal occupation pairs from zero to
`N` inclusive, then normalize it in the full oscillator space. -/
def truncatedVacuum (q : ℂ) (hq : q.normSq < 1) (N : ℕ) : Pair :=
  ((‖cutoff q hq N‖⁻¹ : ℝ) : ℂ) • cutoff q hq N

private lemma cutoff_mass {q : ℂ} (hq : q.normSq < 1) (N : ℕ) :
    ‖cutoff q hq N‖ ^ 2 = 1 - q.normSq ^ (N + 1) := by
  have geom (K : ℕ) : ∑ j ∈ Finset.range K, (1 - q.normSq) * q.normSq ^ j =
      1 - q.normSq ^ K := by
    induction K with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [cutoff, norm_embed_sq]
  change (∑ j : Fin (N + 1), ‖Packet.squeezed q (j, j, ())‖ ^ 2) = _
  simp only [Complex.sq_norm]
  simp [Packet.squeezed, Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt (sub_nonneg.mpr hq.le)]
  exact (Fin.sum_univ_eq_sum_range _ _).trans (geom _)

/-- Finite support alone gives no positive, cutoff-independent vacuum rejection.
The normalized truncated control fails the full squeezed-pair test with precisely
the omitted geometric tail probability, which tends to zero as the cutoff grows. -/
lemma truncatedVacuum_rejection {q : ℂ} (hq : q.normSq < 1) (N : ℕ) :
    ‖truncatedVacuum q hq N‖ = 1 ∧
      1 - pairProbability (vacuum q hq) (fun _ : Unit => truncatedVacuum q hq N) =
        q.normSq ^ (N + 1) := by
  let x := cutoff q hq N
  let v := vacuum q hq
  have hmass : ‖x‖ ^ 2 = 1 - q.normSq ^ (N + 1) := cutoff_mass hq N
  have hp : q.normSq ^ (N + 1) < 1 :=
    pow_lt_one₀ (Complex.normSq_nonneg q) hq (Nat.succ_ne_zero N)
  have hn : ‖x‖ ≠ 0 := by intro h; rw [h] at hmass; nlinarith
  have overlap (y : Pair) : inner ℂ y x =
      ∑ j, inner ℂ (y (diagonal N j)) (v (diagonal N j)) := by
    simp only [x, cutoff, embed, inner_sum, lp.inner_single_right, v]
  have hinner : inner ℂ v x = inner ℂ x x := by
    rw [overlap v, overlap x]
    simp only [x, cutoff, embed_apply, v]
  change ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1 ∧ _
  constructor
  · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hn]
  · have hover : ‖inner ℂ v (truncatedVacuum q hq N)‖ = ‖x‖ := by
      change ‖inner ℂ v (((‖x‖⁻¹ : ℝ) : ℂ) • x)‖ = _
      rw [inner_smul_right, hinner, norm_mul, ← inner_self_re_eq_norm, ← norm_sq_eq_re_inner,
        Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
      field_simp
    rw [pairProbability, EuclideanSpace.norm_sq_eq]
    simpa [pairReadout, ← show v = vacuum q hq from rfl, hover] using
      (show 1 - ‖x‖ ^ 2 = q.normSq ^ (N + 1) by linarith)

/-- Enlarging the support of these normalized controls takes their rejection
probability to zero. -/
lemma truncatedVacuum_rejection_tendsto {q : ℂ} (hq : q.normSq < 1) :
    Filter.Tendsto (fun N => 1 - pairProbability (vacuum q hq)
      (fun _ : Unit => truncatedVacuum q hq N)) Filter.atTop (nhds 0) := by
  simp only [(truncatedVacuum_rejection hq _).2, pow_succ]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (Complex.normSq_nonneg q) hq).mul_const
    q.normSq

end AMPS.Readout
