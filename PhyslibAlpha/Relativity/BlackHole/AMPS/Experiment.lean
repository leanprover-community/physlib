/-
Copyright (c) 2026 AMPS formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AMPS formalization contributors
-/
module

public import PhyslibAlpha.Relativity.BlackHole.AMPS.Prediction
public import PhyslibAlpha.Relativity.BlackHole.AMPS.Smeared
public import PhyslibAlpha.Relativity.BlackHole.AMPS.VacuumTest

/-!
# The AMPS early-radiation and infalling-vacuum experiment

The same outgoing wavepacket.

## i. Overview

AMPS §2 compares the same outgoing packet in two descriptions. In its asymptotic
number basis the early observer can estimate a spectral projection (Appendix A).
In the infalling vacuum the smeared number operator of Eq. (2.2) has a nonzero
two-particle component. This file compares those amplitudes in one experiment.

`T` is the two-infalling-particle component of the proposed exterior evolution of
a late state. It is linear, contractive, and independent of the early basis label.
A candidate smooth state has zero amplitude in that sector for every early label.
For the *same* number operator applied to that state, the proposed mode matching
must give the calculated vacuum matrix element, conditional on each early label.
These two comparisons only request matrix elements needed by the test. They do
not require or construct a unitary map from exterior observables to the interior.

The error below is the Hilbert norm of the error in predicting a number-weighted
amplitude on the original state. It is distinct from the probability of guessing
a number incorrectly. The latter has a bounded-observable test in `VacuumTest`.

## ii. Key results

* `numberReadout_exact`
* `vacuum_prediction_residual`

## iii. Table of contents

- A. The same outgoing wavepacket

## iv. References

* [ref: Almheiri2013]

## A. The same outgoing wavepacket
-/

@[expose] public section

noncomputable section

namespace AMPS.Experiment

open Prediction
open scoped TensorProduct ComplexInnerProductSpace

variable {I R H : Type*} [Fintype I] [Fintype R]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Late amplitudes at a fixed early-radiation basis label. -/
def column (ψ : Wave I (EuclideanSpace ℂ R)) (r : R) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun i => ψ i r)

/-- Apply one early-only matrix; all late amplitudes undergo the same operation. -/
def readColumn (ψ : Wave I (EuclideanSpace ℂ R)) (P : Matrix R R ℂ) (r : R) :
    EuclideanSpace ℂ I := ∑ t, P r t • column ψ t

/-- A finite sum of the paper's early estimators weighted by the outgoing number.
The scale used in Appendix A is a linear estimator. Born probabilities require
a separately normalized measurement instrument. -/
def numberReadout (ψ : Wave I (EuclideanSpace ℂ R)) (n : I → ℕ) : Matrix R R ℂ :=
  ∑ i, (n i : ℂ) • earlyKernel (Fintype.card I : ℝ) (ψ i)

/-- The exact equal-weight orthogonal Schmidt-row idealization of Appendix A
makes the number estimator reproduce the correct number action, including degeneracies. -/
lemma numberReadout_exact [DecidableEq I] (ψ : Wave I (EuclideanSpace ℂ R)) (n : I → ℕ)
    (hgram : ∀ i j, (Fintype.card I : ℂ) * inner ℂ (ψ i) (ψ j) = if j = i then 1 else 0)
    (r : R) :
    readColumn ψ (numberReadout ψ n) r = column (numberAction (fun i => (n i : ℂ)) ψ) r := by
  ext j
  change (∑ t, (numberReadout ψ n) r t • column ψ t) j = (n j : ℂ) * ψ j r
  change WithLp.ofLp (∑ t, (numberReadout ψ n) r t • column ψ t) j =
    (n j : ℂ) * ψ j r
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  change (∑ t, (numberReadout ψ n) r t * ψ j t) = _
  have hrow (i : I) : (∑ t, earlyKernel (Fintype.card I : ℝ) (ψ i) r t * ψ j t) =
      (if j = i then ψ i r else 0) := by
    rw [← earlyBranch_coordinates, earlyBranch_eq_lateBranch i ψ (hgram i)]
    by_cases h : j = i <;> simp [h]
  simp only [numberReadout, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hrow]
  simp [mul_ite]

/-- In an infalling vacuum every independent early predictor incurs a residual of
at least the packet's vacuum standard deviation. This compares two amplitudes
of the same state. No physical early measurement or postselection is performed. -/
lemma vacuum_prediction_residual (ψ : Wave I (EuclideanSpace ℂ R)) (n : I → ℕ)
    (P : Matrix R R ℂ) (u : EuclideanSpace ℂ R) (f g : H)
    (T : EuclideanSpace ℂ I →L[ℂ] H ⊗[ℂ] H) (hcontract : ‖T‖ ≤ 1)
    (hground : ∀ r, T (column ψ r) = 0)
    (hsame : ∀ r, T (column (numberAction (fun i => (n i : ℂ)) ψ) r) =
      u r • (Smeared.numberOnVacuum f g).2) :
    ‖u‖ ^ 2 * (‖f‖ ^ 2 * ‖g‖ ^ 2 + ‖inner ℂ f g‖ ^ 2) ≤
      ∑ r, ‖column (numberAction (fun i => (n i : ℂ)) ψ) r - readColumn ψ P r‖ ^ 2 := by
  have hearly (r : R) : T (readColumn ψ P r) = 0 := by
    simp [readColumn, map_sum, hground]
  have hpoint (r : R) : ‖u r‖ * ‖Smeared.createOne f g‖ ≤
      ‖column (numberAction (fun i => (n i : ℂ)) ψ) r - readColumn ψ P r‖ := by
    let x := column (numberAction (fun i => (n i : ℂ)) ψ) r - readColumn ψ P r
    calc
      _ = ‖T x‖ := by
        simp [x, map_sub, hearly, hsame, Smeared.numberOnVacuum_components, norm_smul]
      _ ≤ ‖T‖ * ‖x‖ := T.le_opNorm _
      _ ≤ _ := by simpa [x] using mul_le_mul_of_nonneg_right hcontract (norm_nonneg x)
  calc
    _ = ‖u‖ ^ 2 * ‖Smeared.createOne f g‖ ^ 2 := by rw [Smeared.createOne_norm_sq]
    _ = ∑ r, (‖u r‖ * ‖Smeared.createOne f g‖) ^ 2 := by
      simp [mul_pow, ← Finset.sum_mul, EuclideanSpace.norm_sq_eq u]
    _ ≤ _ := Finset.sum_le_sum fun r _ =>
      pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hpoint r) 2

private lemma coord_sum {J K X : Type*} [Fintype J] [NormedAddCommGroup X]
    (z : J → PiLp 2 (fun _ : K => X)) (k : K) :
    (∑ j, z j) k = ∑ j, z j k := by
  change WithLp.ofLp (∑ j, z j) k = _
  rw [WithLp.ofLp_sum, Finset.sum_apply]

/-- The weighted early estimator and the sum of the Appendix-A branches describe
exactly the same amplitudes on every early coordinate, for arbitrary Schmidt rows. -/
private lemma readout_column (ψ : Wave I (EuclideanSpace ℂ R)) (n : I → ℕ) (r : R) :
    readColumn ψ (numberReadout ψ n) r = column (∑ i, (n i : ℂ) • earlyBranch i ψ) r := by
  ext j
  change (∑ t, (numberReadout ψ n) r t • column ψ t) j =
    (∑ i, (n i : ℂ) • earlyBranch i ψ) j r
  simp only [coord_sum, PiLp.smul_apply, smul_eq_mul, numberReadout, Matrix.sum_apply,
    Matrix.smul_apply, Finset.sum_mul, mul_assoc, earlyBranch_coordinates, Finset.mul_sum]
  change (∑ t, ∑ i, (n i : ℂ) * (earlyKernel (Fintype.card I : ℝ) (ψ i) r t * ψ j t)) = _
  rw [Finset.sum_comm]

private lemma column_difference_sq (v w : Wave I (EuclideanSpace ℂ R)) :
    ∑ r, ‖column v r - column w r‖ ^ 2 = ‖v - w‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, PiLp.sub_apply]
  change (∑ r, ∑ i, ‖v i r - w i r‖ ^ 2) = ∑ i, ∑ r, ‖v i r - w i r‖ ^ 2
  rw [Finset.sum_comm]

/-- Finite spectral version of the AMPS comparison with imperfect prediction. The left
side is the two-particle weight forced by the proposed vacuum and the common mode
matching. The right side is a samplewise upper bound from the Gram errors of the same
state's early estimators. Occupation weights retain the cost of predicting an unbounded
number observable from its individual spectral projections. -/
lemma vacuum_gram_tradeoff [DecidableEq I] (ψ : Wave I (EuclideanSpace ℂ R))
    (n : I → ℕ) (ε : I → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (hgram : ∀ i, gramError i ψ ≤ ε i ^ 2) (u : EuclideanSpace ℂ R) (f g : H)
    (T : EuclideanSpace ℂ I →L[ℂ] H ⊗[ℂ] H) (hcontract : ‖T‖ ≤ 1)
    (hground : ∀ r, T (column ψ r) = 0)
    (hsame : ∀ r, T (column (numberAction (fun i => (n i : ℂ)) ψ) r) =
      u r • (Smeared.numberOnVacuum f g).2) :
    ‖u‖ ^ 2 * (‖f‖ ^ 2 * ‖g‖ ^ 2 + ‖inner ℂ f g‖ ^ 2) ≤
      (∑ i, (n i : ℝ) * ε i * ‖lateBranch i ψ‖) ^ 2 := by
  have hlo := vacuum_prediction_residual ψ n (numberReadout ψ n) u f g T hcontract hground hsame
  simp_rw [readout_column] at hlo
  rw [column_difference_sq] at hlo
  have hhi := number_prediction_distance_le (fun i => (n i : ℂ)) ψ ε hε hgram
  exact hlo.trans (pow_le_pow_left₀ (norm_nonneg _) (by simpa using hhi) 2)

/-- AMPS §2, exact prediction limit: the same nontrivially mixed outgoing packet
cannot have a normalized infalling vacuum and an exact Appendix-A early number
readout under a common exterior propagation. The smearing vectors can live in L²
of a continuous frequency band. -/
lemma uniform_schmidt_incompatibility [DecidableEq I] (ψ : Wave I (EuclideanSpace ℂ R)) (n : I → ℕ)
    (hgram : ∀ i j, (Fintype.card I : ℂ) * inner ℂ (ψ i) (ψ j) = if j = i then 1 else 0)
    (u : EuclideanSpace ℂ R) (hu : ‖u‖ = 1) {f g : H}
    (hCCR : ‖f‖ ^ 2 - ‖g‖ ^ 2 = 1) (hg : g ≠ 0)
    (T : EuclideanSpace ℂ I →L[ℂ] H ⊗[ℂ] H) (hcontract : ‖T‖ ≤ 1)
    (hground : ∀ r, T (column ψ r) = 0)
    (hsame : ∀ r, T (column (numberAction (fun i => (n i : ℂ)) ψ) r) =
      u r • (Smeared.numberOnVacuum f g).2) : False := by
  have h := vacuum_prediction_residual ψ n (numberReadout ψ n) u f g T hcontract hground hsame
  simp only [hu, one_pow, one_mul, numberReadout_exact ψ n hgram, sub_self, norm_zero, zero_pow
    (by decide : 2 ≠ 0),
    Finset.sum_const_zero] at h
  have hf : 0 < ‖f‖ ^ 2 := by linarith [sq_nonneg ‖g‖]
  have hp := mul_pos hf (sq_pos_of_pos (norm_pos_iff.mpr hg))
  linarith [sq_nonneg ‖inner ℂ f g‖]

/-- In the common domain of the measurements, let `Q` be the selected outgoing number
branch and `K` the early operation predicting it. The following amplitudes would have
to agree if the same exterior number operator `N` propagated to the infalling patch.
`vac u` prepares the infalling vacuum of the relevant modes with arbitrary joint
early/spectator amplitudes `u`. `two` tests its two-particle sector. Both maps are
linear on the common domain; no bounded number operator on all Fock space is assumed.

The profiles can be restrictions to a tested frequency sector, and other
frequencies can be absorbed in the spectator index. Their restricted pieces
need only be nonzero. The full outgoing operator carries its normalization
before making such a restriction. -/
lemma predicted_number_excludes_sector_vacuum {D S : Type*} [AddCommGroup D] [Module ℂ D]
    (ψ : D) (n : ℕ) (N Q K : D →ₗ[ℂ] D) (P : Matrix R R ℂ)
    (vac : (R → S → ℂ) →ₗ[ℂ] D) (two : D →ₗ[ℂ] (R → S → (H ⊗[ℂ] H)))
    {f g : H} (hf : f ≠ 0) (hg : g ≠ 0)
    (hnumber : ∀ x, N (Q x) = (n : ℂ) • Q x)
    (hread : K ψ = Q ψ) (hlive : Q ψ ≠ 0)
    (hlocal : ∀ u, K (vac u) = vac (fun r s => ∑ t, P r t * u t s))
    (hground : ∀ u, two (vac u) = 0)
    (hsame : ∀ u r s, two (N (vac u)) r s = u r s • (Smeared.numberOnVacuum f g).2) :
    ¬ ∃ u, ψ = vac u := by
  rintro ⟨u, rfl⟩
  let w := fun r s => ∑ t, P r t * u t s
  have hbranch : Q (vac u) = vac w := hread.symm.trans (hlocal u)
  have hw : w ≠ 0 := by
    intro hz
    apply hlive
    rw [hbranch, hz, map_zero]
  have hex : ∃ r s, w r s ≠ 0 := by
    by_contra! h
    exact hw (funext fun r => funext (h r))
  obtain ⟨r, s, hrs⟩ := hex
  have heig := hnumber (vac u)
  rw [hbranch] at heig
  have hz : two (N (vac w)) = 0 := by rw [heig, map_smul, hground, smul_zero]
  have hcomponent := hsame w r s
  rw [hz, Smeared.numberOnVacuum_components] at hcomponent
  have hzero : Smeared.createOne f g = 0 :=
    (smul_eq_zero.mp (show w r s • Smeared.createOne f g = 0 from hcomponent.symm)).resolve_left hrs
  have hnorm := Smeared.createOne_norm_sq f g
  rw [hzero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hnorm
  linarith [mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hf)) (sq_pos_of_pos (norm_pos_iff.mpr hg)),
    sq_nonneg ‖inner ℂ f g‖]

/-- The exact same-packet AMPS contradiction for a canonically normalized outgoing
mode with nonzero mixing, finite early readout, and arbitrary spectators. -/
theorem amps_same_packet {D S : Type*} [AddCommGroup D] [Module ℂ D]
    (ψ : D) (n : ℕ) (N Q K : D →ₗ[ℂ] D) (P : Matrix R R ℂ)
    (vac : (R → S → ℂ) →ₗ[ℂ] D) (two : D →ₗ[ℂ] (R → S → (H ⊗[ℂ] H)))
    {f g : H} (hnormal : ‖f‖ ^ 2 - ‖g‖ ^ 2 = 1) (hMix : g ≠ 0)
    (hnumber : ∀ x, N (Q x) = (n : ℂ) • Q x)
    (hread : K ψ = Q ψ) (hlive : Q ψ ≠ 0)
    (hlocal : ∀ u, K (vac u) = vac (fun r s => ∑ t, P r t * u t s))
    (hground : ∀ u, two (vac u) = 0)
    (hsame : ∀ u r s, two (N (vac u)) r s = u r s • (Smeared.numberOnVacuum f g).2) :
    ¬ ∃ u, ψ = vac u := by
  have hf : f ≠ 0 := by
    intro hz
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hnormal
    linarith [sq_nonneg ‖g‖]
  exact predicted_number_excludes_sector_vacuum ψ n N Q K P vac two hf hMix
    hnumber hread hlive hlocal hground hsame

/-- A two-particle frequency projection of the same outgoing number action
can already rule out the vacuum of the selected sector. The one-particle
projection is the orthogonal projection onto the sector. An additional
contribution from untested modes is allowed if the two-particle projection
kills it. The projected profiles need not themselves form a canonical mode. -/
lemma amps_projected_sector {D S : Type*} [AddCommGroup D] [Module ℂ D]
    (ψ : D) (n : ℕ) (N Q K : D →ₗ[ℂ] D) (P : Matrix R R ℂ)
    {sector : Submodule ℂ H} [sector.HasOrthogonalProjection]
    (vac : (R → S → ℂ) →ₗ[ℂ] D) (two : D →ₗ[ℂ] (R → S → (H ⊗[ℂ] H)))
    {f g : H} (hf : sector.orthogonalProjectionOnto f ≠ 0)
    (hg : sector.orthogonalProjectionOnto g ≠ 0)
    (hnumber : ∀ x, N (Q x) = (n : ℂ) • Q x)
    (hread : K ψ = Q ψ) (hlive : Q ψ ≠ 0)
    (hlocal : ∀ u, K (vac u) = vac (fun r s => ∑ t, P r t * u t s))
    (hground : ∀ u r s, TensorProduct.map sector.orthogonalProjectionOnto.toLinearMap
      sector.orthogonalProjectionOnto.toLinearMap (two (vac u) r s) = 0)
    (htransport : ∀ u r s, ∃ other : H ⊗[ℂ] H,
      two (N (vac u)) r s = u r s • Smeared.createOne f g + other ∧
      TensorProduct.map sector.orthogonalProjectionOnto.toLinearMap
        sector.orthogonalProjectionOnto.toLinearMap other = 0) :
    ¬ ∃ u, ψ = vac u := by
  let proj := TensorProduct.map sector.orthogonalProjectionOnto.toLinearMap
    sector.orthogonalProjectionOnto.toLinearMap
  let projected : D →ₗ[ℂ] (R → S → (sector ⊗[ℂ] sector)) :=
    { toFun := fun x r s => proj (two x r s)
      map_add' := fun x y => by ext r s; simp
      map_smul' := fun a x => by ext r s; simp }
  apply predicted_number_excludes_sector_vacuum ψ n N Q K P vac projected hf hg
    hnumber hread hlive hlocal
  · intro u
    funext r s
    exact hground u r s
  · intro u r s
    obtain ⟨other, hobs, hother⟩ := htransport u r s
    change proj (two (N (vac u)) r s) = _
    rw [hobs, map_add, map_smul, show proj other = 0 from hother, add_zero]
    simp only [proj, Smeared.map_createOne, Smeared.numberOnVacuum_components]
    rfl

section BinaryRecord

open VacuumTest

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Probability of both the early ray passing and the outgoing number equalling
`n i`. All late labels with that occupation contribute, including degeneracies. -/
def rayNumberJoint (ψ : Wave I E) (n : I → ℕ) (i : I) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => n j = n i), ‖earlyProjector (ψ i) ψ j‖ ^ 2

/-- The ray accepts the entire selected late component. Degenerate components can
only increase the joint probability for its occupation. -/
lemma selected_weight_le_rayNumberJoint (ψ : Wave I E) (n : I → ℕ) (i : I) :
    ‖ψ i‖ ^ 2 ≤ rayNumberJoint ψ n i := by
  classical
  unfold rayNumberJoint
  calc
    _ = ‖earlyProjector (ψ i) ψ i‖ ^ 2 := by rw [ray_accepts_selected_component]
    _ ≤ _ := Finset.single_le_sum
      (s := Finset.univ.filter (fun j => n j = n i))
      (fun j _ => sq_nonneg ‖earlyProjector (ψ i) ψ j‖) (by simp)

/-- Operational AMPS comparison for one Appendix A ray and a possibly degenerate
outgoing number. The asymptotic state and horizon state describe the same trial:
`hearly` and `hjoint` transport the two observable Born weights. This formulation
requires no decoder for a complete number basis. The vacuum test is the specified
two-mode squeezed-pair projector, inclusive over the finite early record.

Here `p` is the selected component's weight and `d` the actual false-positive
weight. At an exactly smooth horizon the outgoing number has prior weight `h`;
a ray for which `p > (p+d)h` witnesses a departure from that vacuum. The square
bound retains the probability cost of conditioning on a rare outcome. -/
lemma amps_binary_record [DecidableEq I] (ψ : Wave I E) (n : I → ℕ) (i : I)
    {q : ℂ} (hq : q.normSq < 1) (marked : R → Bool) (φ : R → Pair)
    (hnorm : ∑ r, ‖φ r‖ ^ 2 = 1)
    (hearly : markedProbability marked φ = ‖earlyProjector (ψ i) ψ‖ ^ 2)
    (hjoint : markedJointProbability marked φ (n i) = rayNumberJoint ψ n i) :
    let p := ‖ψ i‖ ^ 2
    let d := rayDisagreement (ψ i) i ψ
    let h := thermalNumberWeight q (n i)
    (max 0 (p - (p + d) * h)) ^ 2 ≤
      (p + d) * (1 - pairProbability (vacuum q hq) φ) := by
  dsimp only
  have ht := binary_prediction_pair_test hq marked φ (n i) hnorm
  rw [hearly, earlyYes_eq_lateYes_add_rayDisagreement, hjoint] at ht
  refine le_trans ?_ ht
  rw [← sq_abs (rayNumberJoint ψ n i - _)]
  apply pow_le_pow_left₀ (le_max_left _ _) _ 2
  apply max_le (abs_nonneg _) _
  exact (sub_le_sub_right (selected_weight_le_rayNumberJoint ψ n i) _).trans (le_abs_self _)

/-- Operational, finite-error form of the AMPS comparison. For a nonzero early yes,
Appendix A's samplewise relative squared error `g` guarantees conditional occupation
probability at least `1-g`. If this exceeds the smooth prior, the squared advantage
times the probability of early yes lower-bounds rejection of the pair vacuum.
Degenerate occupations are allowed. No division by a rare branch weight occurs. -/
lemma amps_of_relative_prediction [DecidableEq I] (ψ : Wave I E) (n : I → ℕ) (i : I)
    (hlive : ψ i ≠ 0) {q : ℂ} (hq : q.normSq < 1)
    (marked : R → Bool) (φ : R → Pair) (hnorm : ∑ r, ‖φ r‖ ^ 2 = 1)
    (hearly : markedProbability marked φ = ‖earlyProjector (ψ i) ψ‖ ^ 2)
    (hjoint : markedJointProbability marked φ (n i) = rayNumberJoint ψ n i)
    (hgap : 0 ≤ 1 - gramError i ψ - thermalNumberWeight q (n i)) :
    markedProbability marked φ * (1 - gramError i ψ - thermalNumberWeight q (n i)) ^ 2 ≤
      1 - pairProbability (vacuum q hq) φ := by
  let a := markedProbability marked φ
  let b := markedJointProbability marked φ (n i)
  let h := thermalNumberWeight q (n i)
  have haeq : a = ‖ψ i‖ ^ 2 + rayDisagreement (ψ i) i ψ :=
    hearly.trans (earlyYes_eq_lateYes_add_rayDisagreement i ψ)
  have ha : 0 < a := by
    rw [haeq, rayDisagreement_eq_norm_sq]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr hlive)) (sq_nonneg _)
  have hpost : (1 - gramError i ψ) * a ≤ b := by
    rw [haeq]
    exact (ray_posterior_lower_bound i ψ hlive).trans
      ((selected_weight_le_rayNumberJoint ψ n i).trans_eq hjoint.symm)
  have hcond : 1 - gramError i ψ - h ≤ b / a - h :=
    sub_le_sub_right ((le_div_iff₀ ha).mpr hpost) _
  have hsq := pow_le_pow_left₀ hgap hcond 2
  exact (mul_le_mul_of_nonneg_left hsq ha.le).trans
    (conditional_number_discrepancy hq marked φ (n i) hnorm ha)

end BinaryRecord

end AMPS.Experiment
