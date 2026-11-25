/-
Copyright (c) 2026 AMPS formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AMPS formalization contributors
-/
module

public import PhyslibAlpha.Relativity.BlackHole.AMPS.GroupedPrediction
public import PhyslibAlpha.Relativity.BlackHole.AMPS.Outcome
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# A physical readout for the Appendix A sum

A physical measurement of the grouped estimator.

## i. Overview

Diagonalize the Hermitian early estimator for one complete outgoing
occupation event. In the eigenbasis its error agrees with the squared
vector error of the same state embedded in the full two-mode space.
Thresholding and the infalling bounds can therefore use the grouped
Appendix A estimator with its actual statewise error.

## ii. Key results

* `repr_estimator`
* `diagonalRows_norm_sq`

## iii. Table of contents

- A. A physical measurement of the grouped estimator

## iv. References

* [ref: Almheiri2013]

## A. A physical measurement of the grouped estimator
-/

@[expose] public section

noncomputable section

namespace AMPS.CoarseReadout

open Prediction GroupedPrediction Readout VacuumTest Matrix
open scoped InnerProductSpace

variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

/-- The early Hermitian estimator in an orthonormal eigenbasis acts by its real
eigenvalues, including any degeneracy in the estimator itself. -/
lemma repr_estimator {A : Matrix R R ℂ} (hA : A.IsHermitian) (x : EuclideanSpace ℂ R) (r : R) :
    hA.eigenvectorBasis.repr (A.toEuclideanLin x) r =
      (hA.eigenvalues r : ℂ) * hA.eigenvectorBasis.repr x r := by
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have he : A.toEuclideanLin (hA.eigenvectorBasis r) =
      (hA.eigenvalues r : ℂ) • hA.eigenvectorBasis r := by
    ext i
    change (A *ᵥ ⇑(hA.eigenvectorBasis r)) i = (hA.eigenvalues r : ℂ) * hA.eigenvectorBasis r i
    simpa [RCLike.real_smul_eq_coe_smul (K := ℂ)] using congrFun (hA.mulVec_eigenvectorBasis r) i
  rw [OrthonormalBasis.repr_apply_apply, ← hsym, he, inner_smul_left,
    OrthonormalBasis.repr_apply_apply]
  simp

/-- Early eigenbasis coordinates of the same late rows. -/
def diagonalRows (B : OrthonormalBasis R ℂ (EuclideanSpace ℂ R))
    (ψ : Wave I (EuclideanSpace ℂ R)) : Wave I (EuclideanSpace ℂ R) :=
  WithLp.toLp 2 (fun j => B.repr (ψ j))

omit [DecidableEq R] in
/-- The simultaneous change of early basis preserves total Born mass. -/
lemma diagonalRows_norm_sq (B : OrthonormalBasis R ℂ (EuclideanSpace ℂ R))
    (ψ : Wave I (EuclideanSpace ℂ R)) : ‖diagonalRows B ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  simp [PiLp.norm_sq_eq_of_L2, diagonalRows]

/-- Computing the whole-event estimation error in the early eigenbasis and full
oscillator occupation basis gives the same norm as the Appendix A sum. -/
lemma measured_spectral_error (label : I ↪ ℕ × ℕ × Unit)
    (ψ : Wave I (EuclideanSpace ℂ R)) (k : ℕ) :
    let n := fun j => (label j).1
    let hA := occupationKernel_isHermitian n k ψ
    Operational.spectralError (rows label (diagonalRows hA.eigenvectorBasis ψ)) hA.eigenvalues k =
      error n k ψ := by
  dsimp only
  let n := fun j => (label j).1
  let hA := occupationKernel_isHermitian n k ψ
  let B := hA.eigenvectorBasis
  change Operational.spectralError (rows label (diagonalRows B ψ)) hA.eigenvalues k =
    error n k ψ
  unfold Operational.spectralError error
  simp_rw [rows, hit_embed, embed_sub_smul, norm_embed_sq]
  rw [Finset.sum_comm, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro j _
  let d := selected n k ψ j - estimated n k ψ j
  change (∑ r, ‖(if n j = k then B.repr (ψ j) r else 0) -
    (hA.eigenvalues r : ℂ) * B.repr (ψ j) r‖ ^ 2) = ‖d‖ ^ 2
  rw [← B.repr.norm_map d, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro r _
  have hd : B.repr d r = (if n j = k then B.repr (ψ j) r else 0) -
      (hA.eigenvalues r : ℂ) * B.repr (ψ j) r := by
    unfold d
    rw [map_sub]
    change B.repr ((if n j = k then (1 : ℂ) else 0) • ψ j) r -
      B.repr ((occupationKernel n k ψ).toEuclideanLin (ψ j)) r = _
    rw [show B.repr ((occupationKernel n k ψ).toEuclideanLin (ψ j)) r =
      (hA.eigenvalues r : ℂ) * B.repr (ψ j) r from repr_estimator hA (ψ j) r]
    split <;> simp_all
  rw [hd]

/-- The actual Appendix A grouped estimator gives an infalling outcome bound
when the prediction error is small compared with the whole occupation's weight
and its smooth prior. The basis change on the early register is derived from
the Hermitian estimator. The separate infalling mode identification is supplied. -/
lemma amps_grouped_outcomes (label : I ↪ ℕ × ℕ × Unit)
    (ψ : Wave I (EuclideanSpace ℂ R)) (k : ℕ) (hnorm : ‖ψ‖ = 1)
    {q : ℂ} (hq : q.normSq < 1) (U : Pair ≃ₗᵢ[ℂ] InfallingPair)
    (hground : U (vacuum q hq) = infallingGround) :
    let n := fun j => (label j).1
    let hA := occupationKernel_isHermitian n k ψ
    let x := rows label (diagonalRows hA.eigenvectorBasis ψ)
    let strength := outgoingProbability x k * (1 - thermalNumberWeight q k) - 4 * error n k ψ
    Outcome.InfallingOutcomeBounds ((max 0 strength) ^ 2) (fun r => U (x r)) := by
  dsimp only
  rw [← measured_spectral_error label ψ k]
  apply Outcome.amps_coarse_outcomes _ _ _ _ hq U hground
  rw [row_mass, diagonalRows_norm_sq, hnorm, one_pow]

end AMPS.CoarseReadout
