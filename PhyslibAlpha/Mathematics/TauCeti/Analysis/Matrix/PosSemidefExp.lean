/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.Mathematics.TauCeti.LinearAlgebra.Matrix.PosSemidef
public import PhyslibAlpha.Mathematics.TauCeti.Topology.Instances.Matrix
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The entrywise exponential of a positive-semidefinite matrix

Entrywise exponentials of real positive-semidefinite matrices are positive semidefinite.

## i. Overview

For a real positive-semidefinite matrix `K`, the matrix with entries `exp (K i j)` is the sum of
the series `∑ₙ (1 / n!) (K i j) ^ n`. Every term is a nonnegative multiple of a Schur power of
`K`, which is positive semidefinite by `Matrix.PosSemidef.hadamard_pow`. Positive-semidefinite
matrices form a closed cone, so the sum is positive semidefinite.

As a consequence, for a real positive-semidefinite matrix `G` and `t ≥ 0` the matrix with
entries `exp (-t (G i i + G j j - 2 G i j))` is positive semidefinite. If `G` is the Gram matrix
of vectors `vᵢ`, then `G i i + G j j - 2 G i j` is the squared distance between `vᵢ` and `vⱼ`.

## ii. Key results

- `Matrix.PosSemidef.map_exp` : the entrywise exponential of a real positive-semidefinite matrix
  is positive semidefinite.
- `Matrix.PosSemidef.exp_neg_mul_sqDist` : the matrix `exp (-t (G i i + G j j - 2 G i j))` is
  positive semidefinite for `t ≥ 0`.

## iii. Table of contents

- A. The entrywise exponential
- B. Exponentials of squared distances

## iv. References

There are no references for this file.

-/

@[expose] public section

namespace Matrix.PosSemidef

variable {ι : Type*}

/-!

## A. The entrywise exponential

-/

/-- The entrywise exponential of a real positive-semidefinite matrix is positive semidefinite. -/
lemma map_exp {K : Matrix ι ι ℝ} (hK : K.PosSemidef) : (K.map Real.exp).PosSemidef := by
  have h : HasSum (fun n : ℕ => ((Nat.factorial n : ℝ)⁻¹) • (fun i j => K i j ^ n : Matrix ι ι ℝ))
      (K.map Real.exp) := by
    refine Matrix.hasSum_iff.mpr fun i j => ?_
    rw [Matrix.map_apply, Real.exp_eq_exp_ℝ]
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (K i j)
  exact PosSemidef.of_hasSum h fun n => (hK.hadamard_pow n).smul (by positivity)

/-!

## B. Exponentials of squared distances

-/

/-- For a real positive-semidefinite matrix `G` and `t ≥ 0`, the matrix with entries
`exp (-t (G i i + G j j - 2 G i j))` is positive semidefinite. -/
lemma exp_neg_mul_sqDist {G : Matrix ι ι ℝ} (hG : G.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    (Matrix.of fun i j => Real.exp (-t * (G i i + G j j - 2 * G i j))).PosSemidef := by
  have h₁ := Matrix.posSemidef_vecMulVec_self_star fun i => Real.exp (-t * G i i)
  have h₂ := (hG.smul (by positivity : (0 : ℝ) ≤ 2 * t)).map_exp
  convert h₁.hadamard h₂ using 1
  ext i j
  simp only [Matrix.of_apply, Matrix.hadamard_apply, Matrix.vecMulVec_apply, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul, star_trivial]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

end Matrix.PosSemidef
