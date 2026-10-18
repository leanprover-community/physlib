/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.Uncertainty
/-!

# Robertson's relation does not depend on the observer

## i. Overview

An observer may measure other combinations of the same observables: change units, move origins,
reverse an orientation, take other pairs, mix them. All of these are a real recombination
`b_k = ∑_i M_ki a_i + c_k` of the family. The covariance and bracket matrices transform as

  `Σ_b = M Σ_a Mᵀ`,  `Ω_b = M Ω_a Mᵀ`,

since the covariance and the bracket are bilinear and constants have no fluctuation and no
bracket. So `det Σ_b = (det M)² det Σ_a` and `det Ω_b = (det M)² det Ω_a`: for an invertible `M`,
Robertson's relation `|det Ω| ≤ det Σ` is strict for `b` exactly when it is strict for `a`.

## ii. Key results

- `UnitalPositiveLinearMap.recombine` : the recombination `∑_i M_ki a_i + c_k` of a family.
- `UnitalPositiveLinearMap.covarianceMatrix_recombine` : `Σ_b = M Σ_a Mᵀ`.
- `UnitalPositiveLinearMap.bracketMatrix_recombine` : `Ω_b = M Ω_a Mᵀ`.
- `UnitalPositiveLinearMap.robertson_det_strict_recombine_iff` : for an invertible `M`, the
  relation is strict for `b` iff it is strict for `a`.

## iii. Table of contents

- A. Recombinations of a family
- B. The strict relation does not depend on the observer

## iv. References

* H. P. Robertson, *An indeterminacy relation for several observables and its classical
  interpretation*, Phys. Rev. 46 (1934) 794.

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped ComplexOrder selfAdjoint
open Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι κ : Type*} [Fintype ι]

namespace UnitalPositiveLinearMap

/-!

## A. Recombinations of a family

-/

/-- The recombination `b_k = ∑_i M_ki a_i + c_k` of a family of observables. -/
noncomputable def recombine (M : Matrix κ ι ℝ) (c : κ → ℝ) (a : ι → Observable A) :
    κ → Observable A :=
  fun k => ∑ i, M k i • a i + c k • 1

/-- **`Σ_b = M Σ_a Mᵀ`.** -/
lemma covarianceMatrix_recombine (ω : 𝓢[ℂ, A]) (M : Matrix κ ι ℝ) (c : κ → ℝ)
    (a : ι → Observable A) :
    covarianceMatrix ω (recombine M c a) = M * covarianceMatrix ω a * Mᵀ := by
  ext k l
  simp only [covarianceMatrix, recombine, of_apply, covariance_add_smul_one_left,
    covariance_add_smul_one_right, mul_apply, transpose_apply, Finset.sum_mul]
  change LinearMap.covarianceForm (expectation ω).toLinearMap _ _ = _
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
    change M l j * (M k i * covariance ω (a i) (a j)) = _
    ring

/-- **`Ω_b = M Ω_a Mᵀ`.** -/
lemma bracketMatrix_recombine (ω : 𝓢[ℂ, A]) (M : Matrix κ ι ℝ) (c : κ → ℝ)
    (a : ι → Observable A) :
    bracketMatrix ω (recombine M c a) = M * bracketMatrix ω a * Mᵀ := by
  have hl (t : ℝ) (x y : Observable A) : ⁅t • x, y⁆ = t • ⁅x, y⁆ := by
    rw [← lie_skew, lie_smul, ← lie_skew y x, smul_neg, neg_neg]
  ext k l
  simp only [bracketMatrix, recombine, of_apply, add_lie, lie_add, hl, selfAdjoint.bracket_one_left,
    selfAdjoint.bracket_one_right, lie_smul, smul_zero, add_zero, sum_lie, lie_sum,
    Finset.sum_const_zero, mul_apply, transpose_apply, Finset.sum_mul]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-!

## B. The strict relation does not depend on the observer

-/

variable [DecidableEq ι]

/-- **The strict relation does not depend on the observer.** For an invertible real matrix `M`
and any shifts `c`, Robertson's relation is strict for the recombination `∑_i M_ki a_i + c_k`
exactly when it is strict for `a`. -/
lemma robertson_det_strict_recombine_iff (ω : 𝓢[ℂ, A]) {M : Matrix ι ι ℝ} (hM : M.det ≠ 0)
    (c : ι → ℝ) (a : ι → Observable A) :
    |(bracketMatrix ω (recombine M c a)).det| < (covarianceMatrix ω (recombine M c a)).det ↔
      |(bracketMatrix ω a).det| < (covarianceMatrix ω a).det := by
  have hpos : 0 < M.det ^ 2 := by positivity
  have e1 (x : ℝ) : |M.det| * x * |M.det| = M.det ^ 2 * x := by rw [← sq_abs]; ring
  have e2 (x : ℝ) : M.det * x * M.det = M.det ^ 2 * x := by ring
  rw [bracketMatrix_recombine, covarianceMatrix_recombine, det_mul, det_mul, det_mul, det_mul,
    det_transpose, abs_mul, abs_mul, e1, e2]
  exact mul_lt_mul_iff_of_pos_left hpos

end UnitalPositiveLinearMap

end ProbabilisticTheory
