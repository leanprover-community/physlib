/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.Uncertainty
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.State.Vector

/-!

# Uncertainty in vector states

Variance and uncertainty defect in a vector state via fluctuation vectors `a ψ - ⟨a⟩ ψ`.

## i. Overview

In a vector state `ψ` the centered observable `a - ⟨a⟩` sends `ψ` to the fluctuation vector `a ψ -
⟨a⟩ ψ`. The variance is its squared norm, and the uncertainty defect of two observables is the
Cauchy–Schwarz defect of their fluctuation vectors.

For a family of observables, `Σ + iΩ` is the Gram matrix of the fluctuation vectors. Equality in
Robertson's relation `|det Ω| ≤ det Σ`, with `det Ω ≠ 0`, forces the kernel of this Gram matrix to
have at least half the dimension: the fluctuation vectors satisfy many linear relations.

## ii. Key results

- `UnitalPositiveLinearMap.apply_centered_mul_centered_ofVec` : the covariance matrix entry is the
  inner product of fluctuation vectors.
- `UnitalPositiveLinearMap.variance_ofVec` : the variance is the squared norm of the fluctuation
  vector.
- `UnitalPositiveLinearMap.centeredGramDefect_ofVec` : the uncertainty defect is `‖x‖² ‖y‖² - ‖⟪x,
  y⟫‖²`.
- `UnitalPositiveLinearMap.gram_fluctuation` : `Σ + iΩ` is the Gram matrix of the fluctuation
  vectors.
- `UnitalPositiveLinearMap.card_le_two_mul_finrank_ker_gram_fluctuation` : at equality in
  Robertson's relation for several observables, the fluctuation vectors satisfy at least half as
  many independent linear relations as there are observables.

## iii. Table of contents

- A. Fluctuation vectors in vector states
- B. Equality in Robertson's relation for several observables

## iv. References

* H. P. Robertson, *An indeterminacy relation for several observables and its classical
  interpretation*, Phys. Rev. 46 (1934) 794.

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped ComplexOrder InnerProductSpace
open ContinuousLinearMap

namespace UnitalPositiveLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ψ : H}

/-!

## A. Fluctuation vectors in vector states

-/

/-- The fluctuation vector `a ψ - ⟨a⟩ ψ` is the centered observable applied to `ψ`. -/
lemma centered_ofVec_apply (h : ‖ψ‖ = 1) (a : Observable (H →L[ℂ] H)) :
    (centered (ofVec h) a : H →L[ℂ] H) ψ = (a : H →L[ℂ] H) ψ - (ofVec h)⟨a⟩ • ψ := by
  simp [centered, LinearMap.centered]
  rfl

/-- The state of a product of centered observables is the inner product of the two fluctuation
vectors. -/
lemma apply_centered_mul_centered_ofVec (h : ‖ψ‖ = 1) (a b : Observable (H →L[ℂ] H)) :
    ofVec h ((centered (ofVec h) a : H →L[ℂ] H) * (centered (ofVec h) b : H →L[ℂ] H)) =
      ⟪(a : H →L[ℂ] H) ψ - (ofVec h)⟨a⟩ • ψ, (b : H →L[ℂ] H) ψ - (ofVec h)⟨b⟩ • ψ⟫_ℂ := by
  rw [← centered_ofVec_apply h a, ← centered_ofVec_apply h b]
  have hsym := isSelfAdjoint_iff_isSymmetric.mp (centered (ofVec h) a).property
  simpa [ofVec_apply] using (hsym ψ _).symm

/-- The variance in a vector state is the squared norm of the fluctuation vector. -/
lemma variance_ofVec (h : ‖ψ‖ = 1) (a : Observable (H →L[ℂ] H)) :
    variance (ofVec h) a = ‖(a : H →L[ℂ] H) ψ - (ofVec h)⟨a⟩ • ψ‖ ^ 2 := by
  rw [variance_eq_re_apply_centered_mul_self, apply_centered_mul_centered_ofVec]
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

/-- The centered Gram defect of a vector state is the Cauchy–Schwarz defect of the two
fluctuation vectors. -/
lemma centeredGramDefect_ofVec (h : ‖ψ‖ = 1) (a b : Observable (H →L[ℂ] H)) :
    centeredGramDefect (ofVec h) a b =
      ‖(a : H →L[ℂ] H) ψ - (ofVec h)⟨a⟩ • ψ‖ ^ 2 * ‖(b : H →L[ℂ] H) ψ - (ofVec h)⟨b⟩ • ψ‖ ^ 2 -
        ‖⟪(a : H →L[ℂ] H) ψ - (ofVec h)⟨a⟩ • ψ, (b : H →L[ℂ] H) ψ - (ofVec h)⟨b⟩ • ψ⟫_ℂ‖ ^ 2 := by
  rw [centeredGramDefect, variance_ofVec, variance_ofVec, apply_centered_mul_centered_ofVec,
    Complex.normSq_eq_norm_sq]

/-!

## B. Equality in Robertson's relation for several observables

-/

open Matrix

variable {ι : Type*}

/-- The fluctuation vector `a ψ - ⟨a⟩ ψ` of an observable in a vector state. -/
noncomputable def fluctuation (h : ‖ψ‖ = 1) (a : Observable (H →L[ℂ] H)) : H :=
  (a : H →L[ℂ] H) ψ - (ofVec h)⟨a⟩ • ψ

/-- In a vector state, `Σ + iΩ` is the Gram matrix of the fluctuation vectors. -/
lemma gram_fluctuation (h : ‖ψ‖ = 1) (a : ι → Observable (H →L[ℂ] H)) :
    gram ℂ (fun j => fluctuation h (a j)) =
      (covarianceMatrix (ofVec h) a).map ((↑) : ℝ → ℂ) +
        Complex.I • (bracketMatrix (ofVec h) a).map ((↑) : ℝ → ℂ) := by
  ext j k
  rw [gram_apply, fluctuation, fluctuation, ← apply_centered_mul_centered_ofVec,
    apply_centered_mul_centered]
  simp [covarianceMatrix, bracketMatrix]

/-- In a vector state, `Σ − iΩ` is the transpose of the Gram matrix of the fluctuation vectors. -/
lemma transpose_gram_fluctuation (h : ‖ψ‖ = 1) (a : ι → Observable (H →L[ℂ] H)) :
    (gram ℂ (fun j => fluctuation h (a j)))ᵀ =
      (covarianceMatrix (ofVec h) a).map ((↑) : ℝ → ℂ) -
        Complex.I • (bracketMatrix (ofVec h) a).map ((↑) : ℝ → ℂ) := by
  ext j k
  rw [transpose_apply, gram_apply, ← inner_conj_symm, fluctuation, fluctuation,
    ← apply_centered_mul_centered_ofVec, apply_centered_mul_centered]
  simp [covarianceMatrix, bracketMatrix, sub_eq_add_neg]

omit [CompleteSpace H] in
/-- The kernel of a Gram matrix is the space of linear relations among the vectors. -/
lemma gram_mulVec_eq_zero_iff [Fintype ι] (v : ι → H) (c : ι → ℂ) :
    gram ℂ v *ᵥ c = 0 ↔ ∑ j, c j • v j = 0 := by
  constructor
  · intro hc
    have h := star_dotProduct_gram_mulVec v c c
    rw [hc, dotProduct_zero] at h
    exact inner_self_eq_zero.mp h.symm
  · intro hs
    ext j
    have h : ⟪v j, ∑ k, c k • v k⟫_ℂ = (gram ℂ v *ᵥ c) j := by
      simp [mulVec, dotProduct, gram_apply, inner_sum, inner_smul_right, mul_comm]
    rw [← h, hs, inner_zero_right, Pi.zero_apply]

/-- **Equality in Robertson's relation for several observables.** In a vector state with
`|det Ω| = det Σ ≠ 0`, the fluctuation vectors of the family satisfy linear relations
`∑ j, c j • (a_j ψ - ⟨a_j⟩ ψ) = 0` forming a space of at least half the size of the family. -/
lemma card_le_two_mul_finrank_ker_gram_fluctuation [Fintype ι] [DecidableEq ι] (h : ‖ψ‖ = 1)
    (a : ι → Observable (H →L[ℂ] H)) (hΩ : (bracketMatrix (ofVec h) a).det ≠ 0)
    (heq : |(bracketMatrix (ofVec h) a).det| = (covarianceMatrix (ofVec h) a).det) :
    Fintype.card ι ≤
      2 * Module.finrank ℂ (LinearMap.ker (gram ℂ fun j => fluctuation h (a j)).mulVecLin) :=
  card_le_two_mul_finrank_ker (posSemidef_gram ℂ _) (gram_fluctuation h a)
    (transpose_gram_fluctuation h a) hΩ heq

end UnitalPositiveLinearMap

end ProbabilisticTheory
