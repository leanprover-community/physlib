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

## ii. Key results

- `UnitalPositiveLinearMap.apply_centered_mul_centered_ofVec` : the covariance matrix entry is the
  inner product of fluctuation vectors.
- `UnitalPositiveLinearMap.variance_ofVec` : the variance is the squared norm of the fluctuation
  vector.
- `UnitalPositiveLinearMap.centeredGramDefect_ofVec` : the uncertainty defect is `‖x‖² ‖y‖² - ‖⟪x,
  y⟫‖²`.

## iii. Table of contents

- A. Fluctuation vectors in vector states

## iv. References

* None.

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

end UnitalPositiveLinearMap

end ProbabilisticTheory
