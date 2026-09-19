/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.Uncertainty
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.State.Vector

/-!

# Uncertainty in vector states

In a vector state `ω = ⟪ψ, · ψ⟫` the statistics of `CStarAlgebra.Uncertainty` are plain Hilbert
space geometry: the centered observable `a - ⟨a⟩` sends `ψ` to the fluctuation vector
`a ψ - ⟨a⟩ ψ`, `variance` is its squared norm, and `centeredGramDefect` is the Cauchy–Schwarz
defect of two fluctuation vectors.

## Main results

- `apply_centered_mul_centered_ofVec` : the state of a product of centered observables is the
  inner product of the two fluctuation vectors.
- `variance_ofVec` : the variance is the squared norm of the fluctuation vector.
- `centeredGramDefect_ofVec` : the centered Gram defect is `‖x‖ ^ 2 * ‖y‖ ^ 2 - ‖⟪x, y⟫‖ ^ 2`
  for the fluctuation vectors `x`, `y`.

-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace
open ContinuousLinearMap

namespace UnitalPositiveLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ψ : H}

/-- The fluctuation vector `a ψ - ⟨a⟩ ψ` is the centered observable applied to `ψ`. -/
lemma centered_ofVec_apply (h : ‖ψ‖ = 1) (a : Observable (H →L[ℂ] H)) :
    (centered (ofVec h) a : H →L[ℂ] H) ψ = (a : H →L[ℂ] H) ψ - (ofVec h)⟨a⟩ • ψ := by
  simp [centered, LinearMap.centered]

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
