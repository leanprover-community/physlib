/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Restrict
public import PhyslibAlpha.ProbabilisticTheory.State.Basic
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!

# Vector states

A unit vector `ψ` defines the vector state `x ↦ ⟪ψ, x ψ⟫` on the bounded operators.

## i. Overview

A unit vector `ψ` defines the vector state `x ↦ ⟪ψ, x ψ⟫` on the bounded operators.
Multiplying `ψ` by a phase does not change its vector state, so two unit vectors with different
vector states are not parallel: their overlap has norm `‖⟪ψ, φ⟫‖ < 1`.

## ii. Key results

- `PositiveLinearMap.ofVec` : the positive functional of a vector.
- `UnitalPositiveLinearMap.ofVec` : the vector state of a unit vector.
- `UnitalPositiveLinearMap.ofVec_smul` : vector states do not see a global phase.
- `UnitalPositiveLinearMap.norm_inner_lt_one_of_ofVec_ne` : unit vectors with different vector
  states have overlap of norm less than one.

## iii. Table of contents

- A. Vector states
- B. Phase invariance
- C. Example

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

open ComplexOrder ContinuousLinearMap
open scoped InnerProductSpace

/-!

## A. Vector states

-/

section ofVec

variable {H 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The vector functional associated with `ψ`. -/
@[simps apply]
def _root_.PositiveLinearMap.ofVec (ψ : H) : 𝓟[𝕜, H →L[𝕜] H] where
  toFun x := ⟪ψ, x • ψ⟫_𝕜
  map_add' x y := by simp [inner_add_right]
  map_smul' x y := by simp [inner_smul_right]
  monotone' x y hxy := by
    simpa [inner_sub_right] using (ContinuousLinearMap.le_def.mp hxy).inner_nonneg_right ψ

/-- The vector state associated with a unit vector. -/
def UnitalPositiveLinearMap.ofVec {ψ : H} (h : ‖ψ‖ = 1) : 𝓢[𝕜, H →L[𝕜] H] :=
  { PositiveLinearMap.ofVec ψ with map_one' := by simp [h] }

/-- Evaluation of a vector state is the corresponding quadratic form. -/
@[simp]
lemma UnitalPositiveLinearMap.ofVec_apply {ψ : H} (h : ‖ψ‖ = 1) (x : H →L[𝕜] H) :
    UnitalPositiveLinearMap.ofVec h x = ⟪ψ, x • ψ⟫_𝕜 := rfl

/-!

## B. Phase invariance

-/

/-- Vector states do not see a global phase: `ofVec (c • ψ) = ofVec ψ` for `‖c‖ = 1`. -/
lemma UnitalPositiveLinearMap.ofVec_smul {ψ : H} (h : ‖ψ‖ = 1) {c : 𝕜} (hc : ‖c‖ = 1)
    (h' : ‖c • ψ‖ = 1) :
    UnitalPositiveLinearMap.ofVec (𝕜 := 𝕜) h' = UnitalPositiveLinearMap.ofVec (𝕜 := 𝕜) h :=
  UnitalPositiveLinearMap.ext fun x => by
    simp only [ofVec_apply, ContinuousLinearMap.smul_def, map_smul, inner_smul_left,
      inner_smul_right]
    rw [← mul_assoc, RCLike.mul_conj, hc]
    simp

/-- Unit vectors with different vector states are not parallel: `‖⟪ψ, φ⟫‖ < 1`. -/
lemma UnitalPositiveLinearMap.norm_inner_lt_one_of_ofVec_ne {ψ φ : H} (hψ : ‖ψ‖ = 1)
    (hφ : ‖φ‖ = 1) (h : ofVec (𝕜 := 𝕜) hψ ≠ ofVec (𝕜 := 𝕜) hφ) : ‖⟪ψ, φ⟫_𝕜‖ < 1 := by
  refine ((norm_inner_le_norm ψ φ).trans_eq (by rw [hψ, hφ, one_mul])).lt_of_ne fun heq => h ?_
  -- equality in the Cauchy–Schwarz inequality: `φ` is a multiple of `ψ`
  obtain ⟨c, -, rfl⟩ := (norm_inner_eq_norm_iff (𝕜 := 𝕜) (norm_ne_zero_iff.1 (hψ ▸ one_ne_zero))
    (norm_ne_zero_iff.1 (hφ ▸ one_ne_zero))).1 (by rw [heq, hψ, hφ, one_mul])
  exact (ofVec_smul hψ (by simpa [norm_smul, hψ] using hφ) hφ).symm

end ofVec

/-!

## C. Example

-/

section Example

open UnitalPositiveLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (ψ : H) (h : ‖ψ‖ = 1) :
    (ofVec h).restrictSAC (1 : selfAdjoint (H →L[ℂ] H)) = (1 : ℝ) := by
  simp

end Example

end ProbabilisticTheory
