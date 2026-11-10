/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.Meta.TODO.Basic
public import Physlib.SpaceAndTime.Space.Module
public import Physlib.SpaceAndTime.WaveVectorSpace.Basic
/-!

# Duality of `Space` and `WaveVectorSpace`

## i. Overview

Upon selecting an origin for the affine space `Space d`,
the spaces `Space d` and `WaveVectorSpace d` are dual as real vector spaces.
There is natural continuous bilinear map `WaveVectorSpace d × Space d → ℝ` which sends
the pair `(k, x)` to `∑ᵢ kⁱxᵢ`. For fixed `k` this gives rise to a functional `Space d →L[ℝ] ℝ`
mapping `x ↦ k ⬝ᵥ x`, and similarly for fixed `x`.

## ii. Key results

- `Space.dual x` : the functional on `WaveVectorSpace` corresponding to `x : Space d`,
  bundled as a continuous linear map.
- `WaveVectorSpace.dual k` : the functional on `Space` corresponding to `k : WaveVectorSpace d`,
  bundled as a continuous linear map.
- `WaveVectorSpace.pairingCLM` : the dual pairing between `WaveVectorSpace` and `Space`,
  bundled as a continuous bilinear map.

## iii. Table of contents

- A. Strong duals
- B. Bilinear pairing

## iv. References

-/

@[expose] public section

TODO "Show how the dual functionals interact with `VAdd (EuclideanSpace ℝ (Fin d)) (Space d)`."

variable {d : ℕ}

/-!
## A. Strong duals
-/

namespace Space

/-- The functional on `WaveVectorSpace d` dual to `x`, defined by `k ↦ k ⬝ᵥ x`. -/
def dual (x : Space d) : StrongDual ℝ (WaveVectorSpace d) where
  toFun k := k ⬝ᵥ x
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

lemma dual_apply (x : Space d) (k : WaveVectorSpace d) : x.dual k = k ⬝ᵥ x := rfl

end Space

namespace WaveVectorSpace

/-- The functional on `Space d` dual to `k`, defined by `x ↦ k ⬝ᵥ x`. -/
def dual (k : WaveVectorSpace d) : StrongDual ℝ (Space d) where
  toFun x := k ⬝ᵥ x
  map_add' _ _ := by simp
  map_smul' _ _ := by simp [dotProduct, mul_left_comm, Finset.mul_sum]

lemma dual_apply (k : WaveVectorSpace d) (x : Space d) : k.dual x = k ⬝ᵥ x := rfl

/-!
## B. Bilinear pairing
-/

/-- The bilinear form `WaveVectorSpace d × Space d → ℝ` given by `k ↦ x ↦ k ⬝ᵥ x`. -/
def pairingCLM : WaveVectorSpace d →L[ℝ] Space d →L[ℝ] ℝ where
  toFun k := k.dual
  map_add' _ _ := by ext; simp [dual_apply]
  map_smul' _ _ := by ext; simp [dual_apply, dotProduct, mul_assoc, Finset.mul_sum]
  cont := by
    refine continuous_clm_apply.mpr fun x ↦ ?_
    change Continuous x.dual
    fun_prop

lemma pairingCLM_apply_eq_dual (k : WaveVectorSpace d) : pairingCLM k = k.dual := rfl

lemma pairingCLM_flip_apply_eq_dual (x : Space d) : pairingCLM.flip x = x.dual := rfl

end WaveVectorSpace
