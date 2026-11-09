/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.SpaceAndTime.Space.Module
public import Physlib.SpaceAndTime.WaveVectorSpace.Basic
/-!

# Dual pairing of `Space` and `WaveVectorSpace`

## i. Overview

## ii. Key results

## iii. Table of contents

## iv. References

-/

@[expose] public section

variable {d : ℕ}

/-- The functional on `WaveVectorSpace d` dual to `x`, defined by `k ↦ k ⬝ᵥ x`. -/
def Space.dual (x : Space d) : StrongDual ℝ (WaveVectorSpace d) where
  toFun k := k ⬝ᵥ x
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

lemma Space.dual_apply (x : Space d) (k : WaveVectorSpace d) : x.dual k = k ⬝ᵥ x := rfl

/-- The functional on `Space d` dual to `k`, defined by `x ↦ k ⬝ᵥ x`. -/
def WaveVectorSpace.dual (k : WaveVectorSpace d) : StrongDual ℝ (Space d) where
  toFun x := k ⬝ᵥ x
  map_add' _ _ := by simp
  map_smul' _ _ := by simp [dotProduct, mul_left_comm, Finset.mul_sum]

lemma WaveVectorSpace.dual_apply (k : WaveVectorSpace d) (x : Space d) : k.dual x = k ⬝ᵥ x := rfl
