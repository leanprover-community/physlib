/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Basic.Real.Basic
/-!

# Wave Vector Space

## i. Overview

In this module we define the type `WaveVectorSpace d` which corresponds
to the `d`-dimensional real vector space of (angular) wave vectors in `Space d`.

## ii. Key results

## iii. Table of contents

- A. The `WaveVectorSpace` type
- B. Instances on `WaveVectorSpace`
  - B.1. Coercion to functions
  - B.2. Subsingleton for `d = 0`
  - B.3. Zero
  - B.4. Additive commutative group

## iv. References

-/

@[expose] public section

/-!
## A. The `WaveVectorSpace` type
-/

/-- The type `WaveVectorSpace d` is the real vector space which corresponds to `d`-dimensional
(angular) wave vectors in `Space d` with a given (but arbitrary) choice of inverse length unit.

The default value of `d` is `3`. Thus `WaveVectorSpace = WaveVectorSpace 3`-/
structure WaveVectorSpace (d : ℕ := 3) where
  /-- The underlying map `Fin d → ℝ` associated with a vector in `WaveVectorSpace`. -/
  val : Fin d → ℝ

namespace WaveVectorSpace

variable {d : ℕ} {k k₁ k₂ : WaveVectorSpace d}

lemma eq_of_val (h : k₁.val = k₂.val) : k₁ = k₂ := by
  cases k₁
  congr

@[simp]
lemma val_eq_iff : k₁.val = k₂.val ↔ k₁ = k₂ := ⟨eq_of_val, congrArg val⟩

/-!
## B. Instances on `WaveVectorSpace`
-/

/-!
### B.1. Coercion to functions
-/

instance : CoeFun (WaveVectorSpace d) (fun _ ↦ Fin d → ℝ) where
  coe k := k.val

@[ext]
lemma eq_of_apply (h : ∀ i, k₁ i = k₂ i) : k₁ = k₂ := by
  apply eq_of_val
  funext i
  exact h i

/-!
### B.2. Subsingleton for `d = 0`
-/

instance : Subsingleton (WaveVectorSpace 0) where
  allEq _ _ := eq_of_apply fun i ↦ Fin.elim0 i

/-!
### B.3. Zero
-/

instance : Zero (WaveVectorSpace d) where
  zero := ⟨0⟩

@[simp]
lemma zero_val : (0 : WaveVectorSpace d).val = 0 := rfl

/-!
### B.4. Additive commutative group
-/

variable (k k₁ k₂)

instance : Add (WaveVectorSpace d) where
  add k₁ k₂ := ⟨k₁.val + k₂.val⟩

@[simp]
lemma add_val : (k₁ + k₂).val = k₁.val + k₂.val := rfl

instance : Sub (WaveVectorSpace d) where
  sub k₁ k₂ := ⟨k₁.val - k₂.val⟩

@[simp]
lemma sub_val : (k₁ - k₂).val = k₁.val - k₂.val := rfl

instance : Neg (WaveVectorSpace d) where
  neg k := ⟨-k.val⟩

@[simp]
lemma neg_val : (-k).val = -k.val := rfl

instance : AddCommGroup (WaveVectorSpace d) where
  add_assoc _ _ _ := by ext; simp [add_assoc]
  zero_add _ := by ext; simp
  add_zero _ := by ext; simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel _ := by ext; simp
  add_comm _ _ := by ext; simp [add_comm]

end WaveVectorSpace
