/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.Compatibility
public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.CStarAlgebra.Basic

/-!

# Commuting observables are Jordan compatible

## i. Overview

If two self-adjoint elements of a C⋆-algebra commute, their Jordan multiplication operators commute.
Expanding `a ∘ (b ∘ x)` and `b ∘ (a ∘ x)` in the associative product, the terms agree using `a b = b
a`.

## ii. Key results

- `JB.isJordanCompatible_of_commute` : commuting observables are Jordan compatible.

## iii. Table of contents

- A. Commuting observables

-/

@[expose] public section

namespace ProbabilisticTheory

namespace JB

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped selfAdjoint

/-! ## A. Commuting observables -/

/-- Commuting self-adjoint elements are Jordan compatible. -/
lemma isJordanCompatible_of_commute {a b : selfAdjoint A}
    (hcomm : (a : A) * (b : A) = (b : A) * (a : A)) :
    JordanAlgebra.IsJordanCompatible a b := by
  apply LinearMap.ext
  intro x
  change selfAdjoint.jordanMul a (selfAdjoint.jordanMul b x) =
    selfAdjoint.jordanMul b (selfAdjoint.jordanMul a x)
  rw [selfAdjoint.jordanMul_jordanMul_right, selfAdjoint.jordanMul_jordanMul_right]
  congr 1
  apply Subtype.ext
  simp only [selfAdjoint.coe_anticommutator]
  have e1 : (a:A) * ((b:A)*(x:A)) = (b:A) * ((a:A)*(x:A)) := by
    rw [← mul_assoc, hcomm, mul_assoc]
  have e2 : (a:A) * ((x:A)*(b:A)) = ((a:A)*(x:A)) * (b:A) := (mul_assoc _ _ _).symm
  have e3 : ((b:A)*(x:A)) * (a:A) = (b:A) * ((x:A)*(a:A)) := mul_assoc _ _ _
  have e4 : ((x:A)*(b:A)) * (a:A) = ((x:A)*(a:A)) * (b:A) := by
    rw [mul_assoc, ← hcomm, ← mul_assoc]
  rw [_root_.mul_add, _root_.add_mul, _root_.mul_add, _root_.add_mul, e1, e2, e3, e4]
  abel

end JB

end ProbabilisticTheory
