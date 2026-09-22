/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.Compatibility
public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.Jordan

/-!

# Jordan compatibility of commuting self-adjoint elements

## i. Overview

The sanity check for `Compatibility.lean`'s Jordan-intrinsic notion: for `a`, `b` self-adjoint
elements of a C⋆-algebra `A` that already commute in the ordinary associative sense (`ab = ba`),
their multiplication operators for the *Jordan* product also commute — `a` and `b` are
`IsJordanCompatible`. This is a genuine algebraic computation (not a restatement), using
associativity of `A` and the hypothesis `ab = ba` directly, no linearized Jordan identity needed.

Proof idea: writing `L_a x = ½(ax+xa)`, expand both `a ∘ (b ∘ x)` and `b ∘ (a ∘ x)` into the four
terms `abx`, `axb`, `bxa`, `xba` (respectively `bax`, `bxa`, `axb`, `xab`), and check the two
expansions agree termwise using `ab = ba` (which also gives `xba = xab`, `bax = abx`) — a pure
associative-ring computation.

## ii. Key definitions and results

- `JB.isJordanCompatible_of_commute`

## iii. Table of contents

- A. The bridge theorem

-/

@[expose] public section

namespace JB

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped selfAdjoint

/-! ## A. The bridge theorem -/

omit [PartialOrder A] [StarOrderedRing A] in
/-- **Bridge sanity for compatibility.** If `a` and `b` commute in the ordinary associative sense,
they are Jordan-compatible: their Jordan multiplication operators commute. -/
theorem isJordanCompatible_of_commute {a b : selfAdjoint A}
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
