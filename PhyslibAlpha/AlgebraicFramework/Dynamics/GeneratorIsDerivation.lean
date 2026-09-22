/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.Algebra.Derivation
public import PhyslibAlpha.AlgebraicFramework.Dynamics.Generator
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!

# The generator of a one-parameter automorphism group is a derivation

## i. Overview

**The bridge theorem.** Given a continuous (bounded) bilinear multiplication on a normed space
`E`, and a one-parameter family `α : ℝ → E → E` that (a) fixes `0` at `t = 0` in the sense
`α 0 = id`, and (b) preserves the product at every time (`α t (a * b) = α t a * α t b`), the
generator of `α` — purely analytically defined, `Dynamics/Generator.lean` — automatically satisfies
the Leibniz rule, hence is a derivation in the purely algebraic sense of `Algebra/Derivation.lean`:
$$ D(a \circ b) = D(a) \circ b + a \circ D(b). $$

This is deliberately proved at the most general level where the argument is legitimate: no order,
no Jordan identity, no star structure, not even associativity or commutativity of `*` — only that
`*` is `ℝ`-bilinear and *bounded* (`IsBoundedBilinearMap`), which is exactly what lets one
differentiate `t ↦ α t a * α t b` via the product rule for bilinear maps
(`IsBoundedBilinearMap.hasFDerivAt`) and read off the Leibniz rule from `α`'s multiplicativity. In
particular `IsCommJordan` never appears in this file: it is one instance of the hypothesis
`hmul`/`IsBoundedBilinearMap`, reached only by later composing this theorem with a JB-algebra's
submultiplicativity axiom (`‖a ∘ b‖ ≤ ‖a‖‖b‖`, `JB/Basic.lean`) — see the module docstring's closing
remark for exactly how that composition goes, deliberately *not* performed in this file.

## ii. Key definitions and results

- `IsGenerator.isDerivation_of_isAutomorphismFamily`

## iii. Table of contents

- A. The bridge theorem

-/

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Mul E]

/-! ## A. The bridge theorem -/

/-- **The bridge theorem.** If `α` is a one-parameter family with `α 0 = id`, preserving a bounded
bilinear multiplication at every time, then its generator `D` is a derivation for that
multiplication. Nothing here is specific to Jordan algebras, C⋆-algebras, or any order structure —
see the module docstring for how a JB-algebra's own axioms supply the `IsBoundedBilinearMap`
hypothesis as a corollary, without this theorem ever needing to know that. -/
theorem IsGenerator.isDerivation_of_isAutomorphismFamily
    (bilin : IsBoundedBilinearMap ℝ (fun p : E × E => p.1 * p.2))
    {α : ℝ → E → E} (hα0 : ∀ a, α 0 a = a) (hmul : ∀ t a b, α t (a * b) = α t a * α t b)
    {D : E →ₗ[ℝ] E} (hD : IsGenerator α D) : IsDerivation D := by
  intro a b
  have hpair : HasDerivAt (fun t => (α t a, α t b)) (D a, D b) 0 := (hD a).prodMk (hD b)
  have hcomp0 := (bilin.hasFDerivAt (α 0 a, α 0 b)).comp_hasDerivAt 0 hpair
  have hcomp : HasDerivAt (fun t => α t a * α t b)
      (bilin.deriv (α 0 a, α 0 b) (D a, D b)) 0 := hcomp0
  have hval : bilin.deriv (α 0 a, α 0 b) (D a, D b) = D a * b + a * D b := by
    rw [IsBoundedBilinearMap.deriv_apply, hα0, hα0]
    abel
  rw [hval] at hcomp
  have heq : (fun t => α t a * α t b) = fun t => α t (a * b) := by
    funext t; rw [hmul]
  rw [heq] at hcomp
  exact hcomp.unique (hD (a * b)) |>.symm
