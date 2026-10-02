/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Algebra.Derivation
public import PhyslibAlpha.ProbabilisticTheory.Dynamics.Generator
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!

# Generators of automorphism groups are derivations

## i. Overview

If a one-parameter family `α` with `α 0 = id` preserves a bounded bilinear multiplication at every
time, its generator is a derivation of that multiplication. Differentiating `α t (a b) = α t a α t
b` at `0` with the product rule gives `D (a b) = D a b + a D b`. Only boundedness and bilinearity of
the product are used.

## ii. Key results

- `IsGenerator.isDerivation_of_isAutomorphismFamily` : the generator of a family of automorphisms is
  a derivation.

## iii. Table of contents

- A. The generator is a derivation

-/

@[expose] public section

namespace ProbabilisticTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Mul E]

/-! ## A. The generator is a derivation -/

/-- **The generator of a family of automorphisms is a derivation.** If `α 0 = id` and every `α t`
preserves a bounded bilinear multiplication, the generator of `α` is a derivation of it. -/
lemma IsGenerator.isDerivation_of_isAutomorphismFamily
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

end ProbabilisticTheory
