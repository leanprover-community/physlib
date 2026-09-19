/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Abel

/-!

# Derivations for an arbitrary bilinear multiplication

## i. Overview

A derivation is a purely *algebraic* notion: `D(a * b) = D(a) * b + a * D(b)`. No topology, no
time, no continuity, no exponential — it is meaningful for a bare `NonUnitalNonAssocRing`. This is
deliberately factored out of both the Jordan layer (`JordanOrderUnit/`) and any dynamical layer
(`Dynamics/`): "derivation" is an algebra-axis concept, and the fact that the *generator* of a
one-parameter automorphism group happens to be a derivation (`Dynamics/GeneratorIsDerivation.lean`)
is a separate, genuinely analytic bridge theorem, not a definition.

`E` here is left as general as possible: only `Add`, `Mul`, and enough linearity for `D` itself to
be additive/`ℝ`-linear (`E →ₗ[ℝ] E`) are assumed. `IsCommJordan`, `NonUnitalNonAssocCommRing`, and
every other structure this project puts on top of a bare multiplication are irrelevant to this
file — a Jordan derivation (`D(a ∘ b) = D(a) ∘ b + a ∘ D(b)`) and an associative one are literally
the same predicate, `IsDerivation`, instantiated at different `Mul E`.

## ii. Key definitions and results

- `IsDerivation`
- `IsDerivation.zero`, `.add`, `.neg` : derivations form an additive group (stated pointwise; the
  submodule structure is left for a future file if needed)

## iii. Table of contents

- A. The Leibniz rule
- B. Closure properties

-/

@[expose] public section

/-! ## A. The Leibniz rule -/

/-- `D` is a derivation for the multiplication on `E`: the Leibniz rule `D(a*b) = D(a)*b + a*D(b)`.
Purely algebraic — no topology, and no assumption that `D` arose as the generator of anything.

Stated under the bare minimum `[Add E] [Mul E] [Module ℝ E]` (rather than bundling a full
`NonUnitalNonAssocRing E`) so that this definition, and the bridge theorem
`Dynamics/GeneratorIsDerivation.lean` that concludes it, can be stated for `E` a normed space with
an independent `Mul E` — avoiding the instance diamond a redundant second `AddCommGroup E` would
otherwise create against `NormedAddCommGroup E`. The closure lemmas in part B, which genuinely need
distributivity, take the stronger hypothesis locally instead. -/
def IsDerivation {E : Type*} [Mul E] [AddCommGroup E] [Module ℝ E] (D : E →ₗ[ℝ] E) :
    Prop :=
  ∀ a b : E, D (a * b) = D a * b + a * D b

/-! ## B. Closure properties -/

variable {E : Type*} [NonUnitalNonAssocRing E] [Module ℝ E]

theorem IsDerivation.zero : IsDerivation (0 : E →ₗ[ℝ] E) := by
  intro a b; simp

theorem IsDerivation.add {D₁ D₂ : E →ₗ[ℝ] E} (h₁ : IsDerivation D₁) (h₂ : IsDerivation D₂) :
    IsDerivation (D₁ + D₂) := by
  intro a b
  simp only [LinearMap.add_apply, h₁ a b, h₂ a b, add_mul, mul_add]
  abel

theorem IsDerivation.neg {D : E →ₗ[ℝ] E} (h : IsDerivation D) : IsDerivation (-D) := by
  intro a b
  simp only [LinearMap.neg_apply, h a b, neg_mul, mul_neg, neg_add_rev]
  abel

theorem IsDerivation.smul [SMulCommClass ℝ E E] [IsScalarTower ℝ E E] (c : ℝ) {D : E →ₗ[ℝ] E}
    (h : IsDerivation D) : IsDerivation (c • D) := by
  intro a b
  simp only [LinearMap.smul_apply, h a b, smul_add, smul_mul_assoc, mul_smul_comm]
