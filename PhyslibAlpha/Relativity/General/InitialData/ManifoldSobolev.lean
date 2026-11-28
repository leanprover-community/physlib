/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Normed.Group.Basic

/-!
# The H^s interface on a compact 3-manifold

## i. Overview

This module states, without constructing it, the analytic package that an
elliptic constraint solver consumes: a space of functions on a compact
three-manifold, a norm, completeness, a point-evaluation bound and a
multiplication estimate.  Every field is a hypothesis; no Sobolev space is
constructed and no elliptic estimate is proved.

It is layer L1 of the paper on the constraint equations.

## ii. Key results

- `ManifoldSobolev` : the interface, parameterised by the regularity `s`.

## iii. Table of contents

- A. The interface

## iv. References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., 2003.
* R. Bartnik, J. Isenberg, *The constraint equations*, 2004,
  arXiv:gr-qc/0405092.
-/

@[expose] public section

namespace GeneralRelativity

/-! ## A. The interface -/

/-- Sobolev `H^s` data on a compact three-manifold, for `s` large enough that
the space embeds into bounded functions and is closed under multiplication.
The structure records the analytic facts the constraint solver needs: a norm,
completeness, a point-evaluation bound and a product bound. -/
structure ManifoldSobolev (s : ℝ) where
  /-- The manifold points, the domain of the functions. -/
  Point : Type
  /-- The Sobolev space. -/
  H : Type
  /-- The zero element. -/
  zero : H
  /-- Addition. -/
  add : H → H → H
  /-- Negation. -/
  neg : H → H
  /-- Scalar multiplication. -/
  smul : ℝ → H → H
  /-- The norm. -/
  norm : H → ℝ
  /-- Point evaluation. -/
  eval : H → Point → ℝ
  /-- The norm is nonnegative. -/
  norm_nonneg : ∀ u, 0 ≤ norm u
  /-- The zero element has zero norm. -/
  norm_zero : norm zero = 0
  /-- The norm is homogeneous. -/
  norm_smul : ∀ (c : ℝ) u, norm (smul c u) = |c| * norm u
  /-- The triangle inequality. -/
  norm_add : ∀ u v, norm (add u v) ≤ norm u + norm v
  /-- Cauchy sequences converge. -/
  complete : ∀ seq : ℕ → H,
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      norm (add (seq m) (neg (seq n))) < ε) →
    ∃ u, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      norm (add (seq n) (neg u)) < ε
  /-- Point evaluation is bounded by the norm. -/
  eval_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H) (x : Point), |eval u x| ≤ C * norm u
  /-- Multiplication of two Sobolev functions. -/
  mul : H → H → H
  /-- The product is bounded by the product of the norms. -/
  mul_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ u v, norm (mul u v) ≤ C * norm u * norm v

end GeneralRelativity
