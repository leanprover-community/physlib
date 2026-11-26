/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Tensors.Tensor2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Algebraic Riemann curvature tensor

Covariant Riemann curvature tensor with its algebraic symmetries and flat-space specialization.

## i. Overview

The Riemann tensor (`RiemannTensor n`) carries its covariant components together with three
structural laws: antisymmetry in the last pair, pair symmetry `R_{ijkl} = R_{klij}`, and the
first (algebraic) Bianchi identity. Antisymmetry in the *first* pair (`RiemannTensor.skew_first`)
is derived from the other two rather than assumed.

## ii. Key results

- `RiemannTensor` : covariant Riemann tensor carrying antisymmetry in the last pair, pair
  symmetry, and the first Bianchi identity.
- `RiemannTensor.skew_first` : antisymmetry in the first pair, proved from pair symmetry and
  antisymmetry in the last pair.
- `RiemannTensor.zero_of_repeated_first`, `RiemannTensor.zero_of_repeated_last`,
  `RiemannTensor.swap_mixed` : vanishing and mixed-swap identities.
- `RiemannTensor.frameKretschmannScalar` : quadratic Kretschmann invariant in an orthonormal frame.
- `RiemannTensor.flat`, `RiemannTensor.flat_comp` : flat curvature tensor.

## iii. Table of contents

- A. The Riemann curvature tensor
  - A.1. Algebraic symmetries and vanishing components
  - A.2. The flat curvature tensor

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 3 (Sec. 3.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 11 & Ch. 13.
  [ref: mtw_1973_gravitation]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity* (1983), Ch. 3.
  [ref: oneill_1983_semi_riemannian]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 3
  (https://arxiv.org/pdf/gr-qc/9712019#page=72). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. The Riemann curvature tensor

An algebraic `RiemannTensor n` carries last-pair antisymmetry, pair-exchange symmetry, and the
first Bianchi identity, inducing the full symmetry relations and Kretschmann scalar.

-/

/-- Covariant components of the Riemann tensor with its algebraic symmetries. `bianchi` is the
first (algebraic) Bianchi identity `R_{ijkl} + R_{iklj} + R_{iljk} = 0`. -/
structure RiemannTensor (n : ℕ) where
  /-- Component function `R_{ijkl}` on `Fin n`. -/
  comp : Fin n → Fin n → Fin n → Fin n → ℝ
  /-- Antisymmetry in the last pair of indices: `R_{ijkl} = -R_{ijlk}`. -/
  skew_last : ∀ i j k l, comp i j k l = -comp i j l k
  /-- Symmetry under exchange of the first and second index pairs: `R_{ijkl} = R_{klij}`. -/
  pair_symm : ∀ i j k l, comp i j k l = comp k l i j
  /-- First (algebraic) Bianchi identity: `R_{ijkl} + R_{iklj} + R_{iljk} = 0`. -/
  bianchi : ∀ i j k l, comp i j k l + comp i k l j + comp i l j k = 0

namespace RiemannTensor

/-!

### A.1. Algebraic symmetries and vanishing components

-/

variable {n : ℕ} (R : RiemannTensor n)

/-- Antisymmetry in the first pair follows from pair symmetry and antisymmetry in the second
pair, so it need not be assumed. -/
lemma skew_first (i j k l : Fin n) : R.comp i j k l = -R.comp j i k l := by
  have h1 : R.comp j i k l = R.comp k l j i := R.pair_symm j i k l
  have h2 : R.comp k l j i = -R.comp k l i j := R.skew_last k l j i
  have h3 : R.comp k l i j = R.comp i j k l := R.pair_symm k l i j
  rw [h1, h2, h3]
  ring

/-- A component with a repeated first pair index vanishes. -/
lemma zero_of_repeated_first (i k l : Fin n) : R.comp i i k l = 0 := by
  have h := R.skew_first i i k l
  linarith

/-- A component with a repeated last pair index vanishes. -/
lemma zero_of_repeated_last (i j k : Fin n) : R.comp i j k k = 0 := by
  have h := R.skew_last i j k k
  linarith

/-- Swapping one index in each antisymmetric pair preserves the component. -/
lemma swap_mixed (i j k l : Fin n) : R.comp i j k l = R.comp j i l k := by
  rw [R.skew_first i j k l, R.skew_last j i k l]
  ring

/-- Quadratic Kretschmann invariant `K = ∑_{a,b,c,d} R_{abcd}²` in an orthonormal frame. -/
noncomputable def frameKretschmannScalar (R : RiemannTensor 4) : ℝ :=
  ∑ i, ∑ j, ∑ l, ∑ m, R.comp i j l m * R.comp i j l m

/-!

### A.2. The flat curvature tensor

-/

/-- The flat curvature tensor: every component vanishes. -/
def flat (n : ℕ) : RiemannTensor n where
  comp := fun _ _ _ _ => 0
  skew_last := by intro i j k l; ring
  pair_symm := by intro i j k l; rfl
  bianchi := by intro i j k l; ring

/-- Every component of the flat curvature tensor is zero. -/
@[simp]
lemma flat_comp (i j k l : Fin n) : (flat n).comp i j k l = 0 := rfl

end RiemannTensor

end GeneralRelativity
