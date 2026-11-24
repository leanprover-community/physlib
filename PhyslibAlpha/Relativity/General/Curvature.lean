/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Curvature: Riemann, Ricci, and scalar curvature

Algebraic symmetries and contractions of the Riemann curvature tensor.

## i. Overview

The Riemann tensor (`RiemannTensor n`) carries its covariant components together with three
structural laws: antisymmetry in the last pair, pair symmetry `R_{ijkl} = R_{klij}`, and the
first (algebraic) Bianchi identity. Antisymmetry in the *first* pair (`RiemannTensor.skew_first`)
is derived from the other two rather than assumed.

Unlike diagonal-only contractions, the Ricci tensor `ricci M R` here performs the fully general
contraction `Ric_{ij} = ∑ k l, g^{kl} R_{kilj}` against an arbitrary metric `M : MetricTensor n`,
and `ricci_of_diag` shows that this simplifies to the single sum `∑ k, g^{kk} R_{kikj}` when
`M.ginv` is diagonal.

## ii. Key results

- `RiemannTensor` : covariant Riemann tensor carrying antisymmetry in the last pair, pair
  symmetry, and the first Bianchi identity.
- `RiemannTensor.skew_first` : antisymmetry in the first pair, proved from pair symmetry and
  antisymmetry in the last pair.
- `ricci`, `ricci_symm`, `ricci_of_diag` : general Ricci contraction, its symmetry, and its
  reduction on diagonal inverse metrics.
- `scalarCurv` : scalar curvature `S = ∑ i j, g^{ij} Ric_{ij}`.

## iii. Table of contents

- A. The Riemann curvature tensor
  - A.1. Algebraic symmetries and vanishing components
  - A.2. The flat curvature tensor
- B. The Ricci tensor and scalar curvature

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity* (1983). [ref:
  oneill_1983_semi_riemannian]

-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. The Riemann curvature tensor

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

/-!

## B. The Ricci tensor and scalar curvature

-/

/-- The general Ricci tensor `Ric_{ij} = ∑ k l, g^{kl} R_{kilj}` obtained by contracting the
first and third indices against the inverse metric. -/
noncomputable def ricci {n : ℕ} (M : MetricTensor n) (R : RiemannTensor n) : Tensor2 n :=
  fun i j => ∑ k, ∑ l, M.ginv k l * R.comp k i l j

/-- The Ricci tensor is symmetric, by symmetry of the inverse metric and pair symmetry of the
Riemann tensor. -/
lemma ricci_symm {n : ℕ} (M : MetricTensor n) (R : RiemannTensor n) : IsSymm (ricci M R) := by
  intro i j
  simp only [ricci]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [M.ginv_symm k l, R.pair_symm k i l j]

/-- For a metric with a diagonal inverse (`g^{kl} = 0` for `k ≠ l`), the Ricci contraction
reduces to the single sum `∑ k, g^{kk} R_{kikj}`. -/
lemma ricci_of_diag {n : ℕ} (M : MetricTensor n) (R : RiemannTensor n)
    (hdiag : ∀ k l, k ≠ l → M.ginv k l = 0) (i j : Fin n) :
    ricci M R i j = ∑ k, M.ginv k k * R.comp k i k j := by
  simp only [ricci]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · intro l _ hlk
    rw [hdiag k l hlk.symm, zero_mul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- The flat curvature tensor is Ricci flat. -/
@[simp]
lemma ricci_flat (n : ℕ) (M : MetricTensor n) : ricci M (RiemannTensor.flat n) = 0 := by
  ext i j
  simp [ricci]

/-- Scalar curvature `S = ∑ i j, g^{ij} Ric_{ij}`. -/
noncomputable def scalarCurv {n : ℕ} (M : MetricTensor n) (R : RiemannTensor n) : ℝ :=
  ∑ i, ∑ j, M.ginv i j * ricci M R i j

end GeneralRelativity
