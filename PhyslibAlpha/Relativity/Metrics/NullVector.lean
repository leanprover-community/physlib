/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.ConformalMetric
import Mathlib.Tactic.Ring

/-!

# Null vectors and conformal invariance

The quadratic null-cone condition `g_{ij} v^i v^j = 0` and its invariance under nonzero conformal
rescalings of the metric.

## i. Overview

Light rays propagate along null tangent vectors `v` satisfying `g_{ij} v^i v^j = 0`. Because a
nonzero conformal rescaling `g ↦ ω g` multiplies the quadratic form by `ω`, it preserves the null
cone identically, explaining why conformally flat metrics cannot bend light rays.

## ii. Key results

- `NullVector` : quadratic null-cone predicate `g_{ij} v^i v^j = 0`.
- `nullVector_conformal_iff` : invariance of the null cone under nonzero conformal rescalings.

## iii. Table of contents

- A. Null vectors and conformal invariance

## iv. References

* R. M. Wald, *General Relativity* (1984), App. D. [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 13.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 3
  (https://arxiv.org/pdf/gr-qc/9712019#page=84). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Null vectors and conformal invariance

Light cones are defined purely by the vanishing of the metric quadratic form, independent of any
overall positive or negative conformal factor.

-/

/-- Quadratic null-cone predicate `g_{ij} v^i v^j = 0`. -/
def NullVector {n : ℕ} (g : Tensor2 n) (v : Fin n → ℝ) : Prop :=
  (∑ i : Fin n, ∑ j : Fin n, g i j * v i * v j) = 0

/-- Any nonzero conformal rescaling leaves null cones invariant (`vᵀ (ω g) v = 0 ↔ vᵀ g v = 0`). -/
lemma nullVector_conformal_iff {n : ℕ} (ω : ℝ) (hω : ω ≠ 0) (g : Tensor2 n) (v : Fin n → ℝ) :
    NullVector (conformalRescaleMetric g ω) v ↔ NullVector g v := by
  have hsum : (∑ i : Fin n, ∑ j : Fin n, conformalRescaleMetric g ω i j * v i * v j)
      = ω * ∑ i : Fin n, ∑ j : Fin n, g i j * v i * v j := by
    simp only [conformalRescaleMetric, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [NullVector, hsum, mul_eq_zero, hω, false_or]

end GeneralRelativity
