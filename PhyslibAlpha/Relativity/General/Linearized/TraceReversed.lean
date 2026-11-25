/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
public import PhyslibAlpha.Relativity.Metrics.MetricTrace
import Mathlib.Tactic.Ring

/-!

# Trace-reversed metric perturbations and wave operator

Trace reversal `h̄_{ij} = h_{ij} - ½ η_{ij} h` and the Minkowski d'Alembertian `□_η` for
linearized gravity.

## i. Overview

Around four-dimensional Minkowski spacetime `minkowskiMetric4`, a weak-field metric perturbation
`h` has
Minkowski trace `hTrace h = η^{ab} h_{ab}` (equal to `metricTrace minkowski h`) and trace-reversed
perturbation `traceReversed h = h - ½ η hTrace h`. Trace reversal is an involution
(`traceReversed_involutive`) that flips the sign of the trace (`traceReversed_trace`) and preserves
symmetry. This module also defines the flat-space wave operator `boxEta` and records `C²`
regularity of `hTrace` and `traceReversed`.

## ii. Key results

- `hTrace`, `hTrace_eq_metricTrace`, `traceReversed`, `traceReversed_trace`,
  `traceReversed_involutive`, `traceReversed_symm` : Minkowski trace, bridge to `metricTrace`,
  and trace-reversal involution.
- `boxEta` : Minkowski d'Alembertian wave operator `□_η`.

## iii. Table of contents

- A. Trace reversal and wave operator

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

-/

@[expose] public section

namespace GeneralRelativity

namespace Linearized

open Pipeline

/-!

## A. Trace reversal and wave operator

Trace-reversing the metric perturbation (`h̄_{ij} = h_{ij} - ½ η_{ij} h`) diagonalizes the
principal part of the linearized Einstein equations into the flat d'Alembertian `□_η`.

-/

/-- Minkowski trace `h = η^{ij} h_{ij}` of a symmetric `(0,2)` metric perturbation. -/
noncomputable def hTrace (h : Tensor2 4) : ℝ := metricTrace minkowski h

/-- Minkowski trace `hTrace` coincides with `metricTrace minkowski`. -/
lemma hTrace_eq_metricTrace (h : Tensor2 4) :
    hTrace h = metricTrace minkowski h := rfl

/-- Trace-reversed perturbation `h̄_{ij} = h_{ij} - (1 / 2) η_{ij} h`. -/
noncomputable def traceReversed (h : Tensor2 4) : Tensor2 4 :=
  fun i j => h i j - (1 / 2) * minkowskiMetric4 i j * hTrace h

/-- Trace of the trace-reversed perturbation is `-hTrace h`. -/
lemma traceReversed_trace (h : Tensor2 4) : hTrace (traceReversed h) = -hTrace h := by
  simp [hTrace, traceReversed, Fin.sum_univ_four]
  ring

/-- Trace reversal is an involution: `(h̄)̄ = h`. -/
lemma traceReversed_involutive (h : Tensor2 4) : traceReversed (traceReversed h) = h := by
  ext i j
  simp only [traceReversed, traceReversed_trace]
  ring

/-- Symmetry is preserved by trace reversal. -/
lemma traceReversed_symm {h : Tensor2 4} (hs : IsSymm h) : IsSymm (traceReversed h) := by
  ext i j
  simp only [Matrix.transpose_apply, traceReversed]
  rw [hs.apply i j, minkowskiMetric4_symm.apply i j]

/-- Minkowski d'Alembertian (wave operator) `□f = η^{μν} ∂_μ ∂_ν f = -∂_t² f + ∇² f`. -/
noncomputable def boxEta (f : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ∑ μ : Fin 4, minkowskiMetric4 μ μ * coordDeriv μ (coordDeriv μ f) x

/-- A `C²` metric perturbation has a `C²` Minkowski trace. -/
lemma contDiffAt_hTrace {h : (Fin 4 → ℝ) → Tensor2 4} {x : Fin 4 → ℝ}
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) :
    ContDiffAt ℝ 2 (fun y => hTrace (h y)) x := by
  simp only [hTrace, metricTrace_minkowski, Fin.sum_univ_four]
  have h0 : ContDiffAt ℝ 2 (fun y => minkowskiMetric4 0 0 * h y 0 0) x :=
    (contDiffAt_const (c := minkowskiMetric4 0 0)).mul (hh 0 0)
  have h1 : ContDiffAt ℝ 2 (fun y => minkowskiMetric4 1 1 * h y 1 1) x :=
    (contDiffAt_const (c := minkowskiMetric4 1 1)).mul (hh 1 1)
  have h2 : ContDiffAt ℝ 2 (fun y => minkowskiMetric4 2 2 * h y 2 2) x :=
    (contDiffAt_const (c := minkowskiMetric4 2 2)).mul (hh 2 2)
  have h3 : ContDiffAt ℝ 2 (fun y => minkowskiMetric4 3 3 * h y 3 3) x :=
    (contDiffAt_const (c := minkowskiMetric4 3 3)).mul (hh 3 3)
  exact ((h0.add h1).add h2).add h3

/-- A `C²` metric perturbation has a `C²` trace-reversed perturbation. -/
lemma contDiffAt_traceReversed {h : (Fin 4 → ℝ) → Tensor2 4} {x : Fin 4 → ℝ}
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun y => traceReversed (h y) i j) x := by
  simp only [traceReversed]
  exact (hh i j).sub
    ((contDiffAt_const (c := (1 / 2 : ℝ) * minkowskiMetric4 i j)).mul (contDiffAt_hTrace hh))

end Linearized

end GeneralRelativity
