/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Linearized.Basic
import Mathlib.Tactic.Ring

/-!

# Trace-reversed metric perturbations

Minkowski trace `h = η^{ab} h_{ab}` and trace reversal `h̄_{ij} = h_{ij} - ½ η_{ij} h` for
linearized gravity.

## i. Overview

Around four-dimensional Minkowski spacetime `minkowski`, a weak-field metric perturbation `h` has
Minkowski trace `perturbationTrace h = η^{ab} h_{ab}` (equal to `metricTrace minkowski h`) and
trace-reversed perturbation `traceReversed h = h - ½ η perturbationTrace h`. Trace reversal is an
involution (`traceReversed_involutive`) that flips the sign of the trace (`traceReversed_trace`),
preserves symmetry (`traceReversed_symm`), lifts to `MetricPerturbation.traceReversed`, and
preserves `C²` regularity.

## ii. Key results

- `perturbationTrace`, `perturbationTrace_eq_metricTrace`, `traceReversed`, `traceReversed_trace`,
  `traceReversed_involutive`, `traceReversed_symm` : Minkowski trace, bridge to `metricTrace`,
  and trace-reversal involution.
- `MetricPerturbation.traceReversed`, `MetricPerturbation.IsC2At.traceReversed` : trace reversal
  on metric perturbations and `C²` regularity preservation.

## iii. Table of contents

- A. Trace reversal on symmetric tensors and perturbations

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 4 (Sec. 4.4). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 18.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 6
  (https://arxiv.org/pdf/gr-qc/9712019#page=144). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace Linearized

/-!

## A. Trace reversal on symmetric tensors and perturbations

Trace-reversing a metric perturbation (`h̄_{ij} = h_{ij} - ½ η_{ij} h`) diagonalizes the principal
part of the linearized Einstein equations into the flat d'Alembertian `□_η`.

-/

/-- Minkowski trace `h = η^{ij} h_{ij}` of a symmetric `(0, 2)` metric perturbation. -/
noncomputable def perturbationTrace (h : Tensor2 4) : ℝ := metricTrace minkowski h

/-- Minkowski trace `perturbationTrace` coincides with `metricTrace minkowski`. -/
lemma perturbationTrace_eq_metricTrace (h : Tensor2 4) :
    perturbationTrace h = metricTrace minkowski h := rfl

/-- Trace-reversed perturbation `h̄_{ij} = h_{ij} - (1 / 2) η_{ij} h`. -/
noncomputable def traceReversed (h : Tensor2 4) : Tensor2 4 :=
  Matrix.of fun i j => h i j - (1 / 2) * minkowskiMetric4 i j * perturbationTrace h

/-- Entrywise evaluation of `traceReversed`. -/
lemma traceReversed_apply (h : Tensor2 4) (i j : Fin 4) :
    traceReversed h i j = h i j - (1 / 2) * minkowskiMetric4 i j * perturbationTrace h := rfl

/-- Trace of the trace-reversed perturbation is `-perturbationTrace h`. -/
lemma traceReversed_trace (h : Tensor2 4) :
    perturbationTrace (traceReversed h) = -perturbationTrace h := by
  simp [perturbationTrace, traceReversed, Fin.sum_univ_four]
  ring

/-- Trace reversal is an involution: `(h̄)̄ = h`. -/
lemma traceReversed_involutive (h : Tensor2 4) : traceReversed (traceReversed h) = h := by
  ext i j
  rw [traceReversed_apply, traceReversed_trace, traceReversed_apply]
  ring

/-- Symmetry is preserved by trace reversal. -/
lemma traceReversed_symm {h : Tensor2 4} (hs : IsSymm h) : IsSymm (traceReversed h) := by
  ext i j
  simp only [Matrix.transpose_apply, traceReversed, Matrix.of_apply]
  rw [hs.apply i j, minkowskiMetric4_symm.apply i j]

/-- Trace reversal of a metric perturbation. -/
noncomputable def MetricPerturbation.traceReversed (P : MetricPerturbation) :
    MetricPerturbation where
  h x := Linearized.traceReversed (P.h x)
  symm x := traceReversed_symm (P.symm x)

/-- A `C²` metric perturbation has a `C²` Minkowski trace. -/
lemma contDiffAt_perturbationTrace {h : (Fin 4 → ℝ) → Tensor2 4} {x : Fin 4 → ℝ}
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) :
    ContDiffAt ℝ 2 (fun y => perturbationTrace (h y)) x := by
  simp only [perturbationTrace, metricTrace_minkowski, Fin.sum_univ_four]
  have hterm : ∀ k : Fin 4, ContDiffAt ℝ 2 (fun y => minkowskiMetric4 k k * h y k k) x :=
    fun k => (contDiffAt_const (c := minkowskiMetric4 k k)).mul (hh k k)
  exact (((hterm 0).add (hterm 1)).add (hterm 2)).add (hterm 3)

/-- A `C²` metric perturbation has a `C²` trace-reversed perturbation. -/
lemma contDiffAt_traceReversed {h : (Fin 4 → ℝ) → Tensor2 4} {x : Fin 4 → ℝ}
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun y => traceReversed (h y) i j) x := by
  simp only [traceReversed, Matrix.of_apply]
  exact (hh i j).sub ((contDiffAt_const (c := (1 / 2 : ℝ) * minkowskiMetric4 i j)).mul
    (contDiffAt_perturbationTrace hh))

/-- Trace reversal preserves pointwise `C²` regularity of a `MetricPerturbation`. -/
lemma MetricPerturbation.IsC2At.traceReversed {P : MetricPerturbation} {x : Fin 4 → ℝ}
    (hP : P.IsC2At x) : P.traceReversed.IsC2At x :=
  fun i j => contDiffAt_traceReversed hP i j

end Linearized

end GeneralRelativity
