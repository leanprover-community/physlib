/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Logic.Equiv.Fin.Basic
public import Physlib.Relativity.MinkowskiMatrix
public import Physlib.Relativity.Tensors.RealTensor.Metrics.Basic
public import PhyslibAlpha.Relativity.Metrics.MetricTrace

/-!

# The four-dimensional Minkowski metric

The flat metric `η = diag(-1, 1, 1, 1)` in inertial coordinates, constructed from
`Physlib.Relativity.MinkowskiMatrix` and packaged as a `MetricTensor 4` and constant field.

## i. Overview

Throughout `GeneralRelativity`, the Minkowski metric `minkowskiMetric4` uses the mostly-plus
Lorentzian
signature `(-, +, +, +)` standard in general relativity (Wald / Misner–Thorne–Wheeler), whereas
`Physlib.Relativity.MinkowskiMatrix.minkowskiMatrix` (and `realLorentzTensor.coMetric 3`) uses the
particle-physics mostly-minus convention `(+, -, -, -)`.

We define `minkowskiMetric4` directly as the negation of `minkowskiMatrix (d := 3)` transported
along
`finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4`, inherit its symmetry and self-inverse property from
`minkowskiMatrix.eq_transpose` and `minkowskiMatrix.sq`, and bridge it to
`realLorentzTensor.coMetric 3`.

## ii. Key results

- `minkowskiMetric4`, `minkowskiMetric4_symm`, `minkowskiMetric4_mul_self`,
  `sum_minkowskiMetric4_mul` : the 4D Minkowski metric `diag(-1, 1, 1, 1)`, its self-inverse
  property derived from `minkowskiMatrix`, and its index contraction law.
- `minkowskiMetric4_eq_neg_coMetric_repr` : component bridge to `realLorentzTensor.coMetric 3`.
- `minkowski` : four-dimensional Minkowski spacetime metric as a `MetricTensor 4`.
- `minkowski_ginv_offdiag`, `metricTrace_minkowski` : diagonal property and Minkowski trace.
- `minkowskiMetricField` : the Minkowski metric as a constant field on `Fin 4 → ℝ`.

## iii. Table of contents

- A. The Minkowski matrix `η`
- B. The Minkowski spacetime metric bundle

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 2 (Sec. 2.3). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 2.
  [ref: mtw_1973_gravitation]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity* (1983), Ch. 6.
  [ref: oneill_1983_semi_riemannian]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 1
  (https://arxiv.org/pdf/gr-qc/9712019#page=10). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. The Minkowski matrix `η`

Fixing the `(-, +, +, +)` signature convention defines the constant reference metric
`minkowskiMetric4` and bundles it as `minkowski : MetricTensor 4`.

-/

/-- The Minkowski metric of signature `(-, +, +, +)` in inertial coordinates, obtained by
reindexing and negating `Physlib.Relativity.MinkowskiMatrix.minkowskiMatrix`. -/
def minkowskiMetric4 : Tensor2 4 :=
  fun i j => -minkowskiMatrix (d := 3) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)

/-- Explicit component formula for `minkowskiMetric4` on `Fin 4`. -/
@[simp]
lemma minkowskiMetric4_apply (i j : Fin 4) :
    minkowskiMetric4 i j = if i = j then (if i = 0 then -1 else 1) else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [minkowskiMetric4, finSumFinEquiv, Fin.addCases]

/-- The explicit matrix form `diag(-1, 1, 1, 1)` of `minkowskiMetric4`. -/
lemma minkowskiMetric4_eq_matrix :
    minkowskiMetric4 = !![(-1 : ℝ), 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Componentwise bridge between `minkowskiMetric4` and the real Lorentz tensor metric
`realLorentzTensor.coMetric 3`. -/
lemma minkowskiMetric4_eq_neg_coMetric_repr
    (b : TensorSpecies.Tensor.ComponentIdx (S := realLorentzTensor 3)
      ![realLorentzTensor.Color.down, realLorentzTensor.Color.down]) :
    minkowskiMetric4 (finSumFinEquiv (b 0)) (finSumFinEquiv (b 1)) =
      -((TensorSpecies.Tensor.basis (S := realLorentzTensor 3) _).repr
        (realLorentzTensor.coMetric 3) b) := by
  simp only [minkowskiMetric4, Equiv.symm_apply_apply]
  rw [realLorentzTensor.coMetric_repr_apply_eq_minkowskiMatrix]

/-- The Minkowski metric is symmetric, inherited from `minkowskiMatrix.eq_transpose`. -/
lemma minkowskiMetric4_symm : IsSymm minkowskiMetric4 := by
  ext i j
  simp only [Matrix.transpose_apply, minkowskiMetric4]
  have ht := congrFun (congrFun (@minkowskiMatrix.eq_transpose 3)
    (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  simpa [Matrix.transpose_apply] using congrArg Neg.neg ht

/-- The Minkowski metric is its own inverse: `η * η = 1`, inherited from
`minkowskiMatrix.sq`. -/
lemma minkowskiMetric4_mul_self : minkowskiMetric4 * minkowskiMetric4 = (1 : Tensor2 4) := by
  ext i j
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin 4, minkowskiMetric4 i k * minkowskiMetric4 k j =
      minkowskiMatrix (d := 3) (finSumFinEquiv.symm i) (finSumFinEquiv.symm k) *
        minkowskiMatrix (d := 3) (finSumFinEquiv.symm k) (finSumFinEquiv.symm j) := by
    intro k
    simp only [minkowskiMetric4, neg_mul_neg]
  simp_rw [hterm]
  rw [Equiv.sum_comp finSumFinEquiv.symm (fun μ =>
    minkowskiMatrix (d := 3) (finSumFinEquiv.symm i) μ *
      minkowskiMatrix (d := 3) μ (finSumFinEquiv.symm j))]
  have hsq := congrFun (congrFun (@minkowskiMatrix.sq 3)
    (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  simpa [Matrix.mul_apply, Matrix.one_apply, finSumFinEquiv.symm.injective.eq_iff] using hsq

/-- Raising and lowering with the Minkowski metric cancels:
`∑ a, f a * (η_{aa} η_{ab}) = f b`. -/
lemma sum_minkowskiMetric4_mul (f : Fin 4 → ℝ) (b : Fin 4) :
    (∑ a : Fin 4, f a * (minkowskiMetric4 a a * minkowskiMetric4 a b)) = f b := by
  fin_cases b <;> simp

/-- Contracting a vector with the diagonal Minkowski metric selects the diagonal entry:
`∑ k, η_{ik} f_k = η_{ii} f_i`. -/
lemma sum_minkowskiMetric4_left (i : Fin 4) (f : Fin 4 → ℝ) :
    (∑ k : Fin 4, minkowskiMetric4 i k * f k) = minkowskiMetric4 i i * f i := by
  rw [Finset.sum_eq_single i]
  · intro k _ hki
    simp [minkowskiMetric4_apply, hki.symm]
  · simp

/-!

## B. The Minkowski spacetime metric bundle

Flat Minkowski spacetime packages the constant matrix `η` as a nondegenerate `MetricTensor 4`
and supplies the constant metric field on `ℝ⁴`.

-/

/-- Four-dimensional Minkowski spacetime in inertial coordinates, with signature
`(-, +, +, +)`. -/
def minkowski : MetricTensor 4 where
  g := minkowskiMetric4
  ginv := minkowskiMetric4
  symm := minkowskiMetric4_symm
  inv_left := minkowskiMetric4_mul_self
  inv_right := minkowskiMetric4_mul_self

/-- Off-diagonal entries of the inverse Minkowski metric vanish. -/
lemma minkowski_ginv_offdiag {k l : Fin 4} (h : k ≠ l) : minkowski.ginv k l = 0 := by
  simp [minkowski, minkowskiMetric4_apply, h]

/-- Metric trace against `minkowski` reduces to the diagonal sum `∑ a, η_{aa} T_{aa}`. -/
@[simp]
lemma metricTrace_minkowski (T : Tensor2 4) :
    metricTrace minkowski T = ∑ a : Fin 4, minkowskiMetric4 a a * T a a := by
  rw [metricTrace_diag minkowski T (fun _ _ h => minkowski_ginv_offdiag h)]
  rfl

/-- The constant Minkowski metric field on `ℝ⁴` in global inertial coordinates. -/
noncomputable def minkowskiMetricField : (Fin 4 → ℝ) → Tensor2 4 := fun _ => minkowskiMetric4

end GeneralRelativity
