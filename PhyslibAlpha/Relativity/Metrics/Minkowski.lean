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
public import PhyslibAlpha.Relativity.Metrics.Basic

/-!

# The four-dimensional Minkowski metric

The flat metric `η = diag(-1, 1, 1, 1)` in inertial coordinates, constructed from
`Physlib.Relativity.MinkowskiMatrix` and packaged as a `MetricTensor 4` and constant field.

## i. Overview

Throughout `GeneralRelativity`, the Minkowski metric `eta4` uses the mostly-plus Lorentzian
signature `(-, +, +, +)` standard in general relativity (Wald / Misner–Thorne–Wheeler), whereas
`Physlib.Relativity.MinkowskiMatrix.minkowskiMatrix` (and `realLorentzTensor.coMetric 3`) uses the
particle-physics mostly-minus convention `(+, -, -, -)`.

We define `eta4` directly as the negation of `minkowskiMatrix (d := 3)` transported along
`finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4`, inherit its symmetry and self-inverse property from
`minkowskiMatrix.eq_transpose` and `minkowskiMatrix.sq`, and bridge it to
`realLorentzTensor.coMetric 3`.

## ii. Key results

- `eta4`, `eta4_symm`, `eta4_mul_self` : the 4D Minkowski metric `diag(-1, 1, 1, 1)` and its
  self-inverse property derived from `minkowskiMatrix`.
- `eta4_eq_neg_coMetric_repr` : component bridge to `realLorentzTensor.coMetric 3`.
- `minkowski` : four-dimensional Minkowski spacetime metric as a `MetricTensor 4`.
- `minkowski_ginv_offdiag` : the inverse Minkowski metric is diagonal.
- `minkowskiG` : the Minkowski metric as a constant field on `Fin 4 → ℝ`.

## iii. Table of contents

- A. The Minkowski matrix `η`
- B. The Minkowski spacetime metric bundle

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity* (1983).
  [ref: oneill_1983_semi_riemannian]

-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. The Minkowski matrix `η`

-/

/-- The Minkowski metric of signature `(-, +, +, +)` in inertial coordinates, obtained by
reindexing and negating `Physlib.Relativity.MinkowskiMatrix.minkowskiMatrix`. -/
def eta4 : Tensor2 4 :=
  fun i j => -minkowskiMatrix (d := 3) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)

/-- Explicit component formula for `eta4` on `Fin 4`. -/
@[simp]
lemma eta4_apply (i j : Fin 4) :
    eta4 i j = if i = j then (if i = 0 then -1 else 1) else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [eta4, finSumFinEquiv, Fin.addCases]

/-- The explicit matrix form `diag(-1, 1, 1, 1)` of `eta4`. -/
lemma eta4_eq_matrix :
    eta4 = !![(-1 : ℝ), 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Componentwise bridge between `eta4` and the real Lorentz tensor metric
`realLorentzTensor.coMetric 3`. -/
lemma eta4_eq_neg_coMetric_repr
    (b : TensorSpecies.Tensor.ComponentIdx (S := realLorentzTensor 3)
      ![realLorentzTensor.Color.down, realLorentzTensor.Color.down]) :
    eta4 (finSumFinEquiv (b 0)) (finSumFinEquiv (b 1)) =
      -((TensorSpecies.Tensor.basis (S := realLorentzTensor 3) _).repr
        (realLorentzTensor.coMetric 3) b) := by
  simp only [eta4, Equiv.symm_apply_apply]
  rw [realLorentzTensor.coMetric_repr_apply_eq_minkowskiMatrix]

/-- The Minkowski metric is symmetric, inherited from `minkowskiMatrix.eq_transpose`. -/
lemma eta4_symm : IsSymm eta4 := by
  intro i j
  simp only [eta4]
  have ht := congrFun (congrFun (@minkowskiMatrix.eq_transpose 3)
    (finSumFinEquiv.symm j)) (finSumFinEquiv.symm i)
  simpa [Matrix.transpose_apply] using congrArg Neg.neg ht

/-- The Minkowski metric is its own inverse: `η * η = 1`, inherited from
`minkowskiMatrix.sq`. -/
lemma eta4_mul_self : eta4 * eta4 = (1 : Tensor2 4) := by
  ext i j
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin 4, eta4 i k * eta4 k j =
      minkowskiMatrix (d := 3) (finSumFinEquiv.symm i) (finSumFinEquiv.symm k) *
        minkowskiMatrix (d := 3) (finSumFinEquiv.symm k) (finSumFinEquiv.symm j) := by
    intro k
    simp only [eta4, neg_mul_neg]
  simp_rw [hterm]
  rw [Equiv.sum_comp finSumFinEquiv.symm (fun μ =>
    minkowskiMatrix (d := 3) (finSumFinEquiv.symm i) μ *
      minkowskiMatrix (d := 3) μ (finSumFinEquiv.symm j))]
  have hsq := congrFun (congrFun (@minkowskiMatrix.sq 3)
    (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  simpa [Matrix.mul_apply, Matrix.one_apply, finSumFinEquiv.symm.injective.eq_iff] using hsq

/-!

## B. The Minkowski spacetime metric bundle

-/

/-- Four-dimensional Minkowski spacetime in inertial coordinates, with signature
`(-, +, +, +)`. -/
def minkowski : MetricTensor 4 where
  g := eta4
  ginv := eta4
  symm := eta4_symm
  inv_left := eta4_mul_self
  inv_right := eta4_mul_self

/-- Off-diagonal entries of the inverse Minkowski metric vanish. -/
lemma minkowski_ginv_offdiag {k l : Fin 4} (h : k ≠ l) : minkowski.ginv k l = 0 := by
  simp [minkowski, eta4_apply, h]

/-- The Minkowski metric as a constant field of components on `Fin 4 → ℝ`. -/
noncomputable def minkowskiG : (Fin 4 → ℝ) → Tensor2 4 := fun _ => eta4

end GeneralRelativity
