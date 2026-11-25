/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import PhyslibAlpha.Relativity.General.Modified.KaluzaKlein.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!

# Upper-unitriangular vielbein factorization of the Kaluza–Klein metric

Congruence factorization `G = U diag(g4, φ²) Uᵀ` with `det U = 1`.

## i. Overview

Expressing the 5D Kaluza–Klein metric `kkMetric` as the upper-unitriangular congruence
`kkTriangular A * kkBlockDiag g4 φ * (kkTriangular A)ᵀ` isolates the gauge potential into a
unit-determinant shearing transformation `det (kkTriangular A) = 1`.

## ii. Key results

- `kkTriangular`, `kkBlockDiag` : upper-unitriangular frame matrix and block-diagonal core.
- `det_kkTriangular` : `det (kkTriangular A) = 1`.
- `kkMetric_eq_triangular_conj` : congruence factorization `G = U B Uᵀ`.

## iii. Table of contents

- A. Triangular factorization and determinant

## iv. References

* Theodor Kaluza, *Zum Unitätsproblem der Physik*, *Sitzungsberichte der Preu\ssischen Akademie
  der Wissenschaften zu Berlin, Mathematisch-Physikalische Klasse* (1921). [ref: Kaluza1921]
* Oskar Klein, *Quantentheorie und fünfdimensionale Relativitätstheorie*, *Zeitschrift für Physik*
  (1926). [ref: Klein1926]
* Oskar Klein, *The Atomicity of Electricity as a Quantum Theory Law*, *Nature* (1926). [ref:
  Klein1926Nature]

-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace KaluzaKlein

/-!

## A. Triangular factorization and determinant

Factoring the gauge potential `A_μ` into a unitriangular shear matrix isolates the determinant
contribution of the fifth-dimensional dilaton `φ`.

-/

/-- Upper-unitriangular Kaluza–Klein frame matrix `U` with `U_{μ4} = A_μ` and `1` on the
diagonal. -/
def kkTriangular (A : Fin 4 → ℝ) : Tensor2 5 :=
  fun i j =>
    if i = j then 1
    else if hi : i.val < 4 then
      if j = 4 then A ⟨i.val, hi⟩ else 0
    else 0

/-- Block-diagonal 5D matrix `diag(g4, φ²)`. -/
def kkBlockDiag (g4 : Tensor2 4) (φ : ℝ) : Tensor2 5 :=
  fun i j =>
    if hi : i.val < 4 then
      if hj : j.val < 4 then g4 ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
    else if i = 4 ∧ j = 4 then φ ^ 2 else 0

/-- The upper-unitriangular Kaluza–Klein frame matrix `kkTriangular A` has unit determinant. -/
lemma det_kkTriangular (A : Fin 4 → ℝ) : Matrix.det (kkTriangular A) = 1 := by
  have htri : Matrix.BlockTriangular (kkTriangular A) id := by
    intro i j hij
    have hne : i ≠ j := ne_of_gt hij
    have hj4 : j ≠ 4 := by
      intro h; subst h
      exact absurd hij (not_lt.mpr (Fin.le_last i))
    simp [kkTriangular, hne, hj4]
  rw [Matrix.det_of_isUpperTriangular htri]
  refine Finset.prod_eq_one fun i _ => ?_
  simp [kkTriangular]

/-- Congruence factorization `kkMetric g4 A φ = U * diag(g4, φ²) * Uᵀ`. -/
lemma kkMetric_eq_triangular_conj (g4 : Tensor2 4) (A : Fin 4 → ℝ) (φ : ℝ) :
    kkMetric g4 A φ = kkTriangular A * kkBlockDiag g4 φ * (kkTriangular A).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff,
      Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_five,
      kkMetric, metric4Ext, kkTriangular, kkBlockDiag, extendedPotential] <;>
    ring

end KaluzaKlein

end Modified

end GeneralRelativity
