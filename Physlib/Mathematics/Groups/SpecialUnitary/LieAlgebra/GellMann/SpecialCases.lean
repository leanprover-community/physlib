/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.Groups.SpecialUnitary.LieAlgebra.GellMann.Basic
public import Physlib.Relativity.PauliMatrices.Basic
/-!

# The Pauli and Gell-Mann matrices

The generalized Gell-Mann matrices in the special cases `n = 2` and `n = 3`.

## i. Overview

For `n = 2` the generalized Gell-Mann matrices are the Pauli matrices `σ₁, σ₂, σ₃` (A), and for
`n = 3` they are the Gell-Mann matrices `λ₁, …, λ₈` (B). In each case an equivalence of
`GellMannIndex n` with `Fin (n² - 1)` puts the labels in the standard order.

## ii. Key results

- `SULieAlgebra.gellMannMatrices_two` : for `n = 2`, the Pauli matrices `σ₁, σ₂, σ₃`.
- `SULieAlgebra.gellMannMatrices_three` : for `n = 3`, the Gell-Mann matrices `λ₁, …, λ₈`.

## iii. Table of contents

- A. The case `n = 2`
- B. The case `n = 3`

## iv. References

* https://mathworld.wolfram.com/GeneralizedGell-MannMatrix.html

-/

@[expose] public section

namespace SULieAlgebra

open Matrix

/-!

## A. The case `n = 2`

-/

/-- For `n = 2`, the labelling of the generalized Gell-Mann matrices as the Pauli matrices
  `σ₁, σ₂, σ₃` (as `0, 1, 2`): the symmetric, antisymmetric and diagonal matrices. -/
def GellMannIndex.equivTwo : GellMannIndex 2 ≃ Fin 3 where
  toFun
    | .symm _ _ _ => 0
    | .antisymm _ _ _ => 1
    | .diag _ => 2
  invFun := ![.symm 0 1 (by simp), .antisymm 0 1 (by simp), .diag 0]
  left_inv := by
    rintro (⟨p, q, h⟩ | ⟨p, q, h⟩ | l)
    · fin_cases p <;> fin_cases q <;> first | rfl | simp at h
    · fin_cases p <;> fin_cases q <;> first | rfl | simp at h
    · fin_cases l
      rfl
  right_inv i := by fin_cases i <;> rfl

/-- For `n = 2` the generalized Gell-Mann matrices are the Pauli matrices `σ₁, σ₂, σ₃`, labelled
  by `GellMannIndex.equivTwo`. -/
lemma gellMannMatrices_two (i : Fin 3) :
    (gellMannMatrices (GellMannIndex.equivTwo.symm i)).1 = PauliMatrix.pauliMatrix (Sum.inr i) := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [GellMannIndex.equivTwo, gellMannMatrices, PauliMatrix.pauliMatrix]

/-!

## B. The case `n = 3`

-/

/-- For `n = 3`, the labelling of the Gell-Mann matrices in the standard order `λ₁, …, λ₈`
  (as `0, …, 7`): `λ₁, λ₂, λ₃` are the symmetric, antisymmetric and diagonal matrices of the first
  two coordinates, `λ₄, λ₅` the symmetric and antisymmetric ones of the coordinates `0, 2`,
  `λ₆, λ₇` those of the coordinates `1, 2`, and `λ₈` the second diagonal matrix. -/
def GellMannIndex.equivThree : GellMannIndex 3 ≃ Fin 8 where
  toFun
    | .symm p q _ => if p.1 = 0 then (if q.1 = 1 then 0 else 3) else 5
    | .antisymm p q _ => if p.1 = 0 then (if q.1 = 1 then 1 else 4) else 6
    | .diag l => if l.1 = 0 then 2 else 7
  invFun := ![.symm 0 1 (by simp), .antisymm 0 1 (by simp), .diag 0, .symm 0 2 (by simp),
    .antisymm 0 2 (by simp), .symm 1 2 (by simp), .antisymm 1 2 (by simp), .diag 1]
  left_inv := by
    rintro (⟨p, q, h⟩ | ⟨p, q, h⟩ | l)
    · fin_cases p <;> fin_cases q <;> first | rfl | simp [Fin.lt_def] at h
    · fin_cases p <;> fin_cases q <;> first | rfl | simp [Fin.lt_def] at h
    · fin_cases l <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- For `n = 3` the generalized Gell-Mann matrices are the Gell-Mann matrices `λ₁, …, λ₈`, labelled
  in the standard order by `GellMannIndex.equivThree`. -/
lemma gellMannMatrices_three :
    (fun i => (gellMannMatrices (GellMannIndex.equivThree.symm i)).1) =
    ![!![0, 1, 0; 1, 0, 0; 0, 0, 0],
      !![0, -Complex.I, 0; Complex.I, 0, 0; 0, 0, 0],
      !![1, 0, 0; 0, -1, 0; 0, 0, 0],
      !![0, 0, 1; 0, 0, 0; 1, 0, 0],
      !![0, 0, -Complex.I; 0, 0, 0; Complex.I, 0, 0],
      !![0, 0, 0; 0, 0, 1; 0, 1, 0],
      !![0, 0, 0; 0, 0, -Complex.I; 0, Complex.I, 0],
      (1 / Real.sqrt 3 : ℂ) • !![1, 0, 0; 0, 1, 0; 0, 0, -2]] := by
  funext i
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [GellMannIndex.equivThree, gellMannMatrices, one_add_one_eq_two, div_mul_eq_div_div,
      show (1 : ℝ) + 2 = 3 by norm_num]

end SULieAlgebra
