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

# Compact-circle diffeomorphisms and `U(1)` gauge transformations

Volume-preserving 5D coordinate shifts `x'^4 = x^4 + λ(x^μ)` induce the electromagnetic gauge
transformation `A_μ ↦ A_μ + ∂_μ λ` on `kkMetric`.

## i. Overview

A coordinate diffeomorphism shifting the compact fifth coordinate `x^4` by a scalar function
`λ(x^μ)` has Jacobian `kkGaugeJacobian (∂λ)` of unit determinant, and pulls `kkMetric g4 A φ` back
to `kkMetric g4 (A + ∂λ) φ`.

## ii. Key results

- `kkGaugeJacobian` : Jacobian matrix of a compact-circle shift.
- `det_kkGaugeJacobian` : unit determinant (`det J = 1`).
- `kkGaugeJacobian_pullback` : pullback equivalence with `U(1)` gauge transformations.

## iii. Table of contents

- A. Compact-circle diffeomorphisms and U(1) gauge transformations

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

## A. Compact-circle diffeomorphisms and U(1) gauge transformations

-/

private lemma val_lt_four_0 : (0 : Fin 5).val < 4 := by decide
private lemma val_lt_four_1 : (1 : Fin 5).val < 4 := by decide
private lemma val_lt_four_2 : (2 : Fin 5).val < 4 := by decide
private lemma val_lt_four_3 : (3 : Fin 5).val < 4 := by decide
private lemma not_val_lt_four_4 : ¬((4 : Fin 5).val < 4) := by decide
private lemma fin4_mk_0 (h : (0 : Fin 5).val < 4) : (⟨(0 : Fin 5).val, h⟩ : Fin 4) = 0 := rfl
private lemma fin4_mk_1 (h : (1 : Fin 5).val < 4) : (⟨(1 : Fin 5).val, h⟩ : Fin 4) = 1 := rfl
private lemma fin4_mk_2 (h : (2 : Fin 5).val < 4) : (⟨(2 : Fin 5).val, h⟩ : Fin 4) = 2 := rfl
private lemma fin4_mk_3 (h : (3 : Fin 5).val < 4) : (⟨(3 : Fin 5).val, h⟩ : Fin 4) = 3 := rfl
private lemma potExt_0 (A : Fin 4 → ℝ) : potExt A 0 = A 0 := rfl
private lemma potExt_1 (A : Fin 4 → ℝ) : potExt A 1 = A 1 := rfl
private lemma potExt_2 (A : Fin 4 → ℝ) : potExt A 2 = A 2 := rfl
private lemma potExt_3 (A : Fin 4 → ℝ) : potExt A 3 = A 3 := rfl
private lemma potExt_4 (A : Fin 4 → ℝ) : potExt A 4 = 1 := rfl

/-- Jacobian matrix `(∂x'^A / ∂x^B)` of a 5D compact-circle coordinate shift `x'^4 = x^4 + λ(x^μ)`
with 4D gradient `dlam_μ = ∂_μ λ`. -/
def kkGaugeJacobian (dlam : Fin 4 → ℝ) : Tensor2 5 :=
  fun i j =>
    if i = j then 1
    else if i = 4 then
      if hj : j.val < 4 then dlam ⟨j.val, hj⟩ else 0
    else 0

/-- A compact-circle shift is volume-preserving: `det (kkGaugeJacobian dlam) = 1`. -/
lemma det_kkGaugeJacobian (dlam : Fin 4 → ℝ) : Matrix.det (kkGaugeJacobian dlam) = 1 := by
  rw [← Matrix.det_transpose]
  have htri : Matrix.BlockTriangular (kkGaugeJacobian dlam).transpose id := by
    intro i j hij
    have hne : j ≠ i := ne_of_lt hij
    have hj4 : j ≠ 4 := by
      intro h; subst h
      change 4 < i at hij
      omega
    simp [kkGaugeJacobian, hne, hj4]
  rw [Matrix.det_of_isUpperTriangular htri]
  refine Finset.prod_eq_one fun i _ => ?_
  simp [kkGaugeJacobian]

/-- Five-dimensional diffeomorphism-to-`U(1)`-gauge theorem: pulling back `kkMetric g4 A φ` by
the compact-circle shift Jacobian `kkGaugeJacobian dlam` shifts the 4D electromagnetic potential by
`A_μ ↦ A_μ + dlam_μ` while leaving `g4` and `φ` invariant. -/
lemma kkGaugeJacobian_pullback (g4 : Tensor2 4) (A dlam : Fin 4 → ℝ) (φ : ℝ) :
    (kkGaugeJacobian dlam).transpose * kkMetric g4 A φ * kkGaugeJacobian dlam =
      kkMetric g4 (fun μ => A μ + dlam μ) φ := by
  ext i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by fin_cases i <;> decide
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by fin_cases j <;> decide
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_five,
    kkMetric, metric4Ext, kkGaugeJacobian,
    val_lt_four_0, val_lt_four_1, val_lt_four_2, val_lt_four_3, not_val_lt_four_4,
    fin4_mk_0, fin4_mk_1, fin4_mk_2, fin4_mk_3,
    potExt_0, potExt_1, potExt_2, potExt_3, potExt_4,
    Fin.isValue, Fin.reduceEq, ↓reduceIte, ↓reduceDIte]
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    simp only [val_lt_four_0, val_lt_four_1, val_lt_four_2, val_lt_four_3, not_val_lt_four_4,
      fin4_mk_0, fin4_mk_1, fin4_mk_2, fin4_mk_3,
      potExt_0, potExt_1, potExt_2, potExt_3, potExt_4,
      Fin.isValue, Fin.reduceEq, ↓reduceIte, ↓reduceDIte] <;>
    ring

end KaluzaKlein

end Modified

end GeneralRelativity
