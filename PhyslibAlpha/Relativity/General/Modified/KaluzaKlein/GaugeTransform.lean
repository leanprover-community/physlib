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

* Theodor Kaluza, *Zum Unitätsproblem der Physik*, *Sitzungsberichte der Preußischen Akademie der
  Wissenschaften zu Berlin, Mathematisch-Physikalische Klasse* (1921), pp. 966-972.
  [ref: Kaluza1921]
* Oskar Klein, *Quantentheorie und fünfdimensionale Relativitätstheorie*, *Zeitschrift für Physik*
  37, pp. 895-906 (1926), Sec. 1-2. [ref: Klein1926]
* Oskar Klein, *The Atomicity of Electricity as a Quantum Theory Law*, *Nature* 118, p. 516 (1926).
  [ref: Klein1926Nature]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace KaluzaKlein

/-!

## A. Compact-circle diffeomorphisms and U(1) gauge transformations

Volume-preserving shifts along the compact fifth circle act on the 5D metric by shifting the
4D electromagnetic potential `A_μ ↦ A_μ + ∂_μ λ`.

-/

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
      exact absurd hij (not_lt.mpr (Fin.le_last i))
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
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_five,
      kkMetric, metric4Ext, kkGaugeJacobian, extendedPotential] <;>
    ring

/-- Bundle form of `kkGaugeJacobian_pullback` acting directly on `KaluzaKleinData`. -/
lemma KaluzaKleinData.gaugeJacobian_pullback (D : KaluzaKleinData) (dlam : Fin 4 → ℝ) :
    (kkGaugeJacobian dlam).transpose * D.metric * kkGaugeJacobian dlam =
      (D.gaugeShift dlam).metric :=
  kkGaugeJacobian_pullback D.M.g D.A dlam D.φ

end KaluzaKlein

end Modified

end GeneralRelativity
