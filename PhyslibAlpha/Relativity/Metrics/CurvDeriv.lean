/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.Minkowski
public import PhyslibAlpha.Relativity.Tensors.EinsteinTensor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Conservation of the Einstein tensor

The contracted Bianchi identity implies that the Einstein tensor is divergence free and is the
unique conserved combination of `Ric` and `S g` up to scale.

## i. Overview

The contracted Bianchi identity `∇^a Ric_ab = (1/2) ∇_b S` follows in differential geometry from
the second Bianchi identity together with metric compatibility. Taking it as an explicit
hypothesis `hB` in an orthonormal Lorentzian chart (`g = ginv = η`), this module derives:

- `divergence_combination` : `∇^a (α Ric + β S g)_b = (α / 2 + β) ∇_b S`;
- `divergence_einstein_eq_zero` : `∇^a G_ab = 0`;
- `combination_conserved_iff` : if `∇S ≠ 0` somewhere, `α Ric + β S g` is conserved only when
  `α = -2β`, isolating the Einstein tensor up to an overall constant.

## ii. Key results

- `CurvDeriv` : bundle of coordinate partial derivatives of `Ric` and `S` in an orthonormal
  chart.
- `divergence` : divergence `∇^a T_ab = ∑ a, η^{aa} ∂_a T_ab` in an orthonormal chart.
- `divergence_combination` : divergence of `α Ric + β S g`.
- `divergence_einstein_eq_zero` : conservation of the Einstein tensor from the contracted
  Bianchi hypothesis.
- `combination_conserved_iff` : uniqueness of the Einstein combination `α = -2β`.

## iii. Table of contents

- A. Derivative bundles and divergence in an orthonormal chart
- B. Conservation and uniqueness of the Einstein tensor

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 3 (Sec. 3.1-3.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 11.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 3
  (https://arxiv.org/pdf/gr-qc/9712019#page=69). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Derivative bundles and divergence in an orthonormal chart

-/

/-- Derivatives of the Ricci tensor and of the scalar curvature in an orthonormal chart:
`dRic e i j = ∂_e Ric_ij` and `dS e = ∂_e S`. -/
structure CurvDeriv where
  /-- Coordinate derivatives `∂_e Ric_ij` of the Ricci tensor. -/
  dRic : Fin 4 → Tensor2 4
  /-- Coordinate derivatives `∂_e S` of the scalar curvature. -/
  dS : Fin 4 → ℝ

/-- The derivative of the Einstein tensor, `∂_e G_ij = ∂_e Ric_ij - (1/2) ∂_e S η_ij`
(the metric is constant in an orthonormal chart, so `∂η = 0`). -/
noncomputable def CurvDeriv.dEinstein (D : CurvDeriv) (e : Fin 4) : Tensor2 4 :=
  fun i j => D.dRic e i j - (1 / 2) * D.dS e * minkowskiMetric4 i j

/-- Divergence of a family of rank-2 tensor derivatives in an orthonormal chart:
`∇^a T_ab = ∑ a, η^{aa} ∂_a T_ab`. -/
noncomputable def divergence (T : Fin 4 → Tensor2 4) (b : Fin 4) : ℝ :=
  ∑ a, minkowskiMetric4 a a * T a a b

/-- Raising and lowering with `η` cancels: `∑ a, f a * (η^{aa} η_ab) = f b`. -/
lemma sum_eta_mul (f : Fin 4 → ℝ) (b : Fin 4) :
    (∑ a, f a * (minkowskiMetric4 a a * minkowskiMetric4 a b)) = f b := by
  fin_cases b <;> simp [Fin.sum_univ_four, minkowskiMetric4]

/-!

## B. Conservation and uniqueness of the Einstein tensor

-/

/-- The divergence of a linear combination `α Ric + β S g`: the contracted Bianchi identity
collapses `∇Ric` to `(1/2) ∇S`, leaving `(α/2 + β) ∇_b S`. -/
lemma divergence_combination (D : CurvDeriv)
    (hB : ∀ b, (∑ a, minkowskiMetric4 a a * D.dRic a a b) = (1 / 2) * D.dS b)
    (α β : ℝ) (b : Fin 4) :
    divergence (fun e i j => α * D.dRic e i j + β * D.dS e * minkowskiMetric4 i j) b
      = (α / 2 + β) * D.dS b := by
  have hterm : ∀ a,
      minkowskiMetric4 a a * (α * D.dRic a a b + β * D.dS a * minkowskiMetric4 a b)
        = α * (minkowskiMetric4 a a * D.dRic a a b)
          + β * (D.dS a * (minkowskiMetric4 a a * minkowskiMetric4 a b)) := by
    intro a
    ring
  simp only [divergence]
  rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hB b, sum_eta_mul (fun a => D.dS a) b]
  ring

/-- The Einstein tensor is conserved (`∇^a G_ab = 0`) under the contracted Bianchi identity. -/
lemma divergence_einstein_eq_zero (D : CurvDeriv)
    (hB : ∀ b, (∑ a, minkowskiMetric4 a a * D.dRic a a b) = (1 / 2) * D.dS b) (b : Fin 4) :
    divergence D.dEinstein b = 0 := by
  have h := divergence_combination D hB 1 (-(1 / 2)) b
  have heq : D.dEinstein
      = fun e i j => 1 * D.dRic e i j + (-(1 / 2)) * D.dS e * minkowskiMetric4 i j := by
    funext e i j
    simp only [CurvDeriv.dEinstein]
    ring
  rw [heq, h]
  ring

/-- Uniqueness of the Einstein combination: if `∇_b S ≠ 0` somewhere, `α Ric + β S g` is
divergence free only when `α = -2β`, i.e. a multiple of `G = Ric - (1/2) S g`. -/
lemma combination_conserved_iff (D : CurvDeriv)
    (hB : ∀ b, (∑ a, minkowskiMetric4 a a * D.dRic a a b) = (1 / 2) * D.dS b)
    (α β : ℝ) (hne : ∃ b, D.dS b ≠ 0)
    (h : ∀ b, divergence (fun e i j => α * D.dRic e i j + β * D.dS e * minkowskiMetric4 i j) b
      = 0) :
    α = -2 * β := by
  obtain ⟨b, hb⟩ := hne
  have h0 : (α / 2 + β) * D.dS b = 0 := by
    rw [← divergence_combination D hB α β b]
    exact h b
  have hc : α / 2 + β = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h2
    · exact h1
    · exact absurd h2 hb
  linarith

end GeneralRelativity
