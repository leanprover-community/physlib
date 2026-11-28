/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.SpaceTimeDerivBridge
public import PhyslibAlpha.Relativity.Metrics.Minkowski
public import PhyslibAlpha.Relativity.Tensors.EinsteinTensor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Conservation of the Einstein tensor

The contracted Bianchi identity implies that the Einstein tensor is divergence free and is the
unique conserved combination of `Ric` and `R g` up to scale.

## i. Overview

The contracted Bianchi identity `∇^a Ric_ab = (1/2) ∇_b R` follows in differential geometry from
the second Bianchi identity together with metric compatibility. Taking it as an explicit
hypothesis in locally inertial (Riemann normal) coordinates at a point (`g = ginv = η` and
`∂g = 0`, so covariant and coordinate derivatives coincide there), this module derives:

- `inertialDivergence_combination` : `∇^a (α Ric + β R g)_b = (α / 2 + β) ∇_b R`;
- `inertialDivergence_einstein_eq_zero` : `∇^a G_ab = 0`;
- `combination_conserved_iff` : if `∇R ≠ 0` somewhere, `α Ric + β R g` is conserved only when
  `α = -2β`, isolating the Einstein tensor up to an overall constant.

## ii. Key results

- `CurvatureDerivatives` : the pointwise partial derivatives of `Ric` and `R` in locally inertial
  coordinates.
- `CurvatureDerivatives.einsteinDeriv` : pointwise derivative of the Einstein tensor.
- `CurvatureDerivatives.ofCoordinate` : curvature derivatives read from `coordDeriv`.
- `inertialDivergence` : divergence `∇^a T_ab = ∑ a, η^{aa} ∂_a T_ab` in locally inertial
  coordinates.
- `inertialDivergence_combination` : divergence of `α Ric + β R g`.
- `inertialDivergence_einstein_eq_zero` : conservation of the Einstein tensor from the contracted
  Bianchi hypothesis.
- `combination_conserved_iff` : uniqueness of the Einstein combination `α = -2β`.

## iii. Table of contents

- A. Derivatives and divergence in locally inertial coordinates
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

## A. Derivatives and divergence in locally inertial coordinates

At any point in locally inertial (Riemann normal) coordinates, `g_{ab} = η_{ab}` and
`∂_e g_{ab} = 0`, so covariant derivatives of `Ric`, `R`, and `G` reduce to the partial derivatives
stored in `CurvatureDerivatives`, separately from `coordDeriv`.

-/

/-- First partial derivatives of the Ricci tensor and scalar curvature at a point in locally
inertial (Riemann normal) coordinates (`dRic e i j = ∂_e Ric_ij`, `dS e = ∂_e R`), kept as explicit
data so the pointwise contracted Bianchi identity can be proved algebraically. -/
structure CurvatureDerivatives where
  /-- Coordinate derivatives `∂_e Ric_ij` of the Ricci tensor. -/
  dRic : Fin 4 → Tensor2 4
  /-- Coordinate derivatives `∂_e R` of the scalar curvature. -/
  dS : Fin 4 → ℝ

/-- Curvature derivatives of a Ricci tensor field `Ric` and scalar curvature field `R`, read from
their coordinate partial derivatives via `coordDeriv`. In locally inertial coordinates these are
the partial derivatives appearing in the contracted Bianchi identity. -/
noncomputable def CurvatureDerivatives.ofCoordinate
    (Ric : (Fin 4 → ℝ) → Tensor2 4) (R : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) :
    CurvatureDerivatives where
  dRic := fun e i j => CoordinateCurvature.coordDeriv e (fun y => Ric y i j) x
  dS := fun e => CoordinateCurvature.coordDeriv e R x

@[simp] lemma CurvatureDerivatives.ofCoordinate_dRic
    (Ric : (Fin 4 → ℝ) → Tensor2 4) (R : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ)
    (e : Fin 4) (i j : Fin 4) :
    (CurvatureDerivatives.ofCoordinate Ric R x).dRic e i j =
      CoordinateCurvature.coordDeriv e (fun y => Ric y i j) x := rfl

@[simp] lemma CurvatureDerivatives.ofCoordinate_dS
    (Ric : (Fin 4 → ℝ) → Tensor2 4) (R : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (e : Fin 4) :
    (CurvatureDerivatives.ofCoordinate Ric R x).dS e =
      CoordinateCurvature.coordDeriv e R x := rfl

/-- Pointwise derivative of the Einstein tensor in locally inertial coordinates:
`∂_e G_ij = ∂_e Ric_ij - (1/2) ∂_e R η_ij` (since `g = η` and `∂g = 0` at the origin of locally
inertial coordinates). -/
noncomputable def CurvatureDerivatives.einsteinDeriv (D : CurvatureDerivatives) (e : Fin 4) :
    Tensor2 4 :=
  fun i j => D.dRic e i j - (1 / 2) * D.dS e * minkowskiMetric4 i j

/-- Divergence of a rank-2 tensor derivative family in locally inertial coordinates:
`∇^a T_ab = ∑ a, η^{aa} ∂_a T_ab`. -/
noncomputable def inertialDivergence (T : Fin 4 → Tensor2 4) (b : Fin 4) : ℝ :=
  ∑ a, minkowskiMetric4 a a * T a a b

/-!

## B. Conservation and uniqueness of the Einstein tensor

Using the locally inertial divergence operator, the contracted Bianchi identity forces `G` to be
divergence free and singles out `α = -2 β` uniquely.

-/

/-- The divergence of a linear combination `α Ric + β R g`: the contracted Bianchi identity
collapses `∇Ric` to `(1/2) ∇R`, leaving `(α/2 + β) ∇_b R`. -/
lemma inertialDivergence_combination (D : CurvatureDerivatives)
    (hB : ∀ b, (∑ a, minkowskiMetric4 a a * D.dRic a a b) = (1 / 2) * D.dS b)
    (α β : ℝ) (b : Fin 4) :
    inertialDivergence (fun e i j => α * D.dRic e i j + β * D.dS e * minkowskiMetric4 i j) b
      = (α / 2 + β) * D.dS b := by
  have hterm : ∀ a,
      minkowskiMetric4 a a * (α * D.dRic a a b + β * D.dS a * minkowskiMetric4 a b)
        = α * (minkowskiMetric4 a a * D.dRic a a b)
          + β * (D.dS a * (minkowskiMetric4 a a * minkowskiMetric4 a b)) := by
    intro a
    ring
  simp only [inertialDivergence]
  rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hB b, sum_minkowskiMetric4_mul (fun a => D.dS a) b]
  ring

/-- The Einstein tensor is conserved (`∇^a G_ab = 0`) under the contracted Bianchi identity. -/
lemma inertialDivergence_einstein_eq_zero (D : CurvatureDerivatives)
    (hB : ∀ b, (∑ a, minkowskiMetric4 a a * D.dRic a a b) = (1 / 2) * D.dS b) (b : Fin 4) :
    inertialDivergence D.einsteinDeriv b = 0 := by
  have h := inertialDivergence_combination D hB 1 (-(1 / 2)) b
  have heq : D.einsteinDeriv
      = fun e i j => 1 * D.dRic e i j + (-(1 / 2)) * D.dS e * minkowskiMetric4 i j := by
    funext e i j
    simp only [CurvatureDerivatives.einsteinDeriv]
    ring
  rw [heq, h]
  ring

/-- Uniqueness of the Einstein combination: if `∇_b R ≠ 0` somewhere, `α Ric + β R g` is
divergence free only when `α = -2β`, i.e. a multiple of `G = Ric - (1/2) R g`. -/
lemma combination_conserved_iff (D : CurvatureDerivatives)
    (hB : ∀ b, (∑ a, minkowskiMetric4 a a * D.dRic a a b) = (1 / 2) * D.dS b)
    (α β : ℝ) (hne : ∃ b, D.dS b ≠ 0)
    (h : ∀ b,
      inertialDivergence (fun e i j => α * D.dRic e i j + β * D.dS e * minkowskiMetric4 i j) b
        = 0) :
    α = -2 * β := by
  obtain ⟨b, hb⟩ := hne
  have h0 : (α / 2 + β) * D.dS b = 0 := by
    rw [← inertialDivergence_combination D hB α β b]
    exact h b
  have hc : α / 2 + β = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h2
    · exact h1
    · exact absurd h2 hb
  linarith

end GeneralRelativity
