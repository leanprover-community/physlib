/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Cosmology.FLRW.Christoffel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# FLRW comoving perfect fluid and Friedmann equations

Comoving perfect-fluid stress-energy tensor `perfectFluidT` and equivalence between the FLRW
Einstein field equations `G_{ij} + Λ g_{ij} = 8 π G T_{ij}` and the two Friedmann equations.

## i. Overview

Equating the coordinate-pipeline Einstein tensor of an `FLRWSpacetime` with the comoving
perfect-fluid stress-energy tensor `T_{ij} = (ρ + p) u_i u_j + p g_{ij}` (for `u = (-1, 0, 0, 0)`
in units `c = 1`) recovers:

1. From `(0, 0)`: the first-order Friedmann energy-density equation
   `(a'/a)² = (8 π G / 3) ρ - k / a² + Λ / 3`.
2. From `(1, 1)` together with `(0, 0)`: the second-order Friedmann acceleration equation
   `a''/a = -(4 π G / 3) (ρ + 3 p) + Λ / 3`.

## ii. Key results

- `perfectFluidT` : comoving perfect-fluid stress-energy tensor.
- `FLRWSpacetime.einsteinTensorOf_00_iff_friedmann` : `(0, 0)` Einstein equation ↔ first Friedmann
  equation.
- `FLRWSpacetime.einsteinTensorOf_spatial_iff_friedmann` : `(1, 1)` Einstein equation ↔ second
  Friedmann equation.
- `FLRWSpacetime.einsteinTensorOf_iff_friedmann` : full Einstein equations ↔ both Friedmann
  equations.

## iii. Table of contents

- A. Comoving perfect fluid and Einstein–Friedmann equivalence

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 5 (Sec. 5.1-5.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 27.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 8
  (https://arxiv.org/pdf/gr-qc/9712019#page=201). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace FLRW

open GeneralRelativity.Pipeline

/-!

## A. Comoving perfect fluid and Einstein–Friedmann equivalence

Equating the pipeline Einstein tensor with comoving perfect-fluid stress-energy directly recovers
the first and second Friedmann equations in geometric units `c = 1`.

-/

/-- Comoving perfect-fluid stress-energy tensor `T_{ij} = (ρ + p) u_i u_j + p g_{ij}` for a
comoving observer `u = (-1, 0, 0, 0)` (units `c = 1`). -/
def perfectFluidT (ρ p : ℝ) (g : Tensor2 4) : Tensor2 4 :=
  fun i j => (ρ + p) * (if i = 0 ∧ j = 0 then 1 else 0) + p * g i j

namespace FLRWSpacetime

/-- The `(0, 0)` Einstein equation `G_{00} + Λ g_{00} = 8 π G T_{00}` for an FLRW spacetime and a
comoving perfect fluid is equivalent to the first-order Friedmann energy-density equation. -/
lemma einsteinTensorOf_00_iff_friedmann (S : FLRWSpacetime) (Λ G ρ p : ℝ) (x : Fin 4 → ℝ)
    (ha : S.a (x 0) ≠ 0) (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    (Pipeline.einsteinTensorOf S.metric S.metricInv x 0 0 + Λ * S.metric x 0 0
        = 8 * Real.pi * G * perfectFluidT ρ p (S.metric x) 0 0)
      ↔ (deriv S.a (x 0) / S.a (x 0)) ^ 2
          = (8 * Real.pi * G / 3) * ρ - S.k / (S.a (x 0)) ^ 2 + Λ / 3 := by
  rw [S.einsteinTensorOf x ha hr hkr hsin ha_diff ha2 0 0]
  simp only [metric, perfectFluidT, ↓reduceIte, and_self, mul_one]
  constructor <;> intro h <;> linarith

/-- Given the first-order Friedmann equation, the spatial diagonal Einstein equation `(1, 1)`
is equivalent to the second-order Friedmann acceleration equation. -/
lemma einsteinTensorOf_spatial_iff_friedmann (S : FLRWSpacetime) (Λ G ρ p : ℝ) (x : Fin 4 → ℝ)
    (ha : S.a (x 0) ≠ 0) (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0))
    (hf1 : (deriv S.a (x 0) / S.a (x 0)) ^ 2
      = (8 * Real.pi * G / 3) * ρ - S.k / (S.a (x 0)) ^ 2 + Λ / 3) :
    (Pipeline.einsteinTensorOf S.metric S.metricInv x 1 1 + Λ * S.metric x 1 1
        = 8 * Real.pi * G * perfectFluidT ρ p (S.metric x) 1 1)
      ↔ deriv (deriv S.a) (x 0) / S.a (x 0) = -(4 * Real.pi * G / 3) * (ρ + 3 * p) + Λ / 3 := by
  have hg11 : S.a (x 0) ^ 2 / (1 - S.k * x 1 ^ 2) ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 ha) hkr
  rw [S.einsteinTensorOf x ha hr hkr hsin ha_diff ha2 1 1]
  simp only [metric, perfectFluidT, Fin.isValue, one_ne_zero, false_and, ↓reduceIte,
    mul_zero, zero_add]
  have hfac : -(2 * (deriv (deriv S.a) (x 0) / S.a (x 0)) + (deriv S.a (x 0) / S.a (x 0)) ^ 2
        + S.k / (S.a (x 0)) ^ 2) * (S.a (x 0) ^ 2 / (1 - S.k * x 1 ^ 2))
        + Λ * (S.a (x 0) ^ 2 / (1 - S.k * x 1 ^ 2))
      = 8 * Real.pi * G * (p * (S.a (x 0) ^ 2 / (1 - S.k * x 1 ^ 2))) ↔
      -(2 * (deriv (deriv S.a) (x 0) / S.a (x 0)) + (deriv S.a (x 0) / S.a (x 0)) ^ 2
        + S.k / (S.a (x 0)) ^ 2) + Λ = 8 * Real.pi * G * p := by
    constructor <;> intro h
    · exact mul_right_cancel₀ hg11 (by linear_combination h)
    · linear_combination (S.a (x 0) ^ 2 / (1 - S.k * x 1 ^ 2)) * h
  rw [hfac]
  constructor <;> intro h <;> linarith

/-- Einstein's equation `G_{ij} + Λ g_{ij} = 8 π G T_{ij}` for an FLRW spacetime and a comoving
perfect fluid is equivalent to the first- and second-order Friedmann equations (`c = 1`). -/
lemma einsteinTensorOf_iff_friedmann (S : FLRWSpacetime) (Λ G ρ p : ℝ) (x : Fin 4 → ℝ)
    (ha : S.a (x 0) ≠ 0) (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    (∀ i j, Pipeline.einsteinTensorOf S.metric S.metricInv x i j + Λ * S.metric x i j
        = 8 * Real.pi * G * perfectFluidT ρ p (S.metric x) i j)
      ↔ ((deriv S.a (x 0) / S.a (x 0)) ^ 2
            = (8 * Real.pi * G / 3) * ρ - S.k / (S.a (x 0)) ^ 2 + Λ / 3)
          ∧ (deriv (deriv S.a) (x 0) / S.a (x 0)
              = -(4 * Real.pi * G / 3) * (ρ + 3 * p) + Λ / 3) := by
  constructor
  · intro h
    have hf1 := (S.einsteinTensorOf_00_iff_friedmann Λ G ρ p x ha hr hkr hsin ha_diff ha2).mp
      (h 0 0)
    exact ⟨hf1,
      (S.einsteinTensorOf_spatial_iff_friedmann Λ G ρ p x ha hr hkr hsin ha_diff ha2 hf1).mp
        (h 1 1)⟩
  · rintro ⟨hf1, hf2⟩ i j
    rw [S.einsteinTensorOf x ha hr hkr hsin ha_diff ha2 i j]
    have hcoef : -(2 * (deriv (deriv S.a) (x 0) / S.a (x 0))
        + (deriv S.a (x 0) / S.a (x 0)) ^ 2 + S.k / (S.a (x 0)) ^ 2) + Λ = 8 * Real.pi * G * p := by
      linarith
    fin_cases i <;> fin_cases j <;> simp [metric, perfectFluidT]
    · linarith
    · linear_combination (S.a (x 0) ^ 2 / (1 - S.k * x 1 ^ 2)) * hcoef
    · linear_combination (S.a (x 0) ^ 2 * x 1 ^ 2) * hcoef
    · linear_combination (S.a (x 0) ^ 2 * x 1 ^ 2 * Real.sin (x 2) ^ 2) * hcoef

end FLRWSpacetime

end FLRW

end GeneralRelativity
