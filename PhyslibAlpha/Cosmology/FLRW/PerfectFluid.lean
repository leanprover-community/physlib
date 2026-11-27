/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Physlib.Relativity.SpeedOfLight
public import PhyslibAlpha.Cosmology.FLRW.Curvature
public import PhyslibAlpha.Relativity.General.GravitationalConstant
public import PhyslibAlpha.Relativity.Tensors.PerfectFluidStressEnergy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# FLRW comoving perfect fluid and Friedmann equations

Comoving perfect-fluid stress-energy tensor and equivalence between the FLRW Einstein field
equations `G_{ij} + Λ g_{ij} = (8 π G / c⁴) T_{ij}` and the two Friedmann equations.

## i. Overview

Equating the Einstein tensor of an FLRW spacetime (in length-dimensioned time coordinate
`τ = c t`, so `ds² = -dτ² + a(τ)² dΣ_k²`) with the comoving perfect-fluid stress-energy tensor
`T_{ij} = (ρ c² + p) u_i u_j + p g_{ij}` (with unit four-velocity `u = (-1, 0, 0, 0)`) recovers:

1. From `(0, 0)`: the first-order Friedmann energy-density equation
   `(a'/a)² = (8 π G / (3 c²)) ρ - k / a² + Λ / 3`.
2. From `(1, 1)` together with `(0, 0)`: the second-order Friedmann acceleration equation
   `a''/a = -(4 π G / (3 c²)) (ρ + 3 p / c²) + Λ / 3`.

Here primes denote differentiation with respect to `τ = c t`; multiplying by `c²` converts these
to the standard cosmic-time Friedmann equations bridged in `FriedmannEquations.lean`.

## ii. Key results

- `GeneralRelativity.perfectFluidStressEnergy` : comoving perfect-fluid stress-energy tensor.
- `FLRWSpacetime.einsteinTensor_00_iff_friedmann` : `(0, 0)` Einstein equation ↔ first Friedmann
  equation.
- `FLRWSpacetime.einsteinTensor_spatial_iff_friedmann` : `(1, 1)` Einstein equation ↔ second
  Friedmann equation.
- `FLRWSpacetime.einsteinTensor_iff_friedmann` : full Einstein equations ↔ both Friedmann
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

open GeneralRelativity

namespace Cosmology

namespace FLRW

open GeneralRelativity.CoordinateCurvature

/-!

## A. Comoving perfect fluid and Einstein–Friedmann equivalence

Equating the FLRW Einstein tensor with the comoving perfect-fluid stress-energy tensor directly
recovers the first and second Friedmann equations for an arbitrary speed of light and Newton's
gravitational constant.

-/

namespace FLRWSpacetime

/-- The `(0, 0)` Einstein equation `G_{00} + Λ g_{00} = (8 π G / c⁴) T_{00}` for an FLRW spacetime
and a comoving perfect fluid is equivalent to the first-order Friedmann energy-density equation in
coordinate time `τ = c t`. -/
lemma einsteinTensor_00_iff_friedmann (S : FLRWSpacetime) (c : SpeedOfLight) (Λ : ℝ)
    (G : GravitationalConstant) (ρ p : ℝ) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0) (hr : x 1 ≠ 0)
    (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    (S.toCoordinateMetric.einsteinTensor x 0 0 + Λ * S.metric x 0 0
        = 8 * Real.pi * G.val / (c : ℝ) ^ 4 * GeneralRelativity.perfectFluidStressEnergy c ρ p (S.metric x) 0 0)
      ↔ (deriv S.a (x 0) / S.a (x 0)) ^ 2
          = (8 * Real.pi * G.val / (3 * (c : ℝ) ^ 2)) * ρ - S.k / (S.a (x 0)) ^ 2 + Λ / 3 := by
  have hc : (c : ℝ) ≠ 0 := c.val_ne_zero
  rw [S.einsteinTensor x ha hr hkr hsin ha_diff ha2 0 0]
  simp only [metric, GeneralRelativity.perfectFluidStressEnergy, Matrix.of_apply, ↓reduceIte, and_self, mul_one]
  have hrhs : 8 * Real.pi * G.val / (c : ℝ) ^ 4 * (ρ * (c : ℝ) ^ 2 + p + p * -1)
      = 8 * Real.pi * G.val / (c : ℝ) ^ 2 * ρ := by
    field_simp [hc]
    ring
  rw [hrhs]
  have hdiv : 8 * Real.pi * G.val / (3 * (c : ℝ) ^ 2) * ρ
      = (8 * Real.pi * G.val / (c : ℝ) ^ 2 * ρ) / 3 := by
    field_simp [hc]
  rw [hdiv]
  constructor <;> intro h <;> linarith

/-- Given the first-order Friedmann equation, the spatial diagonal Einstein equation `(1, 1)` is
equivalent to the second-order Friedmann acceleration equation in coordinate time `τ = c t`. -/
lemma einsteinTensor_spatial_iff_friedmann (S : FLRWSpacetime) (c : SpeedOfLight) (Λ : ℝ)
    (G : GravitationalConstant) (ρ p : ℝ) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0) (hr : x 1 ≠ 0)
    (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0))
    (hf1 : (deriv S.a (x 0) / S.a (x 0)) ^ 2
      = (8 * Real.pi * G.val / (3 * (c : ℝ) ^ 2)) * ρ - S.k / (S.a (x 0)) ^ 2 + Λ / 3) :
    (S.toCoordinateMetric.einsteinTensor x 1 1 + Λ * S.metric x 1 1
        = 8 * Real.pi * G.val / (c : ℝ) ^ 4 * GeneralRelativity.perfectFluidStressEnergy c ρ p (S.metric x) 1 1)
      ↔ deriv (deriv S.a) (x 0) / S.a (x 0)
          = -(4 * Real.pi * G.val / (3 * (c : ℝ) ^ 2)) * (ρ + 3 * p / (c : ℝ) ^ 2) + Λ / 3 := by
  have hc : (c : ℝ) ≠ 0 := c.val_ne_zero
  have hg11 : S.a (x 0) ^ 2 / (1 - S.k * x 1 ^ 2) ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 ha) hkr
  rw [S.einsteinTensor x ha hr hkr hsin ha_diff ha2 1 1]
  simp only [metric, GeneralRelativity.perfectFluidStressEnergy, Matrix.of_apply, Fin.isValue, one_ne_zero,
    false_and, ↓reduceIte, mul_zero, zero_add]
  have hfac : -(2 * (deriv (deriv S.a) (x 0) / S.a (x 0)) + (deriv S.a (x 0) / S.a (x 0)) ^ 2
        + S.k / (S.a (x 0)) ^ 2) * (S.a (x 0) ^ 2 / (1 - S.k * x 1 ^ 2))
        + Λ * (S.a (x 0) ^ 2 / (1 - S.k * x 1 ^ 2))
      = 8 * Real.pi * G.val / (c : ℝ) ^ 4 * (p * (S.a (x 0) ^ 2 / (1 - S.k * x 1 ^ 2))) ↔
      -(2 * (deriv (deriv S.a) (x 0) / S.a (x 0)) + (deriv S.a (x 0) / S.a (x 0)) ^ 2
        + S.k / (S.a (x 0)) ^ 2) + Λ = 8 * Real.pi * G.val / (c : ℝ) ^ 4 * p := by
    constructor <;> intro h
    · exact mul_right_cancel₀ hg11 (by linear_combination h)
    · linear_combination (S.a (x 0) ^ 2 / (1 - S.k * x 1 ^ 2)) * h
  rw [hfac]
  have hrhs : -(4 * Real.pi * G.val / (3 * (c : ℝ) ^ 2)) * (ρ + 3 * p / (c : ℝ) ^ 2)
      = -(4 * Real.pi * G.val / (3 * (c : ℝ) ^ 2) * ρ)
        - 4 * Real.pi * G.val / (c : ℝ) ^ 4 * p := by
    field_simp [hc]
    ring
  have h8 : 8 * Real.pi * G.val / (3 * (c : ℝ) ^ 2) * ρ
      = 2 * (4 * Real.pi * G.val / (3 * (c : ℝ) ^ 2) * ρ) := by ring
  have h8p : 8 * Real.pi * G.val / (c : ℝ) ^ 4 * p
      = 2 * (4 * Real.pi * G.val / (c : ℝ) ^ 4 * p) := by ring
  rw [hrhs]
  constructor <;> intro h <;> linarith

/-- Einstein's equation `G_{ij} + Λ g_{ij} = (8 π G / c⁴) T_{ij}` for an FLRW spacetime and a
comoving perfect fluid is equivalent to the first- and second-order Friedmann equations in
coordinate time `τ = c t`. -/
lemma einsteinTensor_iff_friedmann (S : FLRWSpacetime) (c : SpeedOfLight) (Λ : ℝ)
    (G : GravitationalConstant) (ρ p : ℝ) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0) (hr : x 1 ≠ 0)
    (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    (∀ i j, S.toCoordinateMetric.einsteinTensor x i j + Λ * S.metric x i j
        = 8 * Real.pi * G.val / (c : ℝ) ^ 4 * GeneralRelativity.perfectFluidStressEnergy c ρ p (S.metric x) i j)
      ↔ ((deriv S.a (x 0) / S.a (x 0)) ^ 2
            = (8 * Real.pi * G.val / (3 * (c : ℝ) ^ 2)) * ρ - S.k / (S.a (x 0)) ^ 2 + Λ / 3)
          ∧ (deriv (deriv S.a) (x 0) / S.a (x 0)
              = -(4 * Real.pi * G.val / (3 * (c : ℝ) ^ 2)) * (ρ + 3 * p / (c : ℝ) ^ 2)
                + Λ / 3) := by
  have hc : (c : ℝ) ≠ 0 := c.val_ne_zero
  constructor
  · intro h
    have hf1 := (S.einsteinTensor_00_iff_friedmann c Λ G ρ p x ha hr hkr hsin ha_diff ha2).mp
      (h 0 0)
    exact ⟨hf1,
      (S.einsteinTensor_spatial_iff_friedmann c Λ G ρ p x ha hr hkr hsin ha_diff ha2 hf1).mp
        (h 1 1)⟩
  · rintro ⟨hf1, hf2⟩ i j
    rw [S.einsteinTensor x ha hr hkr hsin ha_diff ha2 i j]
    have hcoef : -(2 * (deriv (deriv S.a) (x 0) / S.a (x 0))
        + (deriv S.a (x 0) / S.a (x 0)) ^ 2 + S.k / (S.a (x 0)) ^ 2) + Λ
        = 8 * Real.pi * G.val / (c : ℝ) ^ 4 * p := by
      have hrhs : -(4 * Real.pi * G.val / (3 * (c : ℝ) ^ 2)) * (ρ + 3 * p / (c : ℝ) ^ 2)
          = -(4 * Real.pi * G.val / (3 * (c : ℝ) ^ 2) * ρ)
            - 4 * Real.pi * G.val / (c : ℝ) ^ 4 * p := by
        field_simp [hc]
        ring
      have h8 : 8 * Real.pi * G.val / (3 * (c : ℝ) ^ 2) * ρ
          = 2 * (4 * Real.pi * G.val / (3 * (c : ℝ) ^ 2) * ρ) := by ring
      have h8p : 8 * Real.pi * G.val / (c : ℝ) ^ 4 * p
          = 2 * (4 * Real.pi * G.val / (c : ℝ) ^ 4 * p) := by ring
      rw [hrhs] at hf2
      linarith
    fin_cases i <;> fin_cases j <;> simp [metric, GeneralRelativity.perfectFluidStressEnergy]
    · have hrhs0 : 8 * Real.pi * G.val / (c : ℝ) ^ 4 * (ρ * (c : ℝ) ^ 2)
          = 3 * (8 * Real.pi * G.val / (3 * (c : ℝ) ^ 2) * ρ) := by
        field_simp [hc]
      rw [hrhs0]
      linarith
    · linear_combination (S.a (x 0) ^ 2 / (1 - S.k * x 1 ^ 2)) * hcoef
    · linear_combination (S.a (x 0) ^ 2 * x 1 ^ 2) * hcoef
    · linear_combination (S.a (x 0) ^ 2 * x 1 ^ 2 * Real.sin (x 2) ^ 2) * hcoef

end FLRWSpacetime

end FLRW

end Cosmology
