/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Jinzheng Li
-/
module

public import Physlib.Cosmology.FLRW.MatterContent
/-!

# Density parameters and the closure relation

## i. Overview

The first-order Friedmann equation of `Physlib.Cosmology.FLRW.Basic`,
`H² = (8 π G / 3) ρ - k c² / a² + Λ c² / 3`, can be read as a budget for the expansion rate `H`.

The critical density `ρ_cr = 3 H² / (8 π G)` is the density for which this equation holds with
`k = 0` and `Λ = 0`. When `Λ = 0`, a universe denser than `ρ_cr` is spatially closed (`k > 0`), a
less dense one is open (`k < 0`), and one at exactly `ρ_cr` is flat.

Measuring each term in units of `ρ_cr` gives the density parameter `Ω = ρ / ρ_cr` of a fluid, the
density parameter `Ω_Λ = Λ c² / (3 H²)` of the cosmological constant and the curvature density
parameter `Ω_K = - k c² / (H² a²)`. Dividing the Friedmann equation by `H²` gives the closure
relation `Ω + Ω_Λ + Ω_K = 1`.

These quantities are defined for an FLRW model. For a solution of the Friedmann equations, the
closure relation holds at every time of the interval of the model at which `H ≠ 0`.

The reduced Hubble function of the standard cosmological model is in
`Physlib.Cosmology.FLRW.ReducedHubble`, and the age of the universe in
`Physlib.Cosmology.FLRW.Age`.

## ii. Key results

- `FLRW.criticalDensity`, `FLRW.densityParameter`, `FLRW.curvatureDensityParameter`,
  `FLRW.lambdaDensityParameter`: the critical density and the density parameters of an FLRW
  model.
- `FLRW.lambdaDensityParameter_eq_densityParameter`,
  `FLRW.densityParameter_addCosmologicalConstant`: `Ω_Λ` is the density parameter of the
  cosmological constant as a fluid.
- `FLRW.FriedmannSolution.densityParameter_add_lambda_add_curvature`,
  `FLRW.FriedmannSolution.densityParameter_add_curvature`: the closure relations
  `Ω + Ω_Λ + Ω_K = 1` and, for `Λ = 0`, `Ω + Ω_K = 1`.

## iii. Table of contents

- A. The critical density and the density parameters
- B. The closure relation

-/

@[expose] public section

namespace Cosmology.FLRW

open Real Time FriedmannEquation

variable (U : FLRW)

/-!

## A. The critical density and the density parameters

With the convention `x / 0 = 0`, these quantities vanish when `H = 0` or `G = 0`. They have their
physical meaning at the times at which `H ≠ 0`.

-/

/-- The critical density `ρ_cr = 3 H² / (8 π G)` of an FLRW model at time `t`, where `H` is the
  Hubble parameter of its scale factor. It is the density of a spatially flat universe without
  cosmological constant expanding at the rate `H`. -/
noncomputable def criticalDensity (G : ℝ) (t : Time) : ℝ :=
  3 * hubbleConstant U.a t ^ 2 / (8 * π * G)

/-- The density parameter `Ω = ρ / ρ_cr` of a cosmic fluid in an FLRW model. -/
noncomputable def densityParameter (F : CosmicFluid) (G : ℝ) (t : Time) : ℝ :=
  F.ρ t / U.criticalDensity G t

/-- The curvature density parameter `Ω_K = - k c² / (H² a²)` of an FLRW model, where `k` is the
  curvature parameter of its spatial geometry. When `H`, `a` and `c` are nonzero, it is positive
  for a saddle geometry, negative for a spherical one and zero for the flat one. -/
noncomputable def curvatureDensityParameter (c : ℝ) (t : Time) : ℝ :=
  -U.geometry.curvature * c ^ 2 / (hubbleConstant U.a t ^ 2 * U.a t ^ 2)

/-- The density parameter `Ω_Λ = Λ c² / (3 H²)` of the cosmological constant in an FLRW
  model. -/
noncomputable def lambdaDensityParameter (Λ c : ℝ) (t : Time) : ℝ :=
  Λ * c ^ 2 / (3 * hubbleConstant U.a t ^ 2)

/-- For `G ≠ 0`, `Ω_Λ` is the density parameter of the empty fluid with the cosmological constant
  folded in. -/
lemma lambdaDensityParameter_eq_densityParameter {Λ G c : ℝ} (hG : G ≠ 0) (t : Time) :
    U.lambdaDensityParameter Λ c t
      = U.densityParameter (CosmicFluid.empty.addCosmologicalConstant Λ G c) G t := by
  simp only [lambdaDensityParameter, densityParameter, criticalDensity, CosmicFluid.empty,
    CosmicFluid.addCosmologicalConstant, cosmologicalConstantDensity, zero_add]
  have hπ := Real.pi_ne_zero
  field_simp

/-- For `G ≠ 0`, folding the cosmological constant into a cosmic fluid adds `Ω_Λ` to its
  density parameter. -/
lemma densityParameter_addCosmologicalConstant (F : CosmicFluid) {Λ G c : ℝ} (hG : G ≠ 0)
    (t : Time) :
    U.densityParameter (F.addCosmologicalConstant Λ G c) G t
      = U.densityParameter F G t + U.lambdaDensityParameter Λ c t := by
  rw [U.lambdaDensityParameter_eq_densityParameter hG]
  simp only [densityParameter, CosmicFluid.empty, CosmicFluid.addCosmologicalConstant, zero_add,
    add_div]

/-!

## B. The closure relation

-/

namespace FriedmannSolution

variable {U} {F : CosmicFluid} {Λ G c : ℝ}

/-- The closure relation `Ω + Ω_Λ + Ω_K = 1` for a solution of the Friedmann equations, at the
  times of the interval of the model at which `H ≠ 0`. -/
lemma densityParameter_add_lambda_add_curvature (h : U.FriedmannSolution F Λ G c) {t : Time}
    (ht : t ∈ U.I) (hH : hubbleConstant U.a t ≠ 0) :
    U.densityParameter F G t + U.lambdaDensityParameter Λ c t
      + U.curvatureDensityParameter c t = 1 := by
  have hF1 := h.firstOrder t ht
  unfold densityParameter lambdaDensityParameter curvatureDensityParameter criticalDensity
  unfold FirstOrderFriedmann at hF1
  unfold hubbleConstant at hH ⊢
  have hπ := Real.pi_ne_zero
  have ha := U.a_ne_zero ht
  have key : F.ρ t / (3 * (∂ₜ U.a t / U.a t) ^ 2 / (8 * π * G))
      + Λ * c ^ 2 / (3 * (∂ₜ U.a t / U.a t) ^ 2)
      + -U.geometry.curvature * c ^ 2 / ((∂ₜ U.a t / U.a t) ^ 2 * U.a t ^ 2)
      = (8 * π * G / 3 * F.ρ t - U.geometry.curvature * c ^ 2 / U.a t ^ 2 + Λ * c ^ 2 / 3)
        / (∂ₜ U.a t / U.a t) ^ 2 := by
    field_simp
    ring
  rw [key, ← hF1, div_self (pow_ne_zero 2 hH)]

/-- The closure relation `Ω + Ω_K = 1` for a solution of the Friedmann equations without
  cosmological constant, at the times of the interval of the model at which `H ≠ 0`. -/
lemma densityParameter_add_curvature (h : U.FriedmannSolution F 0 G c) {t : Time} (ht : t ∈ U.I)
    (hH : hubbleConstant U.a t ≠ 0) :
    U.densityParameter F G t + U.curvatureDensityParameter c t = 1 := by
  have h1 := h.densityParameter_add_lambda_add_curvature ht hH
  simpa [lambdaDensityParameter] using h1

end FriedmannSolution

end Cosmology.FLRW
