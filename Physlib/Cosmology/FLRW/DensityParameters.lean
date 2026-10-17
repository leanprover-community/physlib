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

The reference quantity is the critical density `ρ_cr = 3 H² / (8 π G)`. It is the mass density
for which this equation holds with `k = 0` and `Λ = 0`: the density of a spatially flat universe
without cosmological constant expanding at the rate `H`. It is called critical because, when
`Λ = 0`, a universe denser than `ρ_cr` is spatially closed (`k > 0`), a less dense one is open
(`k < 0`), and a universe at exactly `ρ_cr` is flat. It depends on time through `H`.

Each term of the equation is then measured in units of `ρ_cr`, which gives dimensionless
quantities:
- the density parameter `Ω = ρ / ρ_cr` of a component of mass density `ρ`;
- the cosmological-constant density parameter `Ω_Λ = Λ c² / (3 H²)`, which is the density
  parameter of the uniform density `ρ_Λ = Λ c² / (8 π G)` equivalent to `Λ`;
- the curvature density parameter `Ω_K = - k c² / (H² a²)`, which is not the density of a fluid
  but the share of the budget carried by spatial curvature.

Dividing the Friedmann equation by `H²` gives the closure relation `Ω + Ω_Λ + Ω_K = 1`.

The reduced Hubble function of the standard cosmological model, built from these parameters, is
in `Physlib.Cosmology.FLRW.ReducedHubble`, and the age of the universe in
`Physlib.Cosmology.FLRW.Age`.

## ii. Key results

- `criticalDensity`, `densityParameter`, `curvatureDensityParameter`, `lambdaDensityParameter`.
- `densityParameter_add_lambda_add_curvature`: the closure relation `Ω + Ω_Λ + Ω_K = 1`;
  `densityParameter_add_curvature`: `Ω + Ω_K = 1` when `Λ = 0`;
  `FLRW.FriedmannSolution.densityParameter_add_lambda_add_curvature`: the closure relation for
  an FLRW model whose cosmic fluid solves the Friedmann equations, with `Ω_K` given by its
  spatial geometry.

## iii. Table of contents

- A. The critical density and the density parameters
- B. The closure relation

-/

@[expose] public section

namespace Cosmology.FLRW.FriedmannEquation

open Real Time

/-!

## A. The critical density and the density parameters

-/

/-- The critical density `ρ_cr = 3 H² / (8 π G)`: the mass density for which the first-order
  Friedmann equation holds with `k = 0` and `Λ = 0` at the expansion rate `H`, that is, the
  density of a spatially flat universe without cosmological constant. It is the unit in which
  the density parameters are measured, and it depends on time through `H`. -/
noncomputable def criticalDensity (a : Time → ℝ) (G : ℝ) (t : Time) : ℝ :=
  3 * hubbleConstant a t ^ 2 / (8 * π * G)

/-- The density parameter `Ω = ρ / ρ_cr`: the mass density `ρ` of a component in units of the
  critical density. It is dimensionless; without cosmological constant, a total density
  parameter equal to `1` corresponds to a spatially flat universe
  (see `densityParameter_add_curvature`). -/
noncomputable def densityParameter (a ρ : Time → ℝ) (G : ℝ) (t : Time) : ℝ :=
  ρ t / criticalDensity a G t

/-- The curvature density parameter `Ω_K = - k c² / (H² a²)`: the share of the first-order
  Friedmann equation carried by the spatial curvature `k`, in the same units as the density
  parameters. It is not the density of a fluid; it is positive for `k < 0`, negative for
  `k > 0` and zero for a spatially flat universe. -/
noncomputable def curvatureDensityParameter (a : Time → ℝ) (k c : ℝ) (t : Time) : ℝ :=
  -k * c ^ 2 / (hubbleConstant a t ^ 2 * a t ^ 2)

/-- The cosmological-constant density parameter `Ω_Λ = Λ c² / (3 H²)`: the share of the
  first-order Friedmann equation carried by the cosmological constant. It is the density
  parameter of the uniform density `ρ_Λ = Λ c² / (8 π G)` (see `lambdaDensityParameter_eq`). -/
noncomputable def lambdaDensityParameter (a : Time → ℝ) (Λ c : ℝ) (t : Time) : ℝ :=
  Λ * c ^ 2 / (3 * hubbleConstant a t ^ 2)

/-- `Ω_Λ` is the density parameter of the fluid `ρ_Λ = Λ c² / (8 π G)`. -/
lemma lambdaDensityParameter_eq {a : Time → ℝ} {Λ G c : ℝ} {t : Time} (hG : G ≠ 0) :
    lambdaDensityParameter a Λ c t
      = densityParameter a (fun _ => cosmologicalConstantDensity Λ G c) G t := by
  unfold lambdaDensityParameter densityParameter criticalDensity cosmologicalConstantDensity
  have hπ := Real.pi_ne_zero
  field_simp

/-!

## B. The closure relation

-/

/-- The closure relation `Ω + Ω_Λ + Ω_K = 1`, a rearrangement of the first-order Friedmann
  equation, for `H ≠ 0`. -/
lemma densityParameter_add_lambda_add_curvature {a ρ : Time → ℝ} {k Λ G c : ℝ} {t : Time}
    (ha : a t ≠ 0) (hH : hubbleConstant a t ≠ 0)
    (hF1 : FirstOrderFriedmann a ρ k Λ G c t) :
    densityParameter a ρ G t + lambdaDensityParameter a Λ c t
      + curvatureDensityParameter a k c t = 1 := by
  unfold densityParameter lambdaDensityParameter curvatureDensityParameter criticalDensity
  unfold FirstOrderFriedmann at hF1
  unfold hubbleConstant at hH ⊢
  have hπ := Real.pi_ne_zero
  have key : ρ t / (3 * (∂ₜ a t / a t) ^ 2 / (8 * π * G)) + Λ * c ^ 2 / (3 * (∂ₜ a t / a t) ^ 2)
      + -k * c ^ 2 / ((∂ₜ a t / a t) ^ 2 * a t ^ 2)
      = (8 * π * G / 3 * ρ t - k * c ^ 2 / a t ^ 2 + Λ * c ^ 2 / 3) / (∂ₜ a t / a t) ^ 2 := by
    field_simp
    ring
  rw [key, ← hF1, div_self (pow_ne_zero 2 hH)]

/-- The closure relation `Ω + Ω_K = 1` without cosmological constant. -/
lemma densityParameter_add_curvature {a ρ : Time → ℝ} {k G c : ℝ} {t : Time} (ha : a t ≠ 0)
    (hH : hubbleConstant a t ≠ 0) (hF1 : FirstOrderFriedmann a ρ k 0 G c t) :
    densityParameter a ρ G t + curvatureDensityParameter a k c t = 1 := by
  have h := densityParameter_add_lambda_add_curvature ha hH hF1
  have h0 : lambdaDensityParameter a 0 c t = 0 := by
    unfold lambdaDensityParameter
    ring
  rw [h0, add_zero] at h
  exact h

/-- If the FLRW model `U` filled with the cosmic fluid `F` solves the Friedmann equations, the
  closure relation `Ω + Ω_Λ + Ω_K = 1` holds at every time of the interval `U.I` at which
  `H ≠ 0`, the curvature density parameter `Ω_K` being computed from the curvature parameter of
  the spatial geometry. -/
lemma _root_.Cosmology.FLRW.FriedmannSolution.densityParameter_add_lambda_add_curvature
    {U : FLRW} {F : CosmicFluid} {Λ G c : ℝ} (h : U.FriedmannSolution F Λ G c) {t : Time}
    (ht : t ∈ U.I) (hH : hubbleConstant U.a t ≠ 0) :
    densityParameter U.a F.ρ G t + lambdaDensityParameter U.a Λ c t
      + curvatureDensityParameter U.a U.geometry.curvature c t = 1 :=
  FLRW.FriedmannEquation.densityParameter_add_lambda_add_curvature (U.a_ne_zero ht) hH
    (h.firstOrder t ht)

end Cosmology.FLRW.FriedmannEquation
