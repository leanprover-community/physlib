/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Modified Newtonian Dynamics (MOND)

Structural properties of Milgrom's modified inertia/gravity acceleration law and interpolating
functions.

## i. Overview

Milgrom's MOND relates the true acceleration `a` to the Newtonian gravitational acceleration
`g_N = G M / r²` via `μ(a / a₀) a = g_N`, where `a₀` is a universal acceleration scale and
`μ` is an interpolating function satisfying `μ(x) → 1` for `x ≫ 1` and `μ(x) ~ x` for `x ≪ 1`.

This module formalises the MOND relation, the Newtonian limit (`μ = 1`), the deep-MOND regime
(`a = √(a₀ g_N)` yielding flat rotation curves `v⁴ = G M a₀`), the contrast with Keplerian
Newtonian velocities (`G M / r₁ ≠ G M / r₂`), and bounds and asymptotics for the standard
simple (`x / (1 + x)`) and standard (`x / √(1 + x²)`) interpolating functions.

## ii. Key results

- `newtonAccel`, `deepAccel`, `Relation` : Newtonian point-mass acceleration, deep-MOND
  acceleration, and the MOND interpolating relation.
- `newtonian_limit` : where `μ(a / a₀) = 1`, `a = g_N`.
- `flat_rotation` : deep-MOND circular orbits satisfy `v⁴ = G M a₀`, independent of radius.
- `newtonian_velocity_ne` : Newtonian orbits with fixed enclosed mass cannot share a circular
  speed at two distinct radii.
- `simpleMu`, `standardMu` : standard interpolating functions with bounds and high-acceleration
  Newtonian limits.

## iii. Table of contents

- A. The MOND relation and flat rotation curves
- B. Standard interpolating functions

## iv. References

* None.

-/

@[expose] public section

namespace GeneralRelativity

namespace MOND

/-!

## A. The MOND relation and flat rotation curves

-/

/-- Newtonian gravitational acceleration `G M / r²` of a point mass `M`. -/
noncomputable def newtonAccel (G M r : ℝ) : ℝ := G * M / r ^ 2

/-- Deep-MOND acceleration `√(a₀ g_N)` solving `μ(a / a₀) a = g_N` when `μ(x) = x`. -/
noncomputable def deepAccel (a₀ gN : ℝ) : ℝ := Real.sqrt (a₀ * gN)

/-- The MOND interpolating relation `μ(a / a₀) * a = g_N`. -/
def Relation (μ : ℝ → ℝ) (a₀ a gN : ℝ) : Prop := μ (a / a₀) * a = gN

/-- Newtonian limit: where the interpolating function saturates at `1`, MOND reproduces
Newtonian acceleration `a = g_N`. -/
lemma newtonian_limit (μ : ℝ → ℝ) {a₀ a gN : ℝ} (hμ : μ (a / a₀) = 1)
    (h : Relation μ a₀ a gN) : a = gN := by
  simpa [Relation, hμ] using h

/-- Square of the deep-MOND acceleration: `deepAccel a₀ g_N ^ 2 = a₀ * g_N`. -/
lemma deep_accel_sq {a₀ gN : ℝ} (h : 0 ≤ a₀ * gN) :
    deepAccel a₀ gN ^ 2 = a₀ * gN := by
  simp [deepAccel, Real.sq_sqrt h]

/-- Flat rotation curves from MOND: with `v² = a r` and the deep-MOND acceleration law,
`v⁴ = G M a₀` (the baryonic Tully–Fisher relation), independent of radius `r`. -/
lemma flat_rotation (G M a₀ r : ℝ) (hr : r ≠ 0)
    (h : 0 ≤ a₀ * (G * M / r ^ 2)) :
    (deepAccel a₀ (newtonAccel G M r) * r) ^ 2 = G * M * a₀ := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  simp only [newtonAccel] at h ⊢
  rw [mul_pow, deep_accel_sq h]
  rw [mul_assoc, div_mul_cancel₀ _ hr2]
  ring

/-- Contrast with Newtonian dynamics: with a fixed enclosed mass `G M ≠ 0`, two distinct radii
cannot share the same circular velocity squared. -/
lemma newtonian_velocity_ne (G M r₁ r₂ : ℝ) (hGM : G * M ≠ 0)
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) (h : r₁ ≠ r₂) :
    (G * M) / r₁ ≠ (G * M) / r₂ := by
  intro heq
  rw [div_eq_div_iff hr₁ hr₂] at heq
  exact h (mul_left_cancel₀ hGM heq).symm

/-!

## B. Standard interpolating functions

-/

/-- The simple MOND interpolating function `μ(x) = x / (1 + x)`. -/
noncomputable def simpleMu (x : ℝ) : ℝ := x / (1 + x)

/-- The standard MOND interpolating function `μ(x) = x / √(1 + x²)`. -/
noncomputable def standardMu (x : ℝ) : ℝ := x / Real.sqrt (1 + x ^ 2)

/-- For positive `x`, `0 < simpleMu x < 1`. -/
lemma simpleMu_bounds {x : ℝ} (hx : 0 < x) : 0 < simpleMu x ∧ simpleMu x < 1 := by
  have h1 : 0 < 1 + x := by linarith
  refine ⟨div_pos hx h1, ?_⟩
  rw [simpleMu, div_lt_one h1]
  linarith

/-- For positive `x`, `0 < standardMu x < 1`. -/
lemma standardMu_bounds {x : ℝ} (hx : 0 < x) : 0 < standardMu x ∧ standardMu x < 1 := by
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have hsq : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr hpos
  refine ⟨div_pos hx hsq, ?_⟩
  rw [standardMu, div_lt_one hsq, Real.lt_sqrt hx.le]
  linarith

/-- In the Newtonian regime `x → ∞`, the simple interpolating function approaches `1`. -/
lemma simpleMu_tendsto_atTop :
    Filter.Tendsto simpleMu Filter.atTop (nhds 1) := by
  have hden : Filter.Tendsto (fun x : ℝ => 1 + x) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop.2 fun b => Filter.eventually_atTop.2 ⟨b - 1, fun x hx => by linarith⟩
  have h1 : Filter.Tendsto (fun x : ℝ => 1 / (1 + x)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have hsub : Filter.Tendsto (fun x : ℝ => 1 - 1 / (1 + x)) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub h1
  refine Filter.Tendsto.congr' ?_ hsub
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
  have hden : 1 + x ≠ 0 := by linarith
  simp only [simpleMu]
  field_simp
  ring

end MOND

end GeneralRelativity
