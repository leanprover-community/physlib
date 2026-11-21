/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Basic

/-!

# Brans–Dicke scalar–tensor theory

PPN parameter `γ`, effective gravitational coupling, bounds, and the general-relativity limit
`ω → ∞`.

## i. Overview

In Brans–Dicke gravity, a massless scalar field `φ` couples non-minimally to the Ricci scalar
with dimensionless parameter `ω`. In the weak-field post-Newtonian expansion, light deflection and
Shapiro time delay are governed by `γ(ω) = (1 + ω) / (2 + ω)`, while the effective Newton
constant scales as `coupling(ω) = (4 + 2ω) / (3 + 2ω)`.

This module formalises `gamma` and `coupling`, proves `1/2 < γ < 1` for `ω > 0`, establishes the
Cassini solar-system bound `ω > 40000 ⇒ 1 - γ < 1/40000`, proves the `ω → ∞` limit `γ → 1`,
exhibits `ω = 0` (`γ = 1/2`) as the metric `f(R)` value, proves `1 ≤ coupling ω ≤ 4/3` for
`ω ≥ 0`, and records the ghost pole at `ω = -3/2`.

## ii. Key results

- `gamma` : Brans–Dicke PPN parameter `(1 + ω) / (2 + ω)`.
- `gamma_bounds`, `cassini_deviation`, `gamma_tendsto_atTop` : bounds, Cassini constraint, and
  GR limit as `ω → ∞`.
- `fR_gamma` : `γ(0) = 1/2`, matching unscreened metric `f(R)` gravity.
- `coupling`, `coupling_bounds`, `coupling_pole` : effective coupling `1 + 1/(3 + 2ω)` and its
  kinetic degeneracy pole at `ω = -3/2`.

## iii. Table of contents

- A. The PPN parameter and the general-relativity limit
- B. The effective gravitational coupling

## iv. References

* None.

-/

@[expose] public section

namespace GeneralRelativity

namespace BransDicke

/-!

## A. The PPN parameter and the general-relativity limit

-/

/-- The Brans–Dicke PPN parameter `γ = (1 + ω) / (2 + ω)`. -/
noncomputable def gamma (ω : ℝ) : ℝ := (1 + ω) / (2 + ω)

/-- `γ = 1 - 1 / (2 + ω)`: the deviation from general relativity is reciprocal in `2 + ω`. -/
lemma gamma_eq_one_sub (ω : ℝ) (h : 2 + ω ≠ 0) : gamma ω = 1 - 1 / (2 + ω) := by
  simp only [gamma]
  field_simp
  ring

/-- For every `ω > 0`, Brans–Dicke satisfies `1/2 < γ < 1`. -/
lemma gamma_bounds (ω : ℝ) (hω : 0 < ω) : 1 / 2 < gamma ω ∧ gamma ω < 1 := by
  have h2 : (2 : ℝ) < 2 + ω := by linarith
  have hinv_lt : 1 / (2 + ω) < 1 / 2 :=
    one_div_lt_one_div_of_lt (by norm_num) h2
  have hinv_pos : (0 : ℝ) < 1 / (2 + ω) := by positivity
  rw [gamma_eq_one_sub ω (by linarith)]
  constructor <;> linarith

/-- Cassini spacecraft bound: `ω > 40000` forces `1 - γ < 1 / 40000`. -/
lemma cassini_deviation (ω : ℝ) (h : 40000 < ω) : 1 - gamma ω < 1 / 40000 := by
  rw [gamma_eq_one_sub ω (by linarith)]
  have h2 : (40000 : ℝ) < 2 + ω := by linarith
  have hinv : 1 / (2 + ω) < 1 / 40000 :=
    one_div_lt_one_div_of_lt (by norm_num) h2
  linarith

/-- The general-relativity limit: as `ω → ∞`, `gamma ω → 1`. -/
lemma gamma_tendsto_atTop :
    Filter.Tendsto (fun ω : ℝ => gamma ω) Filter.atTop (nhds 1) := by
  have hden : Filter.Tendsto (fun ω : ℝ => 2 + ω) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop.2 fun b => Filter.eventually_atTop.2 ⟨b - 2, fun ω hω => by linarith⟩
  have hinv : Filter.Tendsto (fun ω : ℝ => 1 / (2 + ω)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have hsub : Filter.Tendsto (fun ω : ℝ => 1 - 1 / (2 + ω)) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hinv
  refine Filter.Tendsto.congr' ?_ hsub
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with ω hω
  exact (gamma_eq_one_sub ω (by linarith)).symm

/-- Metric `f(R)` gravity corresponds to Brans–Dicke with `ω = 0`, giving `γ = 1/2`. -/
lemma fR_gamma : gamma 0 = 1 / 2 := by
  norm_num [gamma]

/-!

## B. The effective gravitational coupling

-/

/-- The Brans–Dicke effective gravitational coupling ratio `(4 + 2ω) / (3 + 2ω)`. -/
noncomputable def coupling (ω : ℝ) : ℝ := (4 + 2 * ω) / (3 + 2 * ω)

/-- `(4 + 2ω) / (3 + 2ω) = 1 + 1 / (3 + 2ω)`. -/
lemma coupling_eq_one_add (ω : ℝ) (h : 3 + 2 * ω ≠ 0) :
    coupling ω = 1 + 1 / (3 + 2 * ω) := by
  simp only [coupling]
  field_simp
  ring

/-- For `ω ≥ 0`, the effective coupling lies in `[1, 4/3]`. -/
lemma coupling_bounds (ω : ℝ) (hω : 0 ≤ ω) : 1 ≤ coupling ω ∧ coupling ω ≤ 4 / 3 := by
  have hden : (0 : ℝ) < 3 + 2 * ω := by linarith
  have hinv_le : 1 / (3 + 2 * ω) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hinv_pos : (0 : ℝ) < 1 / (3 + 2 * ω) := by positivity
  rw [coupling_eq_one_add ω (by linarith)]
  constructor <;> linarith

/-- `ω = -3/2` is the pole of the effective coupling where the scalar kinetic term vanishes. -/
lemma coupling_pole : 3 + 2 * (-(3 / 2) : ℝ) = 0 := by norm_num

end BransDicke

end GeneralRelativity
