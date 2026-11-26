/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.NewtonianGravity
public import PhyslibAlpha.Relativity.General.GravitationalConstant
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

This module formalises `MONDTheory`, the Newtonian limit (`μ = 1`), the deep-MOND regime
(`a = √(a₀ g_N)` yielding flat rotation curves `v⁴ = G M a₀`), the contrast with Keplerian
Newtonian velocities (`G M / r₁ ≠ G M / r₂`), bounds and asymptotics for the standard simple
(`x / (1 + x)`) and standard (`x / √(1 + x²)`) interpolating functions, and the norm bridge to
Physlib's classical Newtonian acceleration.

## ii. Key results

- `MONDTheory`, `newtonianAcceleration`, `MONDTheory.deepMONDAcceleration`,
  `MONDTheory.Relation` : MOND theory parameterized by `a₀`, Newtonian point-mass acceleration,
  deep-MOND acceleration, and the MOND interpolating relation.
- `MONDTheory.newtonian_limit`, `MONDTheory.flat_rotation`, `newtonian_velocity_ne` :
  Newtonian recovery, flat rotation curves `v⁴ = G M a₀`, and Keplerian decline contrast.
- `simpleMu`, `standardMu` : standard interpolating functions with bounds and high-acceleration
  Newtonian limits.
- `norm_pairGravityAcceleration_eq_newtonianAcceleration` : bridge to Physlib's classical
  `pairGravityAcceleration`.

## iii. Table of contents

- A. The MOND relation and flat rotation curves
- B. Standard interpolating functions
- C. Bridge to Physlib Newtonian gravity

## iv. References

* Mordehai Milgrom, *A Modification of the Newtonian Dynamics as a Possible Alternative to the
  Hidden Mass Hypothesis*, *The Astrophysical Journal* 270, pp. 365-370 (1983), Sec. II.
  [ref: Milgrom1983a]
* Mordehai Milgrom, *A Modification of the Newtonian Dynamics: Implications for Galaxies*, *The
  Astrophysical Journal* 270, pp. 371-383 (1983), Sec. II. [ref: Milgrom1983b]
* Mordehai Milgrom, *A Modification of the Newtonian Dynamics: Implications for Galaxy Systems*,
  *The Astrophysical Journal* 270, pp. 384-389 (1983). [ref: Milgrom1983c]
* Jacob Bekenstein and Mordehai Milgrom, *Does the Missing Mass Problem Signal the Breakdown of
  Newtonian Gravity?*, *The Astrophysical Journal* 286, pp. 7-14 (1984), Sec. II.
  [ref: BekensteinMilgrom1984]
* Benoit Famaey and Stacy S. McGaugh, *Modified Newtonian Dynamics (MOND): Observational
  Phenomenology and Relativistic Extensions*, *Living Reviews in Relativity* (2012), Sec. 5-6
  (https://arxiv.org/pdf/1112.3960#page=25). [ref: FamaeyMcGaugh2012]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace MOND

/-!

## A. The MOND relation and flat rotation curves

At accelerations below `T.a0`, `T.deepMONDAcceleration` replaces Keplerian orbital decay with
asymptotically flat circular speeds satisfying `v⁴ = G M a₀`.

-/

/-- Milgrom's Modified Newtonian Dynamics (MOND) theory parameterized by the universal
acceleration scale `a₀`. -/
structure MONDTheory where
  /-- Critical transition acceleration scale `a₀`. -/
  a0 : ℝ

/-- Newtonian gravitational acceleration `G.val M / r²` of a point mass `M`. -/
noncomputable def newtonianAcceleration (G : GravitationalConstant) (M r : ℝ) : ℝ :=
  G.val * M / r ^ 2

/-- Deep-MOND acceleration `√(T.a0 g_N)` for a `MONDTheory`, solving `μ(a / a₀) a = g_N` when
`μ(x) = x`. -/
noncomputable def MONDTheory.deepMONDAcceleration (T : MONDTheory) (gN : ℝ) : ℝ :=
  Real.sqrt (T.a0 * gN)

/-- The MOND interpolating relation `μ(a / T.a0) * a = g_N` for a `MONDTheory`. -/
def MONDTheory.Relation (T : MONDTheory) (μ : ℝ → ℝ) (a gN : ℝ) : Prop :=
  μ (a / T.a0) * a = gN

/-- Newtonian limit: where the interpolating function saturates at `1`, MOND reproduces
Newtonian acceleration `a = g_N`. -/
lemma MONDTheory.newtonian_limit (T : MONDTheory) (μ : ℝ → ℝ) {a gN : ℝ}
    (hμ : μ (a / T.a0) = 1) (h : T.Relation μ a gN) : a = gN := by
  simpa [MONDTheory.Relation, hμ] using h

/-- Square of the deep-MOND acceleration: `T.deepMONDAcceleration g_N ^ 2 = T.a0 * g_N`. -/
lemma MONDTheory.deepMONDAcceleration_sq (T : MONDTheory) {gN : ℝ} (h : 0 ≤ T.a0 * gN) :
    T.deepMONDAcceleration gN ^ 2 = T.a0 * gN := by
  simp [MONDTheory.deepMONDAcceleration, Real.sq_sqrt h]

/-- Flat rotation curves from MOND: with `v² = a r` and the deep-MOND acceleration law,
`v⁴ = G.val M T.a0` (the baryonic Tully–Fisher relation), independent of radius `r`. -/
lemma MONDTheory.flat_rotation (T : MONDTheory) (G : GravitationalConstant) (M r : ℝ)
    (hr : r ≠ 0) (h : 0 ≤ T.a0 * (G.val * M / r ^ 2)) :
    (T.deepMONDAcceleration (newtonianAcceleration G M r) * r) ^ 2 = G.val * M * T.a0 := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  simp only [newtonianAcceleration] at h ⊢
  rw [mul_pow, T.deepMONDAcceleration_sq h, mul_assoc, div_mul_cancel₀ _ hr2]
  ring

/-- Contrast with Newtonian dynamics: with a fixed positive enclosed mass `M ≠ 0`, two distinct
radii cannot share the same circular velocity squared. -/
lemma newtonian_velocity_ne (G : GravitationalConstant) (M r₁ r₂ : ℝ) (hM : M ≠ 0)
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) (h : r₁ ≠ r₂) :
    (G.val * M) / r₁ ≠ (G.val * M) / r₂ := by
  have hGM : G.val * M ≠ 0 := mul_ne_zero G.pos.ne' hM
  intro heq
  rw [div_eq_div_iff hr₁ hr₂] at heq
  exact h (mul_left_cancel₀ hGM heq).symm

/-!

## B. Standard interpolating functions

The simple and standard interpolating functions interpolate smoothly between `μ(x) ~ x` at low
accelerations and `μ(x) → 1` in the Newtonian regime `x → ∞`.

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

/-!

## C. Bridge to Physlib Newtonian gravity

Comparing `newtonianAcceleration` with the Euclidean norm of Physlib's pairwise classical gravity
acceleration identifies the scalar input `g_N` of the MOND law with Physlib's reference-frame force.

-/

open scoped Classical in
/-- In Physlib's classical reference frame, the norm of `pairGravityAcceleration` between
non-coincident particles equals `newtonianAcceleration`. -/
lemma norm_pairGravityAcceleration_eq_newtonianAcceleration {d : ℕ}
    {frame : ClassicalMechanics.ReferenceFrame d}
    (G : GravitationalConstant) (particles : Multiset frame.Particle)
    (source target : particles.ToType) (t : ℝ)
    (hne : source.1.pos t ≠ target.1.pos t) :
    ‖ClassicalMechanics.ReferenceFrame.pairGravityAcceleration G.val particles source target t‖ =
      newtonianAcceleration G source.1.mass.val ‖source.1.pos t - target.1.pos t‖ := by
  simp only [ClassicalMechanics.ReferenceFrame.pairGravityAcceleration, newtonianAcceleration,
    norm_smul, Real.norm_eq_abs]
  have hG : 0 < G.val := G.pos
  have hr : 0 < ‖source.1.pos t - target.1.pos t‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hm : 0 ≤ source.1.mass.val := le_of_lt source.1.mass.property
  have hnum : 0 ≤ G.val * source.1.mass.val / ‖source.1.pos t - target.1.pos t‖ ^ 3 := by
    positivity
  rw [abs_of_nonneg hnum]
  have hne0 : ‖source.1.pos t - target.1.pos t‖ ≠ 0 := hr.ne'
  field_simp [hne0]

end MOND

end Modified

end GeneralRelativity
