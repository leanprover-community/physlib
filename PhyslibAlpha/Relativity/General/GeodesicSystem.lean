/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.ODE.ExistUnique

/-!

# The geodesic Cauchy problem

Local existence and uniqueness for the geodesic equation via Picard–Lindelöf.

## i. Overview

On a local coordinate chart `E` modeling spacetime positions and tangent velocities, a geodesic
connection `Γ` governs the free-fall equation of motion `γ'' = -Γ(γ)(γ', γ')`, bundled in
`GeodesicSystem E`. Rewriting this second-order trajectory law as a first-order autonomous flow
`z' = (z.2, -Γ(z.1)(z.2, z.2))` on `(position, velocity)` phase space shows that smooth (`C¹`)
Christoffel symbols generate unique local particle trajectories from any initial position and
velocity `(x₀, v₀)` via the Picard–Lindelöf theorem, reducing to unaccelerated straight-line motion
`t ↦ x₀ + t • v₀` when the connection vanishes (`Γ = 0`).

## ii. Key results

- `Christoffel`, `GeodesicSystem`, `IsGeodesic` : coordinate connection field, geodesic system
  bundle, and free-fall trajectory predicate.
- `geodesicAccel`, `geodesicField` : geodesic acceleration and phase-space equations of motion on
  `E × E`.
- `geodesic_ivp_exists` : local existence of a particle trajectory on some proper-time interval
  `(-ε, ε)` for smooth (`C¹`) Christoffel symbols.
- `geodesic_ivp_exists_curve` : position-and-velocity form of local geodesic existence.
- `geodesic_ivp_unique` : uniqueness of free-fall trajectories on `[a, b]` within a bounded region
  of phase space where the geodesic flow is Lipschitz.
- `flat_geodesic` : inertial straight-line trajectories in flat spacetime (`Γ = 0`).

## iii. Table of contents

- A. The geodesic system and vector field
- B. Local existence and uniqueness
- C. Flat-space straight lines

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 3 (Sec. 3.3). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 13.
  [ref: mtw_1973_gravitation]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity* (1983), Ch. 3.
  [ref: oneill_1983_semi_riemannian]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 3
  (https://arxiv.org/pdf/gr-qc/9712019#page=69). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-!

## A. The geodesic system and vector field

On a local coordinate patch `E`, the Christoffel symbols act quadratically on the tangent velocity
`v` to determine the gravitational acceleration `-Γ(x)(v, v)`, casting the second-order geodesic
equation as a first-order flow on position–velocity phase space.

-/

/-- Christoffel symbols on a local coordinate chart `E`, coupling pairs of tangent-velocity vectors
quadratically into gravitational acceleration. -/
abbrev Christoffel (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E → E →L[ℝ] E →L[ℝ] E

/-- A geodesic system on a local coordinate chart `E`, carrying its Christoffel connection field. -/
structure GeodesicSystem (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- Christoffel symbols determining the geodesic acceleration `-Γ(x)(v, v)`. -/
  christoffel : Christoffel E

/-- Geodesic acceleration `-Γ(x)(v, v)`. -/
def geodesicAccel (Γ : Christoffel E) (x v : E) : E := - Γ x v v

/-- The first-order form of the geodesic equation on state `(position, velocity)`. -/
def geodesicField (Γ : Christoffel E) : E × E → E × E :=
  fun z => (z.2, geodesicAccel Γ z.1 z.2)

/-- Geodesic acceleration of a `GeodesicSystem`. -/
def GeodesicSystem.accel (G : GeodesicSystem E) (x v : E) : E :=
  geodesicAccel G.christoffel x v

/-- First-order phase-space vector field of a `GeodesicSystem`. -/
def GeodesicSystem.field (G : GeodesicSystem E) : E × E → E × E :=
  geodesicField G.christoffel

/-- Predicate asserting that `(γ, w)` solves the geodesic equation on an interval `s`. -/
def IsGeodesic (G : GeodesicSystem E) (s : Set ℝ) (γ w : ℝ → E) : Prop :=
  ∀ t ∈ s, HasDerivAt γ (w t) t ∧ HasDerivAt w (G.accel (γ t) (w t)) t

/-- Evaluation of `geodesicField` on a pair `(x, v)`. -/
@[simp]
lemma geodesicField_apply (Γ : Christoffel E) (x v : E) :
    geodesicField Γ (x, v) = (v, geodesicAccel Γ x v) := rfl

private lemma geodesicField_eq_fun (Γ : Christoffel E) :
    geodesicField Γ = fun z => (z.2, -Γ z.1 z.2 z.2) := rfl

/-- Smooth (`C¹`) variation of the Christoffel symbols ensures the phase-space geodesic flow is `C¹`
and thus locally well-posed for particle trajectories. -/
lemma contDiffAt_geodesicField (Γ : E → E →L[ℝ] E →L[ℝ] E) {x₀ v₀ : E}
    (hΓ : ContDiffAt ℝ 1 Γ x₀) :
    ContDiffAt ℝ 1 (geodesicField Γ) (x₀, v₀) := by
  rw [geodesicField_eq_fun]
  fun_prop

/-!

## B. Local existence and uniqueness

Because smooth Christoffel symbols give a locally Lipschitz phase-space flow, initial position and
velocity uniquely fix the freely falling particle trajectory over short affine-parameter intervals.

-/

/-- Local existence for the geodesic Cauchy problem: given `C¹` Christoffel symbols, every pair
of initial position and velocity generates a geodesic on an open interval `(-ε, ε)`. -/
lemma geodesic_ivp_exists [CompleteSpace E] (Γ : Christoffel E) (hΓ : ContDiff ℝ 1 Γ)
    (x₀ v₀ : E) :
    ∃ ε > 0, ∃ z : ℝ → E × E, z 0 = (x₀, v₀) ∧
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (fun s => (z s).1) (z t).2 t ∧
        HasDerivAt (fun s => (z s).2) (geodesicAccel Γ (z t).1 (z t).2) t := by
  have hf : ContDiffAt ℝ 1 (geodesicField Γ) (x₀, v₀) :=
    contDiffAt_geodesicField Γ hΓ.contDiffAt
  obtain ⟨r, hr, ε, hε, H⟩ :=
    hf.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
  obtain ⟨z, hz0, hz⟩ := H (x₀, v₀) (mem_closedBall_self (le_of_lt hr))
  refine ⟨ε, hε, z, hz0, fun t ht => ?_⟩
  have h := hz t (by simpa using ht)
  exact ⟨(ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t h,
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t h⟩

/-- Curve-and-velocity form of local existence for the geodesic Cauchy problem. -/
lemma geodesic_ivp_exists_curve [CompleteSpace E] (Γ : Christoffel E) (hΓ : ContDiff ℝ 1 Γ)
    (x₀ v₀ : E) :
    ∃ ε > 0, ∃ γ w : ℝ → E, γ 0 = x₀ ∧ w 0 = v₀ ∧
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt γ (w t) t ∧
        HasDerivAt w (geodesicAccel Γ (γ t) (w t)) t := by
  obtain ⟨ε, hε, z, hz0, hz⟩ := geodesic_ivp_exists Γ hΓ x₀ v₀
  refine ⟨ε, hε, fun t => (z t).1, fun t => (z t).2, ?_, ?_, fun t ht => hz t ht⟩
  · simpa using congrArg Prod.fst hz0
  · simpa using congrArg Prod.snd hz0

/-- Uniqueness for the geodesic Cauchy problem: two free-fall trajectories passing through the
same event and velocity at affine parameter `t₀ ∈ (a, b)` coincide across `[a, b]` as long as they
remain in a phase-space neighborhood where the gravitational force field is `K`-Lipschitz. -/
lemma geodesic_ivp_unique (Γ : Christoffel E) {K : NNReal} {a b t₀ : ℝ}
    {c : E × E} {R : ℝ}
    (hLip : ∀ t ∈ Ioo a b, LipschitzOnWith K (geodesicField Γ) (closedBall c R))
    (ht : t₀ ∈ Ioo a b) {z₁ z₂ : ℝ → E × E}
    (h₁ : ContinuousOn z₁ (Icc a b))
    (h₁' : ∀ t ∈ Ioo a b, HasDerivAt z₁ (geodesicField Γ (z₁ t)) t)
    (h₁s : ∀ t ∈ Ioo a b, z₁ t ∈ closedBall c R)
    (h₂ : ContinuousOn z₂ (Icc a b))
    (h₂' : ∀ t ∈ Ioo a b, HasDerivAt z₂ (geodesicField Γ (z₂ t)) t)
    (h₂s : ∀ t ∈ Ioo a b, z₂ t ∈ closedBall c R)
    (h₀ : z₁ t₀ = z₂ t₀) : EqOn z₁ z₂ (Icc a b) :=
  ODE_solution_unique_of_mem_Icc (v := fun _ => geodesicField Γ)
    (s := fun _ => closedBall c R) hLip ht h₁ h₁' h₁s h₂ h₂' h₂s h₀

/-!

## C. Flat-space straight lines

In Minkowski spacetime or any inertial chart (`Γ = 0`), free particles experience no gravitational
acceleration and follow unaccelerated straight worldlines `x₀ + t • v₀`.

-/

/-- In flat space (`Γ = 0`) the geodesic vector field reduces to `(v, 0)`. -/
lemma geodesicField_zero (x v : E) :
    geodesicField (fun _ : E => 0) (x, v) = (v, 0) := by
  simp [geodesicField, geodesicAccel]

/-- In flat space, `t ↦ x₀ + t • v₀` has constant velocity `v₀` and solves `γ'' = 0`. -/
lemma flat_geodesic (x₀ v₀ : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x₀ + s • v₀) v₀ t ∧
      HasDerivAt (fun _ : ℝ => v₀) 0 t := by
  refine ⟨?_, hasDerivAt_const t v₀⟩
  have hid : HasDerivAt (fun s : ℝ => s) (1 : ℝ) t := hasDerivAt_id t
  simpa using (hid.smul_const v₀).const_add x₀

end GeneralRelativity
