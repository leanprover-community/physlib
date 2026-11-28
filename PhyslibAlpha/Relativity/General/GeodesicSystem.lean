/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.ODE.ExistUnique

/-!

# The geodesic Cauchy problem

Local existence and uniqueness for the geodesic equation via Picard–Lindelöf.

## i. Overview

On a local coordinate chart `E` modeling spacetime positions and tangent velocities, a geodesic
connection `Γ` governs the free-fall equation of motion `γ'' = -Γ(γ)(γ', γ')`, encoded in
`GeodesicSystem E`. Rewriting this second-order trajectory law as a first-order autonomous flow
`G.field z = (z.2, G.accel z.1 z.2)` on `(position, velocity)` phase space shows that smooth (`C¹`)
Christoffel symbols generate unique local particle trajectories from any initial position and
velocity `(x₀, v₀)` via the Picard–Lindelöf theorem, reducing to unaccelerated straight-line motion
`t ↦ x₀ + t • v₀` when the connection vanishes (`GeodesicSystem.flat`).

## ii. Key results

- `Christoffel`, `GeodesicSystem`, `GeodesicSystem.accel`, `GeodesicSystem.field`, `IsGeodesic` :
  coordinate connection field, geodesic system, phase-space flow, and free-fall predicate.
- `contDiffAt_geodesicField`, `geodesic_ivp_exists` : local existence of a trajectory on some
  proper-time interval `(-ε, ε)` for smooth (`C¹`) Christoffel symbols.
- `geodesic_ivp_exists_curve` : `IsGeodesic` position-and-velocity form of local existence.
- `geodesic_ivp_unique`, `geodesic_ivp_unique_curve` : uniqueness of free-fall trajectories on
  `[a, b]` within a bounded region of phase space where `G.field` is Lipschitz, in phase-space and
  `IsGeodesic` form.
- `GeodesicSystem.flat`, `geodesicField_zero`, `flat_geodesic` : flat geodesic system and inertial
  straight-line trajectories.

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

On a local coordinate patch `E`, the Christoffel symbols stored in a `GeodesicSystem E` act
quadratically on the tangent velocity `v` to determine the gravitational acceleration `-Γ(x)(v, v)`,
casting the second-order geodesic equation as a first-order flow on position–velocity phase space.

-/

/-- Christoffel symbols on a local coordinate chart `E`, coupling pairs of tangent-velocity vectors
quadratically into gravitational acceleration. -/
abbrev Christoffel (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E → E →L[ℝ] E →L[ℝ] E

/-- A geodesic system on a local coordinate chart `E`, carrying its Christoffel connection field. -/
structure GeodesicSystem (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- Christoffel symbols determining the geodesic acceleration `-Γ(x)(v, v)`. -/
  christoffel : Christoffel E

/-- Geodesic acceleration `-G.christoffel x v v` of a `GeodesicSystem`. -/
def GeodesicSystem.accel (G : GeodesicSystem E) (x v : E) : E :=
  -G.christoffel x v v

/-- First-order phase-space vector field `z ↦ (z.2, G.accel z.1 z.2)` of a `GeodesicSystem`. -/
def GeodesicSystem.field (G : GeodesicSystem E) : E × E → E × E :=
  fun z => (z.2, G.accel z.1 z.2)

/-- Predicate asserting that `(γ, w)` solves the geodesic equation of `G` on a parameter set `s`. -/
def IsGeodesic (G : GeodesicSystem E) (s : Set ℝ) (γ w : ℝ → E) : Prop :=
  ∀ t ∈ s, HasDerivAt γ (w t) t ∧ HasDerivAt w (G.accel (γ t) (w t)) t

/-- Evaluation of `G.field` on a phase-space point `(x, v)`. -/
@[simp]
lemma geodesicField_apply (G : GeodesicSystem E) (x v : E) :
    G.field (x, v) = (v, G.accel x v) := rfl

private lemma geodesicField_eq_fun (G : GeodesicSystem E) :
    G.field = fun z => (z.2, -G.christoffel z.1 z.2 z.2) := rfl

private lemma contDiffAt_geodesicField_of_fun (Γ : E → E →L[ℝ] E →L[ℝ] E) {x₀ v₀ : E}
    (hΓ : ContDiffAt ℝ 1 Γ x₀) :
    ContDiffAt ℝ 1 (fun z : E × E => (z.2, -Γ z.1 z.2 z.2)) (x₀, v₀) := by
  fun_prop

/-- Smooth (`C¹`) variation of `G.christoffel` ensures the phase-space geodesic flow `G.field` is
`C¹` and thus locally well-posed for particle trajectories. -/
lemma contDiffAt_geodesicField (G : GeodesicSystem E) {x₀ v₀ : E}
    (hG : ContDiffAt ℝ 1 G.christoffel x₀) :
    ContDiffAt ℝ 1 G.field (x₀, v₀) := by
  rw [geodesicField_eq_fun]
  exact contDiffAt_geodesicField_of_fun G.christoffel hG

/-!

## B. Local existence and uniqueness

Because smooth Christoffel symbols give a locally Lipschitz phase-space flow `G.field`, initial
position and velocity uniquely fix the freely falling particle trajectory over short
affine-parameter intervals.

-/

/-- Local existence for the geodesic Cauchy problem: given `C¹` Christoffel symbols on `G`, every
pair of initial position and velocity `(x₀, v₀)` generates a geodesic on an open interval
`(-ε, ε)`. -/
lemma geodesic_ivp_exists [CompleteSpace E] (G : GeodesicSystem E)
    (hG : ContDiff ℝ 1 G.christoffel) (x₀ v₀ : E) :
    ∃ ε > 0, ∃ z : ℝ → E × E, z 0 = (x₀, v₀) ∧
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (fun s => (z s).1) (z t).2 t ∧
        HasDerivAt (fun s => (z s).2) (G.accel (z t).1 (z t).2) t := by
  have hf : ContDiffAt ℝ 1 G.field (x₀, v₀) :=
    contDiffAt_geodesicField G hG.contDiffAt
  obtain ⟨r, hr, ε, hε, H⟩ :=
    hf.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
  obtain ⟨z, hz0, hz⟩ := H (x₀, v₀) (mem_closedBall_self (le_of_lt hr))
  refine ⟨ε, hε, z, hz0, fun t ht => ?_⟩
  have h := hz t (by simpa using ht)
  exact ⟨(ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t h,
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t h⟩

/-- Curve-and-velocity form of local existence for the geodesic Cauchy problem in `IsGeodesic`
form. -/
lemma geodesic_ivp_exists_curve [CompleteSpace E] (G : GeodesicSystem E)
    (hG : ContDiff ℝ 1 G.christoffel) (x₀ v₀ : E) :
    ∃ ε > 0, ∃ γ w : ℝ → E, γ 0 = x₀ ∧ w 0 = v₀ ∧ IsGeodesic G (Ioo (-ε) ε) γ w := by
  obtain ⟨ε, hε, z, hz0, hz⟩ := geodesic_ivp_exists G hG x₀ v₀
  refine ⟨ε, hε, fun t => (z t).1, fun t => (z t).2, ?_, ?_, fun t ht => hz t ht⟩
  · simpa using congrArg Prod.fst hz0
  · simpa using congrArg Prod.snd hz0

/-- Uniqueness for the geodesic Cauchy problem: two free-fall trajectories of `G` passing through
the same event and velocity at affine parameter `t₀ ∈ (a, b)` coincide across `[a, b]` as long as
they remain in a phase-space neighborhood where `G.field` is `K`-Lipschitz. -/
lemma geodesic_ivp_unique (G : GeodesicSystem E) {K : NNReal} {a b t₀ : ℝ}
    {c : E × E} {R : ℝ}
    (hLip : ∀ t ∈ Ioo a b, LipschitzOnWith K G.field (closedBall c R))
    (ht : t₀ ∈ Ioo a b) {z₁ z₂ : ℝ → E × E}
    (h₁ : ContinuousOn z₁ (Icc a b))
    (h₁' : ∀ t ∈ Ioo a b, HasDerivAt z₁ (G.field (z₁ t)) t)
    (h₁s : ∀ t ∈ Ioo a b, z₁ t ∈ closedBall c R)
    (h₂ : ContinuousOn z₂ (Icc a b))
    (h₂' : ∀ t ∈ Ioo a b, HasDerivAt z₂ (G.field (z₂ t)) t)
    (h₂s : ∀ t ∈ Ioo a b, z₂ t ∈ closedBall c R)
    (h₀ : z₁ t₀ = z₂ t₀) : EqOn z₁ z₂ (Icc a b) :=
  ODE_solution_unique_of_mem_Icc (v := fun _ => G.field)
    (s := fun _ => closedBall c R) hLip ht h₁ h₁' h₁s h₂ h₂' h₂s h₀

/-- Uniqueness of the geodesic Cauchy problem stated directly with `IsGeodesic`: two free-fall
trajectories `(γ, w)` with the same event and velocity at `t₀` coincide on `[a, b]` whenever their
phase-space paths stay in a region where `G.field` is `K`-Lipschitz. -/
lemma geodesic_ivp_unique_curve (G : GeodesicSystem E) {K : NNReal} {a b t₀ : ℝ}
    {c : E × E} {R : ℝ}
    (hLip : ∀ t ∈ Ioo a b, LipschitzOnWith K G.field (closedBall c R))
    (ht : t₀ ∈ Ioo a b) {γ₁ w₁ γ₂ w₂ : ℝ → E}
    (h₁c : ContinuousOn (fun t => (γ₁ t, w₁ t)) (Icc a b))
    (h₁ : IsGeodesic G (Ioo a b) γ₁ w₁)
    (h₁s : ∀ t ∈ Ioo a b, (γ₁ t, w₁ t) ∈ closedBall c R)
    (h₂c : ContinuousOn (fun t => (γ₂ t, w₂ t)) (Icc a b))
    (h₂ : IsGeodesic G (Ioo a b) γ₂ w₂)
    (h₂s : ∀ t ∈ Ioo a b, (γ₂ t, w₂ t) ∈ closedBall c R)
    (h₀ : (γ₁ t₀, w₁ t₀) = (γ₂ t₀, w₂ t₀)) : EqOn γ₁ γ₂ (Icc a b) := by
  have hpair : EqOn (fun t => (γ₁ t, w₁ t)) (fun t => (γ₂ t, w₂ t)) (Icc a b) :=
    geodesic_ivp_unique G hLip ht h₁c
      (fun t ht => by
        simpa [GeodesicSystem.field] using
          HasDerivAt.prodMk (h₁ t ht).1 (h₁ t ht).2)
      h₁s h₂c
      (fun t ht => by
        simpa [GeodesicSystem.field] using
          HasDerivAt.prodMk (h₂ t ht).1 (h₂ t ht).2)
      h₂s h₀
  exact fun t ht => congrArg Prod.fst (hpair ht)

/-!

## C. Flat-space straight lines

In Minkowski spacetime or any inertial chart (`Γ = 0`, expressed as `GeodesicSystem.flat`), free
particles experience no gravitational acceleration and follow unaccelerated straight worldlines
`x₀ + t • v₀`.

-/

/-- Flat inertial geodesic system with identically vanishing Christoffel symbols. -/
noncomputable def GeodesicSystem.flat : GeodesicSystem E where
  christoffel := fun _ => 0

/-- In flat space (`GeodesicSystem.flat`), the geodesic vector field reduces to `(v, 0)`. -/
lemma geodesicField_zero (x v : E) :
    (GeodesicSystem.flat (E := E)).field (x, v) = (v, 0) := by
  simp [GeodesicSystem.field, GeodesicSystem.accel, GeodesicSystem.flat]

/-- In flat space, `t ↦ x₀ + t • v₀` with constant velocity `v₀` is a global geodesic for
`GeodesicSystem.flat`. -/
lemma flat_geodesic (x₀ v₀ : E) :
    IsGeodesic (GeodesicSystem.flat (E := E)) Set.univ
      (fun s : ℝ => x₀ + s • v₀) (fun _ => v₀) := by
  intro t _
  refine ⟨?_, ?_⟩
  · have hid : HasDerivAt (fun s : ℝ => s) (1 : ℝ) t := hasDerivAt_id t
    simpa using (hid.smul_const v₀).const_add x₀
  · simp [GeodesicSystem.accel, GeodesicSystem.flat, hasDerivAt_const]

end GeneralRelativity
