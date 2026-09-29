/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Geometric.Basic
public import Physlib.SpaceAndTime.Time.Derivatives
/-!
# Geometric trajectories of the harmonic oscillator

## i. Overview

A trajectory of the harmonic oscillator is a time-parametrized curve in the configuration
manifold `Q`. Since this model of `Q` has a single global coordinate valued in
`EuclideanSpace ℝ (Fin 1)`, every geometric trajectory has an associated coordinate curve.

The coordinate diffeomorphism from `Q` to its model space lets smoothness of a geometric
trajectory be tested as ordinary smoothness of its coordinate curve.

## ii. Key results

- `Trajectory` : a curve from `Time` into the configuration manifold.
- `Trajectory.coord` : the global Euclidean coordinate curve of a trajectory.
- `Trajectory.toSpace` : the physical-space position along a trajectory.
- `Trajectory.contMDiff_iff_contDiff_coord` : geometric smoothness of a trajectory is
  equivalent to ordinary smoothness of its coordinate curve.
- `Trajectory.velocity` : the geometric velocity of a trajectory as a tangent vector.
- `Trajectory.velocity_eq_deriv_coord` : in the global coordinate, geometric velocity is
  represented by the time derivative of the coordinate curve.

## iii. Table of contents

- A. The trajectory type and coordinate projection
- B. Smoothness of trajectories
- C. Velocity in the tangent bundle

## iv. References

* Ivo Terek, Introductory Variational Calculus on Manifolds, pages 1-2 (Section 1, Basic definitions
  and examples). [ref: terek_variational_manifolds]
-/

@[expose] public section

namespace ClassicalMechanics

namespace HarmonicOscillator

open scoped Manifold
open Time

/-!
## A. The trajectory type and coordinate projection

A trajectory is a curve in the configuration manifold `Q`, parametrized by `Time`. The
coordinate projection reads the same curve in the chosen global coordinate, while `toSpace`
forgets the manifold structure and returns the corresponding physical-space position.
-/

/-- A trajectory of the oscillator: a curve in the configuration manifold `Q`. -/
abbrev Trajectory := Time → ConfigurationSpace

namespace Trajectory

/-- The coordinate curve of a trajectory: its reading in the global Euclidean coordinate. -/
def coord (γ : Trajectory) : Time → EuclideanSpace ℝ (Fin 1) :=
  fun t => chartAt (EuclideanSpace ℝ (Fin 1)) (γ t) (γ t)

/-- The physical position of the oscillator along a trajectory, over time. -/
def toSpace (γ : Trajectory) : Time → Space 1 := fun t => (γ t).toSpace

lemma coord_apply (γ : Trajectory) (t : Time) : coord γ t = (γ t).val := rfl

/-!
## B. Smoothness of trajectories

Because the global coordinate is a diffeomorphism, composing a trajectory with it preserves
and reflects manifold smoothness. Since both `Time` and the coordinate model are normed
spaces, this manifold-smoothness statement then becomes ordinary `ContDiff` smoothness.
-/

/-- A trajectory is smooth as a curve in `Q` iff its coordinate curve is ordinarily smooth. -/
lemma contMDiff_iff_contDiff_coord {n : WithTop ℕ∞} (γ : Trajectory) :
    ContMDiff 𝓘(ℝ, Time) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) n γ ↔
      ContDiff ℝ n (coord γ) := by
  rw [show coord γ = ConfigurationSpace.valDiffeomorph ∘ γ by rfl]
  rw [← contMDiff_iff_contDiff]
  exact (ConfigurationSpace.valDiffeomorph.contMDiff_diffeomorph_comp_iff
    (m := n) (f := γ) le_top).symm

/-!
## C. Velocity in the tangent bundle

The velocity of a trajectory at time `t` is the tangent vector obtained by differentiating
the curve in the direction of the unit time vector. In this one-chart model, the tangent
space at each configuration is represented by the same Euclidean model space, so the
geometric velocity can be compared with the derivative of the coordinate curve.
-/

/-- The geometric velocity of a trajectory at time `t`: a tangent vector at `γ t`. -/
noncomputable def velocity (γ : Trajectory) (t : Time) :
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (γ t) :=
  mfderiv 𝓘(ℝ, Time) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) γ t
    ((1 : Time) : TangentSpace 𝓘(ℝ, Time) t)

/-- A trajectory is `MDifferentiableAt` a time iff its coordinate curve is ordinarily
differentiable there, since the two differ by the coordinate diffeomorphism. -/
lemma mdifferentiableAt_iff_differentiableAt_coord (γ : Trajectory) (t : Time) :
    MDifferentiableAt 𝓘(ℝ, Time) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) γ t ↔
      DifferentiableAt ℝ (coord γ) t := by
  rw [← mdifferentiableAt_iff_differentiableAt]
  constructor
  · intro hγ
    rw [show coord γ = ConfigurationSpace.valDiffeomorph ∘ γ by rfl]
    exact MDifferentiableAt.comp t
      ((ConfigurationSpace.valDiffeomorph.mdifferentiable WithTop.top_ne_zero).mdifferentiableAt)
      hγ
  · intro hcoord
    have hγ : MDifferentiableAt 𝓘(ℝ, Time) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
        (ConfigurationSpace.valDiffeomorph.symm ∘ coord γ) t :=
      MDifferentiableAt.comp t
        ((ConfigurationSpace.valDiffeomorph.symm.mdifferentiable
          WithTop.top_ne_zero).mdifferentiableAt) hcoord
    convert hγ using 1
    funext s
    exact (ConfigurationSpace.valDiffeomorph.symm_apply_apply (γ s)).symm

/-- A trajectory and its coordinate curve have the same manifold derivative, since they
differ only by the coordinate diffeomorphism. This is the one lemma that unfolds the chart;
every later result uses only the stable `mfderiv`/`fderiv` API. -/
private lemma mfderiv_eq_mfderiv_coord (γ : Trajectory) (t : Time) :
    mfderiv 𝓘(ℝ, Time) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) γ t =
      mfderiv 𝓘(ℝ, Time) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (coord γ) t := by
  by_cases hγ : MDifferentiableAt 𝓘(ℝ, Time) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) γ t
  · have hcoord : MDifferentiableAt 𝓘(ℝ, Time) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
        (coord γ) t :=
      ((mdifferentiableAt_iff_differentiableAt_coord γ t).mp hγ).mdifferentiableAt
    simp [mfderiv, coord, writtenInExtChartAt, hγ, hcoord,
      ConfigurationSpace.valHomeomorphism, ConfigurationSpace.valEquiv, Function.comp_def]
    rfl
  · rw [mfderiv_zero_of_not_mdifferentiableAt hγ,
      mfderiv_zero_of_not_mdifferentiableAt
        (fun h => hγ ((mdifferentiableAt_iff_differentiableAt_coord γ t).mpr
          h.differentiableAt))]
    rfl

/-- In the global coordinate, geometric velocity is represented by the time derivative of the
coordinate curve. -/
lemma velocity_eq_deriv_coord (γ : Trajectory) (t : Time) :
    velocity γ t = ∂ₜ (coord γ) t := by
  rw [velocity, mfderiv_eq_mfderiv_coord]
  exact (Time.deriv_eq_mfderiv (coord γ) t).symm

end Trajectory

end HarmonicOscillator

end ClassicalMechanics
