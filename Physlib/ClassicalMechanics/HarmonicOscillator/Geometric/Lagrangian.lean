/-
Copyright (c) 2026 Robert Forrest. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Forrest
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Geometric.KineticEnergy
public import Physlib.ClassicalMechanics.HarmonicOscillator.Geometric.PotentialEnergy

/-!
# Geometric Lagrangian of the harmonic oscillator

The oscillator Lagrangian is its kinetic energy minus its spring potential energy.

## i. Overview

At a configuration `q` with tangent velocity `v`, the mass metric determines the kinetic
energy and the displacement from equilibrium determines the spring potential energy.

## ii. Key results

- `geometricLagrangian` gives kinetic energy minus spring potential energy at a tangent vector.
- `geometricLagrangian_eq_lagrangian` identifies it with the coordinate Lagrangian at every time.
- `contMDiff_geometricLagrangian` establishes smoothness on the tangent bundle.

## iii. Table of contents

- A. Geometric Lagrangian

## iv. References

* See `Physlib.ClassicalMechanics.HarmonicOscillator.Basic` for the coordinate Lagrangian.
-/

@[expose] public section

namespace ClassicalMechanics.HarmonicOscillator

open scoped Manifold ContDiff

/-!
## A. Geometric Lagrangian
-/

/-- The kinetic energy of the tangent velocity `v` minus the spring potential energy at `q`. -/
noncomputable def geometricLagrangian
    (S : HarmonicOscillator) (q : ConfigurationSpace)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q) : ℝ :=
  geometricKineticEnergy S q v - geometricPotentialEnergy S q

/-- In global position and velocity coordinates, the geometric Lagrangian agrees with the
oscillator's coordinate Lagrangian at every time `t`. -/
lemma geometricLagrangian_eq_lagrangian
    (S : HarmonicOscillator) (q : ConfigurationSpace)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q)
    (t : Time) :
    S.geometricLagrangian q v = S.lagrangian t q.val (tangentCoord q v) := by
  unfold geometricLagrangian lagrangian
  rw [geometricPotentialEnergy_eq_potentialEnergy, geometricKineticEnergy_massMetric_eq]

/-- The geometric Lagrangian is smooth on the tangent bundle of the configuration space. -/
lemma contMDiff_geometricLagrangian
    (S : HarmonicOscillator) :
    ContMDiff (𝓡 1).tangent 𝓘(ℝ, ℝ) ∞
      (fun p : TangentBundle (𝓡 1) ConfigurationSpace =>
        S.geometricLagrangian p.1 p.2) := by
  have hL : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) =>
      S.lagrangian 0 p.1 p.2) :=
    (S.contDiff_lagrangian ∞).comp ((contDiff_const (c := (0 : Time))).prodMk contDiff_id)
  exact (hL.contMDiff.comp contMDiff_tangentCoord).congr
    (fun p => geometricLagrangian_eq_lagrangian S p.proj p.snd 0)

end ClassicalMechanics.HarmonicOscillator
