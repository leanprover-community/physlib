/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Dynamics.KeplerClock

/-!
# Time derivatives of the Hohmann ellipse

Kepler time determines the velocity and acceleration.

## i. Overview

The inverse Kepler clock supplies the anomaly rate. Differentiating the Cartesian coordinates
yields the velocity and then an acceleration parallel to the displacement.

## ii. Key results

- `hasDerivAt_velocity` gives the main result of this module.

## iii. Table of contents

- A. Differentiation along the ellipse

## iv. References

- [ref: hohmann_jpl_orbital_mechanics] describes the Hohmann ellipse and its apses.
-/

@[expose] public noncomputable section

namespace ClassicalMechanics.HohmannTransfer

/-!
## A. Differentiation along the ellipse
-/

/-- The position on the transfer ellipse at the given physical time. -/
def position (p : Parameters) (t : ℝ) : ℂ := ellipse p (anomaly p t)
/-- The velocity on the transfer ellipse at a given physical time. -/
def velocity (p : Parameters) (t : ℝ) : ℂ := velocityAtAnomaly p (anomaly p t)

lemma hasDerivAt_D (p : Parameters) (u : ℝ) :
    HasDerivAt (D p) (p.e*Real.sin u) u := by
  convert (hasDerivAt_const u (1:ℝ)).sub
    ((Real.hasDerivAt_cos u).const_mul p.e) using 1 <;> first | rfl | simp
lemma hasDerivAt_position (p : Parameters) (t : ℝ) :
    HasDerivAt (position p) (velocity p t) t := by
  have hu := hasDerivAt_anomaly p t
  have hx := (hu.cos.sub_const p.e).const_mul p.a
  have hy := hu.sin.const_mul p.b
  convert pack_deriv hx hy using 1
  · rfl
  · apply Complex.ext <;>
      simp [velocity, velocityAtAnomaly, pack] <;> ring
lemma hasDerivAt_velocityAtAnomaly_x (p : Parameters) (u : ℝ) :
    HasDerivAt (fun s => (velocityAtAnomaly p s).re)
      (-p.a*p.n*(Real.cos u-p.e)/(D p u)^2) u := by
  have hnum := (Real.hasDerivAt_sin u).const_mul (-p.a*p.n)
  have h := hnum.div (hasDerivAt_D p u) (D_ne p u)
  convert h using 1
  · rfl
  · apply (div_left_inj' (pow_ne_zero 2 (D_ne p u))).2
    unfold D
    nlinarith [congrArg (fun x : ℝ => p.a*p.n*p.e*x)
      (Real.sin_sq_add_cos_sq u)]
lemma hasDerivAt_velocityAtAnomaly_y (p : Parameters) (u : ℝ) :
    HasDerivAt (fun s => (velocityAtAnomaly p s).im)
      (-p.b*p.n*Real.sin u/(D p u)^2) u := by
  have hnum := (Real.hasDerivAt_cos u).const_mul (p.b*p.n)
  have h := hnum.div (hasDerivAt_D p u) (D_ne p u)
  convert h using 1
  · rfl
  · apply (div_left_inj' (pow_ne_zero 2 (D_ne p u))).2
    unfold D
    ring
lemma hasDerivAt_velocity (p : Parameters) (t : ℝ) :
    HasDerivAt (velocity p)
      (-(p.n^2/(D p (anomaly p t))^3) • position p t) t := by
  have hx := (hasDerivAt_velocityAtAnomaly_x p (anomaly p t)).comp t
    (hasDerivAt_anomaly p t)
  have hy := (hasDerivAt_velocityAtAnomaly_y p (anomaly p t)).comp t
    (hasDerivAt_anomaly p t)
  convert pack_deriv hx hy using 1
  · rfl
  · rw [position, ellipse, pack_smul]
    apply Complex.ext <;>
      simp only [pack_re, pack_im] <;>
      field_simp [D_ne p (anomaly p t)]
lemma deriv_position (p : Parameters) : deriv (position p) = velocity p := by
  funext t
  exact (hasDerivAt_position p t).deriv
lemma position_continuous (p : Parameters) : Continuous (position p) :=
  continuous_iff_continuousAt.2 (fun t => (hasDerivAt_position p t).continuousAt)
lemma velocity_continuous (p : Parameters) : Continuous (velocity p) :=
  continuous_iff_continuousAt.2 (fun t => (hasDerivAt_velocity p t).continuousAt)

end ClassicalMechanics.HohmannTransfer
