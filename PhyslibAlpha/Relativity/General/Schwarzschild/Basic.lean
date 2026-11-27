/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import PhyslibAlpha.Relativity.General.Schwarzschild.IncompressibleSphere
public import PhyslibAlpha.Relativity.Metrics.StaticSphericalMetric.Christoffel
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Schwarzschild black hole spacetime

Exterior Schwarzschild black hole structure `SchwarzschildSpacetime`, its radial metric function
`f(r) = 1 - 2M/r`, radial Christoffel symbols, direct coordinate-level Riemann components, and
matching to the exterior of `IncompressibleSphere`.

## i. Overview

Starting from the line element `g = diag(-f, f⁻¹, r², r² sin²θ)` with radial metric function
`f = 1 - 2M/r`, where `M` is the mass of `S : SchwarzschildSpacetime`, this module views the metric
as a `StaticSphericalMetric`, computes radial derivatives of the metric and its static Newtonian
potential `Φ = -M/r`, evaluates the radial Christoffel symbols
(`Γ^t_{tr}`, `Γ^r_{rr}`, `Γ^r_{θθ}`, `Γ^r_{φφ}`), and computes all six independent Riemann
components directly from the metric components.

Note that this module uses the `(-, +, +, +)` signature (`g_tt = -f`), whereas
`IncompressibleSphere.gttOut` stores the positive factor `f = 1 - r_s / r` directly.

## ii. Key results

- `SchwarzschildSpacetime`, `SchwarzschildSpacetime.metricFn`,
  `SchwarzschildSpacetime.toStaticSpherical`, `SchwarzschildSpacetime.toCoordinateMetric`,
  `SchwarzschildSpacetime.metric`, `SchwarzschildSpacetime.metricInv` : Schwarzschild spacetime
  structure, metric function `1 - 2M / r`, and coordinate metric.
- `SchwarzschildSpacetime.ofIncompressibleSphere`,
  `SchwarzschildSpacetime.metricFn_ofIncompressibleSphere`,
  `SchwarzschildSpacetime.metric_tt_ofIncompressibleSphere`,
  `SchwarzschildSpacetime.metric_rr_ofIncompressibleSphere` : exterior matching with
  `IncompressibleSphere`.
- `SchwarzschildSpacetime.christoffelTtr_from_metric`,
  `SchwarzschildSpacetime.christoffelRrr_from_metric`,
  `SchwarzschildSpacetime.christoffelRThetaTheta_from_metric`,
  `SchwarzschildSpacetime.christoffelRPhiPhi_from_metric` : radial Christoffel symbols derived
  from the metric.

The coordinate Riemann, Ricci, scalar, and Einstein tensors are proved in
`Schwarzschild/CoordinateCurvature.lean` from `SchwarzschildSpacetime.toCoordinateMetric`.

## iii. Table of contents

- A. Metric function and radial Christoffel symbols
- B. Exterior matching with the incompressible sphere

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 6 (Sec. 6.1-6.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 23 & Ch. 31.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 7
  (https://arxiv.org/pdf/gr-qc/9712019#page=168). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace Schwarzschild

/-!

## A. Metric function and radial Christoffel symbols

From the Schwarzschild metric function `f = 1 - 2M/r` and diagonal inverse metric
`diag(-f⁻¹, f, r⁻², r⁻² sin⁻²θ)`, differentiating the radial metric components determines the mixed
Christoffel symbols `Γ^t_{tr}` and `Γ^r_{rr}`.

-/

/-- Exterior Schwarzschild black hole spacetime parameterized by geometric mass `M`. -/
structure SchwarzschildSpacetime where
  /-- Geometric mass parameter `M` (`G = c = 1`). -/
  M : ℝ

namespace SchwarzschildSpacetime

/-- The Schwarzschild radial metric function `f(r) = 1 - 2M / r`. -/
noncomputable def metricFn (S : SchwarzschildSpacetime) (r : ℝ) : ℝ := 1 - 2 * S.M / r

/-- Equational form of `SchwarzschildSpacetime.metricFn`. -/
lemma metricFn_eq (S : SchwarzschildSpacetime) (r : ℝ) : S.metricFn r = 1 - 2 * S.M / r := rfl

/-- Clearing the radial denominator gives `r * S.metricFn r = r - 2 S.M`. -/
lemma r_mul_metricFn (S : SchwarzschildSpacetime) (r : ℝ) (hr : r ≠ 0) :
    r * S.metricFn r = r - 2 * S.M := by
  rw [metricFn_eq]
  field_simp

/-- View a Schwarzschild spacetime as a `StaticSphericalMetric` with profile `S.metricFn`. -/
noncomputable def toStaticSpherical (S : SchwarzschildSpacetime) :
    StaticSpherical.StaticSphericalMetric :=
  ⟨S.metricFn⟩

/-- The underlying radial metric function of `S.toStaticSpherical` is `S.metricFn`. -/
@[simp]
lemma toStaticSpherical_metricFn (S : SchwarzschildSpacetime) :
    S.toStaticSpherical.metricFn = S.metricFn := rfl

/-- The Schwarzschild metric as a `CoordinateMetric 4` on the regular chart
`r ≠ 0`, `1 - 2M/r ≠ 0`, `sin θ ≠ 0`. -/
noncomputable def toCoordinateMetric (S : SchwarzschildSpacetime) : CoordinateMetric 4 :=
  S.toStaticSpherical.toCoordinateMetric

/-- The Schwarzschild metric in `(t, r, θ, φ)` coordinates with signature `(-, +, +, +)`. -/
noncomputable def metric (S : SchwarzschildSpacetime) (x : Fin 4 → ℝ) : Tensor2 4 :=
  S.toStaticSpherical.metric x

/-- The inverse of the Schwarzschild metric in `(t, r, θ, φ)` coordinates. -/
noncomputable def metricInv (S : SchwarzschildSpacetime) (x : Fin 4 → ℝ) : Tensor2 4 :=
  S.toStaticSpherical.metricInv x

/-- The covariant field of `S.toCoordinateMetric` is `S.metric`. -/
@[simp] lemma toCoordinateMetric_g (S : SchwarzschildSpacetime) :
    S.toCoordinateMetric.g = S.metric := rfl

/-- The inverse field of `S.toCoordinateMetric` is `S.metricInv`. -/
@[simp] lemma toCoordinateMetric_ginv (S : SchwarzschildSpacetime) :
    S.toCoordinateMetric.ginv = S.metricInv := rfl

/-- The `tt` component of the Schwarzschild metric is `-(1 - 2M/r)`. -/
lemma metric_tt (S : SchwarzschildSpacetime) (x : Fin 4 → ℝ) :
    S.metric x 0 0 = -(1 - 2 * S.M / x 1) := by
  simp [metric, toStaticSpherical, StaticSpherical.StaticSphericalMetric.metric, metricFn]

/-- The static Newtonian potential is `Φ = -M / r`: `g_tt = -(1 + 2Φ)`. -/
lemma metric_tt_potential (S : SchwarzschildSpacetime) (x : Fin 4 → ℝ) :
    S.metric x 0 0 = -(1 + 2 * (-S.M / x 1)) := by
  rw [S.metric_tt]
  ring

/-- First radial derivative of the potential: `Φ' = M / r²`. -/
lemma potential_hasDerivAt (S : SchwarzschildSpacetime) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => -S.M / s) (S.M / r ^ 2) r := by
  have h : HasDerivAt (fun s : ℝ => s⁻¹) (-(r ^ 2)⁻¹) r := hasDerivAt_inv hr
  have h' := h.const_mul (-S.M)
  have hfun : (fun s : ℝ => -S.M / s) = fun s : ℝ => -S.M * s⁻¹ := by
    funext s
    simp [div_eq_mul_inv]
  have hval : -S.M * -(r ^ 2)⁻¹ = S.M / r ^ 2 := by ring
  rw [← hfun, hval] at h'
  exact h'

/-- Second radial derivative of the potential: `Φ'' = -2M / r³`. -/
lemma potential_second_hasDerivAt (S : SchwarzschildSpacetime) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => S.M / s ^ 2) (-2 * S.M / r ^ 3) r := by
  have hnum : HasDerivAt (fun _ : ℝ => S.M) 0 r := hasDerivAt_const r S.M
  have hden : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have h := hnum.div hden (pow_ne_zero 2 hr)
  have hfun : (fun s : ℝ => S.M / s ^ 2) = (fun _ : ℝ => S.M) / fun s : ℝ => s ^ 2 := rfl
  have hval : (0 * r ^ 2 - S.M * (2 * r)) / (r ^ 2) ^ 2 = -2 * S.M / r ^ 3 := by
    have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
    have hr4 : (r ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hr2
    field_simp
    ring
  rw [← hfun, hval] at h
  exact h

/-- The `rr` component of the Schwarzschild metric is `f⁻¹`. -/
lemma metric_rr (S : SchwarzschildSpacetime) (x : Fin 4 → ℝ) :
    S.metric x 1 1 = (S.metricFn (x 1))⁻¹ := by
  simp [metric, toStaticSpherical, StaticSpherical.StaticSphericalMetric.metric, metricFn]

/-- `f ≠ 0` forces `r - 2M ≠ 0` away from `r = 0`. -/
lemma sub_ne_zero_of_ne (S : SchwarzschildSpacetime) (r : ℝ) (hr : r ≠ 0) (hf : S.metricFn r ≠ 0) :
    r - 2 * S.M ≠ 0 := by
  intro h
  apply hf
  rw [metricFn_eq]
  have h1 : 2 * S.M / r = 1 := by
    field_simp
    linarith
  rw [h1]
  ring

/-- Radial derivative of the metric function `f = 1 - 2M/r`: `∂_r f = 2M / r²`. -/
lemma hasDerivAt_metricFn (S : SchwarzschildSpacetime) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt S.metricFn (2 * S.M / r ^ 2) r := by
  have h := HasDerivAt.sub (hasDerivAt_const r (1 : ℝ))
    ((hasDerivAt_inv hr).const_mul (2 * S.M))
  have hfun : S.metricFn = (fun _ : ℝ => 1) - fun s : ℝ => 2 * S.M * s⁻¹ := by
    funext s
    simp [metricFn, div_eq_mul_inv]
  have hval : (0 : ℝ) - 2 * S.M * -(r ^ 2)⁻¹ = 2 * S.M / r ^ 2 := by
    rw [div_eq_mul_inv]
    ring
  rw [← hfun, hval] at h
  exact h

/-- Because `g_tt = -f` depends only on `r`, the formula
`Γ^t_{tr} = (1/2) g^{tt} ∂_r g_{tt}` contracts `g^{tt} = -f⁻¹` against `-∂_r f = -2M/r²`, yielding
`M / (r² f)`. -/
lemma christoffelTtr_from_metric (S : SchwarzschildSpacetime) (r : ℝ) (hf : S.metricFn r ≠ 0) :
    (1 / 2 : ℝ) * (-(S.metricFn r)⁻¹) * (-(2 * S.M / r ^ 2))
      = S.M / (r ^ 2 * S.metricFn r) := by
  field_simp

/-- Radial derivative of `g_rr = f⁻¹`: `∂_r g_rr = -2M / (r - 2M)²`. -/
lemma deriv_grr (S : SchwarzschildSpacetime) (r : ℝ) (hr : r ≠ 0) (hf : S.metricFn r ≠ 0) :
    deriv ((fun s : ℝ => 1 - 2 * S.M / s)⁻¹) r = -(2 * S.M) / (r - 2 * S.M) ^ 2 := by
  have hf' : 1 - 2 * S.M / r ≠ 0 := hf
  have h2 := S.sub_ne_zero_of_ne r hr hf
  have h := (S.hasDerivAt_metricFn r hr).inv hf
  have hfun : (fun s : ℝ => 1 - 2 * S.M / s)⁻¹ = S.metricFn⁻¹ := rfl
  rw [hfun, h.deriv, metricFn_eq]
  field_simp [hf', hr, h2]

/-- Contracting `g^{rr} = f` against the radial derivative `∂_r g_{rr} = ∂_r(f⁻¹) = -2M / (r - 2M)²`
in `Γ^r_{rr} = (1/2) g^{rr} ∂_r g_{rr}` cancels one factor of `f = (r - 2M)/r` to yield
`-M / (r (r - 2M))`. -/
lemma christoffelRrr_from_metric (S : SchwarzschildSpacetime) (r : ℝ) (hr : r ≠ 0)
    (hf : S.metricFn r ≠ 0) :
    (1 / 2 : ℝ) * (S.metricFn r) * (-(2 * S.M) / (r - 2 * S.M) ^ 2)
      = -S.M / (r * (r - 2 * S.M)) := by
  have h2 := S.sub_ne_zero_of_ne r hr hf
  have hr_mul := S.r_mul_metricFn r hr
  field_simp [h2, hr]
  linear_combination -S.M * hr_mul

/-- Radial derivative of `Γ^t_{tr}`: `∂_r Γ^t_{tr} = -2M(r - M) / (r(r - 2M))²`. -/
lemma deriv_christoffelTtr (S : SchwarzschildSpacetime) (r : ℝ) (hr : r ≠ 0)
    (hf : S.metricFn r ≠ 0) :
    deriv (fun s : ℝ => S.M / (s ^ 2 * S.metricFn s)) r
      = -2 * S.M * (r - S.M) / (r * (r - 2 * S.M)) ^ 2 := by
  have hf' : (1 - 2 * S.M / r) ≠ 0 := by simpa [metricFn_eq] using hf
  have h2 := S.sub_ne_zero_of_ne r hr hf
  have hden : HasDerivAt (fun s : ℝ => s ^ 2 * (1 - 2 * S.M / s)) (2 * r - 2 * S.M) r := by
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    have h2' : HasDerivAt (fun s : ℝ => 1 - 2 * S.M / s) (2 * S.M / r ^ 2) r :=
      S.hasDerivAt_metricFn r hr
    have hm := h1.mul h2'
    have hval : 2 * r * (1 - 2 * S.M / r) + r ^ 2 * (2 * S.M / r ^ 2) = 2 * r - 2 * S.M := by
      field_simp
      ring
    rw [hval] at hm
    exact hm
  have hdenne : r ^ 2 * (1 - 2 * S.M / r) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hr) hf'
  have h := HasDerivAt.div (hasDerivAt_const r S.M) hden hdenne
  have hfun : (fun s : ℝ => S.M / (s ^ 2 * S.metricFn s))
      = (fun _ : ℝ => S.M) / fun s : ℝ => s ^ 2 * (1 - 2 * S.M / s) := by
    funext s
    simp [metricFn_eq]
  rw [hfun, h.deriv]
  field_simp
  ring

/-!

## B. Exterior matching with the incompressible sphere

Matching the exterior mass `M = r_s / 2` to the constant-density sphere connects the point-mass
Schwarzschild geometry to the uniform-density stellar interior. The Riemann, Ricci, scalar, and
Einstein tensors are computed from the coordinate metric in `Schwarzschild/CoordinateCurvature.lean`.

-/

/-- Exterior Schwarzschild spacetime matched to an `IncompressibleSphere` (`M = r_s / 2`). -/
noncomputable def ofIncompressibleSphere (I : IncompressibleSphere) : SchwarzschildSpacetime :=
  ⟨I.rs / 2⟩

/-- With `M = r_s / 2`, the Schwarzschild metric function equals the exterior `g_tt` factor of the
incompressible fluid sphere, `1 - r_s / r`. -/
lemma metricFn_ofIncompressibleSphere (I : IncompressibleSphere) (r : ℝ) :
    (ofIncompressibleSphere I).metricFn r = I.gttOut r := by
  simp only [ofIncompressibleSphere, metricFn, IncompressibleSphere.gttOut]
  ring

/-- The Schwarzschild `tt` metric component is minus the incompressible-sphere exterior `g_tt`
factor, reflecting the `(-, +, +, +)` signature used here. -/
lemma metric_tt_ofIncompressibleSphere (I : IncompressibleSphere) (x : Fin 4 → ℝ) :
    (ofIncompressibleSphere I).metric x 0 0 = -I.gttOut (x 1) := by
  rw [metric_tt, ← metricFn_ofIncompressibleSphere]
  rfl

/-- The Schwarzschild `rr` metric component agrees with the incompressible-sphere exterior
`g_rr`. -/
lemma metric_rr_ofIncompressibleSphere (I : IncompressibleSphere) (x : Fin 4 → ℝ) :
    (ofIncompressibleSphere I).metric x 1 1 = I.grrOut (x 1) := by
  rw [metric_rr, metricFn_ofIncompressibleSphere]
  simp [IncompressibleSphere.grrOut, IncompressibleSphere.gttOut]

end SchwarzschildSpacetime

end Schwarzschild

end GeneralRelativity
