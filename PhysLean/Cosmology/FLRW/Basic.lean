/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luis Gabriel C. Bariuan, Joseph Tooby-Smith
-/
module

public import PhysLean.SpaceAndTime.Space.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
/-!

# The Friedmann-Lemaître-Robertson-Walker metric

Parts of this file is currently informal or semiformal.

-/

@[expose] public section

open Filter
open scoped Topology

namespace Cosmology

/-- The inductive type with three constructors:
- `Spherical (k : ℝ)`
- `Flat`
- `Saddle (k : ℝ)`
-/
inductive SpatialGeometry : Type where
  | Spherical (k : ℝ) (h : k < 0)
  | Flat
  | Saddle (k : ℝ) (h : k > 0)

namespace SpatialGeometry

/-- For `s` corresponding to
- `Spherical k`, `S s r = k * sin (r / k)`
- `Flat`, `S s r = r`,
- `Saddle k`, `S s r = k * sinh (r / k)`.
-/
noncomputable def S (s : SpatialGeometry) : ℝ → ℝ :=
  fun r =>
    match s with
    | SpatialGeometry.Spherical k _ => k * Real.sin (r / k)
    | SpatialGeometry.Flat => r
    | SpatialGeometry.Saddle k _ => k * Real.sinh (r / k)

/-- The limit of `S (Saddle k) r` as `k → ∞` is equal to `S (Flat) r`.
First show that `k * sinh(r / k) = sinh(r / k) / (1 / k)` pointwise. -/
lemma mul_sinh_as_div (r k : ℝ) :
    k * Real.sinh (r / k) = Real.sinh (r / k) / (1 / k) := by field_simp

/-- First, show that limit of `sinh(r * x) / x` is r at the limit x goes to zero.
Then the next theorem will address the rewrite using Filter.Tendsto.comp -/
lemma tendsto_sinh_rx_over_x (r : ℝ) :
    Tendsto (fun x : ℝ => Real.sinh (r * x) / x) (𝓝[≠] 0) (𝓝 r) := by
  simpa [div_eq_inv_mul] using HasDerivAt.tendsto_slope_zero
    (HasDerivAt.sinh (HasDerivAt.const_mul r (hasDerivAt_id 0)))

lemma limit_S_saddle (r : ℝ) :
    Tendsto (fun k : ℝ => k * Real.sinh (r / k)) atTop (𝓝 r) := by
  suffices h_sinh_y : Tendsto (fun y => Real.sinh (r * y) / y)
    (map (fun k => 1 / k) atTop) (𝓝 r) by
      exact h_sinh_y.congr fun x => by simp [div_eq_mul_inv, mul_comm]
  have h_deriv : HasDerivAt (fun y => Real.sinh (r * y)) r 0 := by
    simpa using HasDerivAt.sinh (HasDerivAt.const_mul r (hasDerivAt_id 0))
  simpa [div_eq_inv_mul] using h_deriv.tendsto_slope_zero_right

/-- The limit of `S (Sphere k) r` as `k → ∞` is equal to `S (Flat) r`.
First show that `k * sinh(r / k) = sin(r / k) / (1 / k)` pointwise. -/
lemma mul_sin_as_div (r k : ℝ) :
    k * Real.sin (r / k) = Real.sin (r / k) / (1 / k) := by field_simp

/-- First, show that limit of `sin(r * x) / x` is r at the limit x goes to zero.
Then the next theorem will address the rewrite using Filter.Tendsto.comp -/
lemma tendsto_sin_rx_over_x (r : ℝ) :
    Tendsto (fun x : ℝ => Real.sin (r * x) / x) (𝓝[≠] 0) (𝓝 r) := by
  simpa [div_eq_inv_mul] using HasDerivAt.tendsto_slope_zero
    (HasDerivAt.sin (HasDerivAt.const_mul r (hasDerivAt_id 0)))

lemma limit_S_sphere(r : ℝ) :
    Tendsto (fun k : ℝ => k * Real.sin (r / k)) atTop (𝓝 r) := by
  have h_sin_deriv : Filter.Tendsto (fun x : ℝ => Real.sin x / x) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
    simpa [div_eq_inv_mul] using Real.hasDerivAt_sin 0 |> HasDerivAt.tendsto_slope_zero
  by_cases hr : r = 0
  · simp [hr]
  · have h_subst : Filter.Tendsto (fun k : ℝ => Real.sin (r / k) / (r / k)) Filter.atTop (𝓝 1) := by
      refine h_sin_deriv.comp <| tendsto_inf.mpr
        ⟨tendsto_const_nhds.div_atTop tendsto_id, tendsto_principal.mpr
          <| eventually_ne_atTop 0 |> Eventually.mono <| by aesop⟩
    convert h_subst.const_mul r using 2 <;> field_simp

end SpatialGeometry

/-- The structure FLRW is defined to contain the physical parameters of the
  Friedmann-Lemaître-Robertson-Walker metric. That is, it contains
- The scale factor `a(t)`
- An element of `SpatialGeometry`.

Semiformal implementation note: It is possible that we should restrict
`a(t)` to be smooth or at least twice differentiable.
-/
@[sorryful]
def FLRW : Type := sorry

namespace FLRW

namespace FriedmannEquation

/--
The first-order Friedmann equation.

- `a : ℝ → ℝ` is the FLRW scale factor as a function of cosmic time `t`.
- `ρ : ℝ → ℝ` is the total energy density as a function of cosmic time `t`.
- `k : ℝ` is the spatial curvature parameter.
- `Λ : ℝ` is the cosmological constant.
- `G : ℝ` is Newton's constant.
- `c : ℝ` is the speed of light. It may be set to 1 for convenience.

Note: We will leave `c` explicit for generality and accounting purposes.

At time `t` the equation reads:
`(a'(t) / a(t))^2 = (8πG/3) ρ(t) − k c^2 / a(t)^2 + Λ c^2 / 3`.

-/
def FirstOrderFriedmann (a ρ: ℝ → ℝ) (k Λ G c : ℝ) (t : ℝ) : Prop :=
    ((deriv a t / a t)^2
      = ((8 * Real.pi * G) / 3) * ρ t - k * c^2 / (a t)^2 + Λ * c ^2/ 3)

/--
The second-order Friedmann equation.
Note: Other sources may call this the Raychaudhuri equation.
We choose not to use that terminology to avoid the Raychaudhuri equation
related to describing congruences of geodesics in general relativity.
- `a : ℝ → ℝ` is the FLRW scale factor as a function of cosmic time `t`.
- `ρ : ℝ → ℝ` is the total energy density as a function of cosmic time `t`.
- `p : ℝ → ℝ` is the pressure. It is related to `ρ` via `p = w * ρ `
- `w` is the equation of state. We will introduce this later.
- `Λ : ℝ` is the cosmological constant.
- `G : ℝ` is Newton's constant.
- `c : ℝ` is the speed of light. It may be set to 1 for convenience.

Note: We will leave `c` explicit for generality and accounting purposes.

At time `t` the equation reads:
`(a''(t) / a (t)) = - (4πG/3) * (ρ(t) + 3 * p(t) / c^2) + Λ * c^2 / 3`.

-/
def SecondOrderFriedmann (a ρ p: ℝ → ℝ) (Λ G c : ℝ) (t : ℝ) : Prop :=
    (deriv (deriv a) t) / a t = - (4 * Real.pi * G / 3) * (ρ t + 3 * p t / c^2) + Λ * c^2 / 3

/-- The hubble constant defined in terms of the scale factor
  as `(dₜ a) / a`.

  The notation `H` is used for the `hubbleConstant`.

  Semiformal implementation note: Implement also scoped notation. -/

noncomputable def hubbleConstant (a : ℝ → ℝ) (t : ℝ) : ℝ :=
    deriv a t / a t

/-- The deceleration parameter defined in terms of the scale factor
  as `- (dₜdₜ a) a / (dₜ a)^2`.

  The notation `q` is used for the `decelerationParameter`.

  Semiformal implementation note: Implement also scoped notation. -/

noncomputable def decelerationParameter (a : ℝ → ℝ) (t : ℝ) : ℝ :=
    - (deriv (deriv a) t * a t) / (deriv a t)^2

/-- The deceleration parameter is equal to `- (1 + (dₜ H)/H^2)`. -/
informal_lemma decelerationParameter_eq_one_plus_hubbleConstant where
  deps := []
  tag := "6Z23H"

/-- The time evolution of the hubble parameter is equal to `dₜ H = - H^2 (1 + q)`. -/
informal_lemma time_evolution_hubbleConstant where
  deps := []
  tag := "6Z3BS"

/-- There exists a time at which the hubble constant decreases if and only if
  there exists a time where the deceleration parameter is less then `-1`. -/
informal_lemma hubbleConstant_decrease_iff where
  deps := []
  tag := "6Z3FS"
end FriedmannEquation
end FLRW

end Cosmology
