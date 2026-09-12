/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luis Gabriel C. Bariuan, Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Physlib.Meta.Linters.Sorry
public import Physlib.Meta.Informal.Basic
public import Physlib.Meta.TODO.Basic
public import Physlib.SpaceAndTime.Time.Derivatives
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
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
  have hg : Tendsto (fun k : ℝ => 1 / k) atTop (𝓝[≠] 0) := by
    simpa only [one_div] using tendsto_inv_atTop_nhdsGT_zero.mono_right (nhdsGT_le_nhdsNE 0)
  exact ((tendsto_sinh_rx_over_x r).comp hg).congr fun k => by
    simp only [Function.comp_apply, mul_one_div, div_div_eq_mul_div, div_one, mul_comm]

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
  have hg : Tendsto (fun k : ℝ => 1 / k) atTop (𝓝[≠] 0) := by
    simpa only [one_div] using tendsto_inv_atTop_nhdsGT_zero.mono_right (nhdsGT_le_nhdsNE 0)
  exact ((tendsto_sin_rx_over_x r).comp hg).congr fun k => by
    simp only [Function.comp_apply, mul_one_div, div_div_eq_mul_div, div_one, mul_comm]

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

TODO "Replace the placeholder `FLRW` type with a concrete structure bundling a positive
  scale factor `a : Time → ℝ` (smooth, or at least twice differentiable) together with an
  element of `SpatialGeometry`."

namespace FLRW

namespace FriedmannEquation

open Time

/--
The first-order Friedmann equation.

- `a : Time → ℝ` is the FLRW scale factor as a function of cosmic time `t`.
- `ρ : Time → ℝ` is the total energy density as a function of cosmic time `t`.
- `k : ℝ` is the spatial curvature parameter.
- `Λ : ℝ` is the cosmological constant.
- `G : ℝ` is Newton's constant.
- `c : ℝ` is the speed of light. It may be set to 1 for convenience.

Note: We will leave `c` explicit for generality and accounting purposes.

At time `t` the equation reads:
`(a'(t) / a(t))^2 = (8πG/3) ρ(t) − k c^2 / a(t)^2 + Λ c^2 / 3`.

-/
def FirstOrderFriedmann (a ρ : Time → ℝ) (k Λ G c : ℝ) (t : Time) : Prop :=
    ((∂ₜ a t / a t)^2
      = ((8 * Real.pi * G) / 3) * ρ t - k * c^2 / (a t)^2 + Λ * c ^2/ 3)

/--
The second-order Friedmann equation.
Note: Other sources may call this the Raychaudhuri equation.
We choose not to use that terminology to avoid the Raychaudhuri equation
related to describing congruences of geodesics in general relativity.
- `a : Time → ℝ` is the FLRW scale factor as a function of cosmic time `t`.
- `ρ : Time → ℝ` is the total energy density as a function of cosmic time `t`.
- `p : Time → ℝ` is the pressure. It is related to `ρ` via `p = w * ρ `
- `w` is the equation of state. We will introduce this later.
- `Λ : ℝ` is the cosmological constant.
- `G : ℝ` is Newton's constant.
- `c : ℝ` is the speed of light. It may be set to 1 for convenience.

Note: We will leave `c` explicit for generality and accounting purposes.

At time `t` the equation reads:
`(a''(t) / a (t)) = - (4πG/3) * (ρ(t) + 3 * p(t) / c^2) + Λ * c^2 / 3`.

-/
def SecondOrderFriedmann (a ρ p : Time → ℝ) (Λ G c : ℝ) (t : Time) : Prop :=
    ∂ₜ (∂ₜ a) t / a t = - (4 * Real.pi * G / 3) * (ρ t + 3 * p t / c^2) + Λ * c^2 / 3

/-- The hubble constant defined in terms of the scale factor
  as `(dₜ a) / a`.

  The notation `H` is used for the `hubbleConstant`.

  Semiformal implementation note: Implement also scoped notation. -/

noncomputable def hubbleConstant (a : Time → ℝ) (t : Time) : ℝ :=
    ∂ₜ a t / a t

/-- The Hubble constant is nonzero whenever `∂ₜ a t` and `a t` are both nonzero. -/
lemma hubbleConstant_ne_zero {a : Time → ℝ} {t : Time}
    (hd_az : ∂ₜ a t ≠ 0) (haz : a t ≠ 0) :
    hubbleConstant a t ≠ 0 :=
  div_ne_zero hd_az haz

TODO "Define the Hubble constant `H₀ = H(t₀)`, the present-day value of the Hubble parameter
  `hubbleConstant`, and the present Hubble radius `R_H = c / H₀`. Keep `parameter` (the
  time-dependent `H(t)`) distinct from `constant` (the number `H₀`)."

TODO "Express the Hubble parameter as a function of the scale factor, `H(a)`, and of the
  redshift, `H(z)`, using `a = 1 / (1 + z)` with the normalization `a₀ = 1`; define the
  reduced Hubble function `E(z) = H(z) / H₀`."

/-- The deceleration parameter defined in terms of the scale factor
  as `- (dₜdₜ a) a / (dₜ a)^2`.

  The notation `q` is used for the `decelerationParameter`.

  Semiformal implementation note: Implement also scoped notation. -/

noncomputable def decelerationParameter (a : Time → ℝ) (t : Time) : ℝ :=
    - (∂ₜ (∂ₜ a) t * a t) / (∂ₜ a t)^2

/-- Quotient-rule expression for the time derivative of the Hubble constant:
  `dₜ H = (a'' a - (a')^2) / a^2`. -/
lemma deriv_hubbleConstant {a : Time → ℝ} {t : Time}
    (ha : DifferentiableAt ℝ a t) (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (haz : a t ≠ 0) :
    ∂ₜ (hubbleConstant a) t =
      (∂ₜ (∂ₜ a) t * a t - (∂ₜ a t) ^ 2) / (a t) ^ 2 := by
  show ∂ₜ (fun s => ∂ₜ a s / a s) t = _
  rw [Time.deriv_div hd_a ha haz]
  ring

/-- The deceleration parameter is equal to `- (1 + (dₜ H)/H^2)`. -/
lemma decelerationParameter_eq_one_plus_hubbleConstant
    {a : Time → ℝ} {t : Time}
    (ha : DifferentiableAt ℝ a t) (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (haz : a t ≠ 0) (hd_az : ∂ₜ a t ≠ 0) :
    decelerationParameter a t =
      -(1 + ∂ₜ (hubbleConstant a) t / (hubbleConstant a t) ^ 2) := by
  rw [deriv_hubbleConstant ha hd_a haz, decelerationParameter, hubbleConstant]
  field_simp
  ring

/-- The time derivative of the Hubble constant equals `-H² (1 + q)`. -/
lemma deriv_hubbleConstant_eq_neg_sq_mul
    {a : Time → ℝ} {t : Time}
    (ha : DifferentiableAt ℝ a t) (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (haz : a t ≠ 0) (hd_az : ∂ₜ a t ≠ 0) :
    ∂ₜ (hubbleConstant a) t =
      -(hubbleConstant a t) ^ 2 * (1 + decelerationParameter a t) := by
  rw [deriv_hubbleConstant ha hd_a haz, hubbleConstant, decelerationParameter]
  field_simp
  ring

/-- Pointwise: `∂ₜ H t < 0` iff `-1 < q t` (assuming `a` is twice differentiable at `t`
  and both `a t` and `∂ₜ a t` are nonzero). -/
lemma deriv_hubbleConstant_neg_iff
    {a : Time → ℝ} {t : Time}
    (ha : DifferentiableAt ℝ a t) (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (haz : a t ≠ 0) (hd_az : ∂ₜ a t ≠ 0) :
    ∂ₜ (hubbleConstant a) t < 0 ↔ -1 < decelerationParameter a t := by
  rw [deriv_hubbleConstant_eq_neg_sq_mul ha hd_a haz hd_az]
  constructor <;> intro h <;> nlinarith [sq_pos_iff.mpr (hubbleConstant_ne_zero hd_az haz)]

/-- There exists a time at which `∂ₜ H < 0` iff there exists a time with `q > -1`.

  (The corresponding informal statement was written with `q < -1`. Since
  `dₜ H = -H² (1 + q)` and `H ≠ 0`, one has `dₜ H < 0 ↔ q > -1`, so the formal
  statement uses the corrected inequality `-1 < q`.) -/
lemma exists_deriv_hubbleConstant_neg_iff
    {a : Time → ℝ}
    (ha : ∀ t, DifferentiableAt ℝ a t) (hd_a : ∀ t, DifferentiableAt ℝ (∂ₜ a) t)
    (haz : ∀ t, a t ≠ 0) (hd_az : ∀ t, ∂ₜ a t ≠ 0) :
    (∃ t, ∂ₜ (hubbleConstant a) t < 0) ↔ (∃ t, -1 < decelerationParameter a t) :=
  exists_congr fun t => deriv_hubbleConstant_neg_iff (ha t) (hd_a t) (haz t) (hd_az t)
end FriedmannEquation
end FLRW

end Cosmology
