/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luis Gabriel C. Bariuan, Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Physlib.Meta.Linters.Sorry
public import Physlib.Meta.TODO.Basic
public import Physlib.SpaceAndTime.Time.Derivatives
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
/-!

# The Friedmann-Lemaître-Robertson-Walker metric

The spatial geometry of an FLRW model and its curvature parameter, the structures `FLRW` and
`CosmicFluid`, the first- and second-order Friedmann equations, the proposition
`FLRW.FriedmannSolution` that a model and a fluid solve them, and the Hubble and deceleration
parameters.

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

/-- The curvature parameter of the spatial geometry, the constant `k` of the first-order
  Friedmann equation `FLRW.FriedmannEquation.FirstOrderFriedmann`:
- `1 / k ^ 2` for `Spherical k`, whose profile `S` is that of a sphere of radius `|k|`,
- `0` for `Flat`,
- `-1 / k ^ 2` for `Saddle k`, whose profile `S` is that of a hyperbolic space of curvature
  radius `|k|`.
-/
noncomputable def curvature : SpatialGeometry → ℝ
  | Spherical k _ => 1 / k ^ 2
  | Flat => 0
  | Saddle k _ => -1 / k ^ 2

@[simp]
lemma curvature_flat : Flat.curvature = 0 := rfl

/-- The spherical geometry has a positive curvature parameter. -/
lemma curvature_spherical_pos (k : ℝ) (h : k < 0) : 0 < (Spherical k h).curvature := by
  have hk : k ≠ 0 := h.ne
  simp only [curvature]
  positivity

/-- The saddle geometry has a negative curvature parameter. -/
lemma curvature_saddle_neg (k : ℝ) (h : k > 0) : (Saddle k h).curvature < 0 := by
  simp only [curvature, neg_div]
  exact neg_neg_of_pos (by positivity)

end SpatialGeometry

open Time in
/-- An FLRW model: the scale factor `a` of the Friedmann-Lemaître-Robertson-Walker metric on an
  open interval `I` of cosmic time, positive and twice differentiable on `I`, together with the
  geometry of the spatial slices. The values of `a` outside `I` carry no meaning. The interval
  lets a model begin at a Big Bang, as the Milne model `FLRW.milne` does on
  `I = {t | 0 < t.val}`. -/
structure FLRW where
  /-- The interval of cosmic time on which the model is defined. -/
  I : Set Time
  /-- The interval `I` is open. -/
  isOpen_I : IsOpen I
  /-- The set `I` is an interval. -/
  ordConnected_I : I.OrdConnected
  /-- The scale factor as a function of cosmic time. -/
  a : Time → ℝ
  /-- The scale factor is positive on `I`. -/
  a_pos : ∀ t ∈ I, 0 < a t
  /-- The scale factor is differentiable on `I`. -/
  differentiableOn_a : DifferentiableOn ℝ a I
  /-- The time derivative of the scale factor is differentiable on `I`. -/
  differentiableOn_deriv_a : DifferentiableOn ℝ (∂ₜ a) I
  /-- The geometry of the spatial slices. -/
  geometry : SpatialGeometry

/-- The cosmic fluid filling an FLRW model, described by its total energy density `ρ` and its
  pressure `p`, both functions of cosmic time, as in the first- and second-order Friedmann
  equations `FLRW.FriedmannEquation.FirstOrderFriedmann` and
  `FLRW.FriedmannEquation.SecondOrderFriedmann`. -/
structure CosmicFluid where
  /-- The total energy density as a function of cosmic time. -/
  ρ : Time → ℝ
  /-- The pressure as a function of cosmic time. -/
  p : Time → ℝ

/-- The empty cosmic fluid, with zero energy density and zero pressure at all times. -/
def CosmicFluid.empty : CosmicFluid := ⟨fun _ => 0, fun _ => 0⟩

namespace FLRW

section

open Time

variable (U : FLRW)

lemma a_ne_zero {t : Time} (ht : t ∈ U.I) : U.a t ≠ 0 := (U.a_pos t ht).ne'

lemma differentiableAt_a {t : Time} (ht : t ∈ U.I) : DifferentiableAt ℝ U.a t :=
  U.differentiableOn_a.differentiableAt (U.isOpen_I.mem_nhds ht)

lemma differentiableAt_deriv_a {t : Time} (ht : t ∈ U.I) : DifferentiableAt ℝ (∂ₜ U.a) t :=
  U.differentiableOn_deriv_a.differentiableAt (U.isOpen_I.mem_nhds ht)

end

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

TODO "Prove the change-of-variable relations underlying the age and distance integrals:
  `∂ₜ a = a * hubbleConstant a`, `dt = − dz / ((1 + z) * H)` and `dχ = c * dz / H`."

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

namespace FLRW

open FriedmannEquation

/-- The proposition that the FLRW model `U` filled with the cosmic fluid `F` solves the
  Friedmann equations: the first- and second-order Friedmann equations, with cosmological
  constant `Λ`, Newton's constant `G` and speed of light `c`, hold at every time of the interval
  `U.I`, the curvature parameter being the one of the spatial geometry. The continuity equation
  of the fluid is not part of it: it follows from the two Friedmann equations
  (`FLRW.FriedmannSolution.continuityEquation` in `Physlib.Cosmology.FLRW.MatterContent`). -/
structure FriedmannSolution (U : FLRW) (F : CosmicFluid) (Λ G c : ℝ) : Prop where
  /-- The first-order Friedmann equation holds on `U.I`. -/
  firstOrder : ∀ t ∈ U.I, FirstOrderFriedmann U.a F.ρ U.geometry.curvature Λ G c t
  /-- The second-order Friedmann equation holds on `U.I`. -/
  secondOrder : ∀ t ∈ U.I, SecondOrderFriedmann U.a F.ρ F.p Λ G c t

end FLRW

TODO "State the results on FLRW cosmology (density parameters, reduced Hubble function, exact
  solutions and dynamical criteria) directly in terms of `FLRW`, `CosmicFluid` and
  `FLRW.FriedmannSolution`, so that the API is organised around these rather than around
  separate functions `a`, `ρ` and `p`."

end Cosmology
