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
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
/-!

# The Friedmann-Lemaître-Robertson-Walker metric

The spatial geometry of an FLRW model and its curvature parameter, the structures `FLRW` and
`CosmicFluid`, the density and pressure of the cosmological constant as a fluid and the cosmic
fluid with the cosmological constant folded in, the tangent-line bound for an FLRW model whose
scale factor decelerates and the resulting lower bound on its interval of time, the first- and
second-order Friedmann equations, the proposition `FLRW.FriedmannSolution` that a model and a
fluid solve them, and the Hubble and deceleration parameters.

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

/-- The density `ρ_Λ = Λ c² / (8 π G)` associated with the cosmological constant. -/
noncomputable def FLRW.FriedmannEquation.cosmologicalConstantDensity (Λ G c : ℝ) : ℝ :=
  Λ * c ^ 2 / (8 * Real.pi * G)

/-- The pressure `p_Λ = - ρ_Λ c²` associated with the cosmological constant. -/
noncomputable def FLRW.FriedmannEquation.cosmologicalConstantPressure (Λ G c : ℝ) : ℝ :=
  -(FLRW.FriedmannEquation.cosmologicalConstantDensity Λ G c) * c ^ 2

/-- The cosmic fluid `F` with the cosmological constant folded in as a fluid. -/
noncomputable def CosmicFluid.addCosmologicalConstant (F : CosmicFluid) (Λ G c : ℝ) :
    CosmicFluid :=
  ⟨fun s => F.ρ s + FLRW.FriedmannEquation.cosmologicalConstantDensity Λ G c,
    fun s => F.p s + FLRW.FriedmannEquation.cosmologicalConstantPressure Λ G c⟩

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

/-!

## The interval and the tangent-line bound for a decelerating model

These statements hold for any FLRW model; they do not use the Friedmann equations.

-/

section

open Time

/-- The times between two times of the interval `U.I` of an FLRW model are in `U.I`. -/
lemma mk_mem_I_of_mem_Icc (U : FLRW) {σ τ x : ℝ} (hσ : (⟨σ⟩ : Time) ∈ U.I)
    (hτ : (⟨τ⟩ : Time) ∈ U.I) (hx : x ∈ Set.Icc σ τ) : (⟨x⟩ : Time) ∈ U.I :=
  U.ordConnected_I.out hσ hτ ⟨(Time.le_def _ _).mpr hx.1, (Time.le_def _ _).mpr hx.2⟩

/-- Along the time coordinate, the derivative of the scale factor is continuous on any segment
  of the interval `U.I`. -/
lemma continuousOn_deriv_scaleFactor_mk (U : FLRW) {σ τ : ℝ} (hσ : (⟨σ⟩ : Time) ∈ U.I)
    (hτ : (⟨τ⟩ : Time) ∈ U.I) : ContinuousOn (fun x : ℝ => ∂ₜ U.a ⟨x⟩) (Set.Icc σ τ) :=
  U.differentiableOn_deriv_a.continuousOn.comp toRealCLE.symm.continuous.continuousOn
    fun _ hx => U.mk_mem_I_of_mem_Icc hσ hτ hx

/-- If the scale factor decelerates on the interval (`∂ₜ ∂ₜ a ≤ 0` on `U.I`), it lies below its
  tangent line at any time `t₀` of `U.I`: `a t ≤ a t₀ + ∂ₜ a t₀ (t - t₀)` for `t ∈ U.I`. The
  derivative is antitone on the segment between `t` and `t₀`, which lies in `U.I`, and the mean
  value inequality concludes. -/
lemma scaleFactor_le_tangent (U : FLRW) (hdec : ∀ s ∈ U.I, ∂ₜ (∂ₜ U.a) s ≤ 0) {t₀ t : Time}
    (ht₀ : t₀ ∈ U.I) (ht : t ∈ U.I) : U.a t ≤ U.a t₀ + ∂ₜ U.a t₀ * (t.val - t₀.val) := by
  obtain ⟨τ₀⟩ := t₀
  obtain ⟨σ⟩ := t
  dsimp only
  -- on a segment of `U.I`, the scale factor and its derivative have derivatives along the
  -- time coordinate, and the derivative of the scale factor is antitone
  have key : ∀ {lo hi : ℝ}, (⟨lo⟩ : Time) ∈ U.I → (⟨hi⟩ : Time) ∈ U.I →
      (∀ x ∈ Set.Icc lo hi, HasDerivAt (fun y : ℝ => U.a ⟨y⟩) (∂ₜ U.a ⟨x⟩) x) ∧
      AntitoneOn (fun x : ℝ => ∂ₜ U.a ⟨x⟩) (Set.Icc lo hi) := by
    intro lo hi hlo hhi
    have hA : ∀ x ∈ Set.Icc lo hi, HasDerivAt (fun y : ℝ => U.a ⟨y⟩) (∂ₜ U.a ⟨x⟩) x :=
      fun x hx => hasDerivAt_mk_of_differentiableAt
        (U.differentiableAt_a (U.mk_mem_I_of_mem_Icc hlo hhi hx))
    have hA' : ∀ x ∈ Set.Icc lo hi,
        HasDerivAt (fun y : ℝ => ∂ₜ U.a ⟨y⟩) (∂ₜ (∂ₜ U.a) ⟨x⟩) x :=
      fun x hx => hasDerivAt_mk_of_differentiableAt
        (U.differentiableAt_deriv_a (U.mk_mem_I_of_mem_Icc hlo hhi hx))
    refine ⟨hA, antitoneOn_of_deriv_nonpos (convex_Icc lo hi)
      (U.continuousOn_deriv_scaleFactor_mk hlo hhi)
      (fun x hx => (hA' x (interior_subset hx)).differentiableAt.differentiableWithinAt)
      (fun x hx => ?_)⟩
    rw [(hA' x (interior_subset hx)).deriv]
    exact hdec _ (U.mk_mem_I_of_mem_Icc hlo hhi (interior_subset hx))
  rcases le_total σ τ₀ with h | h
  · obtain ⟨hA, hanti⟩ := key ht ht₀
    have hmv := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc σ τ₀)
      (fun x hx => (hA x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hA x (interior_subset hx)).differentiableAt.differentiableWithinAt)
      (C := ∂ₜ U.a ⟨τ₀⟩) (fun x hx => by
        rw [(hA x (interior_subset hx)).deriv]
        exact hanti (interior_subset hx) ⟨h, le_rfl⟩ (interior_subset hx).2)
      σ ⟨le_rfl, h⟩ τ₀ ⟨h, le_rfl⟩ h
    linarith
  · obtain ⟨hA, hanti⟩ := key ht₀ ht
    have hmv := Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc τ₀ σ)
      (fun x hx => (hA x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hA x (interior_subset hx)).differentiableAt.differentiableWithinAt)
      (C := ∂ₜ U.a ⟨τ₀⟩) (fun x hx => by
        rw [(hA x (interior_subset hx)).deriv]
        exact hanti ⟨le_rfl, h⟩ (interior_subset hx) (interior_subset hx).1)
      τ₀ ⟨le_rfl, h⟩ σ ⟨h, le_rfl⟩ h
    linarith

/-- The Big-Bang bound for an FLRW model: if the scale factor decelerates on `U.I` and the model
  expands at `t₀ ∈ U.I`, every time of `U.I` is later than `t₀ - a t₀ / ∂ₜ a t₀`. Earlier, the
  tangent line, and hence the scale factor, would be non-positive. -/
lemma lt_of_mem_I_of_decelerating (U : FLRW) (hdec : ∀ s ∈ U.I, ∂ₜ (∂ₜ U.a) s ≤ 0)
    {t₀ : Time} (ht₀ : t₀ ∈ U.I) (h0 : 0 < ∂ₜ U.a t₀) {t : Time} (ht : t ∈ U.I) :
    t₀.val - U.a t₀ / ∂ₜ U.a t₀ < t.val := by
  by_contra hle
  have hle' := not_lt.mp hle
  have htan := U.scaleFactor_le_tangent hdec ht₀ ht
  have hpos := U.a_pos t ht
  have hq : ∂ₜ U.a t₀ * (U.a t₀ / ∂ₜ U.a t₀) = U.a t₀ := by field_simp
  have h1 : t.val - t₀.val ≤ -(U.a t₀ / ∂ₜ U.a t₀) := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 h0.le
  rw [mul_neg, hq] at h2
  linarith

/-- Hence the interval of an FLRW model that decelerates on `U.I` and expands at one of its
  times is bounded below. -/
lemma bddBelow_I_of_decelerating (U : FLRW) (hdec : ∀ s ∈ U.I, ∂ₜ (∂ₜ U.a) s ≤ 0) {t₀ : Time}
    (ht₀ : t₀ ∈ U.I) (h0 : 0 < ∂ₜ U.a t₀) : BddBelow U.I :=
  ⟨⟨t₀.val - U.a t₀ / ∂ₜ U.a t₀⟩, fun _ ht =>
    (Time.le_def _ _).mpr (U.lt_of_mem_I_of_decelerating hdec ht₀ h0 ht).le⟩

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

TODO "State the remaining results on FLRW cosmology (the Hubble and deceleration parameters, the
  continuity equation and the density scaling laws, and the exact solutions) directly in terms of
  `FLRW`, `CosmicFluid` and `FLRW.FriedmannSolution`, so that the API is organised around these
  rather than around separate functions `a`, `ρ` and `p`."

end Cosmology
