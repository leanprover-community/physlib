/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Physlib.Cosmology.FLRW.Basic
public import Physlib.Cosmology.FLRW.MatterContent
public import PhyslibAlpha.Cosmology.FLRW.PerfectFluid
public import PhyslibAlpha.Relativity.General.GravitationalConstant
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!

# Deriving the Friedmann equations from Einstein's field equations

Derivation of `Physlib.Cosmology.FLRW`'s first- and second-order Friedmann equations for an
arbitrary speed of light and Newton's gravitational constant from the FLRW Einstein field equations.

## i. Overview

Whereas `Physlib.Cosmology.FLRW` postulates the two Friedmann equations as ordinary differential
equations for a cosmological model with scale factor `a(t)`, this module derives them directly from
Einstein's field equations `G_{ij} + Λ g_{ij} = (8 π G / c⁴) T_{ij}` for a homogeneous, isotropic
metric filled with a comoving perfect fluid, with `G` the gravitational constant and `c` the speed
of light. Reparametrizing cosmic time `t` by the length-dimensioned coordinate `τ = c t` gives
`flrwScaleFactorOfReal` and `FLRWSpacetime.ofCosmology` and yields
`Cosmology.FLRW.FriedmannSolution` directly from the Einstein equations.

## ii. Key results

- `flrwScaleFactorOfReal`, `FLRWSpacetime.ofCosmology` : scale factor in coordinate time `τ = c t`
  and corresponding FLRW spacetime geometry.
- `hasDerivAt_flrwScaleFactorOfReal`, `eventually_differentiableAt_flrwScaleFactorOfReal`,
  `deriv_flrwScaleFactorOfReal_eq`, `hasDerivAt_deriv_flrwScaleFactorOfReal` : first- and
  second-derivative relations between cosmic-time derivatives and `τ = c t` derivatives.
- `einsteinTensor_ofCosmology_iff_friedmann`, `friedmannSolution_of_einsteinTensor` :
  equivalence between the FLRW Einstein field equations and `FirstOrderFriedmann` /
  `SecondOrderFriedmann`, constructing a `Cosmology.FLRW.FriedmannSolution`.

## iii. Table of contents

- A. Real-coordinate scale factor and Friedmann derivation

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 5 (Sec. 5.1-5.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 27.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 8
  (https://arxiv.org/pdf/gr-qc/9712019#page=201). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace FLRW

open GeneralRelativity.CoordinateCurvature

/-!

## A. Real-coordinate scale factor and Friedmann derivation

Rewriting a cosmological model's scale factor `a(t)` as a function of the length-dimensioned time
coordinate `τ = c t` relates the FLRW Einstein tensor directly to the first- and second-order
Friedmann equations in `Physlib.Cosmology.FLRW`.

-/

/-- The scale factor `τ ↦ a(τ / c)` of a cosmological model as a function of coordinate time
`τ = c t`. -/
noncomputable def flrwScaleFactorOfReal (c : SpeedOfLight) (U : Cosmology.FLRW) : ℝ → ℝ :=
  fun τ => U.a ⟨τ / (c : ℝ)⟩

/-- Construct an FLRW spacetime metric from a `Cosmology.FLRW` model and speed of light `c`. -/
noncomputable def FLRWSpacetime.ofCosmology (c : SpeedOfLight) (U : Cosmology.FLRW) :
    FLRWSpacetime where
  a := flrwScaleFactorOfReal c U
  k := U.geometry.curvature

/-- Evaluating `flrwScaleFactorOfReal` at `τ = c t` recovers the scale factor at cosmic time
`t`. -/
lemma flrwScaleFactorOfReal_mul (c : SpeedOfLight) (U : Cosmology.FLRW) (t : Time) :
    flrwScaleFactorOfReal c U ((c : ℝ) * t.val) = U.a t := by
  have heq : (⟨(c : ℝ) * t.val / (c : ℝ)⟩ : Time) = t := by
    ext
    exact mul_div_cancel_left₀ t.val c.val_ne_zero
  simp only [flrwScaleFactorOfReal, heq]

/-- Neighbourhood membership of the rescaled cosmic time `τ / c` in the model's open time
interval. -/
private lemma eventually_div_mem_I (c : SpeedOfLight) (U : Cosmology.FLRW) {t : Time}
    (ht : t ∈ U.I) :
    ∀ᶠ τ in nhds ((c : ℝ) * t.val), (⟨τ / (c : ℝ)⟩ : Time) ∈ U.I := by
  have hcont : Continuous (fun τ : ℝ => (⟨τ / (c : ℝ)⟩ : Time)) :=
    Time.toRealCLE.symm.continuous.comp (continuous_id.div_const (c : ℝ))
  have heq : (⟨(c : ℝ) * t.val / (c : ℝ)⟩ : Time) = t := by
    ext
    exact mul_div_cancel_left₀ t.val c.val_ne_zero
  exact (hcont.tendsto ((c : ℝ) * t.val)).eventually (heq.symm ▸ U.isOpen_I.mem_nhds ht)

/-- Pointwise derivative of the rescaled scale factor `τ ↦ a(τ / c)` in coordinate time `τ`. -/
lemma hasDerivAt_flrwScaleFactorOfReal (c : SpeedOfLight) (U : Cosmology.FLRW) {τ : ℝ}
    (hτ : (⟨τ / (c : ℝ)⟩ : Time) ∈ U.I) :
    HasDerivAt (flrwScaleFactorOfReal c U) (Time.deriv U.a ⟨τ / (c : ℝ)⟩ / (c : ℝ)) τ := by
  have h1 : HasDerivAt (fun s : ℝ => U.a ⟨s⟩) (Time.deriv U.a ⟨τ / (c : ℝ)⟩) (τ / (c : ℝ)) :=
    Time.hasDerivAt_mk_of_differentiableAt (U.differentiableAt_a hτ)
  have h2 : HasDerivAt (fun s : ℝ => s / (c : ℝ)) (1 / (c : ℝ)) τ :=
    (hasDerivAt_id τ).div_const (c : ℝ)
  have hcomp := h1.scomp τ h2
  convert hcomp using 1
  · rfl
  · simp [smul_eq_mul]
    ring

/-- Neighbourhood differentiability of the rescaled scale factor around coordinate time
`τ = c t`. -/
lemma eventually_differentiableAt_flrwScaleFactorOfReal (c : SpeedOfLight) (U : Cosmology.FLRW)
    {t : Time} (ht : t ∈ U.I) :
    ∀ᶠ τ in nhds ((c : ℝ) * t.val), DifferentiableAt ℝ (flrwScaleFactorOfReal c U) τ := by
  filter_upwards [eventually_div_mem_I c U ht] with τ hτ
  exact (hasDerivAt_flrwScaleFactorOfReal c U hτ).differentiableAt

/-- First derivative of the rescaled scale factor at `τ = c t`: `da/dτ = (1 / c) ∂ₜ a`. -/
lemma deriv_flrwScaleFactorOfReal_eq (c : SpeedOfLight) (U : Cosmology.FLRW) {t : Time}
    (ht : t ∈ U.I) :
    deriv (flrwScaleFactorOfReal c U) ((c : ℝ) * t.val) = Time.deriv U.a t / (c : ℝ) := by
  have heq : (⟨(c : ℝ) * t.val / (c : ℝ)⟩ : Time) = t := by
    ext
    exact mul_div_cancel_left₀ t.val c.val_ne_zero
  have hτ : (⟨(c : ℝ) * t.val / (c : ℝ)⟩ : Time) ∈ U.I := heq.symm ▸ ht
  simpa [heq] using (hasDerivAt_flrwScaleFactorOfReal c U hτ).deriv

/-- Second derivative of the rescaled scale factor at `τ = c t`: `d²a/dτ² = (1 / c²) ∂ₜ² a`. -/
lemma hasDerivAt_deriv_flrwScaleFactorOfReal (c : SpeedOfLight) (U : Cosmology.FLRW) {t : Time}
    (ht : t ∈ U.I) :
    HasDerivAt (deriv (flrwScaleFactorOfReal c U))
      (Time.deriv (Time.deriv U.a) t / (c : ℝ) ^ 2) ((c : ℝ) * t.val) := by
  have heq : deriv (flrwScaleFactorOfReal c U) =ᶠ[nhds ((c : ℝ) * t.val)]
      fun τ => Time.deriv U.a ⟨τ / (c : ℝ)⟩ / (c : ℝ) := by
    filter_upwards [eventually_div_mem_I c U ht] with τ hτ
    exact (hasDerivAt_flrwScaleFactorOfReal c U hτ).deriv
  have h1 : HasDerivAt (fun s : ℝ => Time.deriv U.a ⟨s⟩)
      (Time.deriv (Time.deriv U.a) t) ((c : ℝ) * t.val / (c : ℝ)) := by
    have ht' : (c : ℝ) * t.val / (c : ℝ) = t.val := mul_div_cancel_left₀ t.val c.val_ne_zero
    rw [ht']
    exact Time.hasDerivAt_mk_of_differentiableAt (U.differentiableAt_deriv_a ht)
  have h2 : HasDerivAt (fun s : ℝ => s / (c : ℝ)) (1 / (c : ℝ)) ((c : ℝ) * t.val) :=
    (hasDerivAt_id ((c : ℝ) * t.val)).div_const (c : ℝ)
  have hcomp1 := (h1.scomp ((c : ℝ) * t.val) h2).const_smul (1 / (c : ℝ))
  have hcomp : HasDerivAt (fun τ : ℝ => Time.deriv U.a ⟨τ / (c : ℝ)⟩ / (c : ℝ))
      (Time.deriv (Time.deriv U.a) t / (c : ℝ) ^ 2) ((c : ℝ) * t.val) := by
    convert hcomp1 using 1
    · ext τ
      simp [Pi.smul_apply, Function.comp_def, smul_eq_mul, div_eq_inv_mul]
    · simp [smul_eq_mul]
      ring
  exact hcomp.congr_of_eventuallyEq heq

/-- The FLRW Einstein field equations for a comoving cosmic fluid with speed of light `c` and
gravitational constant `G` are equivalent to the first- and second-order Friedmann equations of
`Physlib.Cosmology.FLRW`. -/
lemma einsteinTensor_ofCosmology_iff_friedmann (c : SpeedOfLight) (U : Cosmology.FLRW)
    (F : Cosmology.CosmicFluid) (Λ : ℝ) (G : GravitationalConstant) {t : Time} (ht : t ∈ U.I)
    (x : Fin 4 → ℝ) (hx0 : x 0 = (c : ℝ) * t.val) (hr : x 1 ≠ 0)
    (hkr : 1 - U.geometry.curvature * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    (∀ i j, CoordinateCurvature.einsteinTensor (FLRWSpacetime.ofCosmology c U).metric
          (FLRWSpacetime.ofCosmology c U).metricInv x i j
          + Λ * (FLRWSpacetime.ofCosmology c U).metric x i j
        = 8 * Real.pi * G.val / (c : ℝ) ^ 4 * perfectFluidStressEnergy c (F.ρ t) (F.p t)
            ((FLRWSpacetime.ofCosmology c U).metric x) i j)
      ↔ Cosmology.FLRW.FriedmannEquation.FirstOrderFriedmann U.a F.ρ U.geometry.curvature Λ
            G.val c t
          ∧ Cosmology.FLRW.FriedmannEquation.SecondOrderFriedmann U.a F.ρ F.p Λ G.val c t := by
  have hc : (c : ℝ) ≠ 0 := c.val_ne_zero
  have ha0_eq : flrwScaleFactorOfReal c U (x 0) = U.a t := by
    rw [hx0]
    exact flrwScaleFactorOfReal_mul c U t
  have ha : (FLRWSpacetime.ofCosmology c U).a (x 0) ≠ 0 := by
    simp only [FLRWSpacetime.ofCosmology, ha0_eq]
    exact U.a_ne_zero ht
  have ha_diff : ∀ᶠ τ in nhds (x 0), DifferentiableAt ℝ (FLRWSpacetime.ofCosmology c U).a τ := by
    rw [hx0]
    exact eventually_differentiableAt_flrwScaleFactorOfReal c U ht
  have hd2 := hasDerivAt_deriv_flrwScaleFactorOfReal c U ht
  have ha2 : DifferentiableAt ℝ (deriv (FLRWSpacetime.ofCosmology c U).a) (x 0) := by
    rw [hx0]
    exact hd2.differentiableAt
  have hd1_eq : deriv (flrwScaleFactorOfReal c U) (x 0) = Time.deriv U.a t / (c : ℝ) := by
    rw [hx0]
    exact deriv_flrwScaleFactorOfReal_eq c U ht
  have hd2_eq : deriv (deriv (flrwScaleFactorOfReal c U)) (x 0)
      = Time.deriv (Time.deriv U.a) t / (c : ℝ) ^ 2 := by
    rw [hx0]
    exact hd2.deriv
  rw [(FLRWSpacetime.ofCosmology c U).einsteinTensor_iff_friedmann c Λ G (F.ρ t) (F.p t) x
    ha hr hkr hsin ha_diff ha2]
  simp only [Cosmology.FLRW.FriedmannEquation.FirstOrderFriedmann,
    Cosmology.FLRW.FriedmannEquation.SecondOrderFriedmann, FLRWSpacetime.ofCosmology,
    ha0_eq, hd1_eq, hd2_eq]
  have hau : U.a t ≠ 0 := U.a_ne_zero ht
  have h1 : (Time.deriv U.a t / (c : ℝ) / U.a t) ^ 2
        = 8 * Real.pi * G.val / (3 * (c : ℝ) ^ 2) * F.ρ t
          - U.geometry.curvature / U.a t ^ 2 + Λ / 3
      ↔ (Time.deriv U.a t / U.a t) ^ 2
        = 8 * Real.pi * G.val / 3 * F.ρ t
          - U.geometry.curvature * (c : ℝ) ^ 2 / U.a t ^ 2 + Λ * (c : ℝ) ^ 2 / 3 := by
    constructor <;> intro h
    · have := congrArg (· * (c : ℝ) ^ 2) h
      field_simp [hc, hau] at this ⊢
      linarith
    · have := congrArg (· / (c : ℝ) ^ 2) h
      field_simp [hc, hau] at this ⊢
      linarith
  have h2 : Time.deriv (Time.deriv U.a) t / (c : ℝ) ^ 2 / U.a t
        = -(4 * Real.pi * G.val / (3 * (c : ℝ) ^ 2)) * (F.ρ t + 3 * F.p t / (c : ℝ) ^ 2) + Λ / 3
      ↔ Time.deriv (Time.deriv U.a) t / U.a t
        = -(4 * Real.pi * G.val / 3) * (F.ρ t + 3 * F.p t / (c : ℝ) ^ 2)
          + Λ * (c : ℝ) ^ 2 / 3 := by
    constructor <;> intro h
    · have := congrArg (· * (c : ℝ) ^ 2) h
      field_simp [hc, hau] at this ⊢
      linarith
    · have := congrArg (· / (c : ℝ) ^ 2) h
      field_simp [hc, hau] at this ⊢
      linarith
  exact and_congr h1 h2

/-- If the FLRW Einstein equations hold across the model's open time interval at a regular spatial
chart point, then the model and cosmic fluid form a `Cosmology.FLRW.FriedmannSolution` (and hence
automatically satisfy the fluid continuity equation). -/
lemma friedmannSolution_of_einsteinTensor (c : SpeedOfLight) (U : Cosmology.FLRW)
    (F : Cosmology.CosmicFluid) (Λ : ℝ) (G : GravitationalConstant) (r₀ θ₀ : ℝ) (hr : r₀ ≠ 0)
    (hkr : 1 - U.geometry.curvature * r₀ ^ 2 ≠ 0) (hsin : Real.sin θ₀ ≠ 0)
    (heinst : ∀ t ∈ U.I, ∀ i j,
      let x : Fin 4 → ℝ := ![(c : ℝ) * t.val, r₀, θ₀, 0]
      CoordinateCurvature.einsteinTensor (FLRWSpacetime.ofCosmology c U).metric
          (FLRWSpacetime.ofCosmology c U).metricInv x i j
          + Λ * (FLRWSpacetime.ofCosmology c U).metric x i j
        = 8 * Real.pi * G.val / (c : ℝ) ^ 4 * perfectFluidStressEnergy c (F.ρ t) (F.p t)
            ((FLRWSpacetime.ofCosmology c U).metric x) i j) :
    U.FriedmannSolution F Λ G.val c := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · exact ((einsteinTensor_ofCosmology_iff_friedmann c U F Λ G ht ![(c : ℝ) * t.val, r₀, θ₀, 0]
      rfl hr hkr hsin).mp (heinst t ht)).1
  · exact ((einsteinTensor_ofCosmology_iff_friedmann c U F Λ G ht ![(c : ℝ) * t.val, r₀, θ₀, 0]
      rfl hr hkr hsin).mp (heinst t ht)).2

end FLRW

end GeneralRelativity
