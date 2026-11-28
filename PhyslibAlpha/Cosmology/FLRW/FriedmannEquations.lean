/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Physlib.Cosmology.FLRW.Basic
public import Physlib.Cosmology.FLRW.MatterContent
public import Physlib.Relativity.SpeedOfLight
public import PhyslibAlpha.Cosmology.FLRW.Curvature
public import PhyslibAlpha.Relativity.General.GravitationalConstant
public import PhyslibAlpha.Relativity.Tensors.PerfectFluidStressEnergy
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!

# Deriving the Friedmann equations from Einstein's field equations

Comoving perfect-fluid stress-energy in an FLRW chart, and derivation of `Physlib.Cosmology.FLRW`'s
first- and second-order Friedmann equations for an arbitrary speed of light and Newton's
gravitational constant from the FLRW Einstein field equations.

## i. Overview

Equating the FLRW Einstein tensor with the stress-energy tensor of a comoving perfect fluid —
energy density `ρ`, pressure `p`, and four-velocity `u = ∂_t` in comoving coordinates — gives the
first and second Friedmann equations and their equivalence with the Einstein field equations.

Whereas `Physlib.Cosmology.FLRW` postulates the two Friedmann equations as ordinary differential
equations for a cosmological model with scale factor `a(t)`, this module derives them directly from
Einstein's field equations `G_{ij} + Λ g_{ij} = (8 π G / c⁴) T_{ij}` for a homogeneous, isotropic
metric filled with a comoving perfect fluid, with `G` the gravitational constant and `c` the speed
of light. Reparametrizing cosmic time `t` by the length-dimensioned coordinate `τ = c t` gives
`flrwScaleFactorOfReal` and `FLRWSpacetime.ofCosmology` and yields
`Cosmology.FLRW.FriedmannSolution` directly from the Einstein equations.

## ii. Key results

- `FLRWSpacetime.einsteinTensor_00_iff_friedmann`,
  `FLRWSpacetime.einsteinTensor_spatial_iff_friedmann`,
  `FLRWSpacetime.einsteinTensor_iff_friedmann` : equivalence of the comoving perfect-fluid
  Einstein equations with the two Friedmann equations.
- `flrwScaleFactorOfReal`, `FLRWSpacetime.ofCosmology` : scale factor in coordinate time `τ = c t`
  and corresponding FLRW spacetime geometry.
- `hasDerivAt_flrwScaleFactorOfReal`, `eventually_differentiableAt_flrwScaleFactorOfReal`,
  `deriv_flrwScaleFactorOfReal_eq`, `hasDerivAt_deriv_flrwScaleFactorOfReal` : first- and
  second-derivative relations between cosmic-time derivatives and `τ = c t` derivatives.
- `einsteinTensor_ofCosmology_iff_friedmann`, `friedmannSolution_of_einsteinTensor` :
  equivalence between the FLRW Einstein field equations and `FirstOrderFriedmann` /
  `SecondOrderFriedmann`, constructing a `Cosmology.FLRW.FriedmannSolution`.

## iii. Table of contents

- A. Comoving perfect fluid and Einstein–Friedmann equivalence
- B. Real-coordinate scale factor and Friedmann derivation

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 5 (Sec. 5.1-5.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 27.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 8
  (https://arxiv.org/pdf/gr-qc/9712019#page=201). [ref: Carroll1997]
-/

@[expose] public section

open GeneralRelativity

namespace Cosmology

namespace FLRW

open GeneralRelativity.CoordinateCurvature

/-!

## A. Comoving perfect fluid and Einstein–Friedmann equivalence

Equating the FLRW Einstein tensor with the comoving perfect-fluid stress-energy tensor directly
recovers the first and second Friedmann equations for an arbitrary speed of light and Newton's
gravitational constant.

-/

namespace FLRWSpacetime

/-- The `(0, 0)` Einstein equation `G_{00} + Λ g_{00} = (8 π G / c⁴) T_{00}` for an FLRW spacetime
and a comoving perfect fluid is equivalent to the first-order Friedmann energy-density equation in
coordinate time `τ = c t`. -/
lemma einsteinTensor_00_iff_friedmann (S : FLRWSpacetime) (c : SpeedOfLight) (Λ : ℝ)
    (G : GravitationalConstant) (ρ p : ℝ) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0) (hr : x 1 ≠ 0)
    (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    (S.toCoordinateMetric.einsteinTensor x 0 0 + Λ * S.metric x 0 0
        = 8 * Real.pi * G.val / (c : ℝ) ^ 4
          * GeneralRelativity.perfectFluidStressEnergy c ρ p (S.metric x) 0 0)
      ↔ (deriv S.a (x 0) / S.a (x 0)) ^ 2
          = (8 * Real.pi * G.val / (3 * (c : ℝ) ^ 2)) * ρ - S.k / (S.a (x 0)) ^ 2 + Λ / 3 := by
  have hc : (c : ℝ) ≠ 0 := c.val_ne_zero
  rw [S.einsteinTensor ⟨x, ha, hr, hkr, hsin⟩ ha_diff ha2 0 0]
  simp only [metric, GeneralRelativity.perfectFluidStressEnergy, Matrix.of_apply, ↓reduceIte,
    and_self, mul_one]
  have hrhs : 8 * Real.pi * G.val / (c : ℝ) ^ 4 * (ρ * (c : ℝ) ^ 2 + p + p * -1)
      = 8 * Real.pi * G.val / (c : ℝ) ^ 2 * ρ := by
    field_simp [hc]
    ring
  rw [hrhs]
  have hdiv : 8 * Real.pi * G.val / (3 * (c : ℝ) ^ 2) * ρ
      = (8 * Real.pi * G.val / (c : ℝ) ^ 2 * ρ) / 3 := by
    field_simp [hc]
  rw [hdiv]
  constructor <;> intro h <;> linarith

/-- Algebraic core of the spatial Friedmann equation: given the first-order equation
`(ȧ/a)² = 8πG ρ / (3 c²) - k/a² + Λ/3`, the spatial Einstein equation
`-(2 ä/a + (ȧ/a)² + k/a²) + Λ = 8πG p / c⁴` is equivalent to the acceleration equation
`ä/a = -4πG (ρ + 3p/c²) / (3 c²) + Λ/3`. -/
private lemma spatial_coef_eq (c : SpeedOfLight) (Λ G ρ p a adot addot k : ℝ)
    (hc : (c : ℝ) ≠ 0)
    (hf1 : (adot / a) ^ 2 = 8 * Real.pi * G / (3 * (c : ℝ) ^ 2) * ρ - k / a ^ 2 + Λ / 3) :
    -(2 * (addot / a) + (adot / a) ^ 2 + k / a ^ 2) + Λ = 8 * Real.pi * G / (c : ℝ) ^ 4 * p ↔
      addot / a = -(4 * Real.pi * G / (3 * (c : ℝ) ^ 2)) * (ρ + 3 * p / (c : ℝ) ^ 2) + Λ / 3 := by
  have hrhs : -(4 * Real.pi * G / (3 * (c : ℝ) ^ 2)) * (ρ + 3 * p / (c : ℝ) ^ 2)
      = -(4 * Real.pi * G / (3 * (c : ℝ) ^ 2) * ρ) - 4 * Real.pi * G / (c : ℝ) ^ 4 * p := by
    field_simp [hc]
    ring
  have h8 : 8 * Real.pi * G / (3 * (c : ℝ) ^ 2) * ρ
      = 2 * (4 * Real.pi * G / (3 * (c : ℝ) ^ 2) * ρ) := by ring
  have h8p : 8 * Real.pi * G / (c : ℝ) ^ 4 * p
      = 2 * (4 * Real.pi * G / (c : ℝ) ^ 4 * p) := by ring
  rw [hrhs]
  constructor <;> intro h <;> linarith

/-- Given the first-order Friedmann equation, the spatial diagonal Einstein equation `(1, 1)` is
equivalent to the second-order Friedmann acceleration equation in coordinate time `τ = c t`. -/
lemma einsteinTensor_spatial_iff_friedmann (S : FLRWSpacetime) (c : SpeedOfLight) (Λ : ℝ)
    (G : GravitationalConstant) (ρ p : ℝ) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0) (hr : x 1 ≠ 0)
    (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0))
    (hf1 : (deriv S.a (x 0) / S.a (x 0)) ^ 2
      = (8 * Real.pi * G.val / (3 * (c : ℝ) ^ 2)) * ρ - S.k / (S.a (x 0)) ^ 2 + Λ / 3) :
    (S.toCoordinateMetric.einsteinTensor x 1 1 + Λ * S.metric x 1 1
        = 8 * Real.pi * G.val / (c : ℝ) ^ 4
          * GeneralRelativity.perfectFluidStressEnergy c ρ p (S.metric x) 1 1)
      ↔ deriv (deriv S.a) (x 0) / S.a (x 0)
          = -(4 * Real.pi * G.val / (3 * (c : ℝ) ^ 2)) * (ρ + 3 * p / (c : ℝ) ^ 2) + Λ / 3 := by
  have hc : (c : ℝ) ≠ 0 := c.val_ne_zero
  have hg11 : S.a (x 0) ^ 2 / (1 - S.k * x 1 ^ 2) ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 ha) hkr
  rw [S.einsteinTensor ⟨x, ha, hr, hkr, hsin⟩ ha_diff ha2 1 1]
  simp only [metric, GeneralRelativity.perfectFluidStressEnergy, Matrix.of_apply, Fin.isValue,
    one_ne_zero,
    false_and, ↓reduceIte, mul_zero, zero_add]
  have hfac : -(2 * (deriv (deriv S.a) (x 0) / S.a (x 0)) + (deriv S.a (x 0) / S.a (x 0)) ^ 2
        + S.k / (S.a (x 0)) ^ 2) * (S.a (x 0) ^ 2 / (1 - S.k * x 1 ^ 2))
        + Λ * (S.a (x 0) ^ 2 / (1 - S.k * x 1 ^ 2))
      = 8 * Real.pi * G.val / (c : ℝ) ^ 4 * (p * (S.a (x 0) ^ 2 / (1 - S.k * x 1 ^ 2))) ↔
      -(2 * (deriv (deriv S.a) (x 0) / S.a (x 0)) + (deriv S.a (x 0) / S.a (x 0)) ^ 2
        + S.k / (S.a (x 0)) ^ 2) + Λ = 8 * Real.pi * G.val / (c : ℝ) ^ 4 * p := by
    constructor <;> intro h
    · exact mul_right_cancel₀ hg11 (by linear_combination h)
    · linear_combination (S.a (x 0) ^ 2 / (1 - S.k * x 1 ^ 2)) * h
  rw [hfac]
  exact spatial_coef_eq c Λ G.val ρ p (S.a (x 0)) (deriv S.a (x 0))
    (deriv (deriv S.a) (x 0)) S.k hc hf1

/-- Einstein's equation `G_{ij} + Λ g_{ij} = (8 π G / c⁴) T_{ij}` for an FLRW spacetime and a
comoving perfect fluid is equivalent to the first- and second-order Friedmann equations in
coordinate time `τ = c t`. -/
lemma einsteinTensor_iff_friedmann (S : FLRWSpacetime) (c : SpeedOfLight) (Λ : ℝ)
    (G : GravitationalConstant) (ρ p : ℝ) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0) (hr : x 1 ≠ 0)
    (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    (∀ i j, S.toCoordinateMetric.einsteinTensor x i j + Λ * S.metric x i j
        = 8 * Real.pi * G.val / (c : ℝ) ^ 4
          * GeneralRelativity.perfectFluidStressEnergy c ρ p (S.metric x) i j)
      ↔ ((deriv S.a (x 0) / S.a (x 0)) ^ 2
            = (8 * Real.pi * G.val / (3 * (c : ℝ) ^ 2)) * ρ - S.k / (S.a (x 0)) ^ 2 + Λ / 3)
          ∧ (deriv (deriv S.a) (x 0) / S.a (x 0)
              = -(4 * Real.pi * G.val / (3 * (c : ℝ) ^ 2)) * (ρ + 3 * p / (c : ℝ) ^ 2)
                + Λ / 3) := by
  have hc : (c : ℝ) ≠ 0 := c.val_ne_zero
  constructor
  · intro h
    have hf1 := (S.einsteinTensor_00_iff_friedmann c Λ G ρ p x ha hr hkr hsin ha_diff ha2).mp
      (h 0 0)
    exact ⟨hf1,
      (S.einsteinTensor_spatial_iff_friedmann c Λ G ρ p x ha hr hkr hsin ha_diff ha2 hf1).mp
        (h 1 1)⟩
  · rintro ⟨hf1, hf2⟩ i j
    rw [S.einsteinTensor ⟨x, ha, hr, hkr, hsin⟩ ha_diff ha2 i j]
    have hcoef : -(2 * (deriv (deriv S.a) (x 0) / S.a (x 0))
        + (deriv S.a (x 0) / S.a (x 0)) ^ 2 + S.k / (S.a (x 0)) ^ 2) + Λ
        = 8 * Real.pi * G.val / (c : ℝ) ^ 4 * p :=
      (spatial_coef_eq c Λ G.val ρ p (S.a (x 0)) (deriv S.a (x 0)) (deriv (deriv S.a) (x 0))
        S.k hc hf1).mpr hf2
    fin_cases i <;> fin_cases j <;> simp [metric, GeneralRelativity.perfectFluidStressEnergy]
    · have hrhs0 : 8 * Real.pi * G.val / (c : ℝ) ^ 4 * (ρ * (c : ℝ) ^ 2)
          = 3 * (8 * Real.pi * G.val / (3 * (c : ℝ) ^ 2) * ρ) := by
        field_simp [hc]
      rw [hrhs0]
      linarith
    · linear_combination (S.a (x 0) ^ 2 / (1 - S.k * x 1 ^ 2)) * hcoef
    · linear_combination (S.a (x 0) ^ 2 * x 1 ^ 2) * hcoef
    · linear_combination (S.a (x 0) ^ 2 * x 1 ^ 2 * Real.sin (x 2) ^ 2) * hcoef

end FLRWSpacetime

/-!

## B. Real-coordinate scale factor and Friedmann derivation

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

/-- Rescaling `τ = c t` between the coordinate-time and physical-time first-order Friedmann
equations. -/
private lemma coordinateTime_firstOrder_iff (c : SpeedOfLight) (Λ g ρ k adot a : ℝ)
    (hc : (c : ℝ) ≠ 0) (ha : a ≠ 0) :
    (adot / (c : ℝ) / a) ^ 2
        = 8 * Real.pi * g / (3 * (c : ℝ) ^ 2) * ρ - k / a ^ 2 + Λ / 3 ↔
      (adot / a) ^ 2 = 8 * Real.pi * g / 3 * ρ - k * (c : ℝ) ^ 2 / a ^ 2 + Λ * (c : ℝ) ^ 2 / 3 := by
  constructor <;> intro h
  · have := congrArg (· * (c : ℝ) ^ 2) h
    field_simp [hc, ha] at this ⊢
    linarith
  · have := congrArg (· / (c : ℝ) ^ 2) h
    field_simp [hc, ha] at this ⊢
    linarith

/-- Rescaling `τ = c t` between the coordinate-time and physical-time second-order Friedmann
equations. -/
private lemma coordinateTime_secondOrder_iff (c : SpeedOfLight) (Λ g ρ p addot a : ℝ)
    (hc : (c : ℝ) ≠ 0) (ha : a ≠ 0) :
    addot / (c : ℝ) ^ 2 / a
        = -(4 * Real.pi * g / (3 * (c : ℝ) ^ 2)) * (ρ + 3 * p / (c : ℝ) ^ 2) + Λ / 3 ↔
      addot / a = -(4 * Real.pi * g / 3) * (ρ + 3 * p / (c : ℝ) ^ 2) + Λ * (c : ℝ) ^ 2 / 3 := by
  constructor <;> intro h
  · have := congrArg (· * (c : ℝ) ^ 2) h
    field_simp [hc, ha] at this ⊢
    linarith
  · have := congrArg (· / (c : ℝ) ^ 2) h
    field_simp [hc, ha] at this ⊢
    linarith

/-- The FLRW Einstein field equations for a comoving cosmic fluid with speed of light `c` and
gravitational constant `G` are equivalent to the first- and second-order Friedmann equations of
`Physlib.Cosmology.FLRW`. -/
lemma einsteinTensor_ofCosmology_iff_friedmann (c : SpeedOfLight) (U : Cosmology.FLRW)
    (F : Cosmology.CosmicFluid) (Λ : ℝ) (G : GravitationalConstant) {t : Time} (ht : t ∈ U.I)
    (x : Fin 4 → ℝ) (hx0 : x 0 = (c : ℝ) * t.val) (hr : x 1 ≠ 0)
    (hkr : 1 - U.geometry.curvature * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    (∀ i j, (FLRWSpacetime.ofCosmology c U).toCoordinateMetric.einsteinTensor x i j
          + Λ * (FLRWSpacetime.ofCosmology c U).metric x i j
        = 8 * Real.pi * G.val / (c : ℝ) ^ 4
          * GeneralRelativity.perfectFluidStressEnergy c (F.ρ t) (F.p t)
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
  exact and_congr
    (coordinateTime_firstOrder_iff c Λ G.val (F.ρ t) U.geometry.curvature (Time.deriv U.a t)
      (U.a t) hc hau)
    (coordinateTime_secondOrder_iff c Λ G.val (F.ρ t) (F.p t) (Time.deriv (Time.deriv U.a) t)
      (U.a t) hc hau)

/-- If the FLRW Einstein equations hold across the model's open time interval at a regular spatial
chart point, then the model and cosmic fluid form a `Cosmology.FLRW.FriedmannSolution` (and hence
automatically satisfy the fluid continuity equation). -/
lemma friedmannSolution_of_einsteinTensor (c : SpeedOfLight) (U : Cosmology.FLRW)
    (F : Cosmology.CosmicFluid) (Λ : ℝ) (G : GravitationalConstant) (r₀ θ₀ : ℝ) (hr : r₀ ≠ 0)
    (hkr : 1 - U.geometry.curvature * r₀ ^ 2 ≠ 0) (hsin : Real.sin θ₀ ≠ 0)
    (heinst : ∀ t ∈ U.I, ∀ i j,
      let x : Fin 4 → ℝ := ![(c : ℝ) * t.val, r₀, θ₀, 0]
      (FLRWSpacetime.ofCosmology c U).toCoordinateMetric.einsteinTensor x i j
          + Λ * (FLRWSpacetime.ofCosmology c U).metric x i j
        = 8 * Real.pi * G.val / (c : ℝ) ^ 4
          * GeneralRelativity.perfectFluidStressEnergy c (F.ρ t) (F.p t)
            ((FLRWSpacetime.ofCosmology c U).metric x) i j) :
    U.FriedmannSolution F Λ G.val c := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · exact ((einsteinTensor_ofCosmology_iff_friedmann c U F Λ G ht ![(c : ℝ) * t.val, r₀, θ₀, 0]
      rfl hr hkr hsin).mp (heinst t ht)).1
  · exact ((einsteinTensor_ofCosmology_iff_friedmann c U F Λ G ht ![(c : ℝ) * t.val, r₀, θ₀, 0]
      rfl hr hkr hsin).mp (heinst t ht)).2


end FLRW

end Cosmology
