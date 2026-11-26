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

/-!

# Bridge between FLRW metric pipeline and `Physlib.Cosmology.FLRW`

Constructs `FLRWSpacetime.ofCosmology` from `U : Cosmology.FLRW` and deduces
`Cosmology.FLRW.FriedmannSolution` directly from the coordinate-pipeline Einstein equation.

## i. Overview

Whereas `Physlib.Cosmology.FLRW` postulates the two Friedmann equations as ODEs for
`U : Cosmology.FLRW`, this module bridges `U` into `FLRWSpacetime.ofCosmology U` with scale factor
`flrwScaleFn U := fun τ => U.a ⟨τ⟩` and proves that the coordinate-pipeline Einstein equation for a
comoving `Cosmology.CosmicFluid` is equivalent to `FirstOrderFriedmann` and `SecondOrderFriedmann`
in geometric units `c = 1`, directly constructing `U.FriedmannSolution F Λ G 1`.

## ii. Key results

- `flrwScaleFn`, `FLRWSpacetime.ofCosmology` : real-coordinate scale factor and FLRW spacetime
  from `Cosmology.FLRW`.
- `eventually_differentiableAt_flrwScaleFn`, `deriv_flrwScaleFn_eq`,
  `hasDerivAt_deriv_flrwScaleFn` : differentiation bridge between `Time.deriv` and real `deriv`.
- `einsteinTensorOf_ofCosmology_iff_friedmann`, `friedmannSolution_of_einsteinTensorOf`,
  `friedmannSolution_of_einsteinTensorOf_G` : equivalence with `Physlib.Cosmology.FLRW` Friedmann
  equations and `FriedmannSolution` constructor.

## iii. Table of contents

- A. Real-coordinate scale factor and `Cosmology.FLRW` bridge

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

open GeneralRelativity.Pipeline

/-!

## A. Real-coordinate scale factor and `Cosmology.FLRW` bridge

Lifting `U.a : Time → ℝ` to `flrwScaleFn U : ℝ → ℝ` lets `FLRWSpacetime.ofCosmology U` connect the
metric pipeline to `Cosmology.FLRW.FriedmannEquation` and `Cosmology.FLRW.FriedmannSolution`.

-/

/-- The real-coordinate scale factor `τ ↦ U.a ⟨τ⟩` extracted from `U : Cosmology.FLRW`. -/
noncomputable def flrwScaleFn (U : Cosmology.FLRW) : ℝ → ℝ := fun τ => U.a ⟨τ⟩

/-- Construct an `FLRWSpacetime` directly from `U : Cosmology.FLRW`. -/
noncomputable def FLRWSpacetime.ofCosmology (U : Cosmology.FLRW) : FLRWSpacetime where
  a := flrwScaleFn U
  k := U.geometry.curvature

/-- Neighbourhood differentiability of `flrwScaleFn U` at any time `t ∈ U.I`. -/
lemma eventually_differentiableAt_flrwScaleFn (U : Cosmology.FLRW) {t : Time} (ht : t ∈ U.I) :
    ∀ᶠ τ in nhds t.val, DifferentiableAt ℝ (flrwScaleFn U) τ := by
  have hmem : ∀ᶠ τ in nhds t.val, (⟨τ⟩ : Time) ∈ U.I :=
    (Time.toRealCLE.symm.continuous.tendsto t.val).eventually (U.isOpen_I.mem_nhds ht)
  filter_upwards [hmem] with τ hτ
  exact (Time.hasDerivAt_mk_of_differentiableAt (U.differentiableAt_a hτ)).differentiableAt

/-- First derivative of `flrwScaleFn U` equals `Time.deriv U.a`. -/
lemma deriv_flrwScaleFn_eq (U : Cosmology.FLRW) {t : Time} (ht : t ∈ U.I) :
    deriv (flrwScaleFn U) t.val = Time.deriv U.a t :=
  (Time.hasDerivAt_mk_of_differentiableAt (U.differentiableAt_a ht)).deriv

/-- `flrwScaleFn U` is twice differentiable at `t.val` with second derivative
`Time.deriv (Time.deriv U.a) t`. -/
lemma hasDerivAt_deriv_flrwScaleFn (U : Cosmology.FLRW) {t : Time} (ht : t ∈ U.I) :
    HasDerivAt (deriv (flrwScaleFn U)) (Time.deriv (Time.deriv U.a) t) t.val := by
  have hmem : ∀ᶠ τ in nhds t.val, (⟨τ⟩ : Time) ∈ U.I :=
    (Time.toRealCLE.symm.continuous.tendsto t.val).eventually (U.isOpen_I.mem_nhds ht)
  have heq : deriv (flrwScaleFn U) =ᶠ[nhds t.val] fun τ => Time.deriv U.a ⟨τ⟩ := by
    filter_upwards [hmem] with τ hτ
    exact (Time.hasDerivAt_mk_of_differentiableAt (U.differentiableAt_a hτ)).deriv
  have hderiv := Time.hasDerivAt_mk_of_differentiableAt (U.differentiableAt_deriv_a ht)
  exact hderiv.congr_of_eventuallyEq heq

/-- Bridge to `Physlib.Cosmology.FLRW`: the coordinate-pipeline Einstein equation for
`FLRWSpacetime.ofCosmology U` is equivalent to `FirstOrderFriedmann` and `SecondOrderFriedmann`
(`c = 1`) at `t ∈ U.I`. -/
lemma einsteinTensorOf_ofCosmology_iff_friedmann (U : Cosmology.FLRW) (F : Cosmology.CosmicFluid)
    (Λ G : ℝ) {t : Time} (ht : t ∈ U.I) (x : Fin 4 → ℝ) (hx0 : x 0 = t.val) (hr : x 1 ≠ 0)
    (hkr : 1 - U.geometry.curvature * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    (∀ i j, Pipeline.einsteinTensorOf (FLRWSpacetime.ofCosmology U).metric
          (FLRWSpacetime.ofCosmology U).metricInv x i j
          + Λ * (FLRWSpacetime.ofCosmology U).metric x i j
        = 8 * Real.pi * G * perfectFluidT (F.ρ t) (F.p t)
            ((FLRWSpacetime.ofCosmology U).metric x) i j)
      ↔ Cosmology.FLRW.FriedmannEquation.FirstOrderFriedmann U.a F.ρ U.geometry.curvature Λ G 1 t
          ∧ Cosmology.FLRW.FriedmannEquation.SecondOrderFriedmann U.a F.ρ F.p Λ G 1 t := by
  have ha : (FLRWSpacetime.ofCosmology U).a (x 0) ≠ 0 := by
    rw [hx0]
    exact U.a_ne_zero ht
  have ha_diff : ∀ᶠ τ in nhds (x 0), DifferentiableAt ℝ (FLRWSpacetime.ofCosmology U).a τ := by
    rw [hx0]
    exact eventually_differentiableAt_flrwScaleFn U ht
  have hd2 := hasDerivAt_deriv_flrwScaleFn U ht
  have ha2 : DifferentiableAt ℝ (deriv (FLRWSpacetime.ofCosmology U).a) (x 0) := by
    rw [hx0]
    exact hd2.differentiableAt
  have hd1_eq : deriv (flrwScaleFn U) (x 0) = Time.deriv U.a t := by
    rw [hx0]
    exact deriv_flrwScaleFn_eq U ht
  have hd2_eq :
      deriv (deriv (flrwScaleFn U)) (x 0) = Time.deriv (Time.deriv U.a) t := by
    rw [hx0]
    exact hd2.deriv
  have ha0_eq : flrwScaleFn U (x 0) = U.a t := by
    rw [hx0]
    rfl
  rw [(FLRWSpacetime.ofCosmology U).einsteinTensorOf_iff_friedmann Λ G (F.ρ t) (F.p t) x
    ha hr hkr hsin ha_diff ha2]
  simp only [Cosmology.FLRW.FriedmannEquation.FirstOrderFriedmann,
    Cosmology.FLRW.FriedmannEquation.SecondOrderFriedmann, SpeedOfLight.val_one, one_pow,
    mul_one, div_one, FLRWSpacetime.ofCosmology, ha0_eq, hd1_eq, hd2_eq]

/-- If the FLRW Einstein equation holds across `U.I` (say at a spatial chart point `r₀, θ₀`),
then `U` and `F` form a `Cosmology.FLRW.FriedmannSolution F Λ G 1` (and hence automatically satisfy
the fluid continuity equation by `Cosmology.FLRW.FriedmannSolution.continuityEquation`). -/
lemma friedmannSolution_of_einsteinTensorOf (U : Cosmology.FLRW) (F : Cosmology.CosmicFluid)
    (Λ G r₀ θ₀ : ℝ) (hr : r₀ ≠ 0) (hkr : 1 - U.geometry.curvature * r₀ ^ 2 ≠ 0)
    (hsin : Real.sin θ₀ ≠ 0)
    (heinst : ∀ t ∈ U.I, ∀ i j,
      let x : Fin 4 → ℝ := ![t.val, r₀, θ₀, 0]
      Pipeline.einsteinTensorOf (FLRWSpacetime.ofCosmology U).metric
          (FLRWSpacetime.ofCosmology U).metricInv x i j
          + Λ * (FLRWSpacetime.ofCosmology U).metric x i j
        = 8 * Real.pi * G * perfectFluidT (F.ρ t) (F.p t)
            ((FLRWSpacetime.ofCosmology U).metric x) i j) :
    U.FriedmannSolution F Λ G 1 := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · exact ((einsteinTensorOf_ofCosmology_iff_friedmann U F Λ G ht ![t.val, r₀, θ₀, 0]
      rfl hr hkr hsin).mp (heinst t ht)).1
  · exact ((einsteinTensorOf_ofCosmology_iff_friedmann U F Λ G ht ![t.val, r₀, θ₀, 0]
      rfl hr hkr hsin).mp (heinst t ht)).2

/-- Overload of `friedmannSolution_of_einsteinTensorOf` taking the Newtonian constant as a
`GravitationalConstant`. -/
lemma friedmannSolution_of_einsteinTensorOf_G (U : Cosmology.FLRW) (F : Cosmology.CosmicFluid)
    (Λ : ℝ) (G : GravitationalConstant) (r₀ θ₀ : ℝ) (hr : r₀ ≠ 0)
    (hkr : 1 - U.geometry.curvature * r₀ ^ 2 ≠ 0)
    (hsin : Real.sin θ₀ ≠ 0)
    (heinst : ∀ t ∈ U.I, ∀ i j,
      let x : Fin 4 → ℝ := ![t.val, r₀, θ₀, 0]
      Pipeline.einsteinTensorOf (FLRWSpacetime.ofCosmology U).metric
          (FLRWSpacetime.ofCosmology U).metricInv x i j
          + Λ * (FLRWSpacetime.ofCosmology U).metric x i j
        = 8 * Real.pi * G.val * perfectFluidT (F.ρ t) (F.p t)
            ((FLRWSpacetime.ofCosmology U).metric x) i j) :
    U.FriedmannSolution F Λ G.val 1 :=
  friedmannSolution_of_einsteinTensorOf U F Λ G.val r₀ θ₀ hr hkr hsin heinst

end FLRW

end GeneralRelativity
