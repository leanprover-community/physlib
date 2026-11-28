/-
Copyright (c) 2026 Alex Vergara Gil.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/

module

public import PhyslibAlpha.Relativity.General.InitialData.CauchyInterfaces
public import PhyslibAlpha.Relativity.General.InitialData.SobolevInitialData
public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
public import PhyslibAlpha.Cosmology.FLRW.Basic
public import PhyslibAlpha.Cosmology.FLRW.FriedmannEquations
public import PhyslibAlpha.Relativity.General.SchwarzschildDeSitter.Basic
public import PhyslibAlpha.Relativity.General.Schwarzschild.CoordinateCurvature
public import PhyslibAlpha.Relativity.General.SchwarzschildDeSitter.CoordinateCurvature
public import PhyslibAlpha.Relativity.General.Kerr.RicciCurvature

/-!

# Explicit-solution cross-checks and an inhabited explicit development certificate

## i. Overview

This module instantiates `ExplicitDevelopmentObligations` with non-vacuous
4D Einstein field-equation + `t = 0` spatial-slice / initial-data statements and
proves that `explicitSolutionObligations` is a `ExplicitDevelopmentCertificate`,
recovering all four explicit spacetimes directly from the metric-pipeline
theorems and the curved 3D initial-data theorems in `SobolevInitialData`:

1. **Schwarzschild (`schwarzschild_explicit_development`)**:
   4D vacuum Einstein equation `einsteinOf (schwarzschildG M) (schwarzschildGinv M) = 0`
   together with `t = 0` spatial-metric agreement with `sdsSpatialMetric M 0`
   and vanishing nonlinear 3D Hamiltonian constraint.
2. **Schwarzschild–de Sitter (`sds_explicit_development`)**:
   4D cosmological Einstein equation `einsteinOf (sdsMetric M Λ) (sdsMetricInv M Λ) + Λ g = 0`
   together with `t = 0` spatial-metric agreement with `sdsSpatialMetric M Λ`
   and 3D spatial scalar curvature `³R = 2 Λ`.
3. **Kerr (`kerr_explicit_development`)**:
   4D rotating vacuum Einstein equation `einsteinOf (kerrMetric M a) (kerrMetricInv M a) = 0`
   together with symmetry and `t = 0` spatial/shift slice components.
4. **FLRW (`flrw_explicit_development`)**:
   4D Einstein–Friedmann equivalence `G_{ij} + Λ g_{ij} = 8 π G T_{ij}`
   together with the flat (`k = 0`) `t = 0` spatial scale-factor metric components.

## ii. Key results

- `explicitSolutionObligations` : the non-vacuous obligations for the four
  explicit spacetimes.
- `schwarzschild_explicit_development`, `sds_explicit_development`,
  `kerr_explicit_development`, `flrw_explicit_development` : the four
  explicit-solution verifications.
- `explicitSolutions_certificate` : the inhabited certificate.

## iii. Table of contents

- A. Explicit-solution obligations and verifications

## iv. References

* R. M. Wald, *General Relativity*, University of Chicago Press, 1984.
  [ref: wald_1984_general_relativity]
* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019,
  Ch. 5–7. [ref: Carroll1997]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity*,
  Academic Press, 1983. [ref: oneill_1983_semi_riemannian]

-/

@[expose] public section

namespace GeneralRelativity

/-! ## A. Explicit-solution obligations and verifications -/

/-- Kerr spacetime with mass `M` and spin `a`. -/
abbrev kerrSpacetime (M a : ℝ) : Kerr.KerrSpacetime :=
  ⟨M, a⟩

/-- Non-vacuous explicit-solution obligations pairing the full 4D Einstein
equations with `t = 0` spatial-slice restrictions and initial-data checks for
Schwarzschild, Schwarzschild–de Sitter, Kerr, and FLRW. -/
def explicitSolutionObligations : ExplicitDevelopmentObligations where
  schwarzschild :=
    ∀ (M : ℝ),
      (∀ (x : Fin 4 → ℝ), x 1 ≠ 0 → (schwarzschildSpacetime M).metricFn (x 1) ≠ 0 →
        Real.sin (x 2) ≠ 0 → ∀ i j : Fin 4,
          CoordinateCurvature.einsteinTensor ((schwarzschildSpacetime M).metric)
            ((schwarzschildSpacetime M).metricInv) x i j = 0) ∧
      (∀ (r θ φ : ℝ), r ≠ 0 → (schwarzschildSpacetime M).metricFn r ≠ 0 → Real.sin θ ≠ 0 →
        (∀ i j : Fin 3,
          (schwarzschildSpacetime M).metric ![0, r, θ, φ] i.succ j.succ =
            sdsSpatialMetric M 0 ![r, θ, φ] i j) ∧
        hamiltonianConstraintOf (sdsSpatialMetric M 0) (sdsSpatialMetricInv M 0)
          (fun _ => 0) ![r, θ, φ] = 0)
  deSitter :=
    ∀ (M Λ : ℝ),
      (∀ (x : Fin 4 → ℝ), x 1 ≠ 0 → (sdsSpacetime M Λ).metricFn (x 1) ≠ 0 →
        Real.sin (x 2) ≠ 0 → ∀ i j : Fin 4,
          CoordinateCurvature.einsteinTensor ((sdsSpacetime M Λ).metric)
            ((sdsSpacetime M Λ).metricInv) x i j +
            Λ * (sdsSpacetime M Λ).metric x i j = 0) ∧
      (∀ (r θ φ : ℝ), r ≠ 0 → (sdsSpacetime M Λ).metricFn r ≠ 0 → Real.sin θ ≠ 0 →
        (∀ i j : Fin 3,
          (sdsSpacetime M Λ).metric ![0, r, θ, φ] i.succ j.succ =
            sdsSpatialMetric M Λ ![r, θ, φ] i j) ∧
        spatialScalarCurvOf (sdsSpatialMetric M Λ) (sdsSpatialMetricInv M Λ) ![r, θ, φ] =
          2 * Λ)
  kerr :=
    ∀ (M a : ℝ),
      (∀ (x : Fin 4 → ℝ), (kerrSpacetime M a).sigma (x 1) (x 2) ≠ 0 →
        (kerrSpacetime M a).delta (x 1) ≠ 0 → Real.sin (x 2) ≠ 0 → ∀ i j : Fin 4,
          CoordinateCurvature.einsteinTensor ((kerrSpacetime M a).metric)
            ((kerrSpacetime M a).metricInv) x i j = 0) ∧
      (∀ (x : Fin 4 → ℝ) (i j : Fin 4),
        (kerrSpacetime M a).metric x i j = (kerrSpacetime M a).metric x j i) ∧
      (∀ (r θ φ : ℝ),
        (kerrSpacetime M a).metric ![0, r, θ, φ] 0 3 =
          -(2 * M * a * r * Real.sin θ ^ 2 / (kerrSpacetime M a).sigma r θ))
  flrw :=
    ∀ (a : ℝ → ℝ) (k Λ : ℝ) (c : SpeedOfLight) (G : GravitationalConstant) (ρ p : ℝ)
      (x : Fin 4 → ℝ),
      a (x 0) ≠ 0 → x 1 ≠ 0 → 1 - k * (x 1) ^ 2 ≠ 0 → Real.sin (x 2) ≠ 0 →
      (∀ᶠ t in nhds (x 0), DifferentiableAt ℝ a t) →
      DifferentiableAt ℝ (deriv a) (x 0) →
      ((deriv a (x 0) / a (x 0)) ^ 2 =
          (8 * Real.pi * G.val / (3 * (c : ℝ) ^ 2)) * ρ - k / a (x 0) ^ 2 + Λ / 3 ∧
        deriv (deriv a) (x 0) / a (x 0) =
          -(4 * Real.pi * G.val / (3 * (c : ℝ) ^ 2)) * (ρ + 3 * p / (c : ℝ) ^ 2) + Λ / 3) →
      (∀ i j : Fin 4,
        (⟨a, k⟩ : Cosmology.FLRW.FLRWSpacetime).toCoordinateMetric.einsteinTensor x i j +
          Λ * (⟨a, k⟩ : Cosmology.FLRW.FLRWSpacetime).metric x i j =
          8 * Real.pi * G.val / (c : ℝ) ^ 4 *
            GeneralRelativity.perfectFluidStressEnergy c ρ p
              ((⟨a, k⟩ : Cosmology.FLRW.FLRWSpacetime).metric x) i j) ∧
      (∀ (r θ φ : ℝ),
        (⟨a, 0⟩ : Cosmology.FLRW.FLRWSpacetime).metric ![0, r, θ, φ] 1 1 = a 0 ^ 2 ∧
        (⟨a, 0⟩ : Cosmology.FLRW.FLRWSpacetime).metric ![0, r, θ, φ] 2 2 = a 0 ^ 2 * r ^ 2 ∧
        (⟨a, 0⟩ : Cosmology.FLRW.FLRWSpacetime).metric ![0, r, θ, φ] 3 3 =
          a 0 ^ 2 * r ^ 2 * Real.sin θ ^ 2)

/-- Schwarzschild explicit-development verification: 4D vacuum Einstein equation,
`t = 0` spatial slice metric match, and 3D nonlinear Hamiltonian constraint. -/
lemma schwarzschild_explicit_development : explicitSolutionObligations.schwarzschild := by
  intro M
  refine ⟨fun x hr hf hsin i j => ?_, fun r θ φ hr hf hsin => ⟨fun i j => ?_, ?_⟩⟩
  · have hf' : (schwarzschildSpacetime M).toStaticSpherical.metricFn (x 1) ≠ 0 := by
      simpa using hf
    have h := Schwarzschild.SchwarzschildSpacetime.einsteinTensor_eq_zero
      (schwarzschildSpacetime M) ⟨x, hr, hf', hsin⟩ i j
    simpa using h
  · fin_cases i <;> fin_cases j <;>
      simp [schwarzschildSpacetime, Schwarzschild.SchwarzschildSpacetime.metric,
        StaticSpherical.StaticSphericalMetric.metric, sdsSpatialMetric,
        Schwarzschild.SchwarzschildSpacetime.metricFn,
        Schwarzschild.SchwarzschildSpacetime.toStaticSpherical,
        SchwarzschildDeSitter.SchwarzschildDeSitterSpacetime.metricFn]
  · exact schwarzschild_spatial_hamiltonian_zero M ![r, θ, φ]
      (by simpa using hr) (by simpa using hf) (by simpa using hsin)

/-- Schwarzschild–de Sitter explicit-development verification: 4D cosmological
Einstein equation `G + Λ g = 0`, `t = 0` spatial slice metric match, and 3D
spatial scalar curvature `³R = 2 Λ`. -/
lemma sds_explicit_development : explicitSolutionObligations.deSitter := by
  intro M Λ
  refine ⟨fun x hr hf hsin i j => ?_, fun r θ φ hr hf hsin => ⟨fun i j => ?_, ?_⟩⟩
  · have hf' : (sdsSpacetime M Λ).toStaticSpherical.metricFn (x 1) ≠ 0 := by
      simpa using hf
    have h := SchwarzschildDeSitter.SchwarzschildDeSitterSpacetime.einsteinTensor_eq
      (sdsSpacetime M Λ) ⟨x, hr, hf', hsin⟩ i j
    have h' : CoordinateCurvature.einsteinTensor (sdsSpacetime M Λ).metric
        (sdsSpacetime M Λ).metricInv x i j = -(Λ * (sdsSpacetime M Λ).metric x i j) := by
      simpa using h
    linarith
  · fin_cases i <;> fin_cases j <;>
      simp [sdsSpacetime, SchwarzschildDeSitter.SchwarzschildDeSitterSpacetime.metric,
        StaticSpherical.StaticSphericalMetric.metric, sdsSpatialMetric,
        SchwarzschildDeSitter.SchwarzschildDeSitterSpacetime.toStaticSpherical,
        SchwarzschildDeSitter.SchwarzschildDeSitterSpacetime.metricFn]
  · exact spatialScalarCurvOf_sdsSpatial M Λ ![r, θ, φ]
      (by simpa using hr) (by simpa using hf) (by simpa using hsin)

/-- Kerr explicit-development verification: 4D rotating vacuum Einstein
equation `G = 0`, metric symmetry, and `t = 0` Boyer–Lindquist shift block. -/
lemma kerr_explicit_development : explicitSolutionObligations.kerr := by
  intro M a
  refine ⟨fun x hsig hdel hs i j =>
      (kerrSpacetime M a).einsteinTensor_eq_zero x hsig hdel hs i j,
    fun x i j => ((kerrSpacetime M a).metric_symm x).apply j i,
    fun r θ φ => ?_⟩
  simp [kerrSpacetime, Kerr.KerrSpacetime.metric]

/-- FLRW explicit-development verification: 4D Einstein–Friedmann equivalence
`G + Λ g = 8πG T` and `t = 0` flat (`k = 0`) spatial scale-factor metric components. -/
lemma flrw_explicit_development : explicitSolutionObligations.flrw := by
  intro a k Λ c G ρ p x ha hr hkr hsin ha_diff ha2 hfried
  refine ⟨(Cosmology.FLRW.FLRWSpacetime.einsteinTensor_iff_friedmann
      (⟨a, k⟩ : Cosmology.FLRW.FLRWSpacetime) c Λ G ρ p x
      ha hr hkr hsin ha_diff ha2).mpr hfried,
    fun r θ φ => ?_⟩
  simp [Cosmology.FLRW.FLRWSpacetime.metric]

/-- **Explicit-development certificate**: the inhabited certificate for
`explicitSolutionObligations`, with kernel-verified proofs for Schwarzschild,
Schwarzschild–de Sitter, Kerr, and FLRW. -/
lemma explicitSolutions_certificate :
    ExplicitDevelopmentCertificate explicitSolutionObligations where
  schwarzschild := schwarzschild_explicit_development
  deSitter := sds_explicit_development
  kerr := kerr_explicit_development
  flrw := flrw_explicit_development

end GeneralRelativity
