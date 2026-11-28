/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import PhyslibAlpha.Relativity.General.Bianchi
public import PhyslibAlpha.Relativity.General.InitialData.InitialDataInterface
public import PhyslibAlpha.Relativity.General.InitialData.ReducedWave3D
public import PhyslibAlpha.Relativity.General.InitialData.WaveEnergy
public import PhyslibAlpha.Relativity.General.InitialData.WaveEnergy3D
public import PhyslibAlpha.Relativity.General.Schwarzschild.Basic
public import PhyslibAlpha.Relativity.General.SchwarzschildDeSitter.Basic
public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!

# Sobolev H¹ norms, embedding/trace estimates, and nonlinear constraint solutions

## i. Overview

This module advances M2 beyond the flat chart interface by supplying:

* 1D and 3D-box Sobolev `H¹` energy norms (`sobolevH1NormSq1D`, `sobolevH1NormSq3D`)
  with nonnegativity and component dominance inequalities;
* the 1D Sobolev embedding `H¹([0, L]) ↪ L^∞([0, L])` (`sobolev_embedding_1D`),
  proved from the Fundamental Theorem of Calculus and Cauchy–Schwarz;
* the 1D boundary trace estimate (`trace_estimate_1D`);
* derived 3D geometric curvature (`spatialRiemannOf`, `spatialRicciOf`,
  `spatialScalarCurvOf`) and ADM constraints (`hamiltonianConstraintOf`,
  `momentumConstraintOf`) computed directly from a 3-metric field `(h, hinv)`
  and extrinsic curvature field `K`, without supplying `R3` or `dK` by hand;
* three genuine nonlinear constraint solutions: the Brill–Lindquist / Lichnerowicz
  harmonic conformal factor (`spatialLaplacian3D_brillLindquistPhi`), the curved
  3D Schwarzschild–de Sitter spatial slice (`spatialScalarCurvOf_sdsSpatial = 2 Λ`,
  vacuum at `Λ = 0` with nonzero spatial Ricci curvature), and flat FLRW initial data.


## ii. Key results

- `sobolevH1NormSq1D`
- `sobolev_embedding_1D`
- `trace_estimate_1D`
- `sobolevH1NormSq3D`

## iii. Table of contents

- A. 1D Sobolev H¹ norm, Sobolev embedding, and trace estimate
- B. 3D-box Sobolev H¹ norm
- C. Derived 3D spatial curvature and ADM constraint operators
- D. Solving the nonlinear constraints

## iv. References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, §5.6.
-/
@[expose] public section

namespace GeneralRelativity

open MeasureTheory Filter Topology
open scoped Interval

/-- Coordinate partial derivative of a `Real.sin · ^ 2` slice: `(sin² θ)' = 2 sin θ cos θ`.
The upstream `hasDerivAt_sin_sq` helper was dropped in the
refactor, so it is restated here. -/
lemma hasDerivAt_sin_sq (θ : ℝ) :
    HasDerivAt (fun t => Real.sin t ^ 2) (2 * Real.sin θ * Real.cos θ) θ :=
  ((hasDerivAt_pow 2 (Real.sin θ)).comp θ (Real.hasDerivAt_sin θ)).congr_deriv (by ring)

/-- Schwarzschild spacetime of mass `M`, named so lapse expressions read as
`(schwarzschildSpacetime M).metricFn r`. -/
abbrev schwarzschildSpacetime (M : ℝ) : Schwarzschild.SchwarzschildSpacetime :=
  ⟨M⟩

/-- Schwarzschild–de Sitter spacetime of mass `M` and cosmological constant
`Λ`, named so lapse expressions read as `(sdsSpacetime M Λ).metricFn r`. -/
abbrev sdsSpacetime (M Λ : ℝ) : SchwarzschildDeSitter.SchwarzschildDeSitterSpacetime :=
  ⟨M, Λ⟩

/-! ## A. 1D Sobolev H¹ norm, Sobolev embedding, and trace estimate -/

/-- Squared `H¹([a, b])` Sobolev norm `∫ u² + ∫ (u')²`. -/
noncomputable def sobolevH1NormSq1D (u u' : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (∫ x in a..b, u x ^ 2) + (∫ x in a..b, u' x ^ 2)

lemma sobolevH1NormSq1D_nonneg (u u' : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ sobolevH1NormSq1D u u' a b := by
  unfold sobolevH1NormSq1D
  exact add_nonneg
    (intervalIntegral.integral_nonneg hab fun _ _ => sq_nonneg _)
    (intervalIntegral.integral_nonneg hab fun _ _ => sq_nonneg _)

lemma l2_le_sobolevH1_1D (u u' : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, u x ^ 2) ≤ sobolevH1NormSq1D u u' a b := by
  unfold sobolevH1NormSq1D
  have h := intervalIntegral.integral_nonneg (μ := volume) hab (f := fun x => u' x ^ 2)
    fun _ _ => sq_nonneg _
  linarith

lemma deriv_l2_le_sobolevH1_1D (u u' : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, u' x ^ 2) ≤ sobolevH1NormSq1D u u' a b := by
  unfold sobolevH1NormSq1D
  have h := intervalIntegral.integral_nonneg (μ := volume) hab (f := fun x => u x ^ 2)
    fun _ _ => sq_nonneg _
  linarith

/-- Cauchy–Schwarz inequality on `[0, x]`: `(∫₀ˣ f)² ≤ x ∫₀ˣ f²`. -/
lemma sq_intervalIntegral_le (f : ℝ → ℝ) (hf : Continuous f) {x : ℝ} (hx : 0 ≤ x) :
    (∫ s in (0 : ℝ)..x, f s) ^ 2 ≤ x * ∫ s in (0 : ℝ)..x, f s ^ 2 := by
  let B : ℝ := ∫ s in (0 : ℝ)..x, f s
  let C : ℝ := ∫ s in (0 : ℝ)..x, f s ^ 2
  have hC : 0 ≤ C := intervalIntegral.integral_nonneg hx fun _ _ => sq_nonneg _
  have hquad : ∀ t : ℝ, 0 ≤ C * t ^ 2 - 2 * B * t + x := by
    intro t
    have hi : 0 ≤ ∫ s in (0 : ℝ)..x, (t * f s - 1) ^ 2 :=
      intervalIntegral.integral_nonneg hx fun _ _ => sq_nonneg _
    have hexp : (fun s : ℝ => (t * f s - 1) ^ 2) =
        fun s : ℝ => t ^ 2 * f s ^ 2 + (-(2 * t) * f s + 1) := by
      funext s
      ring
    have int1 : IntervalIntegrable (fun s : ℝ => t ^ 2 * f s ^ 2) volume 0 x :=
      (continuous_const.mul (hf.pow 2)).intervalIntegrable 0 x
    have int2 : IntervalIntegrable (fun s : ℝ => -(2 * t) * f s) volume 0 x :=
      (continuous_const.mul hf).intervalIntegrable 0 x
    have int3 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 x :=
      continuous_const.intervalIntegrable 0 x
    rw [hexp, intervalIntegral.integral_add int1 (int2.add int3),
      intervalIntegral.integral_add int2 int3,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const] at hi
    simp only [smul_eq_mul, sub_zero] at hi
    change 0 ≤ t ^ 2 * C + (-(2 * t) * B + x * 1) at hi
    linarith
  by_cases hC0 : C = 0
  · by_cases hB0 : B = 0
    · simp [B, hB0, C, hC0]
    · have hbad := hquad ((x + 1) / (2 * B))
      dsimp only [C, B] at hbad ⊢
      simp only [C] at hC0
      rw [hC0, zero_mul, zero_sub] at hbad
      have hsimp : 2 * (∫ s in (0 : ℝ)..x, f s) * ((x + 1) / (2 * (∫ s in (0 : ℝ)..x, f s))) =
          x + 1 := by
        change (∫ s in (0 : ℝ)..x, f s) ≠ 0 at hB0
        field_simp [hB0]
      linarith
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have hmin := hquad (B / C)
    have hmul : 0 ≤ C * (C * (B / C) ^ 2 - 2 * B * (B / C) + x) :=
      mul_nonneg hC hmin
    have halg : C * (C * (B / C) ^ 2 - 2 * B * (B / C) + x) = C * x - B ^ 2 := by
      field_simp [hC0]
      ring
    rw [halg] at hmul
    change B ^ 2 ≤ x * C
    linarith

/-- **1D Sobolev embedding `H¹([0, L]) ↪ L^∞([0, L])`**:
if `u 0 = 0`, then `u(x)² ≤ L ∫₀ᴸ (u')²` for every `x ∈ [0, L]`. -/
lemma sobolev_embedding_1D (u u' : ℝ → ℝ)
    (hderiv : ∀ s, HasDerivAt u (u' s) s) (hu' : Continuous u')
    (hu0 : u 0 = 0) {x L : ℝ} (hx0 : 0 ≤ x) (hxL : x ≤ L) :
    u x ^ 2 ≤ L * ∫ s in (0 : ℝ)..L, u' s ^ 2 := by
  have hint_x : IntervalIntegrable u' volume 0 x := hu'.intervalIntegrable 0 x
  have hftc : (∫ s in (0 : ℝ)..x, u' s) = u x := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hderiv s) hint_x
    linarith
  have hcs := sq_intervalIntegral_le u' hu' hx0
  rw [hftc] at hcs
  have hint2_x : IntervalIntegrable (fun s => u' s ^ 2) volume 0 x :=
    (hu'.pow 2).intervalIntegrable 0 x
  have hint2_L : IntervalIntegrable (fun s => u' s ^ 2) volume x L :=
    (hu'.pow 2).intervalIntegrable x L
  have htail : 0 ≤ ∫ s in x..L, u' s ^ 2 :=
    intervalIntegral.integral_nonneg hxL fun _ _ => sq_nonneg _
  have hsplit : (∫ s in (0 : ℝ)..x, u' s ^ 2) + (∫ s in x..L, u' s ^ 2) =
      ∫ s in (0 : ℝ)..L, u' s ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals hint2_x hint2_L
  have hmono_int : (∫ s in (0 : ℝ)..x, u' s ^ 2) ≤ ∫ s in (0 : ℝ)..L, u' s ^ 2 := by
    linarith
  have hmono_x : x * (∫ s in (0 : ℝ)..x, u' s ^ 2) ≤
      L * (∫ s in (0 : ℝ)..L, u' s ^ 2) :=
    mul_le_mul hxL hmono_int
      (intervalIntegral.integral_nonneg hx0 fun _ _ => sq_nonneg _)
      (le_trans hx0 hxL)
  exact le_trans hcs hmono_x

/-- **1D Sobolev trace estimate**: the boundary value `u(0)²` is controlled by
the `H¹([0, L])` norm:
`u(0)² ≤ (2 / L) ∫₀ᴸ u² + 2 L ∫₀ᴸ (u')²`. -/
lemma trace_estimate_1D (u u' : ℝ → ℝ)
    (hderiv : ∀ s, HasDerivAt u (u' s) s) (hu' : Continuous u')
    {L : ℝ} (hL : 0 < L) :
    u 0 ^ 2 ≤ (2 / L) * (∫ s in (0 : ℝ)..L, u s ^ 2) +
      2 * L * (∫ s in (0 : ℝ)..L, u' s ^ 2) := by
  have huC : Continuous u := continuous_iff_continuousAt.mpr fun s => (hderiv s).continuousAt
  have hint2_u : IntervalIntegrable (fun s => u s ^ 2) volume 0 L :=
    (huC.pow 2).intervalIntegrable 0 L
  have hint2_u' : IntervalIntegrable (fun s => u' s ^ 2) volume 0 L :=
    (hu'.pow 2).intervalIntegrable 0 L
  have hpt : ∀ y ∈ Set.Icc (0 : ℝ) L,
      u 0 ^ 2 ≤ 2 * u y ^ 2 + 2 * L * ∫ s in (0 : ℝ)..L, u' s ^ 2 := by
    intro y hy
    have hftc : (∫ s in (0 : ℝ)..y, u' s) = u y - u 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s _ => hderiv s) (hu'.intervalIntegrable 0 y)
    have hcs := sq_intervalIntegral_le u' hu' hy.1
    have hmono : (∫ s in (0 : ℝ)..y, u' s ^ 2) ≤ ∫ s in (0 : ℝ)..L, u' s ^ 2 := by
      have h1 : IntervalIntegrable (fun s : ℝ => u' s ^ 2) volume (0 : ℝ) y :=
        (hu'.pow 2).intervalIntegrable 0 y
      have h2 : IntervalIntegrable (fun s : ℝ => u' s ^ 2) volume y L :=
        (hu'.pow 2).intervalIntegrable y L
      have h3 := intervalIntegral.integral_add_adjacent_intervals h1 h2
      have h4 : 0 ≤ ∫ s in y..L, u' s ^ 2 :=
        intervalIntegral.integral_nonneg hy.2 fun _ _ => sq_nonneg _
      linarith
    have hyC : 0 ≤ ∫ s in (0 : ℝ)..y, u' s ^ 2 :=
      intervalIntegral.integral_nonneg hy.1 fun _ _ => sq_nonneg _
    have hsq : (u y - u 0) ^ 2 ≤ L * ∫ s in (0 : ℝ)..L, u' s ^ 2 := by
      rw [← hftc]
      exact le_trans hcs (mul_le_mul hy.2 hmono hyC hL.le)
    have htwo : u 0 ^ 2 ≤ 2 * u y ^ 2 + 2 * (u y - u 0) ^ 2 := by
      nlinarith [sq_nonneg (u 0 - 2 * u y)]
    linarith
  have hconst_int : IntervalIntegrable (fun _ : ℝ => u 0 ^ 2) volume 0 L :=
    continuous_const.intervalIntegrable 0 L
  have hrhs_int : IntervalIntegrable
      (fun y : ℝ => 2 * u y ^ 2 + 2 * L * ∫ s in (0 : ℝ)..L, u' s ^ 2) volume 0 L :=
    (hint2_u.const_mul 2).add (continuous_const.intervalIntegrable 0 L)
  have hint_le := intervalIntegral.integral_mono_on hL.le hconst_int hrhs_int hpt
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (hint2_u.const_mul 2) (continuous_const.intervalIntegrable 0 L),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hint_le
  simp only [smul_eq_mul, sub_zero] at hint_le
  have hdiv : L * u 0 ^ 2 ≤
      2 * (∫ s in (0 : ℝ)..L, u s ^ 2) + 2 * L * L * (∫ s in (0 : ℝ)..L, u' s ^ 2) := by
    linarith
  have hpos := div_le_div_of_nonneg_right hdiv hL.le
  have hL0 : L ≠ 0 := hL.ne'
  have hcalc1 : (L * u 0 ^ 2) / L = u 0 ^ 2 := by field_simp [hL0]
  have hcalc2 : (2 * (∫ s in (0 : ℝ)..L, u s ^ 2) +
        2 * L * L * (∫ s in (0 : ℝ)..L, u' s ^ 2)) / L =
      (2 / L) * (∫ s in (0 : ℝ)..L, u s ^ 2) +
        2 * L * (∫ s in (0 : ℝ)..L, u' s ^ 2) := by
    field_simp [hL0]
  rw [hcalc1, hcalc2] at hpos
  exact hpos

/-! ## B. 3D-box Sobolev H¹ norm -/

/-- Squared `H¹` norm on a closed 3D box `I`: `∫_I (u² + ∑ᵢ (∂ᵢu)²) dx`. -/
noncomputable def sobolevH1NormSq3D
    (u : Space3 → ℝ) (grad : Space3 → Space3) (I : BoxIntegral.Box (Fin 3)) : ℝ :=
  ∫ x in BoxIntegral.Box.Icc I, waveEnergy3DIntegrand u grad x

lemma sobolevH1NormSq3D_nonneg
    (u : Space3 → ℝ) (grad : Space3 → Space3) (I : BoxIntegral.Box (Fin 3)) :
    0 ≤ sobolevH1NormSq3D u grad I := by
  unfold sobolevH1NormSq3D
  apply setIntegral_nonneg measurableSet_Icc
  intro x _
  unfold waveEnergy3DIntegrand
  exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)

lemma l2_le_sobolevH1_3D
    (u : Space3 → ℝ) (grad : Space3 → Space3) (I : BoxIntegral.Box (Fin 3))
    (hu : IntegrableOn (fun x => u x ^ 2) (BoxIntegral.Box.Icc I))
    (hg : IntegrableOn (fun x => ∑ i : Fin 3, grad x i ^ 2) (BoxIntegral.Box.Icc I)) :
    (∫ x in BoxIntegral.Box.Icc I, u x ^ 2) ≤ sobolevH1NormSq3D u grad I := by
  unfold sobolevH1NormSq3D waveEnergy3DIntegrand
  rw [integral_add hu hg]
  have hnn : 0 ≤ ∫ x in BoxIntegral.Box.Icc I, ∑ i : Fin 3, grad x i ^ 2 := by
    apply setIntegral_nonneg measurableSet_Icc
    intro x _
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

lemma grad_le_sobolevH1_3D
    (u : Space3 → ℝ) (grad : Space3 → Space3) (I : BoxIntegral.Box (Fin 3))
    (hu : IntegrableOn (fun x => u x ^ 2) (BoxIntegral.Box.Icc I))
    (hg : IntegrableOn (fun x => ∑ i : Fin 3, grad x i ^ 2) (BoxIntegral.Box.Icc I)) :
    (∫ x in BoxIntegral.Box.Icc I, ∑ i : Fin 3, grad x i ^ 2) ≤
      sobolevH1NormSq3D u grad I := by
  unfold sobolevH1NormSq3D waveEnergy3DIntegrand
  rw [integral_add hu hg]
  have hnn : 0 ≤ ∫ x in BoxIntegral.Box.Icc I, u x ^ 2 := by
    apply setIntegral_nonneg measurableSet_Icc
    intro x _
    exact sq_nonneg _
  linarith

/-! ## C. Derived 3D spatial curvature and ADM constraint operators -/

/-- Spatial Riemann curvature tensor `³R^a_{bcd}` computed from a 3-metric field. -/
noncomputable def spatialRiemannOf (h hinv : Space3 → Tensor2 3)
    (x : Space3) (a b c d : Fin 3) : ℝ :=
  CoordinateCurvature.riemann h hinv x a b c d

/-- Spatial Ricci tensor `³Ric_{ab}` computed from a 3-metric field. -/
noncomputable def spatialRicciOf (h hinv : Space3 → Tensor2 3)
    (x : Space3) (a b : Fin 3) : ℝ :=
  CoordinateCurvature.ricciTensor h hinv x a b

/-- Spatial scalar curvature `³R` computed from a 3-metric field. -/
noncomputable def spatialScalarCurvOf (h hinv : Space3 → Tensor2 3)
    (x : Space3) : ℝ :=
  CoordinateCurvature.ricciScalar h hinv x

/-- ADM Hamiltonian constraint functional
`H(h, K) = ³R(h) + (tr K)² - K_{ij} K^{ij}`, with `³R(h)` derived from the
3-metric field `h`. -/
noncomputable def hamiltonianConstraintOf (h hinv K : Space3 → Tensor2 3)
    (x : Space3) : ℝ :=
  spatialScalarCurvOf h hinv x
    + (∑ i : Fin 3, ∑ j : Fin 3, hinv x i j * K x i j) ^ 2
    - ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
        hinv x i a * hinv x j b * K x i j * K x a b

/-- ADM momentum constraint functional
`M_i(h, K) = ∂_j (h^{jk} K_{ik}) - ∂_i (tr K)`, with `tr K` and `∂K` derived
directly from the fields `hinv` and `K`. -/
noncomputable def momentumConstraintOf (hinv K : Space3 → Tensor2 3)
    (x : Space3) (i : Fin 3) : ℝ :=
  (∑ j : Fin 3, ∑ k : Fin 3,
      CoordinateCurvature.coordDeriv j (fun y => hinv y j k * K y i k) x)
    - CoordinateCurvature.coordDeriv i (fun y => ∑ j : Fin 3, ∑ k : Fin 3, hinv y j k * K y j k) x

/-- Flat Minkowski slice data with zero extrinsic curvature satisfy both
derived ADM constraints identically. -/
lemma minkowskiChart_spatial_constraints_zero (x : Space3) :
    hamiltonianConstraintOf minkowskiChart.spatialMetricField
        (fun _ => euclideanMetric3.ginv) (fun _ => 0) x = 0 ∧
      ∀ i : Fin 3, momentumConstraintOf (fun _ => euclideanMetric3.ginv)
        (fun _ => 0) x i = 0 := by
  constructor
  · have hconst : ∀ y : Space3, minkowskiChart.spatialMetricField y = euclideanMetric3.g := by
      intro y
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [ChartSpacetime.spatialMetricField, ChartSpacetime.coordinateMetric,
          minkowskiChart, minkowski, euclideanMetric3, minkowskiMetric4_apply]
    have hS : spatialScalarCurvOf minkowskiChart.spatialMetricField
        (fun _ => euclideanMetric3.ginv) x = 0 :=
      CoordinateCurvature.ricciScalar_const minkowskiChart.spatialMetricField
        (fun _ => euclideanMetric3.ginv) euclideanMetric3.g hconst x
    simp [hamiltonianConstraintOf, hS]
  · intro i
    simp [momentumConstraintOf, CoordinateCurvature.coordDeriv_const]

/-! ## D. Solving the nonlinear constraints -/

/-- Squared Euclidean radius `r² = x₀² + x₁² + x₂²` in 3D space. -/
noncomputable def norm3Sq (x : Space3) : ℝ :=
  x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2

lemma norm3Sq_nonneg (x : Space3) : 0 ≤ norm3Sq x := by
  unfold norm3Sq
  positivity

lemma norm3Sq_pos {x : Space3} (hx : norm3Sq x ≠ 0) : 0 < norm3Sq x :=
  lt_of_le_of_ne (norm3Sq_nonneg x) hx.symm

lemma norm3Sq_update_hasDerivAt (x : Space3) (i : Fin 3) :
    HasDerivAt (fun s : ℝ => norm3Sq (Function.update x i s)) (2 * x i) (x i) := by
  fin_cases i
  · change HasDerivAt (fun s : ℝ => norm3Sq (Function.update x 0 s)) (2 * x 0) (x 0)
    have hfun : (fun s : ℝ => norm3Sq (Function.update x 0 s)) =
        fun s : ℝ => s ^ 2 + (x 1 ^ 2 + x 2 ^ 2) := by
      funext s; simp [norm3Sq]; ring
    rw [hfun]
    simpa using ((hasDerivAt_pow 2 (x 0)).add_const (x 1 ^ 2 + x 2 ^ 2))
  · change HasDerivAt (fun s : ℝ => norm3Sq (Function.update x 1 s)) (2 * x 1) (x 1)
    have hfun : (fun s : ℝ => norm3Sq (Function.update x 1 s)) =
        fun s : ℝ => s ^ 2 + (x 0 ^ 2 + x 2 ^ 2) := by
      funext s; simp [norm3Sq]; ring
    rw [hfun]
    simpa using ((hasDerivAt_pow 2 (x 1)).add_const (x 0 ^ 2 + x 2 ^ 2))
  · change HasDerivAt (fun s : ℝ => norm3Sq (Function.update x 2 s)) (2 * x 2) (x 2)
    have hfun : (fun s : ℝ => norm3Sq (Function.update x 2 s)) =
        fun s : ℝ => s ^ 2 + (x 0 ^ 2 + x 1 ^ 2) := by
      funext s; simp [norm3Sq]; ring
    rw [hfun]
    simpa using ((hasDerivAt_pow 2 (x 2)).add_const (x 0 ^ 2 + x 1 ^ 2))

lemma norm3Sq_update_ne_zero {x : Space3} (hx : norm3Sq x ≠ 0) (i : Fin 3) :
    ∃ ε > 0, ∀ s ∈ Metric.ball (x i) ε, norm3Sq (Function.update x i s) ≠ 0 := by
  have hcont : ContinuousAt (fun s : ℝ => norm3Sq (Function.update x i s)) (x i) :=
    (norm3Sq_update_hasDerivAt x i).continuousAt
  have hev : ∀ᶠ s in 𝓝 (x i), norm3Sq (Function.update x i s) ≠ 0 := by
    apply hcont.eventually_ne
    simpa using hx
  exact Metric.mem_nhds_iff.mp hev

/-- **Brill–Lindquist / Lichnerowicz harmonic conformal factor** on `ℝ³ \ {0}`:
`φ(x) = 1 + M / (2 √(x₀² + x₁² + x₂²))`.  Solving the Lichnerowicz vacuum
constraint `Δ φ = 0` yields conformally flat time-symmetric initial data
`h_{ij} = φ⁴ δ_{ij}` with vanishing scalar curvature. -/
noncomputable def brillLindquistPhi (M : ℝ) (x : Space3) : ℝ :=
  1 + M / (2 * Real.sqrt (norm3Sq x))

lemma coordDeriv_brillLindquistPhi (M : ℝ) {x : Space3} (hx : norm3Sq x ≠ 0) (i : Fin 3) :
    coordDeriv (brillLindquistPhi M) i x =
      -(M / 2) * x i / Real.sqrt (norm3Sq x) ^ 3 := by
  have hrpos : 0 < norm3Sq x := norm3Sq_pos hx
  have hsqrt : Real.sqrt (norm3Sq x) ≠ 0 := (Real.sqrt_pos.mpr hrpos).ne'
  have hs0 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (norm3Sq (Function.update x i (x i)))))
      (norm3Sq (Function.update x i (x i))) := by
    simpa [Function.update_eq_self] using Real.hasDerivAt_sqrt hx
  have hs1 := hs0.comp (x i) (norm3Sq_update_hasDerivAt x i)
  simp only [Function.update_eq_self] at hs1
  have hsq : HasDerivAt (fun s : ℝ => 2 * Real.sqrt (norm3Sq (Function.update x i s)))
      (2 * (1 / (2 * Real.sqrt (norm3Sq x)) * (2 * x i))) (x i) :=
    hs1.const_mul 2
  have hinv : HasDerivAt (fun s : ℝ => (2 * Real.sqrt (norm3Sq (Function.update x i s)))⁻¹)
      (-(2 * (1 / (2 * Real.sqrt (norm3Sq x)) * (2 * x i))) /
        (2 * Real.sqrt (norm3Sq x)) ^ 2) (x i) := by
    have h := hsq.fun_inv (by simpa [Function.update_eq_self] using mul_ne_zero two_ne_zero hsqrt)
    simpa [Function.update_eq_self] using h
  have hfull : HasDerivAt (fun s : ℝ => brillLindquistPhi M (Function.update x i s))
      (-(M / 2) * x i / Real.sqrt (norm3Sq x) ^ 3) (x i) := by
    have hfun : (fun s : ℝ => brillLindquistPhi M (Function.update x i s)) =
        fun s : ℝ => 1 + M * (2 * Real.sqrt (norm3Sq (Function.update x i s)))⁻¹ := by
      funext s; simp [brillLindquistPhi, div_eq_mul_inv]
    rw [hfun]
    have hm := (hinv.const_mul M).const_add 1
    convert hm using 1
    have hsq_sq : Real.sqrt (norm3Sq x) ^ 2 = norm3Sq x := Real.sq_sqrt hrpos.le
    have hpow3 : Real.sqrt (norm3Sq x) ^ 3 = norm3Sq x * Real.sqrt (norm3Sq x) := by
      calc Real.sqrt (norm3Sq x) ^ 3 = Real.sqrt (norm3Sq x) ^ 2 * Real.sqrt (norm3Sq x) := by ring
        _ = norm3Sq x * Real.sqrt (norm3Sq x) := by rw [hsq_sq]
    rw [hpow3]
    field_simp [hsqrt]
    rw [hsq_sq]
  exact hfull.deriv

/-- **Solution of the Lichnerowicz–Brill–Lindquist vacuum constraint PDE**:
`Δ φ = 0` everywhere on `ℝ³ \ {0}`. -/
lemma spatialLaplacian3D_brillLindquistPhi (M : ℝ) {x : Space3} (hx : norm3Sq x ≠ 0) :
    spatialLaplacian3D (brillLindquistPhi M) x = 0 := by
  have hrpos : 0 < norm3Sq x := norm3Sq_pos hx
  have hsqrt : Real.sqrt (norm3Sq x) ≠ 0 := (Real.sqrt_pos.mpr hrpos).ne'
  have hcoord2 : ∀ i : Fin 3, coordDeriv2 (brillLindquistPhi M) i x =
      (M / 2) * (3 * x i ^ 2 - norm3Sq x) / Real.sqrt (norm3Sq x) ^ 5 := by
    intro i
    obtain ⟨ε, hε, hball⟩ := norm3Sq_update_ne_zero hx i
    have hev : (fun s : ℝ => coordDeriv (brillLindquistPhi M) i (Function.update x i s)) =ᶠ[𝓝 (x i)]
        fun s : ℝ => -(M / 2) * (Function.update x i s i) /
          Real.sqrt (norm3Sq (Function.update x i s)) ^ 3 := by
      filter_upwards [Metric.ball_mem_nhds (x i) hε] with s hs
      exact coordDeriv_brillLindquistPhi M (hball s hs) i
    rw [coordDeriv2, coordDeriv, hev.deriv_eq]
    have hxi : HasDerivAt (fun s : ℝ => -(M / 2) * Function.update x i s i) (-(M / 2)) (x i) := by
      have hfun : (fun s : ℝ => -(M / 2) * Function.update x i s i) = fun s : ℝ => -(M / 2) * s := by
        funext s; simp
      rw [hfun]
      simpa using (hasDerivAt_id (x i)).const_mul (-(M / 2))
    have hs0 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (norm3Sq (Function.update x i (x i)))))
        (norm3Sq (Function.update x i (x i))) := by
      simpa [Function.update_eq_self] using Real.hasDerivAt_sqrt hx
    have hsqrt_u := hs0.comp (x i) (norm3Sq_update_hasDerivAt x i)
    have hpow3 : HasDerivAt
        (fun s : ℝ => Real.sqrt (norm3Sq (Function.update x i s)) ^ 3)
        (3 * Real.sqrt (norm3Sq (Function.update x i (x i))) ^ 2 *
          (1 / (2 * Real.sqrt (norm3Sq (Function.update x i (x i)))) * (2 * x i))) (x i) :=
      (hasDerivAt_pow 3 _).comp (x i) hsqrt_u
    have hquot := hxi.div hpow3 (by simpa [Function.update_eq_self] using pow_ne_zero 3 hsqrt)
    convert hquot.deriv using 1
    simp only [Function.update_eq_self]
    have hsq2 : Real.sqrt (norm3Sq x) ^ 2 = norm3Sq x := Real.sq_sqrt hrpos.le
    have hpow5 : Real.sqrt (norm3Sq x) ^ 5 = norm3Sq x * Real.sqrt (norm3Sq x) ^ 3 := by
      calc Real.sqrt (norm3Sq x) ^ 5 = Real.sqrt (norm3Sq x) ^ 2 * Real.sqrt (norm3Sq x) ^ 3 := by ring
        _ = norm3Sq x * Real.sqrt (norm3Sq x) ^ 3 := by rw [hsq2]
    have hpow6 : (Real.sqrt (norm3Sq x) ^ 3) ^ 2 = norm3Sq x * Real.sqrt (norm3Sq x) ^ 4 := by
      calc (Real.sqrt (norm3Sq x) ^ 3) ^ 2 = Real.sqrt (norm3Sq x) ^ 2 * Real.sqrt (norm3Sq x) ^ 4 := by ring
        _ = norm3Sq x * Real.sqrt (norm3Sq x) ^ 4 := by rw [hsq2]
    field_simp [hsqrt]
    rw [hsq2]
    ring
  unfold spatialLaplacian3D
  rw [Fin.sum_univ_three, hcoord2 0, hcoord2 1, hcoord2 2]
  have hn : norm3Sq x = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := rfl
  rw [hn]
  ring

/-- Curved 3D Schwarzschild–de Sitter spatial slice `ds² = dr²/f + r² dθ² + r² sin²θ dφ²`
in coordinates `(r, θ, φ)` (`x 0 = r`, `x 1 = θ`, `x 2 = φ`). -/
noncomputable def sdsSpatialMetric (M Λ : ℝ) (x : Space3) : Tensor2 3 :=
  fun i j =>
    if i = j then
      if i = 0 then ((sdsSpacetime M Λ).metricFn (x 0))⁻¹
      else if i = 1 then (x 0) ^ 2
      else (x 0) ^ 2 * Real.sin (x 1) ^ 2
    else 0

/-- Inverse of `sdsSpatialMetric`. -/
noncomputable def sdsSpatialMetricInv (M Λ : ℝ) (x : Space3) : Tensor2 3 :=
  fun i j =>
    if i = j then
      if i = 0 then (sdsSpacetime M Λ).metricFn (x 0)
      else if i = 1 then ((x 0) ^ 2)⁻¹
      else ((x 0) ^ 2 * Real.sin (x 1) ^ 2)⁻¹
    else 0

/-- Closed-form 3D Christoffel symbols of `sdsSpatialMetric`. -/
noncomputable def sdsSpatialG (M Λ : ℝ) (x : Space3) (k i j : Fin 3) : ℝ :=
  if k = 0 then
    if i = 0 ∧ j = 0 then
      -((sdsSpacetime M Λ).metricFnHalfDeriv (x 0) / (sdsSpacetime M Λ).metricFn (x 0))
    else if i = 1 ∧ j = 1 then -(x 0 * (sdsSpacetime M Λ).metricFn (x 0))
    else if i = 2 ∧ j = 2 then -(x 0 * Real.sin (x 1) ^ 2 * (sdsSpacetime M Λ).metricFn (x 0))
    else 0
  else if k = 1 then
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 / x 0
    else if i = 2 ∧ j = 2 then -(Real.sin (x 1) * Real.cos (x 1))
    else 0
  else
    if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then 1 / x 0
    else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then Real.cos (x 1) / Real.sin (x 1)
    else 0

lemma pd_sdsSpatial_00 (M Λ : ℝ) (x : Space3) (hr : x 0 ≠ 0)
    (hf : (sdsSpacetime M Λ).metricFn (x 0) ≠ 0) :
    CoordinateCurvature.coordDeriv 0 (fun y => ((sdsSpacetime M Λ).metricFn (y 0))⁻¹) x =
      -(2 * (sdsSpacetime M Λ).metricFnHalfDeriv (x 0)) /
        (sdsSpacetime M Λ).metricFn (x 0) ^ 2 := by
  have hd := ((sdsSpacetime M Λ).hasDerivAt_metricFn (x 0) hr).fun_inv hf
  have hfun : (fun s : ℝ => ((sdsSpacetime M Λ).metricFn (Function.update x 0 s 0))⁻¹) =
      fun s : ℝ => ((sdsSpacetime M Λ).metricFn s)⁻¹ := by
    funext s; simp
  unfold CoordinateCurvature.coordDeriv
  rw [hfun, hd.deriv]

lemma christoffel_eq_sdsSpatialG (M Λ : ℝ) (x : Space3) (hr : x 0 ≠ 0)
    (hf : (sdsSpacetime M Λ).metricFn (x 0) ≠ 0) (hsin : Real.sin (x 1) ≠ 0)
    (k i j : Fin 3) :
    CoordinateCurvature.christoffel (sdsSpatialMetric M Λ) (sdsSpatialMetricInv M Λ) x k i j =
      sdsSpatialG M Λ x k i j := by
  have h0_00 := pd_sdsSpatial_00 M Λ x hr hf
  have h0_11 : CoordinateCurvature.coordDeriv 0 (fun y : Space3 => y 0 ^ 2) x = 2 * x 0 := by
    have hfun : (fun s : ℝ => Function.update x 0 s 0 ^ 2) = fun s => s ^ 2 := by
      funext s; simp
    unfold CoordinateCurvature.coordDeriv; rw [hfun]
    have hd := hasDerivAt_pow 2 (x 0)
    convert hd.deriv using 1
    ring
  have h0_22 : CoordinateCurvature.coordDeriv 0 (fun y : Space3 => y 0 ^ 2 * Real.sin (y 1) ^ 2) x =
      2 * x 0 * Real.sin (x 1) ^ 2 := by
    have hfun : (fun s : ℝ => Function.update x 0 s 0 ^ 2 *
        Real.sin (Function.update x 0 s 1) ^ 2) = fun s => s ^ 2 * Real.sin (x 1) ^ 2 := by
      funext s; simp
    unfold CoordinateCurvature.coordDeriv; rw [hfun]
    have hd := (hasDerivAt_pow 2 (x 0)).mul_const (Real.sin (x 1) ^ 2)
    convert hd.deriv using 1
    ring
  have h1_22 : CoordinateCurvature.coordDeriv 1 (fun y : Space3 => y 0 ^ 2 * Real.sin (y 1) ^ 2) x =
      2 * x 0 ^ 2 * Real.sin (x 1) * Real.cos (x 1) := by
    have hfun : (fun s : ℝ => Function.update x 1 s 0 ^ 2 *
        Real.sin (Function.update x 1 s 1) ^ 2) = fun s => x 0 ^ 2 * Real.sin s ^ 2 := by
      funext s; simp
    unfold CoordinateCurvature.coordDeriv; rw [hfun]
    have hd := (hasDerivAt_sin_sq (x 1)).const_mul (x 0 ^ 2)
    convert hd.deriv using 1
    ring
  have h2_22 : CoordinateCurvature.coordDeriv 2 (fun y : Space3 => y 0 ^ 2 * Real.sin (y 1) ^ 2) x = 0 := by
    have hfun : (fun s : ℝ => Function.update x 2 s 0 ^ 2 *
        Real.sin (Function.update x 2 s 1) ^ 2) = fun _ => x 0 ^ 2 * Real.sin (x 1) ^ 2 := by
      funext s; simp
    unfold CoordinateCurvature.coordDeriv; rw [hfun, deriv_const']
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [CoordinateCurvature.christoffel, sdsSpatialMetric, sdsSpatialMetricInv,
      sdsSpatialG, h0_00, h0_11, h0_22, h1_22, h2_22] <;>
    (try simp [CoordinateCurvature.coordDeriv]) <;>
    field_simp [hr, hf, hsin]

lemma pd_christoffel_eq_pd_sdsSpatialG (M Λ : ℝ) (x : Space3) (hr : x 0 ≠ 0)
    (hf : (sdsSpacetime M Λ).metricFn (x 0) ≠ 0) (hsin : Real.sin (x 1) ≠ 0)
    (μ k i j : Fin 3) :
    CoordinateCurvature.coordDeriv μ (fun y => CoordinateCurvature.christoffel (sdsSpatialMetric M Λ)
        (sdsSpatialMetricInv M Λ) y k i j) x =
      CoordinateCurvature.coordDeriv μ (fun y => sdsSpatialG M Λ y k i j) x := by
  have hev_r : ∀ᶠ r in 𝓝 (x 0), r ≠ 0 ∧ (sdsSpacetime M Λ).metricFn r ≠ 0 := by
    have h1 : ∀ᶠ r in 𝓝 (x 0), r ≠ 0 := continuousAt_id.eventually_ne hr
    have h2 : ∀ᶠ r in 𝓝 (x 0), (sdsSpacetime M Λ).metricFn r ≠ 0 :=
      ((sdsSpacetime M Λ).hasDerivAt_metricFn (x 0) hr).continuousAt.eventually_ne hf
    exact h1.and h2
  have hev_th : ∀ᶠ th in 𝓝 (x 1), Real.sin th ≠ 0 :=
    Real.continuous_sin.continuousAt.eventually_ne hsin
  have hcont : ∀ p : Fin 3, ContinuousAt (fun y : Space3 => y p) x := fun p => continuousAt_apply p x
  have hev_y : ∀ᶠ y in 𝓝 x,
      y 0 ≠ 0 ∧ (sdsSpacetime M Λ).metricFn (y 0) ≠ 0 ∧ Real.sin (y 1) ≠ 0 := by
    have hr' := (hcont 0).eventually hev_r
    have hth' := (hcont 1).eventually hev_th
    filter_upwards [hr', hth'] with y hy1 hy2
    exact ⟨hy1.1, hy1.2, hy2⟩
  apply Bianchi.pd_congr_nhds μ
  filter_upwards [hev_y] with y hy
  exact christoffel_eq_sdsSpatialG M Λ y hy.1 hy.2.1 hy.2.2 k i j

/-- Complete closed-form derivative table `∂_μ sdsSpatialG^k_{ij}` for `μ, k, i, j : Fin 3`. -/
noncomputable def sdsSpatialDG (M Λ : ℝ) (μ : Fin 3) (x : Space3)
    (k i j : Fin 3) : ℝ :=
  if μ = 0 then
    if k = 0 then
      if i = 0 ∧ j = 0 then
        -(((-2 * M / (x 0) ^ 3 - Λ / 3) * (sdsSpacetime M Λ).metricFn (x 0) -
            2 * (sdsSpacetime M Λ).metricFnHalfDeriv (x 0) ^ 2) /
          (sdsSpacetime M Λ).metricFn (x 0) ^ 2)
      else if i = 1 ∧ j = 1 then
        -((sdsSpacetime M Λ).metricFn (x 0) +
          2 * x 0 * (sdsSpacetime M Λ).metricFnHalfDeriv (x 0))
      else if i = 2 ∧ j = 2 then
        -(Real.sin (x 1) ^ 2 * ((sdsSpacetime M Λ).metricFn (x 0) +
          2 * x 0 * (sdsSpacetime M Λ).metricFnHalfDeriv (x 0)))
      else 0
    else if k = 1 then
      if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then -(1 / x 0 ^ 2) else 0
    else
      if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then -(1 / x 0 ^ 2) else 0
  else if μ = 1 then
    if k = 0 then
      if i = 2 ∧ j = 2 then
        -(2 * x 0 * Real.sin (x 1) * Real.cos (x 1) *
          (sdsSpacetime M Λ).metricFn (x 0))
      else 0
    else if k = 1 then
      if i = 2 ∧ j = 2 then -(Real.cos (x 1) ^ 2 - Real.sin (x 1) ^ 2) else 0
    else
      if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then -(1 / Real.sin (x 1) ^ 2) else 0
  else 0

lemma pd_sdsSpatialG_eq_sdsSpatialDG_0 (M Λ : ℝ) (x : Space3) (hr : x 0 ≠ 0)
    (hf : (sdsSpacetime M Λ).metricFn (x 0) ≠ 0) (k i j : Fin 3) :
    CoordinateCurvature.coordDeriv 0 (fun y => sdsSpatialG M Λ y k i j) x =
      sdsSpatialDG M Λ 0 x k i j := by
  have h000 : CoordinateCurvature.coordDeriv 0 (fun y => sdsSpatialG M Λ y 0 0 0) x =
      sdsSpatialDG M Λ 0 x 0 0 0 := by
    have hfun : (fun s : ℝ => sdsSpatialG M Λ (Function.update x 0 s) 0 0 0) =
        fun s : ℝ => -((sdsSpacetime M Λ).metricFnHalfDeriv s /
          (sdsSpacetime M Λ).metricFn s) := by
      funext s; simp [sdsSpatialG]
    unfold CoordinateCurvature.coordDeriv; rw [hfun]
    have hd := (((sdsSpacetime M Λ).hasDerivAt_metricFnHalfDeriv (x 0) hr).fun_div
      ((sdsSpacetime M Λ).hasDerivAt_metricFn (x 0) hr) hf).fun_neg
    convert hd.deriv using 1
    simp [sdsSpatialDG]
    ring
  have h011 : CoordinateCurvature.coordDeriv 0 (fun y => sdsSpatialG M Λ y 0 1 1) x =
      sdsSpatialDG M Λ 0 x 0 1 1 := by
    have hfun : (fun s : ℝ => sdsSpatialG M Λ (Function.update x 0 s) 0 1 1) =
        fun s : ℝ => -(s * (sdsSpacetime M Λ).metricFn s) := by
      funext s; simp [sdsSpatialG]
    unfold CoordinateCurvature.coordDeriv; rw [hfun]
    have hd := ((hasDerivAt_id' (x 0)).fun_mul
      ((sdsSpacetime M Λ).hasDerivAt_metricFn (x 0) hr)).fun_neg
    rw [hd.deriv]
    dsimp [sdsSpatialDG]
    ring
  have h022 : CoordinateCurvature.coordDeriv 0 (fun y => sdsSpatialG M Λ y 0 2 2) x =
      sdsSpatialDG M Λ 0 x 0 2 2 := by
    have hfun : (fun s : ℝ => sdsSpatialG M Λ (Function.update x 0 s) 0 2 2) =
        fun s : ℝ => -(Real.sin (x 1) ^ 2 * (s * (sdsSpacetime M Λ).metricFn s)) := by
      funext s; simp [sdsSpatialG]; ring
    unfold CoordinateCurvature.coordDeriv; rw [hfun]
    have hd := (((hasDerivAt_id' (x 0)).fun_mul
      ((sdsSpacetime M Λ).hasDerivAt_metricFn (x 0) hr)).const_mul
        (Real.sin (x 1) ^ 2)).fun_neg
    rw [hd.deriv]
    dsimp [sdsSpatialDG]
    ring
  have h101 : CoordinateCurvature.coordDeriv 0 (fun y => sdsSpatialG M Λ y 1 0 1) x =
      sdsSpatialDG M Λ 0 x 1 0 1 := by
    have hfun : (fun s : ℝ => sdsSpatialG M Λ (Function.update x 0 s) 1 0 1) =
        fun s : ℝ => s⁻¹ := by funext s; simp [sdsSpatialG]
    unfold CoordinateCurvature.coordDeriv; rw [hfun, (hasDerivAt_inv hr).deriv]
    simp [sdsSpatialDG, one_div]
  fin_cases k <;> fin_cases i <;> fin_cases j
  all_goals first
    | exact h000 | exact h011 | exact h022
    | exact h101
    | simp [CoordinateCurvature.coordDeriv, sdsSpatialG, sdsSpatialDG]

lemma pd_sdsSpatialG_eq_sdsSpatialDG_1 (M Λ : ℝ) (x : Space3)
    (hsin : Real.sin (x 1) ≠ 0) (k i j : Fin 3) :
    CoordinateCurvature.coordDeriv 1 (fun y => sdsSpatialG M Λ y k i j) x =
      sdsSpatialDG M Λ 1 x k i j := by
  have h022 : CoordinateCurvature.coordDeriv 1 (fun y => sdsSpatialG M Λ y 0 2 2) x =
      sdsSpatialDG M Λ 1 x 0 2 2 := by
    have hfun : (fun s : ℝ => sdsSpatialG M Λ (Function.update x 1 s) 0 2 2) =
        fun s : ℝ => -(x 0 * (sdsSpacetime M Λ).metricFn (x 0) * Real.sin s ^ 2) := by
      funext s; simp [sdsSpatialG]; ring
    unfold CoordinateCurvature.coordDeriv; rw [hfun]
    have hd := ((hasDerivAt_sin_sq (x 1)).const_mul
      (x 0 * (sdsSpacetime M Λ).metricFn (x 0))).fun_neg
    convert hd.deriv using 1
    simp [sdsSpatialDG]
    ring
  have h122 : CoordinateCurvature.coordDeriv 1 (fun y => sdsSpatialG M Λ y 1 2 2) x =
      sdsSpatialDG M Λ 1 x 1 2 2 := by
    have hfun : (fun s : ℝ => sdsSpatialG M Λ (Function.update x 1 s) 1 2 2) =
        fun s : ℝ => -(Real.sin s * Real.cos s) := by funext s; simp [sdsSpatialG]
    unfold CoordinateCurvature.coordDeriv; rw [hfun]
    have hd := ((Real.hasDerivAt_sin (x 1)).fun_mul (Real.hasDerivAt_cos (x 1))).fun_neg
    convert hd.deriv using 1
    simp [sdsSpatialDG]
    ring
  have h212 : CoordinateCurvature.coordDeriv 1 (fun y => sdsSpatialG M Λ y 2 1 2) x =
      sdsSpatialDG M Λ 1 x 2 1 2 := by
    have hfun : (fun s : ℝ => sdsSpatialG M Λ (Function.update x 1 s) 2 1 2) =
        fun s : ℝ => Real.cos s / Real.sin s := by funext s; simp [sdsSpatialG]
    unfold CoordinateCurvature.coordDeriv; rw [hfun]
    have hd := (Real.hasDerivAt_cos (x 1)).fun_div (Real.hasDerivAt_sin (x 1)) hsin
    have hcos_sin : -Real.sin (x 1) * Real.sin (x 1) - Real.cos (x 1) * Real.cos (x 1) =
        -(Real.sin (x 1) ^ 2 + Real.cos (x 1) ^ 2) := by ring
    rw [hd.deriv, hcos_sin, Real.sin_sq_add_cos_sq]
    simp [sdsSpatialDG]
    ring
  fin_cases k <;> fin_cases i <;> fin_cases j
  all_goals first
    | exact h022 | exact h122 | exact h212
    | simp [CoordinateCurvature.coordDeriv, sdsSpatialG, sdsSpatialDG]

lemma pd_sdsSpatialG_eq_sdsSpatialDG_2 (M Λ : ℝ) (x : Space3) (k i j : Fin 3) :
    CoordinateCurvature.coordDeriv 2 (fun y => sdsSpatialG M Λ y k i j) x =
      sdsSpatialDG M Λ 2 x k i j := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [CoordinateCurvature.coordDeriv, sdsSpatialG, sdsSpatialDG]

lemma pd_sdsSpatialG_eq_sdsSpatialDG (M Λ : ℝ) (x : Space3) (hr : x 0 ≠ 0)
    (hf : (sdsSpacetime M Λ).metricFn (x 0) ≠ 0) (hsin : Real.sin (x 1) ≠ 0)
    (μ k i j : Fin 3) :
    CoordinateCurvature.coordDeriv μ (fun y => sdsSpatialG M Λ y k i j) x =
      sdsSpatialDG M Λ μ x k i j := by
  fin_cases μ
  · exact pd_sdsSpatialG_eq_sdsSpatialDG_0 M Λ x hr hf k i j
  · exact pd_sdsSpatialG_eq_sdsSpatialDG_1 M Λ x hsin k i j
  · exact pd_sdsSpatialG_eq_sdsSpatialDG_2 M Λ x k i j

/-- **3D spatial scalar curvature of the Schwarzschild–de Sitter slice**:
`³R = 2 Λ` directly from `sdsSpatialMetric`.  In particular, at `Λ = 0` it gives
nontrivial curved 3D vacuum initial data (`³R = 0` while `³Ric_{00} ≠ 0` for
`M ≠ 0`). -/
lemma spatialScalarCurvOf_sdsSpatial (M Λ : ℝ) (x : Space3) (hr : x 0 ≠ 0)
    (hf : (sdsSpacetime M Λ).metricFn (x 0) ≠ 0) (hsin : Real.sin (x 1) ≠ 0) :
    spatialScalarCurvOf (sdsSpatialMetric M Λ) (sdsSpatialMetricInv M Λ) x = 2 * Λ := by
  have hG : ∀ k i j,
      CoordinateCurvature.christoffel (sdsSpatialMetric M Λ) (sdsSpatialMetricInv M Λ) x k i j =
        sdsSpatialG M Λ x k i j :=
    christoffel_eq_sdsSpatialG M Λ x hr hf hsin
  have hpd : ∀ μ k i j,
      CoordinateCurvature.coordDeriv μ (fun y => CoordinateCurvature.christoffel (sdsSpatialMetric M Λ)
          (sdsSpatialMetricInv M Λ) y k i j) x =
        sdsSpatialDG M Λ μ x k i j := by
    intro μ k i j
    rw [pd_christoffel_eq_pd_sdsSpatialG M Λ x hr hf hsin μ k i j,
      pd_sdsSpatialG_eq_sdsSpatialDG M Λ x hr hf hsin μ k i j]
  have hcos_sq : Real.cos (x 1) ^ 2 = 1 - Real.sin (x 1) ^ 2 := by
    linear_combination Real.sin_sq_add_cos_sq (x 1)
  have hric00 : CoordinateCurvature.ricciTensor (sdsSpatialMetric M Λ) (sdsSpatialMetricInv M Λ) x 0 0 =
      -(2 * (sdsSpacetime M Λ).metricFnHalfDeriv (x 0) /
        (x 0 * (sdsSpacetime M Λ).metricFn (x 0))) := by
    simp [CoordinateCurvature.ricciTensor, CoordinateCurvature.riemann, Fin.sum_univ_three,
      hpd, hG, sdsSpatialG, sdsSpatialDG]
    field_simp [hr, hf]
    ring
  have hric11 : CoordinateCurvature.ricciTensor (sdsSpatialMetric M Λ) (sdsSpatialMetricInv M Λ) x 1 1 =
      1 - (sdsSpacetime M Λ).metricFn (x 0) -
        x 0 * (sdsSpacetime M Λ).metricFnHalfDeriv (x 0) := by
    simp [CoordinateCurvature.ricciTensor, CoordinateCurvature.riemann, Fin.sum_univ_three,
      hpd, hG, sdsSpatialG, sdsSpatialDG]
    field_simp [hr, hsin]
    rw [hcos_sq]
    ring
  have hric22 : CoordinateCurvature.ricciTensor (sdsSpatialMetric M Λ) (sdsSpatialMetricInv M Λ) x 2 2 =
      Real.sin (x 1) ^ 2 * (1 - (sdsSpacetime M Λ).metricFn (x 0) -
        x 0 * (sdsSpacetime M Λ).metricFnHalfDeriv (x 0)) := by
    simp [CoordinateCurvature.ricciTensor, CoordinateCurvature.riemann, Fin.sum_univ_three,
      hpd, hG, sdsSpatialG, sdsSpatialDG]
    field_simp [hr, hsin]
    rw [hcos_sq]
    ring
  have hoff : ∀ σ ν : Fin 3, σ ≠ ν →
      CoordinateCurvature.ricciTensor (sdsSpatialMetric M Λ) (sdsSpatialMetricInv M Λ) x σ ν = 0 := by
    intro σ ν hne
    fin_cases σ <;> fin_cases ν
    · exact absurd rfl hne
    · simp [CoordinateCurvature.ricciTensor, CoordinateCurvature.riemann, Fin.sum_univ_three,
        hpd, hG, sdsSpatialG, sdsSpatialDG]
    · simp [CoordinateCurvature.ricciTensor, CoordinateCurvature.riemann, Fin.sum_univ_three,
        hpd, hG, sdsSpatialG, sdsSpatialDG]
    · simp [CoordinateCurvature.ricciTensor, CoordinateCurvature.riemann, Fin.sum_univ_three,
        hpd, hG, sdsSpatialG, sdsSpatialDG]
      ring
    · exact absurd rfl hne
    · simp [CoordinateCurvature.ricciTensor, CoordinateCurvature.riemann, Fin.sum_univ_three,
        hpd, hG, sdsSpatialG, sdsSpatialDG]
    · simp [CoordinateCurvature.ricciTensor, CoordinateCurvature.riemann, Fin.sum_univ_three,
        hpd, hG, sdsSpatialG, sdsSpatialDG]
    · simp [CoordinateCurvature.ricciTensor, CoordinateCurvature.riemann, Fin.sum_univ_three,
        hpd, hG, sdsSpatialG, sdsSpatialDG]
    · exact absurd rfl hne
  simp [spatialScalarCurvOf, CoordinateCurvature.ricciScalar, Fin.sum_univ_three, sdsSpatialMetricInv,
    hric00, hric11, hric22]
  field_simp [hr, hf, hsin]
  simp only [SchwarzschildDeSitter.SchwarzschildDeSitterSpacetime.metricFn,
    SchwarzschildDeSitter.SchwarzschildDeSitterSpacetime.metricFnHalfDeriv]
  field_simp [hr]
  ring

/-- Time-symmetric curved Schwarzschild spatial slice (`K = 0`, `Λ = 0`) solves
the derived nonlinear Hamiltonian constraint identically. -/
lemma schwarzschild_spatial_hamiltonian_zero (M : ℝ) (x : Space3) (hr : x 0 ≠ 0)
    (hf : (schwarzschildSpacetime M).metricFn (x 0) ≠ 0) (hsin : Real.sin (x 1) ≠ 0) :
    hamiltonianConstraintOf (sdsSpatialMetric M 0) (sdsSpatialMetricInv M 0)
      (fun _ => 0) x = 0 := by
  have hf0 : (sdsSpacetime M 0).metricFn (x 0) ≠ 0 := by
    rwa [SchwarzschildDeSitter.SchwarzschildDeSitterSpacetime.metricFn_zero_lambda]
  have hS := spatialScalarCurvOf_sdsSpatial M 0 x hr hf0 hsin
  simp [hamiltonianConstraintOf, hS]

/-- Flat FLRW initial data `(h_{ij} = a₀² δ_{ij}, K_{ij} = H a₀² δ_{ij})`
satisfy the derived momentum constraint identically and yield Hamiltonian
value `6 H²` (vanishing when `3 H² = Λ`). -/
lemma flrw_initial_constraints (a₀ H : ℝ) (ha : a₀ ≠ 0) (x : Space3) :
    hamiltonianConstraintOf (fun _ => a₀ ^ 2 • (1 : Tensor2 3))
        (fun _ => (a₀ ^ 2)⁻¹ • (1 : Tensor2 3))
        (fun _ => (H * a₀ ^ 2) • (1 : Tensor2 3)) x = 6 * H ^ 2 ∧
      ∀ i : Fin 3, momentumConstraintOf (fun _ => (a₀ ^ 2)⁻¹ • (1 : Tensor2 3))
        (fun _ => (H * a₀ ^ 2) • (1 : Tensor2 3)) x i = 0 := by
  have hS : spatialScalarCurvOf (fun _ => a₀ ^ 2 • (1 : Tensor2 3))
      (fun _ => (a₀ ^ 2)⁻¹ • (1 : Tensor2 3)) x = 0 :=
    CoordinateCurvature.ricciScalar_const _ _ (a₀ ^ 2 • (1 : Tensor2 3)) (fun _ => rfl) x
  constructor
  · simp [hamiltonianConstraintOf, hS, Fin.sum_univ_three]
    field_simp [ha]
    ring
  · intro i
    simp [momentumConstraintOf, CoordinateCurvature.coordDeriv_const]

end GeneralRelativity
