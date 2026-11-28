/-
Copyright (c) 2026 Alex Vergara Gil.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/

module

public import PhyslibAlpha.Relativity.General.Bianchi
public import PhyslibAlpha.Relativity.General.InitialData.ReducedCauchy
public import PhyslibAlpha.Cosmology.FLRW.Basic
public import PhyslibAlpha.Cosmology.FLRW.FriedmannEquations
public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!

# Gauge recovery and constraint propagation

## i. Overview

This module proves gauge recovery and constraint propagation and inhabits
`GaugeRecoveryCertificate` in both the linearized 3D wave-gauge setting and the
nonlinear 4D flat FLRW setting, backed by the general nonlinear Bianchi
conservation identity:

1. **General nonlinear Bianchi constraint-propagation split**:
   `bianchi_constraint_propagation_split` rewrites `Bianchi.covDiv_einstein_eq_zero`
   (`∇^μ G_{μl} = 0`) to isolate the time-evolution term
   `g^{00} ∂ₜ G_{0l}` as minus the spatial-derivative and Christoffel terms.
2. **Linearized 3D wave-gauge system (`linearizedBox_gaugeRecovery`)**:
   assuming each Lorenz gauge divergence component `Γ_k = ∂^m h̄_{mk}` solves
   the box wave problem `WaveSolution3D` with zero initial gauge data on
   `Box.Icc I`, `WaveUniqueness3D.wave_zero_of_zero_data3D` forces `Γ_k = 0`
   on `Box.Icc I`.  Because `Box.Ioo I` is open, Lorenz gauge holds on a
   neighborhood of every interior spacetime point, so
   `Linearized.linearizedEinstein_eq_zero_of_waveGauge` recovers the full
   linearized vacuum Einstein equations `G^{(1)}_{ij} = 0` and preserves the
   `(0, j)` constraints.
3. **Nonlinear 4D flat FLRW Einstein system (`flrw_gaugeRecovery`)**:
   if a scale factor `a` solves the reduced evolution equation
   `2 a a'' + (a')² = Λ a²` on `Ioo (-δ) δ` and satisfies the initial Hamiltonian
   constraint `3 (a'(0))² = Λ a(0)²`, then `d/dt [a (3 (a')² - Λ a²)] = 0`
   propagates `3 (a')² = Λ a²` everywhere on `Ioo (-δ) δ`, and
   `FLRW.einsteinTensorOf_flrw_iff_friedmann` recovers the full 4D Einstein
   equations `G_{ij} + Λ g_{ij} = 0` at every regular chart point.

## ii. Key results

- `bianchi_constraint_propagation_split` : the nonlinear Bianchi
  constraint-propagation split.
- `linearizedBox_gaugeRecovery` : the certificate for the linearized 3D
  wave-gauge system.
- `flrw_constraint_propagates`, `flrw_full_einstein_of_reduced` : nonlinear FLRW
  constraint propagation and full Einstein recovery.
- `flrw_gaugeRecovery` : the certificate for the nonlinear 4D flat FLRW
  system.

## iii. Table of contents

- A. General nonlinear Bianchi constraint-propagation split
- B. Linearized 3D wave-gauge recovery and constraint preservation
- C. Nonlinear 4D flat FLRW constraint propagation and Einstein recovery

## iv. References

* R. M. Wald, *General Relativity*, University of Chicago Press, 1984, Ch. 7.
  [ref: wald_1984_general_relativity]
* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019,
  Ch. 7. [ref: Carroll1997]

-/

@[expose] public section

open MeasureTheory BoxIntegral Set
open scoped Topology

namespace GeneralRelativity

/-- FLRW spacetime with scale factor `a` and curvature `k`, named so the
structure-based metric API reads as `(flrwSpacetime a k).metric`. -/
abbrev flrwSpacetime (a : ℝ → ℝ) (k : ℝ) : Cosmology.FLRW.FLRWSpacetime :=
  ⟨a, k⟩

/-! ## A. General nonlinear Bianchi constraint-propagation split -/

/-- **Nonlinear Bianchi constraint-propagation split**: from Einstein tensor
conservation `∇^μ G_{μl} = 0`, the principal time-derivative term
`g^{00} ∂₀ G_{0l}` of the `(0, l)` constraint equals minus the remaining
spatial-derivative and Christoffel coupling terms. -/
lemma bianchi_constraint_propagation_split
    (g ginv : (Fin 4 → ℝ) → Tensor2 4) {x : Fin 4 → ℝ}
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, g y i j = g y j i)
    (hginvSymm : ∀ᶠ y in 𝓝 x, ∀ i j, ginv y i j = ginv y j i)
    (hInvL : ∀ᶠ y in 𝓝 x, ∀ i j,
      ∑ k, ginv y i k * g y k j = if i = j then 1 else 0)
    (hInvR : ∀ᶠ y in 𝓝 x, ∀ i j,
      ∑ k, g y i k * ginv y k j = if i = j then 1 else 0)
    (hgC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => g y i j) x)
    (hginvD : ∀ i j, DifferentiableAt ℝ (fun y => ginv y i j) x)
    (hΓC2 : ∀ k i j, ContDiffAt ℝ 2 (fun y => CoordinateCurvature.christoffel g ginv y k i j) x)
    (l : Fin 4) :
    ginv x 0 0 * CoordinateCurvature.coordDeriv 0 (fun y => CoordinateCurvature.einsteinTensor g ginv y 0 l) x =
      -(ginv x 0 0 *
          (-(∑ a : Fin 4, CoordinateCurvature.christoffel g ginv x a 0 0 *
              CoordinateCurvature.einsteinTensor g ginv x a l)
            - ∑ a : Fin 4, CoordinateCurvature.christoffel g ginv x a 0 l *
              CoordinateCurvature.einsteinTensor g ginv x 0 a)
        + ∑ ν : Fin 3, ginv x 0 ν.succ *
            Bianchi.covDeriv2 g ginv (CoordinateCurvature.einsteinTensor g ginv) x 0 ν.succ l
        + ∑ μ : Fin 3, ∑ ν : Fin 4, ginv x μ.succ ν *
            Bianchi.covDeriv2 g ginv (CoordinateCurvature.einsteinTensor g ginv) x μ.succ ν l) := by
  have hdiv := Bianchi.covDiv_einstein_eq_zero g ginv
    hgSymm hginvSymm hInvL hInvR hgC2 hginvD hΓC2 l
  unfold Bianchi.covDiv2 at hdiv
  have hsum4 : ∀ f : Fin 4 → ℝ, (∑ μ : Fin 4, f μ) = f 0 + ∑ μ : Fin 3, f μ.succ :=
    Fin.sum_univ_succ
  rw [hsum4] at hdiv
  rw [hsum4 (fun ν => ginv x 0 ν * Bianchi.covDeriv2 g ginv (CoordinateCurvature.einsteinTensor g ginv) x 0 ν l)] at hdiv
  have h00 : Bianchi.covDeriv2 g ginv (CoordinateCurvature.einsteinTensor g ginv) x 0 0 l =
      CoordinateCurvature.coordDeriv 0 (fun y => CoordinateCurvature.einsteinTensor g ginv y 0 l) x
        - ∑ a : Fin 4, CoordinateCurvature.christoffel g ginv x a 0 0 *
            CoordinateCurvature.einsteinTensor g ginv x a l
        - ∑ a : Fin 4, CoordinateCurvature.christoffel g ginv x a 0 l *
            CoordinateCurvature.einsteinTensor g ginv x 0 a := rfl
  rw [h00] at hdiv
  linarith

/-! ## B. Linearized 3D wave-gauge recovery and constraint preservation -/

/-- A perturbation in the linearized wave-gauge reduced Cauchy problem on a
spatial box `I`, whose Lorenz gauge divergence `Γ_k = ∂^m h̄_{mk}` vanishes on
the initial slice together with its initial time derivative and spatial
gradient and obeys the 3D homogeneous box wave equation `WaveSolution3D`. -/
def IsLinearizedGaugeReducedSol (I : BoxIntegral.Box (Fin 3))
    (P : Linearized.MetricPerturbation) : Prop :=
  (∀ y i j, P.h y i j = P.h y j i) ∧
  (∀ y, P.IsC2At y) ∧
  (∀ y i j, Linearized.minkowskiDalembertian (fun z => P.traceReversed.h z i j) y = 0) ∧
  (∀ k : Fin 4,
    ∃ (ut : ℝ → SpaceChart → ℝ) (grad : ℝ → SpaceChart → SpaceChart)
      (utt : ℝ → SpaceChart → ℝ) (gradt : ℝ → SpaceChart → SpaceChart)
      (Dut : ℝ → SpaceChart → SpaceChart →L[ℝ] ℝ)
      (Dgrad : ℝ → SpaceChart → SpaceChart →L[ℝ] SpaceChart)
      (lap : ℝ → SpaceChart → ℝ) (M : ℝ),
      WaveSolution3D (fun t x => Linearized.lorenzDivergence P ![t, x 0, x 1, x 2] k)
        ut grad utt gradt Dut Dgrad lap I M ∧
      (∀ x : SpaceChart, Linearized.lorenzDivergence P ![0, x 0, x 1, x 2] k = 0) ∧
      (∀ x : SpaceChart, ut 0 x = 0) ∧
      (∀ (x : SpaceChart) (i : Fin 3), grad 0 x i = 0))

/-- Linearized wave-gauge reduced Cauchy problem on a spatial box `I`. -/
noncomputable def linearizedGaugeReducedProblem (I : BoxIntegral.Box (Fin 3)) :
    ReducedCauchyProblem minkowskiChart where
  data := minkowskiChartInitialData
  Solution := Linearized.MetricPerturbation
  IsSolution := IsLinearizedGaugeReducedSol I
  HasCauchyData := fun P =>
    ∀ x : SpaceChart, ∀ k : Fin 4, Linearized.lorenzDivergence P ![0, x 0, x 1, x 2] k = 0
  IsWaveGauge := fun P =>
    ∀ t (x : SpaceChart), x ∈ BoxIntegral.Box.Icc I → ∀ k : Fin 4,
      Linearized.IsLorenzGauge P ![t, x 0, x 1, x 2] k

/-- Gauge-recovery problem attached to `linearizedGaugeReducedProblem I`. -/
noncomputable def linearizedBoxGaugeProblem (I : BoxIntegral.Box (Fin 3)) :
    GaugeRecoveryProblem (linearizedGaugeReducedProblem I) where
  GaugeRecovered := fun P =>
    ∀ t (x : SpaceChart), x ∈ BoxIntegral.Box.Icc I → ∀ k : Fin 4,
      Linearized.IsLorenzGauge P ![t, x 0, x 1, x 2] k
  IsFullEinsteinSolution := fun P =>
    ∀ t (x : SpaceChart), x ∈ BoxIntegral.Box.Ioo I → ∀ i j : Fin 4,
      Linearized.linearizedEinstein P ![t, x 0, x 1, x 2] i j = 0
  ConstraintsPreserved := fun P =>
    ∀ t (x : SpaceChart), x ∈ BoxIntegral.Box.Ioo I → ∀ j : Fin 4,
      Linearized.linearizedEinstein P ![t, x 0, x 1, x 2] 0 j = 0

private lemma lorenzGauge_propagates_box (I : BoxIntegral.Box (Fin 3))
    (P : Linearized.MetricPerturbation) (hsol : IsLinearizedGaugeReducedSol I P) :
    ∀ t (x : SpaceChart), x ∈ BoxIntegral.Box.Icc I → ∀ k : Fin 4,
      Linearized.IsLorenzGauge P ![t, x 0, x 1, x 2] k := by
  intro t x hx k
  rcases hsol.2.2.2 k with ⟨ut, grad, utt, gradt, Dut, Dgrad, lap, M, hS, h0, hv0, hg0⟩
  exact wave_zero_of_zero_data3D
    (fun s y => Linearized.lorenzDivergence P ![s, y 0, y 1, y 2] k)
    ut grad utt gradt Dut Dgrad lap I M hS h0 hv0 hg0 t x hx

private lemma isOpen_boxIoo (I : BoxIntegral.Box (Fin 3)) :
    IsOpen (BoxIntegral.Box.Ioo I : Set SpaceChart) := by
  have hset : (BoxIntegral.Box.Ioo I : Set SpaceChart) =
      ⋂ i : Fin 3, (fun y : SpaceChart => y i) ⁻¹' Set.Ioo (I.lower i) (I.upper i) := by
    ext y
    exact ⟨fun h => Set.mem_iInter.mpr fun i => h i (Set.mem_univ i),
      fun h i _ => Set.mem_iInter.mp h i⟩
  rw [hset]
  exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (continuous_apply i)

private lemma linearizedBox_fullEinstein_aux (I : BoxIntegral.Box (Fin 3))
    (P : Linearized.MetricPerturbation) (hsol : IsLinearizedGaugeReducedSol I P)
    (t : ℝ) (x : SpaceChart) (hx : x ∈ BoxIntegral.Box.Ioo I) (i j : Fin 4) :
    Linearized.linearizedEinstein P ![t, x 0, x 1, x 2] i j = 0 := by
  have hgauge := lorenzGauge_propagates_box I P hsol
  have hopen_pre : IsOpen {y : Fin 4 → ℝ | (fun m : Fin 3 => y m.succ) ∈ BoxIntegral.Box.Ioo I} := by
    have hcont : Continuous (fun y : Fin 4 → ℝ => fun m : Fin 3 => y m.succ) :=
      continuous_pi fun m => continuous_apply m.succ
    exact (isOpen_boxIoo I).preimage hcont
  have hmem : ![t, x 0, x 1, x 2] ∈
      {y : Fin 4 → ℝ | (fun m : Fin 3 => y m.succ) ∈ BoxIntegral.Box.Ioo I} := by
    change (fun m : Fin 3 => ![t, x 0, x 1, x 2] m.succ) ∈ BoxIntegral.Box.Ioo I
    have hsub : (fun m : Fin 3 => ![t, x 0, x 1, x 2] m.succ) = x := by
      ext m; fin_cases m <;> rfl
    rwa [hsub]
  have hev : ∀ᶠ y in 𝓝 ![t, x 0, x 1, x 2], ∀ k : Fin 4,
      Linearized.IsLorenzGauge P y k := by
    filter_upwards [hopen_pre.mem_nhds hmem] with y hy k
    have hy_vec : ![y 0, y 1, y 2, y 3] = y := by
      ext m; fin_cases m <;> rfl
    have hyIcc : (fun m : Fin 3 => y m.succ) ∈ BoxIntegral.Box.Icc I :=
      BoxIntegral.Box.Ioo_subset_Icc I hy
    have hg := hgauge (y 0) (fun m => y m.succ) hyIcc k
    simpa [hy_vec] using hg
  have hwg : Linearized.WaveGaugePerturbation P ![t, x 0, x 1, x 2] := {
    smooth := hsol.2.1 ![t, x 0, x 1, x 2]
    gauge := hev
    wave := hsol.2.2.1 ![t, x 0, x 1, x 2] }
  exact Linearized.linearizedEinstein_eq_zero_of_waveGauge P ![t, x 0, x 1, x 2] hwg i j

/-- **Certificate for linearized 3D wave-gauge recovery and constraint propagation**:
`WaveUniqueness3D.wave_zero_of_zero_data3D` forces the Lorenz gauge residual
`Γ_k` to remain zero throughout `ℝ × Box.Icc I`; openness of `Box.Ioo I` then
gives Lorenz gauge in a spacetime neighborhood of every interior box point,
so `Linearized.linearizedEinstein_eq_zero_of_waveGauge` yields `G^{(1)}_{ij} = 0` and
preserves the linearized constraints. -/
lemma linearizedBox_gaugeRecovery (I : BoxIntegral.Box (Fin 3)) :
    GaugeRecoveryCertificate (linearizedBoxGaugeProblem I) where
  gauge_recovered := fun P hsol => lorenzGauge_propagates_box I P hsol
  full_einstein := fun P hsol t x hx i j =>
    linearizedBox_fullEinstein_aux I P hsol t x hx i j
  constraints_preserved := fun P hsol t x hx j =>
    linearizedBox_fullEinstein_aux I P hsol t x hx 0 j

/-! ## C. Nonlinear 4D flat FLRW constraint propagation and Einstein recovery -/

/-- Exact nonlinear FLRW Bianchi/constraint identity: if `a` satisfies the
reduced evolution equation `2 a a'' + (a')² = Λ a²`, then the weighted
Hamiltonian constraint quantity `C(t) = a(t) (3 a'(t)² - Λ a(t)²)` has zero
derivative. -/
lemma hasDerivAt_flrw_constraint_invariant
    (a a' a'' : ℝ → ℝ) (Λ t : ℝ)
    (ha1 : HasDerivAt a (a' t) t)
    (ha2 : HasDerivAt a' (a'' t) t)
    (hevol : 2 * a t * a'' t + a' t ^ 2 = Λ * a t ^ 2) :
    HasDerivAt (fun s : ℝ => a s * (3 * a' s ^ 2 - Λ * a s ^ 2)) 0 t := by
  have ha'2 : HasDerivAt (fun s : ℝ => 3 * a' s ^ 2) (3 * (2 * a' t ^ (2 - 1) * a'' t)) t :=
    ((ha2.pow 2)).const_mul 3
  have ha2p : HasDerivAt (fun s : ℝ => Λ * a s ^ 2) (Λ * (2 * a t ^ (2 - 1) * a' t)) t :=
    ((ha1.pow 2)).const_mul Λ
  have hdiff : HasDerivAt (fun s : ℝ => 3 * a' s ^ 2 - Λ * a s ^ 2)
      (3 * (2 * a' t ^ (2 - 1) * a'' t) - Λ * (2 * a t ^ (2 - 1) * a' t)) t :=
    ha'2.fun_sub ha2p
  have hprod := ha1.fun_mul hdiff
  convert hprod using 1
  simp only [Nat.reduceSub, pow_one]
  linear_combination -(3 * a' t) * hevol

/-- **Nonlinear 4D flat FLRW constraint propagation**: on `Ioo (-δ) δ`, if
`a(t) ≠ 0`, `2 a a'' + (a')² = Λ a²`, and the initial Hamiltonian constraint
`3 a'(0)² = Λ a(0)²` holds at `t = 0`, then `3 a'(t)² = Λ a(t)²` for every
`t ∈ Ioo (-δ) δ`. -/
lemma flrw_constraint_propagates
    (a a' a'' : ℝ → ℝ) (Λ δ : ℝ) (hδ : 0 < δ)
    (ha_ne : ∀ t ∈ Ioo (-δ) δ, a t ≠ 0)
    (ha1 : ∀ t ∈ Ioo (-δ) δ, HasDerivAt a (a' t) t)
    (ha2 : ∀ t ∈ Ioo (-δ) δ, HasDerivAt a' (a'' t) t)
    (hevol : ∀ t ∈ Ioo (-δ) δ, 2 * a t * a'' t + a' t ^ 2 = Λ * a t ^ 2)
    (hham0 : 3 * a' 0 ^ 2 = Λ * a 0 ^ 2) :
    ∀ t ∈ Ioo (-δ) δ, 3 * a' t ^ 2 = Λ * a t ^ 2 := by
  let C : ℝ → ℝ := fun s => a s * (3 * a' s ^ 2 - Λ * a s ^ 2)
  have hC0 : C 0 = 0 := by
    simp only [C, hham0, sub_self, mul_zero]
  have hCd : ∀ s ∈ Ioo (-δ) δ, HasDerivAt C 0 s := fun s hs =>
    hasDerivAt_flrw_constraint_invariant a a' a'' Λ s
      (ha1 s hs) (ha2 s hs) (hevol s hs)
  intro t ht
  have hCt : C t = 0 := by
    rcases lt_trichotomy t 0 with hlt | rfl | hgt
    · have hsub : Icc t 0 ⊆ Ioo (-δ) δ := fun s hs =>
        ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hδ⟩
      have hcont : ContinuousOn C (Icc t 0) :=
        fun s hs => (hCd s (hsub hs)).continuousAt.continuousWithinAt
      have hderiv : ∀ s ∈ Ioo t 0, HasDerivAt C ((fun _ => (0 : ℝ)) s) s :=
        fun s hs => hCd s (hsub (Ioo_subset_Icc_self hs))
      obtain ⟨c, _, hslope⟩ := exists_hasDerivAt_eq_slope C (fun _ => (0 : ℝ)) hlt hcont hderiv
      have hne : (0 : ℝ) - t ≠ 0 := by linarith
      field_simp [hne] at hslope
      linarith
    · exact hC0
    · have hsub : Icc 0 t ⊆ Ioo (-δ) δ := fun s hs =>
        ⟨lt_of_lt_of_le (neg_lt_zero.mpr hδ) hs.1, lt_of_le_of_lt hs.2 ht.2⟩
      have hcont : ContinuousOn C (Icc 0 t) :=
        fun s hs => (hCd s (hsub hs)).continuousAt.continuousWithinAt
      have hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt C ((fun _ => (0 : ℝ)) s) s :=
        fun s hs => hCd s (hsub (Ioo_subset_Icc_self hs))
      obtain ⟨c, _, hslope⟩ := exists_hasDerivAt_eq_slope C (fun _ => (0 : ℝ)) hgt hcont hderiv
      have hne : t - (0 : ℝ) ≠ 0 := by linarith
      field_simp [hne] at hslope
      linarith
  rcases mul_eq_zero.mp hCt with ha0 | hres
  · exact False.elim (ha_ne t ht ha0)
  · linarith

/-- **Full nonlinear 4D Einstein recovery for flat FLRW**: from reduced
evolution `2 a a'' + (a')² = Λ a²` and the initial Hamiltonian constraint
`3 a'(0)² = Λ a(0)²`, the full 4D Einstein equations
`einsteinOf (flrwMetric a 0) (flrwMetricInv a 0) x + Λ flrwMetric a 0 x = 0`
follow at every regular chart point with `x 0 ∈ Ioo (-δ) δ`. -/
lemma flrw_full_einstein_of_reduced
    (a a' a'' : ℝ → ℝ) (Λ δ : ℝ) (hδ : 0 < δ)
    (ha_ne : ∀ t ∈ Ioo (-δ) δ, a t ≠ 0)
    (ha1 : ∀ t ∈ Ioo (-δ) δ, HasDerivAt a (a' t) t)
    (ha2 : ∀ t ∈ Ioo (-δ) δ, HasDerivAt a' (a'' t) t)
    (hevol : ∀ t ∈ Ioo (-δ) δ, 2 * a t * a'' t + a' t ^ 2 = Λ * a t ^ 2)
    (hham0 : 3 * a' 0 ^ 2 = Λ * a 0 ^ 2)
    {x : Fin 4 → ℝ} (hx0 : x 0 ∈ Ioo (-δ) δ)
    (hr : x 1 ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (i j : Fin 4) :
    CoordinateCurvature.einsteinTensor ((flrwSpacetime a 0).metric) ((flrwSpacetime a 0).metricInv) x i j +
      Λ * (flrwSpacetime a 0).metric x i j = 0 := by
  have hham := flrw_constraint_propagates a a' a'' Λ δ hδ ha_ne ha1 ha2 hevol hham0
  have ha_x0 : a (x 0) ≠ 0 := ha_ne (x 0) hx0
  have hdiff_nhds : ∀ᶠ t in 𝓝 (x 0), DifferentiableAt ℝ a t := by
    filter_upwards [isOpen_Ioo.mem_nhds hx0] with t ht
    exact (ha1 t ht).differentiableAt
  have hderiv_eq : deriv a =ᶠ[𝓝 (x 0)] a' := by
    filter_upwards [isOpen_Ioo.mem_nhds hx0] with t ht
    exact (ha1 t ht).deriv
  have hd2 : HasDerivAt (deriv a) (a'' (x 0)) (x 0) :=
    (ha2 (x 0) hx0).congr_of_eventuallyEq hderiv_eq
  have hd1_eq : deriv a (x 0) = a' (x 0) := (ha1 (x 0) hx0).deriv
  have hd2_eq : deriv (deriv a) (x 0) = a'' (x 0) := hd2.deriv
  have hf1 : (deriv a (x 0) / a (x 0)) ^ 2 = Λ / 3 := by
    rw [hd1_eq]
    have h1 := hham (x 0) hx0
    field_simp [ha_x0]
    linarith
  have hf2 : deriv (deriv a) (x 0) / a (x 0) = Λ / 3 := by
    rw [hd2_eq]
    have h1 := hham (x 0) hx0
    have h2 := hevol (x 0) hx0
    have hprod : a (x 0) * (3 * a'' (x 0)) = a (x 0) * (Λ * a (x 0)) := by linarith
    have hcancel := mul_left_cancel₀ ha_x0 hprod
    field_simp [ha_x0]
    linarith
  have hiff := (Cosmology.FLRW.FLRWSpacetime.einsteinTensor_iff_friedmann (flrwSpacetime a 0) 1 Λ 1 0 0 x
    ha_x0 hr (by norm_num) hsin hdiff_nhds hd2.differentiableAt).mpr
      ⟨by simpa using hf1, by simpa using hf2⟩ i j
  have heq : (flrwSpacetime a 0).toCoordinateMetric.einsteinTensor x i j =
      CoordinateCurvature.einsteinTensor ((flrwSpacetime a 0).metric)
        ((flrwSpacetime a 0).metricInv) x i j := rfl
  rw [heq] at hiff
  simpa [GeneralRelativity.perfectFluidStressEnergy] using hiff

/-- Reduced Cauchy problem for flat FLRW with initial Hamiltonian constraint
`3 a'(0)² = Λ a(0)²`. -/
noncomputable def flrwConstraintReducedProblem (Λ δ : ℝ) (_hδ : 0 < δ) :
    ReducedCauchyProblem minkowskiChart where
  data := minkowskiChartInitialData
  Solution := ℝ → ℝ
  IsSolution := fun a =>
    ∃ a' a'' : ℝ → ℝ,
      (∀ t ∈ Ioo (-δ) δ, a t ≠ 0 ∧ HasDerivAt a (a' t) t ∧ HasDerivAt a' (a'' t) t ∧
        2 * a t * a'' t + a' t ^ 2 = Λ * a t ^ 2) ∧
      3 * a' 0 ^ 2 = Λ * a 0 ^ 2
  HasCauchyData := fun a =>
    ∃ v : ℝ, HasDerivAt a v 0 ∧ 3 * v ^ 2 = Λ * a 0 ^ 2
  IsWaveGauge := fun a => ∀ t ∈ Ioo (-δ) δ, a t ≠ 0

/-- Gauge-recovery problem attached to `flrwConstraintReducedProblem`. -/
noncomputable def flrwGaugeRecoveryProblem (Λ δ : ℝ) (hδ : 0 < δ) :
    GaugeRecoveryProblem (flrwConstraintReducedProblem Λ δ hδ) where
  GaugeRecovered := fun a => ∀ t ∈ Ioo (-δ) δ, a t ≠ 0
  IsFullEinsteinSolution := fun a =>
    ∀ x : Fin 4 → ℝ, x 0 ∈ Ioo (-δ) δ → x 1 ≠ 0 → Real.sin (x 2) ≠ 0 →
      ∀ i j : Fin 4,
        CoordinateCurvature.einsteinTensor ((flrwSpacetime a 0).metric) ((flrwSpacetime a 0).metricInv) x i j +
          Λ * (flrwSpacetime a 0).metric x i j = 0
  ConstraintsPreserved := fun a =>
    ∀ t ∈ Ioo (-δ) δ, ∃ a', HasDerivAt a a' t ∧ 3 * a' ^ 2 = Λ * a t ^ 2

/-- **Certificate for nonlinear 4D flat FLRW constraint propagation and full
Einstein recovery)**: every reduced solution preserves the nonlinear Hamiltonian
constraint `3 (a')² = Λ a²` on `Ioo (-δ) δ` and satisfies the full 4D Einstein
equations `G_{ij} + Λ g_{ij} = 0` at every regular chart point. -/
lemma flrw_gaugeRecovery (Λ δ : ℝ) (hδ : 0 < δ) :
    GaugeRecoveryCertificate (flrwGaugeRecoveryProblem Λ δ hδ) where
  gauge_recovered := fun _ ⟨_, _, hsol, _⟩ t ht => (hsol t ht).1
  full_einstein := fun a ⟨a', a'', hsol, hham0⟩ _ hx0 hr hsin i j =>
    flrw_full_einstein_of_reduced a a' a'' Λ δ hδ
      (fun t ht => (hsol t ht).1)
      (fun t ht => (hsol t ht).2.1)
      (fun t ht => (hsol t ht).2.2.1)
      (fun t ht => (hsol t ht).2.2.2)
      hham0 hx0 hr hsin i j
  constraints_preserved := fun a ⟨a', a'', hsol, hham0⟩ t ht =>
    ⟨a' t, (hsol t ht).2.1,
      flrw_constraint_propagates a a' a'' Λ δ hδ
        (fun s hs => (hsol s hs).1)
        (fun s hs => (hsol s hs).2.1)
        (fun s hs => (hsol s hs).2.2.1)
        (fun s hs => (hsol s hs).2.2.2)
        hham0 t ht⟩

end GeneralRelativity
