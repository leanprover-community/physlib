/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/

module

public import PhyslibAlpha.Relativity.General.ManifoldInterface
public import PhyslibAlpha.Relativity.Metrics.Basic
public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Tactic

/-!

# Kruskal–Szekeres chart

## i. Overview

This module adds a Kruskal–Szekeres chart for Schwarzschild spacetime.  In
Kruskal coordinates `(T, X, θ, φ)` the line element is

`ds² = F(r)(-dT² + dX²) + r² dΩ²`,

with

`F(r) = (32 M³ / r) exp(-r / (2M))`

and `r` determined implicitly by

`X² - T² = (r/(2M) - 1) exp(r/(2M))`.

The conformal factor is finite and nonzero at the horizon `r = 2M`, so the
metric and its inverse remain regular across `r = 2M`.  The singularity
`r = 0` corresponds to `T² - X² = 1` and is excluded by the domain condition
`X² - T² > -1`.

## ii. Key results

- `metric`, `metricInv` : Kruskal–Szekeres components and explicit inverse.
- `metricTensor` : bundled `MetricTensor 4` for `M > 0`, `sin θ ≠ 0`.
- `horizonPoint` : a point with `X = T`, hence `r = 2M`.
- `horizonTensor` : the bundled metric at the horizon.
- `horizonTensor_g_00`, `horizonTensor_g_11`, etc. : finite nonzero
  conformal factor and inverse at the horizon.
- `horizonTensor_regular` : the horizon bundle is a certified
  `MetricTensor 4`.
- `partialChart`, `partialChartDomain` : the Kruskal–Szekeres metric packaged
  as a `PartialChartSpacetime` on its restricted domain.
- `partialChart_isSmooth` : the Kruskal partial chart satisfies the smoothness
  certificate `PartialChartSpacetime.IsSmooth`, via the inverse function
  theorem applied to the implicit radial map.
- `horizonPoint_mem_partialChartDomain` : the horizon lies in that domain.

## iii. Table of contents

- A. Implicit radial function
- B. Metric and inverse
- C. The partial chart
- D. Horizon regularity

## iv. References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019,
  Ch. 7, pp. 175–176. [ref: Carroll1997, pp. 175–176]

-/
@[expose] public section

namespace GeneralRelativity

namespace KruskalSzekeres

open Real Set
open scoped ContDiff

/-- The Kruskal radial function `(y - 1) exp y`, with `y = r/(2M)`. -/
private noncomputable def g (y : ℝ) : ℝ := (y - 1) * Real.exp y

/-- Derivative of `g`. -/
private lemma deriv_g (y : ℝ) : deriv g y = y * Real.exp y := by
  unfold g
  simp [deriv_const]
  ring

/-- `g` is strictly increasing on the positive half-line. -/
private lemma strictMono_g_pos : StrictMonoOn g (Set.Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · intro r hr
    have : DifferentiableAt ℝ g r := by
      unfold g
      fun_prop
    exact this.continuousAt.continuousWithinAt
  · intro y hy
    have hy0 : 0 < y := by
      rw [interior_Ioi] at hy
      exact hy
    rw [deriv_g y]
    exact mul_pos hy0 (Real.exp_pos y)

/-! ## A. Implicit radial function -/

/-- The implicit Kruskal radial function `F_M(r) = (r/(2M) - 1) exp(r/(2M))`. -/
noncomputable def kruskalF (M r : ℝ) : ℝ :=
  (r / (2 * M) - 1) * Real.exp (r / (2 * M))

/-- `kruskalF M` is strictly increasing in `r` on `(0, ∞)` when `M > 0`. -/
private lemma kruskalF_strictMono (M : ℝ) (hM : 0 < M) :
    StrictMonoOn (kruskalF M) (Set.Ioi 0) := by
  intro r1 hr1 r2 hr2 hlt
  have hy1 : 0 < r1 / (2 * M) := div_pos hr1 (by linarith)
  have hy2 : 0 < r2 / (2 * M) := div_pos hr2 (by linarith)
  have hgy : g (r1 / (2 * M)) < g (r2 / (2 * M)) := by
    have hlt' : r1 / (2 * M) < r2 / (2 * M) := by
      exact div_lt_div_of_pos_right hlt (by linarith : 0 < 2 * M)
    exact strictMono_g_pos hy1 hy2 hlt'
  simpa [kruskalF, g] using hgy

/-- Injectivity of `kruskalF M` on `(0, ∞)`. -/
private lemma kruskalF_injective (M : ℝ) (hM : 0 < M) :
    ∀ r1 r2, 0 < r1 → 0 < r2 → kruskalF M r1 = kruskalF M r2 → r1 = r2 := by
  intro r1 r2 hr1 hr2 heq
  by_cases hlt : r1 < r2
  · exact False.elim (lt_irrefl (kruskalF M r1) (heq.symm ▸ kruskalF_strictMono M hM hr1 hr2 hlt))
  · by_cases hgt : r2 < r1
    · exact False.elim (lt_irrefl (kruskalF M r2) (heq ▸ kruskalF_strictMono M hM hr2 hr1 hgt))
    · exact le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)

/-- The positive radius selected by the implicit Kruskal relation. -/
noncomputable def kruskalRadius (M : ℝ) (w : ℝ) : ℝ :=
  if _hM : 0 < M then
    (Function.invFun (fun r : {r : ℝ // 0 < r} => kruskalF M r.val) w).val
  else
    2 * M

/-- The selected radius is always positive when `M > 0`. -/
lemma kruskalRadius_pos (M : ℝ) (hM : 0 < M) (w : ℝ) :
    0 < kruskalRadius M w := by
  simp [kruskalRadius, hM]
  exact (Function.invFun (fun r : {r : ℝ // 0 < r} => kruskalF M r.val) w).property

/-- At `w = 0` the implicit relation gives `r = 2M`. -/
lemma kruskalRadius_zero (M : ℝ) (hM : 0 < M) :
    kruskalRadius M 0 = 2 * M := by
  have hex : ∃ r : {r : ℝ // 0 < r}, kruskalF M r.val = 0 := by
    refine ⟨⟨2 * M, by linarith⟩, ?_⟩
    simp [kruskalF]
    field_simp [hM.ne']
    ring
  have hval : kruskalF M (Function.invFun (fun r : {r : ℝ // 0 < r} => kruskalF M r.val) 0).val = 0 := by
    exact Function.invFun_eq hex
  have hrpos : 0 < (Function.invFun (fun r : {r : ℝ // 0 < r} => kruskalF M r.val) 0).val := by
    exact (Function.invFun (fun r : {r : ℝ // 0 < r} => kruskalF M r.val) 0).property
  have hrhs : kruskalF M (2 * M) = 0 := by
    simp [kruskalF]
    field_simp [hM.ne']
    ring
  have heqval : kruskalF M (Function.invFun (fun r : {r : ℝ // 0 < r} => kruskalF M r.val) 0).val =
      kruskalF M (2 * M) := by
    rw [hval, hrhs]
  have heq : (Function.invFun (fun r : {r : ℝ // 0 < r} => kruskalF M r.val) 0).val = 2 * M :=
    kruskalF_injective M hM _ (2 * M) hrpos (by linarith) heqval
  simp [kruskalRadius, hM, heq]

/-- The Kruskal radial map `r ↦ kruskalF M r` is smooth. -/
lemma contDiff_kruskalF (M : ℝ) (_hM : 0 < M) :
    ContDiff ℝ ∞ (fun r : ℝ => kruskalF M r) := by
  unfold kruskalF
  fun_prop

/-- Derivative of the Kruskal radial map. -/
lemma deriv_kruskalF (M r : ℝ) (hM : 0 < M) :
    deriv (fun s : ℝ => kruskalF M s) r =
      r * Real.exp (r / (2 * M)) / (4 * M ^ 2) := by
  have hdiff1 : DifferentiableAt ℝ (fun s : ℝ => s / (2 * M) - 1) r := by
    fun_prop
  have hdiff2 : DifferentiableAt ℝ (fun s : ℝ => Real.exp (s / (2 * M))) r := by
    fun_prop
  have hmul :
      deriv (fun s : ℝ => (s / (2 * M) - 1) * Real.exp (s / (2 * M))) r =
        deriv (fun s : ℝ => s / (2 * M) - 1) r * Real.exp (r / (2 * M)) +
          (r / (2 * M) - 1) * deriv (fun s : ℝ => Real.exp (s / (2 * M))) r := by
    exact deriv_mul hdiff1 hdiff2
  have hd1 : deriv (fun s : ℝ => s / (2 * M) - 1) r = 1 / (2 * M) := by
    have hsub : deriv (fun s : ℝ => s / (2 * M) - 1) r =
        deriv (fun s : ℝ => s / (2 * M)) r - deriv (fun s : ℝ => (1 : ℝ)) r := by
      exact deriv_sub (by fun_prop) (by fun_prop)
    rw [hsub, deriv_const]
    have : deriv (fun s : ℝ => s / (2 * M)) r = 1 / (2 * M) := by
      have heq : (fun s : ℝ => s / (2 * M)) = (fun s : ℝ => (2 * M)⁻¹ * s) := by
        funext s
        field_simp [hM.ne']
      rw [heq, deriv_const_mul_id ((2 * M)⁻¹), one_div]
    rw [this]
    simp
  have hd2 : deriv (fun s : ℝ => Real.exp (s / (2 * M))) r =
      Real.exp (r / (2 * M)) / (2 * M) := by
    have hchain : deriv (fun s : ℝ => Real.exp (s / (2 * M))) r =
        Real.exp (r / (2 * M)) * deriv (fun s : ℝ => s / (2 * M)) r := by
      have hexp : deriv Real.exp (r / (2 * M)) = Real.exp (r / (2 * M)) := by
        rw [Real.deriv_exp]
      have hcomp := deriv_comp r (Real.differentiable_exp.differentiableAt) (by fun_prop : DifferentiableAt ℝ (fun s => s / (2 * M)) r)
      rw [hexp] at hcomp
      exact hcomp
    rw [hchain]
    have : deriv (fun s : ℝ => s / (2 * M)) r = 1 / (2 * M) := by
      have heq : (fun s : ℝ => s / (2 * M)) = (fun s : ℝ => (2 * M)⁻¹ * s) := by
        funext s
        field_simp [hM.ne']
      rw [heq, deriv_const_mul_id ((2 * M)⁻¹), one_div]
    rw [this]
    exact mul_one_div _ _
  have hkr : (fun s : ℝ => kruskalF M s) = (fun s : ℝ => (s / (2 * M) - 1) * Real.exp (s / (2 * M))) := by
    funext s
    simp [kruskalF]
  rw [hkr, hmul, hd1, hd2]
  have hexpnz : Real.exp (r / (2 * M)) ≠ 0 := Real.exp_ne_zero _
  field_simp [hM.ne', hexpnz]
  ring

/-- The Kruskal radial map sends `(0, ∞)` onto `(-1, ∞)`. -/
lemma kruskalF_exists_pos (M : ℝ) (hM : 0 < M) (w : ℝ) (hw : -1 < w) :
    ∃ r : ℝ, 0 < r ∧ kruskalF M r = w := by
  let y1 : ℝ := if w < 0 then (w + 1) / 2 else (1 : ℝ) / 2
  let r1 : ℝ := 2 * M * y1
  have hy1pos : 0 < y1 := by
    by_cases hw0 : w < 0
    · simp [y1, hw0]
      linarith [hw]
    · simp [y1, hw0]
  have hy1le : y1 ≤ (1 : ℝ) / 2 := by
    by_cases hw0 : w < 0
    · simp [y1, hw0]
      linarith [hw]
    · simp [y1, hw0]
  have hr1pos : 0 < r1 := by
    dsimp [r1]
    positivity
  have hr1lt : kruskalF M r1 < w := by
    have hexp : 1 ≤ Real.exp y1 := Real.one_le_exp (le_of_lt hy1pos)
    have hneg : y1 - 1 ≤ 0 := by linarith [hy1le]
    have hle : (y1 - 1) * Real.exp y1 ≤ y1 - 1 := by
      nlinarith [hexp, hneg]
    have hry1 : r1 / (2 * M) = y1 := by
      dsimp [r1]
      field_simp [hM.ne']
    have hkr : kruskalF M r1 = (y1 - 1) * Real.exp y1 := by
      dsimp [kruskalF]
      rw [hry1]
    rw [hkr]
    have hy1ltw : y1 - 1 < w := by
      by_cases hw0 : w < 0
      · have hval : y1 = (w + 1) / 2 := by
          simp [y1, hw0]
        rw [hval]
        linarith [hw]
      · have hval : y1 = (1 : ℝ) / 2 := by
          simp [y1, hw0]
        rw [hval]
        linarith [le_of_not_gt hw0]
    exact lt_of_le_of_lt hle hy1ltw
  let y2 : ℝ := w + 2
  let r2 : ℝ := 2 * M * y2
  have hy2gt1 : 1 < y2 := by
    linarith [hw]
  have hr2pos : 0 < r2 := by
    dsimp [r2]
    positivity
  have hr2gt : w < kruskalF M r2 := by
    have hry2 : r2 / (2 * M) = y2 := by
      dsimp [r2]
      field_simp [hM.ne']
    have hkr : kruskalF M r2 = (y2 - 1) * Real.exp y2 := by
      dsimp [kruskalF]
      rw [hry2]
    rw [hkr]
    have hy2 : y2 - 1 = w + 1 := by
      simp [y2]
      ring
    rw [hy2]
    have hexp : 1 ≤ Real.exp y2 := Real.one_le_exp (by linarith [hy2gt1])
    have hpos : 0 < w + 1 := by linarith [hw]
    have : w + 1 ≤ (w + 1) * Real.exp y2 := by
      nlinarith [hexp, hpos]
    linarith [this]
  have hr1r2 : r1 < r2 := by
    have : r1 ≤ M := by
      dsimp [r1]
      nlinarith [hy1le, hM.le]
    have : r2 > 2 * M := by
      dsimp [r2]
      nlinarith [hy2gt1, hM]
    linarith
  have hcont : ContinuousOn (kruskalF M) (Set.Icc r1 r2) :=
    (contDiff_kruskalF M hM).continuous.continuousOn
  have hsubset := intermediate_value_Icc (le_of_lt hr1r2) hcont
  have hwmem : w ∈ Set.Icc (kruskalF M r1) (kruskalF M r2) :=
    ⟨le_of_lt hr1lt, le_of_lt hr2gt⟩
  have : w ∈ (kruskalF M) '' Set.Icc r1 r2 := hsubset hwmem
  rcases this with ⟨c, hc, hfc⟩
  refine ⟨c, ?_, hfc⟩
  exact lt_of_lt_of_le hr1pos (Set.mem_Icc.1 hc).1

/-- The Kruskal radius is smooth at any `w₀ > -1`. -/
lemma contDiffAt_kruskalRadius (M : ℝ) (hM : 0 < M) (w0 : ℝ) (hw0 : -1 < w0) :
    ContDiffAt ℝ ∞ (fun w : ℝ => kruskalRadius M w) w0 := by
  obtain ⟨r0, hr0pos, hr0eq⟩ := kruskalF_exists_pos M hM w0 hw0
  have hcd : ContDiffAt ℝ ∞ (fun r : ℝ => kruskalF M r) r0 :=
    (contDiff_kruskalF M hM).contDiffAt
  have hdnz : deriv (fun s : ℝ => kruskalF M s) r0 ≠ 0 := by
    rw [deriv_kruskalF M r0 hM]
    have hexp : Real.exp (r0 / (2 * M)) ≠ 0 := Real.exp_ne_zero _
    have hden : (4 : ℝ) * M ^ 2 ≠ 0 := by positivity
    exact div_ne_zero (mul_ne_zero hr0pos.ne' hexp) hden
  have hd : HasDerivAt (fun r : ℝ => kruskalF M r)
      (deriv (fun s : ℝ => kruskalF M s) r0) r0 :=
    (hcd.differentiableAt (by simp)).hasDerivAt
  have hf' : HasFDerivAt (fun r : ℝ => kruskalF M r)
      (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hdnz) : ℝ →L[ℝ] ℝ) r0 :=
    hd.hasFDerivAt_equiv hdnz
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hli : ContDiffAt ℝ ∞ (ContDiffAt.localInverse hcd hf' hn) (kruskalF M r0) :=
    ContDiffAt.to_localInverse hcd hf' hn
  have hkr_left : ∀ᶠ r in nhds r0, kruskalRadius M (kruskalF M r) = r := by
    have hpos : ∀ᶠ r in nhds r0, (0 : ℝ) < r := Ioi_mem_nhds hr0pos
    filter_upwards [hpos] with r hr
    have hex : ∃ a : {r : ℝ // 0 < r},
        (fun a : {r : ℝ // 0 < r} => kruskalF M a.val) a = kruskalF M r :=
      ⟨⟨r, hr⟩, rfl⟩
    have h1 : kruskalF M (Function.invFun
        (fun a : {r : ℝ // 0 < r} => kruskalF M a.val) (kruskalF M r)).val =
        kruskalF M r :=
      Function.invFun_eq hex
    have hpos2 : 0 < (Function.invFun
        (fun a : {r : ℝ // 0 < r} => kruskalF M a.val) (kruskalF M r)).val :=
      (Function.invFun (fun a : {r : ℝ // 0 < r} => kruskalF M a.val) (kruskalF M r)).property
    have hinv : (Function.invFun
        (fun a : {r : ℝ // 0 < r} => kruskalF M a.val) (kruskalF M r)).val = r :=
      kruskalF_injective M hM _ _ hpos2 hr h1
    have hif : kruskalRadius M (kruskalF M r) = (Function.invFun
        (fun a : {r : ℝ // 0 < r} => kruskalF M a.val) (kruskalF M r)).val := by
      simp [kruskalRadius, hM]
    rw [hif]
    exact hinv
  have heq : (fun w : ℝ => kruskalRadius M w) =ᶠ[nhds (kruskalF M r0)]
      (ContDiffAt.localInverse hcd hf' hn) :=
    (hcd.hasStrictFDerivAt hf' hn).localInverse_unique
      (g := fun w : ℝ => kruskalRadius M w) hkr_left
  have hmain : ContDiffAt ℝ ∞ (fun w : ℝ => kruskalRadius M w) (kruskalF M r0) :=
    hli.congr_of_eventuallyEq heq
  rw [hr0eq] at hmain
  exact hmain

/-- The Kruskal radius is smooth on `w > -1`. -/
lemma contDiffOn_kruskalRadius (M : ℝ) (hM : 0 < M) :
    ContDiffOn ℝ ∞ (fun w : ℝ => kruskalRadius M w) (Set.Ioi (-1)) := by
  rw [isOpen_Ioi.contDiffOn_iff]
  intro w hw
  exact contDiffAt_kruskalRadius M hM w hw


/-! ## B. Metric and inverse -/

/-- Kruskal–Szekeres metric in coordinates `(T, X, θ, φ)`.  The radial
coordinate is `r = kruskalRadius M (X² - T²)`. -/
noncomputable def metric (M : ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  fun i j =>
    let r := kruskalRadius M (x 1 ^ 2 - x 0 ^ 2)
    let F := 32 * M ^ 3 / r * Real.exp (-r / (2 * M))
    if i = 0 then
      if j = 0 then -F else 0
    else if i = 1 then
      if j = 1 then F else 0
    else if i = 2 then
      if j = 2 then r ^ 2 else 0
    else
      if j = 3 then r ^ 2 * Real.sin (x 2) ^ 2 else 0

/-- Explicit inverse of `metric`. -/
noncomputable def metricInv (M : ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  fun i j =>
    let r := kruskalRadius M (x 1 ^ 2 - x 0 ^ 2)
    let F := 32 * M ^ 3 / r * Real.exp (-r / (2 * M))
    if i = 0 then
      if j = 0 then -(F⁻¹) else 0
    else if i = 1 then
      if j = 1 then F⁻¹ else 0
    else if i = 2 then
      if j = 2 then (r ^ 2)⁻¹ else 0
    else
      if j = 3 then (r ^ 2 * Real.sin (x 2) ^ 2)⁻¹ else 0

lemma metric_symm (M : ℝ) (x : Fin 4 → ℝ) : IsSymm (metric M x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [metric, Matrix.transpose_apply]

lemma metric_mul_inv (M : ℝ) (x : Fin 4 → ℝ) (hM : 0 < M)
    (hsin : Real.sin (x 2) ≠ 0) :
    metric M x * metricInv M x = 1 := by
  let r := kruskalRadius M (x 1 ^ 2 - x 0 ^ 2)
  have hr : 0 < r := kruskalRadius_pos M hM _
  have hrne : kruskalRadius M (x 1 ^ 2 - x 0 ^ 2) ≠ 0 := hr.ne'
  have hF : 32 * M ^ 3 / r * Real.exp (-r / (2 * M)) ≠ 0 := by
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num : (32 : ℝ) ≠ 0) (pow_ne_zero 3 (by linarith : M ≠ 0))) hr.ne') (Real.exp_ne_zero _)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metric, metricInv, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp [hM.ne', hrne, hsin, hF]

lemma metricInv_mul (M : ℝ) (x : Fin 4 → ℝ) (hM : 0 < M)
    (hsin : Real.sin (x 2) ≠ 0) :
    metricInv M x * metric M x = 1 := by
  let r := kruskalRadius M (x 1 ^ 2 - x 0 ^ 2)
  have hr : 0 < r := kruskalRadius_pos M hM _
  have hrne : kruskalRadius M (x 1 ^ 2 - x 0 ^ 2) ≠ 0 := hr.ne'
  have hF : 32 * M ^ 3 / r * Real.exp (-r / (2 * M)) ≠ 0 := by
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num : (32 : ℝ) ≠ 0) (pow_ne_zero 3 (by linarith : M ≠ 0))) hr.ne') (Real.exp_ne_zero _)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metric, metricInv, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp [hM.ne', hrne, hsin, hF]

/-- Bundled Kruskal–Szekeres metric. -/
noncomputable def metricTensor (M : ℝ) (x : Fin 4 → ℝ) (hM : 0 < M)
    (hsin : Real.sin (x 2) ≠ 0) : MetricTensor 4 where
  g := metric M x
  ginv := metricInv M x
  symm := metric_symm M x
  inv_left := metric_mul_inv M x hM hsin
  inv_right := metricInv_mul M x hM hsin

/-! ## C. The partial chart -/

/-- The open Kruskal–Szekeres chart domain: outside the singularity, i.e.
`X² - T² > -1`, and off the polar axis `sin θ ≠ 0`. -/
def partialChartDomain : Set (Fin 4 → ℝ) :=
  {x | -1 < x 1 ^ 2 - x 0 ^ 2 ∧ Real.sin (x 2) ≠ 0}

/-- The Kruskal–Szekeres chart domain is open. -/
lemma partialChartDomain_isOpen : IsOpen partialChartDomain := by
  have hcont : Continuous (fun x : SpacetimeChart => x 1 ^ 2 - x 0 ^ 2) :=
    ((continuous_apply 1).pow 2).sub ((continuous_apply 0).pow 2)
  have h1 : IsOpen {x : SpacetimeChart | -1 < x 1 ^ 2 - x 0 ^ 2} :=
    hcont.isOpen_preimage (Set.Ioi (-1)) isOpen_Ioi
  have hsin_cont : Continuous (fun x : SpacetimeChart => Real.sin (x 2)) :=
    Real.continuous_sin.comp (continuous_apply 2)
  have h2 : IsOpen {x : SpacetimeChart | Real.sin (x 2) ≠ 0} :=
    hsin_cont.isOpen_preimage ({0}ᶜ) isOpen_compl_singleton
  rw [partialChartDomain, Set.ofPred_and]
  exact h1.inter h2

/-- The Kruskal–Szekeres metric packaged as a partial chart on its restricted
domain.  Smoothness is certified separately by `partialChart_isSmooth`. -/
noncomputable def partialChart (M : ℝ) (hM : 0 < M) : PartialChartSpacetime where
  domain := partialChartDomain
  domain_open := partialChartDomain_isOpen
  metric := fun x hx => metricTensor M x hM hx.2

/-- Alias for `partialChart`. -/
noncomputable def partialChartSpacetime (M : ℝ) (hM : 0 < M) :
    PartialChartSpacetime :=
  partialChart M hM

/-- Alias for `partialChart`. -/
noncomputable def restrictedChart (M : ℝ) (hM : 0 < M) : PartialChartSpacetime :=
  partialChart M hM

/-- The radius pulled back to chart coordinates is smooth on the domain. -/
lemma contDiffOn_radius_comp (M : ℝ) (hM : 0 < M) :
    ContDiffOn ℝ ∞ (fun x : SpacetimeChart => kruskalRadius M (x 1 ^ 2 - x 0 ^ 2))
      partialChartDomain := by
  have hsq : ContDiffOn ℝ ∞ (fun x : SpacetimeChart => x 1 ^ 2 - x 0 ^ 2)
      partialChartDomain := by
    exact ((contDiffOn_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) 1 partialChartDomain).pow 2).sub
      ((contDiffOn_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) 0 partialChartDomain).pow 2)
  have hmem : Set.MapsTo (fun x : SpacetimeChart => x 1 ^ 2 - x 0 ^ 2)
      partialChartDomain (Set.Ioi (-1)) := by
    intro x hx
    obtain ⟨h1, -⟩ := hx
    exact h1
  exact (contDiffOn_kruskalRadius M hM).comp hsq hmem

/-- Each Kruskal–Szekeres metric component is smooth on the chart domain. -/
lemma contDiffOn_ks_metric_component (M : ℝ) (hM : 0 < M) (i j : Fin 4) :
    ContDiffOn ℝ ∞ (fun x : SpacetimeChart => metric M x i j) partialChartDomain := by
  have hr : ContDiffOn ℝ ∞
      (fun x : SpacetimeChart => kruskalRadius M (x 1 ^ 2 - x 0 ^ 2)) partialChartDomain :=
    contDiffOn_radius_comp M hM
  have hrpos : ∀ x ∈ partialChartDomain,
      kruskalRadius M (x 1 ^ 2 - x 0 ^ 2) ≠ 0 := by
    intro x _
    exact (kruskalRadius_pos M hM _).ne'
  have hsin : ContDiffOn ℝ ∞ (fun x : SpacetimeChart => Real.sin (x 2))
      partialChartDomain :=
    (Real.contDiff_sin.comp
      (contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) 2)).contDiffOn
  have hF : ContDiffOn ℝ ∞ (fun x : SpacetimeChart =>
      32 * M ^ 3 / kruskalRadius M (x 1 ^ 2 - x 0 ^ 2) *
        Real.exp (-kruskalRadius M (x 1 ^ 2 - x 0 ^ 2) / (2 * M))) partialChartDomain := by
    apply ContDiffOn.mul
    · apply ContDiffOn.div
      · exact contDiffOn_const
      · exact hr
      · intro x hx
        exact hrpos x hx
    · exact Real.contDiff_exp.comp_contDiffOn (hr.neg.div_const (2 * M))
  fin_cases i <;> fin_cases j <;>
    simp [metric]
  · exact hF.neg
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact hF
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact hr.pow 2
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact (hr.pow 2).mul (hsin.pow 2)

/-- The Kruskal–Szekeres partial chart is smooth on its domain. -/
lemma partialChart_isSmooth (M : ℝ) (hM : 0 < M) : (partialChart M hM).IsSmooth := by
  intro i j
  refine ⟨fun x => metric M x i j, contDiffOn_ks_metric_component M hM i j, ?_⟩
  intro x hx
  rfl

/-! ## D. Horizon regularity -/

/-- A horizon point has `X = T`, hence `X² - T² = 0` and `r = 2M`. -/
def horizonPoint (_M T θ φ : ℝ) : Fin 4 → ℝ :=
  ![T, T, θ, φ]

lemma horizonPoint_sq_diff (M T θ φ : ℝ) :
    (horizonPoint M T θ φ) 1 ^ 2 - (horizonPoint M T θ φ) 0 ^ 2 = 0 := by
  simp [horizonPoint]

/-- A horizon point lies in the Kruskal–Szekeres chart domain. -/
lemma horizonPoint_mem_partialChartDomain (M T θ φ : ℝ)
    (hsin : Real.sin θ ≠ 0) :
    horizonPoint M T θ φ ∈ partialChartDomain := by
  refine ⟨?_, ?_⟩
  · simp [horizonPoint]
  · simpa [horizonPoint] using hsin

/-- Bundled metric at a horizon point. -/
noncomputable def horizonTensor (M T θ φ : ℝ) (hM : 0 < M)
    (hsin : Real.sin θ ≠ 0) : MetricTensor 4 :=
  metricTensor M (horizonPoint M T θ φ) hM
    (by simpa [horizonPoint] using hsin)

/-- The conformal factor at the horizon. -/
lemma horizonConformalFactor (M _T _θ _φ : ℝ) (hM : 0 < M) :
    (32 * M ^ 3 / kruskalRadius M 0 * Real.exp (-kruskalRadius M 0 / (2 * M))) =
      16 * M ^ 2 / Real.exp 1 := by
  rw [kruskalRadius_zero M hM]
  field_simp [hM.ne']
  simp [mul_assoc, ← Real.exp_add, Real.exp_zero]
  ring

/-- The `TT` component at the horizon is finite and nonzero. -/
lemma horizonTensor_g_00 (M T θ φ : ℝ) (hM : 0 < M)
    (hsin : Real.sin θ ≠ 0) :
    (horizonTensor M T θ φ hM hsin).g 0 0 =
      -(16 * M ^ 2 / Real.exp 1) := by
  simp [horizonTensor, metricTensor, metric, horizonPoint, kruskalRadius_zero M hM]
  field_simp [hM.ne']
  simp [mul_assoc, ← Real.exp_add, Real.exp_zero]
  ring

/-- The `XX` component at the horizon. -/
lemma horizonTensor_g_11 (M T θ φ : ℝ) (hM : 0 < M)
    (hsin : Real.sin θ ≠ 0) :
    (horizonTensor M T θ φ hM hsin).g 1 1 =
      16 * M ^ 2 / Real.exp 1 := by
  simp [horizonTensor, metricTensor, metric, horizonPoint, kruskalRadius_zero M hM]
  field_simp [hM.ne']
  simp [mul_assoc, ← Real.exp_add, Real.exp_zero]
  ring

/-- The inverse `TT` component at the horizon. -/
lemma horizonTensor_ginv_00 (M T θ φ : ℝ) (hM : 0 < M)
    (hsin : Real.sin θ ≠ 0) :
    (horizonTensor M T θ φ hM hsin).ginv 0 0 =
      -(Real.exp 1 / (16 * M ^ 2)) := by
  simp [horizonTensor, metricTensor, metricInv, horizonPoint, kruskalRadius_zero M hM]
  field_simp [hM.ne']
  rw [show Real.exp (-1) * 32 * Real.exp 1 = Real.exp (-1) * Real.exp 1 * 32 by ring]
  rw [← Real.exp_add (-1) 1]
  simp [Real.exp_zero]
  ring

/-- The inverse `XX` component at the horizon. -/
lemma horizonTensor_ginv_11 (M T θ φ : ℝ) (hM : 0 < M)
    (hsin : Real.sin θ ≠ 0) :
    (horizonTensor M T θ φ hM hsin).ginv 1 1 =
      Real.exp 1 / (16 * M ^ 2) := by
  simp [horizonTensor, metricTensor, metricInv, horizonPoint, kruskalRadius_zero M hM]
  field_simp [hM.ne']
  rw [show Real.exp (-1) * 32 * Real.exp 1 = Real.exp (-1) * Real.exp 1 * 32 by ring]
  rw [← Real.exp_add (-1) 1]
  simp [Real.exp_zero]
  ring

/-- The horizon bundle is a certified nondegenerate metric. -/
lemma horizonTensor_regular (M T θ φ : ℝ) (hM : 0 < M)
    (hsin : Real.sin θ ≠ 0) :
    Nonempty (MetricTensor 4) := by
  exact ⟨horizonTensor M T θ φ hM hsin⟩

end KruskalSzekeres

end GeneralRelativity
