/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import PhyslibAlpha.Relativity.General.Schwarzschild.Basic
public import PhyslibAlpha.Relativity.Metrics.StaticSphericalMetric
public import PhyslibAlpha.Relativity.Tensors.MaxwellStressEnergy
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!

# The Reissner–Nordström electrovacuum black hole

Coordinate metric, electrovacuum Maxwell stress-energy tensor, pipeline verification of
`G_{ij} = 8 π T_{ij}`, vanishing scalar curvature, and inner/outer horizon structure for
`ReissnerNordstromSpacetime`.

## i. Overview

A static spherically symmetric charged black hole `S : ReissnerNordstromSpacetime` of mass `S.M`
and electric charge `S.Q` has line element `ds² = -f(r) dt² + f(r)⁻¹ dr² + r² dΩ²` with lapse
function `f(r) = 1 - 2 M / r + Q² / r²`, sourced by a radial Coulomb electric field
`F_{01} = -Q / r²`, `F_{10} = Q / r²`.

Feeding `S.metric` through `GeneralRelativity.StaticSpherical` and `GeneralRelativity.Pipeline`,
this module proves:

- `ReissnerNordstromSpacetime.ricciScalarOf` : vanishing Ricci scalar `R = 0`, matching
  `ReissnerNordstromSpacetime.maxwellStressEnergy_trace_zero` (`g^{ij} T^{EM}_{ij} = 0` in 4D);
- `ReissnerNordstromSpacetime.einsteinTensorOf_eq_maxwell` : the full 4D electrovacuum
  Einstein–Maxwell field equations `G_{ij} = 8 π T^{EM}_{ij}` at every index pair `(i, j)`;
- horizon theorems (`ReissnerNordstromSpacetime.lapse_horizonPlus`,
  `ReissnerNordstromSpacetime.lapse_horizonMinus`, extremal double root when `Q² = M²`, and
  positivity `0 < S.lapse r` in the overcharged naked-singularity regime `M² < Q²`).

## ii. Key results

- `ReissnerNordstromSpacetime`, `ReissnerNordstromSpacetime.lapse`,
  `ReissnerNordstromSpacetime.metric`, `ReissnerNordstromSpacetime.metricInv` : Reissner–Nordström
  spacetime structure, lapse function, and coordinate metric.
- `ReissnerNordstromSpacetime.maxwellF`, `maxwellStressEnergy` : radial electric field strength
  and Maxwell stress-energy.
- `ReissnerNordstromSpacetime.ricciTensorOf`, `ReissnerNordstromSpacetime.ricciScalarOf`,
  `ReissnerNordstromSpacetime.maxwellStressEnergy_trace_zero`,
  `ReissnerNordstromSpacetime.einsteinTensorOf_eq_maxwell` : verified Einstein–Maxwell solution
  through `GeneralRelativity.Pipeline`.
- `ReissnerNordstromSpacetime.horizonPlus`, `ReissnerNordstromSpacetime.horizonMinus`,
  `ReissnerNordstromSpacetime.lapse_horizonPlus`, `ReissnerNordstromSpacetime.lapse_horizonMinus`,
  `ReissnerNordstromSpacetime.lapse_extremal`,
  `ReissnerNordstromSpacetime.lapse_pos_of_overcharged` : Cauchy/event horizons, extremal
  coalescence, and overcharged regime.

## iii. Table of contents

- A. Metric, derivatives, and electrovacuum Maxwell field
- B. Electrovacuum Einstein equations through the pipeline
- C. Horizons, extremal limit, and overcharged regime

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 6 & Ch. 12 (Sec. 12.3).
  [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 33 (Box 33.2).
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 7
  (https://arxiv.org/pdf/gr-qc/9712019#page=184). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace ReissnerNordstrom

open GeneralRelativity.Pipeline GeneralRelativity.StaticSpherical

/-!

## A. Metric, derivatives, and electrovacuum Maxwell field

-/

/-- Reissner–Nordström charged black hole spacetime parameterized by mass `M` and electric
charge `Q`. -/
structure ReissnerNordstromSpacetime where
  /-- Geometric mass parameter `M` (`G = c = 1`). -/
  M : ℝ
  /-- Electric charge parameter `Q`. -/
  Q : ℝ

/-- Electromagnetic stress-energy tensor `T^{EM}_{ij} = (1 / (4π)) (F_{ik} F_j{}^k - (1/4) g_{ij}
F_{ab} F^{ab})` in Gaussian-cgs/geometrized units (`G = c = 1`). -/
noncomputable def maxwellStressEnergy (M : MetricTensor 4) (F : Tensor2 4) : Tensor2 4 :=
  fun i j => (1 / (4 * Real.pi)) * GeneralRelativity.maxwellStressEnergy M F i j

namespace ReissnerNordstromSpacetime

/-- The Reissner–Nordström radial lapse function `f(r) = 1 - 2 M / r + Q² / r²`. -/
noncomputable def lapse (S : ReissnerNordstromSpacetime) (r : ℝ) : ℝ :=
  1 - 2 * S.M / r + S.Q ^ 2 / r ^ 2

/-- View a Reissner–Nordström spacetime as a `StaticSphericalMetric` with profile `S.lapse`. -/
noncomputable def toStaticSpherical (S : ReissnerNordstromSpacetime) : StaticSphericalMetric :=
  ⟨S.lapse⟩

/-- The Reissner–Nordström metric in Schwarzschild-like coordinates `(t, r, θ, φ)`. -/
noncomputable def metric (S : ReissnerNordstromSpacetime) : (Fin 4 → ℝ) → Tensor2 4 :=
  S.toStaticSpherical.metric

/-- The inverse of the Reissner–Nordström metric in `(t, r, θ, φ)` coordinates. -/
noncomputable def metricInv (S : ReissnerNordstromSpacetime) : (Fin 4 → ℝ) → Tensor2 4 :=
  S.toStaticSpherical.metricInv

/-- `S.metric` is definitionally `S.toStaticSpherical.metric`. -/
lemma metric_eq_staticSpherical (S : ReissnerNordstromSpacetime) :
    S.metric = S.toStaticSpherical.metric := rfl

/-- `S.metricInv` is definitionally `S.toStaticSpherical.metricInv`. -/
lemma metricInv_eq_staticSpherical (S : ReissnerNordstromSpacetime) :
    S.metricInv = S.toStaticSpherical.metricInv := rfl

/-- At `Q = 0`, the Reissner–Nordström lapse reduces to the Schwarzschild lapse function. -/
lemma lapse_zero_charge (M r : ℝ) :
    (ReissnerNordstromSpacetime.mk M 0).lapse r =
      (Schwarzschild.SchwarzschildSpacetime.mk M).lapse r := by
  simp [lapse, Schwarzschild.SchwarzschildSpacetime.lapse]

/-- First radial derivative of `S.lapse`: `f'(r) = 2 M / r² - 2 Q² / r³`. -/
lemma hasDerivAt_lapse (S : ReissnerNordstromSpacetime) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt S.lapse (2 * S.M / r ^ 2 - 2 * S.Q ^ 2 / r ^ 3) r := by
  have h1 : HasDerivAt (fun s : ℝ => (1 : ℝ)) 0 r := hasDerivAt_const r 1
  have hinv : HasDerivAt (fun s : ℝ => s⁻¹) (-1 / r ^ 2) r := by
    convert hasDerivAt_inv hr using 1
    ring
  have h2M : HasDerivAt (fun s : ℝ => 2 * S.M * s⁻¹) (-2 * S.M / r ^ 2) r := by
    convert hinv.const_mul (2 * S.M) using 1
    ring
  have hsqInv : HasDerivAt (fun s : ℝ => (s ^ 2)⁻¹) (-2 / r ^ 3) r := by
    have hpow : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
      convert hasDerivAt_pow 2 r using 1
      ring
    have hdiv := hpow.inv (pow_ne_zero 2 hr)
    convert hdiv using 1
    field_simp [hr]
  have hQ : HasDerivAt (fun s : ℝ => S.Q ^ 2 * (s ^ 2)⁻¹) (-2 * S.Q ^ 2 / r ^ 3) r := by
    convert hsqInv.const_mul (S.Q ^ 2) using 1
    ring
  have hsum := (h1.sub h2M).add hQ
  convert hsum using 1
  · funext s
    simp only [Pi.add_apply, Pi.sub_apply, lapse, div_eq_mul_inv]
  · ring

/-- Neighbourhood differentiability of `S.lapse` away from `r = 0`. -/
lemma eventually_differentiableAt_lapse (S : ReissnerNordstromSpacetime) (r : ℝ) (hr : r ≠ 0) :
    ∀ᶠ s in nhds r, DifferentiableAt ℝ S.lapse s := by
  filter_upwards [eventually_ne_nhds hr] with s hs
  exact (S.hasDerivAt_lapse s hs).differentiableAt

/-- Second radial derivative of `S.lapse`: `f''(r) = -4 M / r³ + 6 Q² / r⁴`. -/
lemma hasDerivAt_deriv_lapse (S : ReissnerNordstromSpacetime) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (deriv S.lapse) (-4 * S.M / r ^ 3 + 6 * S.Q ^ 2 / r ^ 4) r := by
  have heq : deriv S.lapse =ᶠ[nhds r] fun s => 2 * S.M / s ^ 2 - 2 * S.Q ^ 2 / s ^ 3 := by
    filter_upwards [eventually_ne_nhds hr] with s hs
    exact (S.hasDerivAt_lapse s hs).deriv
  have hinv2 : HasDerivAt (fun s : ℝ => (s ^ 2)⁻¹) (-2 / r ^ 3) r := by
    have h := (hasDerivAt_pow 2 r).inv (pow_ne_zero 2 hr)
    convert h using 1
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    field_simp [hr]
  have hinv3 : HasDerivAt (fun s : ℝ => (s ^ 3)⁻¹) (-3 / r ^ 4) r := by
    have h := (hasDerivAt_pow 3 r).inv (pow_ne_zero 3 hr)
    convert h using 1
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one]
    field_simp [hr]
  have hd : HasDerivAt (fun s : ℝ => 2 * S.M / s ^ 2 - 2 * S.Q ^ 2 / s ^ 3)
      (-4 * S.M / r ^ 3 + 6 * S.Q ^ 2 / r ^ 4) r := by
    have hA : HasDerivAt (fun s : ℝ => 2 * S.M * (s ^ 2)⁻¹) (-4 * S.M / r ^ 3) r := by
      convert hinv2.const_mul (2 * S.M) using 1
      ring
    have hB : HasDerivAt (fun s : ℝ => 2 * S.Q ^ 2 * (s ^ 3)⁻¹) (-6 * S.Q ^ 2 / r ^ 4) r := by
      convert hinv3.const_mul (2 * S.Q ^ 2) using 1
      ring
    convert hA.sub hB using 1
    · funext s
      simp only [Pi.sub_apply, div_eq_mul_inv]
    · ring
  exact hd.congr_of_eventuallyEq heq

/-- Pointwise formula for the first derivative `deriv S.lapse r`. -/
lemma deriv_lapse (S : ReissnerNordstromSpacetime) (r : ℝ) (hr : r ≠ 0) :
    deriv S.lapse r = 2 * S.M / r ^ 2 - 2 * S.Q ^ 2 / r ^ 3 :=
  (S.hasDerivAt_lapse r hr).deriv

/-- Pointwise formula for the second derivative `deriv (deriv S.lapse) r`. -/
lemma deriv_deriv_lapse (S : ReissnerNordstromSpacetime) (r : ℝ) (hr : r ≠ 0) :
    deriv (deriv S.lapse) r = -4 * S.M / r ^ 3 + 6 * S.Q ^ 2 / r ^ 4 :=
  (S.hasDerivAt_deriv_lapse r hr).deriv

/-- Radial electric Maxwell field strength tensor `F_{ab}` (`F_{01} = -Q/r²`, `F_{10} = Q/r²`). -/
noncomputable def maxwellF (S : ReissnerNordstromSpacetime) (r : ℝ) : Tensor2 4 :=
  fun i j =>
    if i = 0 ∧ j = 1 then -S.Q / r ^ 2
    else if i = 1 ∧ j = 0 then S.Q / r ^ 2
    else 0

/-- Antisymmetry of the Maxwell field strength tensor `S.maxwellF`. -/
lemma maxwellF_antisymm (S : ReissnerNordstromSpacetime) (r : ℝ) (i j : Fin 4) :
    S.maxwellF r i j = -S.maxwellF r j i := by
  fin_cases i <;> fin_cases j <;> simp [maxwellF] <;> ring

/-!

## B. Electrovacuum Einstein equations through the pipeline

-/

/-- Metric-level Ricci tensor of a Reissner–Nordström spacetime computed via `Pipeline`. -/
lemma ricciTensorOf (S : ReissnerNordstromSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (σ ν : Fin 4) :
    Pipeline.ricciTensorOf S.metric S.metricInv x σ ν
      = if σ = ν then
          if σ = 0 then S.lapse (x 1) * S.Q ^ 2 / (x 1) ^ 4
          else if σ = 1 then -(S.Q ^ 2 / ((x 1) ^ 4 * S.lapse (x 1)))
          else if σ = 2 then S.Q ^ 2 / (x 1) ^ 2
          else S.Q ^ 2 * Real.sin (x 2) ^ 2 / (x 1) ^ 2
        else 0 := by
  have hfdiff := S.eventually_differentiableAt_lapse (x 1) hr
  have hf2diff := (S.hasDerivAt_deriv_lapse (x 1) hr).differentiableAt
  rw [S.metric_eq_staticSpherical, S.metricInv_eq_staticSpherical,
    S.toStaticSpherical.ricciTensorOf x hr hf hsin hfdiff hf2diff σ ν]
  dsimp [toStaticSpherical]
  rw [S.deriv_lapse (x 1) hr, S.deriv_deriv_lapse (x 1) hr]
  fin_cases σ <;> fin_cases ν <;> simp
  · field_simp [hr]; ring
  · field_simp [hr, hf]; ring
  · simp only [lapse]; field_simp [hr]; ring
  · simp only [lapse]; field_simp [hr]; ring

/-- The Reissner–Nordström spacetime has identically vanishing scalar curvature (`R = 0`),
reflecting conformal invariance of 4D Maxwell electromagnetism. -/
lemma ricciScalarOf (S : ReissnerNordstromSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    Pipeline.ricciScalarOf S.metric S.metricInv x = 0 := by
  have hfdiff := S.eventually_differentiableAt_lapse (x 1) hr
  have hf2diff := (S.hasDerivAt_deriv_lapse (x 1) hr).differentiableAt
  rw [S.metric_eq_staticSpherical, S.metricInv_eq_staticSpherical,
    S.toStaticSpherical.ricciScalarOf x hr hf hsin hfdiff hf2diff]
  dsimp [toStaticSpherical]
  rw [S.deriv_lapse (x 1) hr, S.deriv_deriv_lapse (x 1) hr, lapse]
  field_simp [hr]
  ring

/-- Four-dimensional Maxwell stress-energy is trace-free: `g^{ij} T^{EM}_{ij} = 0`. -/
lemma maxwellStressEnergy_trace_zero (S : ReissnerNordstromSpacetime) (x : Fin 4 → ℝ)
    (hr : x 1 ≠ 0) (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    metricTrace (S.toStaticSpherical.metricTensor x hr hf hsin)
      (maxwellStressEnergy (S.toStaticSpherical.metricTensor x hr hf hsin)
        (S.maxwellF (x 1))) = 0 := by
  rw [show maxwellStressEnergy (S.toStaticSpherical.metricTensor x hr hf hsin) (S.maxwellF (x 1)) =
      fun i j => (1 / (4 * Real.pi)) * GeneralRelativity.maxwellStressEnergy
        (S.toStaticSpherical.metricTensor x hr hf hsin) (S.maxwellF (x 1)) i j from rfl,
    metricTrace_smul, GeneralRelativity.maxwellStressEnergy_trace_zero, mul_zero]

/-- Electrovacuum Einstein–Maxwell equations verified directly through `GeneralRelativity.Pipeline`:
`G_{ij} = 8 π T^{EM}_{ij}` at every coordinate index `(i, j)`. -/
lemma einsteinTensorOf_eq_maxwell (S : ReissnerNordstromSpacetime) (x : Fin 4 → ℝ)
    (hr : x 1 ≠ 0) (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (i j : Fin 4) :
    Pipeline.einsteinTensorOf S.metric S.metricInv x i j
      = 8 * Real.pi
          * maxwellStressEnergy (S.toStaticSpherical.metricTensor x hr hf hsin)
              (S.maxwellF (x 1)) i j := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [Pipeline.einsteinTensorOf, S.ricciTensorOf x hr hf hsin, S.ricciScalarOf x hr hf hsin]
  simp only [maxwellStressEnergy, GeneralRelativity.maxwellStressEnergy, maxwellFieldInvariant,
    StaticSphericalMetric.metricTensor, StaticSphericalMetric.metric,
    StaticSphericalMetric.metricInv, toStaticSpherical, maxwellF, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp
  · field_simp [hr, hf, hpi]; ring
  · field_simp [hr, hf, hpi]; ring
  · field_simp [hr, hf, hpi]; ring
  · field_simp [hr, hf, hpi]; ring

/-!

## C. Horizons, extremal limit, and overcharged regime

-/

/-- Outer event horizon radius `r₊ = M + √(M² - Q²)` for `|Q| ≤ M`. -/
noncomputable def horizonPlus (S : ReissnerNordstromSpacetime) : ℝ :=
  S.M + Real.sqrt (S.M ^ 2 - S.Q ^ 2)

/-- Inner Cauchy horizon radius `r₋ = M - √(M² - Q²)` for `|Q| ≤ M`. -/
noncomputable def horizonMinus (S : ReissnerNordstromSpacetime) : ℝ :=
  S.M - Real.sqrt (S.M ^ 2 - S.Q ^ 2)

/-- Vanishing of `S.lapse` at any root of `r² - 2 M r + Q² = 0`. -/
lemma lapse_eq_zero_of_quad (S : ReissnerNordstromSpacetime) {r : ℝ} (hr : r ≠ 0)
    (hq : r ^ 2 - 2 * S.M * r + S.Q ^ 2 = 0) :
    S.lapse r = 0 := by
  simp only [lapse]
  field_simp [hr]
  linear_combination hq

/-- The outer horizon radius is a root of `S.lapse = 0` when `Q² ≤ M²` and `r₊ ≠ 0`. -/
lemma lapse_horizonPlus (S : ReissnerNordstromSpacetime) (hQ : S.Q ^ 2 ≤ S.M ^ 2)
    (hr : S.horizonPlus ≠ 0) :
    S.lapse S.horizonPlus = 0 := by
  refine S.lapse_eq_zero_of_quad hr ?_
  have hsq : Real.sqrt (S.M ^ 2 - S.Q ^ 2) ^ 2 = S.M ^ 2 - S.Q ^ 2 :=
    Real.sq_sqrt (sub_nonneg.mpr hQ)
  simp only [horizonPlus]
  linear_combination hsq

/-- The inner Cauchy horizon radius is a root of `S.lapse = 0` when `Q² ≤ M²` and `r₋ ≠ 0`. -/
lemma lapse_horizonMinus (S : ReissnerNordstromSpacetime) (hQ : S.Q ^ 2 ≤ S.M ^ 2)
    (hr : S.horizonMinus ≠ 0) :
    S.lapse S.horizonMinus = 0 := by
  refine S.lapse_eq_zero_of_quad hr ?_
  have hsq : Real.sqrt (S.M ^ 2 - S.Q ^ 2) ^ 2 = S.M ^ 2 - S.Q ^ 2 :=
    Real.sq_sqrt (sub_nonneg.mpr hQ)
  simp only [horizonMinus]
  linear_combination hsq

/-- Extremal double horizon (`Q² = M²`, `M ≠ 0`): the horizons coalesce at `r = M`, where both
`S.lapse` and its radial derivative vanish. -/
lemma lapse_extremal (S : ReissnerNordstromSpacetime) (hQ : S.Q ^ 2 = S.M ^ 2) (hM : S.M ≠ 0) :
    S.horizonPlus = S.M ∧ S.horizonMinus = S.M ∧ S.lapse S.M = 0
      ∧ HasDerivAt S.lapse 0 S.M := by
  have hsub : S.M ^ 2 - S.Q ^ 2 = 0 := sub_eq_zero.mpr hQ.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [horizonPlus, hsub]
  · simp [horizonMinus, hsub]
  · simp [lapse, hQ]
    field_simp [hM]
    ring
  · have h := S.hasDerivAt_lapse S.M hM
    have hder : 2 * S.M / S.M ^ 2 - 2 * S.Q ^ 2 / S.M ^ 3 = 0 := by
      rw [hQ]
      field_simp [hM]
      ring
    rwa [hder] at h

/-- Overcharged regime (`M² < Q²`): `S.lapse r > 0` for all `r ≠ 0` (no event horizon; naked
singularity). -/
lemma lapse_pos_of_overcharged (S : ReissnerNordstromSpacetime) (hQ : S.M ^ 2 < S.Q ^ 2)
    {r : ℝ} (hr : r ≠ 0) :
    0 < S.lapse r := by
  have hnum : 0 < (r - S.M) ^ 2 + (S.Q ^ 2 - S.M ^ 2) := by positivity
  have hid : S.lapse r = ((r - S.M) ^ 2 + (S.Q ^ 2 - S.M ^ 2)) / r ^ 2 := by
    simp only [lapse]
    field_simp [hr]
    ring
  rw [hid]
  exact div_pos hnum (sq_pos_iff.mpr hr)

end ReissnerNordstromSpacetime

end ReissnerNordstrom

end GeneralRelativity
