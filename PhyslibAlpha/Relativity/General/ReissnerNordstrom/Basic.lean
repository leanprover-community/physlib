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
`G_{ij} = 8 π T_{ij}`, vanishing scalar curvature, and inner/outer horizon structure.

## i. Overview

A static spherically symmetric charged black hole of mass `M` and electric charge `Q` has line
element `ds² = -f(r) dt² + f(r)⁻¹ dr² + r² dΩ²` with lapse function `f(r) = 1 - 2 M / r + Q² / r²`,
sourced by a radial Coulomb electric field `F_{01} = -Q / r²`, `F_{10} = Q / r²`.

Feeding `rnMetric M Q` through `GeneralRelativity.StaticSpherical` and
`GeneralRelativity.Pipeline`, this module proves:

- `ricciScalarOf_rn` : vanishing Ricci scalar `S = 0`, matching `maxwellStressEnergy_rn_trace_zero`
  (`g^{ij} T^{EM}_{ij} = 0` in 4D);
- `einsteinTensorOf_rn_eq_maxwell` : the full 4D electrovacuum Einstein–Maxwell field equations
  `G_{ij} = 8 π T^{EM}_{ij}` at every index pair `(i, j)`;
- horizon theorems (`rnLapse_horizonPlus`, `rnLapse_horizonMinus`, extremal double root
  when `Q² = M²`, and positivity `0 < rnLapse` in the overcharged naked-singularity regime
  `M² < Q²`).

## ii. Key results

- `ReissnerNordstromSpacetime`, `rnLapse`, `rnMetric`, `rnMetricInv` : Reissner–Nordström
  spacetime structure, lapse function, and coordinate metric.
- `maxwellF`, `maxwellStressEnergy` : radial electric field strength and Maxwell stress-energy.
- `ricciTensorOf_rn`, `ricciScalarOf_rn`, `maxwellStressEnergy_rn_trace_zero`,
  `einsteinTensorOf_rn_eq_maxwell` :
  verified Einstein–Maxwell solution through `GeneralRelativity.Pipeline`.
- `horizonPlus`, `horizonMinus`, `rnLapse_horizonPlus`, `rnLapse_horizonMinus`,
  `rnLapse_extremal`, `rnLapse_pos_of_overcharged` : Cauchy/event horizons, extremal coalescence,
  and overcharged regime.

## iii. Table of contents

- A. Metric, derivatives, and electrovacuum Maxwell field
- B. Electrovacuum Einstein equations through the pipeline
- C. Horizons, extremal limit, and overcharged regime

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

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

/-- The Reissner–Nordström radial lapse function `f(r) = 1 - 2 M / r + Q² / r²`. -/
noncomputable def rnLapse (M Q r : ℝ) : ℝ := 1 - 2 * M / r + Q ^ 2 / r ^ 2

/-- The Reissner–Nordström metric in Schwarzschild-like coordinates `(t, r, θ, φ)`. -/
noncomputable def rnMetric (M Q : ℝ) : (Fin 4 → ℝ) → Tensor2 4 :=
  staticSphericalMetric (rnLapse M Q)

/-- The inverse of the Reissner–Nordström metric in `(t, r, θ, φ)` coordinates. -/
noncomputable def rnMetricInv (M Q : ℝ) : (Fin 4 → ℝ) → Tensor2 4 :=
  staticSphericalMetricInv (rnLapse M Q)

/-- `rnMetric M Q` is definitionally `staticSphericalMetric (rnLapse M Q)`. -/
lemma rnMetric_eq_staticSpherical (M Q : ℝ) :
    rnMetric M Q = staticSphericalMetric (rnLapse M Q) := rfl

/-- `rnMetricInv M Q` is definitionally `staticSphericalMetricInv (rnLapse M Q)`. -/
lemma rnMetricInv_eq_staticSpherical (M Q : ℝ) :
    rnMetricInv M Q = staticSphericalMetricInv (rnLapse M Q) := rfl

/-- At `Q = 0`, `rnLapse` reduces to the Schwarzschild lapse function. -/
lemma rnLapse_zero_charge (M r : ℝ) : rnLapse M 0 r = Schwarzschild.schwarzschildLapse M r := by
  simp [rnLapse, Schwarzschild.schwarzschildLapse]

/-- First radial derivative of `rnLapse`: `f'(r) = 2 M / r² - 2 Q² / r³`. -/
lemma hasDerivAt_rnLapse (M Q r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (rnLapse M Q) (2 * M / r ^ 2 - 2 * Q ^ 2 / r ^ 3) r := by
  have h1 : HasDerivAt (fun s : ℝ => (1 : ℝ)) 0 r := hasDerivAt_const r 1
  have hinv : HasDerivAt (fun s : ℝ => s⁻¹) (-1 / r ^ 2) r := by
    convert hasDerivAt_inv hr using 1
    ring
  have h2M : HasDerivAt (fun s : ℝ => 2 * M * s⁻¹) (-2 * M / r ^ 2) r := by
    convert hinv.const_mul (2 * M) using 1
    ring
  have hsqInv : HasDerivAt (fun s : ℝ => (s ^ 2)⁻¹) (-2 / r ^ 3) r := by
    have hpow : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
      convert hasDerivAt_pow 2 r using 1
      ring
    have hdiv := hpow.inv (pow_ne_zero 2 hr)
    convert hdiv using 1
    field_simp [hr]
  have hQ : HasDerivAt (fun s : ℝ => Q ^ 2 * (s ^ 2)⁻¹) (-2 * Q ^ 2 / r ^ 3) r := by
    convert hsqInv.const_mul (Q ^ 2) using 1
    ring
  have hsum := (h1.sub h2M).add hQ
  convert hsum using 1
  · funext s
    simp only [Pi.add_apply, Pi.sub_apply, rnLapse, div_eq_mul_inv]
  · ring

/-- Neighbourhood differentiability of `rnLapse M Q` away from `r = 0`. -/
lemma eventually_differentiableAt_rnLapse (M Q r : ℝ) (hr : r ≠ 0) :
    ∀ᶠ s in nhds r, DifferentiableAt ℝ (rnLapse M Q) s := by
  filter_upwards [eventually_ne_nhds hr] with s hs
  exact (hasDerivAt_rnLapse M Q s hs).differentiableAt

/-- Second radial derivative of `rnLapse`: `f''(r) = -4 M / r³ + 6 Q² / r⁴`. -/
lemma hasDerivAt_deriv_rnLapse (M Q r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (deriv (rnLapse M Q)) (-4 * M / r ^ 3 + 6 * Q ^ 2 / r ^ 4) r := by
  have heq : deriv (rnLapse M Q) =ᶠ[nhds r] fun s => 2 * M / s ^ 2 - 2 * Q ^ 2 / s ^ 3 := by
    filter_upwards [eventually_ne_nhds hr] with s hs
    exact (hasDerivAt_rnLapse M Q s hs).deriv
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
  have hd : HasDerivAt (fun s : ℝ => 2 * M / s ^ 2 - 2 * Q ^ 2 / s ^ 3)
      (-4 * M / r ^ 3 + 6 * Q ^ 2 / r ^ 4) r := by
    have hA : HasDerivAt (fun s : ℝ => 2 * M * (s ^ 2)⁻¹) (-4 * M / r ^ 3) r := by
      convert hinv2.const_mul (2 * M) using 1
      ring
    have hB : HasDerivAt (fun s : ℝ => 2 * Q ^ 2 * (s ^ 3)⁻¹) (-6 * Q ^ 2 / r ^ 4) r := by
      convert hinv3.const_mul (2 * Q ^ 2) using 1
      ring
    convert hA.sub hB using 1
    · funext s
      simp only [Pi.sub_apply, div_eq_mul_inv]
    · ring
  exact hd.congr_of_eventuallyEq heq

/-- Pointwise formula for the first derivative `deriv (rnLapse M Q) r`. -/
lemma deriv_rnLapse (M Q r : ℝ) (hr : r ≠ 0) :
    deriv (rnLapse M Q) r = 2 * M / r ^ 2 - 2 * Q ^ 2 / r ^ 3 :=
  (hasDerivAt_rnLapse M Q r hr).deriv

/-- Pointwise formula for the second derivative `deriv (deriv (rnLapse M Q)) r`. -/
lemma deriv_deriv_rnLapse (M Q r : ℝ) (hr : r ≠ 0) :
    deriv (deriv (rnLapse M Q)) r = -4 * M / r ^ 3 + 6 * Q ^ 2 / r ^ 4 :=
  (hasDerivAt_deriv_rnLapse M Q r hr).deriv

/-- Radial electric Maxwell field strength tensor `F_{ab}` (`F_{01} = -Q/r²`, `F_{10} = Q/r²`). -/
noncomputable def maxwellF (Q r : ℝ) : Tensor2 4 :=
  fun i j =>
    if i = 0 ∧ j = 1 then -Q / r ^ 2
    else if i = 1 ∧ j = 0 then Q / r ^ 2
    else 0

/-- Antisymmetry of the Maxwell field strength tensor `maxwellF`. -/
lemma maxwellF_antisymm (Q r : ℝ) (i j : Fin 4) : maxwellF Q r i j = -maxwellF Q r j i := by
  fin_cases i <;> fin_cases j <;> simp [maxwellF] <;> ring

/-- Electromagnetic stress-energy tensor `T^{EM}_{ij} = (1 / (4π)) (F_{ik} F_j{}^k - (1/4) g_{ij}
F_{ab} F^{ab})` in Gaussian-cgs/geometrized units (`G = c = 1`). -/
noncomputable def maxwellStressEnergy (g ginv F : Tensor2 4) : Tensor2 4 :=
  fun i j => (1 / (4 * Real.pi)) * maxwellStressEnergyRaw g ginv F i j

/-- The lapse function `rnLapse` of a Reissner–Nordström spacetime. -/
noncomputable def ReissnerNordstromSpacetime.lapse (S : ReissnerNordstromSpacetime)
    (r : ℝ) : ℝ :=
  rnLapse S.M S.Q r

/-- The coordinate metric of a Reissner–Nordström spacetime. -/
noncomputable def ReissnerNordstromSpacetime.metric (S : ReissnerNordstromSpacetime)
    (x : Fin 4 → ℝ) : Tensor2 4 :=
  rnMetric S.M S.Q x

/-- The inverse coordinate metric of a Reissner–Nordström spacetime. -/
noncomputable def ReissnerNordstromSpacetime.metricInv (S : ReissnerNordstromSpacetime)
    (x : Fin 4 → ℝ) : Tensor2 4 :=
  rnMetricInv S.M S.Q x

/-!

## B. Electrovacuum Einstein equations through the pipeline

-/

/-- Metric-level Ricci tensor of the Reissner–Nordström spacetime computed via `Pipeline`. -/
lemma ricciTensorOf_rn (M Q : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) (hf : rnLapse M Q (x 1) ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0) (σ ν : Fin 4) :
    ricciTensorOf (rnMetric M Q) (rnMetricInv M Q) x σ ν
      = if σ = ν then
          if σ = 0 then rnLapse M Q (x 1) * Q ^ 2 / (x 1) ^ 4
          else if σ = 1 then -(Q ^ 2 / ((x 1) ^ 4 * rnLapse M Q (x 1)))
          else if σ = 2 then Q ^ 2 / (x 1) ^ 2
          else Q ^ 2 * Real.sin (x 2) ^ 2 / (x 1) ^ 2
        else 0 := by
  have hfdiff := eventually_differentiableAt_rnLapse M Q (x 1) hr
  have hf2diff := (hasDerivAt_deriv_rnLapse M Q (x 1) hr).differentiableAt
  rw [rnMetric_eq_staticSpherical, rnMetricInv_eq_staticSpherical,
    ricciTensorOf_staticSpherical (rnLapse M Q) x hr hf hsin hfdiff hf2diff σ ν,
    deriv_rnLapse M Q (x 1) hr, deriv_deriv_rnLapse M Q (x 1) hr]
  fin_cases σ <;> fin_cases ν <;> simp
  · field_simp [hr]; ring
  · field_simp [hr, hf]; ring
  · simp only [rnLapse]; field_simp [hr]; ring
  · simp only [rnLapse]; field_simp [hr]; ring

/-- The Reissner–Nordström spacetime has identically vanishing scalar curvature (`S = 0`),
reflecting conformal invariance of 4D Maxwell electromagnetism. -/
lemma ricciScalarOf_rn (M Q : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) (hf : rnLapse M Q (x 1) ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0) :
    ricciScalarOf (rnMetric M Q) (rnMetricInv M Q) x = 0 := by
  have hfdiff := eventually_differentiableAt_rnLapse M Q (x 1) hr
  have hf2diff := (hasDerivAt_deriv_rnLapse M Q (x 1) hr).differentiableAt
  rw [rnMetric_eq_staticSpherical, rnMetricInv_eq_staticSpherical,
    ricciScalarOf_staticSpherical (rnLapse M Q) x hr hf hsin hfdiff hf2diff,
    deriv_rnLapse M Q (x 1) hr, deriv_deriv_rnLapse M Q (x 1) hr, rnLapse]
  field_simp [hr]
  ring

/-- Four-dimensional Maxwell stress-energy is trace-free: `g^{ij} T^{EM}_{ij} = 0`. -/
lemma maxwellStressEnergy_rn_trace_zero (M Q : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : rnLapse M Q (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    metricTrace (staticSphericalMetricTensor (rnLapse M Q) x hr hf hsin)
      (maxwellStressEnergy (rnMetric M Q x) (rnMetricInv M Q x) (maxwellF Q (x 1))) = 0 := by
  have h := maxwellStressEnergyRaw_trace_zero
    (staticSphericalMetricTensor (rnLapse M Q) x hr hf hsin) (maxwellF Q (x 1))
  show metricTrace _ (fun i j => (1 / (4 * Real.pi)) *
    maxwellStressEnergyRaw (rnMetric M Q x) (rnMetricInv M Q x) (maxwellF Q (x 1)) i j) = 0
  rw [metricTrace_smul]
  exact mul_eq_zero_of_right _ h

/-- Electrovacuum Einstein–Maxwell equations verified directly through `GeneralRelativity.Pipeline`:
`G_{ij} = 8 π T^{EM}_{ij}` at every coordinate index `(i, j)`. -/
lemma einsteinTensorOf_rn_eq_maxwell (M Q : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : rnLapse M Q (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (i j : Fin 4) :
    einsteinTensorOf (rnMetric M Q) (rnMetricInv M Q) x i j
      = 8 * Real.pi
          * maxwellStressEnergy (rnMetric M Q x) (rnMetricInv M Q x) (maxwellF Q (x 1)) i j := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [einsteinTensorOf, ricciTensorOf_rn M Q x hr hf hsin, ricciScalarOf_rn M Q x hr hf hsin]
  simp only [maxwellStressEnergy, maxwellStressEnergyRaw, maxwellFieldInvariant, rnMetric,
    rnMetricInv, staticSphericalMetric, staticSphericalMetricInv, maxwellF, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp
  · field_simp [hr, hf, hpi]; ring
  · field_simp [hr, hf, hpi]; ring
  · field_simp [hr, hf, hpi]; ring
  · field_simp [hr, hf, hpi]; ring

/-!

## C. Horizons, extremal limit, and overcharged regime

-/

/-- Outer event horizon radius `r₊ = M + √(M² - Q²)` for `|Q| ≤ M`. -/
noncomputable def horizonPlus (M Q : ℝ) : ℝ := M + Real.sqrt (M ^ 2 - Q ^ 2)

/-- Inner Cauchy horizon radius `r₋ = M - √(M² - Q²)` for `|Q| ≤ M`. -/
noncomputable def horizonMinus (M Q : ℝ) : ℝ := M - Real.sqrt (M ^ 2 - Q ^ 2)

/-- Vanishing of the Reissner–Nordström lapse function at any root of `r² - 2 M r + Q² = 0`. -/
lemma rnLapse_eq_zero_of_quad {M Q r : ℝ} (hr : r ≠ 0) (hq : r ^ 2 - 2 * M * r + Q ^ 2 = 0) :
    rnLapse M Q r = 0 := by
  simp only [rnLapse]
  field_simp [hr]
  linear_combination hq

/-- The outer horizon radius is a root of `rnLapse M Q = 0` when `Q² ≤ M²` and `r₊ ≠ 0`. -/
lemma rnLapse_horizonPlus {M Q : ℝ} (hQ : Q ^ 2 ≤ M ^ 2) (hr : horizonPlus M Q ≠ 0) :
    rnLapse M Q (horizonPlus M Q) = 0 := by
  refine rnLapse_eq_zero_of_quad hr ?_
  have hsq : Real.sqrt (M ^ 2 - Q ^ 2) ^ 2 = M ^ 2 - Q ^ 2 :=
    Real.sq_sqrt (sub_nonneg.mpr hQ)
  simp only [horizonPlus]
  linear_combination hsq

/-- The inner Cauchy horizon radius is a root of `rnLapse M Q = 0` when `Q² ≤ M²` and `r₋ ≠ 0`. -/
lemma rnLapse_horizonMinus {M Q : ℝ} (hQ : Q ^ 2 ≤ M ^ 2) (hr : horizonMinus M Q ≠ 0) :
    rnLapse M Q (horizonMinus M Q) = 0 := by
  refine rnLapse_eq_zero_of_quad hr ?_
  have hsq : Real.sqrt (M ^ 2 - Q ^ 2) ^ 2 = M ^ 2 - Q ^ 2 :=
    Real.sq_sqrt (sub_nonneg.mpr hQ)
  simp only [horizonMinus]
  linear_combination hsq

/-- Extremal double horizon (`Q² = M²`, `M ≠ 0`): the horizons coalesce at `r = M`, where both
`rnLapse` and its radial derivative vanish. -/
lemma rnLapse_extremal {M Q : ℝ} (hQ : Q ^ 2 = M ^ 2) (hM : M ≠ 0) :
    horizonPlus M Q = M ∧ horizonMinus M Q = M ∧ rnLapse M Q M = 0
      ∧ HasDerivAt (rnLapse M Q) 0 M := by
  have hsub : M ^ 2 - Q ^ 2 = 0 := sub_eq_zero.mpr hQ.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [horizonPlus, hsub]
  · simp [horizonMinus, hsub]
  · simp [rnLapse, hQ]
    field_simp [hM]
    ring
  · have h := hasDerivAt_rnLapse M Q M hM
    have hder : 2 * M / M ^ 2 - 2 * Q ^ 2 / M ^ 3 = 0 := by
      rw [hQ]
      field_simp [hM]
      ring
    rwa [hder] at h

/-- Overcharged regime (`M² < Q²`): `rnLapse M Q r > 0` for all `r ≠ 0` (no event horizon; naked
singularity). -/
lemma rnLapse_pos_of_overcharged {M Q r : ℝ} (hQ : M ^ 2 < Q ^ 2) (hr : r ≠ 0) :
    0 < rnLapse M Q r := by
  have hnum : 0 < (r - M) ^ 2 + (Q ^ 2 - M ^ 2) := by positivity
  have hid : rnLapse M Q r = ((r - M) ^ 2 + (Q ^ 2 - M ^ 2)) / r ^ 2 := by
    simp only [rnLapse]
    field_simp [hr]
    ring
  rw [hid]
  exact div_pos hnum (sq_pos_iff.mpr hr)

end ReissnerNordstrom

end GeneralRelativity
