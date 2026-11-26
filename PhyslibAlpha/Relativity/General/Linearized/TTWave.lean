/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Linearized.LorenzGauge
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic.Ring

/-!

# Transverse-traceless gravitational waves

Plane gravitational waves in the transverse-traceless (`TT`) gauge with `+` and `×` polarizations
and verification that they satisfy the linearized vacuum Einstein equations.

## i. Overview

A plane gravitational wave propagating along the `+z` direction with profile `f(t - z)` and
polarization amplitudes `hPlus`, `hCross` is packaged as the `MetricPerturbation`
`ttWave hPlus hCross f`. This module proves that `ttWave` is trace free, fixed by trace reversal,
automatically in Lorenz gauge for any profile `f`, and solves `linearizedEinstein = 0` for every
`C²` wave profile.

## ii. Key results

- `ttWave`, `ttWave_trace_zero`, `traceReversed_ttWave` : transverse-traceless plane gravitational
  wave and its algebraic properties.
- `ttWave_lorenz_gauge` : automatic Lorenz gauge for `ttWave`.
- `ttWave_linearizedEinstein_zero` : `TT` waves with `C²` profile solve `G^{(1)}_{ij} = 0`.

## iii. Table of contents

- A. Transverse-traceless gravitational waves

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 4 (Sec. 4.4). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 35.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 6
  (https://arxiv.org/pdf/gr-qc/9712019#page=155). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace Linearized

open Pipeline

/-!

## A. Transverse-traceless gravitational waves

A plane wave polarized orthogonally to its propagation direction (`+z`) automatically satisfies
both tracelessness and the Lorenz gauge condition, solving the linearized vacuum Einstein
equations.

-/

/-- Transverse-traceless (`TT`) plane gravitational wave propagating along the `+z` direction
with wave profile `f(t - z)` and `+`, `×` polarization amplitudes `hPlus`, `hCross`. -/
noncomputable def ttWave (hPlus hCross : ℝ) (f : ℝ → ℝ) : MetricPerturbation where
  h x i j :=
    let w := f (x 0 - x 3)
    if i = 1 ∧ j = 1 then hPlus * w
    else if i = 2 ∧ j = 2 then -(hPlus * w)
    else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then hCross * w
    else 0
  symm _ := Matrix.IsSymm.ext fun i j => by fin_cases i <;> fin_cases j <;> simp

/-- A `TT` gravitational wave is trace-free: `η^{ij} h^{TT}_{ij} = 0`. -/
lemma ttWave_trace_zero (hPlus hCross : ℝ) (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    perturbationTrace ((ttWave hPlus hCross f).h x) = 0 := by
  simp [perturbationTrace, metricTrace, minkowski, ttWave, Fin.sum_univ_four]

/-- Trace reversal acts trivially on `ttWave`. -/
lemma traceReversed_ttWave (hPlus hCross : ℝ) (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (ttWave hPlus hCross f).traceReversed.h x = (ttWave hPlus hCross f).h x := by
  ext i j
  simp [MetricPerturbation.traceReversed, traceReversed, Matrix.of_apply, ttWave_trace_zero]

private lemma pd_1_wave (c : ℝ) (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    coordDeriv 1 (fun y => c * f (y 0 - y 3)) x = 0 :=
  coordDeriv_const_slice 1 (c * f (x 0 - x 3)) (fun _ => by simp)

private lemma pd_2_wave (c : ℝ) (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    coordDeriv 2 (fun y => c * f (y 0 - y 3)) x = 0 :=
  coordDeriv_const_slice 2 (c * f (x 0 - x 3)) (fun _ => by simp)

/-- A `TT` wave automatically satisfies the Lorenz gauge condition `∂^k h^{TT}_{kj} = 0`
for any wave profile `f`. -/
lemma ttWave_lorenz_gauge (hPlus hCross : ℝ) (f : ℝ → ℝ) (x : Fin 4 → ℝ) (j : Fin 4) :
    IsLorenzGauge (ttWave hPlus hCross f) x j := by
  have htr : ∀ y, (ttWave hPlus hCross f).traceReversed.h y = (ttWave hPlus hCross f).h y :=
    traceReversed_ttWave hPlus hCross f
  have hc0 : ∀ μ, coordDeriv μ (fun _ : Fin 4 → ℝ => (0 : ℝ)) x = 0 :=
    fun μ => coordDeriv_const μ 0 x
  have h1neg : coordDeriv 2 (fun y => -(hPlus * f (y 0 - y 3))) x = 0 := by
    have hfun : (fun y : Fin 4 → ℝ => -(hPlus * f (y 0 - y 3)))
        = fun y => (-hPlus) * f (y 0 - y 3) := funext fun y => by ring
    rw [hfun, pd_2_wave]
  simp only [IsLorenzGauge, lorenzDivergence, htr, Fin.sum_univ_four, minkowskiMetric4_apply]
  fin_cases j <;>
    simp only [ttWave] <;> norm_num
  · simp [hc0]
  · simp [hc0, pd_1_wave, pd_2_wave]
  · simp [hc0, pd_1_wave, h1neg]
  · simp [hc0]

private lemma pd_0_wave (c : ℝ) (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : Fin 4 → ℝ) :
    coordDeriv 0 (fun y => c * f (y 0 - y 3)) x = c * deriv f (x 0 - x 3) := by
  have hfun : (fun s => c * f (Function.update x 0 s 0 - Function.update x 0 s 3))
      = fun s => c * f (s - x 3) := by funext s; simp
  have hsub : HasDerivAt (fun s => s - x 3) 1 (x 0) := by
    simpa using (hasDerivAt_id (x 0)).sub_const (x 3)
  have hd : HasDerivAt (fun s => c * f (s - x 3)) (c * deriv f (x 0 - x 3)) (x 0) := by
    simpa using ((hf (x 0 - x 3)).hasDerivAt.comp (x 0) hsub).const_mul c
  exact coordDeriv_of_hasDerivAt 0 (hfun ▸ hd)

private lemma pd_3_wave (c : ℝ) (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : Fin 4 → ℝ) :
    coordDeriv 3 (fun y => c * f (y 0 - y 3)) x = -(c * deriv f (x 0 - x 3)) := by
  have hfun : (fun s => c * f (Function.update x 3 s 0 - Function.update x 3 s 3))
      = fun s => c * f (x 0 - s) := by funext s; simp
  have hsub : HasDerivAt (fun s => x 0 - s) (-1) (x 3) :=
    ((hasDerivAt_const (x 3) (x 0)).sub (hasDerivAt_id (x 3))).congr_deriv (by ring)
  have hd0 : HasDerivAt (fun s => f (x 0 - s)) (deriv f (x 0 - x 3) * (-1)) (x 3) :=
    (hf (x 0 - x 3)).hasDerivAt.comp (x 3) hsub
  have hd : HasDerivAt (fun s => c * f (x 0 - s)) (-(c * deriv f (x 0 - x 3))) (x 3) :=
    (hd0.const_mul c).congr_deriv (by ring)
  exact coordDeriv_of_hasDerivAt 3 (hfun ▸ hd)

private lemma minkowskiDalembertian_wave (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x : Fin 4 → ℝ) :
    minkowskiDalembertian (fun y => f (y 0 - y 3)) x = 0 := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hf2 : Differentiable ℝ (deriv f) :=
    ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2.differentiable (by norm_num)
  have h0eq : coordDeriv (0 : Fin 4) (fun y : Fin 4 → ℝ => f (y 0 - y 3))
      = fun y => deriv f (y 0 - y 3) := by
    funext y
    simpa using pd_0_wave 1 f hf1 y
  have h3eq : coordDeriv (3 : Fin 4) (fun y : Fin 4 → ℝ => f (y 0 - y 3))
      = fun y => (-1 : ℝ) * deriv f (y 0 - y 3) := by
    funext y
    simpa using pd_3_wave 1 f hf1 y
  have hc1 : coordDeriv (1 : Fin 4) (fun y : Fin 4 → ℝ => f (y 0 - y 3)) = fun _ => 0 := by
    funext y; simpa using pd_1_wave 1 f y
  have hc2 : coordDeriv (2 : Fin 4) (fun y : Fin 4 → ℝ => f (y 0 - y 3)) = fun _ => 0 := by
    funext y; simpa using pd_2_wave 1 f y
  simp only [minkowskiDalembertian, Fin.sum_univ_four, minkowskiMetric4_apply, h0eq, hc1, hc2, h3eq]
  have hp0 := pd_0_wave 1 (deriv f) hf2 x
  have hp3 := pd_3_wave (-1) (deriv f) hf2 x
  simp only [one_mul] at hp0
  rw [hp0, hp3, coordDeriv_const, coordDeriv_const]
  norm_num

private lemma contDiffAt_wave (c : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x : Fin 4 → ℝ) :
    ContDiffAt ℝ 2 (fun y => c * f (y 0 - y 3)) x := by
  have hlin : ContDiff ℝ 2 (fun y : Fin 4 → ℝ => y 0 - y 3) :=
    (contDiff_pi.mp (contDiff_id (𝕜 := ℝ) (E := Fin 4 → ℝ)) 0).sub
      (contDiff_pi.mp (contDiff_id (𝕜 := ℝ) (E := Fin 4 → ℝ)) 3)
  exact contDiffAt_const.mul (hf.comp hlin).contDiffAt

/-- Every transverse-traceless gravitational wave with `C²` profile `f` satisfies the linearized
vacuum Einstein equations `G^{(1)}_{ij} = 0`. -/
lemma ttWave_linearizedEinstein_zero (hPlus hCross : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (x : Fin 4 → ℝ) (i j : Fin 4) :
    linearizedEinstein (ttWave hPlus hCross f) x i j = 0 := by
  have hc : (ttWave hPlus hCross f).IsC2At x := fun a b => by
    fin_cases a <;> fin_cases b <;> simp only [ttWave] <;> norm_num
    all_goals first
      | exact contDiffAt_const
      | exact contDiffAt_wave hPlus f hf x
      | exact (contDiffAt_wave hPlus f hf x).neg
      | exact contDiffAt_wave hCross f hf x
  have hlz : ∀ᶠ y in nhds x, ∀ k, IsLorenzGauge (ttWave hPlus hCross f) y k :=
    Filter.Eventually.of_forall fun y k => ttWave_lorenz_gauge hPlus hCross f y k
  rw [linearizedEinstein_lorenz_gauge (ttWave hPlus hCross f) x hc hlz i j]
  have htr : (fun y => (ttWave hPlus hCross f).traceReversed.h y i j)
      = fun y => (ttWave hPlus hCross f).h y i j := by
    funext y; simp [traceReversed_ttWave]
  rw [htr]
  fin_cases i <;> fin_cases j <;> simp only [ttWave] <;> norm_num
  all_goals first
    | exact minkowskiDalembertian_zero x
    | (rw [minkowskiDalembertian_const_mul, minkowskiDalembertian_wave f hf x, mul_zero])
    | (rw [minkowskiDalembertian_neg, minkowskiDalembertian_const_mul,
        minkowskiDalembertian_wave f hf x, mul_zero, neg_zero])

end Linearized

end GeneralRelativity
