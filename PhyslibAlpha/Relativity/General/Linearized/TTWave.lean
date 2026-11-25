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
polarization amplitudes `hPlus`, `hCross` is defined by `ttWave`. This module proves that `ttWave`
is symmetric, trace free, invariant under trace reversal, automatically in Lorenz gauge for any
profile `f`, and solves `linEinstein = 0` for every `C²` wave profile.

## ii. Key results

- `ttWave`, `ttWave_symm`, `ttWave_trace_zero`, `traceReversed_ttWave` : transverse-traceless
  plane gravitational wave and its algebraic properties.
- `ttWave_lorenz_gauge` : automatic Lorenz gauge for `ttWave`.
- `ttWave_linEinstein_zero` : `TT` waves with `C²` profile solve `G^{(1)}_{ij} = 0`.

## iii. Table of contents

- A. Transverse-traceless gravitational waves

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

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
noncomputable def ttWave (hPlus hCross : ℝ) (f : ℝ → ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  let w := f (x 0 - x 3)
  fun i j =>
    if i = 1 ∧ j = 1 then hPlus * w
    else if i = 2 ∧ j = 2 then -(hPlus * w)
    else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then hCross * w
    else 0

/-- Symmetry of `ttWave`. -/
lemma ttWave_symm (hPlus hCross : ℝ) (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    IsSymm (ttWave hPlus hCross f x) :=
  Matrix.IsSymm.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [ttWave]

/-- A `TT` gravitational wave is trace-free: `η^{ij} h^{TT}_{ij} = 0`. -/
lemma ttWave_trace_zero (hPlus hCross : ℝ) (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    hTrace (ttWave hPlus hCross f x) = 0 := by
  simp [hTrace, metricTrace, minkowski, ttWave, Fin.sum_univ_four]

/-- Trace reversal acts trivially on `ttWave`. -/
lemma traceReversed_ttWave (hPlus hCross : ℝ) (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    traceReversed (ttWave hPlus hCross f x) = ttWave hPlus hCross f x := by
  ext i j
  simp [traceReversed, ttWave_trace_zero]

private lemma pd_1_wave (c : ℝ) (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    coordDeriv 1 (fun y => c * f (y 0 - y 3)) x = 0 := by
  have hfn : (fun s => c * f (Function.update x 1 s 0 - Function.update x 1 s 3))
      = fun _ => c * f (x 0 - x 3) := by funext s; simp
  rw [coordDeriv, hfn, deriv_const']

private lemma pd_2_wave (c : ℝ) (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    coordDeriv 2 (fun y => c * f (y 0 - y 3)) x = 0 := by
  have hfn : (fun s => c * f (Function.update x 2 s 0 - Function.update x 2 s 3))
      = fun _ => c * f (x 0 - x 3) := by funext s; simp
  rw [coordDeriv, hfn, deriv_const']

/-- A `TT` wave automatically satisfies the Lorenz gauge condition `∂^k h^{TT}_{kj} = 0`
for any wave profile `f`. -/
lemma ttWave_lorenz_gauge (hPlus hCross : ℝ) (f : ℝ → ℝ) (x : Fin 4 → ℝ) (j : Fin 4) :
    lorenzGaugeCond (ttWave hPlus hCross f) x j := by
  have htr : ∀ y, traceReversed (ttWave hPlus hCross f y) = ttWave hPlus hCross f y :=
    traceReversed_ttWave hPlus hCross f
  have hc0 : ∀ μ, coordDeriv μ (fun _ : Fin 4 → ℝ => (0 : ℝ)) x = 0 :=
    fun μ => coordDeriv_const μ 0 x
  have h1neg : coordDeriv 2 (fun y => -(hPlus * f (y 0 - y 3))) x = 0 := by
    have hfun : (fun y : Fin 4 → ℝ => -(hPlus * f (y 0 - y 3)))
        = fun y => (-hPlus) * f (y 0 - y 3) := funext fun y => by ring
    rw [hfun, pd_2_wave]
  simp only [lorenzGaugeCond, lorenzDiv, htr, Fin.sum_univ_four, minkowskiMetric4_apply]
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
  rw [coordDeriv, hfun, hd.deriv]

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
  rw [coordDeriv, hfun, hd.deriv]

private lemma boxEta_zero (x : Fin 4 → ℝ) : boxEta (fun _ : Fin 4 → ℝ => (0 : ℝ)) x = 0 := by
  have hpd : ∀ μ : Fin 4, coordDeriv μ (fun _ : Fin 4 → ℝ => (0 : ℝ)) = fun _ => 0 :=
    fun μ => funext fun y => coordDeriv_const μ 0 y
  simp only [boxEta, hpd, coordDeriv_const, mul_zero, Finset.sum_const_zero]

private lemma boxEta_wave (c : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x : Fin 4 → ℝ) :
    boxEta (fun y => c * f (y 0 - y 3)) x = 0 := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hf2 : Differentiable ℝ (deriv f) :=
    ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2.differentiable (by norm_num)
  have h0eq : coordDeriv (0 : Fin 4) (fun y : Fin 4 → ℝ => c * f (y 0 - y 3))
      = fun y => c * deriv f (y 0 - y 3) :=
    funext fun y => pd_0_wave c f hf1 y
  have h3eq : coordDeriv (3 : Fin 4) (fun y : Fin 4 → ℝ => c * f (y 0 - y 3))
      = fun y => (-c) * deriv f (y 0 - y 3) := by
    funext y
    rw [pd_3_wave c f hf1 y]
    ring
  have hc1 : coordDeriv (1 : Fin 4) (fun y : Fin 4 → ℝ => c * f (y 0 - y 3)) = fun _ => 0 :=
    funext fun y => pd_1_wave c f y
  have hc2 : coordDeriv (2 : Fin 4) (fun y : Fin 4 → ℝ => c * f (y 0 - y 3)) = fun _ => 0 :=
    funext fun y => pd_2_wave c f y
  simp only [boxEta, Fin.sum_univ_four, minkowskiMetric4_apply, h0eq, hc1, hc2, h3eq]
  rw [pd_0_wave c (deriv f) hf2 x, pd_3_wave (-c) (deriv f) hf2 x, coordDeriv_const,
    coordDeriv_const]
  norm_num

private lemma contDiffAt_wave (c : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x : Fin 4 → ℝ) :
    ContDiffAt ℝ 2 (fun y => c * f (y 0 - y 3)) x := by
  have hlin : ContDiff ℝ 2 (fun y : Fin 4 → ℝ => y 0 - y 3) :=
    (contDiff_pi.mp (contDiff_id (𝕜 := ℝ) (E := Fin 4 → ℝ)) 0).sub
      (contDiff_pi.mp (contDiff_id (𝕜 := ℝ) (E := Fin 4 → ℝ)) 3)
  exact contDiffAt_const.mul (hf.comp hlin).contDiffAt

/-- Every transverse-traceless gravitational wave with `C²` profile `f` satisfies the linearized
vacuum Einstein equations `G^{(1)}_{ij} = 0`. -/
lemma ttWave_linEinstein_zero (hPlus hCross : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (x : Fin 4 → ℝ) (i j : Fin 4) :
    linEinstein (ttWave hPlus hCross f) x i j = 0 := by
  have hsym : ∀ z a b, ttWave hPlus hCross f z a b = ttWave hPlus hCross f z b a :=
    fun z a b => (ttWave_symm hPlus hCross f z).apply b a
  have hc : ∀ a b, ContDiffAt ℝ 2 (fun z => ttWave hPlus hCross f z a b) x := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp only [ttWave] <;> norm_num
    all_goals first
      | exact contDiffAt_const
      | exact contDiffAt_wave hPlus f hf x
      | exact (contDiffAt_wave hPlus f hf x).neg
      | exact contDiffAt_wave hCross f hf x
  have hlz : ∀ᶠ y in nhds x, ∀ k, lorenzGaugeCond (ttWave hPlus hCross f) y k :=
    Filter.Eventually.of_forall fun y k => ttWave_lorenz_gauge hPlus hCross f y k
  rw [linEinstein_lorenz_gauge (ttWave hPlus hCross f) x hsym hc hlz i j]
  have htr : (fun y => traceReversed (ttWave hPlus hCross f y) i j)
      = fun y => ttWave hPlus hCross f y i j := by
    funext y; simp [traceReversed_ttWave]
  rw [htr]
  fin_cases i <;> fin_cases j <;> simp only [ttWave] <;> norm_num
  all_goals first
    | exact boxEta_zero x
    | exact boxEta_wave hPlus f hf x
    | (rw [show (fun y : Fin 4 → ℝ => -(hPlus * f (y 0 - y 3)))
          = fun y => (-hPlus) * f (y 0 - y 3) from funext fun _ => by ring];
        exact boxEta_wave (-hPlus) f hf x)
    | exact boxEta_wave hCross f hf x

end Linearized

end GeneralRelativity
