/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!

# The one-dimensional wave Cauchy problem

## i. Overview

This file formalises the classical d'Alembert solution of the wave equation

  ∂ₜ² u = ∂ₓ² u,     u(0, x) = f x,     ∂ₜ u(0, x) = g x.

It is a complete, elementary existence theorem for a linear hyperbolic PDE,
with the solution given by an explicit formula.  It is deliberately a *model*:
it is the prototype of the wave-gauge reduced Einstein equations, not the
Einstein equations themselves.  Its role is to put a genuine PDE Cauchy layer
underneath the Cauchy-problem programme, alongside the pointwise constraint
formalisation and the local geodesic ODE theorem.  No uniqueness theorem is
claimed here.


## ii. Key results

- `dAlembert`
- `dAlembert_wave_equation`
- `dAlembert_cauchy_data`

## iii. Table of contents

- A. The one-dimensional Cauchy problem

## iv. References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, §2.4.
-/
@[expose] public section

/-! ## A. The one-dimensional Cauchy problem -/

open scoped Interval Topology
open MeasureTheory

namespace GeneralRelativity

/-- The d'Alembert formula for the solution of the one-dimensional wave equation
with initial position `f` and initial velocity `g`. -/
noncomputable def dAlembert (f g : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (f (x + t) + f (x - t)) / 2 + (1 / 2) * ∫ s in (x - t)..(x + t), g s

/-- The derivative in time of the integral term in the d'Alembert formula. -/
lemma hasDerivAt_integral_shift_t (g : ℝ → ℝ) (hg : Continuous g) (t x : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ s in (x - t)..(x + t), g s)
      (g (x + t) + g (x - t)) t := by
  have h1 : HasDerivAt (fun t : ℝ => ∫ s in (x - t)..(0 : ℝ), g s) (g (x - t)) t := by
    have h := intervalIntegral.integral_hasDerivAt_left (f := g) (a := x - t) (b := 0)
      (hg.intervalIntegrable (x - t) 0)
      (hg.stronglyMeasurableAtFilter volume (𝓝 (x - t))) hg.continuousAt
    simpa using h.comp_const_sub x t
  have h2 : HasDerivAt (fun t : ℝ => ∫ s in (0 : ℝ)..(x + t), g s) (g (x + t)) t := by
    have h := intervalIntegral.integral_hasDerivAt_right (f := g) (a := 0) (b := x + t)
      (hg.intervalIntegrable 0 (x + t))
      (hg.stronglyMeasurableAtFilter volume (𝓝 (x + t))) hg.continuousAt
    simpa using h.comp_const_add x t
  have h := h1.add h2
  have h' : HasDerivAt
      (fun t : ℝ => (∫ s in (x - t)..(0 : ℝ), g s) + ∫ s in (0 : ℝ)..(x + t), g s)
      (g (x - t) + g (x + t)) t := by
    convert h using 1
  have hfun :
      (fun t : ℝ => (∫ s in (x - t)..(0 : ℝ), g s) + ∫ s in (0 : ℝ)..(x + t), g s) =
        fun t : ℝ => ∫ s in (x - t)..(x + t), g s := by
    funext t
    exact intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable (x - t) 0)
      (hg.intervalIntegrable 0 (x + t))
  rw [hfun] at h'
  convert h' using 1
  ring

/-- The derivative in space of the integral term in the d'Alembert formula. -/
lemma hasDerivAt_integral_shift_x (g : ℝ → ℝ) (hg : Continuous g) (t x : ℝ) :
    HasDerivAt (fun x : ℝ => ∫ s in (x - t)..(x + t), g s)
      (g (x + t) - g (x - t)) x := by
  have h1 : HasDerivAt (fun x : ℝ => ∫ s in (x - t)..(0 : ℝ), g s) (-g (x - t)) x := by
    have h := intervalIntegral.integral_hasDerivAt_left (f := g) (a := x - t) (b := 0)
      (hg.intervalIntegrable (x - t) 0)
      (hg.stronglyMeasurableAtFilter volume (𝓝 (x - t))) hg.continuousAt
    simpa using h.comp_sub_const x t
  have h2 : HasDerivAt (fun x : ℝ => ∫ s in (0 : ℝ)..(x + t), g s) (g (x + t)) x := by
    have h := intervalIntegral.integral_hasDerivAt_right (f := g) (a := 0) (b := x + t)
      (hg.intervalIntegrable 0 (x + t))
      (hg.stronglyMeasurableAtFilter volume (𝓝 (x + t))) hg.continuousAt
    simpa using h.comp_add_const x t
  have h := h1.add h2
  have h' : HasDerivAt
      (fun x : ℝ => (∫ s in (x - t)..(0 : ℝ), g s) + ∫ s in (0 : ℝ)..(x + t), g s)
      (-g (x - t) + g (x + t)) x := by
    convert h using 1
  have hfun :
      (fun x : ℝ => (∫ s in (x - t)..(0 : ℝ), g s) + ∫ s in (0 : ℝ)..(x + t), g s) =
        fun x : ℝ => ∫ s in (x - t)..(x + t), g s := by
    funext x
    exact intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable (x - t) 0)
      (hg.intervalIntegrable 0 (x + t))
  rw [hfun] at h'
  convert h' using 1
  ring

/-- Time derivative of the d'Alembert formula. -/
lemma hasDerivAt_dAlembert_t (f g f' : ℝ → ℝ)
    (hf : ∀ y, HasDerivAt f (f' y) y) (hg : Continuous g) (t x : ℝ) :
    HasDerivAt (fun t : ℝ => dAlembert f g t x)
      ((f' (x + t) - f' (x - t)) / 2 + (g (x + t) + g (x - t)) / 2) t := by
  unfold dAlembert
  have h1 : HasDerivAt (fun t : ℝ => f (x + t)) (f' (x + t)) t :=
    (hf (x + t)).comp_const_add x t
  have h2 : HasDerivAt (fun t : ℝ => f (x - t)) (-f' (x - t)) t :=
    (hf (x - t)).comp_const_sub x t
  have h3 : HasDerivAt (fun t : ℝ => ∫ s in (x - t)..(x + t), g s)
      (g (x + t) + g (x - t)) t := hasDerivAt_integral_shift_t g hg t x
  have h := ((h1.add h2).const_mul (1 / 2 : ℝ)).add (h3.const_mul (1 / 2 : ℝ))
  convert h using 1
  · funext y
    simp only [Pi.add_apply]
    ring
  · ring

/-- Space derivative of the d'Alembert formula. -/
lemma hasDerivAt_dAlembert_x (f g f' : ℝ → ℝ)
    (hf : ∀ y, HasDerivAt f (f' y) y) (hg : Continuous g) (t x : ℝ) :
    HasDerivAt (fun x : ℝ => dAlembert f g t x)
      ((f' (x + t) + f' (x - t)) / 2 + (g (x + t) - g (x - t)) / 2) x := by
  unfold dAlembert
  have h1 : HasDerivAt (fun x : ℝ => f (x + t)) (f' (x + t)) x :=
    (hf (x + t)).comp_add_const x t
  have h2 : HasDerivAt (fun x : ℝ => f (x - t)) (f' (x - t)) x :=
    (hf (x - t)).comp_sub_const x t
  have h3 : HasDerivAt (fun x : ℝ => ∫ s in (x - t)..(x + t), g s)
      (g (x + t) - g (x - t)) x := hasDerivAt_integral_shift_x g hg t x
  have h := ((h1.add h2).const_mul (1 / 2 : ℝ)).add (h3.const_mul (1 / 2 : ℝ))
  convert h using 1
  · funext y
    simp only [Pi.add_apply]
    ring_nf
  · ring

/-- Initial position of the d'Alembert formula. -/
lemma dAlembert_zero (f g : ℝ → ℝ) (x : ℝ) : dAlembert f g 0 x = f x := by
  unfold dAlembert
  simp

/-- Initial velocity of the d'Alembert formula. -/
lemma hasDerivAt_dAlembert_zero (f g f' : ℝ → ℝ)
    (hf : ∀ y, HasDerivAt f (f' y) y) (hg : Continuous g) (x : ℝ) :
    HasDerivAt (fun t : ℝ => dAlembert f g t x) (g x) 0 := by
  have h := hasDerivAt_dAlembert_t f g f' hf hg 0 x
  convert h using 1
  simp

/-- Time derivative of the first time derivative of the d'Alembert formula. -/
lemma hasDerivAt_waveT (f' g f'' g' : ℝ → ℝ)
    (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hg' : ∀ y, HasDerivAt g (g' y) y) (t x : ℝ) :
    HasDerivAt
      (fun t : ℝ => (f' (x + t) - f' (x - t)) / 2 + (g (x + t) + g (x - t)) / 2)
      ((f'' (x + t) + f'' (x - t)) / 2 + (g' (x + t) - g' (x - t)) / 2) t := by
  have h1 : HasDerivAt (fun t : ℝ => f' (x + t)) (f'' (x + t)) t :=
    (hf' (x + t)).comp_const_add x t
  have h2 : HasDerivAt (fun t : ℝ => f' (x - t)) (-f'' (x - t)) t :=
    (hf' (x - t)).comp_const_sub x t
  have h3 : HasDerivAt (fun t : ℝ => g (x + t)) (g' (x + t)) t :=
    (hg' (x + t)).comp_const_add x t
  have h4 : HasDerivAt (fun t : ℝ => g (x - t)) (-g' (x - t)) t :=
    (hg' (x - t)).comp_const_sub x t
  have h := ((h1.sub h2).div_const 2).add ((h3.add h4).div_const 2)
  convert h using 1
  ring

/-- Space derivative of the first space derivative of the d'Alembert formula. -/
lemma hasDerivAt_waveX (f' g f'' g' : ℝ → ℝ)
    (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hg' : ∀ y, HasDerivAt g (g' y) y) (t x : ℝ) :
    HasDerivAt
      (fun x : ℝ => (f' (x + t) + f' (x - t)) / 2 + (g (x + t) - g (x - t)) / 2)
      ((f'' (x + t) + f'' (x - t)) / 2 + (g' (x + t) - g' (x - t)) / 2) x := by
  have h1 : HasDerivAt (fun x : ℝ => f' (x + t)) (f'' (x + t)) x :=
    (hf' (x + t)).comp_add_const x t
  have h2 : HasDerivAt (fun x : ℝ => f' (x - t)) (f'' (x - t)) x :=
    (hf' (x - t)).comp_sub_const x t
  have h3 : HasDerivAt (fun x : ℝ => g (x + t)) (g' (x + t)) x :=
    (hg' (x + t)).comp_add_const x t
  have h4 : HasDerivAt (fun x : ℝ => g (x - t)) (g' (x - t)) x :=
    (hg' (x - t)).comp_sub_const x t
  have h := ((h1.add h2).div_const 2).add ((h3.sub h4).div_const 2)
  convert h using 1

/-- **The one-dimensional wave Cauchy problem.**  If `f` has first and second
derivatives `f'` and `f''`, and `g` has first derivative `g'` with `g` continuous,
then the d'Alembert formula has the prescribed initial position and velocity and
solves `∂ₜ² u = ∂ₓ² u`. -/
lemma dAlembert_wave_equation (f g f' f'' g' : ℝ → ℝ)
    (hf : ∀ y, HasDerivAt f (f' y) y)
    (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hg : ∀ y, HasDerivAt g (g' y) y)
    (hgc : Continuous g) (t x : ℝ) :
    deriv (fun t : ℝ => deriv (fun t : ℝ => dAlembert f g t x) t) t =
      deriv (fun x : ℝ => deriv (fun x : ℝ => dAlembert f g t x) x) x := by
  have ht : (fun t : ℝ => deriv (fun t : ℝ => dAlembert f g t x) t) =
      fun t : ℝ => (f' (x + t) - f' (x - t)) / 2 + (g (x + t) + g (x - t)) / 2 := by
    funext t
    exact (hasDerivAt_dAlembert_t f g f' hf hgc t x).deriv
  have hx : (fun x : ℝ => deriv (fun x : ℝ => dAlembert f g t x) x) =
      fun x : ℝ => (f' (x + t) + f' (x - t)) / 2 + (g (x + t) - g (x - t)) / 2 := by
    funext x
    exact (hasDerivAt_dAlembert_x f g f' hf hgc t x).deriv
  rw [ht, hx]
  rw [(hasDerivAt_waveT f' g f'' g' hf' hg t x).deriv,
    (hasDerivAt_waveX f' g f'' g' hf' hg t x).deriv]

/-- The d'Alembert formula gives the prescribed Cauchy data. -/
lemma dAlembert_cauchy_data (f g f' : ℝ → ℝ)
    (hf : ∀ y, HasDerivAt f (f' y) y) (hg : Continuous g) (x : ℝ) :
    dAlembert f g 0 x = f x ∧
      HasDerivAt (fun t : ℝ => dAlembert f g t x) (g x) 0 :=
  ⟨dAlembert_zero f g x, hasDerivAt_dAlembert_zero f g f' hf hg x⟩

end GeneralRelativity
