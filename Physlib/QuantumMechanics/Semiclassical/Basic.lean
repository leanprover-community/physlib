/-
Copyright (c) 2026 Zhuoran Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhuoran Li
-/
module

public import Physlib.QuantumMechanics.Operators.Momentum
public import Physlib.QuantumMechanics.Operators.Position

/-!
# Semiclassical momentum and Fourier coordinates

Introduce a variable reduced Planck parameter while retaining the existing operator API.

## i. Overview

The parameter `h` represents the reduced Planck constant and can vary independently of
`Constants.ℏ`. Scaling the existing momentum by `h / Constants.ℏ` gives `-i h` times the
spatial derivative. The Fourier identities record Mathlib's `2 pi` normalization explicitly.
All operators in this file act on Schwartz maps; the inner products use their `L^2` classes.

## ii. Key results

- `momentumCLM` : momentum with a variable semiclassical parameter
- `momentumCLM_inner` : symmetry on the common Schwartz domain
- `fourier_momentumCLM`, `fourier_positionCLM` : the Fourier-coordinate identities

## iii. Table of contents

- A. Semiclassical momentum
- B. Fourier coordinates

## iv. References

* None.
-/

@[expose] public section

namespace QuantumMechanics.Semiclassical

noncomputable section

open Complex Real MeasureTheory SchwartzMap ContinuousLinearMap
open SpaceDHilbertSpace
open scoped FourierTransform InnerProductSpace

variable {d : ℕ}

/-! ## A. Semiclassical momentum -/

/-- Momentum with a variable reduced Planck parameter `h`, obtained by scaling the existing
momentum. -/
def momentumCLM (h : ℝ) (i : Fin d) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (h / (Constants.ℏ : ℝ)) • QuantumMechanics.momentumCLM i

/-- The physical value of the parameter recovers the existing momentum operator. -/
@[simp]
lemma momentumCLM_hbar (i : Fin d) :
    momentumCLM (Constants.ℏ : ℝ) i = QuantumMechanics.momentumCLM i := by
  simp [momentumCLM]

/-- The momentum vanishes at parameter zero. -/
@[simp]
lemma momentumCLM_zero (i : Fin d) : momentumCLM 0 i = 0 := by
  simp [momentumCLM]

/-- The semiclassical momentum acts as `-i h` times the spatial derivative. -/
lemma momentumCLM_apply (h : ℝ) (i : Fin d) (f : 𝓢(Space d, ℂ)) (x : Space d) :
    momentumCLM h i f x = -I * h * Space.deriv i f x := by
  simp only [momentumCLM, smul_apply,
    QuantumMechanics.momentumCLM_apply, Complex.real_smul, ofReal_div]
  field_simp

/-- Semiclassical momentum is symmetric on the common Schwartz domain. -/
lemma momentumCLM_inner (h : ℝ) (i : Fin d) (f g : 𝓢(Space d, ℂ)) :
    ⟪schwartzIncl volume (momentumCLM h i f), schwartzIncl volume g⟫_ℂ =
      ⟪schwartzIncl volume f, schwartzIncl volume (momentumCLM h i g)⟫_ℂ := by
  simp only [momentumCLM, smul_apply, map_smul_of_tower,
    inner_smul_left_eq_star_smul, inner_smul_right_eq_smul]
  congr 1
  simpa only [SchwartzSubmodule.schwartzEquiv_apply_coe] using
    QuantumMechanics.momentumCLM_inner i f g

/-- Express semiclassical momentum in the directional-derivative API. -/
lemma momentumCLM_eq_lineDeriv (h : ℝ) (i : Fin d) (f : 𝓢(Space d, ℂ)) :
    momentumCLM h i f = (-I * h) • LineDeriv.lineDerivOp (Space.basis i) f := by
  ext x
  simp [momentumCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, Space.deriv]

/-! ## B. Fourier coordinates -/

/-- Express position using the real inner-product multiplier used by the Fourier API. -/
private lemma positionCLM_eq_smulLeftCLM_inner (i : Fin d) (f : 𝓢(Space d, ℂ)) :
    𝐱 i f = SchwartzMap.smulLeftCLM ℂ (inner ℝ · (Space.basis i)) f := by
  ext x
  rw [smulLeftCLM_apply_apply (by fun_prop)]
  simp [Space.inner_basis, Complex.real_smul]

/-- The Fourier transform sends momentum to multiplication by `2 pi h` times the coordinate. -/
lemma fourier_momentumCLM (h : ℝ) (i : Fin d) (f : 𝓢(Space d, ℂ)) :
    𝓕 (momentumCLM h i f) = (2 * π * h : ℂ) • 𝐱 i (𝓕 f) := by
  rw [momentumCLM_eq_lineDeriv, FourierTransform.fourier_smul,
    SchwartzMap.fourier_lineDerivOp_eq, ← positionCLM_eq_smulLeftCLM_inner]
  ext ξ
  simp only [smul_apply, smul_eq_mul]
  ring_nf
  simp [I_sq]

/-- Momentum after the Fourier transform is the transform of `-2 pi h` times position. -/
lemma momentumCLM_fourier (h : ℝ) (i : Fin d) (f : 𝓢(Space d, ℂ)) :
    momentumCLM h i (𝓕 f) = -(2 * π * h : ℂ) • 𝓕 (𝐱 i f) := by
  rw [momentumCLM_eq_lineDeriv, SchwartzMap.lineDerivOp_fourier_eq,
    ← positionCLM_eq_smulLeftCLM_inner, FourierTransform.fourier_smul]
  ext ξ
  simp only [smul_apply, smul_eq_mul]
  ring_nf
  simp [I_sq]

/-- The Fourier transform of position, for a nonzero semiclassical parameter. -/
lemma fourier_positionCLM (h : ℝ) (hh : h ≠ 0) (i : Fin d) (f : 𝓢(Space d, ℂ)) :
    𝓕 (𝐱 i f) = (-(2 * π * h : ℂ))⁻¹ • momentumCLM h i (𝓕 f) := by
  rw [momentumCLM_fourier, inv_smul_smul₀]
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast pi_ne_zero))
    (by exact_mod_cast hh))

end

end QuantumMechanics.Semiclassical
