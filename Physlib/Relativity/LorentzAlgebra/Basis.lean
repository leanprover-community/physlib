/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Physlib.Relativity.LorentzAlgebra.Basic
public import Physlib.Relativity.LorentzGroup.Boosts.Basic

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Generators of the Lorentz algebra

Standard boost and rotation generators and the tangent of a finite boost curve.

## i. Overview

This file defines the 6 standard generators of the Lorentz algebra so(1,3) :
- **Boost generators** K₀, K₁, K₂: Generate Lorentz transformations (velocity changes)
- **Rotation generators** J₀, J₁, J₂: Generate spatial rotations

These generators form a basis for the 6-dimensional Lie algebra so(1,3), though the full
basis structure (linear independence and spanning) is not yet proven here.

- `boostGenerator i`: Infinitesimal boost in the i-th spatial direction. The native
  boost curve parametrized by rapidity has tangent `-boostGenerator i` at zero.
- `rotationGenerator i`: Infinitesimal rotation about the i-th axis following the
  right-hand rule. Exponentiating this generator produces spatial rotations.

Each generator satisfies the Lorentz algebra condition: Aᵀ η = -η A, where η is the
Minkowski metric with signature (+,-,-,-).

The boost generators are symmetric matrices with non-zero entries only in the time-space
block, while rotation generators are antisymmetric matrices acting only on spatial indices.

TODO can be completed by proving linear independence and spanning of these
6 generators, then constructing a formal `Basis (Fin 2 × Fin 3) ℝ lorentzAlgebra`.

## ii. Key results

- `boostGenerator_mem` and `rotationGenerator_mem`: the generators lie in the Lorentz algebra.
- `hasDerivAt_boost_tanh_zero`: the rapidity boost curve has tangent the negative boost generator.

## iii. Table of contents

- A. Generator definitions
- B. Algebraic properties
- C. Rapidity derivatives

## iv. References

* Weinberg, The Quantum Theory of Fields, Vol 1, Section 2.7. [ref: weinberg_qft1]
* Peskin & Schroeder, An Introduction to QFT, Appendix A. [ref: peskin_schroeder_qft]
-/

@[expose] public section

open Matrix

namespace lorentzAlgebra

/-! ## A. Generator definitions -/

/-- The boost generator K_i in the Lorentz algebra so(1,3).

This matrix generates infinitesimal Lorentz boosts in the i-th spatial direction.
The matrix has non-zero entries only at positions (0, i+1) and (i+1, 0) with value 1,
where we use the index convention 0 = time, 1,2,3 = space.

## Properties
- Symmetric: K_iᵀ = K_i
- Traceless: tr(K_i) = 0
- Satisfies Lorentz algebra condition: K_iᵀ η = -η K_i

## Physical Meaning
The native boost curve `LorentzGroup.boost i (Real.tanh r)` has tangent `-K_i` at
rapidity zero, as proved by `hasDerivAt_boost_tanh_zero`.
-/
def boostGenerator (i : Fin 3) : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ :=
  fun μ ν =>
    if (μ = Sum.inl 0 ∧ ν = Sum.inr i) ∨ (μ = Sum.inr i ∧ ν = Sum.inl 0) then 1
    else 0

/-- The rotation generator J_i in the Lorentz algebra so(1,3).

This matrix generates infinitesimal rotations about the i-th axis following the right-hand rule.
The matrix acts only on spatial indices in the antisymmetric pattern characteristic of
angular momentum generators.

## Properties
- Antisymmetric: J_iᵀ = -J_i
- Traceless: tr(J_i) = 0
- Satisfies Lorentz algebra condition: J_iᵀ η = -η J_i

## Structure
- J_0 (rotation about x-axis) : Acts on (y,z) components
- J_1 (rotation about y-axis) : Acts on (z,x) components
- J_2 (rotation about z-axis) : Acts on (x,y) components

## Physical Meaning
Exponentiating θ·J_i produces a finite rotation by angle θ about axis i.
-/
def rotationGenerator (i : Fin 3) : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ :=
  fun μ ν =>
    match i with
    | 0 => if μ = Sum.inr 1 ∧ ν = Sum.inr 2 then -1
            else if μ = Sum.inr 2 ∧ ν = Sum.inr 1 then 1
            else 0
      | 1 => if μ = Sum.inr 0 ∧ ν = Sum.inr 2 then 1
            else if μ = Sum.inr 2 ∧ ν = Sum.inr 0 then -1
            else 0
      | 2 => if μ = Sum.inr 0 ∧ ν = Sum.inr 1 then -1
            else if μ = Sum.inr 1 ∧ ν = Sum.inr 0 then 1
            else 0

/-! ## B. Algebraic properties -/

/-- The boost generator K_i is in the Lorentz algebra. -/
lemma boostGenerator_mem (i : Fin 3) : boostGenerator i ∈ lorentzAlgebra := by
  rw [lorentzAlgebra.mem_iff]
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    simp [boostGenerator, minkowskiMatrix.as_diagonal, mul_diagonal, diagonal_mul, neg_ite]

/-- The rotation generator J_i is in the Lorentz algebra. -/
lemma rotationGenerator_mem (i : Fin 3) : rotationGenerator i ∈ lorentzAlgebra := by
  rw [lorentzAlgebra.mem_iff]
  ext μ ν
  fin_cases i <;> fin_cases μ <;> fin_cases ν <;>
    simp [rotationGenerator, minkowskiMatrix.as_diagonal, mul_diagonal, diagonal_mul]

/-- The boost generators are symmetric. -/
@[simp]
lemma boostGenerator_transpose (i : Fin 3) :
    (boostGenerator i)ᵀ = boostGenerator i := by
  ext μ ν
  simp only [transpose_apply, boostGenerator, and_comm, or_comm]

/-- The boost generators are traceless. -/
@[simp]
lemma boostGenerator_trace (i : Fin 3) :
    Matrix.trace (boostGenerator i) = 0 := by
  simp [Matrix.trace, Matrix.diag, boostGenerator]

/-- The rotation generators are antisymmetric. -/
@[simp]
lemma rotationGenerator_transpose (i : Fin 3) :
    (rotationGenerator i)ᵀ = -rotationGenerator i := by
  ext μ ν
  fin_cases i <;> fin_cases μ <;> fin_cases ν <;> simp [rotationGenerator]

/-- The rotation generators are traceless. -/
@[simp]
lemma rotationGenerator_trace (i : Fin 3) :
    Matrix.trace (rotationGenerator i) = 0 := by
  have h := Matrix.trace_transpose (rotationGenerator i)
  rw [rotationGenerator_transpose, Matrix.trace_neg] at h
  exact eq_zero_of_neg_eq h

/-! ## C. Rapidity derivatives -/

/-- The tangent at zero of the finite boost curve parametrized by rapidity
is the negative of the named boost generator. -/
lemma hasDerivAt_boost_tanh_zero (i : Fin 3) :
    HasDerivAt (fun r : ℝ => (LorentzGroup.boost i (Real.tanh r) (Real.abs_tanh_lt_one r)).1)
      (-boostGenerator i) 0 := by
  have hcosh (r : ℝ) : Real.cosh r * Real.tanh r = Real.sinh r := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [ne_of_gt (Real.cosh_pos r)]
  apply hasDerivAt_pi.mpr
  intro μ
  apply hasDerivAt_pi.mpr
  intro ν
  fin_cases i <;> fin_cases μ <;> fin_cases ν <;>
    simp [LorentzGroup.boost, boostGenerator, LorentzGroup.γ_tanh, hcosh, neg_mul]
  all_goals first
    | simpa only [Real.sinh_zero] using Real.hasDerivAt_cosh 0
    | simpa only [Real.cosh_zero] using (Real.hasDerivAt_sinh 0).fun_neg
    | exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
    | exact hasDerivAt_const (0 : ℝ) (1 : ℝ)

end lorentzAlgebra
