/-
Copyright (c) 2026 Anand Nambakam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Nambakam
-/
module

public import QuantumInfo.States.Pure.BlochSphere

/-!
# Pancharatnam Connection

The angle-parameterized qubit ket `qubitKet α θ` represents the quantum
state `cos(α/2)|0⟩ + e^{iθ}sin(α/2)|1⟩`, mapping to the Bloch sphere
at polar angle `α` and azimuthal angle `θ`.

## Important definitions
 * `qubitKet`: qubit state from Bloch sphere angles

## Important results
 * `dot_qubitKet`: inner product in half-angle form

## References
 * [S. Pancharatnam, *Generalized theory of interference, and its
   applications*, Proc. Indian Acad. Sci. A 44, 247–262 (1956)][pancharatnam1956]
-/

open Braket Complex

noncomputable section

/-- The raw vector for `qubitKet`. Internal helper. -/
private def qubitKetVec (α θ : ℝ) : Fin 2 → ℂ :=
  ![↑(Real.cos (α / 2)), exp (↑θ * I) * ↑(Real.sin (α / 2))]

/-- A qubit state parameterized by Bloch sphere polar angle `α` and
    azimuthal angle `θ`: `|ψ⟩ = cos(α/2)|0⟩ + e^{iθ}sin(α/2)|1⟩`. -/
def qubitKet (α θ : ℝ) : Ket (Fin 2) where
  vec := qubitKetVec α θ
  normalized' := by
    simp only [qubitKetVec, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Complex.norm_real, norm_mul, norm_exp_ofReal_mul_I, one_mul, Real.norm_eq_abs, sq_abs]
    linarith [Real.sin_sq_add_cos_sq (α / 2)]

@[simp]
lemma qubitKet_apply_zero (α θ : ℝ) :
    (qubitKet α θ) (0 : Fin 2) = ↑(Real.cos (α / 2)) := rfl

@[simp]
lemma qubitKet_apply_one (α θ : ℝ) :
    (qubitKet α θ) (1 : Fin 2) = exp (↑θ * I) * ↑(Real.sin (α / 2)) := rfl

/-- The inner product of two angle-parameterized qubit states:
    `⟨ψ₁|ψ₂⟩ = cos(α₁/2)cos(α₂/2) + e^{i(θ₂-θ₁)}sin(α₁/2)sin(α₂/2)`. -/
lemma dot_qubitKet (α₁ θ₁ α₂ θ₂ : ℝ) :
    〈qubitKet α₁ θ₁‖qubitKet α₂ θ₂〉 =
    ↑(Real.cos (α₁ / 2) * Real.cos (α₂ / 2)) +
    exp (↑(θ₂ - θ₁) * I) * ↑(Real.sin (α₁ / 2) * Real.sin (α₂ / 2)) := by
  unfold Braket.dot
  simp only [Fin.sum_univ_two, Bra.eq_conj, qubitKet_apply_zero, qubitKet_apply_one]
  simp only [map_mul, conj_ofReal, ofReal_mul]
  rw [show starRingEnd ℂ (exp (↑θ₁ * I)) = exp (-(↑θ₁ * I)) from by
    rw [← Complex.exp_conj]; congr 1; simp [conj_ofReal, conj_I, mul_neg]]
  congr 1
  have : exp (-(↑θ₁ * I)) * ↑(Real.sin (α₁ / 2)) *
      (exp (↑θ₂ * I) * ↑(Real.sin (α₂ / 2))) =
      exp (-(↑θ₁ * I) + ↑θ₂ * I) *
      (↑(Real.sin (α₁ / 2)) * ↑(Real.sin (α₂ / 2))) := by
    rw [exp_add]; ring
  rw [this]
  congr 1
  congr 1
  push_cast
  ring
