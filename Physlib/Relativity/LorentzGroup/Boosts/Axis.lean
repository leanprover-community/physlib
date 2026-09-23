/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.SL2C.AxisRotations
/-!
# Coordinate-axis boosts in `SL(2,ℂ)` and the Lorentz group

## i. Overview

We define the axis-indexed lift `Lorentz.SL2C.boostAxis` in `SL(2,ℂ)` and its image
`LorentzGroup.boostAxis` in the Lorentz group.

The parameter `t ≠ 0` is multiplicative; replacing `t` by `t⁻¹` reverses the boost. For
`t > 0`, its rapidity is `2 * log t`; negative values retain the action of the central
element `-1 : SL(2,ℂ)`.

For the `z`-axis, `LorentzGroup.boostAxis 2 t ht` agrees with the velocity-parameterized boost
`LorentzGroup.boost 2 β` at `β = (t² - t⁻²) / (t² + t⁻²)`.

The lift is Hermitian along every axis, and the `x`- and `y`-axis lifts are conjugates of
the diagonal `z`-axis lift.

The index `Sum.inl 0` is the time coordinate, while `Sum.inr 0`, `Sum.inr 1`, and
`Sum.inr 2` are the `x`, `y`, and `z` coordinates. Accordingly, axis indices `0`, `1`, and
`2` select the `x`-, `y`-, and `z`-axis boosts. The covering map uses the action
`X ↦ M X Mᴴ` on self-adjoint matrices.

## ii. Key results

- `Lorentz.SL2C.boostAxis` defines the axis-boost lifts.
- `Lorentz.SL2C.boostAxis_inv` and `Lorentz.SL2C.boostAxis_conjTranspose` give their
  inverses and Hermiticity.
- `LorentzGroup.boostAxis` defines the induced Lorentz transformations, with entries given by
  `LorentzGroup.boostAxis_apply`.
- `Lorentz.SL2C.exists_conj_boostAxis` proves that every lift is conjugate to the `z`-boost.

## iii. Table of contents

- A. The axis-boost lift
- B. Axis conjugation
- C. The induced Lorentz transformation

-/

@[expose] public section

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

namespace Lorentz.SL2C

/-!

## A. The axis-boost lift

-/

/-- The `SL(2,ℂ)` lift of the boost along spatial axis `i`, with `0 = x`, `1 = y`, and
`2 = z`. The parameter `t` is multiplicative, and for `t > 0` the rapidity is `2 * log t`. -/
noncomputable def boostAxis : Fin 3 → (t : ℝ) → t ≠ 0 → SL(2,ℂ)
  | 0, t, ht =>
      ⟨!![((t : ℂ) + (t : ℂ)⁻¹) / 2, ((t : ℂ) - (t : ℂ)⁻¹) / 2;
          ((t : ℂ) - (t : ℂ)⁻¹) / 2, ((t : ℂ) + (t : ℂ)⁻¹) / 2], by
        have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
        rw [Matrix.det_fin_two_of]
        field_simp
        ring⟩
  | 1, t, ht =>
      ⟨!![((t : ℂ) + (t : ℂ)⁻¹) / 2, -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2;
          Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2, ((t : ℂ) + (t : ℂ)⁻¹) / 2], by
        have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
        have h2 : -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2 *
            (Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2) =
            ((t : ℂ) - (t : ℂ)⁻¹) / 2 * (((t : ℂ) - (t : ℂ)⁻¹) / 2) := by
          have hI : -Complex.I * Complex.I = 1 := by
            rw [neg_mul, Complex.I_mul_I, neg_neg]
          calc -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2 *
                (Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2)
              = (-Complex.I * Complex.I) *
                  (((t : ℂ) - (t : ℂ)⁻¹) / 2 * (((t : ℂ) - (t : ℂ)⁻¹) / 2)) := by
                ring
            _ = ((t : ℂ) - (t : ℂ)⁻¹) / 2 * (((t : ℂ) - (t : ℂ)⁻¹) / 2) := by
                rw [hI, one_mul]
        rw [Matrix.det_fin_two_of, h2]
        field_simp
        ring⟩
  | 2, t, ht =>
      ⟨!![(t : ℂ), 0; 0, (t : ℂ)⁻¹], by
        have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
        rw [Matrix.det_fin_two_of]
        simp [mul_inv_cancel₀ htc]⟩

/-- The matrix entries of the `SL(2,ℂ)` boost lift along the `x`-axis. -/
@[simp] lemma boostAxis_zero_apply (t : ℝ) (ht : t ≠ 0) (j k : Fin 2) :
    (boostAxis 0 t ht).1 j k =
      (!![((t : ℂ) + (t : ℂ)⁻¹) / 2, ((t : ℂ) - (t : ℂ)⁻¹) / 2;
        ((t : ℂ) - (t : ℂ)⁻¹) / 2, ((t : ℂ) + (t : ℂ)⁻¹) / 2]) j k := rfl

/-- The matrix entries of the `SL(2,ℂ)` boost lift along the `y`-axis. -/
@[simp] lemma boostAxis_one_apply (t : ℝ) (ht : t ≠ 0) (j k : Fin 2) :
    (boostAxis 1 t ht).1 j k =
      (!![((t : ℂ) + (t : ℂ)⁻¹) / 2,
        -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2;
        Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2,
        ((t : ℂ) + (t : ℂ)⁻¹) / 2]) j k := rfl

/-- The matrix entries of the diagonal `SL(2,ℂ)` boost lift along the `z`-axis. -/
@[simp] lemma boostAxis_two_apply (t : ℝ) (ht : t ≠ 0) (j k : Fin 2) :
    (boostAxis 2 t ht).1 j k = (!![(t : ℂ), 0; 0, (t : ℂ)⁻¹]) j k := rfl

/-- Inverting an axis boost replaces its multiplicative parameter `t` by `t⁻¹`. -/
lemma boostAxis_inv (i : Fin 3) (t : ℝ) (ht : t ≠ 0) :
    (boostAxis i t ht)⁻¹ = boostAxis i t⁻¹ (inv_ne_zero ht) := by
  fin_cases i
  · ext j k
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    fin_cases j <;> fin_cases k <;>
      simp [boostAxis, Complex.ofReal_inv, inv_inv] <;>
      ring
  · ext j k
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    fin_cases j <;> fin_cases k <;>
      simp [boostAxis, Complex.ofReal_inv, inv_inv] <;>
      ring
  · ext j k
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    fin_cases j <;> fin_cases k <;>
      simp [boostAxis, Complex.ofReal_inv, inv_inv]

/-- The matrix underlying an axis-boost lift is Hermitian. -/
lemma boostAxis_conjTranspose (i : Fin 3) (t : ℝ) (ht : t ≠ 0) :
    (boostAxis i t ht).1ᴴ = (boostAxis i t ht).1 := by
  fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;> simp [boostAxis]

/-- Hermiticity read on the entries: conjugating an entry of an axis boost transposes it. -/
lemma star_boostAxis_apply (i : Fin 3) (t : ℝ) (ht : t ≠ 0) (β α : Fin 2) :
    star ((boostAxis i t ht).1 β α) = (boostAxis i t ht).1 α β := by
  have h := congrFun (congrFun (boostAxis_conjTranspose i t ht) α) β
  rwa [Matrix.conjTranspose_apply] at h

/-!

## B. Axis conjugation

-/

/-- Every axis boost is obtained by conjugating the `z`-axis boost by `rotationZToAxis`. -/
lemma boostAxis_eq_conj (i : Fin 3) (t : ℝ) (ht : t ≠ 0) :
    boostAxis i t ht =
      rotationZToAxis i * boostAxis 2 t ht * (rotationZToAxis i)⁻¹ := by
  fin_cases i
  · refine Subtype.ext ?_
    change !![((t : ℂ) + (t : ℂ)⁻¹) / 2, ((t : ℂ) - (t : ℂ)⁻¹) / 2;
        ((t : ℂ) - (t : ℂ)⁻¹) / 2, ((t : ℂ) + (t : ℂ)⁻¹) / 2] =
      (rotationZToAxis 0).1 * !![(t : ℂ), 0; 0, (t : ℂ)⁻¹] *
        ((rotationZToAxis 0)⁻¹).1
    rw [rotationZToAxis_zero_mul_diagonal_mul_inv]
  · refine Subtype.ext ?_
    change !![((t : ℂ) + (t : ℂ)⁻¹) / 2,
        -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2;
        Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2,
        ((t : ℂ) + (t : ℂ)⁻¹) / 2] =
      (rotationZToAxis 1).1 * !![(t : ℂ), 0; 0, (t : ℂ)⁻¹] *
        ((rotationZToAxis 1)⁻¹).1
    rw [rotationZToAxis_one_mul_diagonal_mul_inv]
  · refine Subtype.ext ?_
    change !![(t : ℂ), 0; 0, (t : ℂ)⁻¹] =
      (rotationZToAxis 2).1 * !![(t : ℂ), 0; 0, (t : ℂ)⁻¹] *
        ((rotationZToAxis 2)⁻¹).1
    rw [rotationZToAxis_two_mul_diagonal_mul_inv]

/-- Every coordinate-axis boost is conjugate to the `z`-axis boost. -/
lemma exists_conj_boostAxis (i : Fin 3) :
    ∃ R : SL(2,ℂ), ∀ (t : ℝ) (ht : t ≠ 0),
      boostAxis i t ht = R * boostAxis 2 t ht * R⁻¹ := by
  exact ⟨rotationZToAxis i, fun t ht => boostAxis_eq_conj i t ht⟩

end Lorentz.SL2C

namespace LorentzGroup

/-!

## C. The induced Lorentz transformation

-/

/-- The Lorentz transformation induced by the multiplicatively parameterized `SL(2,ℂ)` boost
along spatial axis `i`. -/
noncomputable def boostAxis (i : Fin 3) (t : ℝ) (ht : t ≠ 0) : LorentzGroup 3 :=
  Lorentz.SL2C.toLorentzGroup (Lorentz.SL2C.boostAxis i t ht)

/-- The entries of an axis boost in the Lorentz group. -/
lemma boostAxis_apply (i : Fin 3) (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (boostAxis i t ht).1 a b =
      if a = Sum.inl 0 ∧ b = Sum.inl 0 then (t ^ 2 + (t⁻¹) ^ 2) / 2
      else if a = Sum.inl 0 ∧ b = Sum.inr i then -((t ^ 2 - (t⁻¹) ^ 2) / 2)
      else if a = Sum.inr i ∧ b = Sum.inl 0 then -((t ^ 2 - (t⁻¹) ^ 2) / 2)
      else if a = Sum.inr i ∧ b = Sum.inr i then (t ^ 2 + (t⁻¹) ^ 2) / 2
      else if a = b then 1 else 0 := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Complex.ofReal_injective ?_
  rw [boostAxis, Lorentz.SL2C.toLorentzGroup_eq_trace,
    PauliMatrix.trace_pauliSelfAdjoint'_mul_apply, Lorentz.SL2C.boostAxis_conjTranspose]
  fin_cases i
  all_goals
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
      simp [Lorentz.SL2C.boostAxis, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
        Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp <;>
      ring_nf
  all_goals simp only [Complex.I_sq, Complex.I_pow_four]
  all_goals ring

end LorentzGroup

end
