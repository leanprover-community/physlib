/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Physlib.Relativity.SL2C.Basic
/-!
# Coordinate-axis rotations in `SL(2,ℂ)`

This file defines chosen `SL(2,ℂ)` rotations associated with the spatial coordinate axes. The
spatial-axis convention is `0 = x`, `1 = y`, and `2 = z`.

The cyclic rotation is the rotation by `2π/3` about the diagonal spatial axis. Its Lorentz matrix
fixes time and permutes the spatial directions as `x → y → z → x`. The rotations from the `z`-axis
to a selected coordinate axis provide the common change of basis used by coordinate-axis boosts
and later constructions based on diagonal representatives.

The main declarations are:

- `Lorentz.cycDir`, the cyclic permutation of Lorentz direction labels;
- `rotationCycle`, the cyclic rotation in `SL(2,ℂ)`;
- `toLorentzGroup_rotationCycle_apply`, its Lorentz matrix;
- `rotationZToAxis`, the indexed family of rotations;
- `rotationZToAxis_zero_apply` and its companions, their matrix entries;
- `rotationZToAxis_zero_mul_diagonal_mul_inv` and its companions, their action on a
  diagonal matrix;
- `halfTurn`, the rotation by `π` about a coordinate axis, lifted as `-i σ_k`;
- `toLorentzGroup_halfTurn_apply`, its diagonal Lorentz matrix with signs `halfTurnSign`.
-/

@[expose] public section

/-!

## A. The cyclic coordinate rotation

-/

namespace Lorentz

/-- The cyclic permutation of Lorentz direction labels: time is fixed and the spatial
directions rotate as `x → y → z → x`. -/
def cycDir : Fin 1 ⊕ Fin 3 → Fin 1 ⊕ Fin 3 := Sum.map id (· + 1)

/-- The cyclic permutation fixes the time direction. -/
@[simp] lemma cycDir_inl : cycDir (Sum.inl 0) = Sum.inl 0 := rfl

/-- The cyclic permutation advances a spatial direction by one. -/
@[simp] lemma cycDir_inr (m : Fin 3) : cycDir (Sum.inr m) = Sum.inr (m + 1) := rfl

/-- Composing the cyclic permutation with a two-slot index vector rotates both entries. -/
lemma cycDir_comp_two (μ ν : Fin 1 ⊕ Fin 3) :
    (fun j => cycDir (![μ, ν] j)) = ![cycDir μ, cycDir ν] := by
  funext j
  fin_cases j <;> rfl

/-- Composing the cyclic permutation with a one-slot index vector rotates its entry. -/
lemma cycDir_comp_one (μ : Fin 1 ⊕ Fin 3) :
    (fun j => cycDir (![μ] j)) = ![cycDir μ] := by
  funext j
  fin_cases j
  rfl

/-- Composing the cyclic permutation with the empty index vector is the empty vector. -/
lemma cycDir_comp_nil : (fun j : Fin 0 => cycDir (![] j)) = ![] := by
  funext j
  exact j.elim0

/-- The cyclic permutation of Lorentz direction labels has order three. -/
lemma cycDir_cycDir_cycDir (μ : Fin 1 ⊕ Fin 3) : cycDir (cycDir (cycDir μ)) = μ := by
  rcases μ with μ | μ
  · rfl
  · simp only [cycDir, Sum.map_inr]
    congr 1
    calc
      (μ + 1 + 1) + 1 = μ + ((1 + 1 + 1) : Fin 3) := by ac_rfl
      _ = μ + 0 := rfl
      _ = μ := add_zero μ

/-- The cyclic permutation of Lorentz direction labels is injective: applying it twice
more returns the original label. -/
lemma cycDir_injective : Function.Injective cycDir :=
  Function.LeftInverse.injective (g := fun μ => cycDir (cycDir μ)) cycDir_cycDir_cycDir

/-- An index not fixed by the rotation has three distinct rotations. -/
lemma cycDir_orbit_distinct {ι : Type*} (d : ι → Fin 1 ⊕ Fin 3)
    (hd : (fun s => cycDir (d s)) ≠ d) :
    (fun s => cycDir (cycDir (d s))) ≠ d
      ∧ (fun s => cycDir (cycDir (d s))) ≠ (fun s => cycDir (d s)) := by
  constructor
  · refine fun h => hd (funext fun s => ?_)
    have h3 := congrArg cycDir (congrFun h s)
    rw [cycDir_cycDir_cycDir] at h3
    exact h3.symm
  · exact fun h => hd (funext fun s => cycDir_injective (congrFun h s))

namespace SL2C

open Matrix MatrixGroups

/-- The cyclic rotation `x → y → z → x` in `SL(2,ℂ)`, realized as the rotation by
`2π/3` about the diagonal spatial axis. -/
noncomputable def rotationCycle : SL(2,ℂ) :=
  ⟨(2 : ℂ)⁻¹ • !![1 - Complex.I, -(1 + Complex.I); 1 - Complex.I, 1 + Complex.I], by
    rw [Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin]
    simp [Complex.ext_iff]
    norm_num⟩

/-- The Lorentz matrix of `rotationCycle`: it is the permutation matrix associated with
`cycDir`. -/
lemma toLorentzGroup_rotationCycle_apply (a b : Fin 1 ⊕ Fin 3) :
    (toLorentzGroup rotationCycle).1 a b = if a = cycDir b then 1 else 0 := by
  refine Complex.ofReal_injective ?_
  rw [toLorentzGroup_eq_trace, PauliMatrix.trace_pauliSelfAdjoint'_mul_apply]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [rotationCycle, cycDir, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Complex.ext_iff] <;>
    norm_num

end SL2C

end Lorentz

/-!

## B. Rotations from the `z`-axis

-/

namespace Lorentz.SL2C

open Matrix MatrixGroups

/-- The `SL(2,ℂ)` rotation carrying the `z`-axis to axis `i`. -/
noncomputable def rotationZToAxis : Fin 3 → SL(2,ℂ)
  | 0 =>
      ⟨(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, -1; 1, 1], by
        rw [Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin, inv_pow]
        norm_num [← Complex.ofReal_pow, Real.sq_sqrt]⟩
  | 1 =>
      ⟨(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, Complex.I; Complex.I, 1], by
        rw [Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin, inv_pow,
          Complex.I_mul_I]
        norm_num [← Complex.ofReal_pow, Real.sq_sqrt]⟩
  | 2 => 1

/-- The matrix entries of the rotation carrying the `z`-axis to the `x`-axis. -/
@[simp] lemma rotationZToAxis_zero_apply (j k : Fin 2) :
    (rotationZToAxis 0).1 j k =
      ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, -1; 1, 1]) j k := rfl

/-- The matrix entries of the rotation carrying the `z`-axis to the `y`-axis. -/
@[simp] lemma rotationZToAxis_one_apply (j k : Fin 2) :
    (rotationZToAxis 1).1 j k =
      ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, Complex.I; Complex.I, 1]) j k := rfl

/-- The rotation carrying the `z`-axis to itself is the identity matrix. -/
@[simp] lemma rotationZToAxis_two_apply (j k : Fin 2) :
    (rotationZToAxis 2).1 j k = (1 : Matrix (Fin 2) (Fin 2) ℂ) j k := rfl

/-- The matrix entries of the inverse rotation from the `x`-axis to the `z`-axis. -/
@[simp] lemma rotationZToAxis_zero_inv_apply (j k : Fin 2) :
    ((rotationZToAxis 0)⁻¹).1 j k =
      ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, 1; -1, 1]) j k := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases j <;> fin_cases k <;> simp [rotationZToAxis]

/-- The matrix entries of the inverse rotation from the `y`-axis to the `z`-axis. -/
@[simp] lemma rotationZToAxis_one_inv_apply (j k : Fin 2) :
    ((rotationZToAxis 1)⁻¹).1 j k =
      ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, -Complex.I; -Complex.I, 1]) j k := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases j <;> fin_cases k <;> simp [rotationZToAxis]

/-- The inverse rotation from the `z`-axis to itself is the identity matrix. -/
@[simp] lemma rotationZToAxis_two_inv_apply (j k : Fin 2) :
    ((rotationZToAxis 2)⁻¹).1 j k = (1 : Matrix (Fin 2) (Fin 2) ℂ) j k := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases j <;> fin_cases k <;> simp [rotationZToAxis]

/-- Conjugating `diag(a, b)` by the rotation to the `x`-axis expresses it in the `x`-axis
basis. -/
lemma rotationZToAxis_zero_mul_diagonal_mul_inv (a b : ℂ) :
    (rotationZToAxis 0).1 * !![a, 0; 0, b] * ((rotationZToAxis 0)⁻¹).1 =
      !![(a + b) / 2, (a - b) / 2; (a - b) / 2, (a + b) / 2] := by
  have hsqrt_ne : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by simp
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, rotationZToAxis_zero_apply,
      rotationZToAxis_zero_inv_apply] <;>
    simp <;>
    field_simp <;>
    norm_num [← Complex.ofReal_pow, Real.sq_sqrt] <;>
    ring

/-- Conjugating `diag(a, b)` by the rotation to the `y`-axis expresses it in the `y`-axis
basis. -/
lemma rotationZToAxis_one_mul_diagonal_mul_inv (a b : ℂ) :
    (rotationZToAxis 1).1 * !![a, 0; 0, b] * ((rotationZToAxis 1)⁻¹).1 =
      !![(a + b) / 2, -Complex.I * (a - b) / 2;
        Complex.I * (a - b) / 2, (a + b) / 2] := by
  have hsqrt_ne : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by simp
  ext j k
  fin_cases j <;> fin_cases k
  all_goals
    simp only [Matrix.mul_apply, Fin.sum_univ_two, rotationZToAxis_one_apply,
      rotationZToAxis_one_inv_apply]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.smul_apply, of_apply, cons_val',
      cons_val_zero, cons_val_fin_one, smul_eq_mul, mul_one, cons_val_one, mul_zero,
      add_zero, zero_add, mul_neg, neg_mul, Fin.mk_one]
    field_simp
    norm_num [← Complex.ofReal_pow, Real.sq_sqrt]
  all_goals ring

/-- Conjugating `diag(a, b)` by the identity rotation leaves it unchanged. -/
lemma rotationZToAxis_two_mul_diagonal_mul_inv (a b : ℂ) :
    (rotationZToAxis 2).1 * !![a, 0; 0, b] * ((rotationZToAxis 2)⁻¹).1 =
      !![a, 0; 0, b] := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, rotationZToAxis_two_apply,
      rotationZToAxis_two_inv_apply] <;>
    simp [Matrix.one_apply]

end Lorentz.SL2C

/-!

## C. Half turns about the coordinate axes

The half turn about the axis `k` is the rotation by `π` about it. It has two lifts to
`SL(2,ℂ)`, `-i σ_k` and `i σ_k`, which differ by the central element `-1` and have the same
Lorentz matrix. The chosen lift `halfTurn k` is `-i σ_k`, the value at `θ = π` of
`cos (θ / 2) - i sin (θ / 2) σ_k`, the convention `rotationCycle` also follows. Its Lorentz
matrix is diagonal: it fixes time and the axis and negates the two transverse directions, with
the signs recorded by `halfTurnSign`.

-/

namespace Lorentz

/-- The sign the half turn about the axis `k` gives a direction: `1` on time and on the axis,
`-1` on the two transverse directions. -/
def halfTurnSign (k : Fin 3) (μ : Fin 1 ⊕ Fin 3) : ℤ :=
  if μ = Sum.inl 0 ∨ μ = Sum.inr k then 1 else -1

namespace SL2C

open Matrix MatrixGroups

/-- The half turn about the axis `k`, the rotation by `π` about it, as the element `-i σ_k` of
`SL(2,ℂ)`. The other lift `i σ_k` is `-halfTurn k`. -/
noncomputable def halfTurn : Fin 3 → SL(2,ℂ)
  | 0 => ⟨!![0, -Complex.I; -Complex.I, 0], by
      rw [Matrix.det_fin_two_of]
      simp [Complex.I_mul_I]⟩
  | 1 => ⟨!![0, -1; 1, 0], by
      rw [Matrix.det_fin_two_of]
      simp⟩
  | 2 => ⟨!![-Complex.I, 0; 0, Complex.I], by
      rw [Matrix.det_fin_two_of]
      simp [Complex.I_mul_I]⟩

/-- The matrix entries of the half turn about the `x`-axis, `-i σ_x`. -/
@[simp] lemma halfTurn_zero_apply (j k : Fin 2) :
    (halfTurn 0).1 j k = (!![0, -Complex.I; -Complex.I, 0]) j k := rfl

/-- The matrix entries of the half turn about the `y`-axis, `-i σ_y`. -/
@[simp] lemma halfTurn_one_apply (j k : Fin 2) :
    (halfTurn 1).1 j k = (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) j k := rfl

/-- The matrix entries of the half turn about the `z`-axis, `-i σ_z`. -/
@[simp] lemma halfTurn_two_apply (j k : Fin 2) :
    (halfTurn 2).1 j k = (!![-Complex.I, 0; 0, Complex.I]) j k := rfl

/-- The Lorentz matrix of the half turn about the axis `k` is diagonal, with the signs
`halfTurnSign k`: it fixes time and the axis and negates the two transverse directions. -/
lemma toLorentzGroup_halfTurn_apply (k : Fin 3) (a b : Fin 1 ⊕ Fin 3) :
    (toLorentzGroup (halfTurn k)).1 a b = if a = b then (halfTurnSign k a : ℝ) else 0 := by
  refine Complex.ofReal_injective ?_
  rw [toLorentzGroup_eq_trace, PauliMatrix.trace_pauliSelfAdjoint'_mul_apply]
  fin_cases k <;> rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [halfTurnSign, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.ext_iff]

/-- The Lorentz matrix of the half turn is diagonal, hence symmetric. -/
lemma toLorentzGroup_halfTurn_symm (k : Fin 3) (a b : Fin 1 ⊕ Fin 3) :
    (toLorentzGroup (halfTurn k)).1 a b = (toLorentzGroup (halfTurn k)).1 b a := by
  rw [toLorentzGroup_halfTurn_apply, toLorentzGroup_halfTurn_apply]
  by_cases h : a = b
  · rw [h]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

end SL2C

end Lorentz

end
