/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Physlib.Relativity.PauliMatrices.SelfAdjoint
public import Physlib.Relativity.SL2C.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Pre.Contraction
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.Uncertainty
/-!

# The uncertainty cone

## i. Overview

A self-adjoint `2 × 2` matrix is `v₀ 1 + v₁ σ₁ + v₂ σ₂ + v₃ σ₃` for one real four-vector `v`
(`PauliMatrix.pauliBasis`), its determinant is the Minkowski interval `v₀² - |v⃗|²`, and
`SL(2, ℂ)` keeps it (van der Waerden, 1929). The Gram matrix of the fluctuations of two
observables `a`, `b` in a state `ω` is such a matrix. Its four-vector carries the variances in
`v₀ ± v₃`, the covariance in `v₁` and the bracket `ω⟨⁅a, b⁆⟩` in `v₂`, and its interval is the
centered Gram defect. The Robertson–Schrödinger relation says exactly that this four-vector lies
in the closed future cone, and it is an equality exactly when the four-vector is null.

## ii. Key results

- `PauliMatrix.det_eq_scalarCoeff_sq_sub_pauliRadius_sq` : `det A = v₀² - |v⃗|²`.
- `gramMatrix` : the Gram matrix of the fluctuations of `a` and `b`.
- `det_gramMatrix` : its interval is the centered Gram defect.
- `scalarCoeff_gramMatrix`, `vectorCoeff_gramMatrix` : its four-vector.
- `pauliRadius_gramMatrix_le` : the four-vector lies in the closed future cone.
- `pauliRadius_gramMatrix_eq_iff` : it is null iff the centered Gram defect vanishes.
- `det_toSelfAdjointMap_gramMatrix` : `SL(2, ℂ)` keeps the interval.
- `gramVector` : the Gram four-vector as a contravariant Lorentz vector.
- `minkowski_gramVector` : its Minkowski square is the centered Gram defect.

## iii. Table of contents

- A. The determinant is the Minkowski interval
- B. The Gram matrix of two fluctuations
- C. The future cone
- D. The Lorentz vector of two fluctuations

## iv. References

* B. L. van der Waerden, *Spinoranalyse*, Nachrichten von der Gesellschaft der Wissenschaften
  zu Göttingen (1929) 100–109.
* H. P. Robertson, *A general formulation of the uncertainty principle and its classical
  interpretation*, Phys. Rev. 35 (1930) 667.

-/

@[expose] public section

/-!

## A. The determinant is the Minkowski interval

-/

namespace PauliMatrix

open Matrix

/-- **The determinant is the Minkowski interval**: `det A = v₀² - |v⃗|²` for the Pauli
four-vector `v` of a self-adjoint `2 × 2` matrix `A`. -/
lemma det_eq_scalarCoeff_sq_sub_pauliRadius_sq (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    A.1.det = ((scalarCoeff A ^ 2 - pauliRadius A ^ 2 : ℝ) : ℂ) := by
  have hA := matrix_eq_scalar_add_vector A
  have hsq := congrFun (congrFun (vectorPart_sq A) 0) 0
  have htr := trace_vectorPart A
  simp only [mul_apply, Fin.sum_univ_two, Matrix.smul_apply, one_apply_eq, Complex.real_smul,
    mul_one] at hsq
  push_cast at hsq
  rw [trace_fin_two] at htr
  rw [hA, det_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, one_apply_eq,
    one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    one_apply_ne (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul, mul_one, mul_zero, zero_add]
  push_cast
  linear_combination (-1 : ℂ) * hsq + (vectorPart A 0 0 + (scalarCoeff A : ℂ)) * htr

end PauliMatrix

namespace ProbabilisticTheory

open scoped ComplexOrder selfAdjoint MatrixGroups TensorProduct
open Matrix PauliMatrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace UnitalPositiveLinearMap

/-!

## B. The Gram matrix of two fluctuations

-/

/-- The Gram matrix of the fluctuations of `a` and `b` in the state `ω`. -/
noncomputable def gramMatrix (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨!![(variance ω a : ℂ), ω ((centered ω a : A) * centered ω b);
      star (ω ((centered ω a : A) * centered ω b)), (variance ω b : ℂ)], by
    rw [selfAdjoint.mem_iff, star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp⟩

variable (ω : 𝓢[ℂ, A]) (a b : Observable A)

/-- The interval of the Gram matrix is the centered Gram defect. -/
lemma det_gramMatrix : (gramMatrix ω a b).1.det = (centeredGramDefect ω a b : ℂ) := by
  rw [gramMatrix, det_fin_two_of, centeredGramDefect, Complex.star_def, Complex.mul_conj]
  push_cast
  ring

/-- The time component of the Gram four-vector is the mean variance. -/
lemma scalarCoeff_gramMatrix :
    scalarCoeff (gramMatrix ω a b) = (variance ω a + variance ω b) / 2 := by
  have h := trace_eq_two_mul_scalarCoeff (gramMatrix ω a b)
  have ht : trace (gramMatrix ω a b).1 = ((variance ω a + variance ω b : ℝ) : ℂ) := by
    simp [gramMatrix, trace_fin_two_of]
  rw [ht] at h
  have := congrArg Complex.re h
  simp only [Complex.ofReal_re, Complex.re_ofNat, Complex.mul_re, Complex.ofReal_im,
    Complex.im_ofNat, mul_zero, sub_zero] at this
  linarith

/-- The space components of the Gram four-vector: the covariance, the bracket and half the
difference of the variances. -/
lemma vectorCoeff_gramMatrix :
    vectorCoeff (gramMatrix ω a b) 0 = covariance ω a b ∧
      vectorCoeff (gramMatrix ω a b) 1 = -ω⟨⁅a, b⁆⟩ ∧
      vectorCoeff (gramMatrix ω a b) 2 = (variance ω a - variance ω b) / 2 := by
  have hz := apply_centered_mul_centered ω a b
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [vectorCoeff, pauliCoeff, gramMatrix, hz, pauliMatrix, trace_fin_two,
      mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one,
      empty_val', cons_val_fin_one, Complex.star_def, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    simp only [one_div, one_mul, zero_mul, mul_zero, zero_add, add_zero, selfAdjoint.bracket_def,
      neg_mul, mul_neg, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      sub_self, neg_zero, sub_neg_eq_add, zero_sub]
    ring

/-!

## C. The future cone

-/

/-- **Robertson–Schrödinger is the future cone.** The Gram four-vector of two fluctuations lies
in the closed future cone: `0 ≤ v₀` and `|v⃗| ≤ v₀`. -/
theorem pauliRadius_gramMatrix_le :
    0 ≤ scalarCoeff (gramMatrix ω a b) ∧
      pauliRadius (gramMatrix ω a b) ≤ scalarCoeff (gramMatrix ω a b) := by
  have h0 : 0 ≤ scalarCoeff (gramMatrix ω a b) := by
    rw [scalarCoeff_gramMatrix]
    have := variance_nonneg ω a
    have := variance_nonneg ω b
    positivity
  have hd := det_gramMatrix ω a b
  rw [det_eq_scalarCoeff_sq_sub_pauliRadius_sq, Complex.ofReal_inj] at hd
  refine ⟨h0, (pow_le_pow_iff_left₀ (pauliRadius_nonneg _) h0 two_ne_zero).mp ?_⟩
  linarith [centeredGramDefect_nonneg ω a b]

/-- The Gram four-vector is null exactly when the Robertson–Schrödinger relation is an equality,
that is when the centered Gram defect vanishes. -/
theorem pauliRadius_gramMatrix_eq_iff :
    pauliRadius (gramMatrix ω a b) = scalarCoeff (gramMatrix ω a b) ↔
      centeredGramDefect ω a b = 0 := by
  have hd := det_gramMatrix ω a b
  rw [det_eq_scalarCoeff_sq_sub_pauliRadius_sq, Complex.ofReal_inj] at hd
  have h0 := (pauliRadius_gramMatrix_le ω a b).1
  rw [← hd, sub_eq_zero, pow_left_inj₀ h0 (pauliRadius_nonneg _) two_ne_zero]
  exact eq_comm

/-- `SL(2, ℂ)` keeps the interval of the Gram matrix. -/
lemma det_toSelfAdjointMap_gramMatrix (M : SL(2, ℂ)) :
    ((Lorentz.SL2C.toSelfAdjointMap M) (gramMatrix ω a b)).1.det =
      (centeredGramDefect ω a b : ℂ) := by
  rw [Lorentz.SL2C.toSelfAdjointMap_apply_det, det_gramMatrix]

/-!

## D. The Lorentz vector of two fluctuations

-/

/-- The Gram four-vector of the fluctuations of `a` and `b`, as a contravariant Lorentz vector. -/
noncomputable def gramVector : Lorentz.ContrMod 3 :=
  Lorentz.ContrMod.toSelfAdjoint.symm (gramMatrix ω a b)

/-- **The Minkowski square of the Gram vector is the centered Gram defect**, the slack in the
Robertson–Schrödinger relation. -/
theorem minkowski_gramVector :
    Lorentz.contrContrContractField (gramVector ω a b ⊗ₜ gramVector ω a b) =
      centeredGramDefect ω a b := by
  have h := Lorentz.contrContrContractField.same_eq_det_toSelfAdjoint (gramVector ω a b)
  rw [gramVector, LinearEquiv.apply_symm_apply, det_gramMatrix] at h
  exact_mod_cast h

end UnitalPositiveLinearMap

end ProbabilisticTheory
