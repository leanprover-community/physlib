/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeAlgebra.Basic
public import Physlib.Relativity.PauliMatrices.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Fin
/-!
# The standard basis of the gauge algebra

The standard basis of the gauge algebra of the Standard Model, indexed by
`Fin 8 ⊕ Fin 3 ⊕ Fin 1`: the eight Gell-Mann matrices on the `su(3)` factor, the three
Pauli matrices on the `su(2)` factor, and `1` on the `u(1)` factor.

In this basis the adjoint action of the gauge group is the block-diagonal matrix
`adjointMatrix`, whose blocks are the trace pairings of the basis elements with their
conjugates; `adjoint_stdBasis` and `toMatrix_adjoint` identify its action with the
adjoint action.

-/

@[expose] public section

namespace StandardModel
open Matrix Module PauliMatrix

noncomputable section

/-!

## A. The Gell-Mann matrices

The Pauli matrices `σ1`, `σ2`, `σ3` embedded along the three coordinate planes of
`Fin 3`, together with the normalised traceless diagonal matrix.

-/

/-- The embedding of `2 × 2` matrices into the `3 × 3` matrices supported on the plane
  of two coordinate directions: the entries of `A` land at the row and column indices
  `p 0` and `p 1`, every other entry vanishing. -/
def planeEmbed (p : Fin 2 → Fin 3) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun i j => ∑ a, ∑ b, if i = p a ∧ j = p b then A a b else 0

/-- The Gell-Mann matrices: the standard basis of the traceless hermitian `3 × 3`
  matrices. The first seven are the Pauli matrices `σ1`, `σ2`, `σ3` embedded along the
  three coordinate planes; the eighth is the normalised traceless diagonal matrix. -/
def gellMannMatrix : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ
  | 0 => planeEmbed ![0, 1] σ1
  | 1 => planeEmbed ![0, 1] σ2
  | 2 => planeEmbed ![0, 1] σ3
  | 3 => planeEmbed ![0, 2] σ1
  | 4 => planeEmbed ![0, 2] σ2
  | 5 => planeEmbed ![1, 2] σ1
  | 6 => planeEmbed ![1, 2] σ2
  | 7 => (((Real.sqrt 3 : ℝ) : ℂ))⁻¹ • !![1, 0, 0; 0, 1, 0; 0, 0, -2]

lemma gellMannMatrix_zero : gellMannMatrix 0 = !![0, 1, 0; 1, 0, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gellMannMatrix, planeEmbed, pauliMatrix, Fin.sum_univ_two]

lemma gellMannMatrix_one :
    gellMannMatrix 1 = !![0, -Complex.I, 0; Complex.I, 0, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gellMannMatrix, planeEmbed, pauliMatrix, Fin.sum_univ_two]

lemma gellMannMatrix_two : gellMannMatrix 2 = !![1, 0, 0; 0, -1, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gellMannMatrix, planeEmbed, pauliMatrix, Fin.sum_univ_two]

lemma gellMannMatrix_three : gellMannMatrix 3 = !![0, 0, 1; 0, 0, 0; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gellMannMatrix, planeEmbed, pauliMatrix, Fin.sum_univ_two]

lemma gellMannMatrix_four :
    gellMannMatrix 4 = !![0, 0, -Complex.I; 0, 0, 0; Complex.I, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gellMannMatrix, planeEmbed, pauliMatrix, Fin.sum_univ_two]

lemma gellMannMatrix_five : gellMannMatrix 5 = !![0, 0, 0; 0, 0, 1; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gellMannMatrix, planeEmbed, pauliMatrix, Fin.sum_univ_two]

lemma gellMannMatrix_six :
    gellMannMatrix 6 = !![0, 0, 0; 0, 0, -Complex.I; 0, Complex.I, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gellMannMatrix, planeEmbed, pauliMatrix, Fin.sum_univ_two]

lemma gellMannMatrix_seven :
    gellMannMatrix 7 = (((Real.sqrt 3 : ℝ) : ℂ))⁻¹ • !![1, 0, 0; 0, 1, 0; 0, 0, -2] := rfl

/-- The Gell-Mann matrices are hermitian. -/
lemma gellMannMatrix_selfAdjoint (k : Fin 8) :
    star (gellMannMatrix k) = gellMannMatrix k := by
  fin_cases k <;>
    · rw [Matrix.star_eq_conjTranspose]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [gellMannMatrix_zero, gellMannMatrix_one, gellMannMatrix_two, gellMannMatrix_three,
          gellMannMatrix_four, gellMannMatrix_five, gellMannMatrix_six, gellMannMatrix_seven,
          Matrix.conjTranspose_apply, Complex.conj_ofReal]

/-- The Gell-Mann matrices are traceless. -/
lemma gellMannMatrix_trace (k : Fin 8) : (gellMannMatrix k).trace = 0 := by
  fin_cases k
  all_goals
    simp [gellMannMatrix_zero, gellMannMatrix_one, gellMannMatrix_two, gellMannMatrix_three,
      gellMannMatrix_four, gellMannMatrix_five, gellMannMatrix_six, gellMannMatrix_seven,
      Matrix.trace_fin_three]
  all_goals ring

/-- A combination of the Gell-Mann matrices, entry by entry. -/
lemma sum_smul_gellMannMatrix (g : Fin 8 → ℝ) :
    ∑ k, g k • gellMannMatrix k =
      !![((g 2 + (Real.sqrt 3)⁻¹ * g 7 : ℝ) : ℂ),
          ((g 0 : ℝ) : ℂ) - ((g 1 : ℝ) : ℂ) * Complex.I,
          ((g 3 : ℝ) : ℂ) - ((g 4 : ℝ) : ℂ) * Complex.I;
        ((g 0 : ℝ) : ℂ) + ((g 1 : ℝ) : ℂ) * Complex.I,
          ((-g 2 + (Real.sqrt 3)⁻¹ * g 7 : ℝ) : ℂ),
          ((g 5 : ℝ) : ℂ) - ((g 6 : ℝ) : ℂ) * Complex.I;
        ((g 3 : ℝ) : ℂ) + ((g 4 : ℝ) : ℂ) * Complex.I,
          ((g 5 : ℝ) : ℂ) + ((g 6 : ℝ) : ℂ) * Complex.I,
          ((-2 * (Real.sqrt 3)⁻¹ * g 7 : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Fin.sum_univ_eight, Matrix.sum_apply, gellMannMatrix_zero, gellMannMatrix_one,
      gellMannMatrix_two, gellMannMatrix_three, gellMannMatrix_four, gellMannMatrix_five,
      gellMannMatrix_six, gellMannMatrix_seven, Complex.real_smul]
  all_goals ring

/-- A combination of the three Pauli matrices `σ1`, `σ2`, `σ3`, entry by entry. -/
lemma sum_smul_pauliMatrix_inr (g : Fin 3 → ℝ) :
    ∑ i, g i • pauliMatrix (Sum.inr i) =
      !![((g 2 : ℝ) : ℂ), ((g 0 : ℝ) : ℂ) - ((g 1 : ℝ) : ℂ) * Complex.I;
        ((g 0 : ℝ) : ℂ) + ((g 1 : ℝ) : ℂ) * Complex.I, ((-g 2 : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Fin.sum_univ_three, Matrix.sum_apply, pauliMatrix, Complex.real_smul]
  all_goals ring

/-- The Pauli matrices `σ1`, `σ2`, `σ3` are hermitian, phrased through `star`. -/
lemma pauliMatrix_inr_star (i : Fin 3) :
    star (pauliMatrix (Sum.inr i)) = pauliMatrix (Sum.inr i) := by
  rw [Matrix.star_eq_conjTranspose]
  exact pauliMatrix_selfAdjoint _

/-- The Pauli matrices `σ1`, `σ2`, `σ3` are traceless. -/
lemma pauliMatrix_inr_trace (i : Fin 3) : (pauliMatrix (Sum.inr i)).trace = 0 := by
  fin_cases i <;> simp [pauliMatrix, Matrix.trace_fin_two]

/-!

## B. Coordinates in the Gell-Mann and Pauli bases

The coordinates of a traceless hermitian matrix in the Gell-Mann and Pauli bases, read
off from its entries; they coincide with the trace pairings
`2⁻¹ * (trace (T k * M)).re` with the basis matrices.

-/

/-- The entries of a hermitian matrix are conjugate-symmetric. -/
lemma entry_symm_of_star_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hsa : star M = M)
    (i j : Fin n) : M j i = (starRingEnd ℂ) (M i j) := by
  conv_lhs => rw [← hsa]
  rw [Matrix.star_apply]
  rfl

/-- The diagonal entries of a hermitian matrix are real. -/
lemma diag_re_of_star_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hsa : star M = M)
    (i : Fin n) : M i i = ((M i i).re : ℂ) :=
  (Complex.conj_eq_iff_re.mp (entry_symm_of_star_eq hsa i i).symm).symm

/-- The coordinates of a matrix in the Gell-Mann basis, read off from its entries. -/
def gellMannCoeff (M : Matrix (Fin 3) (Fin 3) ℂ) : Fin 8 → ℝ
  | 0 => (M 0 1).re
  | 1 => -(M 0 1).im
  | 2 => ((M 0 0).re - (M 1 1).re) / 2
  | 3 => (M 0 2).re
  | 4 => -(M 0 2).im
  | 5 => (M 1 2).re
  | 6 => -(M 1 2).im
  | 7 => Real.sqrt 3 / 2 * ((M 0 0).re + (M 1 1).re)

/-- The coordinates of a matrix in the Pauli basis `σ1`, `σ2`, `σ3`, read off from its
  entries. -/
def pauliCoeff (M : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℝ
  | 0 => (M 0 1).re
  | 1 => -(M 0 1).im
  | 2 => (M 0 0).re

/-- A traceless hermitian `3 × 3` matrix is the combination of the Gell-Mann matrices
  with its `gellMannCoeff` coordinates. -/
lemma eq_sum_gellMannCoeff_smul {M : Matrix (Fin 3) (Fin 3) ℂ}
    (hsa : star M = M) (htr : M.trace = 0) :
    M = ∑ k, gellMannCoeff M k • gellMannMatrix k := by
  have hherm := entry_symm_of_star_eq hsa
  have hdiag := diag_re_of_star_eq hsa
  have htr3 : M 2 2 = -(M 0 0 + M 1 1) := by
    rw [Matrix.trace_fin_three] at htr
    linear_combination htr
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rw [sum_smul_gellMannMatrix]
  simp only [gellMannCoeff]
  generalize hgen : Real.sqrt 3 = s at hs ⊢
  have hsc : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  ext i j
  match i, j with
  | 0, 0 =>
    conv_lhs => rw [hdiag 0]
    simp
    field_simp
    ring
  | 0, 1 => simp
  | 0, 2 => simp
  | 1, 0 =>
    conv_lhs => rw [hherm 0 1]
    simp
    apply Complex.ext <;> simp
  | 1, 1 =>
    conv_lhs => rw [hdiag 1]
    simp
    field_simp
    ring
  | 1, 2 => simp
  | 2, 0 =>
    conv_lhs => rw [hherm 0 2]
    simp
    apply Complex.ext <;> simp
  | 2, 1 =>
    conv_lhs => rw [hherm 1 2]
    simp
    apply Complex.ext <;> simp
  | 2, 2 =>
    conv_lhs => rw [htr3]
    conv_lhs => rw [hdiag 0]
    conv_lhs => rw [hdiag 1]
    simp
    field_simp
    ring

/-- A traceless hermitian `2 × 2` matrix is the combination of the Pauli matrices
  `σ1`, `σ2`, `σ3` with its `pauliCoeff` coordinates. -/
lemma eq_sum_pauliCoeff_smul {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hsa : star M = M) (htr : M.trace = 0) :
    M = ∑ i, pauliCoeff M i • pauliMatrix (Sum.inr i) := by
  have hherm := entry_symm_of_star_eq hsa
  have hdiag := diag_re_of_star_eq hsa
  have htr2 : M 1 1 = -M 0 0 := by
    rw [Matrix.trace_fin_two] at htr
    linear_combination htr
  rw [sum_smul_pauliMatrix_inr]
  simp only [pauliCoeff]
  ext i j
  match i, j with
  | 0, 0 =>
    conv_lhs => rw [hdiag 0]
    simp
  | 0, 1 => simp
  | 1, 0 =>
    conv_lhs => rw [hherm 0 1]
    simp
    apply Complex.ext <;> simp
  | 1, 1 =>
    conv_lhs => rw [htr2]
    conv_lhs => rw [hdiag 0]
    simp

/-- The Gell-Mann coordinates of a traceless hermitian matrix are its trace pairings
  with the Gell-Mann matrices. -/
lemma gellMannCoeff_eq_trace {M : Matrix (Fin 3) (Fin 3) ℂ}
    (hsa : star M = M) (htr : M.trace = 0) (k : Fin 8) :
    gellMannCoeff M k = 2⁻¹ * (Matrix.trace (gellMannMatrix k * M)).re := by
  have hherm := entry_symm_of_star_eq hsa
  have hdiag := diag_re_of_star_eq hsa
  have htr3 : M 2 2 = -(M 0 0 + M 1 1) := by
    rw [Matrix.trace_fin_three] at htr
    linear_combination htr
  match k with
  | 0 =>
    rw [gellMannMatrix_zero]
    simp only [gellMannCoeff]
    rw [Matrix.trace_fin_three, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp [Fin.sum_univ_three, hherm 0 1]
    ring
  | 1 =>
    rw [gellMannMatrix_one]
    simp only [gellMannCoeff]
    rw [Matrix.trace_fin_three, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp [Fin.sum_univ_three, hherm 0 1]
    ring
  | 2 =>
    rw [gellMannMatrix_two]
    simp only [gellMannCoeff]
    rw [Matrix.trace_fin_three, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp [Fin.sum_univ_three]
    ring
  | 3 =>
    rw [gellMannMatrix_three]
    simp only [gellMannCoeff]
    rw [Matrix.trace_fin_three, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp [Fin.sum_univ_three, hherm 0 2]
    ring
  | 4 =>
    rw [gellMannMatrix_four]
    simp only [gellMannCoeff]
    rw [Matrix.trace_fin_three, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp [Fin.sum_univ_three, hherm 0 2]
    ring
  | 5 =>
    rw [gellMannMatrix_five]
    simp only [gellMannCoeff]
    rw [Matrix.trace_fin_three, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp [Fin.sum_univ_three, hherm 1 2]
    ring
  | 6 =>
    rw [gellMannMatrix_six]
    simp only [gellMannCoeff]
    rw [Matrix.trace_fin_three, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp [Fin.sum_univ_three, hherm 1 2]
    ring
  | 7 =>
    have h33 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    rw [gellMannMatrix_seven]
    simp only [gellMannCoeff]
    rw [Matrix.smul_mul, Matrix.trace_smul]
    rw [show Matrix.trace (!![1, 0, 0; 0, 1, 0; 0, 0, -2] * M)
        = M 0 0 + M 1 1 - 2 * M 2 2 by
      rw [Matrix.trace_fin_three, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
      simp [Fin.sum_univ_three]
      ring]
    rw [htr3, hdiag 0, hdiag 1]
    rw [show (((Real.sqrt 3 : ℝ) : ℂ))⁻¹ = (((Real.sqrt 3)⁻¹ : ℝ) : ℂ) by push_cast; ring]
    rw [smul_eq_mul, Complex.re_ofReal_mul]
    simp
    field_simp
    linear_combination ((M 0 0).re + (M 1 1).re) * h33

/-- The Pauli coordinates of a traceless hermitian matrix are its trace pairings with
  the Pauli matrices `σ1`, `σ2`, `σ3`. -/
lemma pauliCoeff_eq_trace {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hsa : star M = M) (htr : M.trace = 0) (i : Fin 3) :
    pauliCoeff M i = 2⁻¹ * (Matrix.trace (pauliMatrix (Sum.inr i) * M)).re := by
  have hherm := entry_symm_of_star_eq hsa
  have htr2 : M 1 1 = -M 0 0 := by
    rw [Matrix.trace_fin_two] at htr
    linear_combination htr
  match i with
  | 0 =>
    simp only [pauliCoeff]
    rw [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply]
    simp [Fin.sum_univ_two, pauliMatrix, hherm 0 1]
    ring
  | 1 =>
    simp only [pauliCoeff]
    rw [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply]
    simp [Fin.sum_univ_two, pauliMatrix, hherm 0 1]
    ring
  | 2 =>
    simp only [pauliCoeff]
    rw [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply]
    simp [Fin.sum_univ_two, pauliMatrix, htr2]
    ring

namespace GaugeAlgebra

/-!

## C. The Gell-Mann basis of the su(3) factor

-/

/-- The Gell-Mann matrices as elements of the `su(3)` factor of the gauge algebra. -/
def gellMannSU3 (k : Fin 8) :
    ↥(selfAdjoint.submodule ℝ (Matrix (Fin 3) (Fin 3) ℂ) ⊓
      LinearMap.ker (Matrix.traceLinearMap (Fin 3) ℝ ℂ)) :=
  ⟨gellMannMatrix k, gellMannMatrix_selfAdjoint k, gellMannMatrix_trace k⟩

@[simp]
lemma coe_gellMannSU3 (k : Fin 8) :
    (gellMannSU3 k : Matrix (Fin 3) (Fin 3) ℂ) = gellMannMatrix k := rfl

/-- The Gell-Mann matrices are linearly independent. -/
lemma gellMannSU3_linearIndependent : LinearIndependent ℝ gellMannSU3 := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg
  have hM : ∑ k, g k • gellMannMatrix k = (0 : Matrix (Fin 3) (Fin 3) ℂ) := by
    simpa [gellMannSU3] using congrArg Subtype.val hg
  rw [sum_smul_gellMannMatrix] at hM
  have h00 := congrFun (congrFun hM 0) 0
  have h11 := congrFun (congrFun hM 1) 1
  have h01 := congrFun (congrFun hM 0) 1
  have h02 := congrFun (congrFun hM 0) 2
  have h12 := congrFun (congrFun hM 1) 2
  simp [Complex.ext_iff] at h00 h11 h01 h02 h12
  obtain ⟨h0, h1⟩ := h01
  obtain ⟨h3, h4⟩ := h02
  obtain ⟨h5, h6⟩ := h12
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have h2 : g 2 = 0 := by linarith
  have hx : Real.sqrt 3 * g 7 = 0 := by linarith
  have h7 : g 7 = 0 := (mul_eq_zero.mp hx).resolve_left hs
  intro k
  fin_cases k <;> assumption

/-- The Gell-Mann matrices span the `su(3)` factor. -/
lemma gellMannSU3_span : ⊤ ≤ Submodule.span ℝ (Set.range gellMannSU3) := by
  refine (Submodule.top_le_span_range_iff_forall_exists_fun ℝ).mpr fun A => ?_
  refine ⟨gellMannCoeff (A : Matrix (Fin 3) (Fin 3) ℂ), Subtype.ext ?_⟩
  rw [AddSubmonoidClass.coe_finsetSum]
  simp only [SetLike.val_smul, coe_gellMannSU3]
  exact (eq_sum_gellMannCoeff_smul A.2.1 A.2.2).symm

/-- The Gell-Mann basis of the `su(3)` factor of the gauge algebra. -/
def su3Basis : Basis (Fin 8) ℝ
    ↥(selfAdjoint.submodule ℝ (Matrix (Fin 3) (Fin 3) ℂ) ⊓
      LinearMap.ker (Matrix.traceLinearMap (Fin 3) ℝ ℂ)) :=
  Basis.mk gellMannSU3_linearIndependent gellMannSU3_span

@[simp]
lemma su3Basis_apply (k : Fin 8) : su3Basis k = gellMannSU3 k := by
  rw [su3Basis, Basis.mk_apply]

/-!

## D. The Pauli basis of the su(2) factor

-/

/-- The Pauli matrices `σ1`, `σ2`, `σ3` as elements of the `su(2)` factor of the gauge
  algebra. -/
def pauliSU2 (i : Fin 3) :
    ↥(selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ) ⊓
      LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℝ ℂ)) :=
  ⟨pauliMatrix (Sum.inr i), pauliMatrix_inr_star i, pauliMatrix_inr_trace i⟩

@[simp]
lemma coe_pauliSU2 (i : Fin 3) :
    (pauliSU2 i : Matrix (Fin 2) (Fin 2) ℂ) = pauliMatrix (Sum.inr i) := rfl

/-- The Pauli matrices `σ1`, `σ2`, `σ3` are linearly independent. -/
lemma pauliSU2_linearIndependent : LinearIndependent ℝ pauliSU2 := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg
  have hM : ∑ i, g i • pauliMatrix (Sum.inr i) = (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
    simpa [pauliSU2] using congrArg Subtype.val hg
  rw [sum_smul_pauliMatrix_inr] at hM
  have h00 := congrFun (congrFun hM 0) 0
  have h01 := congrFun (congrFun hM 0) 1
  simp [Complex.ext_iff] at h00 h01
  obtain ⟨h0, h1⟩ := h01
  intro i
  fin_cases i <;> assumption

/-- The Pauli matrices `σ1`, `σ2`, `σ3` span the `su(2)` factor. -/
lemma pauliSU2_span : ⊤ ≤ Submodule.span ℝ (Set.range pauliSU2) := by
  refine (Submodule.top_le_span_range_iff_forall_exists_fun ℝ).mpr fun A => ?_
  refine ⟨pauliCoeff (A : Matrix (Fin 2) (Fin 2) ℂ), Subtype.ext ?_⟩
  rw [AddSubmonoidClass.coe_finsetSum]
  simp only [SetLike.val_smul, coe_pauliSU2]
  exact (eq_sum_pauliCoeff_smul A.2.1 A.2.2).symm

/-- The Pauli basis of the `su(2)` factor of the gauge algebra. -/
def su2Basis : Basis (Fin 3) ℝ
    ↥(selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ) ⊓
      LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℝ ℂ)) :=
  Basis.mk pauliSU2_linearIndependent pauliSU2_span

@[simp]
lemma su2Basis_apply (i : Fin 3) : su2Basis i = pauliSU2 i := by
  rw [su2Basis, Basis.mk_apply]

/-!

## E. The basis of the u(1) factor

-/

/-- The unit `1` as the single basis element of the `u(1)` factor of the gauge
  algebra. -/
def u1One (_ : Fin 1) : selfAdjoint ℂ := 1

@[simp]
lemma coe_u1One (i : Fin 1) : (u1One i : ℂ) = 1 := rfl

/-- The unit is linearly independent. -/
lemma u1One_linearIndependent : LinearIndependent ℝ u1One := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg
  have h : g 0 = 0 := by
    simpa [u1One] using congrArg Subtype.val hg
  intro i
  rw [Subsingleton.elim i 0]
  exact h

/-- The unit spans the `u(1)` factor. -/
lemma u1One_span : ⊤ ≤ Submodule.span ℝ (Set.range u1One) := by
  refine (Submodule.top_le_span_range_iff_forall_exists_fun ℝ).mpr fun z => ?_
  refine ⟨fun _ => (z : ℂ).re, Subtype.ext ?_⟩
  have hz : (z : ℂ).im = 0 := Complex.conj_eq_iff_im.mp z.2
  simp [u1One, Complex.ext_iff, hz]

/-- The basis of the `u(1)` factor of the gauge algebra. -/
def u1Basis : Basis (Fin 1) ℝ (selfAdjoint ℂ) :=
  Basis.mk u1One_linearIndependent u1One_span

@[simp]
lemma u1Basis_apply (i : Fin 1) : u1Basis i = 1 := by
  rw [u1Basis, Basis.mk_apply, u1One]

/-!

## F. The standard basis of the gauge algebra

-/

/-- The standard basis of the gauge algebra, indexed by `Fin 8 ⊕ Fin 3 ⊕ Fin 1`: the
  eight Gell-Mann matrices on the `su(3)` factor, the three Pauli matrices `σ1`, `σ2`,
  `σ3` on the `su(2)` factor, and `1` on the `u(1)` factor. -/
def stdBasis : Basis (Fin 8 ⊕ Fin 3 ⊕ Fin 1) ℝ GaugeAlgebra :=
  su3Basis.prod (su2Basis.prod u1Basis)

@[simp]
lemma stdBasis_inl_toSU3Matrix (k : Fin 8) :
    (stdBasis (Sum.inl k)).toSU3Matrix = gellMannMatrix k := by
  simp only [stdBasis, toSU3Matrix, Basis.prod_apply_inl_fst, su3Basis_apply, coe_gellMannSU3]

@[simp]
lemma stdBasis_inl_toSU2Matrix (k : Fin 8) :
    (stdBasis (Sum.inl k)).toSU2Matrix = 0 := by
  simp only [stdBasis, toSU2Matrix, Basis.prod_apply_inl_snd, Prod.fst_zero,
    ZeroMemClass.coe_zero]

@[simp]
lemma stdBasis_inl_toU1Value (k : Fin 8) :
    (stdBasis (Sum.inl k)).toU1Value = 0 := by
  simp only [stdBasis, toU1Value, Basis.prod_apply_inl_snd, Prod.snd_zero,
    ZeroMemClass.coe_zero]

@[simp]
lemma stdBasis_inr_inl_toSU3Matrix (i : Fin 3) :
    (stdBasis (Sum.inr (Sum.inl i))).toSU3Matrix = 0 := by
  simp only [stdBasis, toSU3Matrix, Basis.prod_apply_inr_fst, ZeroMemClass.coe_zero]

@[simp]
lemma stdBasis_inr_inl_toSU2Matrix (i : Fin 3) :
    (stdBasis (Sum.inr (Sum.inl i))).toSU2Matrix = pauliMatrix (Sum.inr i) := by
  simp only [stdBasis, toSU2Matrix, Basis.prod_apply_inr_snd, Basis.prod_apply_inl_fst,
    su2Basis_apply, coe_pauliSU2]

@[simp]
lemma stdBasis_inr_inl_toU1Value (i : Fin 3) :
    (stdBasis (Sum.inr (Sum.inl i))).toU1Value = 0 := by
  simp only [stdBasis, toU1Value, Basis.prod_apply_inr_snd, Basis.prod_apply_inl_snd,
    ZeroMemClass.coe_zero]

@[simp]
lemma stdBasis_inr_inr_toSU3Matrix (i : Fin 1) :
    (stdBasis (Sum.inr (Sum.inr i))).toSU3Matrix = 0 := by
  simp only [stdBasis, toSU3Matrix, Basis.prod_apply_inr_fst, ZeroMemClass.coe_zero]

@[simp]
lemma stdBasis_inr_inr_toSU2Matrix (i : Fin 1) :
    (stdBasis (Sum.inr (Sum.inr i))).toSU2Matrix = 0 := by
  simp only [stdBasis, toSU2Matrix, Basis.prod_apply_inr_snd, Basis.prod_apply_inr_fst,
    ZeroMemClass.coe_zero]

@[simp]
lemma stdBasis_inr_inr_toU1Value (i : Fin 1) :
    (stdBasis (Sum.inr (Sum.inr i))).toU1Value = 1 := by
  simp only [stdBasis, toU1Value, Basis.prod_apply_inr_snd, u1Basis_apply,
    selfAdjoint.val_one]

/-!

## G. The adjoint action in the standard basis

In the standard basis the adjoint action of a gauge group element is the block-diagonal
matrix `adjointMatrix`: the `su(3)` and `su(2)` blocks pair the basis elements with
their conjugates through the trace, and the `u(1)` entry is `1`.

-/

lemma toSU3Matrix_sum {ι : Type*} (s : Finset ι) (f : ι → GaugeAlgebra) :
    (∑ x ∈ s, f x).toSU3Matrix = ∑ x ∈ s, (f x).toSU3Matrix := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, add_toSU3Matrix, ih]

lemma toSU2Matrix_sum {ι : Type*} (s : Finset ι) (f : ι → GaugeAlgebra) :
    (∑ x ∈ s, f x).toSU2Matrix = ∑ x ∈ s, (f x).toSU2Matrix := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, add_toSU2Matrix, ih]

lemma toU1Value_sum {ι : Type*} (s : Finset ι) (f : ι → GaugeAlgebra) :
    (∑ x ∈ s, f x).toU1Value = ∑ x ∈ s, (f x).toU1Value := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, add_toU1Value, ih]

/-- The matrix of the adjoint action of a gauge group element in the standard basis:
  block diagonal, with the `su(3)` and `su(2)` blocks the trace pairings
  `2⁻¹ * (trace (T a * g T b g⁻¹)).re` of the basis elements with the conjugated basis
  elements, `1` on the `u(1)` entry, and `0` between different factors. -/
noncomputable def adjointMatrix (g : GaugeGroupI) :
    Matrix (Fin 8 ⊕ Fin 3 ⊕ Fin 1) (Fin 8 ⊕ Fin 3 ⊕ Fin 1) ℝ :=
  Matrix.of fun a b =>
    match a, b with
    | Sum.inl a, Sum.inl b =>
        2⁻¹ * (Matrix.trace (gellMannMatrix a *
          (g.toSU3.1 * gellMannMatrix b * star g.toSU3.1))).re
    | Sum.inr (Sum.inl i), Sum.inr (Sum.inl j) =>
        2⁻¹ * (Matrix.trace (pauliMatrix (Sum.inr i) *
          (g.toSU2.1 * pauliMatrix (Sum.inr j) * star g.toSU2.1))).re
    | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => 1
    | _, _ => 0

@[simp]
lemma adjointMatrix_inl_inl (g : GaugeGroupI) (a b : Fin 8) :
    adjointMatrix g (Sum.inl a) (Sum.inl b)
      = 2⁻¹ * (Matrix.trace (gellMannMatrix a *
          (g.toSU3.1 * gellMannMatrix b * star g.toSU3.1))).re := rfl

@[simp]
lemma adjointMatrix_inl_inr (g : GaugeGroupI) (a : Fin 8) (x : Fin 3 ⊕ Fin 1) :
    adjointMatrix g (Sum.inl a) (Sum.inr x) = 0 := by
  cases x <;> rfl

@[simp]
lemma adjointMatrix_inr_inl (g : GaugeGroupI) (x : Fin 3 ⊕ Fin 1) (b : Fin 8) :
    adjointMatrix g (Sum.inr x) (Sum.inl b) = 0 := by
  cases x <;> rfl

@[simp]
lemma adjointMatrix_inr_inl_inr_inl (g : GaugeGroupI) (i j : Fin 3) :
    adjointMatrix g (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j))
      = 2⁻¹ * (Matrix.trace (pauliMatrix (Sum.inr i) *
          (g.toSU2.1 * pauliMatrix (Sum.inr j) * star g.toSU2.1))).re := rfl

@[simp]
lemma adjointMatrix_inr_inl_inr_inr (g : GaugeGroupI) (i : Fin 3) (u : Fin 1) :
    adjointMatrix g (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr u)) = 0 := rfl

@[simp]
lemma adjointMatrix_inr_inr_inr_inl (g : GaugeGroupI) (u : Fin 1) (j : Fin 3) :
    adjointMatrix g (Sum.inr (Sum.inr u)) (Sum.inr (Sum.inl j)) = 0 := rfl

@[simp]
lemma adjointMatrix_inr_inr_inr_inr (g : GaugeGroupI) (u v : Fin 1) :
    adjointMatrix g (Sum.inr (Sum.inr u)) (Sum.inr (Sum.inr v)) = 1 := rfl

/-- The adjoint action of the gauge group acts on the standard basis through
  `adjointMatrix`. -/
lemma adjoint_stdBasis (g : GaugeGroupI) (b : Fin 8 ⊕ Fin 3 ⊕ Fin 1) :
    adjoint g (stdBasis b) = ∑ a, adjointMatrix g a b • stdBasis a := by
  match b with
  | Sum.inl k =>
    have hmem := conj_mem g.toSU3.2.1 (gellMannMatrix_selfAdjoint k) (gellMannMatrix_trace k)
    refine ext_of_matrix ?_ ?_ ?_
    · rw [adjoint_toSU3Matrix, stdBasis_inl_toSU3Matrix, toSU3Matrix_sum]
      simp only [smul_toSU3Matrix, Fintype.sum_sum_type, stdBasis_inl_toSU3Matrix,
        stdBasis_inr_inl_toSU3Matrix, stdBasis_inr_inr_toSU3Matrix, smul_zero,
        Finset.sum_const_zero, add_zero, adjointMatrix_inl_inl]
      conv_lhs => rw [eq_sum_gellMannCoeff_smul hmem.1 hmem.2]
      exact Finset.sum_congr rfl fun a _ => by
        rw [gellMannCoeff_eq_trace hmem.1 hmem.2]
    · rw [adjoint_toSU2Matrix, stdBasis_inl_toSU2Matrix, toSU2Matrix_sum]
      simp [Fintype.sum_sum_type]
    · rw [adjoint_toU1Value, stdBasis_inl_toU1Value, toU1Value_sum]
      simp [Fintype.sum_sum_type]
  | Sum.inr (Sum.inl j) =>
    have hmem := conj_mem g.toSU2.2.1 (pauliMatrix_inr_star j) (pauliMatrix_inr_trace j)
    refine ext_of_matrix ?_ ?_ ?_
    · rw [adjoint_toSU3Matrix, stdBasis_inr_inl_toSU3Matrix, toSU3Matrix_sum]
      simp [Fintype.sum_sum_type]
    · rw [adjoint_toSU2Matrix, stdBasis_inr_inl_toSU2Matrix, toSU2Matrix_sum]
      simp only [smul_toSU2Matrix, Fintype.sum_sum_type, stdBasis_inl_toSU2Matrix,
        stdBasis_inr_inl_toSU2Matrix, stdBasis_inr_inr_toSU2Matrix, smul_zero,
        Finset.sum_const_zero, zero_add, add_zero, adjointMatrix_inr_inl_inr_inl]
      conv_lhs => rw [eq_sum_pauliCoeff_smul hmem.1 hmem.2]
      exact Finset.sum_congr rfl fun i _ => by
        rw [pauliCoeff_eq_trace hmem.1 hmem.2]
    · rw [adjoint_toU1Value, stdBasis_inr_inl_toU1Value, toU1Value_sum]
      simp [Fintype.sum_sum_type]
  | Sum.inr (Sum.inr u) =>
    refine ext_of_matrix ?_ ?_ ?_
    · rw [adjoint_toSU3Matrix, stdBasis_inr_inr_toSU3Matrix, toSU3Matrix_sum]
      simp [Fintype.sum_sum_type]
    · rw [adjoint_toSU2Matrix, stdBasis_inr_inr_toSU2Matrix, toSU2Matrix_sum]
      simp [Fintype.sum_sum_type]
    · rw [adjoint_toU1Value, stdBasis_inr_inr_toU1Value, toU1Value_sum]
      simp [Fintype.sum_sum_type]

/-- The matrix of the adjoint action in the standard basis is `adjointMatrix`. -/
lemma toMatrix_adjoint (g : GaugeGroupI) :
    LinearMap.toMatrix stdBasis stdBasis (adjoint g) = adjointMatrix g := by
  ext a b
  rw [LinearMap.toMatrix_apply, adjoint_stdBasis g b]
  exact congrFun (stdBasis.repr_sum_self _) a

/-- The action of `adjointMatrix` on coordinates in the standard basis corresponds to
  the adjoint action of the gauge group on the gauge algebra. -/
lemma adjointMatrix_mulVec_repr (g : GaugeGroupI) (a : GaugeAlgebra) :
    (adjointMatrix g).mulVec (stdBasis.repr a) = ⇑(stdBasis.repr (adjoint g a)) := by
  rw [← toMatrix_adjoint]
  exact LinearMap.toMatrix_mulVec_repr stdBasis stdBasis (adjoint g) a

/-- The dual adjoint action on the dual standard basis: the coordinate functions
  transform through the rows of `adjointMatrix`. -/
lemma adjoint_dualMap_coord (g : GaugeGroupI) (a : Fin 8 ⊕ Fin 3 ⊕ Fin 1) :
    (adjoint g).dualMap (stdBasis.coord a)
      = ∑ b, adjointMatrix g a b • stdBasis.coord b := by
  refine LinearMap.ext fun x => ?_
  have h := congrFun (adjointMatrix_mulVec_repr g x) a
  simp only [LinearMap.dualMap_apply, Basis.coord_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [← h]
  simp [Matrix.mulVec, dotProduct]

/-!

## H. Orthogonality of the adjoint matrix

The adjoint action preserves the trace pairing of the standard basis, so `adjointMatrix`
is an orthogonal matrix. Multiplicativity turns the star of a group element into the
transpose of its matrix, and the two combine to the orthogonality relation.

-/

/-- The matrix of the adjoint action turns a product in the gauge group into the
  product of the corresponding matrices. -/
lemma adjointMatrix_mul (g h : GaugeGroupI) :
    GaugeAlgebra.adjointMatrix (g * h)
      = GaugeAlgebra.adjointMatrix g * GaugeAlgebra.adjointMatrix h := by
  rw [← GaugeAlgebra.toMatrix_adjoint, ← GaugeAlgebra.toMatrix_adjoint,
    ← GaugeAlgebra.toMatrix_adjoint, map_mul, LinearMap.toMatrix_mul]

/-- The matrix of the adjoint action of the identity is the identity matrix. -/
lemma adjointMatrix_one : GaugeAlgebra.adjointMatrix (1 : GaugeGroupI) = 1 := by
  rw [← GaugeAlgebra.toMatrix_adjoint, map_one, LinearMap.toMatrix_one]

/-- The star of a gauge group element is its inverse. -/
lemma gaugeGroup_mul_star_self (g : GaugeGroupI) : g * star g = 1 := by
  refine GaugeGroupI.ext ?_ ?_ ?_
  · rw [map_mul, GaugeGroupI.star_toSU3, map_one, Matrix.star_eq_inv, mul_inv_cancel]
  · rw [map_mul, GaugeGroupI.star_toSU2, map_one, Matrix.star_eq_inv, mul_inv_cancel]
  · rw [map_mul, GaugeGroupI.star_toU1, map_one, Unitary.mul_star_self]

/-- The matrix of the adjoint action of the star of a gauge group element is the
  transpose of the matrix of the adjoint action, since the trace pairing is symmetric
  under moving the conjugation from one argument to the other. -/
lemma adjointMatrix_star (g : GaugeGroupI) :
    GaugeAlgebra.adjointMatrix (star g) = (GaugeAlgebra.adjointMatrix g)ᵀ := by
  have key : ∀ {m : ℕ} (X Y U : Matrix (Fin m) (Fin m) ℂ),
      Matrix.trace (X * (star U * Y * U)) = Matrix.trace (Y * (U * X * star U)) := by
    intro m X Y U
    calc Matrix.trace (X * (star U * Y * U))
        = Matrix.trace (X * star U * Y * U) := by simp only [mul_assoc]
      _ = Matrix.trace (U * (X * star U * Y)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (U * X * star U * Y) := by simp only [mul_assoc]
      _ = Matrix.trace (Y * (U * X * star U)) := Matrix.trace_mul_comm _ _
  ext a b
  match a, b with
  | Sum.inl a, Sum.inl b =>
    simp only [Matrix.transpose_apply, GaugeAlgebra.adjointMatrix_inl_inl,
      GaugeGroupI.star_toSU3, Matrix.specialUnitaryGroup.coe_star, star_star]
    rw [key]
  | Sum.inl a, Sum.inr x => simp
  | Sum.inr x, Sum.inl b => simp
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inl j) =>
    simp only [Matrix.transpose_apply, GaugeAlgebra.adjointMatrix_inr_inl_inr_inl,
      GaugeGroupI.star_toSU2, Matrix.specialUnitaryGroup.coe_star, star_star]
    rw [key]
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inr u) => simp
  | Sum.inr (Sum.inr u), Sum.inr (Sum.inl j) => simp
  | Sum.inr (Sum.inr u), Sum.inr (Sum.inr v) => simp

/-- The matrix of the adjoint action is orthogonal. -/
lemma adjointMatrix_mul_transpose (g : GaugeGroupI) :
    GaugeAlgebra.adjointMatrix g * (GaugeAlgebra.adjointMatrix g)ᵀ = 1 := by
  rw [← adjointMatrix_star, ← adjointMatrix_mul, gaugeGroup_mul_star_self,
    adjointMatrix_one]

/-- The rows of the `su(3)` block of the adjoint matrix are orthonormal. The matrix is
  block diagonal, so orthogonality of the whole matrix restricts to each block. -/
lemma sum_adjointMatrix_inl_row_mul (g : GaugeGroupI) (c d : Fin 8) :
    ∑ a : Fin 8, adjointMatrix g (Sum.inl c) (Sum.inl a) *
      adjointMatrix g (Sum.inl d) (Sum.inl a) = if c = d then 1 else 0 := by
  have h : (adjointMatrix g * (adjointMatrix g)ᵀ) (Sum.inl c) (Sum.inl d)
      = (1 : Matrix (Fin 8 ⊕ Fin 3 ⊕ Fin 1) (Fin 8 ⊕ Fin 3 ⊕ Fin 1) ℝ)
        (Sum.inl c) (Sum.inl d) := by
    rw [adjointMatrix_mul_transpose]
  rw [Matrix.mul_apply, Fintype.sum_sum_type] at h
  simpa [Fintype.sum_sum_type, Matrix.one_apply] using h

/-- The rows of the `su(2)` block of the adjoint matrix are orthonormal. -/
lemma sum_adjointMatrix_inr_inl_row_mul (g : GaugeGroupI) (c d : Fin 3) :
    ∑ a : Fin 3, adjointMatrix g (Sum.inr (Sum.inl c)) (Sum.inr (Sum.inl a)) *
      adjointMatrix g (Sum.inr (Sum.inl d)) (Sum.inr (Sum.inl a))
      = if c = d then 1 else 0 := by
  have h : (adjointMatrix g * (adjointMatrix g)ᵀ)
      (Sum.inr (Sum.inl c)) (Sum.inr (Sum.inl d))
      = (1 : Matrix (Fin 8 ⊕ Fin 3 ⊕ Fin 1) (Fin 8 ⊕ Fin 3 ⊕ Fin 1) ℝ)
        (Sum.inr (Sum.inl c)) (Sum.inr (Sum.inl d)) := by
    rw [adjointMatrix_mul_transpose]
  rw [Matrix.mul_apply, Fintype.sum_sum_type] at h
  simpa [Fintype.sum_sum_type, Matrix.one_apply] using h

/-- The matrix of the adjoint action of the inverse of a gauge group element is the
  transpose of the matrix of the adjoint action. -/
lemma adjointMatrix_inv_apply (g : GaugeGroupI) (a b : Fin 8 ⊕ Fin 3 ⊕ Fin 1) :
    adjointMatrix g⁻¹ a b = adjointMatrix g b a := by
  rw [inv_eq_of_mul_eq_one_right (gaugeGroup_mul_star_self g), adjointMatrix_star,
    Matrix.transpose_apply]

end GaugeAlgebra

end

end StandardModel
