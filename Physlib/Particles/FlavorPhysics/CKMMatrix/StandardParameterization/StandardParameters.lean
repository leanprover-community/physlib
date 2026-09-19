/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.FlavorPhysics.CKMMatrix.PhaseFreedom
public import Physlib.Particles.FlavorPhysics.CKMMatrix.StandardParameterization.Basic
/-!
# Standard parameters for the CKM Matrix

Given a CKM matrix `V` we can extract four real numbers `θ₁₂`, `θ₁₃`, `θ₂₃` and `δ₁₃`.
These, when used in the standard parameterization return `V` up to equivalence.

This leads to the theorem `standParam.exists_for_CKMatrix` which says that up to equivalence every
CKM matrix can be written using the standard parameterization.

-/

@[expose] public section

open Matrix Complex
open ComplexConjugate
open CKMMatrix

noncomputable section

/-- Given a CKM matrix `V` the real number corresponding to `sin θ₁₂` in the
standard parameterization. --/
def S₁₂ (V : Quotient CKMMatrixSetoid) : ℝ := VusAbs V / (√ (VudAbs V ^ 2 + VusAbs V ^ 2))

/-- Given a CKM matrix `V` the real number corresponding to `sin θ₁₃` in the
standard parameterization. --/
def S₁₃ (V : Quotient CKMMatrixSetoid) : ℝ := VubAbs V

/-- Given a CKM matrix `V` the real number corresponding to `sin θ₂₃` in the
standard parameterization. --/
def S₂₃ (V : Quotient CKMMatrixSetoid) : ℝ :=
  if VubAbs V = 1 then VcdAbs V
  else VcbAbs V / √ (VudAbs V ^ 2 + VusAbs V ^ 2)

/-- Given a CKM matrix `V` the real number corresponding to `θ₁₂` in the
standard parameterization. --/
def θ₁₂ (V : Quotient CKMMatrixSetoid) : ℝ := Real.arcsin (S₁₂ V)

/-- Given a CKM matrix `V` the real number corresponding to `θ₁₃` in the
standard parameterization. --/
def θ₁₃ (V : Quotient CKMMatrixSetoid) : ℝ := Real.arcsin (S₁₃ V)

/-- Given a CKM matrix `V` the real number corresponding to `θ₂₃` in the
standard parameterization. --/
def θ₂₃ (V : Quotient CKMMatrixSetoid) : ℝ := Real.arcsin (S₂₃ V)

/-- Given a CKM matrix `V` the real number corresponding to `cos θ₁₂` in the
standard parameterization. --/
def C₁₂ (V : Quotient CKMMatrixSetoid) : ℝ := Real.cos (θ₁₂ V)

/-- Given a CKM matrix `V` the real number corresponding to `cos θ₁₃` in the
standard parameterization. --/
def C₁₃ (V : Quotient CKMMatrixSetoid) : ℝ := Real.cos (θ₁₃ V)

/-- Given a CKM matrix `V` the real number corresponding to `sin θ₂₃` in the
standard parameterization. --/
def C₂₃ (V : Quotient CKMMatrixSetoid) : ℝ := Real.cos (θ₂₃ V)

/-- Given a CKM matrix `V` the real number corresponding to the phase `δ₁₃` in the
standard parameterization. --/
def δ₁₃ (V : Quotient CKMMatrixSetoid) : ℝ :=
  arg (Invariant.mulExpδ₁₃ V)

section sines

/-- For a CKM matrix `sin θ₁₂` is non-negative. -/
lemma S₁₂_nonneg (V : Quotient CKMMatrixSetoid) : 0 ≤ S₁₂ V :=
  div_nonneg (VAbs_ge_zero 0 1 V) (Real.sqrt_nonneg _)

/-- For a CKM matrix `sin θ₁₃` is non-negative. -/
lemma S₁₃_nonneg (V : Quotient CKMMatrixSetoid) : 0 ≤ S₁₃ V :=
  VAbs_ge_zero 0 2 V

/-- For a CKM matrix `sin θ₂₃` is non-negative. -/
lemma S₂₃_nonneg (V : Quotient CKMMatrixSetoid) : 0 ≤ S₂₃ V := by
  rw [S₂₃]
  split
  · exact VAbs_ge_zero 1 0 V
  · exact div_nonneg (VAbs_ge_zero 1 2 V) (Real.sqrt_nonneg _)

/-- For a CKM matrix `sin θ₁₂` is less than or equal to 1. -/
lemma S₁₂_leq_one (V : Quotient CKMMatrixSetoid) : S₁₂ V ≤ 1 := by
  rw [S₁₂]
  exact div_le_one_of_le₀ (Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (sq_nonneg _)))
    (Real.sqrt_nonneg _)

/-- For a CKM matrix `sin θ₁₃` is less than or equal to 1. -/
lemma S₁₃_leq_one (V : Quotient CKMMatrixSetoid) : S₁₃ V ≤ 1 :=
  VAbs_leq_one 0 2 V

/-- For a CKM matrix `sin θ₂₃` is less than or equal to 1. -/
lemma S₂₃_leq_one (V : Quotient CKMMatrixSetoid) : S₂₃ V ≤ 1 := by
  rw [S₂₃]
  split
  · exact VAbs_leq_one 1 0 V
  · apply div_le_one_of_le₀ _ (Real.sqrt_nonneg _)
    rw [VudAbs_sq_add_VusAbs_sq, ← VcbAbs_sq_add_VtbAbs_sq]
    exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))

lemma S₁₂_eq_sin_θ₁₂ (V : Quotient CKMMatrixSetoid) : Real.sin (θ₁₂ V) = S₁₂ V :=
  Real.sin_arcsin (le_trans (by simp) (S₁₂_nonneg V)) (S₁₂_leq_one V)

lemma S₁₃_eq_sin_θ₁₃ (V : Quotient CKMMatrixSetoid) : Real.sin (θ₁₃ V) = S₁₃ V :=
  Real.sin_arcsin (le_trans (by simp) (S₁₃_nonneg V)) (S₁₃_leq_one V)

lemma S₂₃_eq_sin_θ₂₃ (V : Quotient CKMMatrixSetoid) : Real.sin (θ₂₃ V) = S₂₃ V :=
  Real.sin_arcsin (le_trans (by simp) (S₂₃_nonneg V)) (S₂₃_leq_one V)

lemma S₁₂_eq_ℂsin_θ₁₂ (V : Quotient CKMMatrixSetoid) : Complex.sin (θ₁₂ V) = S₁₂ V :=
  (ofReal_sin _).symm.trans (congrArg ofReal (S₁₂_eq_sin_θ₁₂ V))

lemma S₁₃_eq_ℂsin_θ₁₃ (V : Quotient CKMMatrixSetoid) : Complex.sin (θ₁₃ V) = S₁₃ V :=
  (ofReal_sin _).symm.trans (congrArg ofReal (S₁₃_eq_sin_θ₁₃ V))

lemma S₂₃_eq_ℂsin_θ₂₃ (V : Quotient CKMMatrixSetoid) : Complex.sin (θ₂₃ V) = S₂₃ V :=
  (ofReal_sin _).symm.trans (congrArg ofReal (S₂₃_eq_sin_θ₂₃ V))

lemma complexAbs_sin_θ₁₂ (V : Quotient CKMMatrixSetoid) :
    norm (Complex.sin (θ₁₂ V)) = sin (θ₁₂ V) := by
  rw [S₁₂_eq_ℂsin_θ₁₂, Complex.norm_real, ofReal_inj]
  exact Real.norm_of_nonneg (S₁₂_nonneg _)

lemma complexAbs_sin_θ₁₃ (V : Quotient CKMMatrixSetoid) :
    norm (Complex.sin (θ₁₃ V)) = sin (θ₁₃ V) := by
  rw [S₁₃_eq_ℂsin_θ₁₃, Complex.norm_real, ofReal_inj]
  exact Real.norm_of_nonneg (S₁₃_nonneg _)

lemma complexAbs_sin_θ₂₃ (V : Quotient CKMMatrixSetoid) :
    norm (Complex.sin (θ₂₃ V)) = sin (θ₂₃ V) := by
  rw [S₂₃_eq_ℂsin_θ₂₃, Complex.norm_real, ofReal_inj]
  exact Real.norm_of_nonneg (S₂₃_nonneg _)

lemma S₁₂_of_Vub_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V = 1) : S₁₂ V = 0 := by
  simp [S₁₂, VudAbs_sq_add_VusAbs_sq, ha]

lemma S₁₃_of_Vub_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V = 1) : S₁₃ V = 1 := ha

lemma S₂₃_of_Vub_eq_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V = 1) : S₂₃ V = VcdAbs V := by
  rw [S₂₃, ite_eq_left ha]

lemma S₂₃_of_Vub_ne_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V ≠ 1) :
    S₂₃ V = VcbAbs V / √ (VudAbs V ^ 2 + VusAbs V ^ 2) := by
  rw [S₂₃, ite_eq_right ha]

end sines

section cosines

lemma C₁₂_eq_ℂcos_θ₁₂ (V : Quotient CKMMatrixSetoid) : Complex.cos (θ₁₂ V) = C₁₂ V := by
  simp [C₁₂]

lemma C₁₃_eq_ℂcos_θ₁₃ (V : Quotient CKMMatrixSetoid) : Complex.cos (θ₁₃ V) = C₁₃ V := by
  simp [C₁₃]

lemma C₂₃_eq_ℂcos_θ₂₃ (V : Quotient CKMMatrixSetoid) : Complex.cos (θ₂₃ V) = C₂₃ V := by
  simp [C₂₃]

lemma complexAbs_cos_θ₁₂ (V : Quotient CKMMatrixSetoid) : norm (Complex.cos (θ₁₂ V)) =
    cos (θ₁₂ V) := by
  rw [C₁₂_eq_ℂcos_θ₁₂, Complex.norm_real]
  exact_mod_cast Real.norm_of_nonneg (Real.cos_arcsin_nonneg _)

lemma complexAbs_cos_θ₁₃ (V : Quotient CKMMatrixSetoid) : norm (Complex.cos (θ₁₃ V)) =
    cos (θ₁₃ V) := by
  rw [C₁₃_eq_ℂcos_θ₁₃, Complex.norm_real]
  exact_mod_cast Real.norm_of_nonneg (Real.cos_arcsin_nonneg _)

lemma complexAbs_cos_θ₂₃ (V : Quotient CKMMatrixSetoid) : norm (Complex.cos (θ₂₃ V)) =
    cos (θ₂₃ V) := by
  rw [C₂₃_eq_ℂcos_θ₂₃, Complex.norm_real]
  exact_mod_cast Real.norm_of_nonneg (Real.cos_arcsin_nonneg _)

lemma S₁₂_sq_add_C₁₂_sq (V : Quotient CKMMatrixSetoid) : S₁₂ V ^ 2 + C₁₂ V ^ 2 = 1 := by
  simp only [← S₁₂_eq_sin_θ₁₂ V, C₁₂, Real.sin_sq_add_cos_sq]

lemma S₁₃_sq_add_C₁₃_sq (V : Quotient CKMMatrixSetoid) : S₁₃ V ^ 2 + C₁₃ V ^ 2 = 1 := by
  simp only [← S₁₃_eq_sin_θ₁₃ V, C₁₃, Real.sin_sq_add_cos_sq]

lemma S₂₃_sq_add_C₂₃_sq (V : Quotient CKMMatrixSetoid) : S₂₃ V ^ 2 + C₂₃ V ^ 2 = 1 := by
  simp only [← S₂₃_eq_sin_θ₂₃ V, C₂₃, Real.sin_sq_add_cos_sq]

lemma C₁₂_of_Vub_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V = 1) : C₁₂ V = 1 := by
  simp [C₁₂, θ₁₂, S₁₂_of_Vub_one ha]

lemma C₁₃_of_Vub_eq_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V = 1) : C₁₃ V = 0 := by
  simp [C₁₃, θ₁₃, S₁₃, ha]

--rename
lemma C₁₂_eq_Vud_div_sqrt {V : Quotient CKMMatrixSetoid} (ha : VubAbs V ≠ 1) :
    C₁₂ V = VudAbs V / √ (VudAbs V ^ 2 + VusAbs V ^ 2) := by
  rw [C₁₂, θ₁₂, Real.cos_arcsin, S₁₂, div_pow, Real.sq_sqrt]
  · rw [one_sub_div]
    · simp only [VudAbs, Fin.isValue, VusAbs, add_sub_cancel_right]
      rw [Real.sqrt_div (sq_nonneg (VAbs 0 0 V)), Real.sqrt_sq (VAbs_ge_zero 0 0 V)]
    exact VAbsub_ne_zero_Vud_Vus_ne_zero ha
  exact (Left.add_nonneg (sq_nonneg (VAbs 0 0 V)) (sq_nonneg (VAbs 0 1 V)))

--rename
lemma C₁₃_eq_add_sq (V : Quotient CKMMatrixSetoid) : C₁₃ V = √ (VudAbs V ^ 2 + VusAbs V ^ 2) := by
  rw [C₁₃, θ₁₃, Real.cos_arcsin, S₁₃, ← VudAbs_sq_add_VusAbs_sq]

lemma C₂₃_of_Vub_ne_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V ≠ 1) :
    C₂₃ V = VtbAbs V / √ (VudAbs V ^ 2 + VusAbs V ^ 2) := by
  rw [C₂₃, θ₂₃, Real.cos_arcsin, S₂₃_of_Vub_ne_one ha, div_pow, Real.sq_sqrt]
  · rw [VudAbs_sq_add_VusAbs_sq, ← VcbAbs_sq_add_VtbAbs_sq]
    rw [one_sub_div]
    · simp only [VcbAbs, Fin.isValue, VtbAbs, add_sub_cancel_left]
      rw [Real.sqrt_div (sq_nonneg (VAbs 2 2 V)), Real.sqrt_sq (VAbs_ge_zero 2 2 V)]
    · rw [VcbAbs_sq_add_VtbAbs_sq, ← VudAbs_sq_add_VusAbs_sq]
      exact VAbsub_ne_zero_Vud_Vus_ne_zero ha
  exact (Left.add_nonneg (sq_nonneg (VAbs 0 0 V)) (sq_nonneg (VAbs 0 1 V)))

end cosines

section VAbs

-- rename to VudAbs_standard_param
lemma VudAbs_eq_C₁₂_mul_C₁₃ (V : Quotient CKMMatrixSetoid) : VudAbs V = C₁₂ V * C₁₃ V := by
  by_cases ha : VubAbs V = 1
  · rw [C₁₃_of_Vub_eq_one ha, mul_zero]
    exact VAbs_thd_eq_one_fst_eq_zero ha
  · rw [C₁₂_eq_Vud_div_sqrt ha, C₁₃, θ₁₃, Real.cos_arcsin, S₁₃, ← VudAbs_sq_add_VusAbs_sq, mul_comm]
    exact (mul_div_cancel₀ (VudAbs V) (VAbsub_ne_zero_sqrt_Vud_Vus_ne_zero ha)).symm

lemma VusAbs_eq_S₁₂_mul_C₁₃ (V : Quotient CKMMatrixSetoid) : VusAbs V = S₁₂ V * C₁₃ V := by
  by_cases ha : VubAbs V = 1
  · rw [C₁₃_of_Vub_eq_one ha, mul_zero]
    exact VAbs_thd_eq_one_snd_eq_zero ha
  · rw [C₁₃, θ₁₃, Real.cos_arcsin, S₁₂, S₁₃, ← VudAbs_sq_add_VusAbs_sq, mul_comm]
    exact (mul_div_cancel₀ (VusAbs V) (VAbsub_ne_zero_sqrt_Vud_Vus_ne_zero ha)).symm

lemma VubAbs_eq_S₁₃ (V : Quotient CKMMatrixSetoid) : VubAbs V = S₁₃ V := rfl

lemma VcbAbs_eq_S₂₃_mul_C₁₃ (V : Quotient CKMMatrixSetoid) : VcbAbs V = S₂₃ V * C₁₃ V := by
  by_cases ha : VubAbs V = 1
  · rw [C₁₃_of_Vub_eq_one ha, mul_zero]
    exact VAbs_fst_col_eq_one_snd_eq_zero ha
  · rw [S₂₃_of_Vub_ne_one ha, C₁₃_eq_add_sq, mul_comm]
    exact (mul_div_cancel₀ (VcbAbs V) (VAbsub_ne_zero_sqrt_Vud_Vus_ne_zero ha)).symm

lemma VtbAbs_eq_C₂₃_mul_C₁₃ (V : Quotient CKMMatrixSetoid) : VtbAbs V = C₂₃ V * C₁₃ V := by
  by_cases ha : VubAbs V = 1
  · rw [C₁₃_of_Vub_eq_one ha, mul_zero]
    exact VAbs_fst_col_eq_one_thd_eq_zero ha
  · rw [C₂₃_of_Vub_ne_one ha, C₁₃_eq_add_sq, mul_comm]
    exact (mul_div_cancel₀ (VtbAbs V) (VAbsub_ne_zero_sqrt_Vud_Vus_ne_zero ha)).symm

lemma VubAbs_of_cos_θ₁₃_zero {V : Quotient CKMMatrixSetoid} (h1 : Real.cos (θ₁₃ V) = 0) :
    VubAbs V = 1 := by
  rw [VubAbs_eq_S₁₃]
  rw [θ₁₃, Real.cos_arcsin, Real.sqrt_eq_zero'] at h1
  refine le_antisymm (S₁₃_leq_one V) ?_
  nlinarith [S₁₃_nonneg V, S₁₃_leq_one V, h1]

lemma Vs_zero_iff_cos_sin_zero (V : CKMMatrix) :
    VudAbs ⟦V⟧ = 0 ∨ VubAbs ⟦V⟧ = 0 ∨ VusAbs ⟦V⟧ = 0 ∨ VcbAbs ⟦V⟧ = 0 ∨ VtbAbs ⟦V⟧ = 0
    ↔ Real.cos (θ₁₂ ⟦V⟧) = 0 ∨ Real.cos (θ₁₃ ⟦V⟧) = 0 ∨ Real.cos (θ₂₃ ⟦V⟧) = 0 ∨
      Real.sin (θ₁₂ ⟦V⟧) = 0 ∨ Real.sin (θ₁₃ ⟦V⟧) = 0 ∨ Real.sin (θ₂₃ ⟦V⟧) = 0 := by
  rw [VudAbs_eq_C₁₂_mul_C₁₃, VubAbs_eq_S₁₃, VusAbs_eq_S₁₂_mul_C₁₃, VcbAbs_eq_S₂₃_mul_C₁₃,
    VtbAbs_eq_C₂₃_mul_C₁₃, C₁₂, C₁₃, C₂₃, S₁₂_eq_sin_θ₁₂, S₂₃_eq_sin_θ₂₃, S₁₃_eq_sin_θ₁₃]
  aesop

end VAbs

namespace standParam
open Invariant

lemma mulExpδ₁₃_on_param_δ₁₃ (V : CKMMatrix) (δ₁₃ : ℝ) :
    mulExpδ₁₃ ⟦standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃⟧ =
    sin (θ₁₂ ⟦V⟧) * cos (θ₁₃ ⟦V⟧) ^ 2 * sin (θ₂₃ ⟦V⟧) * sin (θ₁₃ ⟦V⟧)
    * cos (θ₁₂ ⟦V⟧) * cos (θ₂₃ ⟦V⟧) * cexp (I * δ₁₃) := by
  refine mulExpδ₁₃_eq _ _ _ _ ?_ (Real.cos_arcsin_nonneg _) ?_ (Real.cos_arcsin_nonneg _)
  · exact le_of_le_of_eq (S₁₂_nonneg _) (S₁₂_eq_sin_θ₁₂ _).symm
  · exact le_of_le_of_eq (S₂₃_nonneg _) (S₂₃_eq_sin_θ₂₃ _).symm

lemma mulExpδ₁₃_on_param_eq_zero_iff (V : CKMMatrix) (δ₁₃ : ℝ) :
    mulExpδ₁₃ ⟦standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃⟧ = 0 ↔
      VudAbs ⟦V⟧ = 0 ∨ VubAbs ⟦V⟧ = 0 ∨ VusAbs ⟦V⟧ = 0 ∨ VcbAbs ⟦V⟧ = 0 ∨ VtbAbs ⟦V⟧ = 0 := by
  rw [VudAbs_eq_C₁₂_mul_C₁₃, VubAbs_eq_S₁₃, VusAbs_eq_S₁₂_mul_C₁₃, VcbAbs_eq_S₂₃_mul_C₁₃,
    VtbAbs_eq_C₂₃_mul_C₁₃, ← ofReal_inj,
    ← ofReal_inj, ← ofReal_inj, ← ofReal_inj, ← ofReal_inj]
  simp only [ofReal_mul]
  rw [← S₁₃_eq_ℂsin_θ₁₃, ← S₁₂_eq_ℂsin_θ₁₂, ← S₂₃_eq_ℂsin_θ₂₃,
    ← C₁₃_eq_ℂcos_θ₁₃, ← C₂₃_eq_ℂcos_θ₂₃, ← C₁₂_eq_ℂcos_θ₁₂, mulExpδ₁₃_on_param_δ₁₃]
  simp only [mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    ofReal_zero, exp_ne_zero, or_false]
  aesop

lemma mulExpδ₁₃_on_param_abs (V : CKMMatrix) (δ₁₃ : ℝ) :
    norm (mulExpδ₁₃ ⟦standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃⟧) =
    sin (θ₁₂ ⟦V⟧) * cos (θ₁₃ ⟦V⟧) ^ 2 * sin (θ₂₃ ⟦V⟧) * sin (θ₁₃ ⟦V⟧)
    * cos (θ₁₂ ⟦V⟧) * cos (θ₂₃ ⟦V⟧) := by
  rw [mulExpδ₁₃_on_param_δ₁₃]
  simp only [Complex.norm_mul, norm_pow, norm_exp, mul_re, I_re, ofReal_re, zero_mul, I_im,
    ofReal_im, mul_zero, sub_self, Real.exp_zero, mul_one, ofReal_mul, ofReal_pow]
  rw [complexAbs_sin_θ₁₃, complexAbs_cos_θ₁₃, complexAbs_sin_θ₁₂, complexAbs_cos_θ₁₂,
    complexAbs_sin_θ₂₃, complexAbs_cos_θ₂₃]

lemma mulExpδ₁₃_on_param_ne_zero_arg (V : CKMMatrix) (δ₁₃ : ℝ)
    (h1 : mulExpδ₁₃ ⟦standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃⟧ ≠ 0) :
    cexp (arg (mulExpδ₁₃ ⟦standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃⟧) * I) =
    cexp (δ₁₃ * I) := by
  have h2 : mulExpδ₁₃ ⟦standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃⟧ = norm
      (mulExpδ₁₃ ⟦standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃⟧) * exp (δ₁₃ * I) := by
    rw [mulExpδ₁₃_on_param_abs V δ₁₃, mulExpδ₁₃_on_param_δ₁₃ V δ₁₃]
    ring_nf
  nth_rewrite 1 [← norm_mul_exp_arg_mul_I (mulExpδ₁₃
    ⟦standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃⟧)] at h2
  have habs_ne_zero :
      (norm (mulExpδ₁₃ ⟦standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃⟧) : ℂ) ≠ 0 := by
    simpa only [ne_eq, ofReal_eq_zero, norm_eq_zero] using h1
  rw [← mul_right_inj' habs_ne_zero, ← h2]

set_option backward.isDefEq.respectTransparency false in
lemma on_param_cos_θ₁₃_eq_zero {V : CKMMatrix} (δ₁₃ : ℝ) (h : Real.cos (θ₁₃ ⟦V⟧) = 0) :
    standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃ ≈ standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) 0 := by
  have hub := VubAbs_of_cos_θ₁₃_zero h
  use 0, 0, 0, δ₁₃, 0, -δ₁₃
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standParam, standParamAsMatrix, phaseShift, phaseShiftMatrix, mul_apply,
      Fin.sum_univ_three, ofReal_cos, ofReal_sin, S₁₃_eq_ℂsin_θ₁₃, C₁₂_eq_ℂcos_θ₁₂,
      S₁₂_eq_ℂsin_θ₁₂, S₁₃_of_Vub_one hub, C₁₂_of_Vub_one hub, S₁₂_of_Vub_one hub, h, exp_neg]

set_option backward.isDefEq.respectTransparency false in
lemma on_param_cos_θ₁₂_eq_zero {V : CKMMatrix} (δ₁₃ : ℝ) (h : Real.cos (θ₁₂ ⟦V⟧) = 0) :
    standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃ ≈ standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) 0 := by
  use 0, δ₁₃, δ₁₃, -δ₁₃, 0, - δ₁₃
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standParam, standParamAsMatrix, phaseShift, phaseShiftMatrix, mul_apply,
      Fin.sum_univ_three, h, exp_neg] <;>
    field_simp

set_option backward.isDefEq.respectTransparency false in
lemma on_param_cos_θ₂₃_eq_zero {V : CKMMatrix} (δ₁₃ : ℝ) (h : Real.cos (θ₂₃ ⟦V⟧) = 0) :
    standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃ ≈ standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) 0 := by
  use 0, δ₁₃, 0, 0, 0, - δ₁₃
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standParam, standParamAsMatrix, phaseShift, phaseShiftMatrix, mul_apply,
      Fin.sum_univ_three, h, exp_neg] <;>
    field_simp

set_option backward.isDefEq.respectTransparency false in
lemma on_param_sin_θ₁₃_eq_zero {V : CKMMatrix} (δ₁₃ : ℝ) (h : Real.sin (θ₁₃ ⟦V⟧) = 0) :
    standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃ ≈ standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) 0 := by
  use 0, 0, 0, 0, 0, 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standParam, standParamAsMatrix, phaseShift, phaseShiftMatrix, mul_apply,
      Fin.sum_univ_three, h, exp_neg]

set_option backward.isDefEq.respectTransparency false in
lemma on_param_sin_θ₁₂_eq_zero {V : CKMMatrix} (δ₁₃ : ℝ) (h : Real.sin (θ₁₂ ⟦V⟧) = 0) :
    standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃ ≈ standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) 0 := by
  use 0, δ₁₃, δ₁₃, 0, -δ₁₃, - δ₁₃
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standParam, standParamAsMatrix, phaseShift, phaseShiftMatrix, mul_apply,
      Fin.sum_univ_three, h, exp_neg] <;>
    field_simp

set_option backward.isDefEq.respectTransparency false in
lemma on_param_sin_θ₂₃_eq_zero {V : CKMMatrix} (δ₁₃ : ℝ) (h : Real.sin (θ₂₃ ⟦V⟧) = 0) :
    standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃ ≈ standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) 0 := by
  use 0, 0, δ₁₃, 0, 0, - δ₁₃
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standParam, standParamAsMatrix, phaseShift, phaseShiftMatrix, mul_apply,
      Fin.sum_univ_three, h, exp_neg] <;>
    field_simp

lemma eq_standParam_of_fstRowThdColRealCond {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0)
    (hV : FstRowThdColRealCond V) : V = standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) (- arg [V]ub) := by
  have hb' : VubAbs ⟦V⟧ ≠ 1 := (ud_us_ne_zero_iff_ub_ne_one V).mp hb
  have h1 : ofRealHom (√(VAbs 0 0 ⟦V⟧ ^ 2 + VAbs 0 1 ⟦V⟧ ^ 2) *
    ↑√(VAbs 0 0 ⟦V⟧ ^ 2 + VAbs 0 1 ⟦V⟧ ^ 2)) = ofRealHom (VAbs 0 0 ⟦V⟧ ^ 2 + VAbs 0 1 ⟦V⟧ ^ 2) := by
    rw [Real.mul_self_sqrt]
    apply add_nonneg (sq_nonneg _) (sq_nonneg _)
  simp only [Fin.isValue, _root_.map_mul, ofRealHom_eq_coe, map_add, map_pow] at h1
  have hx := Vabs_sq_add_ne_zero hb
  refine eq_rows V ?_ ?_ hV.2.2.2.2
  · funext i
    fin_cases i
    · simp [uRow, standParam, standParamAsMatrix, hV.1, VudAbs_eq_C₁₂_mul_C₁₃ ⟦V⟧, C₁₂, C₁₃]
    · simp [uRow, standParam, standParamAsMatrix, hV.2.1, VusAbs_eq_S₁₂_mul_C₁₃ ⟦V⟧,
        ← S₁₂_eq_sin_θ₁₂ ⟦V⟧, C₁₃]
    · simp only [uRow, Fin.isValue, Fin.reduceFinMk, cons_val_two, Nat.succ_eq_add_one,
      Nat.reduceAdd, tail_cons, head_cons, standParam, standParamAsMatrix, ofReal_cos, ofReal_sin,
      ofReal_neg, mul_neg, neg_mul, neg_neg, cons_val', cons_val_zero, empty_val', cons_val_fin_one,
      cons_val_one]
      nth_rewrite 1 [← norm_mul_exp_arg_mul_I (V.1 0 2)]
      rw [show norm (V.1 0 2) = VubAbs ⟦V⟧ from rfl, VubAbs_eq_S₁₃, ← S₁₃_eq_sin_θ₁₃ ⟦V⟧]
      simp only [ofReal_sin, Fin.isValue, mul_eq_mul_left_iff]
      ring_nf
      simp only [true_or]
  · funext i
    fin_cases i
    · simp only [cRow, Fin.isValue, Fin.zero_eta, cons_val_zero, standParam, standParamAsMatrix,
      ofReal_cos, ofReal_sin, ofReal_neg, mul_neg, neg_mul, neg_neg, cons_val', empty_val',
      cons_val_fin_one, cons_val_one, head_cons, cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd,
      tail_cons]
      rw [cd_of_fstRowThdColRealCond hb hV, S₁₂_eq_ℂsin_θ₁₂ ⟦V⟧, S₁₂, C₁₂_eq_ℂcos_θ₁₂ ⟦V⟧,
        C₁₂_eq_Vud_div_sqrt hb', S₂₃_eq_ℂsin_θ₂₃ ⟦V⟧, S₂₃_of_Vub_ne_one hb', C₂₃_eq_ℂcos_θ₂₃ ⟦V⟧,
        C₂₃_of_Vub_ne_one hb', S₁₃_eq_ℂsin_θ₁₃ ⟦V⟧, S₁₃]
      simp only [VtbAbs, Fin.isValue, VusAbs, neg_mul, VudAbs, VubAbs, VcbAbs, ofReal_div]
      field_simp
      conv_rhs => rw [sq, h1]
      simp only [Fin.isValue, sq]
      field_simp
      ring_nf
    · simp only [cRow, Fin.isValue, Fin.mk_one, cons_val_one, head_cons, standParam,
      standParamAsMatrix, ofReal_cos, ofReal_sin, ofReal_neg, mul_neg, neg_mul, neg_neg, cons_val',
      cons_val_zero, empty_val', cons_val_fin_one, cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd,
      tail_cons]
      rw [C₁₂_eq_ℂcos_θ₁₂ ⟦V⟧, C₂₃_eq_ℂcos_θ₂₃ ⟦V⟧, S₁₂_eq_ℂsin_θ₁₂ ⟦V⟧,
        S₁₃_eq_ℂsin_θ₁₃ ⟦V⟧, S₂₃_eq_ℂsin_θ₂₃ ⟦V⟧, C₁₂_eq_Vud_div_sqrt hb', C₂₃_of_Vub_ne_one hb',
        S₁₂, S₁₃, S₂₃_of_Vub_ne_one hb', cs_of_fstRowThdColRealCond hb hV]
      simp only [VtbAbs, Fin.isValue, VudAbs, VusAbs, VubAbs, neg_mul, VcbAbs, ofReal_div]
      field_simp
      conv_rhs => rw [sq, h1]
      simp only [Fin.isValue, sq]
      field_simp
      ring_nf
    · simp [cRow, standParam, standParamAsMatrix, hV.2.2.1, VcbAbs_eq_S₂₃_mul_C₁₃ ⟦V⟧,
        S₂₃_eq_ℂsin_θ₂₃ ⟦V⟧, C₁₃]

lemma eq_standParam_of_ubOnePhaseCond {V : CKMMatrix} (hV : ubOnePhaseCond V) :
    V = standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) 0 := by
  have h1 : VubAbs ⟦V⟧ = 1 := by
    simp only [VubAbs, VAbs, VAbs', Fin.isValue, Quotient.lift_mk, hV.2.2.2.1, norm_one]
  refine eq_rows V ?_ ?_ hV.2.2.2.2.1
  · funext i
    fin_cases i
    · simp only [uRow, Fin.isValue, Fin.zero_eta, cons_val_zero, standParam, standParamAsMatrix,
      ofReal_cos, ofReal_sin, ofReal_zero, mul_zero, exp_zero, mul_one, neg_mul, cons_val',
      empty_val', cons_val_fin_one, cons_val_one, head_cons, cons_val_two, Nat.succ_eq_add_one,
      Nat.reduceAdd, tail_cons]
      rw [C₁₃_eq_ℂcos_θ₁₃ ⟦V⟧, C₁₃_of_Vub_eq_one h1, hV.1]
      exact Eq.symm (mul_eq_zero_of_right (cos ↑(θ₁₂ ⟦V⟧)) rfl)
    · simp only [uRow, Fin.isValue, Fin.mk_one, cons_val_one, head_cons, standParam,
      standParamAsMatrix, ofReal_cos, ofReal_sin, ofReal_zero, mul_zero, exp_zero, mul_one, neg_mul,
      cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_two, Nat.succ_eq_add_one,
      Nat.reduceAdd, tail_cons]
      rw [C₁₃_eq_ℂcos_θ₁₃ ⟦V⟧, C₁₃_of_Vub_eq_one h1, hV.2.1]
      exact Eq.symm (mul_eq_zero_of_right (sin ↑(θ₁₂ ⟦V⟧)) rfl)
    · simp only [uRow, Fin.isValue, Fin.reduceFinMk, cons_val_two, Nat.succ_eq_add_one,
      Nat.reduceAdd, tail_cons, head_cons, standParam, standParamAsMatrix, ofReal_cos, ofReal_sin,
      ofReal_zero, mul_zero, exp_zero, mul_one, neg_mul, cons_val', cons_val_zero, empty_val',
      cons_val_fin_one, cons_val_one]
      rw [S₁₃_eq_ℂsin_θ₁₃ ⟦V⟧, S₁₃]
      simp only [Fin.isValue, VubAbs, VAbs, VAbs', Quotient.lift_mk]
      rw [hV.2.2.2.1]
      simp
  · funext i
    fin_cases i
    · simp only [cRow, Fin.isValue, Fin.zero_eta, cons_val_zero, standParam, standParamAsMatrix,
      ofReal_cos, ofReal_sin, ofReal_zero, mul_zero, exp_zero, mul_one, neg_mul, cons_val',
      empty_val', cons_val_fin_one, cons_val_one, head_cons, cons_val_two, Nat.succ_eq_add_one,
      Nat.reduceAdd, tail_cons]
      rw [S₂₃_eq_ℂsin_θ₂₃ ⟦V⟧, S₂₃_of_Vub_eq_one h1, S₁₂_eq_ℂsin_θ₁₂ ⟦V⟧, S₁₂_of_Vub_one h1,
        C₁₂_eq_ℂcos_θ₁₂ ⟦V⟧, C₁₂_of_Vub_one h1, S₁₃_eq_ℂsin_θ₁₃ ⟦V⟧, S₁₃_of_Vub_one h1,
        hV.2.2.2.2.2.1]
      simp only [VcdAbs, Fin.isValue, ofReal_zero, zero_mul, neg_zero, ofReal_one, mul_one, one_mul,
        zero_sub]
    · simp only [cRow, Fin.isValue, Fin.mk_one, cons_val_one, head_cons, standParam,
      standParamAsMatrix, ofReal_cos, ofReal_sin, ofReal_zero, mul_zero, exp_zero, mul_one, neg_mul,
      cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_two, Nat.succ_eq_add_one,
      Nat.reduceAdd, tail_cons]
      rw [S₂₃_eq_ℂsin_θ₂₃ ⟦V⟧, S₂₃_of_Vub_eq_one h1, S₁₂_eq_ℂsin_θ₁₂ ⟦V⟧, S₁₂_of_Vub_one h1,
        C₁₂_eq_ℂcos_θ₁₂ ⟦V⟧, C₁₂_of_Vub_one h1, S₁₃_eq_ℂsin_θ₁₃ ⟦V⟧, S₁₃_of_Vub_one h1]
      simp only [Fin.isValue, ofReal_one, one_mul, ofReal_zero, mul_one, VcdAbs, zero_mul, sub_zero]
      have h3 : (Real.cos (θ₂₃ ⟦V⟧) : ℂ) = √(1 - S₂₃ ⟦V⟧ ^ 2) := by
        rw [θ₂₃, Real.cos_arcsin]
      simp only [ofReal_cos] at h3
      rw [h3, S₂₃_of_Vub_eq_one h1, hV.2.2.2.2.2.2]
    · simp only [cRow, Fin.isValue, Fin.reduceFinMk, cons_val_two, Nat.succ_eq_add_one,
      Nat.reduceAdd, tail_cons, head_cons, standParam, standParamAsMatrix, ofReal_cos, ofReal_sin,
      ofReal_zero, mul_zero, exp_zero, mul_one, neg_mul, cons_val', cons_val_zero, empty_val',
      cons_val_fin_one, cons_val_one]
      rw [C₁₃_eq_ℂcos_θ₁₃ ⟦V⟧, C₁₃_of_Vub_eq_one h1, hV.2.2.1]
      exact Eq.symm (mul_eq_zero_of_right (sin ↑(θ₂₃ ⟦V⟧)) rfl)

theorem exists_δ₁₃ (V : CKMMatrix) :
    ∃ (δ₃ : ℝ), V ≈ standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₃ := by
  obtain ⟨U, hU⟩ := fstRowThdColRealCond_holds_up_to_equiv V
  have hUV : ⟦U⟧ = ⟦V⟧ := (Quotient.eq.mpr (phaseShiftRelation_equiv.symm hU.1))
  by_cases ha : [V]ud ≠ 0 ∨ [V]us ≠ 0
  · have haU : [U]ud ≠ 0 ∨ [U]us ≠ 0 := by
      rw [ud_us_ne_zero_iff_ub_ne_one] at ha ⊢
      rwa [show norm [U]ub = VubAbs ⟦U⟧ from rfl, hUV]
    have hU' := eq_standParam_of_fstRowThdColRealCond haU hU.2
    rw [hU'] at hU
    use (- arg ([U]ub))
    exact hUV ▸ hU.1
  · have haU : ¬ ([U]ud ≠ 0 ∨ [U]us ≠ 0) := by
      rw [ud_us_ne_zero_iff_ub_ne_one] at ha ⊢
      rwa [show norm [U]ub = VubAbs ⟦U⟧ from rfl, hUV]
    have ⟨U2, hU2⟩ := ubOnePhaseCond_hold_up_to_equiv_of_ub_one haU hU.2
    have hUVa2 : V ≈ U2 := phaseShiftRelation_equiv.trans hU.1 hU2.1
    have hUV2 : ⟦U2⟧ = ⟦V⟧ := (Quotient.eq.mpr (phaseShiftRelation_equiv.symm hUVa2))
    have hx := eq_standParam_of_ubOnePhaseCond hU2.2
    use 0
    rw [← hUV2, ← hx]
    exact hUVa2

open Invariant in
theorem eq_standardParameterization_δ₃ (V : CKMMatrix) :
    V ≈ standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) (δ₁₃ ⟦V⟧) := by
  obtain ⟨δ₁₃', hδ₃⟩ := exists_δ₁₃ V
  have hSV := (Quotient.eq.mpr (hδ₃))
  by_cases h : Invariant.mulExpδ₁₃ ⟦standParam (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃'⟧ ≠ 0
  · have h2 := eq_exp_of_phases (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃'
      (δ₁₃ ⟦V⟧) (by rw [← mulExpδ₁₃_on_param_ne_zero_arg V δ₁₃' h,
        ← hSV, δ₁₃, Invariant.mulExpδ₁₃])
    rw [h2] at hδ₃
    exact hδ₃
  · simp only [ne_eq, Decidable.not_not] at h
    have h1 : δ₁₃ ⟦V⟧ = 0 := by
      rw [hSV, δ₁₃, h]
      exact arg_zero
    rw [h1]
    rw [mulExpδ₁₃_on_param_eq_zero_iff, Vs_zero_iff_cos_sin_zero] at h
    refine phaseShiftRelation_equiv.trans hδ₃ ?_
    rcases h with h | h | h | h | h | h
    · exact on_param_cos_θ₁₂_eq_zero δ₁₃' h
    · exact on_param_cos_θ₁₃_eq_zero δ₁₃' h
    · exact on_param_cos_θ₂₃_eq_zero δ₁₃' h
    · exact on_param_sin_θ₁₂_eq_zero δ₁₃' h
    · exact on_param_sin_θ₁₃_eq_zero δ₁₃' h
    · exact on_param_sin_θ₂₃_eq_zero δ₁₃' h

theorem exists_for_CKMatrix (V : CKMMatrix) :
    ∃ (θ₁₂ θ₁₃ θ₂₃ δ₁₃ : ℝ), V ≈ standParam θ₁₂ θ₁₃ θ₂₃ δ₁₃ := by
  use θ₁₂ ⟦V⟧, θ₁₃ ⟦V⟧, θ₂₃ ⟦V⟧, δ₁₃ ⟦V⟧
  exact eq_standardParameterization_δ₃ V

end standParam

open CKMMatrix

end
