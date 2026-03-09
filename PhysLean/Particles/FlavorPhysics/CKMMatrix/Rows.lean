/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.FlavorPhysics.CKMMatrix.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Cases
/-!
# Rows for the CKM Matrix

This file contains the definition extracting the rows of the CKM matrix and
proves some properties between them.

The first row can be extracted as `[V]u` for a CKM matrix `V`.

-/

@[expose] public section

open Matrix Complex ComplexConjugate Module

noncomputable section

namespace CKMMatrix

/-- The `u`th row of the CKM matrix. -/
def uRow (V : CKMMatrix) : Fin 3 → ℂ := ![[V]ud, [V]us, [V]ub]

/-- The `u`th row of the CKM matrix. -/
scoped[CKMMatrix] notation (name := u_row) "[" V "]u" => uRow V

/-- The `c`th row of the CKM matrix. -/
def cRow (V : CKMMatrix) : Fin 3 → ℂ := ![[V]cd, [V]cs, [V]cb]

/-- The `c`th row of the CKM matrix. -/
scoped[CKMMatrix] notation (name := c_row) "[" V "]c" => cRow V

/-- The `t`th row of the CKM matrix. -/
def tRow (V : CKMMatrix) : Fin 3 → ℂ := ![[V]td, [V]ts, [V]tb]

/-- The `t`th row of the CKM matrix. -/
scoped[CKMMatrix] notation (name := t_row) "[" V "]t" => tRow V

/-- The up-quark row of the CKM matrix is normalized to `1`. -/
lemma uRow_normalized (V : CKMMatrix) : conj [V]u ⬝ᵥ [V]u = 1 := by
  simp only [vec3_dotProduct, Fin.isValue, Pi.conj_apply]
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 0) 0
  simp only [Fin.isValue, mul_apply, star_apply, RCLike.star_def, Fin.sum_univ_three,
    one_apply_eq] at ht
  rw [mul_comm (V.1 0 0) _, mul_comm (V.1 0 1) _, mul_comm (V.1 0 2) _] at ht
  exact ht

/-- The charm-quark row of the CKM matrix is normalized to `1`. -/
lemma cRow_normalized (V : CKMMatrix) : conj [V]c ⬝ᵥ [V]c = 1 := by
  simp only [vec3_dotProduct, Fin.isValue, Pi.conj_apply]
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 1) 1
  simp only [Fin.isValue, mul_apply, star_apply, RCLike.star_def, Fin.sum_univ_three,
    one_apply_eq] at ht
  rw [mul_comm (V.1 1 0) _, mul_comm (V.1 1 1) _, mul_comm (V.1 1 2) _] at ht
  exact ht

/-- The top-quark row of the CKM matrix is normalized to `1`. -/
lemma tRow_normalized (V : CKMMatrix) : conj [V]t ⬝ᵥ [V]t = 1 := by
  simp only [vec3_dotProduct, Fin.isValue, Pi.conj_apply]
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 2) 2
  simp only [Fin.isValue, mul_apply, star_apply, RCLike.star_def, Fin.sum_univ_three,
    one_apply_eq] at ht
  rw [mul_comm (V.1 2 0) _, mul_comm (V.1 2 1) _, mul_comm (V.1 2 2) _] at ht
  exact ht

/-- The up-quark row of the CKM matrix is orthogonal to the charm-quark row. -/
lemma uRow_cRow_orthog (V : CKMMatrix) : conj [V]u ⬝ᵥ [V]c = 0 := by
  simp only [vec3_dotProduct, Fin.isValue, Pi.conj_apply]
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 1) 0
  simp only [Fin.isValue, mul_apply, star_apply, RCLike.star_def, Fin.sum_univ_three, ne_eq,
    one_ne_zero, not_false_eq_true, one_apply_ne] at ht
  rw [mul_comm (V.1 _ 0) _, mul_comm (V.1 _ 1) _, mul_comm (V.1 _ 2) _] at ht
  exact ht

/-- The up-quark row of the CKM matrix is orthogonal to the top-quark row. -/
lemma uRow_tRow_orthog (V : CKMMatrix) : conj [V]u ⬝ᵥ [V]t = 0 := by
  simp only [vec3_dotProduct, Fin.isValue, Pi.conj_apply]
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 2) 0
  simp only [Fin.isValue, mul_apply, star_apply, RCLike.star_def, Fin.sum_univ_three, ne_eq,
    Fin.reduceEq, not_false_eq_true, one_apply_ne] at ht
  rw [mul_comm (V.1 _ 0) _, mul_comm (V.1 _ 1) _, mul_comm (V.1 _ 2) _] at ht
  exact ht

/-- The charm-quark row of the CKM matrix is orthogonal to the up-quark row. -/
lemma cRow_uRow_orthog (V : CKMMatrix) : conj [V]c ⬝ᵥ [V]u = 0 := by
  simp only [vec3_dotProduct, Fin.isValue, Pi.conj_apply]
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 0) 1
  simp only [Fin.isValue, mul_apply, star_apply, RCLike.star_def, Fin.sum_univ_three, ne_eq,
    zero_ne_one, not_false_eq_true, one_apply_ne] at ht
  rw [mul_comm (V.1 _ 0) _, mul_comm (V.1 _ 1) _, mul_comm (V.1 _ 2) _] at ht
  exact ht

/-- The charm-quark row of the CKM matrix is orthogonal to the top-quark row. -/
lemma cRow_tRow_orthog (V : CKMMatrix) : conj [V]c ⬝ᵥ [V]t = 0 := by
  simp only [vec3_dotProduct, Fin.isValue, Pi.conj_apply]
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 2) 1
  simp only [Fin.isValue, mul_apply, star_apply, RCLike.star_def, Fin.sum_univ_three, ne_eq,
    Fin.reduceEq, not_false_eq_true, one_apply_ne] at ht
  rw [mul_comm (V.1 _ 0) _, mul_comm (V.1 _ 1) _, mul_comm (V.1 _ 2) _] at ht
  exact ht

/-- The top-quark row of the CKM matrix is orthogonal to the up-quark row. -/
lemma tRow_uRow_orthog (V : CKMMatrix) : conj [V]t ⬝ᵥ [V]u = 0 := by
  simp only [vec3_dotProduct, Fin.isValue, Pi.conj_apply]
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 0) 2
  simp only [Fin.isValue, mul_apply, star_apply, RCLike.star_def, Fin.sum_univ_three, ne_eq,
    Fin.reduceEq, not_false_eq_true, one_apply_ne] at ht
  rw [mul_comm (V.1 _ 0) _, mul_comm (V.1 _ 1) _, mul_comm (V.1 _ 2) _] at ht
  exact ht

/-- The top-quark row of the CKM matrix is orthogonal to the charm-quark row. -/
lemma tRow_cRow_orthog (V : CKMMatrix) : conj [V]t ⬝ᵥ [V]c = 0 := by
  simp only [vec3_dotProduct, Fin.isValue, Pi.conj_apply]
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 1) 2
  simp only [Fin.isValue, mul_apply, star_apply, RCLike.star_def, Fin.sum_univ_three, ne_eq,
    Fin.reduceEq, not_false_eq_true, one_apply_ne] at ht
  rw [mul_comm (V.1 _ 0) _, mul_comm (V.1 _ 1) _, mul_comm (V.1 _ 2) _] at ht
  exact ht

lemma uRow_cross_cRow_conj (V : CKMMatrix) : conj (conj [V]u ⨯₃ conj [V]c) = [V]u ⨯₃ [V]c := by
  simp only [crossProduct, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, LinearMap.mk₂_apply,
    Pi.conj_apply]
  funext i
  fin_cases i <;> simp

lemma cRow_cross_tRow_conj (V : CKMMatrix) : conj (conj [V]c ⨯₃ conj [V]t) = [V]c ⨯₃ [V]t := by
  simp only [crossProduct, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, LinearMap.mk₂_apply,
    Pi.conj_apply]
  funext i
  fin_cases i <;> simp

lemma uRow_cross_cRow_normalized (V : CKMMatrix) :
    conj (conj [V]u ⨯₃ conj [V]c) ⬝ᵥ (conj [V]u ⨯₃ conj [V]c) = 1 := by
  rw [uRow_cross_cRow_conj, cross_dot_cross, dotProduct_comm, uRow_normalized,
    dotProduct_comm, cRow_normalized, dotProduct_comm, cRow_uRow_orthog,
    dotProduct_comm, uRow_cRow_orthog]
  simp

lemma cRow_cross_tRow_normalized (V : CKMMatrix) :
    conj (conj [V]c ⨯₃ conj [V]t) ⬝ᵥ (conj [V]c ⨯₃ conj [V]t) = 1 := by
  rw [cRow_cross_tRow_conj, cross_dot_cross, dotProduct_comm, cRow_normalized,
    dotProduct_comm, tRow_normalized, dotProduct_comm, tRow_cRow_orthog,
    dotProduct_comm, cRow_tRow_orthog]
  simp

/-- A map from `Fin 3` to each row of a CKM matrix. -/
@[simp]
def rows (V : CKMMatrix) : Fin 3 → Fin 3 → ℂ := fun i =>
  match i with
  | 0 => uRow V
  | 1 => cRow V
  | 2 => tRow V

/-- The rows of a CKM matrix are linearly independent. -/
lemma rows_linearly_independent (V : CKMMatrix) : LinearIndependent ℂ (rows V) := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg
  rw [Fin.sum_univ_three] at hg
  simp only [Fin.isValue, rows] at hg
  have h0 := congrArg (fun X => conj [V]u ⬝ᵥ X) hg
  have h1 := congrArg (fun X => conj [V]c ⬝ᵥ X) hg
  have h2 := congrArg (fun X => conj [V]t ⬝ᵥ X) hg
  simp only [Fin.isValue, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_zero] at h0 h1 h2
  rw [uRow_normalized, uRow_cRow_orthog, uRow_tRow_orthog] at h0
  rw [cRow_normalized, cRow_uRow_orthog, cRow_tRow_orthog] at h1
  rw [tRow_normalized, tRow_uRow_orthog, tRow_cRow_orthog] at h2
  simp only [Fin.isValue, mul_one, mul_zero, add_zero, zero_add] at h0 h1 h2
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- The rows of a CKM matrix as a basis of `ℂ³`. -/
@[simps!]
noncomputable def rowBasis (V : CKMMatrix) : Basis (Fin 3) ℂ (Fin 3 → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank (rows_linearly_independent V)
    (Module.finrank_fin_fun ℂ).symm

lemma cRow_cross_tRow_eq_uRow (V : CKMMatrix) :
    ∃ (κ : ℝ), [V]u = cexp (κ * I) • (conj [V]c ⨯₃ conj [V]t) := by
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (Basis.mem_span (rowBasis V)
    (conj [V]c ⨯₃ conj [V]t))
  simp only [Fin.sum_univ_three, rowBasis, Fin.isValue,
    coe_basisOfLinearIndependentOfCardEqFinrank, rows] at hg
  have h0 := congrArg (fun X => conj [V]c ⬝ᵥ X) hg
  have h1 := congrArg (fun X => conj [V]t ⬝ᵥ X) hg
  simp only [Fin.isValue, dotProduct_add, dotProduct_smul, smul_eq_mul] at h0 h1
  rw [cRow_normalized, cRow_uRow_orthog, cRow_tRow_orthog, dot_self_cross] at h0
  rw [tRow_normalized, tRow_uRow_orthog, tRow_cRow_orthog, dot_cross_self] at h1
  simp only [Fin.isValue, mul_zero, mul_one, zero_add, add_zero] at h0 h1 hg
  simp only [h0, h1, zero_smul, add_zero] at hg
  have h2 := congrArg (fun X => conj X ⬝ᵥ X) hg
  simp only [Fin.isValue, dotProduct_smul, smul_eq_mul, cRow_cross_tRow_normalized] at h2
  have h3 : conj (g 0 • [V]u) = conj (g 0) • conj [V]u := by
    funext i
    fin_cases i <;> simp
  simp only [Fin.isValue, h3, smul_dotProduct, uRow_normalized, smul_eq_mul, mul_one, mul_conj, ←
    Complex.sq_norm] at h2
  simp only [Fin.isValue, ofReal_pow, sq_eq_one_iff, ofReal_eq_one] at h2
  cases' h2 with h2 h2
  · have hx : [V]u = (g 0)⁻¹ • (conj ([V]c) ⨯₃ conj ([V]t)) := by
      rw [← hg, smul_smul, inv_mul_cancel₀, one_smul]
      by_contra hn
      simp [hn] at h2
    have hg2 : norm (g 0)⁻¹ = 1 := by
      simp [h2]
    have hg22 : ∃ (τ : ℝ), (g 0)⁻¹ = Complex.exp (τ * I) := by
      rw [← norm_mul_exp_arg_mul_I (g 0)⁻¹, hg2]
      use arg (g 0)⁻¹
      simp
    obtain ⟨τ, hτ⟩ := hg22
    use τ
    rw [hx, hτ]
  · have hx : norm (g 0) = -1 := by
      simp [← ofReal_inj, Fin.isValue, ofReal_neg, ofReal_one, h2]
    have h3 := norm_nonneg (g 0)
    simp_all only [ofReal_neg, ofReal_one, Left.nonneg_neg_iff]
    have h4 : (0 : ℝ) < 1 := by norm_num
    exact False.elim (lt_iff_not_ge.mp h4 h3)

lemma uRow_cross_cRow_eq_tRow (V : CKMMatrix) :
    ∃ (τ : ℝ), [V]t = cexp (τ * I) • (conj ([V]u) ⨯₃ conj ([V]c)) := by
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (Basis.mem_span (rowBasis V)
    (conj ([V]u) ⨯₃ conj ([V]c)))
  rw [Fin.sum_univ_three, rowBasis] at hg
  simp only [Fin.isValue, coe_basisOfLinearIndependentOfCardEqFinrank, rows] at hg
  have h0 := congrArg (fun X => conj [V]u ⬝ᵥ X) hg
  have h1 := congrArg (fun X => conj [V]c ⬝ᵥ X) hg
  simp only [Fin.isValue, dotProduct_add, dotProduct_smul, smul_eq_mul] at h0 h1
  rw [uRow_normalized, uRow_cRow_orthog, uRow_tRow_orthog, dot_self_cross] at h0
  rw [cRow_normalized, cRow_uRow_orthog, cRow_tRow_orthog, dot_cross_self] at h1
  simp only [Fin.isValue, mul_one, mul_zero, add_zero, zero_add] at h0 h1
  simp only [Fin.isValue, h0, zero_smul, h1, add_zero, zero_add] at hg
  have h2 := congrArg (fun X => conj X ⬝ᵥ X) hg
  simp only [Fin.isValue, dotProduct_smul, smul_eq_mul] at h2
  rw [uRow_cross_cRow_normalized] at h2
  have h3 : conj (g 2 • [V]t) = conj (g 2) • conj [V]t := by
    funext i
    fin_cases i <;> simp
  simp only [h3, Fin.isValue, smul_dotProduct, smul_eq_mul, tRow_normalized,
    Fin.isValue, mul_one, mul_conj, ← Complex.sq_norm, ofReal_pow, sq_eq_one_iff,
    ofReal_eq_one] at h2
  cases' h2 with h2 h2
  swap
  · have hx : norm (g 2) = -1 := by
      simp [h2, ← ofReal_inj, Fin.isValue, ofReal_neg, ofReal_one]
    have h3 := norm_nonneg (g 2)
    simp_all only [ofReal_neg, ofReal_one, Left.nonneg_neg_iff]
    have h4 : (0 : ℝ) < 1 := by norm_num
    exact False.elim (lt_iff_not_ge.mp h4 h3)
  · have hx : [V]t = (g 2)⁻¹ • (conj ([V]u) ⨯₃ conj ([V]c)) := by
      rw [← hg, @smul_smul, inv_mul_cancel₀, one_smul]
      by_contra hn
      simp [hn] at h2
    have hg2 : norm (g 2)⁻¹ = 1 := by
      simp [h2]
    have hg22 : ∃ (τ : ℝ), (g 2)⁻¹ = Complex.exp (τ * I) := by
      rw [← norm_mul_exp_arg_mul_I (g 2)⁻¹]
      use arg (g 2)⁻¹
      simp [hg2]
    obtain ⟨τ, hτ⟩ := hg22
    use τ
    rw [hx, hτ]

lemma ext_Rows {U V : CKMMatrix} (hu : [U]u = [V]u) (hc : [U]c = [V]c) (ht : [U]t = [V]t) :
    U = V := by
  apply CKMMatrix_ext
  funext i j
  fin_cases i
  · have h1 := congrFun hu j
    fin_cases j <;> simpa using h1
  · have h1 := congrFun hc j
    fin_cases j <;> simpa using h1
  · have h1 := congrFun ht j
    fin_cases j <;> simpa using h1

end CKMMatrix

namespace phaseShiftApply
open CKMMatrix

variable (V : CKMMatrix) (a b c d e f : ℝ)

/-- The cross product of the conjugate of the `u` and `c` rows of a CKM matrix. -/
def ucCross : Fin 3 → ℂ :=
  conj [phaseShiftApply V a b c d e f]u ⨯₃ conj [phaseShiftApply V a b c d e f]c

lemma ucCross_fst (V : CKMMatrix) : (ucCross V a b c d e f) 0 =
    cexp ((- a * I) + (- b * I) + (- e * I) + (- f * I)) * (conj [V]u ⨯₃ conj [V]c) 0 := by
  simp only [ucCross, crossProduct, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, uRow,
    phaseShiftApply_coe, us, exp_add, ub, cRow, cs, cb, LinearMap.mk₂_apply, Pi.conj_apply,
    cons_val_one, head_cons, _root_.map_mul, ← exp_conj, conj_ofReal, conj_I, mul_neg, cons_val_two,
    tail_cons, cons_val_zero, neg_mul]
  ring

lemma ucCross_snd (V : CKMMatrix) : (ucCross V a b c d e f) 1 =
    cexp ((- a * I) + (- b * I) + (- d * I) + (- f * I)) * (conj [V]u ⨯₃ conj [V]c) 1 := by
  simp only [ucCross, crossProduct, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, uRow, ud,
    exp_add, us, ub, cRow, cd, cs, cb, LinearMap.mk₂_apply, Pi.conj_apply, cons_val_one, head_cons,
    _root_.map_mul, ← exp_conj, conj_ofReal, conj_I, mul_neg, cons_val_two, tail_cons,
    cons_val_zero, neg_mul]
  ring

lemma ucCross_thd (V : CKMMatrix) : (ucCross V a b c d e f) 2 =
    cexp ((- a * I) + (- b * I) + (- d * I) + (- e * I)) * (conj [V]u ⨯₃ conj [V]c) 2 := by
  simp only [ucCross, crossProduct, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, uRow, ud,
    exp_add, us, ub, cRow, cd, cs, cb, LinearMap.mk₂_apply, Pi.conj_apply, cons_val_one, head_cons,
    _root_.map_mul, ← exp_conj, conj_ofReal, conj_I, mul_neg, cons_val_two, tail_cons,
    cons_val_zero, neg_mul]
  ring

lemma uRow_mul (V : CKMMatrix) (a b c : ℝ) :
    [phaseShiftApply V a b c 0 0 0]u = cexp (a * I) • [V]u := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  fin_cases i <;>
    change (phaseShiftApply V a b c 0 0 0).1 0 _ = _
  · simp only [Fin.isValue, ud, ofReal_zero, zero_mul, add_zero, uRow, Fin.zero_eta, cons_val_zero]
  · simp [Fin.isValue, us, ofReal_zero, zero_mul, add_zero, uRow, Fin.mk_one, cons_val_one]
  · simp only [Fin.isValue, ub, ofReal_zero, zero_mul, add_zero, uRow, Fin.reduceFinMk,
    cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, tail_cons, head_cons]

lemma cRow_mul (V : CKMMatrix) (a b c : ℝ) :
    [phaseShiftApply V a b c 0 0 0]c = cexp (b * I) • [V]c := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  fin_cases i <;>
    change (phaseShiftApply V a b c 0 0 0).1 1 _ = _
  · simp only [Fin.isValue, cd, ofReal_zero, zero_mul, add_zero, cRow, Fin.zero_eta, cons_val_zero]
  · simp [Fin.isValue, cs, ofReal_zero, zero_mul, add_zero, cRow, Fin.mk_one, cons_val_one]
  · simp only [Fin.isValue, cb, ofReal_zero, zero_mul, add_zero, cRow, Fin.reduceFinMk,
    cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, tail_cons, head_cons]

lemma tRow_mul (V : CKMMatrix) (a b c : ℝ) :
    [phaseShiftApply V a b c 0 0 0]t = cexp (c * I) • [V]t := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  fin_cases i <;>
    change (phaseShiftApply V a b c 0 0 0).1 2 _ = _
  · simp only [Fin.isValue, td, ofReal_zero, zero_mul, add_zero, tRow, Fin.zero_eta, cons_val_zero]
  · simp [Fin.isValue, ts, ofReal_zero, zero_mul, add_zero, tRow, Fin.mk_one, cons_val_one]
  · simp only [Fin.isValue, tb, ofReal_zero, zero_mul, add_zero, tRow, Fin.reduceFinMk,
    cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, tail_cons, head_cons]

end phaseShiftApply

end
