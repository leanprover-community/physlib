/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.BeyondTheStandardModel.TwoHDM.Basic
/-!

# The gram matrix for the two Higgs doublet model

The main reference for material in this section is https://arxiv.org/pdf/hep-ph/0605184.

We will show that the gram matrix of the two Higgs doublet model
describes the gauge orbits of the configuration space.

-/

@[expose] public section
namespace TwoHiggsDoublet

open InnerProductSpace
open StandardModel

/-!

## A. The Gram matrix

-/

/-- The Gram matrix of the two Higgs doublet.
  This matrix is used in https://arxiv.org/abs/hep-ph/0605184. -/
noncomputable def gramMatrix (H : TwoHiggsDoublet) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟪H.Φ1, H.Φ1⟫_ℂ, ⟪H.Φ2, H.Φ1⟫_ℂ; ⟪H.Φ1, H.Φ2⟫_ℂ, ⟪H.Φ2, H.Φ2⟫_ℂ]

lemma gramMatrix_selfAdjoint (H : TwoHiggsDoublet) :
    IsSelfAdjoint (gramMatrix H) := by
  rw [gramMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [inner_conj_symm]

lemma eq_fst_norm_of_eq_gramMatrix {H1 H2 : TwoHiggsDoublet}
    (h : H1.gramMatrix = H2.gramMatrix) : ‖H1.Φ1‖ = ‖H2.Φ1‖ := by
  rw [gramMatrix, gramMatrix] at h
  have h1 := congrArg (fun x => x 0 0) h
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Fin.isValue] at h1
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
  rw [sq_eq_sq_iff_eq_or_eq_neg] at h1
  rcases h1 with h1 | h1
  · simpa using h1
  · rw [← RCLike.ofReal_neg] at h1
    have hnorm1 : 0 ≤ ‖H1.Φ1‖ := norm_nonneg H1.Φ1
    have hnorm2 : 0 ≤ ‖H2.Φ1‖ := norm_nonneg H2.Φ1
    have hl : ‖H1.Φ1‖ = (-‖H2.Φ1‖) := Eq.symm
      ((fun {z w} => Complex.ofReal_inj.mp) (id (Eq.symm h1)))
    grind

lemma eq_snd_norm_of_eq_gramMatrix {H1 H2 : TwoHiggsDoublet}
    (h : H1.gramMatrix = H2.gramMatrix) : ‖H1.Φ2‖ = ‖H2.Φ2‖ := by
  rw [gramMatrix, gramMatrix] at h
  have h1 := congrArg (fun x => x 1 1) h
  simp [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Fin.isValue] at h1
  rw [sq_eq_sq_iff_eq_or_eq_neg] at h1
  rcases h1 with h1 | h1
  · simpa using h1
  · erw [← RCLike.ofReal_neg] at h1
    have hnorm1 : 0 ≤ ‖H1.Φ2‖ := norm_nonneg H1.Φ2
    have hnorm2 : 0 ≤ ‖H2.Φ2‖ := norm_nonneg H2.Φ2
    have hl : ‖H1.Φ2‖ = (-‖H2.Φ2‖) := Eq.symm
      ((fun {z w} => Complex.ofReal_inj.mp) (id (Eq.symm h1)))
    grind

@[simp]
lemma gaugeGroupI_smul_gramMatrix (g : StandardModel.GaugeGroupI) (H : TwoHiggsDoublet) :
    (g • H).gramMatrix = H.gramMatrix := by
  rw [gramMatrix, gramMatrix, gaugeGroupI_smul_fst, gaugeGroupI_smul_snd]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma gramMatrix_det_eq (H : TwoHiggsDoublet) :
    H.gramMatrix.det = ‖H.Φ1‖ ^ 2 * ‖H.Φ2‖ ^ 2 - ‖⟪H.Φ1, H.Φ2⟫_ℂ‖ ^ 2 := by
  rw [gramMatrix, Matrix.det_fin_two]
  simp only [inner_self_eq_norm_sq_to_K, Complex.coe_algebraMap, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
    sub_right_inj]
  rw [← Complex.conj_mul']
  simp only [inner_conj_symm]

lemma gramMatrix_det_eq_real (H : TwoHiggsDoublet) :
    H.gramMatrix.det.re = ‖H.Φ1‖ ^ 2 * ‖H.Φ2‖ ^ 2 - ‖⟪H.Φ1, H.Φ2⟫_ℂ‖ ^ 2 := by
  rw [gramMatrix_det_eq]
  simp [← Complex.ofReal_pow, Complex.ofReal_im]

lemma gramMatrix_det_nonneg (H : TwoHiggsDoublet) :
    0 ≤ H.gramMatrix.det.re := by
  rw [gramMatrix_det_eq_real]
  simp only [sub_nonneg]
  convert inner_mul_inner_self_le (𝕜 := ℂ) H.Φ1 H.Φ2
  · simp [sq, norm_inner_symm]
  · exact norm_sq_eq_re_inner H.Φ1
  · exact norm_sq_eq_re_inner H.Φ2

lemma gramMatrix_tr_nonneg (H : TwoHiggsDoublet) :
    0 ≤ H.gramMatrix.trace.re := by
  rw [gramMatrix, Matrix.trace_fin_two]
  simp only [inner_self_eq_norm_sq_to_K, Complex.coe_algebraMap, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
    Complex.add_re]
  apply add_nonneg
  · rw [← Complex.ofReal_pow, Complex.ofReal_re]
    exact sq_nonneg ‖H.Φ1‖
  · rw [← Complex.ofReal_pow, Complex.ofReal_re]
    exact sq_nonneg ‖H.Φ2‖

lemma gaugeGroupI_exists_fst_eq {H : TwoHiggsDoublet} (h1 : H.Φ1 ≠ 0) :
    ∃ g : StandardModel.GaugeGroupI,
      g • H.Φ1 = (!₂[‖H.Φ1‖, 0] : HiggsVec) ∧
      (g • H.Φ2) 0 = ⟪H.Φ1, H.Φ2⟫_ℂ / ‖H.Φ1‖ ∧
      ‖(g • H.Φ2) 1‖ = Real.sqrt (H.gramMatrix.det.re) / ‖H.Φ1‖ := by
  rw [gramMatrix_det_eq_real]
  obtain ⟨g, h⟩ := (HiggsVec.mem_orbit_gaugeGroupI_iff (H.Φ1) (!₂[‖H.Φ1‖, 0] : HiggsVec)).mpr
    (by simp [@PiLp.norm_eq_of_L2])
  use g
  simp at h
  simp [h]
  have h_fst : (g • H.Φ2).ofLp 0 = ⟪H.Φ1, H.Φ2⟫_ℂ / ‖H.Φ1‖ := by
    have h2 : ⟪H.Φ1, H.Φ2⟫_ℂ = ⟪g • H.Φ1, g • H.Φ2⟫_ℂ := by
      simp
    rw [h] at h2
    conv_rhs at h2 =>
      simp [PiLp.inner_apply]
    rw [h2]
    have hx : (‖H.Φ1‖ : ℂ) ≠ 0 := by
      simp_all
    field_simp
  apply And.intro h_fst
  have hx : ‖g • H.Φ2‖ ^ 2 = ‖H.Φ2‖ ^ 2 := by
    simp
  rw [PiLp.norm_sq_eq_of_L2] at hx
  simp at hx
  have hx0 : ‖(g • H.Φ2).ofLp 1‖ ^ 2 = ‖H.Φ2‖ ^ 2 - ‖(g • H.Φ2).ofLp 0‖ ^ 2 := by
    rw [← hx]
    simp
  have h0 : ‖(g • H.Φ2) 1‖ ^ 2 = (‖H.Φ1‖ ^ 2 * ‖H.Φ2‖ ^ 2 - ‖⟪H.Φ1, H.Φ2⟫_ℂ‖ ^ 2) / ‖H.Φ1‖ ^ 2 := by
    field_simp
    rw [hx0, h_fst]
    simp only [Fin.isValue, Complex.norm_div, Complex.norm_real, norm_norm]
    ring_nf
    field_simp
  have habc (a b c : ℝ) (ha : 0 ≤ a) (hx : a ^ 2 = b / c ^2) (hc : c ≠ 0) (hc : 0 < c) :
      a = Real.sqrt b / c := by
    field_simp
    symm
    have hb : b = a ^ 2 * c ^ 2 := by
      rw [hx]
      field_simp
    subst hb
    rw [Real.sqrt_eq_iff_eq_sq]
    · ring
    · positivity
    · positivity
  apply habc
  rw [h0]
  ring_nf
  · exact norm_ne_zero_iff.mpr h1
  · simpa using h1
  · exact norm_nonneg ((g • H.Φ2).ofLp 1)

lemma gaugeGroupI_exists_fst_eq_snd_eq {H : TwoHiggsDoublet} (h1 : H.Φ1 ≠ 0) :
    ∃ g : StandardModel.GaugeGroupI,
      g • H.Φ1 = (!₂[‖H.Φ1‖, 0] : HiggsVec) ∧
      g • H.Φ2 = (!₂[⟪H.Φ1, H.Φ2⟫_ℂ / ‖H.Φ1‖, √(H.gramMatrix.det.re) / ‖H.Φ1‖] : HiggsVec) := by
  obtain ⟨g, h_fst, h_snd_0, h_snd_1⟩ := gaugeGroupI_exists_fst_eq h1
  obtain ⟨k, h1, h2, h3⟩ := HiggsVec.gaugeGroupI_smul_phase_snd (g • H.Φ2)
  use k * g
  apply And.intro
  · rw [mul_smul, h_fst, h3]
  · rw [mul_smul]
    ext i
    fin_cases i
    · simp
      rw [h2, h_snd_0]
    · simp
      rw [h1, h_snd_1]
      simp

lemma mem_orbit_gaugeGroupI_iff_gramMatrix (H1 H2 : TwoHiggsDoublet) :
    H1 ∈ MulAction.orbit GaugeGroupI H2 ↔ H1.gramMatrix = H2.gramMatrix := by
  apply Iff.intro
  · intro h
    obtain ⟨g, hg⟩ := h
    simp at hg
    simp [← hg]
  by_cases Φ1_zero : H1.Φ1 = 0
  · intro h
    obtain ⟨g1, hg1⟩ := (HiggsVec.mem_orbit_gaugeGroupI_iff (H1.Φ2) (!₂[‖H1.Φ2‖, 0] : HiggsVec)).mpr
      (by simp [@PiLp.norm_eq_of_L2])
    obtain ⟨g2, hg2⟩ := (HiggsVec.mem_orbit_gaugeGroupI_iff (H2.Φ2) (!₂[‖H2.Φ2‖, 0] : HiggsVec)).mpr
      (by simp [@PiLp.norm_eq_of_L2])
    use g1⁻¹ * g2
    simp only
    ext:1
    · simp [Φ1_zero]
      have hnorm : ‖H2.Φ1‖ = ‖H1.Φ1‖ := by
        symm
        rw [← eq_fst_norm_of_eq_gramMatrix h]
      simp [Φ1_zero] at hnorm
      simp [hnorm]
    · simp [mul_smul]
      refine inv_smul_eq_iff.mpr ?_
      simp at hg1 hg2
      simp [hg1, hg2]
      exact eq_snd_norm_of_eq_gramMatrix (id (Eq.symm h))
  · intro h
    obtain ⟨g1, H1_Φ1, H1_Φ2⟩ := gaugeGroupI_exists_fst_eq_snd_eq (H := H1) Φ1_zero
    have Φ2_nezero : H2.Φ1 ≠ 0 := by
      intro hzero
      have hnorm : ‖H1.Φ1‖ = ‖H2.Φ1‖ := by
        rw [← eq_fst_norm_of_eq_gramMatrix h]
      simp [hzero] at hnorm
      simp [hnorm] at Φ1_zero
    obtain ⟨g2, H2_Φ1, H2_Φ2⟩ := gaugeGroupI_exists_fst_eq_snd_eq (H := H2) Φ2_nezero
    use g1⁻¹ * g2
    simp only
    ext:1
    · simp [mul_smul]
      refine inv_smul_eq_iff.mpr ?_
      simp [H1_Φ1, H2_Φ1]
      apply eq_fst_norm_of_eq_gramMatrix (id (Eq.symm h))
    · simp [mul_smul]
      refine inv_smul_eq_iff.mpr ?_
      simp [H1_Φ2, H2_Φ2]
      apply And.intro
      · congr 1
        · symm
          exact congrArg (fun x => x 1 0) h
        · simp only [Complex.ofReal_inj]
          exact eq_fst_norm_of_eq_gramMatrix (id (Eq.symm h))
      · congr 2
        · simp [h]
        · exact eq_fst_norm_of_eq_gramMatrix (id (Eq.symm h))

/-!

### A.1. Gram matrix is surjective

-/

open ComplexConjugate

lemma gramMatrix_surjective_det_tr (K : Matrix (Fin 2) (Fin 2) ℂ)
    (hKs : IsSelfAdjoint K) (hKdet : 0 ≤ K.det.re) (hKtr : 0 ≤ K.trace.re) :
    ∃ H : TwoHiggsDoublet, H.gramMatrix = K := by
  /- Basic results related to K. -/
  have hK_explicit : K = !![K 0 0, K 0 1; K 1 0, K 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hK_star_explicit : star K = !![star (K 0 0), star (K 1 0); star (K 0 1), star (K 1 1)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [isSelfAdjoint_iff, hK_star_explicit] at hKs
  conv_rhs at hKs => rw [hK_explicit]
  simp at hKs
  have hK_explicit2 : K = !![((K 0 0).re : ℂ), K 0 1; conj (K 0 1), ((K 1 1).re : ℂ)] := by
    conv_lhs => rw [hK_explicit]
    simp [hKs]
    apply And.intro
    · refine Eq.symm ((fun {z} => Complex.conj_eq_iff_re.mp) ?_)
      simp [hKs]
    · refine Eq.symm ((fun {z} => Complex.conj_eq_iff_re.mp) ?_)
      simp [hKs]
  clear hK_explicit hK_star_explicit hKs
  generalize (K 0 0).re = a at *
  generalize (K 1 1).re = b at *
  generalize K 0 1 = c at *
  have det_eq_abc : K.det = a * b - ‖c‖ ^ 2 := by
    simp [hK_explicit2]
    rw [Complex.mul_conj']
  have tra_eq_abc : K.trace.re = a + b := by
    simp [hK_explicit2]
  simp [det_eq_abc, ← Complex.ofReal_pow] at hKdet
  rw [tra_eq_abc] at hKtr
  rw [hK_explicit2]
  clear hK_explicit2 det_eq_abc tra_eq_abc
  have ha_nonneg : 0 ≤ a := by nlinarith
  have hb_nonneg : 0 ≤ b := by nlinarith
  /- Splitting the cases into a = 0 and other. -/
  by_cases ha : a = 0
  · use ⟨(0 : HiggsVec), (!₂[√b, 0] : HiggsVec)⟩
    subst ha
    simp_all
    subst hKdet
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gramMatrix]
    simp [PiLp.norm_eq_of_L2, ← Complex.ofReal_pow]
    exact Real.sq_sqrt hb_nonneg
  /- The case when a ≠ 0. -/
  have h1 : (√a : ℂ) ≠ 0 := by
      simp_all
  use ⟨(!₂[√a, 0] : HiggsVec), !₂[conj c/ √a, √(a * b - ‖c‖ ^ 2) / √a]⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gramMatrix, PiLp.norm_eq_of_L2, ← Complex.ofReal_pow]
  · exact Real.sq_sqrt ha_nonneg
  · simp [PiLp.inner_apply]
    field_simp
  · simp [PiLp.inner_apply]
    field_simp
  · rw [Real.sq_sqrt, abs_of_nonneg, abs_of_nonneg]
    field_simp
    rw [Real.sq_sqrt, Real.sq_sqrt]
    ring
    · positivity
    · nlinarith
    · exact Real.sqrt_nonneg (a * b - ‖c‖ ^ 2)
    · positivity
    · positivity

/-!

## B. The Gram vector

-/

/-- A real vector containing the components of the Gram matrix in the Pauli basis. -/
noncomputable def gramVector (H : TwoHiggsDoublet) : Fin 1 ⊕ Fin 3 → ℝ := fun μ =>
  2 * PauliMatrix.pauliBasis.repr ⟨gramMatrix H, gramMatrix_selfAdjoint H⟩ μ

/-- The lemma manifesting the definitional equality for the gramVector. -/
lemma gramVector_eq (H : TwoHiggsDoublet) : H.gramVector = fun μ =>
    2 * PauliMatrix.pauliBasis.repr ⟨gramMatrix H, gramMatrix_selfAdjoint H⟩ μ := rfl

@[simp]
lemma gaugeGroupI_smul_fst_gramVector (g : StandardModel.GaugeGroupI)
    (H : TwoHiggsDoublet) (μ : Fin 1 ⊕ Fin 3) :
    (g • H).gramVector μ = H.gramVector μ := by
  rw [gramVector, gramVector]
  congr 1
  simp

lemma gramMatrix_eq_gramVector_sum_pauliMatrix (H : TwoHiggsDoublet) :
    gramMatrix H = (1 / 2 : ℝ) • ∑ μ, H.gramVector μ • PauliMatrix.pauliMatrix μ := by
  have h1 := congrArg (fun x => x.1) <|
    PauliMatrix.pauliBasis.sum_repr ⟨gramMatrix H, gramMatrix_selfAdjoint H⟩
  simp [-Module.Basis.sum_repr] at h1
  rw [← h1]
  simp [gramVector, smul_smul, Finset.smul_sum]
  congr 1
  · simp [PauliMatrix.pauliBasis, PauliMatrix.pauliSelfAdjoint]
  · simp [PauliMatrix.pauliBasis, PauliMatrix.pauliSelfAdjoint]

lemma gramMatrix_eq_component_gramVector (H : TwoHiggsDoublet) :
    gramMatrix H =
    !![(1 / 2 : ℂ) * (H.gramVector (Sum.inl 0) + H.gramVector (Sum.inr 2)),
      (1 / 2 : ℂ) * (H.gramVector (Sum.inr 0) - Complex.I * H.gramVector (Sum.inr 1));
      (1 / 2 : ℂ) * (H.gramVector (Sum.inr 0) + Complex.I * H.gramVector (Sum.inr 1)),
      (1 / 2 : ℂ) * (H.gramVector (Sum.inl 0) - H.gramVector (Sum.inr 2))] := by
  rw [gramMatrix_eq_gramVector_sum_pauliMatrix]
  simp only [one_div, PauliMatrix.pauliMatrix, Matrix.one_fin_two, Fintype.sum_sum_type,
    Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton, Matrix.smul_of,
    Matrix.smul_cons, Complex.real_smul, mul_one, smul_zero, Matrix.smul_empty, Fin.sum_univ_three,
    smul_neg, Matrix.of_add_of, Matrix.add_cons, Matrix.head_cons, add_zero, Matrix.tail_cons,
    Matrix.empty_add_empty, zero_add, smul_add, Complex.ofReal_inv, Complex.ofReal_ofNat,
    EmbeddingLike.apply_eq_iff_eq, Matrix.vecCons_inj, and_true]
  ring_nf
  simp

lemma gramVector_inl_eq_trace_gramMatrix (H : TwoHiggsDoublet) :
    H.gramVector (Sum.inl 0) = H.gramMatrix.trace.re := by
  rw [gramMatrix_eq_component_gramVector, Matrix.trace_fin_two]
  simp only [Fin.isValue, one_div, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one]
  ring_nf
  simp

lemma gramVector_inl_nonneg (H : TwoHiggsDoublet) :
    0 ≤ H.gramVector (Sum.inl 0) := by
  rw [gramVector_inl_eq_trace_gramMatrix]
  exact gramMatrix_tr_nonneg H

lemma normSq_Φ1_eq_gramVector (H : TwoHiggsDoublet) :
    ‖H.Φ1‖ ^ 2 = (1/2 : ℝ) * (H.gramVector (Sum.inl 0) + H.gramVector (Sum.inr 2)) := by
  trans (gramMatrix H 0 0).re
  · simp [gramMatrix]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  · rw [gramMatrix_eq_component_gramVector]
    simp

lemma normSq_Φ2_eq_gramVector (H : TwoHiggsDoublet) :
    ‖H.Φ2‖ ^ 2 = (1/2 : ℝ) * (H.gramVector (Sum.inl 0) - H.gramVector (Sum.inr 2)) := by
  trans (gramMatrix H 1 1).re
  · simp [gramMatrix]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  · rw [gramMatrix_eq_component_gramVector]
    simp

lemma Φ1_inner_Φ2_eq_gramVector (H : TwoHiggsDoublet) :
    (⟪H.Φ1, H.Φ2⟫_ℂ) = (1/2 : ℝ) * (H.gramVector (Sum.inr 0) +
    Complex.I * H.gramVector (Sum.inr 1)) := by
  trans (gramMatrix H 1 0)
  · simp [gramMatrix]
  · simp [gramMatrix_eq_component_gramVector]

lemma Φ2_inner_Φ1_eq_gramVector (H : TwoHiggsDoublet) :
    (⟪H.Φ2, H.Φ1⟫_ℂ) = (1/2 : ℝ) * (H.gramVector (Sum.inr 0) -
    Complex.I * H.gramVector (Sum.inr 1)) := by
  trans (gramMatrix H 0 1)
  · simp [gramMatrix]
  · simp [gramMatrix_eq_component_gramVector]

open ComplexConjugate

lemma Φ1_inner_Φ2_normSq_eq_gramVector (H : TwoHiggsDoublet) :
    ‖⟪H.Φ1, H.Φ2⟫_ℂ‖ ^ 2 =
    (1/4 : ℝ) * (H.gramVector (Sum.inr 0) ^ 2 + H.gramVector (Sum.inr 1) ^ 2) := by
  trans (⟪H.Φ1, H.Φ2⟫_ℂ * conj ⟪H.Φ1, H.Φ2⟫_ℂ).re
  · rw [Complex.mul_conj', ← Complex.ofReal_pow]
    rfl
  rw [conj_inner_symm H.Φ2 H.Φ1]
  rw [Φ1_inner_Φ2_eq_gramVector, Φ2_inner_Φ1_eq_gramVector]
  simp only [one_div, Complex.ofReal_inv, Complex.ofReal_ofNat, Fin.isValue, Complex.mul_re,
    Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self', Complex.add_re,
    Complex.ofReal_re, Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self,
    add_zero, Complex.inv_im, Complex.im_ofNat, neg_zero, zero_div, Complex.add_im, Complex.mul_im,
    one_mul, zero_add, sub_zero, Complex.sub_re, Complex.sub_im, zero_sub, mul_neg, sub_neg_eq_add]
  ring

lemma gramVector_inl_zero_eq (H : TwoHiggsDoublet) :
    H.gramVector (Sum.inl 0) = ‖H.Φ1‖ ^ 2 + ‖H.Φ2‖ ^ 2 := by
  rw [normSq_Φ1_eq_gramVector, normSq_Φ2_eq_gramVector]
  ring

lemma gramVector_inl_zero_eq_gramMatrix (H : TwoHiggsDoublet) :
    H.gramVector (Sum.inl 0) = (H.gramMatrix 0 0).re + (H.gramMatrix 1 1).re := by
  simp [gramVector_inl_zero_eq, gramMatrix, ← Complex.ofReal_pow, Complex.ofReal_re]

lemma gramVector_inr_zero_eq (H : TwoHiggsDoublet) :
    H.gramVector (Sum.inr 0) = 2 * (⟪H.Φ1, H.Φ2⟫_ℂ).re := by
  rw [Φ1_inner_Φ2_eq_gramVector]
  simp

lemma gramVector_inr_zero_eq_gramMatrix (H : TwoHiggsDoublet) :
    H.gramVector (Sum.inr 0) = 2 * (H.gramMatrix 1 0).re := by
  rw [gramMatrix, gramVector_inr_zero_eq]
  simp

lemma gramVector_inr_one_eq (H : TwoHiggsDoublet) :
    H.gramVector (Sum.inr 1) = 2 * (⟪H.Φ1, H.Φ2⟫_ℂ).im := by
  rw [Φ1_inner_Φ2_eq_gramVector]
  simp

lemma gramVector_inr_one_eq_gramMatrix (H : TwoHiggsDoublet) :
    H.gramVector (Sum.inr 1) = 2 * (H.gramMatrix 1 0).im := by
  rw [gramMatrix, gramVector_inr_one_eq]
  simp

lemma gramVector_inr_two_eq (H : TwoHiggsDoublet) :
    H.gramVector (Sum.inr 2) = ‖H.Φ1‖ ^ 2 - ‖H.Φ2‖ ^ 2 := by
  rw [normSq_Φ1_eq_gramVector, normSq_Φ2_eq_gramVector]
  ring

lemma gramVector_inr_two_eq_gramMatrix (H : TwoHiggsDoublet) :
    H.gramVector (Sum.inr 2) = (H.gramMatrix 0 0).re - (H.gramMatrix 1 1).re := by
  simp [gramVector_inr_two_eq, gramMatrix, ← Complex.ofReal_pow, Complex.ofReal_re]

lemma gramMatrix_det_eq_gramVector (H : TwoHiggsDoublet) :
    H.gramMatrix.det.re =
    (1/4 : ℝ) * (H.gramVector (Sum.inl 0) ^ 2 -
    ∑ μ : Fin 3, H.gramVector (Sum.inr μ) ^ 2) := by
  rw [gramMatrix_det_eq_real]
  simp [normSq_Φ1_eq_gramVector, normSq_Φ2_eq_gramVector, Φ1_inner_Φ2_normSq_eq_gramVector,
    Fin.sum_univ_three]
  ring

lemma gramVector_inr_sum_sq_le_inl (H : TwoHiggsDoublet) :
    ∑ μ : Fin 3, H.gramVector (Sum.inr μ) ^ 2 ≤ H.gramVector (Sum.inl 0) ^ 2 := by
  apply sub_nonneg.mp
  trans (4 : ℝ) * H.gramMatrix.det.re
  · apply mul_nonneg
    · norm_num
    · exact gramMatrix_det_nonneg H
  apply (le_of_eq _)
  rw [gramMatrix_det_eq_gramVector]
  ring

lemma gramVector_surjective (v : Fin 1 ⊕ Fin 3 → ℝ)
    (h_inl : 0 ≤ v (Sum.inl 0))
    (h_det : ∑ μ : Fin 3, v (Sum.inr μ) ^ 2 ≤ v (Sum.inl 0) ^ 2) :
    ∃ H : TwoHiggsDoublet, H.gramVector = v := by
  let K := !![(1 / 2 : ℂ) * (v (Sum.inl 0) + v (Sum.inr 2)),
      (1 / 2 : ℂ) * (v (Sum.inr 0) - Complex.I * v (Sum.inr 1));
      (1 / 2 : ℂ) * (v (Sum.inr 0) + Complex.I * v (Sum.inr 1)),
      (1 / 2 : ℂ) * (v (Sum.inl 0) - v (Sum.inr 2))]
  have K_star : star K = !![(1 / 2 : ℂ) * (v (Sum.inl 0) + v (Sum.inr 2)),
      (1 / 2 : ℂ) * (v (Sum.inr 0) - Complex.I * v (Sum.inr 1));
      (1 / 2 : ℂ) * (v (Sum.inr 0) + Complex.I * v (Sum.inr 1)),
      (1 / 2 : ℂ) * (v (Sum.inl 0) - v (Sum.inr 2))] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [K]
    ring
  have hK_selfAdjoint : IsSelfAdjoint K := by
    exact K_star
  have hK_det_nonneg : 0 ≤ K.det.re := by
    simp [K]
    simp [Fin.sum_univ_three] at h_det
    linarith
  have hK_tr : 0 ≤ K.trace.re := by
    simp [K]
    linarith
  obtain ⟨H, hH⟩ := gramMatrix_surjective_det_tr K hK_selfAdjoint hK_det_nonneg hK_tr
  use H
  ext μ
  fin_cases μ
  · simp [gramVector_inl_zero_eq_gramMatrix, hH, K]
    ring
  · simp [gramVector_inr_zero_eq_gramMatrix, hH, K]
  · simp [gramVector_inr_one_eq_gramMatrix, hH, K]
  · simp [gramVector_inr_two_eq_gramMatrix, hH, K]
    ring

lemma mem_orbit_gaugeGroupI_iff_gramVector (H1 H2 : TwoHiggsDoublet) :
    H1 ∈ MulAction.orbit GaugeGroupI H2 ↔ H1.gramVector = H2.gramVector := by
  rw [mem_orbit_gaugeGroupI_iff_gramMatrix]
  constructor
  · intro h
    rw [gramVector_eq, gramVector_eq]
    funext μ
    congr
  · intro h
    rw [gramMatrix_eq_gramVector_sum_pauliMatrix,
      gramMatrix_eq_gramVector_sum_pauliMatrix, h]

end TwoHiggsDoublet
