/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.CompoundMatrix
public import QuantumInfo.ForMathlib.HermitianMat.LogExp
public import QuantumInfo.ForMathlib.HermitianMat.Sqrt
public import QuantumInfo.ForMathlib.HermitianMat.Unitary
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

variable {d d₂ 𝕜 : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]
variable [RCLike 𝕜]
variable {A B : HermitianMat d 𝕜} {x q r : ℝ}

/-! # Matrix Powers With Real Exponents

This file defines real powers of finite-dimensional Hermitian matrices by continuous
functional calculus:

`A ^ r = A.cfc (fun x => x ^ r)`.

The scalar function is `Real.rpow`, so this is a total operation on Hermitian matrices.
For positive semidefinite matrices it has the expected spectral meaning. For negative
exponents on singular matrices it follows the `Real.rpow` convention, so zero eigenvalues
remain zero; use positive-definiteness hypotheses for inverse laws.

Main results:
* algebraic and spectral lemmas for real powers;
* continuity in the exponent and in the matrix argument;
* the Loewner-Heinz monotonicity theorem for `0 < q <= 1`;
* Lieb-Thirring and Rotfel'd trace inequalities for `0 < p <= 1`.
-/

noncomputable section
namespace HermitianMat

/-- Real powers of Hermitian matrices via continuous functional calculus.

This is the total functional-calculus definition `A.cfc (fun x => x ^ r)`. For positive
semidefinite `A`, this is the usual spectral power. For negative exponents on singular
matrices, zero eigenvalues stay zero because this uses `Real.rpow`. -/
def rpow (A : HermitianMat d 𝕜) (r : ℝ) : HermitianMat d 𝕜 :=
  A.cfc (Real.rpow · r)

instance instRPow : Pow (HermitianMat d 𝕜) ℝ :=
  ⟨rpow⟩

theorem rpow_conj_unitary (A : HermitianMat d 𝕜) (U : Matrix.unitaryGroup d 𝕜) (r : ℝ) :
    (HermitianMat.conj U.val A) ^ r = HermitianMat.conj U.val (A ^ r) := by
  exact A.cfc_conj_unitary (· ^ r) U

theorem pow_eq_rpow : A ^ r = A.rpow r :=
  rfl

theorem rpow_eq_cfc : A ^ r = A.cfc (· ^ r) :=
  rfl

theorem diagonal_pow (f : d → ℝ) :
    (diagonal 𝕜 f) ^ r = diagonal 𝕜 (fun i ↦ (f i) ^ r) := by
  simp [rpow_eq_cfc]
  rfl

@[fun_prop]
theorem rpow_const_continuous {r : ℝ} (hr : 0 ≤ r) : Continuous (fun A : HermitianMat d ℂ ↦ A ^ r) := by
  exact HermitianMat.cfc_continuous (Real.continuous_rpow_const hr)

@[fun_prop]
theorem const_rpow_continuous [NonSingular A] : Continuous (fun r : ℝ ↦ A ^ r) := by
  rw [← continuousOn_univ]
  apply continuousOn_cfc_fun_nonsingular
  simp only [Real.rpow_eq_pow]
  fun_prop (disch := assumption)

/--
For a fixed Hermitian matrix A, the function x ↦ A^x is continuous for x > 0.
-/
@[fun_prop]
theorem continuousOn_rpow_pos (A : HermitianMat d ℂ) : ContinuousOn (fun x : ℝ ↦ A ^ x) (Set.Ioi 0) := by
  apply A.continuousOn_cfc_fun (hA := subset_rfl)
  intro i _ x hx
  exact (Real.continuousAt_const_rpow' hx.ne').continuousWithinAt

/--
For a fixed Hermitian matrix A, the function x ↦ A^x is continuous for x < 0.
-/
@[fun_prop]
theorem continuousOn_rpow_neg (A : HermitianMat d ℂ) : ContinuousOn (fun x : ℝ ↦ A ^ x) (Set.Iio 0) := by
  apply A.continuousOn_cfc_fun (hA := subset_rfl)
  intro i _ x hx
  exact (Real.continuousAt_const_rpow' hx.ne).continuousWithinAt

@[simp]
theorem rpow_one : A ^ (1 : ℝ) = A := by
  simp [rpow_eq_cfc]

/--
Functional calculus of Real.sqrt is equal to functional calculus of x^(1/2).
-/
lemma sqrt_eq_cfc_rpow_half (A : HermitianMat d 𝕜)  :
    A.sqrt = A.cfc (fun x ↦ x ^ (1/2 : ℝ)) := by
  rw [sqrt, cfc_eq_cfc_iff_eqOn]
  intro
  simp [Real.sqrt_eq_rpow]

@[simp]
theorem one_rpow : (1 : HermitianMat d 𝕜) ^ r = 1 := by
  rcases isEmpty_or_nonempty d
  · apply Subsingleton.allEq
  · nth_rw 2 [← HermitianMat.cfc_id (1 : HermitianMat d 𝕜)]
    rw [rpow_eq_cfc]
    simp

@[simp]
lemma rpow_zero (A : HermitianMat d 𝕜) : A ^ (0 : ℝ) = 1 := by
  simp [rpow_eq_cfc]

lemma rpow_diagonal (a : d → ℝ) (r : ℝ) :
  (diagonal ℂ a) ^ r = diagonal ℂ (fun i => a i ^ r) := by
    exact cfc_diagonal _ _

/-- Keeps in line with our simp-normal form for moving reindex outwards. -/
@[simp]
theorem reindex_rpow (e : d ≃ d₂) :
    A.reindex e ^ r = (A ^ r).reindex e := by
  apply A.cfc_reindex

theorem mat_rpow_add (hA : 0 ≤ A) {p q : ℝ} (hpq : p + q ≠ 0) :
    (A ^ (p + q)).mat = (A ^ p).mat * (A ^ q).mat := by
  simp only [rpow_eq_cfc, ← mat_cfc_mul, ← HermitianMat.ext_iff]
  exact cfc_congr_of_nonneg hA (fun i hi ↦ Real.rpow_add' hi hpq)

theorem rpow_mul (hA : 0 ≤ A) {p q : ℝ} : A ^ (p * q) = (A ^ p) ^ q := by
  simp only [rpow_eq_cfc, ← cfc_comp]
  exact cfc_congr_of_nonneg hA (fun i hi ↦ Real.rpow_mul hi p q)

theorem conj_rpow (hA : 0 ≤ A) (hq : q ≠ 0) (hqr : r + 2 * q ≠ 0) :
    (A ^ r).conj (A ^ q) = A ^ (r + 2 * q) := by
  simp only [rpow_eq_cfc, cfc_conj]
  refine cfc_congr_of_nonneg hA (fun i hi ↦ ?_)
  rw [pow_two, Real.rpow_add' hi hqr, two_mul, Real.rpow_add' hi (by simpa)]
  rfl

theorem pow_half_mul (hA : 0 ≤ A) :
    (A ^ (1/2 : ℝ)).mat * (A ^ (1/2 : ℝ)).mat = A := by
  rw [← mat_rpow_add hA]
  · norm_num
  · norm_num

theorem rpow_pos {A : HermitianMat d 𝕜} (hA : 0 < A) {p : ℝ} : 0 < A ^ p := by
  convert! cfc_pos_of_pos hA _ _
  · exact fun i hi => Real.rpow_pos_of_pos hi _
  · rcases eq_or_ne p 0 with h | h <;> simp [h]

theorem rpow_nonneg (hA : 0 ≤ A) {p : ℝ} : 0 ≤ A ^ p := by
  apply cfc_nonneg_of_nonneg hA
  exact fun i hi => Real.rpow_nonneg hi p

open ComplexOrder in
theorem inv_eq_rpow_neg_one (hA : A.mat.PosDef) : A⁻¹ = A ^ (-1 : ℝ) := by
  have := nonSingular_of_posDef hA
  rw [← cfc_inv, rpow_eq_cfc]
  simp_rw [Real.rpow_neg_one]

open ComplexOrder in
theorem sandwich_self (hB : B.mat.PosDef) :
    (B.conj (B ^ (-1/2 : ℝ)).mat) = 1 := by
  have hB_inv_sqrt : (B ^ (-1 / 2 : ℝ)).mat * (B ^ (-1 / 2 : ℝ)).mat = (B ^ (-1 : ℝ)).mat := by
    rw [ ← mat_rpow_add ] <;> norm_num
    rw [zero_le_iff]
    exact hB.posSemidef
  have hB_inv : (B ^ (-1 : ℝ)).mat = B.mat⁻¹ := by
    rw [← inv_eq_rpow_neg_one hB, mat_inv]
  rw [ hB_inv ] at hB_inv_sqrt;
  ext1
  simp [mul_assoc];
  rw [ ← Matrix.mul_assoc, mul_eq_one_comm.mp ];
  rw [ ← Matrix.mul_assoc, hB_inv_sqrt, Matrix.nonsing_inv_mul _ ];
  exact isUnit_iff_ne_zero.mpr hB.det_pos.ne'

open ComplexOrder in
lemma rpow_inv_eq_neg_rpow (hA : A.mat.PosDef) (p : ℝ) : (A ^ p)⁻¹ = A ^ (-p) := by
  --TODO cleanup
  ext i j;
  have h_inv : (A ^ p).mat * (A ^ (-p)).mat = 1 := by
    have h_inv : (A ^ p).mat * (A ^ (-p)).mat = 1 := by
      have h_pow : (A ^ p).mat = A.cfc (fun x => x ^ p) := by
        exact rfl
      have h_pow_neg : (A ^ (-p)).mat = A.cfc (fun x => x ^ (-p)) := by
        exact rfl
      have h_inv : (A ^ p).mat * (A ^ (-p)).mat = A.cfc (fun x => x ^ p * x ^ (-p)) := by
        rw [ h_pow, h_pow_neg, ← mat_cfc_mul ];
        rfl;
      have h_inv : (A ^ p).mat * (A ^ (-p)).mat = A.cfc (fun x => 1) := by
        rw [ h_inv ];
        refine' congr_arg _ ( cfc_congr_of_posDef hA _ );
        exact fun x hx => by simp [ ← Real.rpow_add hx ] ;
      rw [ h_inv, cfc_const ] ; norm_num;
    exact h_inv;
  -- By definition of matrix inverse, if $(A^p) * (A^{-p}) = 1$, then $(A^{-p})$ is the inverse of $(A^p)$.
  have h_inv_def : (A ^ p).mat⁻¹ = (A ^ (-p)).mat := by
    exact Matrix.inv_eq_right_inv h_inv;
  convert! congr_fun ( congr_fun h_inv_def i ) j using 1

open ComplexOrder in
lemma sandwich_le_one (hB : B.mat.PosDef) (h : A ≤ B) :
    (A.conj (B ^ (-1/2 : ℝ)).mat) ≤ 1 := by
  exact le_trans (conj_mono h) (sandwich_self hB).le

open ComplexOrder in
lemma rpow_neg_mul_rpow_self (hA : A.mat.PosDef) (p : ℝ) :
    (A ^ (-p)).mat * (A ^ p).mat = 1 := by
  have := rpow_inv_eq_neg_rpow hA p;
  rw [ ← this ];
  -- Since $A$ is positive definite, $A^p$ is also positive definite.
  have h_pos_def : (A ^ p).mat.PosDef := by
    have h_pos_def : ∀ p : ℝ, A.mat.PosDef → (A ^ p).mat.PosDef := by
      intro p hA_pos_def
      have h_eigenvalues_pos : ∀ i, 0 < (A.H.eigenvalues i) ^ p := by
        exact fun i => Real.rpow_pos_of_pos ( by exact Matrix.PosDef.eigenvalues_pos hA i ) _;
      have h_eigenvalues_pos : (A ^ p).mat.PosDef ↔ ∀ i, 0 < (A ^ p).H.eigenvalues i := by
        exact Matrix.IsHermitian.posDef_iff_eigenvalues_pos (H (A ^ p));
      have h_eigenvalues_pos : ∃ e : d ≃ d, (A ^ p).H.eigenvalues = fun i => (A.H.eigenvalues (e i)) ^ p := by
        exact Matrix.IsHermitian.cfc_eigenvalues (H A) fun x => x.rpow p;
      aesop;
    exact h_pos_def p hA;
  convert! Matrix.nonsing_inv_mul _ _;
  exact isUnit_iff_ne_zero.mpr h_pos_def.det_pos.ne'

open ComplexOrder in
lemma isUnit_rpow_toMat (hA : A.mat.PosDef) (p : ℝ) : IsUnit (A ^ p).mat := by
  have hA_inv : IsUnit (A ^ (-p)).mat := by
    have hA_inv : (A ^ (-p)).mat * (A ^ p).mat = 1 := by
      exact rpow_neg_mul_rpow_self hA p
    exact IsUnit.of_mul_eq_one _ hA_inv
  -- Since $(A^{-p}) (A^p) = 1$, we have that $(A^p)$ is the inverse of $(A^{-p})$.
  have hA_inv : (A ^ p).mat = (A ^ (-p)).mat⁻¹ := by
    have hA_inv : (A ^ (-p)).mat * (A ^ p).mat = 1 := by
      exact rpow_neg_mul_rpow_self hA p;
    exact Eq.symm (Matrix.inv_eq_right_inv hA_inv);
  aesop

open ComplexOrder in
lemma sandwich_inv (hB : B.mat.PosDef) :
    (A.conj (B ^ (-1/2 : ℝ)).mat)⁻¹ = A⁻¹.conj (B ^ (1/2 : ℝ)).mat := by
  have h_inv : (B ^ (-1 / 2 : ℝ)).mat⁻¹ = (B ^ (1 / 2 : ℝ)).mat := by
    apply Matrix.inv_eq_right_inv
    rw [← rpow_neg_mul_rpow_self hB (1 / 2), neg_div 2 1]
  simp [inv_conj (isUnit_rpow_toMat hB _), h_inv]

theorem ker_rpow_eq_of_nonneg {A : HermitianMat d ℂ} (hA : 0 ≤ A) (hp : r ≠ 0):
    (A ^ r).ker = A.ker := by
  apply ker_cfc_eq_ker_nonneg hA
  grind [Real.rpow_eq_zero_iff_of_nonneg, Real.rpow_eq_pow]

theorem ker_rpow_le_of_nonneg {A : HermitianMat d ℂ} (hA : 0 ≤ A) :
    (A ^ r).ker ≤ A.ker := by
  apply ker_cfc_le_ker_nonneg hA
  grind [Real.rpow_eq_zero_iff_of_nonneg, Real.rpow_eq_pow]

private lemma rpow_kron_diagonal
    (a : d → ℝ) (b : d₂ → ℝ) (r : ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) :
    ((diagonal ℂ a) ⊗ₖ (diagonal ℂ b)) ^ r =
    ((diagonal ℂ a) ^ r) ⊗ₖ ((diagonal ℂ b) ^ r) := by
  simp only [kronecker_diagonal, rpow_diagonal]
  congr! 2 with x
  apply Real.mul_rpow (ha x.1) (hb x.2)

set_option backward.isDefEq.respectTransparency false in
open scoped Kronecker in
omit [DecidableEq d] [DecidableEq d₂] in
lemma conj_kron
  (A : Matrix d d 𝕜) (B : Matrix d₂ d₂ 𝕜) (C : HermitianMat d 𝕜) (D : HermitianMat d₂ 𝕜) :
    conj (A ⊗ₖ B) (C ⊗ₖ D) = conj A C ⊗ₖ conj B D := by
  ext1
  simp [conj, Matrix.mul_kronecker_mul, Matrix.conjTranspose_kronecker]

lemma rpow_kron
    {A : HermitianMat d ℂ} {B : HermitianMat d₂ ℂ} (r : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (A ⊗ₖ B) ^ r = (A ^ r) ⊗ₖ (B ^ r) := by
  obtain ⟨U, a, ha, hA⟩ : ∃ U : 𝐔[d], ∃ a : d → ℝ, (∀ i, 0 ≤ a i) ∧ A = conj U.val (diagonal ℂ a) := by
    rw [zero_le_iff] at hA
    exact ⟨_, _, hA.eigenvalues_nonneg, eq_conj_diagonal A⟩
  obtain ⟨V, b, hb, hB⟩ : ∃ V : 𝐔[d₂], ∃ b : d₂ → ℝ, (∀ j, 0 ≤ b j) ∧ B = conj V.val (diagonal ℂ b) := by
    rw [zero_le_iff] at hB
    exact ⟨_, _, hB.eigenvalues_nonneg, eq_conj_diagonal B⟩
  have h_kron_r_pow : (A ⊗ₖ B) ^ r = conj (Matrix.unitary_kron U V).val ((diagonal ℂ a ⊗ₖ diagonal ℂ b) ^ r) := by
    subst hB hA
    rw [← rpow_conj_unitary, Matrix.unitary_kron, conj_kron]
  rw [h_kron_r_pow]
  subst A B
  have h_kron_r_pow_diag : (diagonal ℂ a ⊗ₖ diagonal ℂ b) ^ r = ((diagonal ℂ a) ^ r) ⊗ₖ ((diagonal ℂ b) ^ r) := by
    exact rpow_kron_diagonal a b r ha hb
  rw [h_kron_r_pow_diag, Matrix.unitary_kron]
  rw [rpow_conj_unitary, rpow_conj_unitary, ← conj_kron]

attribute [fun_prop] ContinuousAt.rpow ContinuousOn.rpow

lemma continuousOn_rpow_uniform {K : Set ℝ} (hK : IsCompact K) :
    ContinuousOn (fun r : ℝ ↦ UniformOnFun.ofFun {K} (fun t : ℝ ↦ t ^ r)) (Set.Ioi 0) := by
  refine continuousOn_of_forall_continuousAt fun r hr => ?_
  rw [Set.mem_Ioi] at hr
  apply UniformOnFun.tendsto_iff_tendstoUniformlyOn.mpr
  simp only [Set.mem_singleton_iff, UniformOnFun.toFun_ofFun, Metric.tendstoUniformlyOn_iff,
    Function.comp_apply, forall_eq]
  intro ε hεpos;
  have h_unif_cont : UniformContinuousOn (fun (p : ℝ × ℝ) => p.1 ^ p.2) (K ×ˢ Set.Icc (r / 2) (r * 2)) := by
    apply IsCompact.uniformContinuousOn_of_continuous
    · exact hK.prod CompactIccSpace.isCompact_Icc
    · refine continuousOn_of_forall_continuousAt fun p ⟨hp₁, ⟨hp₂₁, hp₂₂⟩⟩ ↦ ?_
      have _ : p.1 ≠ 0 ∨ 0 < p.2 := by right; linarith
      fun_prop (disch := assumption)
  rw [Metric.uniformContinuousOn_iff] at h_unif_cont
  obtain ⟨δ, hδpos, H⟩ := h_unif_cont ε hεpos
  filter_upwards [Ioo_mem_nhds (show r / 2 < r by linarith) (show r < r * 2 by linarith), Ioo_mem_nhds (show r - δ < r by linarith) (show r < r + δ by linarith)] with n ⟨_, _⟩ ⟨_, _⟩ x hx
  refine H (x, r) ⟨hx, ?_⟩ (x, n) ⟨hx, ?_⟩ ?_
  · constructor <;> linarith
  · constructor <;> linarith
  · have : |r - n| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
    simpa

section continuity

/-- Joint continuity of matrix rpow for Hermitian matrices with positive exponent -/
@[fun_prop]
theorem continuousOn_rpow_joint_nonneg_pos
    {X : Type*} [TopologicalSpace X]
    {A : X → HermitianMat d ℂ} {p : X → ℝ} {S : Set X}
    (hA : ContinuousOn A S) (hp : ContinuousOn p S)
    (hp_pos : ∀ x ∈ S, 0 < p x) :
    ContinuousOn (fun x ↦ A x ^ p x) S := by
  have h_cont_f : ContinuousOn (fun q : X × ℝ => q.2 ^ p q.1) (S ×ˢ Set.univ) := by
    -- fun_prop (disch := grind [Set.MapsTo]) --After BUMP - fix in discharger
    apply continuousOn_snd.rpow
    · exact hp.comp continuousOn_fst (fun x ↦ And.left)
    · grind
  simp_rw [rpow_eq_cfc]
  fun_prop (disch := simp)

end continuity

/-- For positive semidefinite `A`, `(A ^ 2) ^ (p / 2) = A ^ p` in functional calculus form.

The nonnegative exponent assumption is needed for continuity at zero. For positive definite
matrices, the same identity should hold for all real `p`. -/
theorem cfc_sq_rpow_eq_cfc_rpow
    (A : HermitianMat d 𝕜) (hA : 0 ≤ A) (p : ℝ) (hp : 0 ≤ p) :
    (A ^ 2).cfc (fun x => x ^ (p/2)) = A.cfc (fun x => x ^ p) := by
  have h_sqrt : (A ^ 2).cfc (fun x => x ^ (p / 2)) = (A.cfc (fun x => x ^ 2)).cfc (fun x => x ^ (p / 2)) := by
    convert rfl;
    exact cfc_pow A;
  rw [ h_sqrt ];
  have h_sqrt : ∀ (f g : ℝ → ℝ), Continuous f → Continuous g → ∀ (A : HermitianMat d 𝕜), (A.cfc f).cfc g = A.cfc (fun x => g (f x)) := by
    exact fun f g a a A => Eq.symm (cfc_comp_apply A f g);
  rw [ h_sqrt ];
  · have h_sqrt : ∀ x : ℝ, 0 ≤ x → (x ^ 2) ^ (p / 2) = x ^ p := by
      intro x hx
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul hx ]
      ring_nf
    exact cfc_congr_of_nonneg hA h_sqrt;
  · continuity;
  · exact continuous_id.rpow_const fun x => Or.inr <| div_nonneg hp (by norm_num)

/-- Tr[A^p] = ∑ᵢ λᵢ^p for a Hermitian matrix A. -/
lemma trace_rpow_eq_sum (A : HermitianMat d ℂ) (p : ℝ) :
    (A ^ p).trace = ∑ i, (A.H.eigenvalues i) ^ p := by
  exact A.trace_cfc_eq (· ^ p)

/-! ## Loewner-Heinz Theorem
The operator monotonicity of `x ↦ x ^ q` for `0 < q ≤ 1`:
if `A ≤ B` (in the Loewner order), then `A ^ q ≤ B ^ q`.
This is proved using the resolvent integral representation, following the same
approach as `log_mono` in `LogExp.lean`. The key identity is:
  `x ^ q = c_q * ∫ t in (0,∞), t ^ (q-1) * x / (x + t) dt`
where `c_q = sin(π q) / π`. Since each integrand `x / (x + t)` is operator
monotone (via `inv_antitone`), the integral is operator monotone.
-/
section LoewnerHeinz

variable {A B : HermitianMat d ℂ} {q : ℝ}

open MeasureTheory ComplexOrder Filter in
/-- Finite integral approximation for the rpow monotonicity proof.
    Same integrand as `logApprox` but with weight `t ^ q`. -/
noncomputable def rpowApprox (A : HermitianMat d ℂ) (q T : ℝ) : HermitianMat d ℂ :=
  ∫ t in (0)..T, t ^ q • ((1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (A + t • 1)⁻¹)

set_option backward.isDefEq.respectTransparency false in
open MeasureTheory ComplexOrder in
theorem rpowApprox_mono {A B : HermitianMat d ℂ} (hA : A.mat.PosDef) (hB : B.mat.PosDef)
    (hAB : A ≤ B) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T) :
    rpowApprox A q T ≤ rpowApprox B q T := by
  unfold HermitianMat.rpowApprox
  have h_integral_mono : ∀ᵐ t ∂Measure.restrict volume (Set.Ioc 0 T), t ^ q • ((1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (A + t • 1)⁻¹) ≤ t ^ q • ((1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (B + t • 1)⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have h_inv_antitone : (B + t • 1)⁻¹ ≤ (A + t • 1)⁻¹ := by
      apply inv_antitone
      · exact hA.add_posSemidef ( Matrix.PosSemidef.smul ( Matrix.PosSemidef.one ) ht.1.le )
      · exact add_le_add_left hAB _
    exact smul_le_smul_of_nonneg_left (sub_le_sub_left h_inv_antitone _) (Real.rpow_nonneg ht.1.le q)
  have h_cont_tq : ContinuousOn (fun t : ℝ => t ^ q) (Set.Icc 0 T) := by
    exact continuousOn_id.rpow_const fun _ _ => Or.inr hq
  have h_cont_const :
      ContinuousOn (fun t : ℝ => (1 + t)⁻¹ • (1 : HermitianMat d ℂ)) (Set.Icc 0 T) := by
    exact ((continuousOn_const.add continuousOn_id).inv₀
      (fun t ht => by
        change (1 : ℝ) + t ≠ 0
        linarith [ht.1])).smul continuousOn_const
  have h_integrable (C : HermitianMat d ℂ) (hC : C.mat.PosDef) :
      Integrable
        (fun t => t ^ q • ((1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (C + t • 1)⁻¹))
        (volume.restrict (Set.Ioc 0 T)) := by
    have h_const :
        IntervalIntegrable
          (fun t : ℝ => (1 + t)⁻¹ • (1 : HermitianMat d ℂ)) volume 0 T :=
      h_cont_const.intervalIntegrable_of_Icc hT.le
    have h_diff :
        IntervalIntegrable
          (fun t : ℝ => (1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (C + t • 1)⁻¹)
          volume 0 T :=
      h_const.sub (integrable_inv_shift hC T hT.le)
    exact (h_diff.continuousOn_smul (by simpa [Set.uIcc_of_le hT.le] using h_cont_tq)).1
  rw [ intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_of_le hT.le ] at *
  refine integral_mono_ae ?_ ?_ h_integral_mono
  · exact h_integrable A hA
  · exact h_integrable B hB

open MeasureTheory ComplexOrder in
/-- The scalar function underlying rpowApprox via the CFC. -/
noncomputable def scalarRpowApprox (q T x : ℝ) : ℝ :=
  ∫ t in (0)..T, t ^ q * (1 / (1 + t) - 1 / (x + t))

open MeasureTheory ComplexOrder in
theorem rpowApprox_eq_cfc_scalar (A : HermitianMat d ℂ) (hA : A.mat.PosDef) (q T : ℝ)
    (hq : 0 ≤ q) (hT : 0 < T) :
    rpowApprox A q T = A.cfc (scalarRpowApprox q T) := by
  have rpowApprox_eq_cfc_scalar : ∀ t ∈ Set.Ioc 0 T, t ^ q • ((1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (A + t • 1)⁻¹) = A.cfc (fun u => t ^ q * (1 / (1 + t) - 1 / (u + t))) := by
    intro t ht
    have h_integrand : ((1 + t)⁻¹ • (1 : HermitianMat d ℂ) - (A + t • 1)⁻¹) = A.cfc (fun u => (1 + t)⁻¹ - (u + t)⁻¹) := by
      have h_integrand : (A + t • 1)⁻¹ = A.cfc (fun u => (u + t)⁻¹) := by
        have h_inv : (A + t • 1)⁻¹ = A.cfc (fun u => (u + t)⁻¹) := by
          have h_inv_def : (A + t • 1)⁻¹ = (A.cfc (fun u => u + t))⁻¹ := by
            rw [ show ( fun u => u + t ) = ( fun u => u ) + fun u => t from rfl, cfc_add ] ; aesop;
          have h_inv_comp : (A.cfc (fun u => u + t))⁻¹ = A.cfc (fun u => (u + t)⁻¹) := by
            have h_inv_smul : ∀ {f : ℝ → ℝ} (hf : ∀ i, f (A.H.eigenvalues i) ≠ 0), (A.cfc f)⁻¹ = A.cfc (fun u => (f u)⁻¹) := by
              exact fun {f} hf => inv_cfc_eq_cfc_inv f hf
            apply h_inv_smul
            intro i
            have h_eigenvalue_pos : 0 < A.H.eigenvalues i := by
              exact Matrix.PosDef.eigenvalues_pos hA i
            exact ne_of_gt (add_pos h_eigenvalue_pos ht.left);
          rw [h_inv_def, h_inv_comp];
        exact h_inv
      rw [ h_integrand, ← cfc_const ];
      rw [ ← cfc_sub ];
      rfl;
    aesop;
  -- Apply the fact that the integral of a CFC is the CFC of the integral.
  have rpowApprox_integral_eq : ∫ t in (0)..T, A.cfc (fun u => t ^ q * (1 / (1 + t) - 1 / (u + t))) = A.cfc (fun u => ∫ t in (0)..T, t ^ q * (1 / (1 + t) - 1 / (u + t))) := by
    have h_integrable : ∀ u : d, IntervalIntegrable (fun t : ℝ => t ^ q * (1 / (1 + t) - 1 / (A.H.eigenvalues u + t))) volume 0 T := by
      intro u
      have h_integrable : IntervalIntegrable (fun t : ℝ => t ^ q * (1 / (1 + t) - 1 / (A.H.eigenvalues u + t))) volume 0 T := by
        have h_pos : 0 < A.H.eigenvalues u := by
          exact Matrix.PosDef.eigenvalues_pos hA u
        exact ContinuousOn.intervalIntegrable ( by exact ContinuousOn.mul ( continuousOn_id.rpow_const fun x hx => Or.inr <| by linarith ) <| ContinuousOn.sub ( continuousOn_const.div ( continuousOn_const.add continuousOn_id ) fun x hx => by linarith [ Set.mem_Icc.mp <| by simpa [ hT.le ] using hx ] ) ( continuousOn_const.div ( continuousOn_const.add continuousOn_id ) fun x hx => by linarith [ Set.mem_Icc.mp <| by simpa [ hT.le ] using hx ] ) ) ..;
      exact h_integrable
    exact integral_cfc_eq_cfc_integral _ _ _ h_integrable
  unfold HermitianMat.rpowApprox scalarRpowApprox; simp_all +singlePass;
  rw [ ← rpowApprox_integral_eq, intervalIntegral.integral_of_le hT.le, integral_Ioc_eq_integral_Ioo ] at *
  rw [ setIntegral_congr_fun measurableSet_Ioo fun t ht => rpowApprox_eq_cfc_scalar t ht.1 ht.2.le ]
  simp [ ← integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le hT.le ]

/-- The positive constant arising from the resolvent integral.
    Equal to `∫ u in Set.Ioi 0, u ^ (q-1) / (1+u)` = `π / sin(π q)`,
    but we only need its positivity. -/
noncomputable def rpowConst (q : ℝ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), (u ^ (q - 1) / (1 + u) : ℝ)

open MeasureTheory in
/-- The integrand `u ^ (q-1) / (1+u)` is integrable on `(0, ∞)` for `0 < q < 1`. -/
lemma rpowConst_integrableOn (hq : 0 < q) (hq1 : q < 1) :
    IntegrableOn (fun u : ℝ => u ^ (q - 1) / (1 + u)) (Set.Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  apply IntegrableOn.union
  · have h_integrable_0_1 : IntegrableOn (fun u : ℝ => u ^ (q - 1)) (Set.Ioc 0 1) := by
      exact ( intervalIntegral.intervalIntegrable_rpow' ( by linarith ) ).1;
    apply h_integrable_0_1.mono'
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioc ] with x hx
      rw [ Real.norm_of_nonneg ( div_nonneg ( Real.rpow_nonneg hx.1.le _ ) ( by linarith [ hx.1 ] ) ) ]
      exact div_le_self ( Real.rpow_nonneg hx.1.le _ ) ( by linarith [ hx.1 ] ) ;
  · have h_bound : ∀ u : ℝ, 1 ≤ u → u ^ (q - 1) / (1 + u) ≤ u ^ (q - 2) := by
      intro u hu
      rw [div_le_iff₀ ( by positivity )]
      ring_nf
      apply le_add_of_nonneg_of_le (by positivity)
      rw [← Real.rpow_add_one (by positivity)]
      ring_nf
      rfl
    have h_integrable : IntegrableOn (fun u : ℝ => u ^ (q - 2)) (Set.Ioi 1) := by
      rw [integrableOn_Ioi_rpow_iff zero_lt_one]
      linarith
    apply h_integrable.mono'
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have _ := hu.out
      rw [Real.norm_of_nonneg (by positivity)]
      exact h_bound u hu.out.le

open MeasureTheory in
/-- The resolvent constant is positive for `0 < q < 1`. -/
lemma rpowConst_pos (hq : 0 < q) (hq1 : q < 1) : 0 < rpowConst q := by
  unfold rpowConst;
  have h_nonzero : 0 < ∫ u in Set.Ioi (0 : ℝ), u ^ (q - 1) / (1 + u) := by
    have h_integrable : IntegrableOn (fun u : ℝ => u ^ (q - 1) / (1 + u)) (Set.Ioi (0 : ℝ)) := by
      exact rpowConst_integrableOn hq hq1
    rw [ integral_pos_iff_support_of_nonneg_ae ];
    · simp [Function.support]
      exact lt_of_lt_of_le ( by norm_num ) ( measure_mono <| show Set.Ioi ( 0 : ℝ ) ⊆ { x : ℝ | ¬x ^ ( q - 1 ) = 0 ∧ ¬1 + x = 0 } ∩ Set.Ioi 0 from fun x hx => ⟨ ⟨ ne_of_gt <| Real.rpow_pos_of_pos hx _, ne_of_gt <| add_pos zero_lt_one hx ⟩, hx ⟩ );
    · filter_upwards [ ae_restrict_mem measurableSet_Ioi ] with u hu using div_nonneg ( Real.rpow_nonneg hu.out.le _ ) ( add_nonneg zero_le_one hu.out.le );
    · exact h_integrable;
  linarith

open MeasureTheory Filter in
/-- The scalar rpow approximation converges pointwise.
    `scalarRpowApprox q T x → rpowConst q * (x^q - 1)` as `T → ∞`. -/
lemma scalarRpowApprox_tendsto {x : ℝ} (hx : 0 < x) (hq : 0 < q) (hq1 : q < 1) :
    Filter.Tendsto (fun T => scalarRpowApprox q T x) atTop (nhds (rpowConst q * (x ^ q - 1))) := by
  have h_def : ∀ T > 0, scalarRpowApprox q T x = x * (∫ t in (0)..T, t ^ (q - 1) / (x + t)) - (∫ t in (0)..T, t ^ (q - 1) / (1 + t)) := by
    intro T hT
    have : ∀ t ∈ Set.Ioc (0 : ℝ) T, t ^ q * (1 / (1 + t) - 1 / (x + t)) = x * (t ^ (q - 1) / (x + t)) - (t ^ (q - 1) / (1 + t)) := by
      intro t ht; rw [ Real.rpow_sub_one ht.1.ne' ]
      grind
    rw [ intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_of_le hT.le ];
    rw [ ← integral_const_mul, ← integral_sub ];
    · exact Eq.trans ( intervalIntegral.integral_of_le hT.le ) ( setIntegral_congr_fun measurableSet_Ioc this );
    · apply Integrable.const_mul _ _;
      apply Integrable.mono' (g := fun t => t ^ ( q - 1 ) / x)
      · exact ( intervalIntegral.intervalIntegrable_rpow' ( by linarith ) ).1.div_const _;
      · apply Measurable.aestronglyMeasurable
        fun_prop
      · filter_upwards [ ae_restrict_mem measurableSet_Ioc ] with t ht using by rw [ Real.norm_of_nonneg ( div_nonneg ( Real.rpow_nonneg ht.1.le _ ) ( by linarith [ ht.1 ] ) ) ] ; exact div_le_div_of_nonneg_left ( Real.rpow_nonneg ht.1.le _ ) ( by linarith [ ht.1 ] ) ( by linarith [ ht.1 ] ) ;
    · apply Integrable.mono' (g := fun t => t ^ ( q - 1 ) / ( 1 + 0 ))
      · exact ( intervalIntegral.intervalIntegrable_rpow' ( by linarith ) ).1.div_const _;
      · apply Measurable.aestronglyMeasurable
        fun_prop
      · filter_upwards [ ae_restrict_mem measurableSet_Ioc ] with t ht using by rw [ Real.norm_of_nonneg ( div_nonneg ( Real.rpow_nonneg ( by linarith [ ht.1 ] ) _ ) ( by linarith [ ht.1 ] ) ) ] ; exact div_le_div_of_nonneg_left ( Real.rpow_nonneg ( by linarith [ ht.1 ] ) _ ) ( by linarith [ ht.1 ] ) ( by linarith [ ht.1 ] ) ;
  have h_int_1 : Filter.Tendsto (fun T => ∫ t in (0)..T, t ^ (q - 1) / (1 + t)) Filter.atTop (nhds (rpowConst q)) := by
    apply intervalIntegral_tendsto_integral_Ioi
    · exact rpowConst_integrableOn hq hq1
    · exact Filter.tendsto_id
  have h_int_x : Filter.Tendsto (fun T => ∫ t in (0)..T, t ^ (q - 1) / (x + t)) Filter.atTop (nhds (rpowConst q * x ^ (q - 1))) := by
    have h_subst : ∀ T > 0, ∫ t in (0)..T, t ^ (q - 1) / (x + t) = x ^ (q - 1) * ∫ u in (0)..T / x, u ^ (q - 1) / (1 + u) := by
      intro T hT
      have h_subst : ∫ t in (0)..T, t ^ (q - 1) / (x + t) = ∫ u in (0)..T / x, (x * u) ^ (q - 1) / (x + x * u) * x := by
        simp [ mul_comm x, intervalIntegral.integral_comp_mul_right ( fun u => u ^ ( q - 1 ) / ( x + u ) ), hx.ne' ];
        rw [ inv_mul_eq_div, div_mul_cancel₀ _ hx.ne' ];
      rw [ h_subst, ← intervalIntegral.integral_const_mul ];
      refine intervalIntegral.integral_congr fun u hu ↦ ?_
      rw [ Real.mul_rpow ( by positivity ) ( by cases Set.mem_uIcc.mp hu <;> nlinarith [ div_mul_cancel₀ T hx.ne' ] ) ]
      field_simp
    rw [ Filter.tendsto_congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with T hT using h_subst T hT ) ]
    simpa [ mul_comm ] using h_int_1.comp ( Filter.tendsto_id.atTop_div_const hx ) |> Filter.Tendsto.const_mul ( x ^ ( q - 1 ) ) ;
  rw [ Filter.tendsto_congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with T hT using h_def T hT ) ]
  convert Filter.Tendsto.sub ( h_int_x.const_mul x ) h_int_1 using 2
  ring_nf
  rw [ mul_assoc, ← Real.rpow_one_add' hx.le ]
  · simp
  · linarith

open MeasureTheory ComplexOrder Filter in
set_option backward.isDefEq.respectTransparency false in
/-- The matrix rpow approximation converges: `rpowApprox A q T → rpowConst q • (A^q - 1)`. -/
lemma tendsto_rpowApprox (hA : A.mat.PosDef) (hq : 0 < q) (hq1 : q < 1) :
    Tendsto (rpowApprox A q) atTop (nhds (rpowConst q • (A ^ q - 1))) := by
  have h_target : rpowConst q • (A ^ q - 1) = A.cfc (fun x => rpowConst q * (x ^ q - 1)) := by
    have h2 : A.cfc (fun x => rpowConst q * (x ^ q - 1)) = rpowConst q • A.cfc (fun x => x ^ q - 1) :=
      HermitianMat.cfc_const_mul A (fun x => x ^ q - 1) (rpowConst q)
    have h3 : A.cfc (fun x => x ^ q - 1) = A.cfc (· ^ q) - 1 := by
      conv_rhs => rw [show (1 : HermitianMat d ℂ) = A.cfc (fun _ => (1 : ℝ)) by simp]
      exact cfc_sub_apply A (f := (· ^ q)) (g := fun _ => 1)
    rw [h2, h3, rpow_eq_cfc]
  have h_eq : ∀ᶠ T in atTop, rpowApprox A q T = A.cfc (scalarRpowApprox q T) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with T hT
    exact rpowApprox_eq_cfc_scalar A hA q T hq.le hT
  rw [Filter.tendsto_congr' h_eq, h_target]
  have h_expand_src : ∀ T, (A.cfc (scalarRpowApprox q T)).mat = ∑ i, scalarRpowApprox q T (A.H.eigenvalues i) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) :=
    fun T => cfc_toMat_eq_sum_smul_proj A (scalarRpowApprox q T)
  have h_expand_tgt : (A.cfc (fun x => rpowConst q * (x ^ q - 1))).mat = ∑ i, (rpowConst q * (A.H.eigenvalues i ^ q - 1)) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) :=
    cfc_toMat_eq_sum_smul_proj A (fun x => rpowConst q * (x ^ q - 1))
  have h_sum : Tendsto (fun T : ℝ => ∑ i, scalarRpowApprox q T (A.H.eigenvalues i) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose)) atTop (nhds (∑ i, (rpowConst q * (A.H.eigenvalues i ^ q - 1)) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose))) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    have := scalarRpowApprox_tendsto (hA.eigenvalues_pos i) hq hq1
    exact Filter.Tendsto.smul_const (Complex.continuous_ofReal.continuousAt.tendsto.comp this) _
  open scoped Matrix.Norms.Frobenius in
  rw [tendsto_iff_norm_sub_tendsto_zero] at *
  convert h_sum using 2 with T
  show ‖(A.cfc (scalarRpowApprox q T)).mat - (A.cfc (fun x => rpowConst q * (x ^ q - 1))).mat‖ = _
  rw [h_expand_src, h_expand_tgt]

open MeasureTheory ComplexOrder Filter in
/-- Loewner-Heinz for positive definite lower endpoint.

This is the positive-definite core used to prove the positive-semidefinite statement by
adding `ε • 1` and taking a limit. -/
theorem rpow_le_rpow_of_posDef (hA : A.mat.PosDef) (hAB : A ≤ B)
    (hq : 0 < q) (hq1 : q ≤ 1) : A ^ q ≤ B ^ q := by
  by_cases hq_eq_one : q = 1;
  · aesop;
  · have h_rpow : rpowConst q • (A ^ q - 1) ≤ rpowConst q • (B ^ q - 1) := by
      convert le_of_tendsto_of_tendsto ( tendsto_rpowApprox hA hq ( lt_of_le_of_ne hq1 hq_eq_one ) ) ( tendsto_rpowApprox ( posDef_of_posDef_le hA hAB ) hq ( lt_of_le_of_ne hq1 hq_eq_one ) ) _ using 1
      generalize_proofs at *; (
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with T hT using rpowApprox_mono hA ( posDef_of_posDef_le hA hAB ) hAB hq.le T hT |> le_trans <| by aesop;);
    have h_rpow_pos : 0 < rpowConst q := by
      exact rpowConst_pos hq ( lt_of_le_of_ne hq1 hq_eq_one );
    simp_all

open ComplexOrder Filter in
/-- The **Löwner—Heinz theorem**: for matrices A and B, if `0 ≤ A ≤ B` and `0 < q ≤ 1`,
then `A^q ≤ B^q`. That is, real roots are operator monotone. -/
theorem rpow_le_rpow_of_le (hA : 0 ≤ A) (hAB : A ≤ B)
    (hq : 0 < q) (hq1 : q ≤ 1) : A ^ q ≤ B ^ q := by
  -- For ε > 0, let Aε = A + ε • 1 and Bε = B + ε • 1.
  set Aε : ℝ → HermitianMat d ℂ := fun ε => A + ε • 1
  set Bε : ℝ → HermitianMat d ℂ := fun ε => B + ε • 1
  -- For ε > 0, Aε and Bε are positive definite and Aε ≤ Bε.
  have h_pos_def : ∀ ε > 0, (Aε ε).mat.PosDef ∧ (Bε ε).mat.PosDef ∧ Aε ε ≤ Bε ε := by
    intro ε hε_pos
    have h_pos_def_Aε : (Aε ε).mat.PosDef := by
      rw [Matrix.posDef_iff_dotProduct_mulVec] at ⊢
      constructor <;> norm_num [ hε_pos, hA, hAB ];
      · exact H (Aε ε)
      · intro x hx_nonzero
        have h_inner : star x ⬝ᵥ (Aε ε).mat.mulVec x = star x ⬝ᵥ A.mat.mulVec x + ε * star x ⬝ᵥ x := by
          simp [ Aε, Matrix.add_mulVec]
          ring_nf
          simp [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm];
          simp [ Matrix.one_apply]
        have h_inner_nonneg : 0 ≤ star x ⬝ᵥ A.mat.mulVec x := by
          exact inner_mulVec_nonneg hA x
        have h_inner_pos : 0 < star x ⬝ᵥ x := by
          simp_all
        exact h_inner.symm ▸ add_pos_of_nonneg_of_pos h_inner_nonneg ( mul_pos ( mod_cast hε_pos ) ( mod_cast h_inner_pos ) ) |> lt_of_lt_of_le <| le_rfl;
    have h_pos_def_Bε : (Bε ε).mat.PosDef := by
      convert posDef_of_posDef_le h_pos_def_Aε _ using 1
      exact add_le_add_left hAB _ |> le_trans ( by simp [ Aε ] ) ;
    have h_le_Aε_Bε : Aε ε ≤ Bε ε := by
      exact add_le_add_left hAB _ |> le_trans <| by simp [ Bε ] ;
    exact ⟨h_pos_def_Aε, h_pos_def_Bε, h_le_Aε_Bε⟩
  -- By the continuity of the function $M \mapsto M^q$, we have $(Aε ε)^q \to A^q$ and $(Bε ε)^q \to B^q$ as $\epsilon \to 0^+$.
  have h_cont : Filter.Tendsto (fun ε => (Aε ε) ^ q) (nhdsWithin 0 (Set.Ioi 0)) (nhds (A ^ q)) ∧ Filter.Tendsto (fun ε => (Bε ε) ^ q) (nhdsWithin 0 (Set.Ioi 0)) (nhds (B ^ q)) := by
    have h_cont : ContinuousOn (fun M : HermitianMat d ℂ => M ^ q) (Set.univ : Set (HermitianMat d ℂ)) := by
      -- Apply the continuity of the function $M \mapsto M^q$ on the set of all Hermitian matrices.
      apply rpow_const_continuous hq.le |> Continuous.continuousOn
    refine' ⟨ h_cont.continuousAt ( by simp ) |> fun h => h.tendsto.comp ( tendsto_nhdsWithin_of_tendsto_nhds <| Continuous.tendsto' _ _ _ _ ), h_cont.continuousAt ( by simp ) |> fun h => h.tendsto.comp ( tendsto_nhdsWithin_of_tendsto_nhds <| Continuous.tendsto' _ _ _ _ ) ⟩ <;> continuity;
  -- By the continuity of the function $M \mapsto M^q$, we have $(Aε ε)^q \leq (Bε ε)^q$ for all $\epsilon > 0$.
  have h_le : ∀ ε > 0, (Aε ε) ^ q ≤ (Bε ε) ^ q := by
    exact fun ε hε => rpow_le_rpow_of_posDef ( h_pos_def ε hε |>.1 ) ( h_pos_def ε hε |>.2.2 ) hq hq1 |> le_trans <| by simp [ * ] ;
  exact le_of_tendsto_of_tendsto h_cont.1 h_cont.2 ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => h_le ε hε ) |> fun h => by simpa using h;

end LoewnerHeinz

/-! ## Araki-Lieb-Thirring Inequality

The next section proves the trace inequality
`Tr[(B ^ r) (A ^ r) (B ^ r)] <= Tr[(B A B) ^ r]` for `0 < r <= 1`.
The proof uses compound matrices to convert the multiplicative singular-value estimates
into a weak log-majorization argument.
-/

section ArakiLiebThirring

variable {A B : HermitianMat d ℂ} {q r : ℝ}
open ComplexOrder MatrixOrder
open scoped AllOrdered

private lemma compoundHermitian_rpow (A : HermitianMat d ℂ) (hA : 0 ≤ A)
    (k : ℕ) (r : ℝ) :
    compoundHermitian (A ^ r) k = (compoundHermitian A k) ^ r := by
  obtain ⟨U, a, ha, hAeq⟩ :
      ∃ U : 𝐔[d], ∃ a : d → ℝ, (∀ i, 0 ≤ a i) ∧ A = conj U.val (diagonal ℂ a) := by
    rw [zero_le_iff] at hA
    exact ⟨_, _, hA.eigenvalues_nonneg, eq_conj_diagonal A⟩
  have hdiag_rpow :
      compoundHermitian ((diagonal ℂ a) ^ r) k =
        (compoundHermitian (diagonal ℂ a) k) ^ r := by
    have hdiag (b : d → ℝ) :
        compoundHermitian (diagonal ℂ b) k =
          diagonal ℂ
            (fun S : {S : Finset d // S.card = k} =>
              ∏ i : Fin k, b (S.1.orderEmbOfFin S.2 i)) := by
      ext1
      simp [compoundHermitian, compoundMatrix_diagonal]
    rw [rpow_diagonal, hdiag, hdiag, rpow_diagonal]
    ext S T
    by_cases h : S = T
    · subst h
      simp [Real.finsetProd_rpow _ _ (fun i _ => ha _)]
    · rw [HermitianMat.diagonal_mat, HermitianMat.diagonal_mat]
      simp [Matrix.diagonal, h]
  rw [hAeq, rpow_conj_unitary, compoundHermitian_conj, compoundHermitian_conj, hdiag_rpow]
  exact (rpow_conj_unitary ((diagonal ℂ a).compoundHermitian k) (compoundUnitary U k) r).symm

private lemma conj_rpow_le_one_of_conj_le_one_posDef
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A) (hB : B.mat.PosDef)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hAB : A.conj B.mat ≤ 1) :
    (A ^ r).conj (B ^ r).mat ≤ 1 := by
  have hA_le : A ≤ B ^ (-2 : ℝ) := by
    have hconj := HermitianMat.conj_mono (M := (B ^ (-1 : ℝ)).mat) hAB
    have hleft : (A.conj B.mat).conj (B ^ (-1 : ℝ)).mat = A := by
      rw [HermitianMat.conj_conj]
      have hmul : (B ^ (-1 : ℝ)).mat * B.mat = 1 := by
        simpa using rpow_neg_mul_rpow_self hB 1
      exact (HermitianMat.conj_one (A := A)).symm ▸ by simp [hmul]
    have hright : (1 : HermitianMat d ℂ).conj (B ^ (-1 : ℝ)).mat = B ^ (-2 : ℝ) := by
      ext1
      rw [HermitianMat.conj_apply_mat]
      simp only [HermitianMat.conjTranspose_mat]
      rw [show (B ^ (-2 : ℝ)).mat =
          (B ^ (-1 : ℝ)).mat * (B ^ (-1 : ℝ)).mat by
        rw [← HermitianMat.mat_rpow_add (zero_le_iff.mpr hB.posSemidef)] <;> norm_num]
      simp
    simpa [hleft, hright] using hconj
  have hconj := HermitianMat.conj_mono (M := (B ^ r).mat)
    (rpow_le_rpow_of_le hA hA_le hr0 hr1)
  have hright : ((B ^ (-2 : ℝ)) ^ r).conj (B ^ r).mat = 1 := by
    ext1
    rw [HermitianMat.conj_apply_mat]
    simp only [HermitianMat.conjTranspose_mat]
    have h1 : ((B ^ (-2 : ℝ)) ^ r) = B ^ (-2 * r) := by
      rw [← HermitianMat.rpow_mul (zero_le_iff.mpr hB.posSemidef)]
    rw [h1]
    calc
      (B ^ r).mat * (B ^ (-2 * r)).mat * (B ^ r).mat = (B ^ r).mat * (B ^ (-r)).mat := by
        rw [Matrix.mul_assoc, ← HermitianMat.mat_rpow_add (zero_le_iff.mpr hB.posSemidef)]
        · ring_nf
        · linarith [hr0.ne']
      _ = 1 := by
        have hInv : (B ^ (-r : ℝ)).mat = (B ^ r).mat⁻¹ := by
          simpa [HermitianMat.mat_inv] using congrArg HermitianMat.mat (rpow_inv_eq_neg_rpow hB r).symm
        rw [hInv]
        exact Matrix.mul_nonsing_inv _ (((B ^ r).mat).isUnit_iff_isUnit_det.mp (isUnit_rpow_toMat hB r))
  exact le_trans hconj hright.le

private lemma conj_smul_right (A B : HermitianMat d ℂ) (c : ℝ) :
    A.conj (↑(c • B).mat) = c ^ 2 • A.conj B.mat := by
  ext1
  rw [HermitianMat.conj_apply_mat]
  simp [HermitianMat.mat_smul, Matrix.conjTranspose_smul, sq, smul_smul]

private lemma conjTranspose_half_mul_eq_conj
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A) :
    ((A ^ (1/2 : ℝ)).mat * B.mat).conjTranspose * ((A ^ (1/2 : ℝ)).mat * B.mat)
      = (A.conj B.mat).mat := by
  have := HermitianMat.pow_half_mul hA
  simp only [Matrix.conjTranspose_mul, HermitianMat.conjTranspose_mat, Matrix.mul_assoc]
  simpa [HermitianMat.conj_apply_mat, Matrix.mul_assoc] using congrArg (fun M => B.mat * M * B.mat) this

private lemma top_singular_le_of_self_mul_le_smul_one
    {e : Type*} [Fintype e] [DecidableEq e] (X : Matrix e e ℂ)
    {α : ℝ} (_ : 0 ≤ α) (hX : X.conjTranspose * X ≤ α • (1 : Matrix e e ℂ))
    (hcard : 0 < Fintype.card e) :
    singularValuesSorted X ⟨0, hcard⟩ ≤ Real.sqrt α := by
  let : Nonempty e := Fintype.card_pos_iff.mp hcard
  let hne : (Finset.univ : Finset e).Nonempty := by
    simp
  rw [singularValuesSorted_zero_eq_sup X hcard]
  refine Finset.sup'_le _ _ ?_
  intro i hi
  unfold singularValues
  refine Real.sqrt_le_sqrt ?_
  exact (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff
    (Matrix.isHermitian_mul_conjTranspose_self X.conjTranspose) α).mpr (by simpa using hX) i

private lemma compound_top_singular_le_posDef
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A) (hB : B.mat.PosDef)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (k : ℕ) (hk : k ≤ Fintype.card d) :
    singularValuesSorted (compoundMatrix ((A ^ (r / 2 : ℝ)).mat * (B ^ r).mat) k) (compoundZero k hk) ≤
      singularValuesSorted (compoundMatrix ((A ^ (1 / 2 : ℝ)).mat * B.mat) k) (compoundZero k hk) ^ r := by
  let Ak : HermitianMat {S : Finset d // S.card = k} ℂ := compoundHermitian A k
  let Bk : HermitianMat {S : Finset d // S.card = k} ℂ := compoundHermitian B k
  let Mk : Matrix {S : Finset d // S.card = k} {S : Finset d // S.card = k} ℂ :=
    compoundMatrix ((A ^ (1 / 2 : ℝ)).mat * B.mat) k
  let Nk : Matrix {S : Finset d // S.card = k} {S : Finset d // S.card = k} ℂ :=
    compoundMatrix ((A ^ (r / 2 : ℝ)).mat * (B ^ r).mat) k
  let c : ℝ := singularValuesSorted Mk (compoundZero k hk)
  have hAk : 0 ≤ Ak := compoundHermitian_nonneg A hA k
  have hBk : Bk.mat.PosDef := by
    rw [(compoundHermitian B k).H.posDef_iff_eigenvalues_pos]
    obtain ⟨σ, hσ⟩ := compoundHermitian_eigenvalues B k
    intro S
    rw [show (compoundHermitian B k).H.eigenvalues S =
        ∏ i : Fin k, B.H.eigenvalues ((σ.symm S).1.orderEmbOfFin (σ.symm S).2 i) by
      simpa [Function.comp_def] using congrFun hσ (σ.symm S)]
    exact Finset.prod_pos (fun i _ => Matrix.PosDef.eigenvalues_pos hB _)
  have hc_nonneg : 0 ≤ c := singularValuesSorted_nonneg Mk (compoundZero k hk)
  have hMk_conj : Mk.conjTranspose * Mk = (Ak.conj Bk.mat).mat := by
    dsimp [Mk, Ak, Bk]
    rw [compoundMatrix_mul]
    change ((compoundHermitian (A ^ (1 / 2 : ℝ)) k).mat *
        (compoundHermitian B k).mat).conjTranspose *
          ((compoundHermitian (A ^ (1 / 2 : ℝ)) k).mat *
            (compoundHermitian B k).mat) =
        ((compoundHermitian A k).conj (compoundHermitian B k).mat).mat
    rw [compoundHermitian_rpow A hA k (1 / 2 : ℝ)]
    exact conjTranspose_half_mul_eq_conj (A := compoundHermitian A k)
      (B := compoundHermitian B k) hAk
  have hNk_conj : Nk.conjTranspose * Nk = ((Ak ^ r).conj (Bk ^ r).mat).mat := by
    dsimp [Nk, Ak, Bk]
    rw [compoundMatrix_mul]
    change ((compoundHermitian (A ^ (r / 2 : ℝ)) k).mat *
        (compoundHermitian (B ^ r) k).mat).conjTranspose *
          ((compoundHermitian (A ^ (r / 2 : ℝ)) k).mat *
            (compoundHermitian (B ^ r) k).mat) =
        (((compoundHermitian A k) ^ r).conj ((compoundHermitian B k) ^ r).mat).mat
    rw [compoundHermitian_rpow A hA k (r / 2 : ℝ),
      compoundHermitian_rpow B (zero_le_iff.mpr hB.posSemidef) k r]
    rw [show (compoundHermitian A k) ^ (r / 2 : ℝ) = ((compoundHermitian A k) ^ r) ^ (1 / 2 : ℝ) from by
      change Ak ^ (r / 2 : ℝ) = (Ak ^ r) ^ (1 / 2 : ℝ)
      rw [← HermitianMat.rpow_mul hAk]; ring_nf]
    exact conjTranspose_half_mul_eq_conj
      (A := (compoundHermitian A k) ^ r) (B := (compoundHermitian B k) ^ r)
      (rpow_nonneg hAk)
  have hMk_le : Ak.conj Bk.mat ≤ c ^ 2 • 1 := by
    change (Ak.conj Bk.mat).mat ≤ (c ^ 2 • (1 : HermitianMat {S : Finset d // S.card = k} ℂ)).mat
    have hmat : Mk.conjTranspose * Mk ≤
        c ^ 2 • (1 : Matrix {S : Finset d // S.card = k} {S : Finset d // S.card = k} ℂ) :=
      by
        simpa using
          (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff
            (Matrix.isHermitian_mul_conjTranspose_self Mk.conjTranspose) (c ^ 2)).mp
              fun i => by
                dsimp [c]
                exact eigenvalue_le_singularValuesSorted_sq Mk (compound_card_pos k hk) i
    simpa [HermitianMat.conj_apply_mat, hMk_conj] using hmat
  by_cases hc_zero : c = 0
  · have hMk_eq_zero : Ak.conj Bk.mat = 0 := by
      apply le_antisymm
      · have := hMk_le; rw [hc_zero] at this; simpa using this
      · exact HermitianMat.conj_nonneg (M := Bk.mat) hAk
    have hAk_eq_zero : Ak = 0 := by
      have hconj := congrArg (fun H : HermitianMat _ ℂ => H.conj (Bk ^ (-1 : ℝ)).mat) hMk_eq_zero
      have hleft : (Ak.conj Bk.mat).conj (Bk ^ (-1 : ℝ)).mat = Ak := by
        rw [HermitianMat.conj_conj]
        have : (Bk ^ (-1 : ℝ)).mat * Bk.mat = 1 := by
          simpa using rpow_neg_mul_rpow_self hBk 1
        simp [this, HermitianMat.conj_one (A := Ak)]
      simpa [hleft] using hconj
    have hNk_zero : Nk.conjTranspose * Nk = 0 := by
      rw [hNk_conj, hAk_eq_zero]
      simp [rpow_eq_cfc, cfc_apply_zero, Real.zero_rpow hr0.ne']
    have htop : singularValuesSorted Nk (compoundZero k hk) ≤ 0 := by
      have h1 :=
        top_singular_le_of_self_mul_le_smul_one Nk (show 0 ≤ (0 : ℝ) by norm_num)
          (by simp [hNk_zero])
          (compound_card_pos k hk)
      simp_all only [Std.le_refl, map_zero, mat_zero, Matrix.conjTranspose_mul_self_eq_zero,
        conj_apply_mat, conjTranspose_mat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        _root_.zero_pow, zero_smul, Real.sqrt_zero, ge_iff_le]
      exact h1
    change singularValuesSorted Nk (compoundZero k hk) ≤ c ^ r
    rw [hc_zero, Real.zero_rpow hr0.ne']
    exact htop
  · have hc_pos : 0 < c := lt_of_le_of_ne hc_nonneg (Ne.symm hc_zero)
    have hscaled : Ak.conj ((c⁻¹) • Bk).mat ≤ 1 := by
      have hmul := smul_le_smul_of_nonneg_left hMk_le (show 0 ≤ c⁻¹ ^ 2 by positivity)
      rw [conj_smul_right]
      have hs : (c ^ 2)⁻¹ * c ^ 2 = 1 := by field_simp [pow_two, hc_zero]
      simpa [smul_smul, hs] using hmul
    have hpow := conj_rpow_le_one_of_conj_le_one_posDef hAk
      (by simpa [HermitianMat.mat_smul] using hBk.smul (inv_pos.mpr hc_pos))
      hr0 hr1 hscaled
    have hpow' : ((c⁻¹) ^ r) ^ 2 • ((Ak ^ r).conj (Bk ^ r).mat) ≤ 1 := by
      have hBk_scale : ((c⁻¹) • Bk) ^ r = (c⁻¹) ^ r • (Bk ^ r) := by
        rw [show (c⁻¹) • Bk = Bk.cfc (fun x => c⁻¹ * x) from
          (HermitianMat.cfc_const_mul_id (A := Bk) (r := c⁻¹)).symm]
        rw [HermitianMat.rpow_eq_cfc, ← HermitianMat.cfc_comp]
        calc
          Bk.cfc (((fun x => x ^ r) : ℝ → ℝ) ∘ fun x => c⁻¹ * x)
            = Bk.cfc (fun x => (c⁻¹) ^ r * x ^ r) := by
                apply HermitianMat.cfc_congr_of_nonneg (zero_le_iff.mpr hBk.posSemidef)
                intro x hx
                rw [Function.comp_apply, Real.mul_rpow (inv_nonneg.mpr hc_nonneg) hx]
          _ = (c⁻¹) ^ r • (Bk ^ r) := by
                rw [HermitianMat.cfc_const_mul, HermitianMat.rpow_eq_cfc]
      rwa [hBk_scale, conj_smul_right] at hpow
    have hNk_le : ((Ak ^ r).conj (Bk ^ r).mat) ≤ c ^ (2 * r) • 1 := by
      have hmul := smul_le_smul_of_nonneg_left hpow' (show 0 ≤ c ^ (2 * r) by positivity)
      have hs : c ^ (2 * r) * ((c⁻¹) ^ r) ^ 2 = 1 := by
        have hcr_pos : 0 < c ^ r := Real.rpow_pos_of_pos hc_pos r
        have hpow : c ^ (2 * r) = (c ^ r) ^ 2 := by
          calc
            c ^ (2 * r) = c ^ (r + r) := by ring_nf
            _ = c ^ r * c ^ r := by rw [Real.rpow_add hc_pos]
            _ = (c ^ r) ^ 2 := by ring
        have hinv : (c⁻¹) ^ r = (c ^ r)⁻¹ := by
          rw [Real.inv_rpow hc_nonneg]
        calc
          c ^ (2 * r) * ((c⁻¹) ^ r) ^ 2 = (c ^ r) ^ 2 * ((c ^ r)⁻¹) ^ 2 := by
            rw [hpow, hinv]
          _ = 1 := by
            field_simp [pow_two, hcr_pos.ne']
      rwa [smul_smul, hs, one_smul] at hmul
    have htop : singularValuesSorted Nk (compoundZero k hk) ≤ Real.sqrt (c ^ (2 * r)) :=
      top_singular_le_of_self_mul_le_smul_one Nk
        (by positivity)
        (hNk_conj ▸ hNk_le)
        (compound_card_pos k hk)
    have hsqrt : Real.sqrt (c ^ (2 * r)) = c ^ r := by
      have hpow : c ^ (2 * r) = (c ^ r) ^ 2 := by
        rw [mul_comm, Real.rpow_mul hc_nonneg]
        norm_num
      rw [hpow, Real.sqrt_sq_eq_abs, abs_of_nonneg]
      exact Real.rpow_nonneg hc_nonneg r
    exact htop.trans (by rw [hsqrt])

/-- Expresses a conjugated trace power as a sum of singular values.

This is private infrastructure for the Lieb-Thirring inequality. -/
private lemma trace_conj_rpow_eq_sum_singularValuesSorted
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A) (α : ℝ) :
    ((A.conj B.mat) ^ α).trace =
      ∑ i : Fin (Fintype.card d),
        singularValuesSorted ((A ^ (1 / 2 : ℝ)).mat * B.mat) i ^ (2 * α) := by
  let M : Matrix d d ℂ := (A ^ (1 / 2 : ℝ)).mat * B.mat
  let H : HermitianMat d ℂ :=
    ⟨M.conjTranspose * M, by
      have h1 := Matrix.isHermitian_mul_conjTranspose_self M.conjTranspose
      simp_all only [Matrix.conjTranspose_conjTranspose]
      exact h1⟩
  have hH : H = A.conj B.mat := by
    ext1; dsimp [H, M]
    exact conjTranspose_half_mul_eq_conj (A := A) (B := B) hA
  calc
    ((A.conj B.mat) ^ α).trace = ∑ i, (H.H.eigenvalues i) ^ α := by
      simpa [hH] using trace_rpow_eq_sum H α
    _ = ∑ i : Fin (Fintype.card d), singularValuesSorted M i ^ (2 * α) := by
      rw [← sum_singularValues_rpow_eq_sum_sorted M (2 * α)]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold singularValues
      have h_nn := Matrix.eigenvalues_conjTranspose_mul_self_nonneg M i
      rw [show H.H.eigenvalues i = Real.sqrt (H.H.eigenvalues i) ^ 2 from
        (Real.sq_sqrt h_nn).symm, ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul (Real.sqrt_nonneg _)]
      push_cast
      congr 1
      simp [H, Matrix.conjTranspose_conjTranspose]
      rfl

private lemma lieb_thirring_le_one_posDef
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A) (hB : B.mat.PosDef)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ((A ^ r).conj (B ^ r).mat).trace ≤ ((A.conj B.mat) ^ r).trace := by
  classical
  let M : Matrix d d ℂ := (A ^ (1 / 2 : ℝ)).mat * B.mat
  let N : Matrix d d ℂ := (A ^ (r / 2 : ℝ)).mat * (B ^ r).mat
  have hlogmaj :
      ∀ (k : ℕ) (_ : k ≤ Fintype.card d),
        ∏ i : Fin k, singularValuesSorted N ⟨i.val, by omega⟩ ≤
        ∏ i : Fin k, (singularValuesSorted M ⟨i.val, by omega⟩) ^ r := by
    intro k hk
    calc
      ∏ i : Fin k, singularValuesSorted N ⟨i.val, by omega⟩
        = singularValuesSorted (compoundMatrix N k) (compoundZero k hk) := by
            exact prod_singularValuesSorted_eq_compoundSV N k hk
      _ ≤ singularValuesSorted (compoundMatrix M k) (compoundZero k hk) ^ r := by
            simpa [M, N] using compound_top_singular_le_posDef hA hB hr0 hr1 k hk
      _ = ∏ i : Fin k, (singularValuesSorted M ⟨i.val, by omega⟩) ^ r := by
            have hprod := congrArg (· ^ r) (prod_singularValuesSorted_eq_compoundSV M k hk).symm
            have hrpow := (Real.finsetProd_rpow (s := Finset.univ)
              (f := fun i : Fin k => singularValuesSorted M ⟨i.val, by omega⟩)
              (fun i _ => singularValuesSorted_nonneg M _) r)
            exact hprod.trans hrpow.symm
  have hsum :
      ∑ i : Fin (Fintype.card d), singularValuesSorted N i ^ 2 ≤
      ∑ i : Fin (Fintype.card d), (singularValuesSorted M i ^ r) ^ 2 := by
    simpa using weak_log_maj_sum_rpow_le
      (n := Fintype.card d)
      (x := singularValuesSorted N)
      (y := fun i : Fin (Fintype.card d) => singularValuesSorted M i ^ r)
      (r := (2 : ℝ))
      (fun i => singularValuesSorted_nonneg N i)
      (fun i => Real.rpow_nonneg (singularValuesSorted_nonneg M i) r)
      (singularValuesSorted_antitone N)
      (rpow_antitone_of_nonneg_antitone
        (singularValuesSorted_antitone M)
        (singularValuesSorted_nonneg M)
        hr0)
      hlogmaj
      (by norm_num)
  have hleft :
      ((A ^ r).conj (B ^ r).mat).trace =
        ∑ i : Fin (Fintype.card d), singularValuesSorted N i ^ 2 := by
    have := trace_conj_rpow_eq_sum_singularValuesSorted (A := A ^ r) (B := B ^ r) (hA := rpow_nonneg hA) (α := 1)
    rw [show ((A ^ r) ^ (1 / 2 : ℝ)) = A ^ (r / 2 : ℝ) from by
      rw [← HermitianMat.rpow_mul hA]; ring_nf] at this
    simpa [N] using this
  have hright :
      ((A.conj B.mat) ^ r).trace =
        ∑ i : Fin (Fintype.card d), (singularValuesSorted M i ^ r) ^ 2 := by
    calc ((A.conj B.mat) ^ r).trace
        = ∑ i : Fin (Fintype.card d), singularValuesSorted M i ^ (2 * r) := by
            simpa [M] using trace_conj_rpow_eq_sum_singularValuesSorted (A := A) (B := B) (hA := hA) (α := r)
      _ = ∑ i, (singularValuesSorted M i ^ r) ^ 2 := Finset.sum_congr rfl fun i _ => by
            have hn := singularValuesSorted_nonneg M i
            rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hn]; push_cast; ring_nf
  simpa [hleft, hright] using hsum

/-- Lieb-Thirring type inequality for positive semidefinite Hermitian matrices.

For `0 < r <= 1`,
`Tr[(B ^ r) (A ^ r) (B ^ r)] <= Tr[(B A B) ^ r]`, written using
`HermitianMat.conj`. -/
lemma lieb_thirring_le_one
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ((A ^ r).conj (B ^ r).mat).trace ≤ ((A.conj B.mat) ^ r).trace := by
  set Bε : ℝ → HermitianMat d ℂ := fun ε => B + ε • 1
  have hPos : ∀ ε > 0, (Bε ε).mat.PosDef := by
    intro ε hε
    simpa [Bε, add_comm, add_left_comm, add_assoc] using
      ((Matrix.PosDef.one).smul hε).add_posSemidef (HermitianMat.zero_le_iff.mp hB)
  -- Helper to avoid expensive isDefEq: prove f(0) = target explicitly, then rewrite nhds
  have tendsto_helper {f : ℝ → HermitianMat d ℂ} (hf : Continuous f)
      {target : HermitianMat d ℂ} (h0 : f 0 = target) :
      Filter.Tendsto (fun ε => (f ε).trace) (nhdsWithin 0 (Set.Ioi 0)) (nhds target.trace) := by
    rw [← h0]
    simp only [HermitianMat.trace_eq_re_trace]
    exact (RCLike.continuous_re.comp (HermitianMat.continuous_mat.comp hf).matrix_trace).continuousWithinAt.tendsto
  have hleft_tendsto :
      Filter.Tendsto
        (fun ε => ((A ^ r).conj ((Bε ε) ^ r).mat).trace)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (((A ^ r).conj (B ^ r).mat).trace)) :=
    tendsto_helper
      ((HermitianMat.continuous_conj (ρ := A ^ r)).comp
        (HermitianMat.continuous_mat.comp ((rpow_const_continuous hr0.le).comp (by fun_prop))))
      (by simp [Bε])
  have hright_tendsto :
      Filter.Tendsto
        (fun ε => ((A.conj (Bε ε).mat) ^ r).trace)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (((A.conj B.mat) ^ r).trace)) :=
    tendsto_helper
      ((rpow_const_continuous hr0.le).comp
        ((HermitianMat.continuous_conj (ρ := A)).comp
          (HermitianMat.continuous_mat.comp (by fun_prop))))
      (by simp [Bε])
  exact le_of_tendsto_of_tendsto hleft_tendsto hright_tendsto
    (Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => by
      simpa [Bε] using lieb_thirring_le_one_posDef hA (hPos ε hε) hr0 hr1)

end ArakiLiebThirring

/-! ## Rotfel'd Trace Subadditivity

For positive semidefinite `A`, `B` and `0 < p <= 1`, Rotfel'd's inequality says
`Tr[(A + B) ^ p] <= Tr[A ^ p] + Tr[B ^ p]`.

The proof here uses the same resolvent-integral representation as Loewner-Heinz, plus
monotonicity of the trace after inserting square roots. A stronger version can be stated
as a majorization theorem.
-/
open ComplexOrder MatrixOrder MeasureTheory Filter

private lemma trace_conj_mono_sqrt {A B : HermitianMat d ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {t : ℝ} (ht : 0 < t) :
    (((A + B + t • 1)⁻¹).conj A.sqrt.mat).trace ≤ (((A + t • 1)⁻¹).conj A.sqrt.mat).trace := by
  have hInv : (A + B + t • 1)⁻¹ ≤ (A + t • 1)⁻¹ := by
    apply inv_antitone
    · simpa [add_comm, add_left_comm, add_assoc] using
        ((Matrix.PosDef.one).smul ht).add_posSemidef (HermitianMat.zero_le_iff.mp hA)
    · simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hB (A + t • 1)
  have hTrace := HermitianMat.trace_nonneg (show
      0 ≤ ((A + t • 1)⁻¹).conj A.sqrt.mat - ((A + B + t • 1)⁻¹).conj A.sqrt.mat by
    simpa [sub_nonneg] using HermitianMat.conj_mono (M := A.sqrt.mat) hInv)
  simpa [HermitianMat.trace_sub] using hTrace

private lemma trace_conj_sqrt_eq_trace_mul_left {A X : HermitianMat d ℂ} (hA : 0 ≤ A) :
    (((X).conj A.sqrt.mat).trace : ℂ) = (A.mat * X.mat).trace := by
  change algebraMap ℝ ℂ ((X.conj A.sqrt.mat).trace) = (A.mat * X.mat).trace
  simp [HermitianMat.trace_eq_trace, HermitianMat.conj_apply_mat, HermitianMat.conjTranspose_mat]
  rw [Matrix.trace_mul_cycle, HermitianMat.sqrt_sq hA]

private lemma scalarRpowApprox_eq_mul_integral_sub_integral {x q T : ℝ}
    (hx : 0 < x) (hq : 0 < q) (hT : 0 < T) :
    scalarRpowApprox q T x =
      x * (∫ t in (0)..T, t ^ (q - 1) / (x + t)) -
        (∫ t in (0)..T, t ^ (q - 1) / (1 + t)) := by
  have : ∀ t ∈ Set.Ioc (0 : ℝ) T,
      t ^ q * (1 / (1 + t) - 1 / (x + t)) =
        x * (t ^ (q - 1) / (x + t)) - (t ^ (q - 1) / (1 + t)) := by
    intro t ht
    rw [Real.rpow_sub_one ht.1.ne']
    grind
  have hInt (y : ℝ) (hy : 0 < y) :
      Integrable (fun t => t ^ (q - 1) / (y + t)) (volume.restrict (Set.Ioc 0 T)) := by
    apply Integrable.mono' (g := fun t => t ^ (q - 1) / y)
    · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).1.div_const _
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_of_nonneg (div_nonneg (Real.rpow_nonneg ht.1.le _) (by linarith [hy, ht.1]))]
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg ht.1.le _) (by linarith [hy])
        (by linarith [ht.1])
  rw [HermitianMat.scalarRpowApprox, intervalIntegral.integral_of_le hT.le,
    intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_of_le hT.le]
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_sub]
  · exact setIntegral_congr_fun measurableSet_Ioc this
  · exact (hInt x hx).const_mul _
  · simpa using hInt 1 zero_lt_one

private lemma tendsto_mul_intervalIntegral_rpow_div_add {x q : ℝ} (hx : 0 < x)
    (hq : 0 < q) (hq1 : q < 1) :
    Filter.Tendsto
      (fun T => x * (∫ t in (0)..T, t ^ (q - 1) / (x + t)))
      Filter.atTop
      (nhds (rpowConst q * x ^ q)) := by
  have hEq : ∀ᶠ T in Filter.atTop,
      x * (∫ t in (0)..T, t ^ (q - 1) / (x + t)) =
        scalarRpowApprox q T x + (∫ t in (0)..T, t ^ (q - 1) / (1 + t)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
    rw [scalarRpowApprox_eq_mul_integral_sub_integral hx hq hT]
    ring
  rw [Filter.tendsto_congr' hEq]
  convert (scalarRpowApprox_tendsto hx hq hq1).add
    (show Filter.Tendsto
        (fun T => ∫ t in (0)..T, t ^ (q - 1) / (1 + t))
        Filter.atTop
        (nhds (rpowConst q)) from by
      apply MeasureTheory.intervalIntegral_tendsto_integral_Ioi
      · exact rpowConst_integrableOn hq hq1
      · exact Filter.tendsto_id) using 1
  ring_nf


private lemma intervalIntegrable_weighted_div_nonneg {x p T : ℝ}
    (hx : 0 ≤ x) (hp : 0 < p) (hT : 0 < T) :
    IntervalIntegrable (fun t => t ^ (p - 1) * (x / (x + t))) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
  apply Integrable.mono' (g := fun t => t ^ (p - 1))
  · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < p - 1)).1
      |>.mono_set (Set.Ioc_subset_Ioc le_rfl le_rfl)
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _)
      (div_nonneg hx (by linarith [ht.1])))]
    simpa using mul_le_mul_of_nonneg_left
      ((div_le_one (by linarith [ht.1])).2 (by linarith [ht.1]))
      (Real.rpow_nonneg ht.1.le _)

private lemma tendsto_intervalIntegral_weighted_div_nonneg {x p : ℝ}
    (hx : 0 ≤ x) (hp : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto
      (fun T => ∫ t in (0)..T, t ^ (p - 1) * (x / (x + t)))
      Filter.atTop
      (nhds (rpowConst p * x ^ p)) := by
  rcases eq_or_lt_of_le hx with rfl | hx'
  · have hEq : ∀ᶠ T in Filter.atTop,
        (∫ t in (0)..T, t ^ (p - 1) * (0 / (0 + t))) = 0 := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
      apply intervalIntegral.integral_zero_ae
      filter_upwards with t ht
      simp
    rw [Filter.tendsto_congr' hEq]
    simp [Real.zero_rpow hp.ne']
  · have hEq : ∀ᶠ T in Filter.atTop,
        (∫ t in (0)..T, t ^ (p - 1) * (x / (x + t))) =
          x * (∫ t in (0)..T, t ^ (p - 1) / (x + t)) := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
      rw [intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_of_le hT.le]
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioc ?_
      intro t ht
      field_simp [hx'.ne', ht.1.ne']
    rw [Filter.tendsto_congr' hEq]
    exact tendsto_mul_intervalIntegral_rpow_div_add hx' hp hp1

private lemma trace_mul_inv_shift_add_le {A B : HermitianMat d ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {t : ℝ} (ht : 0 < t) :
    (((A + B).mat * (A + B + t • 1).mat⁻¹).trace : ℂ) ≤
      ((A.mat * (A + t • 1).mat⁻¹).trace : ℂ) + ((B.mat * (B + t • 1).mat⁻¹).trace : ℂ) := by
  rw [show (((A + B).mat * (A + B + t • 1).mat⁻¹).trace : ℂ) =
    ((A.mat * (A + B + t • 1).mat⁻¹).trace : ℂ) + ((B.mat * (A + B + t • 1).mat⁻¹).trace : ℂ) from
    by simp [HermitianMat.mat_add, Matrix.add_mul, Matrix.trace_add]]
  apply add_le_add
  · change ((A.mat * ((A + B + t • 1)⁻¹).mat).trace : ℂ) ≤
      ((A.mat * ((A + t • 1)⁻¹).mat).trace : ℂ)
    rw [← trace_conj_sqrt_eq_trace_mul_left hA (X := (A + B + t • 1)⁻¹),
      ← trace_conj_sqrt_eq_trace_mul_left hA (X := (A + t • 1)⁻¹)]
    exact_mod_cast trace_conj_mono_sqrt hA hB ht
  · change ((B.mat * ((A + B + t • 1)⁻¹).mat).trace : ℂ) ≤
      ((B.mat * ((B + t • 1)⁻¹).mat).trace : ℂ)
    rw [← trace_conj_sqrt_eq_trace_mul_left hB (X := (A + B + t • 1)⁻¹),
      ← trace_conj_sqrt_eq_trace_mul_left hB (X := (B + t • 1)⁻¹)]
    exact_mod_cast by simpa [add_comm, add_left_comm, add_assoc] using
      trace_conj_mono_sqrt hB hA ht

private lemma trace_mul_inv_shift_eq_sum_div {A : HermitianMat d ℂ} (hA : 0 ≤ A) {t : ℝ}
    (ht : 0 < t) :
    (((A.mat * (A + t • 1).mat⁻¹).trace : ℂ)).re =
      ∑ i, A.H.eigenvalues i / (A.H.eigenvalues i + t) := by
  change (((A.mat * ((A + t • 1)⁻¹).mat).trace : ℂ)).re = _
  rw [show (A + t • 1)⁻¹ = A.cfc (fun u => (u + t)⁻¹) from by
    rw [show A + t • 1 = A.cfc (fun u => u + t) from by
      rw [show (fun u => u + t) = (fun u => u) + fun _ => t from rfl, cfc_add]
      simp]
    apply inv_cfc_eq_cfc_inv
    intro i
    exact ne_of_gt (add_pos_of_nonneg_of_pos (by simpa using hA.eigenvalues_nonneg i) ht)]
  calc
    (((A.mat * (A.cfc fun u => (u + t)⁻¹).mat).trace : ℂ)).re
        = ∑ i, A.H.eigenvalues i *
            ((A.H.eigenvalues i + t) / Complex.normSq (↑(A.H.eigenvalues i) + ↑t)) := by
              simpa using congrArg Complex.re (HermitianMat.trace_mul_cfc A (fun u => (u + t)⁻¹))
    _ = ∑ i, A.H.eigenvalues i / (A.H.eigenvalues i + t) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hpos : 0 < A.H.eigenvalues i + t := by
            exact add_pos_of_nonneg_of_pos (by simpa using (zero_le_iff.mp hA).eigenvalues_nonneg i) ht
          rw [show ((↑(A.H.eigenvalues i) + ↑t : ℂ)) = ↑(A.H.eigenvalues i + t) by simp,
            Complex.normSq_ofReal]
          field_simp [hpos.ne', div_eq_mul_inv]

private lemma intervalIntegrable_weighted_trace_mul_inv_shift {A : HermitianMat d ℂ}
    (hA : 0 ≤ A) {p T : ℝ} (hp : 0 < p) (hT : 0 < T) :
    IntervalIntegrable
      (fun t => t ^ (p - 1) * (((A.mat * (A + t • 1).mat⁻¹).trace : ℂ)).re)
      volume 0 T := by
  classical
  let g : ℝ → ℝ := fun t =>
    ∑ i, t ^ (p - 1) * (A.H.eigenvalues i / (A.H.eigenvalues i + t))
  have hg : IntervalIntegrable g volume 0 T := by
    unfold g
    classical
    induction (Finset.univ : Finset d) using Finset.induction_on with
    | empty =>
        simp
    | @insert i s hi hs =>
        simpa [Finset.sum_insert hi] using
          (intervalIntegrable_weighted_div_nonneg
            (x := A.H.eigenvalues i) (by simpa using (zero_le_iff.mp hA).eigenvalues_nonneg i)
            hp hT).add hs
  refine hg.congr ?_
  intro t ht
  have htIoc : t ∈ Set.Ioc (0 : ℝ) T := by
    simpa [Set.uIoc_of_le hT.le] using ht
  unfold g
  change ∑ i, t ^ (p - 1) * (A.H.eigenvalues i / (A.H.eigenvalues i + t)) =
    t ^ (p - 1) * (((A.mat * (A + t • 1).mat⁻¹).trace : ℂ)).re
  rw [trace_mul_inv_shift_eq_sum_div hA htIoc.1]
  simp [Finset.mul_sum]

private lemma tendsto_intervalIntegral_weighted_trace_mul_inv_shift {A : HermitianMat d ℂ}
    (hA : 0 ≤ A) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto
      (fun T => ∫ t in (0)..T, t ^ (p - 1) * (((A.mat * (A + t • 1).mat⁻¹).trace : ℂ)).re)
      Filter.atTop
      (nhds (rpowConst p * (A ^ p).trace)) := by
  classical
  have hEq : ∀ᶠ T in Filter.atTop,
      (∫ t in (0)..T, t ^ (p - 1) * (((A.mat * (A + t • 1).mat⁻¹).trace : ℂ)).re) =
        ∑ i, ∫ t in (0)..T, t ^ (p - 1) * (A.H.eigenvalues i / (A.H.eigenvalues i + t)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
    calc
      (∫ t in (0)..T, t ^ (p - 1) * (((A.mat * (A + t • 1).mat⁻¹).trace : ℂ)).re)
          = ∫ t in (0)..T, ∑ i, t ^ (p - 1) * (A.H.eigenvalues i / (A.H.eigenvalues i + t)) := by
              apply intervalIntegral.integral_congr_ae
              filter_upwards with t ht
              rw [trace_mul_inv_shift_eq_sum_div hA (by
                have htIoc : t ∈ Set.Ioc (0 : ℝ) T := by
                  simpa [Set.uIoc_of_le hT.le] using ht
                exact htIoc.1)]
              simp [Finset.mul_sum]
      _ = ∑ i, ∫ t in (0)..T, t ^ (p - 1) * (A.H.eigenvalues i / (A.H.eigenvalues i + t)) := by
            rw [intervalIntegral.integral_finsetSum]
            intro i hi
            exact intervalIntegrable_weighted_div_nonneg
              (x := A.H.eigenvalues i) (by simpa using (zero_le_iff.mp hA).eigenvalues_nonneg i)
              hp hT
  rw [Filter.tendsto_congr' hEq]
  simpa [trace_rpow_eq_sum, Finset.mul_sum] using
    (tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_intervalIntegral_weighted_div_nonneg
        (x := A.H.eigenvalues i) (by simpa using (zero_le_iff.mp hA).eigenvalues_nonneg i)
        hp hp1)

/-- Rotfel'd trace subadditivity for positive semidefinite Hermitian matrices.

For `0 < p <= 1`, `Tr[(A + B) ^ p] <= Tr[A ^ p] + Tr[B ^ p]`. -/
lemma trace_rpow_add_le
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ((A + B) ^ p).trace ≤ (A ^ p).trace + (B ^ p).trace := by
  by_cases hp_eq : p = 1; · subst hp_eq; simp
  have hp1' : p < 1 := lt_of_le_of_ne hp1 hp_eq
  suffices hmono :
      (fun T => ∫ t in (0)..T, t ^ (p - 1) * ((((A + B).mat * (A + B + t • 1).mat⁻¹).trace : ℂ)).re)
        ≤ᶠ[Filter.atTop]
      (fun T => (∫ t in (0)..T, t ^ (p - 1) * (((A.mat * (A + t • 1).mat⁻¹).trace : ℂ)).re) +
          (∫ t in (0)..T, t ^ (p - 1) * (((B.mat * (B + t • 1).mat⁻¹).trace : ℂ)).re)) by
    exact le_of_mul_le_mul_left
      (by
        simpa [mul_add] using le_of_tendsto_of_tendsto
          (tendsto_intervalIntegral_weighted_trace_mul_inv_shift (add_nonneg hA hB) p hp hp1')
          ((tendsto_intervalIntegral_weighted_trace_mul_inv_shift hA p hp hp1').add
            (tendsto_intervalIntegral_weighted_trace_mul_inv_shift hB p hp hp1'))
          hmono)
      (rpowConst_pos hp hp1')
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
  rw [← intervalIntegral.integral_add
    (intervalIntegrable_weighted_trace_mul_inv_shift hA hp hT)
    (intervalIntegrable_weighted_trace_mul_inv_shift hB hp hT)]
  refine intervalIntegral.integral_mono_on hT.le
    (intervalIntegrable_weighted_trace_mul_inv_shift (add_nonneg hA hB) hp hT)
    ((intervalIntegrable_weighted_trace_mul_inv_shift hA hp hT).add
      (intervalIntegrable_weighted_trace_mul_inv_shift hB hp hT)) ?_
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | ht0
  · simp [Real.zero_rpow (sub_ne_zero.mpr hp_eq)]
  · simpa [mul_add] using mul_le_mul_of_nonneg_left
      (show ((((A + B).mat * (A + B + t • 1).mat⁻¹).trace : ℂ)).re ≤
          (((A.mat * (A + t • 1).mat⁻¹).trace : ℂ)).re +
            (((B.mat * (B + t • 1).mat⁻¹).trace : ℂ)).re from by
        simpa [Complex.add_re] using (Complex.le_def.mp (trace_mul_inv_shift_add_le hA hB ht0)).1)
      (Real.rpow_nonneg ht0.le _)
