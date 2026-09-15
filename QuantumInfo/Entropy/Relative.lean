/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Entropy.SSA
public import QuantumInfo.Entropy.VonNeumann
public import QuantumInfo.ForMathlib.HermitianMat.BlockDiag
public import QuantumInfo.ForMathlib.HermitianMat.Unitary
public import Physlib.Meta.Sorry

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

noncomputable section

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]
variable {dA dB dC dA₁ dA₂ : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α : ℝ} {ρ σ : MState d}

open scoped Matrix ComplexOrder InnerProductSpace RealInnerProductSpace HermitianMat

/-!
To do relative entropies, we start with the _sandwiched Renyi Relative Entropy_ which is a nice general form.
Then instead of proving many theorems (like DPI, relabelling, additivity, etc.) several times, we just prove
it for this one quantity, then it follows for other quantities (like the relative entropy) as a special case.
-/

--Note: without the assumption `h`, we could still get nonnegativity, just not strict positivity.
private theorem sandwiched_trace_pos (h : σ.M.ker ≤ ρ.M.ker) :
    0 < ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace := by
  apply HermitianMat.trace_pos
  apply HermitianMat.rpow_pos
  apply HermitianMat.conj_pos ρ.pos
  grw [← h]
  exact HermitianMat.ker_rpow_le_of_nonneg σ.nonneg

--TODO: We don't actually use this, and it's not clear that it's useful (since it's just a
-- specialization); remove?
omit [DecidableEq d] in
/--
Weighted Jensen inequality: for weights w_j ≥ 0 with ∑ w_j = 1, values b_j ≥ 0,
and q ≥ 1: (∑_j w_j * b_j)^q ≤ ∑_j w_j * b_j^q.

This is the special case of `Real.rpow_arith_mean_le_arith_mean_rpow` applied to
`Finset.univ`
-/
lemma weighted_jensen_rpow (b w : d → ℝ) (q : ℝ)
  (hb : ∀ j, 0 ≤ b j) (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) (hq : 1 ≤ q) :
    (∑ j, w j * b j) ^ q ≤ ∑ j, w j * b j ^ q :=
  Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ _ _ (fun i _ ↦ hw i) hsum (fun i _ ↦ hb i) hq

omit [DecidableEq d] in
/--
Doubly stochastic Hölder inequality: for nonneg a, b, doubly stochastic w,
and conjugate p, q > 1:
∑_{ij} a_i * b_j * w_{ij} ≤ (∑ a_i^p)^{1/p} * (∑ b_j^q)^{1/q}.
-/
lemma doubly_stochastic_holder (a b : d → ℝ) (w : d → d → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hw : ∀ i j, 0 ≤ w i j)
    (hrow : ∀ i, ∑ j, w i j = 1) (hcol : ∀ j, ∑ i, w i j = 1)
    (p q : ℝ) (hp : 1 < p) (hpq : 1/p + 1/q = 1) :
    ∑ i, ∑ j, a i * b j * w i j ≤ (∑ i, a i ^ p) ^ (1/p) * (∑ j, b j ^ q) ^ (1/q) := by
  by_contra h_contra
  contrapose! h_contra with h_contra
  simp_all [ ← Finset.mul_sum, mul_assoc ]
  have h0q : 0 < q :=
    lt_of_le_of_ne ( le_of_not_gt fun hq => by { rw [ inv_eq_one_div, div_eq_mul_inv ] at hpq; nlinarith [ inv_mul_cancel₀ ( by linarith : ( p : ℝ ) ≠ 0 ), inv_lt_zero.2 hq ] } ) (by grind)
  -- Apply Hölder's inequality with the sequences $a_i$ and $g_i = \sum_j w_{ij} b_j$.
  have h_holder : (∑ i, a i * (∑ j, w i j * b j)) ≤ (∑ i, a i ^ p) ^ (1 / p) * (∑ i, (∑ j, w i j * b j) ^ q) ^ (1 / q) := by
    have := @Real.inner_le_Lp_mul_Lq
    simp_all
    convert this Finset.univ a ( fun i => ∑ j, w i j * b j ) ( show p.HolderConjugate q from ?_ ) using 1
    · simp only [ha, abs_of_nonneg, mul_eq_mul_left_iff]
      left
      congr!
      symm
      exact abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (hw _ _) (hb _))
    · constructor <;> linarith
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ i, (∑ j, w i j * b j) ^ q ≤ ∑ j, b j ^ q := by
    -- Apply Jensen's inequality to the convex function $x^q$ with weights $w_{ij}$.
    have h_jensen : ∀ i, (∑ j, w i j * b j) ^ q ≤ ∑ j, w i j * b j ^ q := by
      intro i
      have h_jensen : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ q) := by
        apply convexOn_rpow
        nlinarith [ inv_pos.2 ( zero_lt_one.trans hp ), inv_pos.2 h0q, mul_inv_cancel₀ h0q.ne']
      convert h_jensen.map_sum_le _ _ _ <;> aesop
    refine' le_trans ( Finset.sum_le_sum fun i _ => h_jensen i ) _;
    rw [ Finset.sum_comm ]
    simp [ ← Finset.sum_mul, hcol]
  simp_all only [mul_comm];
  simpa using h_holder.trans ( mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow ( Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ( Finset.sum_nonneg fun _ _ => mul_nonneg ( hb _ ) ( hw _ _ ) ) _ ) h_fubini (one_div_nonneg.mpr h0q.le)) ( Real.rpow_nonneg ( Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ( ha _ ) _ ) _ ) ) |> le_trans <| by simp;

--PULLOUT
/--
Hermitian trace Hölder inequality: for PSD A, B and conjugate exponents p, q > 1,
⟪A, B⟫ ≤ Tr[A^p]^(1/p) * Tr[B^q]^(1/q).
-/
lemma HermitianMat.inner_le_trace_rpow_mul
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p q : ℝ) (hp : 1 < p) (hpq : 1/p + 1/q = 1) :
    ⟪A, B⟫_ℝ ≤ (A ^ p).trace ^ (1/p) * (B ^ q).trace ^ (1/q) := by
  by_cases hq : q > 1;
  · -- Apply the doubly_stochastic_holder lemma with the weights $w_{ij} = \|C_{ij}\|^2$.
    rw [trace_rpow_eq_sum, trace_rpow_eq_sum, inner_eq_doubly_stochastic_sum]
    refine doubly_stochastic_holder
      A.H.eigenvalues B.H.eigenvalues
      (fun i j ↦ ‖(A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val) i j‖ ^ 2)
      (fun i ↦ by simpa using hA.eigenvalues_nonneg i)
      (fun i ↦ by simpa using hB.eigenvalues_nonneg i)
      (by bound) ?_ ?_ p q hp hpq
    · apply Matrix.unitary_row_sum_norm_sq (A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val)
      simp [mul_assoc]
      simp [← mul_assoc, Matrix.IsHermitian.eigenvectorUnitary]
    · apply Matrix.unitary_col_sum_norm_sq (A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val)
      simp [mul_assoc]
      simp [← mul_assoc, Matrix.IsHermitian.eigenvectorUnitary]
  · rcases eq_or_ne q 0 with _ | _
    · grind only [cases Or]
    · field_simp at hpq
      nlinarith

--PULLOUT
lemma MState.rpow_le_one' {r : ℝ} (hσ : 0 < r) : σ.M ^ r ≤ 1 := by
  rw [HermitianMat.le_iff]
  have h1 : 1 - σ.M ^ r = σ.M.cfc (fun x => 1 - x ^ r) := by
    rw [HermitianMat.rpow_eq_cfc]
    have : σ.M.cfc (fun _ => (1:ℝ)) = 1 := by ext1; simp
    rw [← this, ← HermitianMat.cfc_sub_apply]
  rw [h1, ← HermitianMat.zero_le_iff, HermitianMat.cfc_nonneg_iff]
  intro i
  have hge : 0 ≤ σ.M.H.eigenvalues i :=
    (HermitianMat.zero_le_iff.mp σ.nonneg).eigenvalues_nonneg i
  have hle : σ.M.H.eigenvalues i ≤ 1 := σ.eigenvalue_le_one i
  linarith [Real.rpow_le_one hge hle hσ.le]

--PULLOUT
/-- If A ≥ 0 and A ≤ 1, then each eigenvalue of A is in [0, 1]. -/
lemma HermitianMat.eigenvalues_le_one_of_le_one
    (A : HermitianMat d ℂ) (hA1 : A ≤ 1) (i : d) :
    A.H.eigenvalues i ≤ 1 := by
  by_contra! h
  obtain ⟨v, hv₁, hv₂⟩ : ∃ v : EuclideanSpace ℂ d, ‖v‖ = 1 ∧ A.mat.mulVec v = (A.H.eigenvalues i) • v := by
    use A.H.eigenvectorBasis i
    exact ⟨A.H.eigenvectorBasis.orthonormal.1 i, A.H.mulVec_eigenvectorBasis i⟩
  have h_eigenvalue : star v ⬝ᵥ A.mat.mulVec v = (A.H.eigenvalues i) * star v ⬝ᵥ v := by
    rw [hv₂, dotProduct_smul, Complex.real_smul]
  have h_unit : star v ⬝ᵥ v = 1 := by
    simp only [EuclideanSpace.norm_eq, Real.sqrt_eq_one, dotProduct, Pi.star_apply,
      RCLike.star_def]  at hv₁ ⊢
    simp only [sq, Complex.ext_iff, Complex.re_sum, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.mul_im, neg_mul, sub_neg_eq_add, Complex.im_sum,
      Complex.one_re, Complex.one_im] at hv₁ ⊢
    simp only [Complex.norm_def, Complex.normSq, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      mul_comm, add_neg_cancel, Finset.sum_const_zero, and_true] at hv₁ ⊢
    rw [← hv₁]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [Real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))]
  open ComplexOrder in
  have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hA1).2 v
  simp only [val_eq_coe, mul_one, mat_one, Matrix.sub_mulVec,
    Matrix.one_mulVec, dotProduct_sub, h_eigenvalue, h_unit] at this
  norm_cast at this
  linarith

--PULLOUT
/-- For positive A ≤ 1 and p ≥ 1, `Tr[A^p] ≤ Tr[A]`.
-/
lemma HermitianMat.trace_rpow_le_trace_of_le_one
    (A : HermitianMat d ℂ) (hA : 0 ≤ A) (hA1 : A ≤ 1)
    (p : ℝ) (hp : 1 ≤ p) :
    (A ^ p).trace ≤ A.trace := by
  -- Rewrite both sides using trace_rpow_eq_sum: Tr[A^p] = ∑ λ_i^p and Tr[A] = ∑ λ_i (using trace_rpow_eq_sum and rpow_one for the latter).
  have h_trace_eq_sum : (A ^ p).trace = ∑ i, (A.H.eigenvalues i) ^ p ∧ A.trace = ∑ i, (A.H.eigenvalues i) := by
    exact ⟨ by rw [ HermitianMat.trace_rpow_eq_sum ], by rw [ show A.trace = ∑ i, ( A.H.eigenvalues i ) by simpa using HermitianMat.trace_rpow_eq_sum A 1 ] ⟩;
  rw [ h_trace_eq_sum.1, h_trace_eq_sum.2 ];
  apply_rules [ Finset.sum_le_sum ];
  intro i hi; by_cases hi0 : A.H.eigenvalues i = 0 <;> simp_all
  · rw [ Real.zero_rpow ( by positivity ) ];
  · conv_rhs => rw [← (A.H.eigenvalues i).rpow_one]
    apply Real.rpow_le_rpow_of_exponent_ge
    · exact lt_of_le_of_ne' (le_of_not_gt fun hi => hi0 <| by linarith [ show 0 ≤ A.H.eigenvalues i by simpa using hA.eigenvalues_nonneg i ] ) hi0
    · exact A.eigenvalues_le_one_of_le_one hA1 i
    · exact hp

private lemma trace_conj_rpow_eq_inner (hα₀ : 0 < α) (hα : α < 1) :
    ((ρ.M ^ α).conj (σ.M ^ ((1 - α) / (2 * α) * α)).mat).trace = ⟪ρ.M ^ α, σ.M ^ (1 - α)⟫_ℝ := by
  convert congr_arg _ ( HermitianMat.inner_eq_trace_rc _ _ ) using 2;
  rotate_left;
  rotate_left;
  rotate_left;
  exact d;
  exact ℂ;
  all_goals try infer_instance;
  exact ρ ^ α;
  exact σ ^ ( 1 - α );
  rotate_right;
  exact fun x => x.re;
  · unfold HermitianMat.conj;
    simp [ Matrix.trace, Matrix.mul_apply, inner]
    rw [ show ( 1 - α ) / ( 2 * α ) * α = ( 1 - α ) / 2 by rw [ div_mul_eq_mul_div, div_eq_iff ] <;> linarith ];
    -- By the properties of the trace, we can rearrange the terms inside the trace.
    have h_trace : Matrix.trace ((σ.M ^ ((1 - α) / 2)).mat * (ρ.M ^ α).mat * (σ.M ^ ((1 - α) / 2)).mat) = Matrix.trace ((ρ.M ^ α).mat * (σ.M ^ (1 - α)).mat) := by
      have h_trace : (σ.M ^ ((1 - α) / 2)).mat * (σ.M ^ ((1 - α) / 2)).mat = (σ.M ^ (1 - α)).mat := by
        have := σ.nonneg;
        rw [ ← HermitianMat.mat_rpow_add this ]
        ring_nf
        linarith;
      rw [ ← h_trace, Matrix.mul_assoc ];
      rw [ ← Matrix.trace_mul_comm ]
      simp [ Matrix.mul_assoc ]
    convert! congr_arg Complex.re h_trace using 1;
    simp [ Matrix.trace, Matrix.mul_apply ];
  · exact HermitianMat.inner_eq_re_trace _ _

private lemma inner_rpow_le_one (hα₀ : 0 < α) (hα : α < 1) :
    ⟪ρ.M ^ α, σ.M ^ (1 - α)⟫_ℝ ≤ 1 := by
  convert HermitianMat.inner_le_trace_rpow_mul
      (HermitianMat.rpow_nonneg ρ.nonneg) (HermitianMat.rpow_nonneg σ.nonneg)
      (1 / α) (1 / (1 - α)) _ _ using 1
  · rw [← HermitianMat.rpow_mul ρ.nonneg, ← HermitianMat.rpow_mul σ.nonneg]
    simp [hα₀.ne', (sub_pos.mpr hα).ne']
  · field_simp
    exact hα
  · simp

private theorem sandwiched_trace_of_lt_1 (hα₀ : 0 < α) (hα : α < 1) :
    ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace ≤ 1 := by
    have h1α : 0 < 1 - α := sub_pos.mpr hα
    -- Apply trace_rpow_conj_le with p = 2 and q = 2α/(1-α)
    set t := (1 - α) / (2 * α) with ht_def
    have ht_pos : 0 < t := by positivity
    have hp : (0 : ℝ) < 2 := by positivity
    have hq : (0 : ℝ) < 2 * α / (1 - α) := by positivity
    have hpq : 1 / (2 * α) = 1 / 2 + 1 / (2 * α / (1 - α)) := by
      field_simp
      ring
    calc ((ρ.M.conj (σ.M ^ t).mat) ^ α).trace
        ≤ (((ρ.M ^ (2 / 2)).trace) ^ (1 / 2) *
          (((σ.M ^ t) ^ (2 * α / (1 - α))).trace) ^ (1 / (2 * α / (1 - α)))) ^ (2 * α) :=
          HermitianMat.trace_rpow_conj_le ρ.nonneg (HermitianMat.rpow_nonneg σ.nonneg) hα₀ hp hq hpq
      _ = 1 := by
          -- Simplify: ρ.M ^ (2/2) = ρ.M ^ 1 = ρ.M, Tr[ρ.M] = 1
          -- (σ.M ^ t) ^ (2α/(1-α)) = σ.M ^ (t * 2α/(1-α)) = σ.M ^ 1, Tr[σ.M] = 1
          have h1 : (2 : ℝ) / 2 = 1 := by norm_num
          have h2 : t * (2 * α / (1 - α)) = 1 := by
            rw [ht_def]; field_simp
          rw [h1, HermitianMat.rpow_one,
              ← HermitianMat.rpow_mul σ.nonneg, h2, HermitianMat.rpow_one,
              ρ.tr, σ.tr]
          simp

/-- For PSD A and p ≠ 0, `A^{-p} * A^p = HermitianMat.supportProj A`. -/
lemma HermitianMat.rpow_neg_mul_rpow_eq_supportProj
    {A : HermitianMat d ℂ} (hA : 0 ≤ A) {p : ℝ} (hp : p ≠ 0) :
    (A ^ (-p)).mat * (A ^ p).mat = A.supportProj.mat := by
  unfold HermitianMat.supportProj;
  have h_cfc : (A ^ (-p)).mat * (A ^ p).mat = (A.cfc (fun x => x ^ (-p))) * (A.cfc (fun x => x ^ p)) := by
    congr! 1;
  rw [ h_cfc, ← mat_cfc_mul ];
  have h_cfc : ∀ x : ℝ, 0 ≤ x → x ^ (-p) * x ^ p = if x = 0 then 0 else 1 := by
    intro x hx; by_cases hx' : x = 0 <;> simp [ hx', Real.rpow_neg, hx, hp ] ;
  have h_cfc_eq : (A.cfc (fun x => x ^ (-p) * x ^ p)) = (A.cfc (fun x => if x = 0 then 0 else 1)) := by
    apply cfc_congr_of_nonneg hA;
    exact fun x hx => h_cfc x hx;
  convert! congr_arg ( fun x : HermitianMat d ℂ => x.val ) h_cfc_eq using 1;
  exact congr_arg ( fun x : HermitianMat d ℂ => x.val ) ( supportProj_eq_cfc A )

lemma HermitianMat.supportProj_mul_self (A : HermitianMat d ℂ) :
    A.supportProj.mat * A.mat = A.mat := by
  have h_supportProj_mul_A : ∀ (v : d → ℂ), (A.supportProj.val.mulVec (A.val.mulVec v)) = (A.val.mulVec v) := by
    intro v
    have h_range : WithLp.toLp 2 (A.val.mulVec v) ∈ LinearMap.range A.val.toEuclideanLin := by
      exact ⟨ _, rfl ⟩
    have h_supportProj_mul_A : ∀ (v : EuclideanSpace ℂ d), v ∈ LinearMap.range A.val.toEuclideanLin → (A.supportProj.val.toEuclideanLin v) = v := by
      intro v hv
      have h_supportProj_mul_A : (A.supportProj.val.toEuclideanLin v) = (Submodule.orthogonalProjectionOnto (LinearMap.range A.val.toEuclideanLin) v) := by
        simp only [val_eq_coe, Submodule.coe_orthogonalProjectionOnto_apply]
        simp [supportProj, projector]
        simp only [Submodule.starProjection]
        simp
        have key : ∀ (f : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d),
            Matrix.toEuclideanLin
              ((LinearMap.toMatrix (EuclideanSpace.basisFun d ℂ).toBasis (EuclideanSpace.basisFun d ℂ).toBasis) f) = f := by
          intro f
          rw [Matrix.toEuclideanLin, Matrix.toLpLin_eq_toLin]
          exact Matrix.toLin_toMatrix _ _ f
        have hsup : A.support = (Matrix.toEuclideanLin (↑A : Matrix d d ℂ)).range := by
          simp [HermitianMat.support, HermitianMat.lin]
        rw [key, LinearMap.comp_apply, Submodule.subtype_apply, hsup]
        rfl
      rw [h_supportProj_mul_A]
      exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero (by simpa using hv) (by simp)
    exact congr(WithLp.ofLp $(h_supportProj_mul_A _ h_range))
  exact Matrix.toLin'.injective ( LinearMap.ext fun v => by simpa using h_supportProj_mul_A v )

lemma HermitianMat.inner_supportProj_self (A : HermitianMat d ℂ) :
    ⟪A, A.supportProj⟫ = A.trace := by
  simp only [trace, IsMaximalSelfAdjoint.RCLike_selfadjMap, Matrix.trace, Matrix.diag_apply,
    mat_apply, map_sum, RCLike.re_to_complex]
  simp only [inner, IsMaximalSelfAdjoint.RCLike_selfadjMap, RCLike.re_to_complex];
  convert congr_arg Complex.re ( congr_arg Matrix.trace ( HermitianMat.supportProj_mul_self A ) ) using 1;
  · simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, mat_apply, Complex.re_sum,
      Complex.mul_re, Finset.sum_sub_distrib, mul_comm];
    exact congrArg₂ _ ( Finset.sum_comm ) ( Finset.sum_comm );
  · simp only [Matrix.trace, Matrix.diag_apply, mat_apply, Complex.re_sum]

lemma HermitianMat.mul_supportProj_of_ker_le {A B : HermitianMat d ℂ}
  (h : LinearMap.ker B.lin.toLinearMap ≤ LinearMap.ker A.lin.toLinearMap) :
    A.mat * B.supportProj.mat = A.mat := by
  -- Since $B.supportProj$ is the projection onto $range B$, we have $B.supportProj * B.mat = B.mat$.
  have h_supportProj_mul_B : B.supportProj.mat * B.mat = B.mat := by
    exact supportProj_mul_self B
  have h_range_A_subset_range_B : LinearMap.range A.lin.toLinearMap ≤ LinearMap.range B.lin.toLinearMap := by
    have h_orthogonal_complement : LinearMap.range (B.lin : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d) = (LinearMap.ker (B.lin : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d))ᗮ := by
      have h_orthogonal_complement : ∀ (T : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d), T = T.adjoint → LinearMap.range T = (LinearMap.ker T)ᗮ := by
        intro T hT;
        refine' Submodule.eq_of_le_of_finrank_eq _ _;
        · rintro x ⟨y, rfl⟩
          rw [Submodule.mem_orthogonal' (LinearMap.ker T) (T y)]
          intro z hz
          rw [LinearMap.mem_ker] at hz
          simp [← LinearMap.adjoint_inner_right, ← hT, hz]
        · have := LinearMap.finrank_range_add_finrank_ker T;
          have := Submodule.finrank_add_finrank_orthogonal (LinearMap.ker T)
          linarith;
      apply h_orthogonal_complement
      simp
    have h_orthogonal_complement_A : LinearMap.range (A.lin : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d) ≤ (LinearMap.ker (A.lin : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d))ᗮ := by
      intro x hx y hy
      simp_all only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, LinearMap.mem_ker]
      obtain ⟨ z, rfl ⟩ := hx;
      have h_orthogonal_complement_A : ∀ (y z : EuclideanSpace ℂ d), ⟪y, A.lin z⟫_ℂ = ⟪A.lin y, z⟫_ℂ := by
        simp
      rw [ h_orthogonal_complement_A, hy, inner_zero_left ];
    exact h_orthogonal_complement.symm ▸ le_trans h_orthogonal_complement_A ( Submodule.orthogonal_le h );
  -- Since $B.supportProj$ is the projection onto $range B$, and $range A \subseteq range B$, we have $B.supportProj * A = A$.
  have h_supportProj_mul_A : ∀ (v : EuclideanSpace ℂ d), B.supportProj.mat.mulVec (A.mat.mulVec v) = A.mat.mulVec v := by
    intro v
    obtain ⟨w, hw⟩ : WithLp.toLp 2 (A.mat.mulVec v) ∈ LinearMap.range B.lin.toLinearMap := by
      exact h_range_A_subset_range_B ( Set.mem_range_self v );
    replace h_supportProj_mul_B := congr(Matrix.mulVec $h_supportProj_mul_B w)
    replace hw := congr(WithLp.ofLp $hw)
    simp only [ContinuousLinearMap.coe_coe] at hw
    simp_all only [← hw, ← Matrix.mulVec_mulVec]
    exact h_supportProj_mul_B
  -- By definition of matrix multiplication, if B.supportProj * A * v = A * v for all vectors v, then B.supportProj * A = A.
  have h_matrix_eq : ∀ (M N : Matrix d d ℂ), (∀ v : EuclideanSpace ℂ d, M.mulVec (N.mulVec v) = N.mulVec v) → M * N = N := by
    intro M N hMN
    ext i j
    specialize hMN (WithLp.toLp 2 ( Pi.single j 1 ))
    replace hMN := congr_fun hMN i
    aesop;
  rw [← Matrix.conjTranspose_inj]
  simp_all only [Matrix.mulVec_mulVec, Matrix.conjTranspose_mul, conjTranspose_mat, implies_true]

lemma HermitianMat.inner_supportProj_of_ker_le {A B : HermitianMat d ℂ}
  (h : LinearMap.ker B.lin.toLinearMap ≤ LinearMap.ker A.lin.toLinearMap) :
    ⟪A, B.supportProj⟫ = A.trace := by
  rw [inner_def, mul_supportProj_of_ker_le h, trace]

lemma supportProj_inner_density (h : σ.M.ker ≤ ρ.M.ker) :
    ⟪σ.M.supportProj, ρ.M⟫_ℝ = 1 := by
  rw [HermitianMat.inner_comm, HermitianMat.inner_supportProj_of_ker_le h]
  simp

/-
⟪ρ.M.conj (σ.M ^ t).mat, σ.M ^ (-2 * t)⟫_ℝ = 1 for density matrices ρ, σ with ker(σ) ≤ ker(ρ).
-/
private lemma sandwiched_inner_eq_one (h : σ.M.ker ≤ ρ.M.ker) (t : ℝ) :
    ⟪ρ.M.conj (σ.M ^ t).mat, σ.M ^ (-2 * t)⟫_ℝ = 1 := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · have h_combine : (σ.M ^ (-2 * t)).mat * (σ.M ^ t).mat = (σ.M ^ (-t)).mat := by
      rw [show (-t : ℝ) = -2 * t + t by ring, HermitianMat.mat_rpow_add σ.nonneg]
      contrapose! ht
      linarith
    have h_support : (σ.M ^ t).mat * (σ.M ^ (-t)).mat = σ.M.supportProj.mat := by
      rw [← neg_ne_zero] at ht
      simpa only [neg_neg] using σ.M.rpow_neg_mul_rpow_eq_supportProj σ.nonneg ht
    rw [HermitianMat.inner_def, HermitianMat.conj_apply_mat, HermitianMat.conjTranspose_mat]
    rw [Matrix.trace_mul_comm, ← mul_assoc, ← mul_assoc, h_combine]
    rw [Matrix.trace_mul_cycle, h_support, ← HermitianMat.inner_def]
    exact supportProj_inner_density h

private theorem sandwiched_trace_of_gt_1 (h : σ.M.ker ≤ ρ.M.ker) (hα : α > 1) :
    1 ≤ ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace := by
  -- Let t = (1 - α) / (2 * α), A = ρ.M.conj (σ.M ^ t) and B = σ.M ^ (-2 * t)
  set t : ℝ := (1 - α) / (2 * α)
  set A := ρ.M.conj (σ.M ^ t).mat
  set B := σ.M ^ (-2 * t)
  have h_trace : ⟪A, B⟫ = 1 := sandwiched_inner_eq_one h t
  have h_inner : ⟪A, B⟫ ≤ (A ^ α).trace ^ (1 / α) * (B ^ (α / (α - 1))).trace ^ (1 / (α / (α - 1))) := by
    apply HermitianMat.inner_le_trace_rpow_mul
    · positivity
    · exact HermitianMat.rpow_nonneg σ.nonneg --TODO positivity
    · exact hα
    · rw [div_div_eq_mul_div, div_add_div, div_eq_iff]
      · ring
      · positivity
      · positivity
      · positivity
  have h_trace_B : (B ^ (α / (α - 1))).trace = 1 := by
    have hB : B ^ (α / (α - 1)) = σ.M ^ (-2 * t * (α / (α - 1))) := by
      rw [HermitianMat.rpow_mul σ.nonneg]
    have h : -2 * t * ( α / ( α - 1 ) ) = 1 := by
      rw [mul_div, div_eq_iff]
      · linarith [mul_div_cancel₀ (1 - α) (by linarith : (2 * α) ≠ 0)]
      · linarith only [hα]
    rw [hB, h]
    simp
  have h_final : 1 ≤ (A ^ α).trace ^ (1 / α) := by
    simpa only [h_trace, one_div, h_trace_B, Real.one_rpow, mul_one] using h_inner
  have : 0 ≤ (A ^ α).trace := by
    --TODO: Make this all discharge via just `positivity`.
    apply HermitianMat.trace_nonneg
    apply HermitianMat.rpow_nonneg
    positivity
  refine le_of_not_gt fun h => h_final.not_gt ?_
  simpa using Real.rpow_lt_one this h (by positivity)

private theorem sandwichedRelRentropy_nonneg_α_lt_1 (h : σ.M.ker ≤ ρ.M.ker) (hα0 : 0 < α) (hα : α < 1) :
    0 ≤ ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace.log / (α - 1) := by
  apply div_nonneg_of_nonpos
  · apply Real.log_nonpos
    · exact (sandwiched_trace_pos h).le
    · exact sandwiched_trace_of_lt_1 hα0 hα
  · linarith

private theorem sandwichedRelRentropy_nonneg_α_gt_1 (h : σ.M.ker ≤ ρ.M.ker) (hα : α > 1) :
    0 ≤ ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace.log / (α - 1) := by
  grw [← sandwiched_trace_of_gt_1 h hα]
  positivity
  positivity

private lemma sandwichedRelRentropy.trace_at_one (ρ σ : MState d) :
    ((ρ.M.conj (σ.M ^ ((1 - (1:ℝ)) / (2 * (1:ℝ)))).mat) ^ (1:ℝ)).trace = 1 := by
  simp

/-
For fixed PSD B, the derivative of α ↦ Tr[B^α] at α = 1 is ⟪B, B.log⟫ = Tr[B log B].
-/
private lemma hasDerivAt_trace_rpow_at_one (B : HermitianMat d ℂ) (hB : 0 ≤ B) :
    HasDerivAt (fun α : ℝ => (B ^ α).trace) ⟪B, B.log⟫ 1 := by
  have h_inner : ⟪B, B.log⟫ = ∑ i, (B.H.eigenvalues i) * Real.log (B.H.eigenvalues i) := by
    -- By definition of the inner product, we have ⟪B, B.log⟫ = tr(B * B.log).
    have h_inner_def : ⟪B, B.log⟫ = Matrix.trace (B.mat * B.log.mat) := by
      simp [ Matrix.trace, Inner.inner ];
      refine' Finset.sum_congr rfl fun i _ => _;
      have h_herm : (B * B.log : Matrix d d ℂ).IsHermitian := by
        have h_comm : Commute (B : Matrix d d ℂ) (B.log : Matrix d d ℂ) := by
          commutes
        simp_all [Matrix.IsHermitian]
        rw [h_comm]
      have := h_herm.apply i i
      simp_all [Complex.ext_iff]
      linarith
    -- By definition of the trace, we have tr(B * B.log) = ∑ i, B.eigenvalues i * log(B.eigenvalues i).
    have h_trace : (B.mat * B.log.mat).trace = ∑ i, B.H.eigenvalues i * Real.log (B.H.eigenvalues i) := by
      have h_trace : (B ^ 1 * B.log.mat).trace = (B.cfc (fun x ↦ x * Real.log x)).trace := by
        have h_trace : B ^ 1 * B.log.mat = B.cfc (fun x ↦ x * Real.log x) := by
          have h_log : B ^ 1 * B.log.mat = B.cfc id * B.cfc Real.log := by
            simp [pow_one, HermitianMat.log]
          rw [h_log]
          exact (B.mat_cfc_mul_apply id Real.log).symm
        rw [h_trace, ← HermitianMat.trace_eq_trace_rc]
        rfl
      simp_all [ HermitianMat.trace_cfc_eq ];
    exact_mod_cast h_inner_def.trans h_trace;
  have h_deriv : ∀ i, HasDerivAt (fun α : ℝ => (B.H.eigenvalues i) ^ α) (B.H.eigenvalues i * Real.log (B.H.eigenvalues i)) 1 := by
    intro i
    by_cases h_pos : 0 < B.H.eigenvalues i;
    · convert! HasDerivAt.rpow ( hasDerivAt_const _ _ ) ( hasDerivAt_id 1 ) h_pos using 1
      simp only [id_eq, mul_one, sub_self, Real.rpow_zero, Real.rpow_one, one_mul, zero_add]
    · have h_zero : B.H.eigenvalues i = 0 := by
        exact le_antisymm ( le_of_not_gt h_pos ) ( by simpa using hB.eigenvalues_nonneg i )
      simp [h_zero]
      exact (hasDerivAt_const _ _).congr_of_eventuallyEq (Filter.eventuallyEq_of_mem ( Ioi_mem_nhds zero_lt_one ) fun x hx => Real.zero_rpow hx.out.ne' )
  simp only [HermitianMat.trace_rpow_eq_sum, ← Finset.sum_apply]
  convert! HasDerivAt.sum fun i _ => h_deriv i using 1

/-
PROBLEM
Trace cyclicity for conj: Tr[conj(σ^t, ρ)] = ⟪ρ, σ^{2t}⟫ = Tr[ρ σ^{2t}].
    Since σ^t is Hermitian: Tr[σ^t ρ σ^t] = Tr[ρ (σ^t)²] = Tr[ρ σ^{2t}].
PROVIDED SOLUTION
By definition, (ρ.M.conj (σ.M ^ t).mat).mat = (σ.M ^ t).mat * ρ.M.mat * ((σ.M ^ t).mat)^* (from conj_apply_mat). Since σ.M ^ t is Hermitian, ((σ.M ^ t).mat)^* = (σ.M ^ t).mat (from σ.M ^ t property .H). So the trace is Tr[(σ^t).mat * ρ.mat * (σ^t).mat].
By Matrix.trace_mul_comm applied to the product ((σ^t).mat * ρ.mat) and (σ^t).mat:
Tr[(σ^t).mat * ρ.mat * (σ^t).mat] = Tr[(σ^t).mat * (σ^t).mat * ρ.mat].
Now use mat_rpow_add with σ.nonneg and t + t = 2t (≠ 0 since t ≠ 0): (σ.M ^ (t+t)).mat = (σ.M ^ t).mat * (σ.M ^ t).mat. So the trace becomes Tr[(σ.M ^ (2*t)).mat * ρ.mat].
By inner_eq_trace_rc: ⟪ρ.M, σ.M ^ (2*t)⟫ = (ρ.M.mat * (σ.M ^ (2*t)).mat).trace.
By Matrix.trace_mul_comm: Tr[ρ.mat * (σ^{2t}).mat] = Tr[(σ^{2t}).mat * ρ.mat].
Combine: the conj trace = Tr[(σ^{2t}).mat * ρ.mat] = Tr[ρ.mat * (σ^{2t}).mat] = ⟪ρ, σ^{2t}⟫.
Note: show t + t = 2 * t by ring, and 2 * t ≠ 0 from ht using two_mul_ne_zero or similar.
-/
private lemma trace_conj_eq_inner_rpow {ρ σ : MState d} {t : ℝ} (ht : t ≠ 0) :
    (ρ.M.conj (σ.M ^ t).mat).trace = ⟪ρ.M, σ.M ^ (2 * t)⟫ := by
  have h_cyclic : ((σ.M ^ t).mat * ρ.M.mat * (σ.M ^ t).mat).trace = ((σ.M ^ (2 * t)).mat * ρ.M.mat).trace := by
    -- Since σ.M ^ t is Hermitian, we can use the property that the trace of a product is invariant under cyclic permutations.
    have h_cyclic : Matrix.trace ((σ.M ^ t).mat * ρ.M.mat * (σ.M ^ t).mat) = Matrix.trace ((σ.M ^ t).mat * (σ.M ^ t).mat * ρ.M.mat) := by
      rw [ ← Matrix.trace_mul_comm ]
      simp [ Matrix.mul_assoc ]
    rw [ h_cyclic, two_mul ]
    ring_nf
    have h_exp : (σ.M ^ (t + t)).mat = (σ.M ^ t).mat * (σ.M ^ t).mat := by
      have h_nonneg : 0 ≤ σ.M := by
        exact σ.nonneg
      have h_ne_zero : t + t ≠ 0 := by
        exact fun h => ht ( by linarith )
      exact HermitianMat.mat_rpow_add h_nonneg h_ne_zero
    rw [ mul_two, h_exp ]
  have h_inner : ⟪ρ.M, σ.M ^ (2 * t)⟫ = ((ρ.M.mat * (σ.M ^ (2 * t)).mat).trace).re := by
    exact rfl
  simp_all
  convert congr_arg Complex.re h_cyclic using 1 ; simp [ HermitianMat.conj ] ; ring!;
  rw [ Matrix.trace_mul_comm ]

-- The weight of eigenvalue i in the inner product decomposition
private def eigenWeight (ρ σ : MState d) (i : d) : ℝ :=
  RCLike.re ((Matrix.vecMul (star (σ.M.H.eigenvectorBasis i : d → ℂ)) ρ.M.mat) ⬝ᵥ (σ.M.H.eigenvectorBasis i : d → ℂ))

private lemma inner_cfc_eq_sum_eigenWeight (ρ σ : MState d) (f : ℝ → ℝ) :
    ⟪ρ.M, σ.M.cfc f⟫ = ∑ i, f (σ.M.H.eigenvalues i) * eigenWeight ρ σ i := by
  -- By definition of the inner product in the context of Hermitian matrices, we can expand it using the trace.
  have h_inner : ⟪ρ.M, σ.M.cfc f⟫ = RCLike.re (Matrix.trace (ρ.M.mat * (σ.M.cfc f).mat)) := by
    exact rfl;
  have h_trace : Matrix.trace (ρ.M.mat * (σ.M.cfc f).mat) = ∑ i, f (σ.M.H.eigenvalues i) * (star (σ.M.H.eigenvectorBasis i) ⬝ᵥ ρ.M.mat.mulVec (σ.M.H.eigenvectorBasis i)) := by
    rw [ Matrix.trace ];
    have h_cfc_def : (σ.M.cfc f).mat = ∑ i, (f (Matrix.IsHermitian.eigenvalues σ.M.H i)) • Matrix.of (fun x y => (σ.M.H.eigenvectorBasis i x) * (star (σ.M.H.eigenvectorBasis i y))) := by
      convert σ.M.cfc_toMat_eq_sum_smul_proj f using 1;
      ext i j; simp [ Matrix.single ] ; ring_nf
      simp [ Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply ];
      refine' Finset.sum_congr rfl fun x _ => _ ; simp [ Finset.sum_ite, Finset.filter_eq, Finset.filter_and ] ; ring_nf
      rw [ Finset.sum_eq_single x ] <;> aesop;
    simp [ h_cfc_def, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm ];
    simp [ Matrix.sum_apply, Matrix.mul_apply ];
    rw [ Finset.sum_comm ] ; congr ; ext ; congr ; ext ; congr ; ext ; ring!;
  simp_all [ eigenWeight ];
  simp [ Matrix.dotProduct_mulVec ]

private lemma eigenWeight_nonneg (ρ σ : MState d) (i : d) : 0 ≤ eigenWeight ρ σ i := by
  -- By definition of `eigenWeight`, we have:
  set v := σ.M.H.eigenvectorBasis i
  set w := ρ.M.mat.mulVec v
  have h_eigenWeight : eigenWeight ρ σ i = RCLike.re (star v ⬝ᵥ w) := by
    unfold eigenWeight;
    simp +zetaDelta at *;
    simp [ Matrix.dotProduct_mulVec ]
  rw [h_eigenWeight];
  -- Since ρ is positive semi-definite, we have that the inner product of any vector with ρ is non-negative. Hence, we can write:
  have := ρ.pos
  obtain ⟨ h₁, h₂ ⟩ := this;
  open ComplexOrder in
  have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h₁).2 v;
  exact this.1.trans (by simp [w])

private lemma eigenWeight_zero_of_eigenvalue_zero {i : d} (hσ : σ.M.ker ≤ ρ.M.ker)
  (hei : σ.M.H.eigenvalues i = 0) :
    eigenWeight ρ σ i = 0 := by
  unfold eigenWeight
  have h_mulVec_zero : σ.M.mat.mulVec (σ.M.H.eigenvectorBasis i) = 0 := by
    convert Matrix.IsHermitian.mulVec_eigenvectorBasis σ.M.H i using 1
    simp [hei]
  have h_mulVec_zero' : ρ.M.mat.mulVec (σ.M.H.eigenvectorBasis i) = 0 := by
    specialize hσ congr(WithLp.toLp 2 $h_mulVec_zero)
    exact congr(WithLp.ofLp $hσ)
  convert congr_arg ( fun x : d → ℂ => RCLike.re ( star ( σ.M.H.eigenvectorBasis i ) ⬝ᵥ x ) ) h_mulVec_zero' using 1;
  · simp [Matrix.dotProduct_mulVec]
  · simp [dotProduct]

/-
The derivative of u ↦ ⟪ρ, σ^u⟫ at u = 0 is ⟪ρ, σ.log⟫.
    Use inner_cfc_eq_sum_eigenWeight to write ⟪ρ, σ^u⟫ = ∑ i, q_i^u * eigenWeight ρ σ i,
    differentiate term by term using HasDerivAt.sum.
-/
private lemma hasDerivAt_inner_rpow_at_zero (h : σ.M.ker ≤ ρ.M.ker) :
    HasDerivAt (fun u : ℝ => ⟪ρ.M, σ.M ^ u⟫) ⟪ρ.M, σ.M.log⟫ 0 := by
  convert HasDerivAt.congr_of_eventuallyEq ?_ ?_;
  exact fun u => ∑ i, ( σ.M.H.eigenvalues i ) ^ u * eigenWeight ρ σ i;
  · have h_deriv : ∀ i, HasDerivAt (fun u : ℝ => (σ.M.H.eigenvalues i) ^ u * eigenWeight ρ σ i) (Real.log (σ.M.H.eigenvalues i) * eigenWeight ρ σ i) 0 := by
      intro i
      rcases (σ.eigenvalue_nonneg i).lt_or_eq' with h_pos | h_zero
      · simp only [h_pos, Real.rpow_def_of_pos, mul_comm]
        convert! ((hasDerivAt_id 0).mul (hasDerivAt_const _ _)).exp.const_mul (eigenWeight ρ σ i ) using 1
        simp
      · simp [Real.rpow_def_of_nonpos, mul_comm, h_zero]
        convert! hasDerivAt_const (0 : ℝ) (0 : ℝ) using 1
        ext1 u
        split_ifs with hu
        · simp [eigenWeight_zero_of_eigenvalue_zero h h_zero]
        · rfl
    convert HasDerivAt.sum (u := Finset.univ) fun i _ => h_deriv i using 1
    · ext x : 1
      simp only [Finset.sum_apply]
    · exact inner_cfc_eq_sum_eigenWeight ρ σ Real.log
  · filter_upwards [Metric.ball_mem_nhds 0 zero_lt_one] with u hu
    exact inner_cfc_eq_sum_eigenWeight ρ σ (· ^ u)

/-  The derivative of α ↦ Tr[ρ σ^((1-α)/α)] at α = 1 is -⟪ρ, log σ⟫.
    Uses trace cyclic: Tr[σ^t ρ σ^t] = Tr[ρ σ^(2t)].
    With 2t(α) = (1-α)/α, d/dα (2t) = -1/α², and d/dε σ^ε|_{ε=0} = log σ. -/
private lemma hasDerivAt_trace_conj_at_one {ρ σ : MState d}
    (h : σ.M.ker ≤ ρ.M.ker) :
    HasDerivAt
      (fun α : ℝ => ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat)).trace)
      (-⟪ρ.M, σ.M.log⟫)
      1 := by
  have h_chain : HasDerivAt (fun α : ℝ => ⟪ρ.M, σ.M ^ ((1 - α) / α)⟫) (⟪ρ.M, σ.M.log⟫ * (-1)) 1 := by
    apply HasDerivAt.comp (h₂ := fun u => ⟪ρ.M, σ.M ^ u⟫) (h := fun α => (1 - α) / α)
    · simpa using hasDerivAt_inner_rpow_at_zero h
    · have h1 := HasDerivAt.div ( hasDerivAt_id ( 1 : ℝ ) |> HasDerivAt.const_sub 1 )
        ( hasDerivAt_id ( 1 : ℝ ) ) ( by norm_num )
      simp_all only [id_eq, mul_one, sub_self, sub_zero, one_pow, div_one]
      exact h1
  ring_nf at h_chain
  apply h_chain.congr_of_eventuallyEq _
  filter_upwards [ lt_mem_nhds zero_lt_one ] with α hα
  by_cases h : ( 1 - α ) / ( 2 * α ) = 0
  · simp [ne_of_gt, hα] at h
    obtain ⟨⟩ : α = 1 := by linarith
    simp [*]
  · simp only [trace_conj_eq_inner_rpow h]
    ring_nf

/-
For a differentiable function b with b(1) = c ≥ 0 and b(α) ≥ 0 near α = 1,
the function α ↦ b(α)^α - b(α) has derivative c * log c at α = 1.
-/
private lemma scalar_rpow_cross_term {b : ℝ → ℝ} {c : ℝ}
    (hb : HasDerivAt b (deriv b 1) 1) (hc : b 1 = c) (hc_pos : 0 < c) :
    HasDerivAt (fun α => b α ^ α - b α) (c * Real.log c) 1 := by
  subst c
  have := (hb.rpow (hasDerivAt_id 1) hc_pos).sub hb
  simp_all only [hasDerivAt_deriv_iff, id_eq, mul_one, sub_self, Real.rpow_zero, Real.rpow_one,
    one_mul, add_sub_cancel_left]
  exact this

/-- For a PSD matrix A, Tr[A^s] - Tr[A] has derivative ⟪A, log A⟫ at s = 1.
    This generalizes `hasDerivAt_trace_rpow_at_one` to give the derivative of the
    difference Tr[A^s] - Tr[A], which equals ⟪A, log A⟫ since d/ds Tr[A] = 0. -/
private lemma hasDerivAt_trace_rpow_sub_trace (A : HermitianMat d ℂ) (hA : 0 ≤ A) :
    HasDerivAt (fun s : ℝ => (A ^ s).trace - A.trace) ⟪A, A.log⟫ 1 := by
  simpa using hasDerivAt_trace_rpow_at_one A hA

-- Abbreviation for the "B(α)" matrix appearing in the sandwiched trace.
private abbrev B_of (ρ σ : MState d) (α : ℝ) : HermitianMat d ℂ :=
  ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat

-- At α = 1, B(α) = ρ.M since (1-1)/(2·1) = 0 and conj by 1 is identity.
private lemma B_of_one (ρ σ : MState d) : B_of ρ σ 1 = ρ.M := by
  simp [B_of, HermitianMat.rpow_zero, HermitianMat.conj_one]

-- B(α) is nonneg for α > 0, because it's a conj of a nonneg matrix.
private lemma B_of_nonneg (ρ σ : MState d) (α : ℝ) : 0 ≤ B_of ρ σ α := by
  exact HermitianMat.conj_nonneg _ ρ.nonneg

-- The function g(M) = Tr[M^s] - Tr[M] satisfies g(M) = 0 when s = 1.
private lemma trace_rpow_sub_trace_at_one (M : HermitianMat d ℂ) :
    (M ^ (1 : ℝ)).trace - M.trace = 0 := by
  simp [HermitianMat.rpow_one]

-- The cross term function value at α = 1 is zero.
private lemma cross_term_at_one (ρ σ : MState d) :
    ((B_of ρ σ 1) ^ (1 : ℝ)).trace - (B_of ρ σ 1).trace
    - (ρ.M ^ (1 : ℝ)).trace + 1 = 0 := by
  simp [B_of_one, HermitianMat.rpow_one, ρ.tr]

/-
Scalar rpow cross term with just continuity: for a continuous function b with
  b(1) = c > 0, b(α) > 0 near 1, the function α ↦ b(α)^α - b(α) has derivative
  c * log c at α = 1. The key insight is that ∂/∂x(x^α - x)|_{α=1} = 0,
  so the derivative of b doesn't matter.
-/
private lemma scalar_rpow_cross_term_of_continuous {b : ℝ → ℝ} {c : ℝ}
    (hb_cont : ContinuousAt b 1) (hc : b 1 = c) (hc_pos : 0 < c)
    (hb_pos : ∀ᶠ α in nhds 1, 0 < b α) :
    HasDerivAt (fun α => b α ^ α - b α) (c * Real.log c) 1 := by
  rw [ hasDerivAt_iff_tendsto_slope_zero ];
  -- Use the fact that $b(1 + t)^{1 + t} - b(1 + t)$ can be rewritten as $b(1 + t) \cdot (b(1 + t)^t - 1)$.
  suffices h_rewrite : Filter.Tendsto (fun t => t⁻¹ * (b (1 + t) * (b (1 + t) ^ t - 1))) (nhdsWithin 0 {0}ᶜ) (nhds (c * Real.log c)) by
    refine' h_rewrite.congr' _;
    rw [ Filter.EventuallyEq, eventually_nhdsWithin_iff ];
    rw [ Metric.eventually_nhds_iff ] at *;
    obtain ⟨ ε, ε_pos, hε ⟩ := hb_pos; use ε, ε_pos; intros y hy hy'; rw [ Real.rpow_add ( hε ( show Dist.dist ( 1 + y ) 1 < ε from by simpa using hy ) ), Real.rpow_one ]
    ring_nf
    norm_num [ hc ]
  -- Use the fact that $b(1 + t) \to c$ as $t \to 0$.
  have h_b : Filter.Tendsto (fun t => b (1 + t)) (nhdsWithin 0 {0}ᶜ) (nhds c) := by
    exact hc ▸ hb_cont.tendsto.comp ( tendsto_nhdsWithin_of_tendsto_nhds ( by norm_num [ Filter.Tendsto ] ) );
  -- Use the fact that $b(1 + t)^t - 1 \sim t \log(b(1 + t))$ as $t \to 0$.
  have h_exp : Filter.Tendsto (fun t => t⁻¹ * (b (1 + t) ^ t - 1)) (nhdsWithin 0 {0}ᶜ) (nhds (Real.log c)) := by
    have h_exp : Filter.Tendsto (fun t => (b (1 + t) ^ t - 1) / t) (nhdsWithin 0 {0}ᶜ) (nhds (Real.log c)) := by
      have h_log : Filter.Tendsto (fun t => (Real.log (b (1 + t)) * t) / t) (nhdsWithin 0 {0}ᶜ) (nhds (Real.log c)) := by
        exact Filter.Tendsto.congr' ( by filter_upwards [ self_mem_nhdsWithin ] with t ht using by rw [ mul_div_cancel_right₀ _ ht ] ) ( Filter.Tendsto.log h_b hc_pos.ne' )
      have h_exp : Filter.Tendsto (fun t => (Real.exp (Real.log (b (1 + t)) * t) - 1) / t) (nhdsWithin 0 {0}ᶜ) (nhds (Real.log c)) := by
        have h_exp : HasDerivAt (fun t => Real.exp (Real.log (b (1 + t)) * t)) (Real.log c) 0 := by
          have h_log : HasDerivAt (fun t => Real.log (b (1 + t)) * t) (Real.log c) 0 := by
            rw [ hasDerivAt_iff_tendsto_slope_zero ];
            simpa [ div_eq_inv_mul ] using h_log
          convert h_log.exp using 1 ; norm_num [ hc ];
        simpa [ div_eq_inv_mul ] using h_exp.tendsto_slope_zero;
      refine' h_exp.congr' _;
      filter_upwards [ h_b.eventually ( lt_mem_nhds hc_pos ) ] with t ht using by rw [ Real.rpow_def_of_pos ht, mul_comm ] ;
    simpa only [ div_eq_inv_mul ] using h_exp;
  convert h_b.mul h_exp using 2 ; ring

/-
Scalar rpow cross term for the zero case: for continuous b with b(1) = 0,
  0 ≤ b(α) near 1, the function α ↦ b(α)^α - b(α) has derivative 0 at α = 1.
  Uses the convention 0 * log 0 = 0.
-/
private lemma scalar_rpow_cross_term_of_continuous_zero {b : ℝ → ℝ}
    (hb_cont : ContinuousAt b 1) (hc : b 1 = 0)
    (hb_nonneg : ∀ᶠ α in nhds 1, 0 ≤ b α) :
    HasDerivAt (fun α => b α ^ α - b α) 0 1 := by
  -- Let's choose any $\epsilon > 0$.
  have h_eps : ∀ ε > 0, ∃ δ > 0, ∀ α, abs (α - 1) < δ → abs (b α ^ α - b α) ≤ ε * abs (α - 1) := by
    -- Use the fact that $|b(α)^α - b(α)| ≤ |h| · sqrt(b(α)) · |log b(α)|$ for $0 < b(α) ≤ 1$ and $|h| ≤ 1/2$.
    have h_bound : ∀ᶠ α in nhds 1, |b α ^ α - b α| ≤ |α - 1| * Real.sqrt (|b α|) * |Real.log (|b α|)| := by
      have h_bound : ∀ᶠ α in nhds 1, 0 ≤ b α ∧ b α ≤ 1 ∧ |α - 1| ≤ 1 / 2 → |b α ^ α - b α| ≤ |α - 1| * Real.sqrt (b α) * |Real.log (b α)| := by
        filter_upwards [ hb_nonneg ] with α hα₁ hα₂ ; rcases eq_or_lt_of_le hα₂.1 with hα₃ | hα₃ <;> simp_all [ Real.rpow_def_of_nonneg ] ; ring_nf ;
        · norm_num [ ← hα₃ ] at *;
          linarith [ abs_le.mp hα₂ ];
        · split_ifs <;> simp_all [ne_of_gt]
          -- Use the fact that $|e^{x} - 1| \leq |x| e^{|x|}$ for any $x$.
          have h_exp_bound : ∀ x : ℝ, |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
            intro x; rw [ abs_le ] ; constructor <;> cases abs_cases x <;> simp [ * ] <;> nlinarith [ Real.exp_pos x, Real.exp_neg x, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos x ) ), Real.add_one_le_exp x, Real.add_one_le_exp ( -x ), Real.exp_le_exp.2 ( by linarith : x ≤ |x| ), Real.exp_le_exp.2 ( by linarith : -x ≤ |x| ) ] ;
          -- Apply the exponential bound to $x = \log(b(\alpha)) \cdot (\alpha - 1)$.
          have h_exp_bound_applied : |Real.exp (Real.log (b α) * (α - 1)) - 1| ≤ |Real.log (b α)| * |α - 1| * Real.exp (|Real.log (b α)| * |α - 1|) := by
            simpa only [ abs_mul, mul_assoc ] using h_exp_bound ( Real.log ( b α ) * ( α - 1 ) ) |> le_trans <| by simp [ abs_mul, mul_assoc ] ;
          -- Use the fact that $|b(\alpha)| \leq \sqrt{b(\alpha)}$ for $0 < b(\alpha) \leq 1$.
          have h_sqrt_bound : |b α| * Real.exp (|Real.log (b α)| * |α - 1|) ≤ Real.sqrt (b α) := by
            rw [ abs_of_nonneg hα₂.1 ] ; rw [ Real.sqrt_eq_rpow ] ; rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_rpow ( by positivity ) ] ; ring_nf ; norm_num [ hα₂.1, hα₂.2.1, hα₂.2.2 ] ;
            cases abs_cases ( Real.log ( b α ) ) <;> cases abs_cases ( -1 + α ) <;> nlinarith [ Real.log_le_sub_one_of_pos hα₃, abs_le.mp hα₂.2.2 ] ;
          rw [ show Real.exp ( Real.log ( b α ) * α ) = Real.exp ( Real.log ( b α ) * ( α - 1 ) ) * Real.exp ( Real.log ( b α ) ) by rw [ ← Real.exp_add ] ; ring_nf, Real.exp_log hα₃ ];
          field_simp;
          rw [ abs_mul ] ; nlinarith [ abs_nonneg ( Real.log ( b α ) ), abs_nonneg ( α - 1 ), abs_nonneg ( b α ), Real.sqrt_nonneg ( b α ), mul_le_mul_of_nonneg_left h_sqrt_bound ( abs_nonneg ( Real.log ( b α ) ) ), mul_le_mul_of_nonneg_left h_sqrt_bound ( abs_nonneg ( α - 1 ) ), mul_le_mul_of_nonneg_left h_sqrt_bound ( abs_nonneg ( b α ) ) ] ;
      have h_bound : ∀ᶠ α in nhds 1, 0 ≤ b α ∧ b α ≤ 1 ∧ |α - 1| ≤ 1 / 2 := by
        have h_bound : ∀ᶠ α in nhds 1, 0 ≤ b α ∧ b α ≤ 1 := by
          filter_upwards [ hb_nonneg, hb_cont.eventually ( Metric.ball_mem_nhds _ zero_lt_one ) ] with α hα₁ hα₂ using ⟨ hα₁, by linarith [ abs_lt.mp hα₂ ] ⟩;
        filter_upwards [ h_bound, Metric.ball_mem_nhds 1 ( show ( 0 : ℝ ) < 1 / 2 by norm_num ) ] with α hα₁ hα₂ using ⟨ hα₁.1, hα₁.2, by exact hα₂.out.le ⟩;
      filter_upwards [ h_bound, ‹∀ᶠ α in nhds 1, 0 ≤ b α ∧ b α ≤ 1 ∧ |α - 1| ≤ 1 / 2 → |b α ^ α - b α| ≤ |α - 1| * Real.sqrt ( b α ) * |Real.log ( b α )|› ] with α hα₁ hα₂ using by simpa [ abs_of_nonneg hα₁.1 ] using hα₂ hα₁;
    -- Use the fact that $\sqrt{|b(α)|} \cdot |\log(|b(α)|)| \to 0$ as $b(α) \to 0$.
    have h_sqrt_log : Filter.Tendsto (fun α => Real.sqrt (|b α|) * |Real.log (|b α|)|) (nhds 1) (nhds 0) := by
      have h_sqrt_log : Filter.Tendsto (fun x => Real.sqrt x * |Real.log x|) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have h_sqrt_log : Filter.Tendsto (fun x => Real.sqrt x * Real.log x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
          -- Let $y = \sqrt{x}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(y^2) = \lim_{y \to 0^+} 2y \log(y)$.
          suffices h_log_y : Filter.Tendsto (fun y => 2 * y * Real.log y) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) by
            have h_subst : Filter.Tendsto (fun x => 2 * Real.sqrt x * Real.log (Real.sqrt x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
              exact h_log_y.comp <| Filter.Tendsto.inf ( Real.continuous_sqrt.tendsto' _ _ <| by norm_num ) <| Filter.tendsto_principal_principal.mpr fun x hx => Real.sqrt_pos.mpr hx;
            generalize_proofs at *; (
            exact h_subst.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ Real.log_sqrt hx.out.le ] ; ring ) |> fun h => h.trans ( by norm_num ) ;);
          exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [ mul_assoc ] using Filter.Tendsto.const_mul 2 ( Real.continuous_mul_log.tendsto 0 ) ) |> fun h => h.trans ( by norm_num ) ;
        exact tendsto_zero_iff_norm_tendsto_zero.mpr ( by simpa using h_sqrt_log.norm );
      have h_sqrt_log : Filter.Tendsto (fun α => Real.sqrt (|b α|) * |Real.log (|b α|)|) (nhdsWithin 1 {α | 0 < |b α|}) (nhds 0) := by
        refine' h_sqrt_log.comp _;
        rw [ tendsto_nhdsWithin_iff ];
        exact ⟨ tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [ hc ] using hb_cont.abs.tendsto ), Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => hx ⟩;
      rw [ Metric.tendsto_nhdsWithin_nhds ] at h_sqrt_log;
      exact Metric.tendsto_nhds_nhds.mpr fun ε hε => by rcases h_sqrt_log ε hε with ⟨ δ, hδ, H ⟩ ; exact ⟨ δ, hδ, by intro x hx; by_cases hx' : 0 < |b x| <;> aesop ⟩ ;
    intro ε hε_pos
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ α, abs (α - 1) < δ₁ → Real.sqrt (|b α|) * |Real.log (|b α|)| < ε := by
      simpa using Metric.tendsto_nhds_nhds.mp h_sqrt_log ε hε_pos |> fun ⟨ δ₁, hδ₁₁, hδ₁₂ ⟩ => ⟨ δ₁, hδ₁₁, fun α hα => lt_of_abs_lt <| by simpa using hδ₁₂ hα ⟩;
    obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, ∀ α, abs (α - 1) < δ₂ → |b α ^ α - b α| ≤ |α - 1| * Real.sqrt (|b α|) * |Real.log (|b α|)| := by
      exact Metric.mem_nhds_iff.mp h_bound |> fun ⟨ δ₂, hδ₂_pos, hδ₂ ⟩ => ⟨ δ₂, hδ₂_pos, fun α hα => hδ₂ hα ⟩;
    exact ⟨ Min.min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun α hα => le_trans ( hδ₂ α ( lt_of_lt_of_le hα ( min_le_right _ _ ) ) ) ( by nlinarith [ hδ₁ α ( lt_of_lt_of_le hα ( min_le_left _ _ ) ), abs_nonneg ( α - 1 ) ] ) ⟩;
  rw [ hasDerivAt_iff_isLittleO_nhds_zero ];
  rw [ Asymptotics.isLittleO_iff ];
  intro ε hε; rcases h_eps ε hε with ⟨ δ, hδ, H ⟩ ; filter_upwards [ Metric.ball_mem_nhds _ hδ ] with x hx using by simpa [ hc ] using H ( 1 + x ) ( by simpa using hx ) ;

/-- If ker A ≤ ker ρM, then conjugating ρM by the support projection of A gives back ρM.
    This is because ρM is supported entirely on the support (= range) of A. -/
private lemma conj_supportProj_eq_of_ker_le (A ρM : HermitianMat d ℂ) (hker : A.ker ≤ ρM.ker) :
    ρM.conj (A.supportProj).mat = ρM := by
  have h_conj_support : ρM.mat * A.supportProj.mat = ρM.mat := by
    apply HermitianMat.mul_supportProj_of_ker_le; assumption;
  -- Using the conjugate transpose property and the fact that A.supportProj is Hermitian, we can simplify the expression.
  have h_conj_support : (A.supportProj.mat).conjTranspose * ρM.mat * A.supportProj.mat = ρM.mat := by
    rw [ ← Matrix.conjTranspose_inj ] at * ; aesop;
  simp_all [ HermitianMat.conj, Matrix.mul_assoc ]

/-- For a PSD matrix A, the function r ↦ A ^ r converges to A.supportProj
    as r → 0 through nonzero values. On positive eigenvalues λ, λ^r → 1.
    On zero eigenvalues, 0^r = 0 for r ≠ 0. So the limit is the support
    projection (indicator of nonzero eigenvalues). -/
private lemma rpow_tendsto_supportProj
    (A : HermitianMat d ℂ)  :
    Filter.Tendsto (fun r : ℝ => A ^ r) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds A.supportProj) := by
  -- By definition of $g$, we know that $A.cfc (g r)$ converges to $A.supportProj$ as $r$ approaches $0$.
  have h_cfc_g_conv : Filter.Tendsto (fun r : ℝ => A.cfc (fun x : ℝ => if r = 0 then (if x = 0 then 0 else 1) else x ^ r)) (nhds 0) (nhds A.supportProj) := by
    have h_cfc_g_conv : Continuous (fun r : ℝ => A.cfc (fun x : ℝ => if r = 0 then (if x = 0 then 0 else 1) else x ^ r)) := by
      -- Apply the continuity of the cfc function.
      have h_cfc_cont : Continuous (fun r : ℝ => A.cfc (fun x : ℝ => if r = 0 then (if x = 0 then 0 else 1) else x ^ r)) := by
        have h_g_cont : ∀ x : ℝ, Continuous (fun r : ℝ => if r = 0 then (if x = 0 then 0 else 1) else x ^ r) := by
          intro x
          by_cases hx : x = 0 <;> simp [hx];
          · rw [ Metric.continuous_iff ] ; aesop;
          · rw [ show ( fun r : ℝ => if r = 0 then 1 else x ^ r ) = fun r : ℝ => x ^ r by ext r; by_cases hr : r = 0 <;> simp [ hr ] ] ; exact Continuous.rpow continuous_const continuous_id' <| by continuity;
        apply_rules [ HermitianMat.continuous_cfc_fun ];
      convert h_cfc_cont using 1;
    convert h_cfc_g_conv.tendsto 0 using 2 ; simp [ HermitianMat.supportProj_eq_cfc ];
  exact Filter.Tendsto.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by aesop ) ( h_cfc_g_conv.mono_left inf_le_left )

/-- For PSD matrices A, ρ with A.ker ≤ ρ.ker, the function r ↦ ρ.conj (A ^ r).mat
    is continuous at r = 0. Even though A ^ r is discontinuous at r = 0 when A
    has zero eigenvalues, the kernel condition ensures the conj "kills" the
    discontinuity. -/
private lemma conj_rpow_continuousAt_zero
    (A ρM : HermitianMat d ℂ)
    (hker : A.ker ≤ ρM.ker) :
    ContinuousAt (fun r : ℝ => ρM.conj (A ^ r).mat) 0 := by
  have h_conj : Filter.Tendsto (fun r : ℝ => A ^ r) (nhdsWithin 0 {0}ᶜ) (nhds A.supportProj) := by
    convert rpow_tendsto_supportProj A using 1;
  have h_conj : Filter.Tendsto (fun r : ℝ => (HermitianMat.conj (A ^ r).mat) ρM) (nhdsWithin 0 {0}ᶜ) (nhds ρM) := by
    convert! Filter.Tendsto.comp ( show Filter.Tendsto ( fun M : { M : Matrix d d ℂ // M.IsHermitian } ↦ ( HermitianMat.conj M.val ) ρM ) ( nhds ( A.supportProj ) ) ( nhds ρM ) from ?_ ) h_conj using 2;
    convert Continuous.tendsto _ _;
    · convert! conj_supportProj_eq_of_ker_le A ρM hker |> Eq.symm;
    · fun_prop;
  rw [ Metric.tendsto_nhdsWithin_nhds ] at *;
  exact Metric.tendsto_nhds_nhds.mpr fun ε hε => by rcases h_conj ε hε with ⟨ δ, hδ, H ⟩ ; exact ⟨ δ, hδ, by intro x hx; by_cases hx' : x = 0 <;> aesop ⟩ ;

/-
ContinuousAt for B_of: the function α ↦ B(α) is continuous at α = 1.
  This requires the kernel condition because σ.M ^ r is discontinuous at r = 0
  on the kernel of σ. The kernel condition ensures the discontinuity is
  "killed" by ρ vanishing on σ's kernel.
-/
private lemma B_of_continuousAt (ρ σ : MState d) (h : σ.M.ker ≤ ρ.M.ker) :
    ContinuousAt (B_of ρ σ) 1 := by
  -- Use the fact that the composition of continuous functions is continuous.
  have h_cont : ContinuousAt (fun α : ℝ => ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) 1 := by
    have h_inner : ContinuousAt (fun r : ℝ => ρ.M.conj (σ.M ^ r).mat) 0 := by
      -- Apply the hypothesis `h_cont` directly to conclude the proof.
      exact conj_rpow_continuousAt_zero σ.M ρ.M h
    have h_exp : ContinuousAt (fun α : ℝ => (1 - α) / (2 * α)) 1 := by
      exact ContinuousAt.div ( continuousAt_const.sub continuousAt_id ) ( continuousAt_const.mul continuousAt_id ) ( by norm_num )
    exact ContinuousAt.comp ( by simpa using h_inner ) h_exp |> ContinuousAt.congr <| Filter.eventuallyEq_of_mem ( Ioi_mem_nhds zero_lt_one ) fun x hx ↦ by aesop;
  exact h_cont

private lemma trace_cfc_sub_le (A : HermitianMat d ℂ) (f g : ℝ → ℝ) :
    |(A.cfc f).trace - (A.cfc g).trace| ≤
      (Fintype.card d : ℝ) * (⨆ i, |f (A.H.eigenvalues i) - g (A.H.eigenvalues i)|) := by
  rw [HermitianMat.trace_cfc_eq, HermitianMat.trace_cfc_eq]
  convert! Finset.abs_sum_le_sum_abs _ Finset.univ |> le_trans <| Finset.sum_le_card_nsmul _ _ _ fun i _ => show |f ( A.H.eigenvalues i ) - g ( A.H.eigenvalues i )| ≤ ⨆ i, |f ( A.H.eigenvalues i ) - g ( A.H.eigenvalues i )| from le_ciSup ( Finite.bddAbove_range fun i => |f ( A.H.eigenvalues i ) - g ( A.H.eigenvalues i )| ) i using 1
  · simp [← Finset.sum_sub_distrib]
  · simp

/-- Eigenvalues of M(α) are uniformly bounded near α = 1. -/
private lemma eigenvalues_bounded_near {M : ℝ → HermitianMat d ℂ}
    (hM_nonneg : ∀ᶠ α in nhds 1, 0 ≤ M α)
    (hM_cont : ContinuousAt M 1) :
    ∃ K > 0, ∀ᶠ α in nhds 1, ∀ i, 0 ≤ (M α).H.eigenvalues i ∧ (M α).H.eigenvalues i ≤ K := by
  have h_op_norm_bound : ∃ K > 0, ∀ᶠ α in nhds 1, ‖M α‖ ≤ K := by
    exact ⟨ ‖M 1‖ + 1, by positivity, hM_cont.norm.eventually ( ge_mem_nhds ( lt_add_one _ ) ) ⟩
  have h_eigenvalue_bound : ∀ᶠ α in nhds 1, ∀ i, 0 ≤ (M α).H.eigenvalues i ∧ (M α).H.eigenvalues i ≤ ‖M α‖ := by
    have h_eigenvalue_bound : ∀ᶠ α in nhds 1, ∀ i, |(M α).H.eigenvalues i| ≤ ‖M α‖ := by
      filter_upwards [ hM_nonneg, h_op_norm_bound.choose_spec.2 ] with α hα₁ hα₂ i
      exact HermitianMat.eigenvalue_norm_le (M α) i
    filter_upwards [ h_eigenvalue_bound, hM_nonneg ] with α hα hα' i
    exact ⟨ hα' |> fun h => by simpa using h.eigenvalues_nonneg i, le_of_abs_le ( hα i ) ⟩
  exact ⟨ h_op_norm_bound.choose, h_op_norm_bound.choose_spec.1, h_eigenvalue_bound.and ( h_op_norm_bound.choose_spec.2 ) |> fun h => h.mono fun α hα i => ⟨ hα.1 i |>.1, hα.1 i |>.2.trans ( hα.2 ) ⟩ ⟩

/-
Uniform convergence of (x^{1+h} - x)/h to x * log x on [0, K] as h → 0.
This is the uniform version of the derivative of s ↦ x^s at s = 1.
-/
private lemma rpow_slope_tendsto_uniformly (K : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < |h| → |h| < δ →
    ∀ x ∈ Set.Icc 0 K, |(x ^ (1 + h) - x) / h - x * Real.log x| < ε := by
  intro ε ε_pos
  obtain ⟨δ₁, δ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ x ∈ Set.Icc 0 K, 0 < x → x < δ₁ → |x * Real.log x| < ε / 4 ∧ ∀ h, 0 < |h| → |h| < 1 / 2 → |(x ^ (1 + h) - x) / h| < ε / 4 := by
    obtain ⟨δ₁, δ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ x ∈ Set.Icc 0 K, 0 < x → x < δ₁ → |x * Real.log x| < ε / 4 := by
      have h_cont : Filter.Tendsto (fun x => x * Real.log x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.tendsto 0 );
      have := Metric.tendsto_nhdsWithin_nhds.mp h_cont ( ε / 4 ) ( by linarith );
      exact ⟨ this.choose, this.choose_spec.1, fun x hx₁ hx₂ hx₃ => by simpa [ abs_mul ] using this.choose_spec.2 hx₂ ( by simpa [ abs_of_pos hx₂ ] using hx₃ ) ⟩;
    have h_bound : ∃ δ₁ > 0, ∀ x ∈ Set.Icc 0 K, 0 < x → x < δ₁ → ∀ h, 0 < |h| → |h| < 1 / 2 → |x ^ (1 + h) - x| ≤ |h| * x * (|Real.log x| + 1) * Real.exp (|h| * (|Real.log x| + 1)) := by
      have h_bound : ∀ x ∈ Set.Icc 0 K, 0 < x → ∀ h : ℝ, 0 < |h| → |h| < 1 / 2 → |x ^ (1 + h) - x| ≤ |h| * x * (|Real.log x| + 1) * Real.exp (|h| * (|Real.log x| + 1)) := by
        intros x hx hx_pos h hh_pos hh_lt_half
        have h_exp_bound : |Real.exp (h * Real.log x) - 1| ≤ |h| * |Real.log x| * Real.exp (|h| * |Real.log x|) := by
          have h_exp_bound : ∀ y : ℝ, |Real.exp y - 1| ≤ |y| * Real.exp (|y|) := by
            intro y; rw [ abs_le ] ; constructor <;> cases abs_cases y <;> simp [ * ];
            · nlinarith [ Real.add_one_le_exp y ];
            · nlinarith [ Real.exp_pos y, Real.exp_neg y, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos y ) ), Real.add_one_le_exp y, Real.add_one_le_exp ( -y ) ];
            · nlinarith [ Real.exp_pos y, Real.exp_neg y, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos y ) ), Real.add_one_le_exp y, Real.add_one_le_exp ( -y ) ];
            · nlinarith [ Real.exp_pos y, Real.exp_neg y, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos y ) ), Real.add_one_le_exp y, Real.add_one_le_exp ( -y ) ];
          simpa only [ abs_mul ] using h_exp_bound ( h * Real.log x );
        rw [ Real.rpow_add hx_pos, Real.rpow_one ];
        rw [ Real.rpow_def_of_pos hx_pos ];
        rw [ show x * Real.exp ( Real.log x * h ) - x = x * ( Real.exp ( h * Real.log x ) - 1 ) by ring_nf ]
        rw [ abs_mul, abs_of_nonneg hx_pos.le ]
        refine' le_trans ( mul_le_mul_of_nonneg_left h_exp_bound hx_pos.le ) _
        ring_nf
        exact le_add_of_le_of_nonneg ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr ( by nlinarith [ abs_nonneg h, abs_nonneg ( Real.log x ) ] ) ) ( by positivity ) ) ( by positivity );
      exact ⟨ δ₁, δ₁_pos, fun x hx hx' hx'' h hh hh' => h_bound x hx hx' h hh hh' ⟩;
    obtain ⟨δ₂, δ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, ∀ x ∈ Set.Icc 0 K, 0 < x → x < δ₂ → x * (|Real.log x| + 1) * Real.exp (1 / 2 * (|Real.log x| + 1)) < ε / 4 := by
      have h_bound : Filter.Tendsto (fun x => x * (|Real.log x| + 1) * Real.exp (1 / 2 * (|Real.log x| + 1))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        -- Let $y = -\log x$, so we can rewrite the limit as $y \to \infty$.
        suffices h_log : Filter.Tendsto (fun y => Real.exp (-y) * (y + 1) * Real.exp ((y + 1) / 2)) Filter.atTop (nhds 0) by
          have h_subst : Filter.Tendsto (fun x => Real.exp (-(-Real.log x)) * ((-Real.log x) + 1) * Real.exp ((-Real.log x + 1) / 2)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
            exact h_log.comp ( Filter.tendsto_neg_atBot_atTop.comp ( Real.tendsto_log_nhdsNE_zero.mono_left <| nhdsWithin_mono _ <| by norm_num ) );
          refine' h_subst.congr' _;
          filter_upwards [ Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ] with x hx
          rw [ abs_of_nonpos ( Real.log_nonpos hx.1.le hx.2.le ) ]
          rw [ neg_neg, Real.exp_log hx.1 ]
          ring_nf
        -- We can factor out $e^{-y/2}$ and use the fact that $e^{-y/2} \to 0$ as $y \to \infty$.
        suffices h_factor : Filter.Tendsto (fun y => Real.exp (-y / 2) * (y + 1)) Filter.atTop (nhds 0) by
          convert h_factor.const_mul ( Real.exp ( 1 / 2 ) ) using 2 <;> ring_nf
          norm_num [ mul_assoc, ← Real.exp_add ] ; ring_nf
        -- Let $z = \frac{y}{2}$, so we can rewrite the limit as $z \to \infty$.
        suffices h_z : Filter.Tendsto (fun z => Real.exp (-z) * (2 * z + 1)) Filter.atTop (nhds 0) by
          convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 2⁻¹ : ℝ ) ) ) using 2 ; norm_num ; ring_nf
        have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
        convert this.const_mul 2 |> Filter.Tendsto.add <| Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot using 2 <;> norm_num
        ring;
      have := Metric.tendsto_nhdsWithin_nhds.mp h_bound ( ε / 4 ) ( by linarith );
      obtain ⟨ δ₂, δ₂_pos, H ⟩ := this; exact ⟨ δ₂, δ₂_pos, fun x hx₁ hx₂ hx₃ => by linarith [ abs_lt.mp ( H hx₂ ( by simpa [ abs_of_pos hx₂ ] using hx₃ ) ) ] ⟩ ;
    obtain ⟨δ₃, δ₃_pos, hδ₃⟩ : ∃ δ₃ > 0, ∀ x ∈ Set.Icc 0 K, 0 < x → x < δ₃ → ∀ h, 0 < |h| → |h| < 1 / 2 → |(x ^ (1 + h) - x) / h| ≤ x * (|Real.log x| + 1) * Real.exp (|h| * (|Real.log x| + 1)) := by
      obtain ⟨ δ₃, δ₃_pos, hδ₃ ⟩ := h_bound;
      exact ⟨ δ₃, δ₃_pos, fun x hx hx' hx'' h hh hh' => by rw [ abs_div, div_le_iff₀ ( by positivity ) ] ; convert! hδ₃ x hx hx' hx'' h hh hh' using 1 ; ring ⟩;
    refine' ⟨ Min.min δ₁ ( Min.min δ₂ δ₃ ), lt_min δ₁_pos ( lt_min δ₂_pos δ₃_pos ), fun x hx hx' hx'' => ⟨ hδ₁ x hx hx' ( lt_of_lt_of_le hx'' ( min_le_left _ _ ) ), fun h hh₁ hh₂ => lt_of_le_of_lt ( hδ₃ x hx hx' ( lt_of_lt_of_le hx'' ( min_le_right _ _ |> le_trans <| min_le_right _ _ ) ) h hh₁ hh₂ ) _ ⟩ ⟩;
    exact lt_of_le_of_lt ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| mul_le_mul_of_nonneg_right hh₂.le <| by positivity ) <| by positivity ) <| hδ₂ x hx hx' <| lt_of_lt_of_le hx'' <| min_le_right _ _ |> le_trans <| min_le_left _ _;
  obtain ⟨δ₂, δ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, ∀ x ∈ Set.Icc δ₁ K, ∀ h, 0 < |h| → |h| < δ₂ → |(x ^ (1 + h) - x) / h - x * Real.log x| < ε / 4 := by
    have h_mean_value : ∀ x ∈ Set.Icc δ₁ K, ∀ h, 0 < |h| → |h| < 1 / 2 → |(x ^ (1 + h) - x) / h - x * Real.log x| ≤ |h| * x * (Real.log x) ^ 2 * Real.exp (|h| * |Real.log x|) := by
      intros x hx h h_pos h_lt
      have h_mean_value : |(x ^ h - 1) / h - Real.log x| ≤ |h| * (Real.log x) ^ 2 * Real.exp (|h| * |Real.log x|) := by
        -- Applying the inequality |e^y - 1 - y| ≤ |y|^2 e^|y| with y = h * Real.log x.
        have h_exp_ineq : ∀ y : ℝ, |Real.exp y - 1 - y| ≤ |y|^2 * Real.exp |y| := by
          intro y; rw [ abs_le ] ; constructor <;> cases abs_cases y <;> simp [ * ];
          · nlinarith [ Real.add_one_le_exp y, Real.exp_pos y ];
          · nlinarith [ Real.add_one_le_exp y, Real.add_one_le_exp ( -y ), Real.exp_pos y, Real.exp_pos ( -y ) ];
          · -- Using the Taylor series expansion of $e^y$, we have $e^y \leq 1 + y + y^2 e^y$ for $y \geq 0$.
            have h_taylor : ∀ y : ℝ, 0 ≤ y → Real.exp y ≤ 1 + y + y^2 * Real.exp y := by
              intro y hy; nlinarith [ Real.exp_pos y, Real.exp_neg y, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos y ) ), Real.add_one_le_exp y, Real.add_one_le_exp ( -y ), mul_nonneg hy ( Real.exp_nonneg y ), mul_nonneg hy ( Real.exp_nonneg ( -y ) ) ] ;
            linarith [ h_taylor y ( by linarith ) ];
          · nlinarith [ Real.exp_pos y, Real.exp_neg y, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos y ) ), Real.add_one_le_exp y, Real.add_one_le_exp ( -y ) ];
        convert! mul_le_mul_of_nonneg_left ( h_exp_ineq ( h * Real.log x ) ) ( inv_nonneg.mpr h_pos.le ) using 1 <;> norm_num [ Real.rpow_def_of_pos ( show 0 < x from lt_of_lt_of_le δ₁_pos hx.1 ), mul_comm ] ; ring_nf
        · rw [ ← abs_inv, ← abs_mul ] ; ring_nf;
          by_cases hh : h = 0 <;> aesop;
        · simp [ sq, mul_assoc, mul_comm, mul_left_comm, h_pos.ne' ];
      convert! mul_le_mul_of_nonneg_left h_mean_value ( show 0 ≤ x by linarith [ hx.1 ] ) using 1 <;> ring_nf

      rw [ show x ^ (1 + h) * h⁻¹ - x * h⁻¹ - x * Real.log x = x * ( -h⁻¹ + ( h⁻¹ * x ^ h - Real.log x ) ) by rw [ Real.rpow_add ( by linarith [ hx.1 ] ), Real.rpow_one ] ; ring ]
      rw [ abs_mul, abs_of_nonneg ( by linarith [ hx.1 ] : 0 ≤ x ) ]
      ring_nf

    -- Choose δ₂ such that |h| * x * (Real.log x) ^ 2 * Real.exp (|h| * |Real.log x|) < ε / 4 for all x ∈ [δ₁, K] and |h| < δ₂.
    obtain ⟨δ₂, δ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, ∀ x ∈ Set.Icc δ₁ K, ∀ h, 0 < |h| → |h| < δ₂ → |h| * x * (Real.log x) ^ 2 * Real.exp (|h| * |Real.log x|) < ε / 4 := by
      -- Since $x * (\log x)^2 * \exp(|h| * |\log x|)$ is continuous on the compact interval $[\delta₁, K]$, it is bounded.
      obtain ⟨M, hM⟩ : ∃ M > 0, ∀ x ∈ Set.Icc δ₁ K, ∀ h, 0 < |h| → |h| < 1 / 2 → x * (Real.log x) ^ 2 * Real.exp (|h| * |Real.log x|) ≤ M := by
        have h_cont : ContinuousOn (fun x => x * (Real.log x) ^ 2 * Real.exp (1 / 2 * |Real.log x|)) (Set.Icc δ₁ K) := by
          exact ContinuousOn.mul ( ContinuousOn.mul continuousOn_id ( ContinuousOn.pow ( Real.continuousOn_log.mono ( by exact fun x hx => ne_of_gt <| lt_of_lt_of_le δ₁_pos hx.1 ) ) _ ) ) ( ContinuousOn.rexp <| ContinuousOn.mul continuousOn_const <| ContinuousOn.abs <| Real.continuousOn_log.mono ( by exact fun x hx => ne_of_gt <| lt_of_lt_of_le δ₁_pos hx.1 ) );
        obtain ⟨ M, hM ⟩ := IsCompact.exists_bound_of_continuousOn ( CompactIccSpace.isCompact_Icc ) h_cont;
        norm_num +zetaDelta at *;
        exact ⟨ Max.max M 1, by positivity, fun x hx₁ hx₂ h hh₁ hh₂ => le_trans ( by rw [ abs_of_nonneg ( by linarith : 0 ≤ x ) ] ; exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith [ abs_nonneg ( Real.log x ) ] ) <| by nlinarith [ abs_nonneg ( Real.log x ) ] ) <| le_trans ( hM x hx₁ hx₂ ) <| le_max_left _ _ ⟩;
      exact ⟨ Min.min ( 1 / 2 ) ( ε / 4 / M ), lt_min ( by norm_num ) ( div_pos ( by linarith ) hM.1 ), fun x hx h hh₁ hh₂ => by nlinarith [ min_le_left ( 1 / 2 ) ( ε / 4 / M ), min_le_right ( 1 / 2 ) ( ε / 4 / M ), mul_div_cancel₀ ( ε / 4 ) hM.1.ne', abs_nonneg h, hM.2 x hx h hh₁ ( lt_of_lt_of_le hh₂ ( min_le_left _ _ ) ), mul_le_mul_of_nonneg_left ( hM.2 x hx h hh₁ ( lt_of_lt_of_le hh₂ ( min_le_left _ _ ) ) ) ( abs_nonneg h ) ] ⟩;
    exact ⟨ Min.min δ₂ ( 1 / 2 ), lt_min δ₂_pos ( by norm_num ), fun x hx h hh₁ hh₂ => lt_of_le_of_lt ( h_mean_value x hx h hh₁ ( lt_of_lt_of_le hh₂ ( min_le_right _ _ ) ) ) ( hδ₂ x hx h hh₁ ( lt_of_lt_of_le hh₂ ( min_le_left _ _ ) ) ) ⟩;
  refine' ⟨ Min.min ( 1 / 2 ) δ₂, lt_min ( by positivity ) δ₂_pos, fun h hh₁ hh₂ x hx => _ ⟩ ; cases lt_or_ge x δ₁ <;> simp_all [ abs_lt ];
  · cases lt_or_eq_of_le hx.1 <;> simp_all [ abs_of_nonneg ];
    · constructor <;> cases abs_cases ( Real.log x ) <;> nlinarith [ hδ₁ x hx.1 hx.2 ‹_› ‹_›, hδ₁ x hx.1 hx.2 ‹_› ‹_› |>.2 h hh₁ hh₂.1.1 hh₂.1.2 ];
    · by_cases h : 1 + h = 0 <;> simp_all [ division_def ] ; linarith [ Real.log_le_sub_one_of_pos ( show 0 < ε by linarith ) ] ;
      norm_num [ ← ‹0 = x› ] at * ; aesop;
  · constructor <;> linarith [ hδ₂ x ‹_› hx.2 h hh₁ hh₂.2.1 hh₂.2.2 ]

/-
CFC trace continuity: if M → ρ.M and f is continuous on [0,∞),
then Tr[(M α).cfc(f)] → Tr[ρ.M.cfc(f)].
-/
private lemma trace_cfc_tendsto_of_tendsto (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ici 0))
    {M : ℝ → HermitianMat d ℂ}
    (hM_cont : ContinuousAt M 1) (hM_nonneg : ∀ᶠ α in nhds 1, 0 ≤ M α)
    (hM_one : M 1 = ρ.M) :
    Filter.Tendsto (fun α => ((M α).cfc f).trace) (nhds 1) (nhds ((ρ.M.cfc f).trace)) := by
  have h_cfc_cont : ContinuousWithinAt (fun A : HermitianMat d ℂ => A.cfc f) {A : HermitianMat d ℂ | 0 ≤ A} ρ := by
    have h_cont : ContinuousOn (fun A : HermitianMat d ℂ => A.cfc f) {A : HermitianMat d ℂ | 0 ≤ A} := by
      have h_cont_trace : ContinuousOn (fun A : HermitianMat d ℂ => (A.cfc f)) {A : HermitianMat d ℂ | 0 ≤ A} := by
        have h_cont_cfc : ContinuousOn (fun A : HermitianMat d ℂ => A.cfc f) {A : HermitianMat d ℂ | spectrum ℝ A.mat ⊆ Set.Ici 0} := by
          intro A hA
          exact HermitianMat.continuousWithinAt_cfc_of_continuousOn hf hA
        have h_spectrum_subset : ∀ A : HermitianMat d ℂ, 0 ≤ A → spectrum ℝ A.mat ⊆ Set.Ici 0 := by
          intro A hA
          exact (HermitianMat.posSemidef_iff_spectrum_Ici A).mp hA
        exact h_cont_cfc.mono fun A hA => h_spectrum_subset A hA
      exact h_cont_trace
    exact h_cont _ ρ.nonneg |> ContinuousWithinAt.mono <| Set.Subset.refl _;
  have h_trace_cont : Continuous (fun A : HermitianMat d ℂ => A.trace) := by
    exact HermitianMat.trace_Continuous;
  have h_comp_cont : Filter.Tendsto (fun α => (M α).cfc f) (nhds 1) (nhds ((ρ : HermitianMat d ℂ).cfc f)) := by
    convert! h_cfc_cont.tendsto.comp _ using 2;
    exact tendsto_nhdsWithin_iff.mpr ⟨ hM_cont.tendsto.trans ( by simp [ hM_one ] ), hM_nonneg ⟩;
  exact h_trace_cont.continuousAt.tendsto.comp h_comp_cont

/-
The remainder term r(1+h)/h → 0 where
`r(α) = Tr[M(α)^α] - Tr[M(α)] - Tr[ρ.M^α] + Tr[ρ.M]`
-/
private lemma cross_term_slope_tendsto_zero
    {M : ℝ → HermitianMat d ℂ}
    (hM_nonneg : ∀ᶠ α in nhds 1, 0 ≤ M α)
    (hM_cont : ContinuousAt M 1)
    (hM_one : M 1 = ρ.M) :
    Filter.Tendsto
      (fun h : ℝ => ((M (1 + h) ^ (1 + h)).trace - (M (1 + h)).trace
                    - (ρ.M ^ (1 + h)).trace + ρ.M.trace) / h)
      (nhdsWithin 0 {0}ᶜ)
      (nhds 0) := by
  obtain ⟨ K, hK_pos, hK ⟩ := eigenvalues_bounded_near hM_nonneg hM_cont;
  clear hK_pos
  -- Let $G_h(x) = \frac{x^{1+h} - x}{h}$ for $h \neq 0$ and $G_0(x) = x \log x$.
  set Gh : ℝ → ℝ → ℝ := fun h x => if h = 0 then x * Real.log x else (x ^ (1 + h) - x) / h;
  -- Using the triangle inequality decomposition with $G_0(x) = x \log x$, we get:
  have h_triangle : Filter.Tendsto (fun h => (∑ i, Gh h ((M (1 + h)).H.eigenvalues i)) - (∑ i, Gh h (ρ.M.H.eigenvalues i))) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    -- By the properties of the trace and the continuity of $G_h$, we can bound the difference.
    have h_bound : ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < |h| → |h| < δ → ∀ x ∈ Set.Icc 0 K, |Gh h x - x * Real.log x| < ε := by
      intro ε ε_pos
      obtain ⟨δ, δ_pos, hδ⟩ : ∃ δ > 0, ∀ h : ℝ, 0 < |h| → |h| < δ → ∀ x ∈ Set.Icc 0 K, |(x ^ (1 + h) - x) / h - x * Real.log x| < ε := by
        have := rpow_slope_tendsto_uniformly K ε ε_pos; aesop;
      use δ, δ_pos
      intro h hh_pos hh_lt
      aesop;
    -- Using the bound, we can show that the difference tends to zero.
    have h_diff_zero : Filter.Tendsto (fun h => ∑ i, (Gh h ((M (1 + h)).H.eigenvalues i) - (M (1 + h)).H.eigenvalues i * Real.log ((M (1 + h)).H.eigenvalues i))) (nhdsWithin 0 {0}ᶜ) (nhds 0) ∧ Filter.Tendsto (fun h => ∑ i, (Gh h (ρ.M.H.eigenvalues i) - ρ.M.H.eigenvalues i * Real.log (ρ.M.H.eigenvalues i))) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      constructor;
      · have h_diff_zero : ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < |h| → |h| < δ → ∀ i, |Gh h ((M (1 + h)).H.eigenvalues i) - (M (1 + h)).H.eigenvalues i * Real.log ((M (1 + h)).H.eigenvalues i)| < ε := by
          intro ε hε_pos
          obtain ⟨δ, hδ_pos, hδ⟩ := h_bound ε hε_pos
          obtain ⟨δ', hδ'_pos, hδ'⟩ : ∃ δ' > 0, ∀ h : ℝ, |h| < δ' → ∀ i, 0 ≤ (M (1 + h)).H.eigenvalues i ∧ (M (1 + h)).H.eigenvalues i ≤ K := by
            rcases Metric.mem_nhds_iff.mp hK with ⟨ δ', hδ'_pos, hδ' ⟩;
            exact ⟨ δ', hδ'_pos, fun h hh i => hδ' ( mem_ball_iff_norm.mpr <| by simpa using hh ) i ⟩;
          exact ⟨ Min.min δ δ', lt_min hδ_pos hδ'_pos, fun h hh₁ hh₂ i => hδ h hh₁ ( lt_of_lt_of_le hh₂ ( min_le_left _ _ ) ) _ ( hδ' h ( lt_of_lt_of_le hh₂ ( min_le_right _ _ ) ) i ) ⟩;
        rw [ Metric.tendsto_nhdsWithin_nhds ];
        intro ε hε_pos
        obtain ⟨δ, hδ_pos, hδ⟩ := h_diff_zero (ε / (Fintype.card d + 1)) (by
        positivity);
        refine' ⟨ δ, hδ_pos, fun x hx hx' => _ ⟩;
        simp +zetaDelta at *;
        rw [ if_neg hx ];
        rw [ ← Finset.sum_sub_distrib ];
        exact lt_of_le_of_lt ( Finset.abs_sum_le_sum_abs _ _ ) ( lt_of_le_of_lt ( Finset.sum_le_sum fun i _ => le_of_lt ( by simpa [ hx ] using hδ x hx hx' i ) ) ( by norm_num; nlinarith [ mul_div_cancel₀ ε ( by positivity : ( Fintype.card d + 1 : ℝ ) ≠ 0 ) ] ) );
      · rw [ Metric.tendsto_nhdsWithin_nhds ];
        intro ε ε_pos; rcases h_bound ( ε / ( Fintype.card d + 1 ) ) ( div_pos ε_pos ( Nat.cast_add_one_pos _ ) ) with ⟨ δ, δ_pos, H ⟩ ; use δ, δ_pos; intro x hx hx'; simp_all [ dist_eq_norm ] ;
        rw [ ← Finset.sum_sub_distrib ];
        refine' lt_of_le_of_lt ( Finset.abs_sum_le_sum_abs _ _ ) _;
        refine' lt_of_le_of_lt ( Finset.sum_le_sum fun i _ => le_of_lt ( H x hx hx' _ _ _ ) ) _;
        · have := hK i; have := this.1.self_of_nhds; aesop;
        · exact hK i |>.2.self_of_nhds |> fun h => by simpa [ hM_one ] using h;
        · simp [ div_eq_mul_inv ];
          nlinarith [ mul_inv_cancel_left₀ ( by positivity : ( Fintype.card d : ℝ ) + 1 ≠ 0 ) ε ];
    have h_diff_zero : Filter.Tendsto (fun h => ∑ i, ((M (1 + h)).H.eigenvalues i * Real.log ((M (1 + h)).H.eigenvalues i)) - ∑ i, (ρ.M.H.eigenvalues i * Real.log (ρ.M.H.eigenvalues i))) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      have h_diff_zero : Filter.Tendsto (fun h => ((M (1 + h)).cfc (fun x => x * Real.log x)).trace - (ρ.M.cfc (fun x => x * Real.log x)).trace) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
        have h_diff_zero : Filter.Tendsto (fun h => ((M (1 + h)).cfc (fun x => x * Real.log x)).trace) (nhdsWithin 0 {0}ᶜ) (nhds ((ρ.M.cfc (fun x => x * Real.log x)).trace)) := by
          have h_diff_zero : Filter.Tendsto (fun α => ((M α).cfc (fun x => x * Real.log x)).trace) (nhds 1) (nhds ((ρ.M.cfc (fun x => x * Real.log x)).trace)) := by
            convert trace_cfc_tendsto_of_tendsto _ _ _ _ _ using 1;
            · exact Continuous.continuousOn ( Real.continuous_mul_log );
            · exact hM_cont;
            · exact hM_nonneg;
            · exact hM_one;
          exact h_diff_zero.comp ( tendsto_nhdsWithin_of_tendsto_nhds ( by norm_num [ Filter.Tendsto ] ) );
        simpa using h_diff_zero.sub_const ( ( ρ.M.cfc fun x => x * Real.log x ).trace );
      convert h_diff_zero using 2;
      rw [ HermitianMat.trace_cfc_eq, HermitianMat.trace_cfc_eq ];
    convert h_diff_zero.add ( ‹Filter.Tendsto ( fun h => ∑ i, ( Gh h ( ( M ( 1 + h ) ).H.eigenvalues i ) - ( M ( 1 + h ) ).H.eigenvalues i * Real.log ( ( M ( 1 + h ) ).H.eigenvalues i ) ) ) ( nhdsWithin 0 { 0 } ᶜ ) ( nhds 0 ) ∧ Filter.Tendsto ( fun h => ∑ i, ( Gh h ( ρ.M.H.eigenvalues i ) - ρ.M.H.eigenvalues i * Real.log ( ρ.M.H.eigenvalues i ) ) ) ( nhdsWithin 0 { 0 } ᶜ ) ( nhds 0 ) ›.1.sub ‹Filter.Tendsto ( fun h => ∑ i, ( Gh h ( ( M ( 1 + h ) ).H.eigenvalues i ) - ( M ( 1 + h ) ).H.eigenvalues i * Real.log ( ( M ( 1 + h ) ).H.eigenvalues i ) ) ) ( nhdsWithin 0 { 0 } ᶜ ) ( nhds 0 ) ∧ Filter.Tendsto ( fun h => ∑ i, ( Gh h ( ρ.M.H.eigenvalues i ) - ρ.M.H.eigenvalues i * Real.log ( ρ.M.H.eigenvalues i ) ) ) ( nhdsWithin 0 { 0 } ᶜ ) ( nhds 0 ) ›.2 ) using 2 <;> simp [ Finset.sum_sub_distrib ] ; ring;
  refine' h_triangle.congr' _;
  rw [ Filter.EventuallyEq, eventually_nhdsWithin_iff ];
  rw [ Metric.eventually_nhds_iff ] at *;
  obtain ⟨ ε, ε_pos, hε ⟩ := hK; use ε, ε_pos; intro y hy hy'; simp_all [ div_eq_inv_mul] ;
  have h_trace_rpow : ∀ (A : HermitianMat d ℂ) (p : ℝ), (A ^ p).trace = ∑ i, (A.H.eigenvalues i) ^ p := by
    exact fun A p => HermitianMat.trace_rpow_eq_sum A p;
  have := h_trace_rpow ( M ( 1 + y ) ) 1; have := h_trace_rpow ( ρ : HermitianMat d ℂ ) 1; simp_all
  simp +zetaDelta at *;
  simp [ ← this, div_eq_inv_mul, mul_sub, hy' ];
  simp [ ← Finset.mul_sum _ _ _, this.symm ]
  ring

/-- For a differentiable family of PSD matrices M(α) with M(1) having eigenvalues p_i,
    the function α ↦ Tr[M(α)^α] - Tr[M(α)] has derivative ⟪M(1), M(1).log⟫ at α = 1.
    This is because at α = 1, the function x^s - x has zero x-derivative (since d/dx(x^1) = 1),
    so only the s-derivative contributes, giving the same answer as for fixed eigenvalues. -/
private lemma hasDerivAt_trace_rpow_sub_trace_variable_base
    {M : ℝ → HermitianMat d ℂ}
    (hM_nonneg : ∀ᶠ α in nhds 1, 0 ≤ M α)
    (hM_cont : ContinuousAt M 1)
    (hM_one : M 1 = ρ.M) :
    HasDerivAt (fun α : ℝ => (M α ^ α).trace - (M α).trace) ⟪ρ.M, ρ.M.log⟫ 1 := by
  have h_deriv : HasDerivAt (fun α : ℝ => ((M α) ^ α).trace - (M α).trace - ((ρ.M) ^ α).trace + ρ.M.trace) 0 1 := by
    convert hasDerivAt_iff_tendsto_slope_zero.mpr _ using 1
    convert cross_term_slope_tendsto_zero hM_nonneg hM_cont hM_one using 2 ; norm_num [ hM_one ] ; ring!
  convert! h_deriv.add ( hasDerivAt_trace_rpow_sub_trace ρ.M ρ.nonneg ) using 1 <;> norm_num
  ring_nf
  ext; norm_num; ring

/-- The cross term in the derivative decomposition vanishes: the function
    α ↦ Tr[B(α)^α] - Tr[B(α)] - Tr[ρ^α] + 1 has derivative 0 at α = 1.
    This is because at α=1, B^1 = B, so ∂/∂B Tr[B^α] = Tr[·] (the trace is linear),
    making the cross term (variation in B times variation in α) vanish. -/
private lemma rpow_trace_cross_term_vanishes {ρ σ : MState d}
    (h : σ.M.ker ≤ ρ.M.ker) :
    HasDerivAt
      (fun α : ℝ => ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace
        - (ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat).trace
        - (ρ.M ^ α).trace + 1)
      0
      1 := by
  have h_cross_term : HasDerivAt (fun α : ℝ => ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace - (ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat).trace) ⟪ρ.M, ρ.M.log⟫ 1 ∧ HasDerivAt (fun α : ℝ => (ρ.M ^ α).trace) ⟪ρ.M, ρ.M.log⟫ 1 := by
    apply And.intro;
    · convert hasDerivAt_trace_rpow_sub_trace_variable_base _ _ _ using 1;
      · exact Filter.Eventually.of_forall fun α => B_of_nonneg ρ σ α;
      · convert B_of_continuousAt ρ σ h using 1;
      · simp [ HermitianMat.conj ];
    · convert hasDerivAt_trace_rpow_at_one ρ.M ( by exact ρ.nonneg ) using 1
  convert! HasDerivAt.add ( HasDerivAt.sub h_cross_term.1 h_cross_term.2 ) ( hasDerivAt_const _ _ ) using 1
  ring

private theorem sandwichedRelRentropy.hasDerivAt_trace_at_one {ρ σ : MState d}
    (h : σ.M.ker ≤ ρ.M.ker) :
    HasDerivAt
      (fun α : ℝ => ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace)
      ⟪ρ.M, ρ.M.log - σ.M.log⟫
      1 := by
  have h_deriv :=
    have h_cross_term := rpow_trace_cross_term_vanishes h
    have h_conj := hasDerivAt_trace_conj_at_one h
    have h_rpow := hasDerivAt_trace_rpow_at_one ρ.M ρ.nonneg
    (h_cross_term.add (h_conj.add h_rpow)).sub (hasDerivAt_const 1 1)
  convert! h_deriv using 2
  · simp only [Pi.sub_apply, Pi.add_apply]
    ring
  · simp only [inner_sub_right]
    ring

/--
The key limit: as α → 1, log(Tr[(ρ.conj σ^t)^α]) / (α-1) → ⟪ρ, log ρ - log σ⟫,
    where t = (1-α)/(2α). Derived from hasDerivAt_trace_at_one via L'Hôpital
    (or equivalently, log(1+x)/x → 1 and (f(α)-1)/(α-1) → f'(1)).
-/
private theorem sandwichedRelRentropy.limit_at_one (ρ σ : MState d)
    (h : σ.M.ker ≤ ρ.M.ker) :
    Filter.Tendsto
      (fun α : ℝ ↦ ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace.log / (α - 1))
      (nhdsWithin 1 (Set.Ioi 0 \ {1}))
      (nhds ⟪ρ.M, ρ.M.log - σ.M.log⟫) := by
  have h_log_approx : HasDerivAt (fun α : ℝ ↦ Real.log (((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace)) (⟪ρ.M, ρ.M.log - σ.M.log⟫) 1 := by
    have h_deriv := sandwichedRelRentropy.hasDerivAt_trace_at_one h
    convert h_deriv.log (by simp) using 1
    simp
  rw [hasDerivAt_iff_tendsto_slope] at h_log_approx
  convert h_log_approx.mono_left (nhdsWithin_mono _ _) using 2
  · norm_num [ div_eq_inv_mul, slope_def_field ]
  · simp

theorem inner_log_sub_log_nonneg (h : σ.M.ker ≤ ρ.M.ker) :
    0 ≤ ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  -- Take the limit α → 1+ of the sandwiched Renyi relative entropy,
  -- which converges to ⟪ρ.M, ρ.M.log - σ.M.log⟫ and is nonneg for all α > 1.
  -- Use the limit from the right: for α > 1, log(Tr[...]^α) / (α - 1) ≥ 0
  have h_limit := sandwichedRelRentropy.limit_at_one ρ σ h
  -- Restrict the filter to (1, ∞) ⊂ (0, ∞) \ {1}
  have h_mono : nhdsWithin (1 : ℝ) (Set.Ioi 1) ≤ nhdsWithin 1 (Set.Ioi 0 \ {1}) := by
    apply nhdsWithin_mono
    intro x hx
    exact ⟨Set.mem_Ioi.mpr (lt_trans zero_lt_one hx), ne_of_gt hx⟩
  have : (nhdsWithin (1 : ℝ) (Set.Ioi 1)).NeBot := inferInstance
  apply ge_of_tendsto (h_limit.mono_left h_mono)
  filter_upwards [self_mem_nhdsWithin] with α hα
  exact sandwichedRelRentropy_nonneg_α_gt_1 h hα

theorem sandwichedRelRentropy_nonneg {α : ℝ} (hα : 0 < α) (h : σ.M.ker ≤ ρ.M.ker) :
    0 ≤ if α = 1 then ⟪ρ.M, ρ.M.log - σ.M.log⟫
      else ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace.log / (α - 1) := by
  split_ifs with h1
  · exact inner_log_sub_log_nonneg h
  by_cases hα₂ : α > 1
  · exact sandwichedRelRentropy_nonneg_α_gt_1 h hα₂
  · have : α < 1 := by push Not at hα₂; exact lt_of_le_of_ne hα₂ h1
    exact sandwichedRelRentropy_nonneg_α_lt_1 h hα this

section additivity

--TODO Cleanup. Ugh.

/--
If the kernels of the components are contained, then the kernel of the Kronecker product is contained.
-/
lemma ker_kron_le_of_le {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (A C : Matrix d₁ d₁ ℂ) (B D : Matrix d₂ d₂ ℂ)
    (hA : LinearMap.ker A.toEuclideanLin ≤ LinearMap.ker C.toEuclideanLin)
    (hB : LinearMap.ker B.toEuclideanLin ≤ LinearMap.ker D.toEuclideanLin) :
    LinearMap.ker (A.kronecker B).toEuclideanLin ≤ LinearMap.ker (C.kronecker D).toEuclideanLin := by
  intro x hx
  simp only [Matrix.kronecker, LinearMap.mem_ker, Matrix.toLpLin_apply,
    WithLp.toLp_eq_zero] at hx ⊢
  -- By definition of Kronecker product, we know that $(A \otimes B)x = 0$ if and only if for all $i$ and $j$, $\sum_{k,l} A_{ik} B_{jl} x_{kl} = 0$.
  have h_kronecker : ∀ i j, ∑ k, A i k • ∑ l, B j l • x (k, l) = 0 := by
    intro i j
    replace hx := congr_fun hx ( i, j )
    simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
      Pi.zero_apply, smul_eq_mul, Finset.mul_sum] at hx ⊢
    rw [ ← Finset.sum_product' ]
    simpa only [mul_assoc, Finset.univ_product_univ] using hx
  -- Apply the hypothesis `hA` to each term in the sum.
  have h_apply_hA : ∀ i j, ∑ k, C i k • ∑ l, B j l • x (k, l) = 0 := by
    intro i j
    specialize hA ( show (WithLp.toLp 2 ( fun k => ∑ l, B j l • x ( k, l ) )) ∈ LinearMap.ker ( Matrix.toEuclideanLin A ) from ?_ )
    · simp_all only [smul_eq_mul, LinearMap.mem_ker]
      ext i_1 : 1
      simp_all only [PiLp.zero_apply]
      apply h_kronecker
    · exact congr(WithLp.ofLp $hA i)
  ext ⟨ i, j ⟩
  simp only [smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Pi.zero_apply] at h_kronecker h_apply_hA ⊢
  have h_apply_hB : ∑ l, D j l • ∑ k, C i k • x (k, l) = 0 := by
    specialize hB
    simp_all only [funext_iff, Pi.zero_apply, Prod.forall, smul_eq_mul]
    have := hB ( show  (WithLp.toLp 2 ( fun l => ∑ k, C i k * x ( k, l ) )) ∈ LinearMap.ker ( Matrix.toEuclideanLin B ) from ?_ )
    · simp_all only [LinearMap.mem_ker] ;
      exact congr(WithLp.ofLp $this j)
    · ext j
      specialize h_apply_hA i j
      simp [ Matrix.mulVec, dotProduct, Finset.mul_sum ] at h_apply_hA ⊢
      simp_rw [mul_left_comm]
      rw [Finset.sum_comm]
      exact h_apply_hA
  rw [← h_apply_hB]
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [ Finset.sum_sigma' ];
  refine' Finset.sum_bij ( fun x _ => ⟨ x.2, x.1 ⟩ ) _ _ _ _
  · simp
  · simp
  · simp
  · simp only [Finset.mem_univ, mul_assoc, Prod.mk.eta, mul_left_comm, imp_self, implies_true]

--TODO: Generalize to arbitrary PSD matrices.
/--
If the kernel of a product state is contained in another, the left component kernel is contained.
-/
lemma ker_le_of_ker_kron_le_left (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂)
  (h : (σ₁.M ⊗ₖ σ₂.M).ker ≤ (ρ₁.M ⊗ₖ ρ₂.M).ker) :
    σ₁.M.ker ≤ ρ₁.M.ker := by
  rw [← MState.prod_M, ← MState.prod_M] at h
  intro u hu
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℂ d₂, v ∉ (σ₂ :HermitianMat d₂ ℂ).ker ∧ v ∉ (ρ₂ :HermitianMat d₂ ℂ).ker := by
    have h_union : (σ₂ : HermitianMat d₂ ℂ).ker ≠ ⊤ ∧ (ρ₂ : HermitianMat d₂ ℂ).ker ≠ ⊤ := by
      constructor <;> intro h_top;
      · have h_contra : σ₂.M = 0 := by
          ext1
          simp_all [ Submodule.eq_top_iff'];
          ext i j
          specialize h_top ( EuclideanSpace.single j 1 )
          simp_all
          replace h_top := congr(WithLp.ofLp $h_top i)
          simp_all
          convert h_top using 1;
          erw [ Matrix.toLpLin_apply ]
          simp_all only [DensityOp.mat_M, PiLp.ofLp_single, Matrix.mulVec_single,
            MulOpposite.op_one, Pi.smul_apply, Matrix.col_apply, one_smul]
        exact σ₂.pos.ne' h_contra;
      · have h_contra : ρ₂.M = 0 := by
          ext i j; simp_all [ Submodule.eq_top_iff' ] ;
          convert! congr(WithLp.ofLp $(h_top (WithLp.toLp 2 ( Pi.single j 1 )) ) i) using 1
          simp
          simp [ HermitianMat.lin ];
          rfl
        exact ρ₂.pos.ne' h_contra;
    have h_union : ∀ (U V : Submodule ℂ (EuclideanSpace ℂ d₂)), U ≠ ⊤ → V ≠ ⊤ → ∃ v : EuclideanSpace ℂ d₂, v ∉ U ∧ v ∉ V := by
      intros U V hU hV;
      by_contra h_contra;
      have h_union : U ⊔ V = ⊤ := by
        ext v
        simp only [Submodule.mem_top, iff_true]
        by_cases hvU : v ∈ U <;> by_cases hvV : v ∈ V <;> simp_all [ Submodule.mem_sup ];
        · exact ⟨ v, hvU, 0, by simp, by simp ⟩;
        · exact ⟨ v, hvU, 0, by simp, by simp ⟩;
        · exact ⟨ 0, by simp, v, h_contra v hvU, by simp ⟩;
      have h_union : ∃ v : EuclideanSpace ℂ d₂, v ∉ U ∧ v ∈ V := by
        have h_union : ∃ v : EuclideanSpace ℂ d₂, v ∈ V ∧ v ∉ U := by
          have h_not_subset : ¬V ≤ U := by
            exact fun h => hU <| by rw [ eq_top_iff ] ; exact h_union ▸ sup_le ( by tauto ) h;
          exact Set.not_subset.mp h_not_subset;
        exact ⟨ h_union.choose, h_union.choose_spec.2, h_union.choose_spec.1 ⟩;
      obtain ⟨ v, hv₁, hv₂ ⟩ := h_union;
      obtain ⟨ w, hw₁, hw₂ ⟩ : ∃ w : EuclideanSpace ℂ d₂, w ∉ V ∧ w ∈ U := by
        obtain ⟨ w, hw ⟩ := ( show ∃ w : EuclideanSpace ℂ d₂, w ∉ V from by simpa [ Submodule.eq_top_iff' ] using hV ) ; use w; simp_all [ Submodule.eq_top_iff' ] ;
        exact Classical.not_not.1 fun hw' => hw <| h_contra _ hw';
      have h_union : v + w ∉ U ∧ v + w ∉ V := by
        exact ⟨ fun h => hv₁ <| by simpa using U.sub_mem h hw₂, fun h => hw₁ <| by simpa using V.sub_mem h hv₂ ⟩;
      exact h_contra ⟨ v + w, h_union.1, h_union.2 ⟩;
    exact h_union _ _ ( by tauto ) ( by tauto );
  -- Consider $z = u \otimes v$.
  set z : EuclideanSpace ℂ (d₁ × d₂) := WithLp.toLp 2 ( fun p => u p.1 * v p.2 );
  have hz : z ∈ (σ₁ ⊗ᴹ σ₂ : HermitianMat (d₁ × d₂) ℂ).ker := by
    ext ⟨i, j⟩
    simp [z]
    have h_kronecker : ∀ (A : Matrix d₁ d₁ ℂ) (B : Matrix d₂ d₂ ℂ) (u : d₁ → ℂ) (v : d₂ → ℂ), (A.kronecker B).mulVec (fun p => u p.1 * v p.2) = fun p => (A.mulVec u) p.1 * (B.mulVec v) p.2 := by
      intro A B u v; ext ⟨ i, j ⟩ ; simp [ Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm ] ;
      exact Fintype.sum_prod_type_right fun x => A i x.1 * (B j x.2 * (u x.1 * v x.2));
    convert! congr_fun ( h_kronecker σ₁.m σ₂.m u v ) ( i, j ) using 1 ; simp
    exact Or.inl ( by exact congr(WithLp.ofLp $hu i) );
  have hz' : z ∈ (ρ₁ ⊗ᴹ ρ₂ : HermitianMat (d₁ × d₂) ℂ).ker := by
    exact h hz;
  have hz'' : ∀ a b, (ρ₁.M.val.mulVec u) a * (ρ₂.M.val.mulVec v) b = 0 := by
    intro a b
    have hz'' : (ρ₁.M.val.mulVec u) a * (ρ₂.M.val.mulVec v) b = ((ρ₁ ⊗ᴹ ρ₂ : HermitianMat (d₁ × d₂) ℂ).val.mulVec z) (a, b) := by
      simp [ Matrix.mulVec, dotProduct];
      simp [  Finset.sum_mul, mul_assoc, mul_comm];
      simp [ z, Finset.mul_sum, mul_assoc, mul_left_comm ];
      erw [ Finset.sum_product ] ; simp
      exact rfl;
    exact hz''.trans ( by exact congr(WithLp.ofLp $hz' ( a, b )) );
  ext a; specialize hz'' a; simp_all [ Matrix.mulVec, dotProduct ] ;
  contrapose! hv;
  intro hv'; ext b; specialize hz'' b; simp_all
  exact hz''.resolve_left ( by exact hv )


--TODO: Generalize to arbitrary PSD matrices.
--TODO: Rewrite the proof using the `ker_le_of_ker_kron_le_left` lemma, and the fact that
-- there's a unitary whose conjugation swaps the kronecker product.
/--
If the kernel of a product state is contained in another, the right component kernel is contained.
-/
lemma ker_le_of_ker_kron_le_right (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂)
  (h : (σ₁.M ⊗ₖ σ₂.M).ker ≤ (ρ₁.M ⊗ₖ ρ₂.M).ker) :
    σ₂.M.ker ≤ ρ₂.M.ker := by
  rw [← MState.prod_M, ← MState.prod_M] at h
  intro v hv;
  have h_z : ∃ u : EuclideanSpace ℂ d₁, u ≠ 0 ∧ u ∉ σ₁.M.ker ∧ u ∉ ρ₁.M.ker := by
    have h_z : σ₁.M.ker ≠ ⊤ ∧ ρ₁.M.ker ≠ ⊤ := by
      have h_ker_ne_top : ∀ (ρ : MState d₁), ρ.M.ker ≠ ⊤ := by
        intro ρ hρ_top
        have h_contra : ρ.M = 0 := by
          ext i j
          simp_all [ Submodule.eq_top_iff' ] ;
          convert! congr(WithLp.ofLp $(hρ_top ( EuclideanSpace.single j 1 ) ) i) using 1
          simp
          erw [ Matrix.toLpLin_apply ]
          aesop
        exact ρ.pos.ne' h_contra;
      exact ⟨ h_ker_ne_top σ₁, h_ker_ne_top ρ₁ ⟩;
    have h_z : ∃ u : EuclideanSpace ℂ d₁, u ∉ σ₁.M.ker ∧ u ∉ ρ₁.M.ker := by
      have h_z : ∀ (U V : Submodule ℂ (EuclideanSpace ℂ d₁)), U ≠ ⊤ → V ≠ ⊤ → ∃ u : EuclideanSpace ℂ d₁, u ∉ U ∧ u ∉ V := by
        intro U V hU hV
        by_contra h_contra
        push Not at h_contra;
        have h_union : ∃ u : EuclideanSpace ℂ d₁, u ∉ U ∧ u ∈ V := by
          exact Exists.elim ( show ∃ u : EuclideanSpace ℂ d₁, u ∉ U from by simpa [ Submodule.eq_top_iff' ] using hU ) fun u hu => ⟨ u, hu, h_contra u hu ⟩;
        obtain ⟨ u, hu₁, hu₂ ⟩ := h_union;
        have h_union : ∀ v : EuclideanSpace ℂ d₁, v ∈ U → v + u ∈ V := by
          intro v hv; specialize h_contra ( v + u ) ; simp_all [ Submodule.add_mem_iff_right ] ;
        have h_union : ∀ v : EuclideanSpace ℂ d₁, v ∈ U → v ∈ V := by
          exact fun v hv => by simpa using V.sub_mem ( h_union v hv ) hu₂;
        exact hV ( eq_top_iff.mpr fun x hx => by by_cases hxU : x ∈ U <;> aesop );
      exact h_z _ _ ( by tauto ) ( by tauto );
    exact ⟨ h_z.choose, by intro h; simpa [ h ] using h_z.choose_spec.1, h_z.choose_spec.1, h_z.choose_spec.2 ⟩;
  obtain ⟨ u, hu₁, hu₂, hu₃ ⟩ := h_z;
  -- Consider the vector $z = u \otimes v$.
  set z : EuclideanSpace ℂ (d₁ × d₂) := .toLp 2 ( fun p => u p.1 * v p.2 );
  have hz : z ∈ (σ₁ ⊗ᴹ σ₂).M.ker := by
    -- By definition of $z$, we have $(σ₁ ⊗ σ₂).mat.mulVec z = σ₁.mat.mulVec u ⊗ σ₂.mat.mulVec v$.
    have hz_mul : (σ₁ ⊗ᴹ σ₂).M.mat.mulVec z = fun p => (σ₁.M.mat.mulVec u) p.1 * (σ₂.M.mat.mulVec v) p.2 := by
      ext p; simp [z, Matrix.mulVec]
      simp [ dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm ];
      rw [ ← Finset.sum_product' ];
      refine' Finset.sum_bij ( fun x _ => ( x.2, x.1 ) ) _ _ _ _ <;> simp;
      exact fun a b => Or.inl <| Or.inl <| rfl;
    simp_all [ funext_iff, Matrix.mulVec ];
    ext ⟨ a, b ⟩
    specialize hz_mul a b
    simp_all [ dotProduct]
    convert! hz_mul using 1;
    simp_all only [zero_eq_mul]
    exact Or.inr ( by exact congr(WithLp.ofLp $hv b) );
  have hz' : z ∈ (ρ₁ ⊗ᴹ ρ₂).M.ker := by
    exact h hz;
  have hz'' : ∀ i j, (ρ₁.M.val.mulVec u) i * (ρ₂.M.val.mulVec v) j = 0 := by
    intro i j;
    have hz'' : (ρ₁.M.val.kronecker ρ₂.M.val).mulVec (fun p => u p.1 * v p.2) (i, j) = (ρ₁.M.val.mulVec u) i * (ρ₂.M.val.mulVec v) j := by
      simp [ Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm ];
      simp [ mul_assoc, Finset.mul_sum, Finset.sum_mul ];
      rw [ ← Finset.sum_product' ];
      refine' Finset.sum_bij ( fun x _ => ( x.2, x.1 ) ) _ _ _ _
      · simp
      · simp
      · simp
      · intro _ _
        simp only [DensityOp.m, HermitianMat.mat_apply]
    refine hz''.symm.trans ?_
    have h0 := (HermitianMat.mem_ker_iff_mulVec_zero _ z).1 hz'
    rw [MState.prod_M, HermitianMat.kronecker_mat] at h0
    simpa [z] using congr_fun h0 (i, j)
  contrapose! hz'';
  obtain ⟨ i, hi ⟩ := Function.ne_iff.mp ( show ρ₁.M.val.mulVec u ≠ 0 from fun h => hu₃ <| congr(WithLp.toLp 2 $h))
  obtain ⟨ j, hj ⟩ := Function.ne_iff.mp ( show ρ₂.M.val.mulVec v ≠ 0 from fun h => hz'' <| congr(WithLp.toLp 2 $h))
  use i, j
  aesop;

/--
The kernel of a product state is contained in another product state's kernel iff the individual
kernels are contained.
-/
lemma ker_prod_le_iff (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    (σ₁.M ⊗ₖ σ₂.M).ker ≤ (ρ₁.M ⊗ₖ ρ₂.M).ker ↔ σ₁.M.ker ≤ ρ₁.M.ker ∧ σ₂.M.ker ≤ ρ₂.M.ker := by
  constructor <;> intro h;
  · exact ⟨ ker_le_of_ker_kron_le_left ρ₁ σ₁ ρ₂ σ₂ h, ker_le_of_ker_kron_le_right ρ₁ σ₁ ρ₂ σ₂ h ⟩;
  · convert! ker_kron_le_of_le _ _ _ _ h.1 h.2 using 1

--TODO: Generalize to RCLike.
omit [DecidableEq d₁] [DecidableEq d₂] in
lemma HermitianMat.inner_kron
    (A : HermitianMat d₁ ℂ) (B : HermitianMat d₂ ℂ) (C : HermitianMat d₁ ℂ) (D : HermitianMat d₂ ℂ) :
    ⟪A ⊗ₖ B, C ⊗ₖ D⟫ = ⟪A, C⟫ * ⟪B, D⟫ := by
  -- Apply the property of the trace of Kronecker products.
  have h_trace_kron : ∀ (A₁ B₁ : Matrix d₁ d₁ ℂ) (A₂ B₂ : Matrix d₂ d₂ ℂ), Matrix.trace (Matrix.kroneckerMap (· * ·) A₁ A₂ * Matrix.kroneckerMap (· * ·) B₁ B₂) = Matrix.trace (A₁ * B₁) * Matrix.trace (A₂ * B₂) := by
    intro A₁ B₁ A₂ B₂
    rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
  simp_all only [inner, IsMaximalSelfAdjoint.RCLike_selfadjMap, kronecker_mat, RCLike.mul_re,
    RCLike.re_to_complex, RCLike.im_to_complex, sub_eq_self, mul_eq_zero];
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, mat_apply, Complex.im_sum,
    Complex.mul_im];
  left;
  have h_symm : ∀ x x_1, (A x x_1).re * (C x_1 x).im + (A x x_1).im * (C x_1 x).re = -((A x_1 x).re * (C x x_1).im + (A x_1 x).im * (C x x_1).re) := by
    intro x y; have := congr_fun ( congr_fun A.2 y ) x; have := congr_fun ( congr_fun C.2 y ) x; simp_all [ Complex.ext_iff ] ;
    grind;
  have h_sum_zero : ∑ x, ∑ x_1, ((A x x_1).re * (C x_1 x).im + (A x x_1).im * (C x_1 x).re) = ∑ x, ∑ x_1, -((A x x_1).re * (C x_1 x).im + (A x x_1).im * (C x_1 x).re) := by
    rw [ Finset.sum_comm ];
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => h_symm _ _ ▸ rfl;
  norm_num [ Finset.sum_add_distrib ] at * ; linarith

attribute [fun_prop] ContinuousAt.rpow

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

theorem sandwichedRelRentropy_additive_alpha_one_aux (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂)
  (h1 : σ₁.M.ker ≤ ρ₁.M.ker) (h2 : σ₂.M.ker ≤ ρ₂.M.ker) :
    ⟪(ρ₁ ⊗ᴹ ρ₂).M, (ρ₁ ⊗ᴹ ρ₂).M.log - (σ₁ ⊗ᴹ σ₂).M.log⟫ =
    ⟪ρ₁.M, ρ₁.M.log - σ₁.M.log⟫_ℝ + ⟪ρ₂.M, ρ₂.M.log - σ₂.M.log⟫ := by
  simp only [MState.prod_M]
  have h_log_kron : (ρ₁.M ⊗ₖ ρ₂.M).log
        = ρ₁.M.log ⊗ₖ ρ₂.M.supportProj + ρ₁.M.supportProj ⊗ₖ ρ₂.M.log
      ∧ (σ₁.M ⊗ₖ σ₂.M).log
        = σ₁.M.log ⊗ₖ σ₂.M.supportProj + σ₁.M.supportProj ⊗ₖ σ₂.M.log :=
    ⟨HermitianMat.log_kron_with_proj, HermitianMat.log_kron_with_proj⟩
  have h_inner_supportProj : ∀ (A : HermitianMat d₁ ℂ) (B : HermitianMat d₂ ℂ),
      ⟪ρ₁.M ⊗ₖ ρ₂.M, A ⊗ₖ B⟫ = ⟪ρ₁.M, A⟫ * ⟪ρ₂.M, B⟫ :=
    fun A B => HermitianMat.inner_kron ρ₁.M ρ₂.M A B
  simp only [HermitianMat.ker] at h1 h2
  simp_all only [inner_sub_right, inner_add_right,
    HermitianMat.inner_supportProj_self, DensityOp.tr, mul_one, one_mul,
    HermitianMat.inner_supportProj_of_ker_le]
  abel

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The index type of the basis that `StdBasis.some ℂ E` picks out. -/
local notation "ι₀" => Fin (Module.finrank ℂ E)

section Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι]

/-- The state on `EuclideanSpace ℂ ι` with the same density matrix as `ρ`. It carries the matrix
form of every basis-free quantity attached to `ρ`, which is how facts proved for `MState` are
transported to `DensityOp E`. -/
private def coords (ρ : DensityOp E) : MState ι :=
  DensityOp.ofMat (ρ.M : HermitianMat ι ℂ) ρ.nonneg ρ.tr

@[simp]
private theorem coords_M (ρ : DensityOp E) :
    ((coords (ι := ι) ρ).M : HermitianMat ι ℂ) = ρ.M :=
  DensityOp.M_ofMat _ _ _

private theorem inner_op_log_sub_log (ρ σ : DensityOp E) :
    ⟪ρ.op, ρ.op.log - σ.op.log⟫ =
      ⟪(ρ.M : HermitianMat ι ℂ), (ρ.M : HermitianMat ι ℂ).log - (σ.M : HermitianMat ι ℂ).log⟫ := by
  rw [← HermitianOp.inner_toMat (ι := ι), HermitianOp.toMat_sub, HermitianOp.toMat_log,
    HermitianOp.toMat_log]
  rfl

private theorem trace_conj_rpow (ρ σ : DensityOp E) (α β : ℝ) :
    ((ρ.op.conj ((σ.op ^ β).op)) ^ α).trace =
      (((ρ.M : HermitianMat ι ℂ).conj ((σ.M : HermitianMat ι ℂ) ^ β).mat) ^ α).trace := by
  have h : StdBasis.toMat ℂ E ι ((σ.op ^ β).op) = ((σ.M : HermitianMat ι ℂ) ^ β).mat := by
    rw [← HermitianOp.toMat_mat (ι := ι), HermitianOp.toMat_rpow]
    rfl
  rw [← HermitianOp.trace_toMat (ι := ι), HermitianOp.toMat_rpow, HermitianOp.toMat_conj, h]
  rfl

private theorem ker_op_le_ker_op {ρ σ : DensityOp E} :
    σ.op.ker ≤ ρ.op.ker ↔ (σ.M : HermitianMat ι ℂ).ker ≤ (ρ.M : HermitianMat ι ℂ).ker :=
  HermitianOp.ker_toMat_le_ker_toMat.symm

/-- `sandwichedRelRentropy_nonneg`, transported to the density matrix of a state on an arbitrary
finite-dimensional space. -/
theorem sandwichedRelRentropy_nonneg_M {α : ℝ} (hα : 0 < α) {ρ σ : DensityOp E}
    (h : (σ.M : HermitianMat ι ℂ).ker ≤ (ρ.M : HermitianMat ι ℂ).ker) :
    0 ≤ if α = 1 then
        ⟪(ρ.M : HermitianMat ι ℂ),
          (ρ.M : HermitianMat ι ℂ).log - (σ.M : HermitianMat ι ℂ).log⟫
      else
        (((ρ.M : HermitianMat ι ℂ).conj
          ((σ.M : HermitianMat ι ℂ) ^ ((1 - α)/(2 * α))).mat) ^ α).trace.log / (α - 1) := by
  simpa using sandwichedRelRentropy_nonneg (ρ := coords (ι := ι) ρ) (σ := coords (ι := ι) σ)
    hα (by simpa using h)

end Bridge

theorem sandwichedRelRentropy_op_nonneg {α : ℝ} (hα : 0 < α) {ρ σ : DensityOp E}
    (h : σ.op.ker ≤ ρ.op.ker) :
    0 ≤ if α = 1 then ⟪ρ.op, ρ.op.log - σ.op.log⟫
      else ((ρ.op.conj ((σ.op ^ ((1 - α) / (2 * α))).op)) ^ α).trace.log / (α - 1) := by
  let _ : StdBasis ℂ E ι₀ := StdBasis.some ℂ E
  rw [inner_op_log_sub_log (ι := ι₀), trace_conj_rpow (ι := ι₀)]
  exact sandwichedRelRentropy_nonneg_M hα (ker_op_le_ker_op.1 h)

/-- The Sandwiched Renyi Relative Entropy, defined with ln (nits). Note that at `α = 1` this definition
  switch to the standard Relative Entropy, for continuity. For α ≤ 0, this gives junk value 0. (There
  is no conventional value for α < 0; there is a continuous limit at α = 0, but it is complicated and
  unneeded at the moment.)

  This makes no reference to a basis; `sandwichedRelRentropy_eq_matrix` is the matrix analogue. -/
def SandwichedRelRentropy (α : ℝ) (ρ σ : DensityOp E) : ENNReal :=
  open Classical in
  if hα : 0 < α then
    if h : σ.op.ker ≤ ρ.op.ker
    then (.ofNNReal ⟨if α = 1 then
        ⟪ρ.op, ρ.op.log - σ.op.log⟫
      else
        ((ρ.op.conj ((σ.op ^ ((1 - α)/(2 * α))).op)) ^ α).trace.log / (α - 1),
      sandwichedRelRentropy_op_nonneg hα h⟩)
    else ⊤
  else 0

notation "D̃_" α "(" ρ "‖" σ ")" => SandwichedRelRentropy α ρ σ

/-- **Matrix analogue of `SandwichedRelRentropy`.** -/
theorem sandwichedRelRentropy_eq_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι]
    (α : ℝ) (ρ σ : DensityOp E) :
    D̃_ α(ρ‖σ) =
      open Classical in
      if hα : 0 < α then
        if h : (σ.M : HermitianMat ι ℂ).ker ≤ (ρ.M : HermitianMat ι ℂ).ker
        then (.ofNNReal ⟨if α = 1 then
            ⟪(ρ.M : HermitianMat ι ℂ),
              (ρ.M : HermitianMat ι ℂ).log - (σ.M : HermitianMat ι ℂ).log⟫
          else
            (((ρ.M : HermitianMat ι ℂ).conj
              ((σ.M : HermitianMat ι ℂ) ^ ((1 - α)/(2 * α))).mat) ^ α).trace.log / (α - 1),
          sandwichedRelRentropy_nonneg_M hα h⟩)
        else ⊤
      else 0 := by
  rw [SandwichedRelRentropy]
  by_cases hα : 0 < α
  swap
  · rw [dif_neg hα, dif_neg hα]
  rw [dif_pos hα, dif_pos hα]
  by_cases h : σ.op.ker ≤ ρ.op.ker
  swap
  · rw [dif_neg h, dif_neg (fun hc ↦ h (ker_op_le_ker_op (ι := ι) |>.2 hc))]
  rw [dif_pos h, dif_pos (ker_op_le_ker_op (ι := ι) |>.1 h), ENNReal.coe_inj]
  congr! 1
  split_ifs with h₁
  · exact inner_op_log_sub_log (ι := ι) ρ σ
  · rw [trace_conj_rpow (ι := ι)]

/-- The sandwiched Rényi relative entropy is unchanged by reading both states on another space
whose preferred basis has the same index type. -/
@[simp]
theorem sandwichedRelRentropy_transport {ι : Type*} [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [StdBasis ℂ F ι]
    (α : ℝ) (ρ σ : DensityOp E) :
    D̃_ α(ρ.transport F‖σ.transport F) = D̃_ α(ρ‖σ) := by
  have hρ : ((ρ.transport F).M : HermitianMat ι ℂ) = ρ.M := DensityOp.M_transport ρ
  have hσ : ((σ.transport F).M : HermitianMat ι ℂ) = σ.M := DensityOp.M_transport σ
  have hker : ((σ.transport F).M : HermitianMat ι ℂ).ker ≤
        ((ρ.transport F).M : HermitianMat ι ℂ).ker ↔
      (σ.M : HermitianMat ι ℂ).ker ≤ (ρ.M : HermitianMat ι ℂ).ker := by
    rw [hρ, hσ]
  rw [sandwichedRelRentropy_eq_matrix (ι := ι), sandwichedRelRentropy_eq_matrix (ι := ι)]
  by_cases hα : 0 < α
  swap
  · rw [dif_neg hα, dif_neg hα]
  rw [dif_pos hα, dif_pos hα]
  by_cases h : (σ.M : HermitianMat ι ℂ).ker ≤ (ρ.M : HermitianMat ι ℂ).ker
  swap
  · rw [dif_neg h, dif_neg fun hc ↦ h (hker.mp hc)]
  rw [dif_pos h, dif_pos (hker.mpr h), ENNReal.coe_inj]
  refine NNReal.coe_injective ?_
  simp only [hρ, hσ]

/-- The quantum relative entropy `𝐃(ρ‖σ) := Tr[ρ (log ρ - log σ)]`. Also called
the Umegaki quantum relative entropy, when it's necessary to distinguish from other
relative entropies. -/
def qRelativeEnt (ρ σ : DensityOp E) : ENNReal :=
  D̃_1(ρ‖σ)

notation "𝐃(" ρ "‖" σ ")" => qRelativeEnt ρ σ

/-- The quantum relative entropy is unchanged by reading both states on another space whose
preferred basis has the same index type. -/
@[simp]
theorem qRelativeEnt_transport {ι : Type*} [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [StdBasis ℂ F ι]
    (ρ σ : DensityOp E) : 𝐃(ρ.transport F‖σ.transport F) = 𝐃(ρ‖σ) :=
  sandwichedRelRentropy_transport 1 ρ σ

end Operator

/-- `sandwichedRelRentropy_eq_matrix` for a state on `EuclideanSpace ℂ d`, whose preferred basis is
the standard one, so that the index type is determined by the state. -/
theorem MState.sandwichedRelRentropy_eq_matrix (α : ℝ) (ρ σ : MState d) :
    D̃_ α(ρ‖σ) =
      open Classical in
      if hα : 0 < α then
        if h : σ.M.ker ≤ ρ.M.ker
        then (.ofNNReal ⟨if α = 1 then
            ⟪ρ.M, ρ.M.log - σ.M.log⟫
          else
            ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α))).mat) ^ α).trace.log / (α - 1),
          sandwichedRelRentropy_nonneg_M hα h⟩)
        else ⊤
      else 0 :=
  _root_.sandwichedRelRentropy_eq_matrix α ρ σ

/--
The Sandwiched Renyi Relative entropy is additive for α=1 (standard relative entropy).
-/
private theorem sandwichedRelRentropy_additive_alpha_one (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    D̃_ 1(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = D̃_ 1(ρ₁‖σ₁) + D̃_ 1(ρ₂‖σ₂) := by
  have hker : (σ₁ ⊗ᴹ σ₂).M.ker ≤ (ρ₁ ⊗ᴹ ρ₂).M.ker ↔
      σ₁.M.ker ≤ ρ₁.M.ker ∧ σ₂.M.ker ≤ ρ₂.M.ker := by
    simpa using ker_prod_le_iff ρ₁ σ₁ ρ₂ σ₂
  by_cases h1 : σ₁.M.ker ≤ ρ₁.M.ker
  <;> by_cases h2 : σ₂.M.ker ≤ ρ₂.M.ker
  · simp only [MState.sandwichedRelRentropy_eq_matrix, zero_lt_one, ↓reduceDIte, ↓reduceIte, h1, h2,
      hker.mpr ⟨h1, h2⟩]
    rw [← ENNReal.coe_add, ENNReal.coe_inj]
    apply NNReal.eq
    push_cast
    exact sandwichedRelRentropy_additive_alpha_one_aux ρ₁ σ₁ ρ₂ σ₂ h1 h2
  all_goals
    simp only [MState.sandwichedRelRentropy_eq_matrix, zero_lt_one, ↓reduceDIte, ↓reduceIte, h1, h2,
      add_top, top_add, dite_eq_right_iff, ENNReal.coe_ne_top, imp_false]
    rw [hker]
    tauto

lemma sandwiched_term_product (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) (α β : ℝ) :
    (((ρ₁ ⊗ᴹ ρ₂).M.conj ((σ₁ ⊗ᴹ σ₂).M ^ β).mat) ^ α).trace =
    ((ρ₁.M.conj (σ₁.M ^ β).mat) ^ α).trace * ((ρ₂.M.conj (σ₂.M ^ β).mat) ^ α).trace := by
  simp only [MState.prod_M]
  rw [← HermitianMat.trace_kronecker]
  rw [← HermitianMat.rpow_kron α ?_ ?_, ← HermitianMat.conj_kron,
    HermitianMat.rpow_kron β σ₁.nonneg σ₂.nonneg, HermitianMat.kronecker_mat]
  · exact HermitianMat.conj_nonneg _ ρ₁.nonneg
  · exact HermitianMat.conj_nonneg _ ρ₂.nonneg

/-
The Sandwiched Renyi Relative entropy is additive for alpha != 1.
-/
theorem sandwichedRelRentropy_additive_alpha_ne_one {α : ℝ} (hα : α ≠ 1) (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    D̃_ α(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = D̃_ α(ρ₁‖σ₁) + D̃_ α(ρ₂‖σ₂) := by
  by_cases hα0 : 0 < α; swap
  · simp [MState.sandwichedRelRentropy_eq_matrix, hα0]
  by_cases h_ker : σ₁.M.ker ≤ ρ₁.M.ker ∧ σ₂.M.ker ≤ ρ₂.M.ker
  · simp_all [MState.sandwichedRelRentropy_eq_matrix]
    -- Apply the additivity of the trace term to split the logarithm into the sum of the logarithms.
    have h_trace_add : Real.log ((ρ₁ ⊗ᴹ ρ₂).M.conj ((σ₁ ⊗ᴹ σ₂).M ^ ((1 - α) / (2 * α))).mat ^ α).trace = Real.log ((ρ₁.M.conj (σ₁.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace + Real.log ((ρ₂.M.conj (σ₂.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace := by
      rw [ sandwiched_term_product, Real.log_mul ];
      · exact (sandwiched_trace_pos h_ker.1).ne'
      · exact (sandwiched_trace_pos h_ker.2).ne'
    split_ifs <;> simp_all
    · norm_num [ add_div ];
      exact rfl;
    · exact absurd ((ker_prod_le_iff ρ₁ σ₁ ρ₂ σ₂).2 h_ker) ‹_›
  · have h_ker_prod : ¬((σ₁.M ⊗ₖ σ₂.M).ker ≤ (ρ₁.M ⊗ₖ ρ₂.M).ker) := by
      simp_all  [ ker_prod_le_iff ]
    rw [not_and_or] at h_ker
    rcases h_ker with h_ker | h_ker
    · simp [MState.sandwichedRelRentropy_eq_matrix, h_ker_prod, h_ker, hα0]
    · simp [MState.sandwichedRelRentropy_eq_matrix, h_ker_prod, h_ker, hα0]

end additivity

/-- The Sandwiched Renyi Relative entropy is additive when the inputs are product states -/
@[simp]
theorem sandwichedRelRentropy_additive (α) (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    D̃_ α(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = D̃_ α(ρ₁‖σ₁) + D̃_ α(ρ₂‖σ₂) := by
  rcases eq_or_ne α 1 with rfl | hα
  · exact sandwichedRelRentropy_additive_alpha_one ρ₁ σ₁ ρ₂ σ₂
  · apply sandwichedRelRentropy_additive_alpha_ne_one hα

/-- The quantum relative entropy is additive when the inputs are product states -/
@[simp]
theorem qRelativeEnt_additive (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    𝐃(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = 𝐃(ρ₁‖σ₁) + 𝐃(ρ₂‖σ₂) := by
  --or `simp [SandwichedRelRentropy]`.
  exact sandwichedRelRentropy_additive_alpha_one ρ₁ σ₁ ρ₂ σ₂

@[simp]
theorem sandwichedRelRentropy_relabel (ρ σ : MState d) (e : d₂ ≃ d) :
    D̃_ α(ρ.relabel e‖σ.relabel e) = D̃_ α(ρ‖σ) := by
  simp only [MState.sandwichedRelRentropy_eq_matrix]
  rw! [MState.relabel_M, MState.relabel_M, HermitianMat.ker_reindex_le_iff]
  --Why doesn't this `simp`? Because it's an if condition, I'm guessing
  simp [HermitianMat.conj_submatrix]

@[simp]
theorem sandwichedRelRentropy_self (hα : 0 < α) (ρ : MState d) :
  --Technically this holds for all α except for `-1` and `0`. But those are stupid.
  --TODO: Maybe SandwichedRelRentropy should actually be defined differently for α = 0?
    D̃_ α(ρ‖ρ) = 0 := by
  rw [MState.sandwichedRelRentropy_eq_matrix]
  simp only [hα, ↓reduceDIte, le_refl, sub_self, inner_zero_right, ENNReal.coe_eq_zero]
  apply NNReal.coe_injective
  show (if α = 1 then (0 : ℝ)
      else ((ρ.M.conj ((ρ.M ^ ((1 - α) / (2 * α))).mat)) ^ α).trace.log / (α - 1)) = 0
  simp only [ite_eq_left_iff, div_eq_zero_iff, Real.log_eq_zero]
  intro hα
  left; right; left
  rw [HermitianMat.rpow_eq_cfc, HermitianMat.rpow_eq_cfc]
  nth_rw 2 [← HermitianMat.cfc_id ρ.M]
  rw [HermitianMat.cfc_conj, ← HermitianMat.cfc_comp]
  conv =>
    enter [1, 1]
    equals ρ.M.cfc id =>
      apply HermitianMat.cfc_congr_of_nonneg ρ.nonneg
      intro i (hi : 0 ≤ i)
      simp
      rw [← Real.rpow_mul_natCast hi, ← Real.rpow_one_add' hi]
      · rw [← Real.rpow_mul hi]
        field_simp
        ring_nf
        exact Real.rpow_one i
      · field_simp; ring_nf; positivity
  simp

/-- The Sandwiched Renyi Relative entropy is infinite exactly when the support condition fails. -/
theorem sandwichedRelRentropy_eq_top (hα : 0 < α) {ρ σ : MState d} (h : ¬ σ.M.ker ≤ ρ.M.ker) :
    D̃_ α(ρ‖σ) = ⊤ := by
  rw [MState.sandwichedRelRentropy_eq_matrix, dif_pos hα, dif_neg h]

theorem qRelativeEnt_eq_top {ρ σ : MState d} (h : ¬ σ.M.ker ≤ ρ.M.ker) : 𝐃(ρ‖σ) = ⊤ :=
  sandwichedRelRentropy_eq_top zero_lt_one h

@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem sandwichedRelEntropy_ne_top {ρ σ : MState d} [σ.M.NonSingular] : D̃_ α(ρ‖σ) ≠ ⊤ := by
  by_cases 0 < α
  · simp [MState.sandwichedRelRentropy_eq_matrix, HermitianMat.nonSingular_ker_bot, *]
  · simp [MState.sandwichedRelRentropy_eq_matrix, *]

@[fun_prop]
lemma continuousOn_exponent : ContinuousOn (fun α : ℝ => (1 - α) / (2 * α)) (Set.Ioi 0) := by
  fun_prop (disch := intros; linarith [Set.mem_Ioi.mp ‹_›])

@[fun_prop]
lemma Complex.continuousOn_cpow_const_Ioi (z : ℂ) :
    ContinuousOn (fun r : ℝ => z ^ (r : ℂ)) (Set.Ioi 0) := by
  apply ContinuousOn.const_cpow (f := Complex.ofReal)
  · fun_prop
  · grind [ofReal_ne_zero]

/--
The function α ↦ (1 - α) / (2 * α) maps the interval (1, ∞) to (-∞, 0).
-/
lemma maps_to_Iio_of_Ioi_1 : Set.MapsTo (fun α : ℝ => (1 - α) / (2 * α)) (Set.Ioi 1) (Set.Iio 0) := by
  intro x hx
  rw [Set.mem_Ioi] at hx
  rw [Set.mem_Iio]
  have h1 : 1 - x < 0 := by linarith
  have h2 : 0 < 2 * x := by linarith
  exact div_neg_of_neg_of_pos h1 h2

--PR'ed: #35494
@[simp]
theorem frontier_singleton {X : Type*} [TopologicalSpace X] [T1Space X] [PerfectSpace X]
    (p : X) : frontier {p} = {p} := by
  simp [frontier]

private theorem sandwichedRelRentropy.continuousOn_Ioi_1_aux (ρ σ : MState d) :
    ContinuousOn (fun (α : ℝ) ↦ ((HermitianMat.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ρ.M ^ α)) (Set.Ioi 1) := by
  have h_cont : ContinuousOn (fun α : ℝ => (HermitianMat.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ρ.M) (Set.Ioi 1) := by
    have h_cont : ContinuousOn (fun α : ℝ => (σ.M ^ ((1 - α) / (2 * α))).mat) (Set.Ioi 1) := by
      have h_cont : ContinuousOn (fun α : ℝ => σ.M ^ ((1 - α) / (2 * α))) (Set.Ioi 1) := by
        have h_cont : ContinuousOn (fun α : ℝ => (1 - α) / (2 * α)) (Set.Ioi 1) := by
          exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ( continuousAt_const.sub continuousAt_id ) ( continuousAt_const.mul continuousAt_id ) ( by linarith [ hx.out ] )
        have h_cont : ContinuousOn (fun α : ℝ => (σ.M ^ α)) (Set.Iio 0) := by
          apply_rules [ HermitianMat.continuousOn_rpow_neg ];
        exact h_cont.comp ‹_› fun x hx => by rw [ Set.mem_Iio ] ; rw [ div_lt_iff₀ ] <;> linarith [ hx.out ] ;
      exact Continuous.comp_continuousOn ( by continuity ) h_cont;
    fun_prop;
  -- Apply the lemma HermitianMat.continuousOn_rpow_joint_nonneg_pos with the given conditions.
  apply HermitianMat.continuousOn_rpow_joint_nonneg_pos;
  · exact h_cont;
  · exact continuousOn_id;
  · exact fun x hx => zero_lt_one.trans hx;

private theorem sandwichedRelRentropy.continuousOn_Ioi_1 (ρ σ : MState d) :
    ContinuousOn (fun α => D̃_ α(ρ‖σ)) (Set.Ioi 1) := by
  simp only [MState.sandwichedRelRentropy_eq_matrix]
  split_ifs with hρ
  · rw [continuousOn_congr (f := fun α ↦ ENNReal.ofReal
      (Real.log ((HermitianMat.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ρ.M ^ α).trace / (α - 1)))]
    · apply (ENNReal.continuous_ofReal).comp_continuousOn
      apply ContinuousOn.div₀
      · apply ContinuousOn.log
        · exact HermitianMat.trace_Continuous.comp_continuousOn
            (continuousOn_Ioi_1_aux ρ σ)
        · intro x hx
          apply LT.lt.ne'
          grw [← sandwiched_trace_of_gt_1 hρ hx]
          exact zero_lt_one
      · fun_prop
      · clear hρ; grind
    · intro α (hα : 1 < α)
      dsimp only
      have hα₀ : 0 < α := by linarith
      have hα₁ : α ≠ 1 := by linarith
      simp only [dif_pos hα₀, if_neg hα₁, ENNReal.ofReal]
      rw [Real.toNNReal_of_nonneg]
      rfl
  · rw [continuousOn_congr (f := fun α ↦ ⊤)]
    · fun_prop
    · clear ρ σ hρ;
      grind only [→ Set.EqOn.eq_of_mem, = Set.mem_Ioi, Set.EqOn, cases Or]

private theorem sandwichedRelRentropy.continuousOn_Ioo_0_1_aux (ρ σ : MState d) :
    ContinuousOn (fun (α : ℝ) ↦ ((HermitianMat.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ρ.M ^ α)) (Set.Ioo 0 1) := by
  have h_cont : ContinuousOn (fun α : ℝ => (HermitianMat.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ρ.M) (Set.Ioo 0 1) := by
    have h_cont : ContinuousOn (fun α : ℝ => (σ.M ^ ((1 - α) / (2 * α))).mat) (Set.Ioo 0 1) := by
      have h_cont : ContinuousOn (fun α : ℝ => σ.M ^ ((1 - α) / (2 * α))) (Set.Ioo 0 1) := by
        have h_exp_cont : ContinuousOn (fun α : ℝ => (1 - α) / (2 * α)) (Set.Ioo 0 1) := by
          exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ( continuousAt_const.sub continuousAt_id ) ( continuousAt_const.mul continuousAt_id ) ( by linarith [ hx.1 ] )
        have h_rpow_cont : ContinuousOn (fun α : ℝ => (σ.M ^ α)) (Set.Ioi 0) := by
          apply_rules [ HermitianMat.continuousOn_rpow_pos ]
        exact h_rpow_cont.comp h_exp_cont fun x hx => by rw [ Set.mem_Ioi ] ; apply div_pos <;> linarith [ hx.1, hx.2 ]
      exact Continuous.comp_continuousOn ( by continuity ) h_cont
    fun_prop
  apply HermitianMat.continuousOn_rpow_joint_nonneg_pos
  · exact h_cont
  · exact continuousOn_id
  · exact fun x hx => hx.1

/-- Continuity on (0,1): the sandwich relative Rényi entropy is continuous in α on (0,1). -/
private theorem sandwichedRelRentropy.continuousOn_Ioo_0_1 (ρ σ : MState d) :
    ContinuousOn (fun α => D̃_ α(ρ‖σ)) (Set.Ioo 0 1) := by
  simp only [MState.sandwichedRelRentropy_eq_matrix]
  split_ifs with hρ
  · rw [continuousOn_congr (f := fun α ↦ ENNReal.ofReal
      (Real.log ((HermitianMat.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ρ.M ^ α).trace / (α - 1)))]
    · apply (ENNReal.continuous_ofReal).comp_continuousOn
      apply ContinuousOn.div₀
      · apply ContinuousOn.log
        · exact HermitianMat.trace_Continuous.comp_continuousOn
            (continuousOn_Ioo_0_1_aux ρ σ)
        · intro x hx
          exact (sandwiched_trace_pos hρ).ne'
      · fun_prop
      · intro x hx; exact sub_ne_zero.mpr (ne_of_lt hx.2)
    · intro α hα
      dsimp only
      have hα₀ : 0 < α := hα.1
      have hα₁ : α ≠ 1 := ne_of_lt hα.2
      split_ifs
      · norm_cast
      · rw [ENNReal.ofReal, Real.toNNReal_of_nonneg]
        rfl
  · rw [continuousOn_congr (f := fun α ↦ ⊤)]
    · fun_prop
    · intro x hx
      dsimp only
      simp [hx.1]

/-- Continuity at 1: the sandwich relative Rényi entropy is continuous at α = 1. -/
private theorem sandwichedRelRentropy.continuousAt_1 (ρ σ : MState d) :
    ContinuousWithinAt (fun α => D̃_ α(ρ‖σ)) (Set.Ioi 0) 1 := by
  by_cases h : σ.M.ker ≤ ρ.M.ker
  · simp only [ContinuousWithinAt, MState.sandwichedRelRentropy_eq_matrix, dif_pos h, zero_lt_one,
      if_true]
    -- Use the fact that the limit of the real-valued function is the inner product.
    have h_real_limit : Filter.Tendsto (fun α : ℝ => if α = 1 then ⟪ρ.M, ρ.M.log - σ.M.log⟫ else Real.log ((HermitianMat.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ρ.M ^ α).trace / (α - 1)) (nhdsWithin 1 (Set.Ioi 0)) (nhds ⟪ρ.M, ρ.M.log - σ.M.log⟫) := by
      have h_real_limit : Filter.Tendsto (fun α : ℝ => Real.log ((HermitianMat.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ρ.M ^ α).trace / (α - 1)) (nhdsWithin 1 (Set.Ioi 0 \ {1})) (nhds ⟪ρ.M, ρ.M.log - σ.M.log⟫) := by
        exact sandwichedRelRentropy.limit_at_one ρ σ h
      rw [ Metric.tendsto_nhdsWithin_nhds ] at *
      intro ε hε
      rcases h_real_limit ε hε with ⟨δ, hδ, H⟩
      use δ, hδ
      intro x hx₁ hx₂
      by_cases hx₃ : x = 1 <;> simp [*]
    -- Since the real-valued function tends to the inner product, the ENNReal version should also tend to the same limit because the ENNReal conversion is continuous.
    have h_ennreal_limit : Filter.Tendsto (fun α : ℝ => ENNReal.ofReal (if α = 1 then ⟪ρ.M, ρ.M.log - σ.M.log⟫ else Real.log ((HermitianMat.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ρ.M ^ α).trace / (α - 1))) (nhdsWithin 1 (Set.Ioi 0)) (nhds (ENNReal.ofReal ⟪ρ.M, ρ.M.log - σ.M.log⟫)) := by
      exact (ENNReal.tendsto_ofReal h_real_limit).comp Filter.tendsto_id
    convert h_ennreal_limit.congr' _ using 2
    · symm
      apply ENNReal.ofReal_eq_coe_nnreal
    · filter_upwards [self_mem_nhdsWithin] with α (hα : 0 < α)
      simp only [ENNReal.ofReal, ENNReal.coe_inj, hα, ↓reduceDIte]
      exact Real.toNNReal_of_nonneg _
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with α hα
    simp only [MState.sandwichedRelRentropy_eq_matrix, Set.mem_Ioi.mp hα, zero_lt_one, dif_neg h]

@[fun_prop]
theorem sandwichedRelRentropy.continuousOn (ρ σ : MState d) :
    ContinuousOn (fun α => D̃_ α(ρ‖σ)) (Set.Ioi 0) := by
  --If this turns out too hard, we just need `ContinousAt f 1`.
  --If that's still too hard, we really _just_ need that `(𝓝[>] 1).Tendsto f (𝓝 (f 1))`.
  intro α hα
  rcases lt_trichotomy α 1 with hα1 | rfl | hα1
  · have h := sandwichedRelRentropy.continuousOn_Ioo_0_1 ρ σ
    exact (h.continuousAt (Ioo_mem_nhds hα hα1)).continuousWithinAt
  · exact sandwichedRelRentropy.continuousAt_1 ρ σ
  · have h := sandwichedRelRentropy.continuousOn_Ioi_1 ρ σ
    exact (h.continuousAt (Ioi_mem_nhds hα1)).continuousWithinAt

/-- Quantum relative entropy as `Tr[ρ (log ρ - log σ)]` when supports are contained. -/
theorem qRelativeEnt_ker {ρ σ : MState d} (h : σ.M.ker ≤ ρ.M.ker) :
    𝐃(ρ‖σ).toEReal = ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  simp [qRelativeEnt, MState.sandwichedRelRentropy_eq_matrix, h, EReal.coe_nnreal_eq_coe_real]
  rfl

open Classical in
theorem qRelativeEnt_eq_neg_Sᵥₙ_add (ρ σ : MState d) :
    (qRelativeEnt ρ σ).toEReal = -(Sᵥₙ ρ : EReal) +
      if σ.M.ker ≤ ρ.M.ker then (-⟪ρ.M, σ.M.log⟫ : EReal) else (⊤ : EReal) := by
  by_cases h : σ.M.ker ≤ ρ.M.ker
  · simp [h, Sᵥₙ_eq_neg_trace_log, qRelativeEnt_ker, inner_sub_right]
    rw [real_inner_comm, sub_eq_add_neg]
  · simp [h, qRelativeEnt, MState.sandwichedRelRentropy_eq_matrix]

/-- The quantum relative entropy is unchanged by `MState.relabel` -/
@[simp]
theorem qRelativeEnt_relabel (ρ σ : MState d) (e : d₂ ≃ d) :
    𝐃(ρ.relabel e‖σ.relabel e) = 𝐃(ρ‖σ) := by
  simp [qRelativeEnt]

@[simp]
theorem sandwichedRelRentropy_of_unique [Unique d] (ρ σ : MState d) :
    D̃_α(ρ‖σ) = 0 := by
  rcases Subsingleton.allEq ρ default
  rcases Subsingleton.allEq σ default
  simp [MState.sandwichedRelRentropy_eq_matrix]
  intro
  rfl

@[simp]
theorem qRelEntropy_of_unique [Unique d] (ρ σ : MState d) :
    𝐃(ρ‖σ) = 0 := by
  exact sandwichedRelRentropy_of_unique ρ σ

theorem sandwichedRelRentropy_heq_congr
      {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂) (hρ : ρ₁ ≍ ρ₂) (hσ : σ₁ ≍ σ₂) :
    D̃_ α(ρ₁‖σ₁) = D̃_ α(ρ₂‖σ₂) := by
  --Why does this thm need to exist? Why not just `subst d₁` and `simp [heq_eq_eq]`? Well, even though d₁
  --and d₂ are equal, we then end up with two distinct instances of `Fintype d₁` and `DecidableEq d₁`,
  --and ρ₁ and ρ₂ refer to them each and so have different types. And then we'd need to `subst` those away
  --too. This is kind of tedious, so it's better to just have this theorem around.
  rw [heq_iff_exists_eq_cast] at hρ hσ
  obtain ⟨_, rfl⟩ := hρ
  obtain ⟨_, rfl⟩ := hσ
  simp [← MState.relabel_cast _ hd]

theorem sandwichedRelRentropy_congr {α : ℝ}
      {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂)
        (hρ : ρ₁ = ρ₂.relabel (Equiv.cast hd)) (hσ : σ₁ = σ₂.relabel (Equiv.cast hd)) :
    D̃_ α(ρ₁‖σ₁) = D̃_ α(ρ₂‖σ₂) := by
  subst ρ₁ σ₁
  simp

theorem qRelEntropy_heq_congr {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂) (hρ : ρ₁ ≍ ρ₂) (hσ : σ₁ ≍ σ₂) :
    𝐃(ρ₁‖σ₁) = 𝐃(ρ₂‖σ₂) := by
  exact sandwichedRelRentropy_heq_congr hd hρ hσ

/-- Quantum relative entropy when σ has full rank -/
theorem qRelativeEnt_rank {ρ σ : MState d} [σ.M.NonSingular] :
    (𝐃(ρ‖σ) : EReal) = ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  apply qRelativeEnt_ker
  simp [HermitianMat.nonSingular_ker_bot]

section lowerSemicontinuous_1

variable {d : Type*} [Fintype d] [DecidableEq d]

open scoped InnerProductSpace RealInnerProductSpace HermitianMat

private def approxLog (N : ℕ) : ℝ → ℝ := fun t => Real.log (max t (Real.exp (-(N : ℝ))))

private lemma approxLog_continuous (N : ℕ) : Continuous (approxLog N) := by
  have h_cont : Continuous (fun t : ℝ => max t (Real.exp (-N))) :=
    Continuous.max continuous_id continuous_const
  exact Continuous.log h_cont (fun x => ne_of_gt (lt_max_of_lt_right (Real.exp_pos _)))

private lemma approxLog_ge_log_pos {t : ℝ} (ht : 0 < t) (N : ℕ) :
    Real.log t ≤ approxLog N t := by
  unfold approxLog
  exact Real.log_le_log ht (le_max_left _ _)

private lemma continuous_inner_cfc_approxLog (ρ : MState d) (N : ℕ) :
    Continuous (fun σ : MState d => ⟪ρ.M, σ.M.cfc (approxLog N)⟫) := by
  refine Continuous.comp ?_ ?_
  · fun_prop (disch := solve_by_elim)
  · exact (HermitianMat.cfc_continuous (approxLog_continuous N)).comp continuous_induced_dom

private lemma approxLog_tendsto_at_pos {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun N : ℕ => approxLog N t) Filter.atTop (nhds (Real.log t)) := by
  refine' Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [Filter.eventually_gt_atTop ⌈-Real.log t⌉₊] with N hN
  unfold approxLog
  rw [max_eq_left (by rw [← Real.log_le_log_iff (by positivity) (by positivity)]; linarith [Nat.le_ceil (-Real.log t), show (N : ℝ) ≥ ⌈-Real.log t⌉₊ + 1 by exact_mod_cast hN, Real.log_exp (-N)])]

open ComplexOrder in
private lemma inner_cfc_approxLog_ge (ρ σ : MState d) (N : ℕ) (hσ : σ.M.ker ≤ ρ.M.ker) :
    ⟪ρ.M, σ.M.log⟫ ≤ ⟪ρ.M, σ.M.cfc (approxLog N)⟫ := by
  rw [inner_cfc_eq_sum_eigenWeight, show σ.M.log = σ.M.cfc Real.log from rfl, inner_cfc_eq_sum_eigenWeight]
  apply Finset.sum_le_sum
  intro i _
  have hpsd : σ.M.mat.PosSemidef := by
    have h := σ.pos.le
    rwa [HermitianMat.le_iff, sub_zero] at h
  have hei_nn : 0 ≤ σ.M.H.eigenvalues i := hpsd.eigenvalues_nonneg i
  by_cases hei : σ.M.H.eigenvalues i = 0
  · rw [eigenWeight_zero_of_eigenvalue_zero hσ hei, mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right (approxLog_ge_log_pos (lt_of_le_of_ne hei_nn (Ne.symm hei)) N)
      (eigenWeight_nonneg ρ σ i)

open ComplexOrder in
private lemma tendsto_inner_cfc_approxLog (ρ x : MState d) (hx : x.M.ker ≤ ρ.M.ker) :
    Filter.Tendsto (fun N : ℕ => ⟪ρ.M, x.M.cfc (approxLog N)⟫)
      Filter.atTop (nhds ⟪ρ.M, x.M.log⟫) := by
  rw [show x.M.log = x.M.cfc Real.log from rfl, inner_cfc_eq_sum_eigenWeight]
  simp_rw [inner_cfc_eq_sum_eigenWeight]
  apply tendsto_finsetSum
  intro i _
  have hpsd : x.M.mat.PosSemidef := by
    have h := x.pos.le
    rwa [HermitianMat.le_iff, sub_zero] at h
  have hei_nn : 0 ≤ x.M.H.eigenvalues i := hpsd.eigenvalues_nonneg i
  by_cases hei : x.M.H.eigenvalues i = 0
  · simp [eigenWeight_zero_of_eigenvalue_zero hx hei]
  · exact (approxLog_tendsto_at_pos (lt_of_le_of_ne hei_nn (Ne.symm hei))).mul_const _

lemma inner_log_bounded_near (hx : σ.M.ker ≤ ρ.M.ker) {y : ℝ} (hy : ⟪ρ.M, σ.M.log⟫ < y) :
    ∀ᶠ x in nhds σ, x.M.ker ≤ ρ.M.ker → ⟪ρ.M, x.M.log⟫ < y := by
  have h_tendsto := tendsto_inner_cfc_approxLog ρ σ hx
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ⟪ρ.M, σ.M.cfc (approxLog N)⟫ < y := by
    by_contra h
    push Not at h
    exact absurd (lt_of_lt_of_le hy (ge_of_tendsto h_tendsto (Filter.Eventually.of_forall h)))
      (lt_irrefl _)
  have h_cont := continuous_inner_cfc_approxLog ρ N
  have h_lt : ∀ᶠ x in nhds σ, ⟪ρ.M, x.M.cfc (approxLog N)⟫ < y :=
    h_cont.continuousAt.eventually (gt_mem_nhds hN)
  filter_upwards [h_lt] with σ hσ_lt hσ_ker
  exact lt_of_le_of_lt (inner_cfc_approxLog_ge ρ σ N hσ_ker) hσ_lt

end lowerSemicontinuous_1

section lowerSemicontinuous_2

variable {d : Type*} [Fintype d] [DecidableEq d]

open scoped InnerProductSpace RealInnerProductSpace HermitianMat

private lemma eigenWeight_eq_zero_iff (ρ x : MState d) (i : d) :
    eigenWeight ρ x i = 0 ↔ (x.M.H.eigenvectorBasis i : EuclideanSpace ℂ d) ∈ ρ.M.ker := by
  have h_forward : eigenWeight ρ x i = 0 → (x.M.H.eigenvectorBasis i) ∈ ρ.M.ker := by
    unfold eigenWeight
    intro h_zero
    have h_inner : star (x.M.H.eigenvectorBasis i : d → ℂ) ⬝ᵥ (ρ.M.mat.mulVec (x.M.H.eigenvectorBasis i : d → ℂ)) = 0 := by
      convert h_zero using 1
      have h_real : ∀ (v : d → ℂ), star v ⬝ᵥ (ρ.M.mat.mulVec v) = star (star v ⬝ᵥ (ρ.M.mat.mulVec v)) := by
        intro v
        have h_real : star v ⬝ᵥ (ρ.M.mat.mulVec v) = star (star v ⬝ᵥ (ρ.M.mat.mulVec v)) := by
          have h_inner : ∀ (v w : d → ℂ), star v ⬝ᵥ (ρ.M.mat.mulVec w) = star (star w ⬝ᵥ (ρ.M.mat.mulVec v)) := by
            intro v w
            have hH : ∀ a b, star (ρ.M.mat b a) = ρ.M.mat a b := fun a b ↦
              congrFun (congrFun ρ.M.2 a) b
            simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star,
              Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
            rw [hH a b]
            ring
          exact h_inner v v ▸ by simp [ Matrix.mulVec, dotProduct ] ;
        exact h_real.trans ( by simp [] )
      have h_real : ∀ (v : d → ℂ), star v ⬝ᵥ (ρ.M.mat.mulVec v) = RCLike.re (star v ⬝ᵥ (ρ.M.mat.mulVec v)) := by
        intro v; specialize h_real v; rw [ eq_comm ] at h_real; simp_all [ Complex.ext_iff ] ;
        linarith! [ h_real ] ;
      rw [ h_real ] ; norm_cast; simp [Matrix.dotProduct_mulVec ]
    exact HermitianMat.mem_ker_of_inner_mulVec_zero ρ.nonneg _ h_inner
  refine ⟨h_forward, fun h ↦ ?_⟩
  -- Since ρ e_i = 0, we have e_i^* ρ e_i = 0.
  have h_zero : (Matrix.vecMul (star (x.M.H.eigenvectorBasis i : d → ℂ)) ρ.M.mat) ⬝ᵥ (x.M.H.eigenvectorBasis i : d → ℂ) = 0 := by
    have h_zero : ρ.M.mat.mulVec (x.M.H.eigenvectorBasis i : d → ℂ) = 0 := by
      exact congr(WithLp.ofLp $h)
    convert congr_arg ( fun v => star ( x.M.H.eigenvectorBasis i : d → ℂ ) ⬝ᵥ v ) h_zero using 1
    simp [ Matrix.dotProduct_mulVec]
    ring_nf
    simp [ dotProduct ]
  exact congr_arg Complex.re h_zero

private lemma ker_le_iff_eigenWeight_zero (ρ x : MState d) :
    x.M.ker ≤ ρ.M.ker ↔ ∀ i, x.M.H.eigenvalues i = 0 → eigenWeight ρ x i = 0 := by
  constructor
  · exact fun h i ↦ eigenWeight_zero_of_eigenvalue_zero h
  · intro h v hv
    obtain ⟨w, hw⟩ : ∃ w : d → ℂ, v = ∑ i, w i • x.M.H.eigenvectorBasis i := by
      exact ⟨ _, Eq.symm ( x.M.H.eigenvectorBasis.sum_repr v ) ⟩;
    -- Since $v \in \ker(x.M)$, we have $x.M(v) = 0$. Using the eigenvector basis, this implies that for each $i$, if the eigenvalue is non-zero, then $w i = 0$.
    have h_w_zero : ∀ i, x.M.H.eigenvalues i ≠ 0 → w i = 0 := by
      intro i hi
      have h_eigenvalue : x.M.val.mulVec v = ∑ i, (x.M.H.eigenvalues i) • w i • x.M.H.eigenvectorBasis i := by
        have h_eigenvalue : ∀ i, x.M.val.mulVec (x.M.H.eigenvectorBasis i) = x.M.H.eigenvalues i • x.M.H.eigenvectorBasis i := by
          exact fun i => x.M.H.mulVec_eigenvectorBasis i |> fun h => by simpa [ mul_comm ] using h;
        rw [ hw]
        simp only [WithLp.ofLp_sum, WithLp.ofLp_smul]
        rw [Matrix.mulVec_sum ];
        exact Finset.sum_congr rfl fun i _ => by rw [ Matrix.mulVec_smul, h_eigenvalue i, SMulCommClass.smul_comm ]
      have h_eigenvalue_zero : ∑ i, (x.M.H.eigenvalues i) • w i • x.M.H.eigenvectorBasis i = 0 := by
        replace h_eigenvalue := congr(WithLp.toLp 2 $h_eigenvalue)
        simp only [HermitianMat.val_eq_coe, DensityOp.mat_M, WithLp.ofLp_sum, WithLp.ofLp_smul,
          WithLp.toLp_sum, WithLp.toLp_smul, WithLp.toLp_ofLp] at h_eigenvalue
        rw [← h_eigenvalue, ← hv]
        rfl
      have h_eigenvalue_zero : ∀ i, (x.M.H.eigenvalues i) • w i = 0 := by
        intro i
        have h_eigenvalue_zero : (x.M.H.eigenvalues i) • w i = inner ℂ (x.M.H.eigenvectorBasis i) (∑ j, (x.M.H.eigenvalues j) • w j • x.M.H.eigenvectorBasis j) := by
          simp [ orthonormal_iff_ite.mp ( show Orthonormal ℂ ( fun i => x.M.H.eigenvectorBasis i ) from ?_ ) ]
        aesop
      simpa [ hi ] using h_eigenvalue_zero i |> fun h => by simpa [ hi ] using h;
    simp_all [ eigenWeight_eq_zero_iff ];
    exact Submodule.sum_mem _ fun i _ => if hi : x.M.H.eigenvalues i = 0 then by simpa [ hi, h_w_zero i ] using Submodule.smul_mem _ ( w i ) ( h i hi ) else by simp [ h_w_zero i hi ] ;

private lemma neg_ker_exists_eigenWeight_pos (ρ x : MState d) (hx : ¬(x.M.ker ≤ ρ.M.ker)) :
    ∃ i, x.M.H.eigenvalues i = 0 ∧ 0 < eigenWeight ρ x i := by
  -- By `ker_le_iff_eigenWeight_zero`, ¬(x.M.ker ≤ ρ.M.ker) iff ∃ i, eigenvalue_i = 0 ∧ eigenWeight ≠ 0. Use this fact.
  have h_eigenWeight_ne_zero : ∃ i, x.M.H.eigenvalues i = 0 ∧ eigenWeight ρ x i ≠ 0 := by
    exact Classical.not_forall_not.1 fun h => hx <| by simpa using ker_le_iff_eigenWeight_zero ρ x |>.2 fun i hi => Classical.not_not.1 fun hi' => h i ⟨ hi, hi' ⟩ ;
  exact h_eigenWeight_ne_zero.imp fun i hi => ⟨ hi.1, lt_of_le_of_ne ( eigenWeight_nonneg ρ x i ) hi.2.symm ⟩

private lemma approxLog_at_zero (N : ℕ) : approxLog N 0 = -(N : ℝ) := by
  simp [approxLog, max_eq_right (Real.exp_pos (-N)).le]

private lemma inner_cfc_approxLog_tendsto_bot (ρ x : MState d) (hx : ¬(x.M.ker ≤ ρ.M.ker)) :
    Filter.Tendsto (fun N : ℕ => ⟪ρ.M, x.M.cfc (approxLog N)⟫) Filter.atTop Filter.atBot := by
  have h_split_sum : Filter.Tendsto (fun N : ℕ => ∑ i ∈ Finset.univ.filter (fun i => x.M.H.eigenvalues i = 0), approxLog N (x.M.H.eigenvalues i) * eigenWeight ρ x i) Filter.atTop Filter.atBot := by
    have h_split_sum : Filter.Tendsto (fun N : ℕ => ∑ i ∈ Finset.univ.filter (fun i => x.M.H.eigenvalues i = 0), (-↑N) * eigenWeight ρ x i) Filter.atTop Filter.atBot := by
      have h_split_sum : ∑ i ∈ Finset.univ.filter (fun i => x.M.H.eigenvalues i = 0), eigenWeight ρ x i > 0 := by
        obtain ⟨ i, hi, hi' ⟩ := neg_ker_exists_eigenWeight_pos ρ x hx; exact lt_of_lt_of_le hi' ( Finset.single_le_sum ( fun i _ => eigenWeight_nonneg ρ x i ) ( by aesop ) ) ;
      simp_rw [← Finset.mul_sum, neg_mul]
      exact Filter.tendsto_neg_atTop_atBot.comp
        (tendsto_natCast_atTop_atTop.atTop_mul_const h_split_sum)
    apply h_split_sum.congr'
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ show approxLog N ( x.M.H.eigenvalues i ) = -↑N from by rw [ show x.M.H.eigenvalues i = 0 from Finset.mem_filter.mp hi |>.2 ] ; exact approxLog_at_zero N ] ;
  convert h_split_sum.atBot_add ( show Filter.Tendsto ( fun N : ℕ => ∑ i ∈ Finset.univ.filter ( fun i => x.M.H.eigenvalues i ≠ 0 ), approxLog N ( x.M.H.eigenvalues i ) * eigenWeight ρ x i ) Filter.atTop ( nhds ( ∑ i ∈ Finset.univ.filter ( fun i => x.M.H.eigenvalues i ≠ 0 ), Real.log ( x.M.H.eigenvalues i ) * eigenWeight ρ x i ) ) from ?_ ) using 2;
  · rw [ inner_cfc_eq_sum_eigenWeight, Finset.sum_filter_add_sum_filter_not ];
  · apply tendsto_finsetSum
    intro i hi
    exact Filter.Tendsto.mul ((approxLog_tendsto_at_pos ( show 0 < x.M.H.eigenvalues i from lt_of_le_of_ne (x.eigenvalue_nonneg i) (Ne.symm (by aesop))))) tendsto_const_nhds

end lowerSemicontinuous_2

open Classical in
theorem qRelativeEnt_lowerSemicontinuous_2 (ρ x : MState d) (hx : ¬(x.M.ker ≤ ρ.M.ker)) (y : ENNReal) (hy : y < ⊤) :
    ∀ᶠ (x' : MState d) in nhds x,
      y < (if x'.M.ker ≤ ρ.M.ker then ⟪ρ.M, ρ.M.log - x'.M.log⟫ else ⊤ : EReal) := by
  -- Since $y < \top$, we can choose a neighborhood around $x$ where the inner product is less than $y$.
  have h_inner_lt_y : ∀ᶠ x' in nhds x, x'.M.ker ≤ ρ.M.ker → ⟪ρ.M, ρ.M.log - x'.M.log⟫ > y.toReal := by
    have h_inner_lt_y : Filter.Tendsto (fun N : ℕ => ⟪ρ.M, ρ.M.log - x.M.cfc (approxLog N)⟫) Filter.atTop Filter.atTop := by
      have h_inner_lt_y : Filter.Tendsto (fun N : ℕ => ⟪ρ.M, ρ.M.log⟫ - ⟪ρ.M, x.M.cfc (approxLog N)⟫) Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.add_atTop tendsto_const_nhds ( Filter.tendsto_neg_atBot_atTop.comp ( inner_cfc_approxLog_tendsto_bot ρ x hx ) ) |> Filter.Tendsto.congr ( by aesop ) ;
      convert h_inner_lt_y using 1
      ext1 N
      simp [inner_sub_right]
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ⟪ρ.M, ρ.M.log - x.M.cfc (approxLog N)⟫ > y.toReal := by
      exact (h_inner_lt_y.eventually_gt_atTop _ ).exists
    have h_cont : Continuous (fun σ : MState d => ⟪ρ.M, ρ.M.log - σ.M.cfc (approxLog N)⟫) := by
      simp only [inner_sub_right]
      exact continuous_const.sub (continuous_inner_cfc_approxLog ρ N)
    have h_cont : ∀ᶠ x' in nhds x, ⟪ρ.M, ρ.M.log - x'.M.cfc (approxLog N)⟫ > y.toReal := by
      exact h_cont.continuousAt.eventually ( lt_mem_nhds hN ) |> fun h => h.mono fun x' hx' => hx' |> fun hx'' => by simpa using hx'';
    filter_upwards [h_cont] with x' hx' hx''
    apply lt_of_lt_of_le hx'
    have h_inner_le : ⟪ρ.M, x'.M.log⟫ ≤ ⟪ρ.M, x'.M.cfc (approxLog N)⟫ := by
      exact inner_cfc_approxLog_ge ρ x' N hx''
    rw [inner_sub_right, inner_sub_right]
    exact sub_le_sub_left h_inner_le _
  filter_upwards [ h_inner_lt_y ] with x' hx';
  split_ifs <;> simp_all [ ENNReal.toReal ];
  · convert ENNReal.ofReal_lt_ofReal_iff (show 0 < ⟪ρ.M, ρ.M.log - x'.M.log⟫ from lt_of_le_of_lt (by positivity) hx' ) |>.2 hx' using 1
    cases y
    · simp at hy
    simp only [ENNReal.ofReal, ENNReal.toNNReal_coe, Real.toNNReal_coe, ENNReal.coe_lt_coe]
    rw [← NNReal.coe_lt_coe, Real.toNNReal_of_nonneg (le_trans (by positivity) hx'.le)]
    simp [← ENNReal.ofReal_coe_nnreal]
  · rw [lt_top_iff_ne_top, ne_eq] at hy ⊢
    rwa [EReal.coe_ennreal_eq_top_iff]

/-
Relative entropy is lower semicontinuous (in each argument, actually, but we only need in the
latter here). Will need the fact that all the cfc / eigenvalue stuff is continuous, plus
carefully handling what happens with the kernel subspace, which will make this a pain.
-/
@[fun_prop]
theorem qRelativeEnt.lowerSemicontinuous (ρ : MState d) : LowerSemicontinuous fun σ => 𝐃(ρ‖σ) := by
  simp_rw [qRelativeEnt, MState.sandwichedRelRentropy_eq_matrix, if_true, lowerSemicontinuous_iff]
  simp only [zero_lt_one, ↓reduceDIte]
  intro x
  by_cases hx : x.M.ker ≤ ρ.M.ker
  · intro y hy
    obtain ⟨y', hy'⟩ : ∃ y' : ℝ, y < ENNReal.ofReal y' ∧ y' < ⟪ρ.M, ρ.M.log - x.M.log⟫ := by
      rcases ENNReal.lt_iff_exists_real_btwn.mp hy with ⟨ y', hy₁, hy₂ ⟩;
      rw [ ENNReal.ofReal_lt_iff_lt_toReal ] at hy₂ <;> aesop;
    simp only [↓reduceDIte, inner_sub_right, hx] at hy hy' ⊢
    have := inner_log_bounded_near hx (y := ⟪ρ.M, ρ.M.log⟫ - y') (by linarith)
    filter_upwards [this] with σ hσ
    split
    · simp_all only [ENNReal.ofReal, forall_const]
      apply lt_of_lt_of_le hy'.1
      refine mod_cast max_le (a := y') (b := 0) (c := ⟪ρ.M, ρ.M.log⟫ - ⟪ρ.M, σ.M.log⟫) ?_ ?_
      · linarith
      · linarith [ show 0 ≤ y' from le_of_not_gt fun h => by norm_num [ Real.toNNReal_of_nonpos h.le ] at hy' ]
    · exact hy'.1.trans_le (by simp)
  · intro y hy
    simp only [hx, ↓reduceDIte] at hy ⊢
    have h₂ := qRelativeEnt_lowerSemicontinuous_2 ρ x hx y hy
    filter_upwards [h₂] with x' hx'
    split_ifs with h₁ junk
    · simp_all only [gt_iff_lt, ← EReal.coe_ennreal_lt_coe_ennreal_iff, EReal.coe_ennreal_top,
      ↓reduceIte]
      exact hx'
    · simp at junk
    · exact hy

@[simp]
theorem qRelEntropy_self (ρ : MState d) : 𝐃(ρ‖ρ) = 0 := by
  simp [qRelativeEnt]

@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem qRelativeEnt_ne_top {ρ σ : MState d} [σ.M.NonSingular] : 𝐃(ρ‖σ) ≠ ⊤ := by
  rw [qRelativeEnt]
  finiteness

section mutualInfo

open HermitianMat

private lemma inner_kerProj_kron_one (ρ : MState (dA × dB)) :
    ⟪ρ.M, ρ.traceRight.M.kerProj ⊗ₖ (1 : HermitianMat dB ℂ)⟫ = 0 := by
  rw [inner_comm, inner_kron_one, ← MState.traceRight_M,
    eq_sub_of_add_eq (kerProj_add_supportProj ρ.traceRight.M), inner_sub_left, one_inner,
    inner_comm, inner_supportProj_self, sub_self]

private lemma inner_one_kron_kerProj (ρ : MState (dA × dB)) :
    ⟪ρ.M, (1 : HermitianMat dA ℂ) ⊗ₖ ρ.traceLeft.M.kerProj⟫ = 0 := by
  rw [inner_comm, inner_one_kron, ← MState.traceLeft_M,
    eq_sub_of_add_eq (kerProj_add_supportProj ρ.traceLeft.M), inner_sub_left, one_inner,
    inner_comm, inner_supportProj_self, sub_self]

private lemma mul_kerProj_kron_one (ρ : MState (dA × dB)) :
    ρ.M.mat * (ρ.traceRight.M.kerProj ⊗ₖ (1 : HermitianMat dB ℂ)).mat = 0 := by
  refine mul_eq_zero_of_inner_eq_zero ρ.nonneg ?_ (inner_kerProj_kron_one ρ)
  rw [kronecker_mat, mat_one, ← Matrix.mul_kronecker_mul, one_mul, kerProj_sq]

private lemma mul_one_kron_kerProj (ρ : MState (dA × dB)) :
    ρ.M.mat * ((1 : HermitianMat dA ℂ) ⊗ₖ ρ.traceLeft.M.kerProj).mat = 0 := by
  refine mul_eq_zero_of_inner_eq_zero ρ.nonneg ?_ (inner_one_kron_kerProj ρ)
  rw [kronecker_mat, mat_one, ← Matrix.mul_kronecker_mul, one_mul, kerProj_sq]

private lemma mul_kerProj_kron (ρ : MState (dA × dB)) (Y : HermitianMat dB ℂ) :
    ρ.M.mat * (ρ.traceRight.M.kerProj ⊗ₖ Y).mat = 0 := by
  have h : (ρ.traceRight.M.kerProj ⊗ₖ Y).mat
      = (ρ.traceRight.M.kerProj ⊗ₖ (1 : HermitianMat dB ℂ)).mat
        * ((1 : HermitianMat dA ℂ) ⊗ₖ Y).mat := by
    rw [kronecker_mat, kronecker_mat, kronecker_mat, mat_one, mat_one, ← Matrix.mul_kronecker_mul,
      mul_one, one_mul]
  rw [h, ← mul_assoc, mul_kerProj_kron_one, Matrix.zero_mul]

private lemma mul_kron_kerProj (ρ : MState (dA × dB)) (X : HermitianMat dA ℂ) :
    ρ.M.mat * (X ⊗ₖ ρ.traceLeft.M.kerProj).mat = 0 := by
  have h : (X ⊗ₖ ρ.traceLeft.M.kerProj).mat
      = ((1 : HermitianMat dA ℂ) ⊗ₖ ρ.traceLeft.M.kerProj).mat
        * (X ⊗ₖ (1 : HermitianMat dB ℂ)).mat := by
    rw [kronecker_mat, kronecker_mat, kronecker_mat, mat_one, mat_one, ← Matrix.mul_kronecker_mul,
      mul_one, one_mul]
  rw [h, ← mul_assoc, mul_one_kron_kerProj, Matrix.zero_mul]

/-- A bipartite state is unchanged by projecting onto the support of the product of its
marginals. -/
private lemma mul_supportProj_prod (ρ : MState (dA × dB)) :
    ρ.M.mat * (ρ.traceRight ⊗ᴹ ρ.traceLeft).M.supportProj.mat = ρ.M.mat := by
  have hA : ρ.traceRight.M.supportProj = 1 - ρ.traceRight.M.kerProj :=
    eq_sub_of_add_eq' (kerProj_add_supportProj ρ.traceRight.M)
  have hB : ρ.traceLeft.M.supportProj = 1 - ρ.traceLeft.M.kerProj :=
    eq_sub_of_add_eq' (kerProj_add_supportProj ρ.traceLeft.M)
  rw [MState.prod_M, supportProj_kron, hA, hB, sub_kronecker, kronecker_sub, kronecker_sub]
  simp only [mat_sub, Matrix.mul_sub, mul_kron_kerProj, mul_kerProj_kron]
  simp

private lemma ker_prod_le_ker (ρ : MState (dA × dB)) :
    (ρ.traceRight ⊗ᴹ ρ.traceLeft).M.ker ≤ ρ.M.ker := by
  intro v hv
  have hPv := (mem_ker_iff_mulVec_zero _ v).mp (ker_le_ker_supportProj _ hv)
  rw [mem_ker_iff_mulVec_zero] at hv ⊢
  calc ρ.M.mat.mulVec v
      = (ρ.M.mat * (ρ.traceRight ⊗ᴹ ρ.traceLeft).M.supportProj.mat).mulVec v := by
        rw [mul_supportProj_prod]
    _ = ρ.M.mat.mulVec ((ρ.traceRight ⊗ᴹ ρ.traceLeft).M.supportProj.mat.mulVec v) := by
        rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hPv, Matrix.mulVec_zero]

private lemma inner_log_prod (ρ : MState (dA × dB)) :
    ⟪ρ.M, (ρ.traceRight ⊗ᴹ ρ.traceLeft).M.log⟫ = -Sᵥₙ ρ.traceRight - Sᵥₙ ρ.traceLeft := by
  rw [MState.prod_M, log_kron_with_proj, inner_add_right]
  have h1 : ⟪ρ.M, ρ.traceRight.M.log ⊗ₖ ρ.traceLeft.M.supportProj⟫ = -Sᵥₙ ρ.traceRight := by
    rw [eq_sub_of_add_eq' (kerProj_add_supportProj ρ.traceLeft.M), kronecker_sub, inner_sub_right,
      inner_eq_zero_of_mul_eq_zero (mul_kron_kerProj ρ _), sub_zero, inner_comm, inner_kron_one,
      ← MState.traceRight_M, Sᵥₙ_eq_neg_trace_log, neg_neg]
  have h2 : ⟪ρ.M, ρ.traceRight.M.supportProj ⊗ₖ ρ.traceLeft.M.log⟫ = -Sᵥₙ ρ.traceLeft := by
    rw [eq_sub_of_add_eq' (kerProj_add_supportProj ρ.traceRight.M), sub_kronecker, inner_sub_right,
      inner_eq_zero_of_mul_eq_zero (mul_kerProj_kron ρ _), sub_zero, inner_comm, inner_one_kron,
      ← MState.traceLeft_M, Sᵥₙ_eq_neg_trace_log, neg_neg]
  rw [h1, h2]
  ring

/-- `I(A:B) = 𝐃(ρᴬᴮ‖ρᴬ ⊗ ρᴮ)` -/
theorem qMutualInfo_as_qRelativeEnt (ρ : MState (dA × dB)) :
    qMutualInfo ρ = (𝐃(ρ‖ρ.traceRight ⊗ᴹ ρ.traceLeft) : EReal) := by
  rw [qRelativeEnt_ker (ker_prod_le_ker ρ), inner_sub_right, inner_log_prod]
  rw [show ⟪ρ.M, ρ.M.log⟫ = -Sᵥₙ ρ by rw [Sᵥₙ_eq_neg_trace_log, neg_neg, inner_comm]]
  rw [qMutualInfo]
  norm_cast
  ring

end mutualInfo

/-
Helper: If σ₂ ≤ α • σ₁ for density matrices, then α > 0.
   Proof: σ₂ has trace 1, so it's nonzero. If α ≤ 0, then α • σ₁ ≤ 0 (since σ₁ ≥ 0),
   but σ₂ ≤ α • σ₁ ≤ 0 with σ₂ ≥ 0 forces σ₂ = 0, contradicting trace = 1.
-/
private lemma pos_of_MState_le_smul {σ₁ σ₂ : MState d} (hσ : σ₂.M ≤ α • σ₁.M) : 0 < α := by
  by_contra! h_nonpos
  apply σ₂.pos.ne'
  apply le_antisymm
  · convert ← hσ using 1
    apply le_antisymm
    · exact smul_nonpos_of_nonpos_of_nonneg h_nonpos ( by positivity)
    · exact hσ.trans' ( by positivity );
  · positivity

open ComplexOrder in
private lemma HermitianMat.inner_log_mono_of_posDef_of_le {A B C : HermitianMat d 𝕜}
    (hC : 0 ≤ C) (hA : A.mat.PosDef) (hAB : A ≤ B) :
    ⟪C, A.log⟫ ≤ ⟪C, B.log⟫ := by
  exact inner_mono hC (log_mono hA hAB)

open ComplexOrder in
private lemma posDef_add_eps {A : HermitianMat d ℂ} (hA : 0 ≤ A) {ε : ℝ} (hε : 0 < ε) :
    (A + ε • 1).mat.PosDef := by
  rw [HermitianMat.zero_le_iff] at hA
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · exact HermitianMat.H _
  · intro x hx_ne_zero
    have h_inner : star x ⬝ᵥ (A.val.mulVec x) ≥ 0 := by
      simp [hA]
    have h_eps : star x ⬝ᵥ (ε • 1 : Matrix d d ℂ).mulVec x = ε * star x ⬝ᵥ x := by
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm, Matrix.one_apply]
    have h_pos : 0 < ε * star x ⬝ᵥ x := by
      simp [*]
    simpa [Matrix.add_mulVec, h_eps] using add_pos_of_nonneg_of_pos h_inner h_pos

private lemma log_add_eps_eq_cfc (A : HermitianMat d 𝕜) (ε : ℝ) :
    (A + ε • 1).log = A.cfc (Real.log <| · + ε) := by
  have h_cfc : A + ε • 1 = A.cfc (· + ε) := by
    have h_add : A.cfc (fun u => u + ε) = A.cfc (fun u => u) + A.cfc (fun _ => ε) := by
      exact A.cfc_add_apply _ _
    simp only [HermitianMat.cfc_id', HermitianMat.cfc_const, h_add]
  rw [h_cfc, HermitianMat.log, A.cfc_comp_apply]

private lemma inner_cfc_eq_sum (A C : HermitianMat d 𝕜) (f : ℝ → ℝ) :
    ⟪C, A.cfc f⟫ = ∑ i, f (A.H.eigenvalues i) *
      RCLike.re ((C.mat * (A.H.eigenvectorUnitary.val * Matrix.single i i 1 * A.H.eigenvectorUnitary.val.conjTranspose)).trace) := by
  apply congr(RCLike.re ((C.val * $(A.cfc_toMat_eq_sum_smul_proj f)).trace)).trans
  simp only [HermitianMat.val_eq_coe, Matrix.mul_sum, Algebra.mul_smul_comm, Matrix.trace_sum,
    Matrix.trace_smul, RCLike.real_smul_eq_coe_mul, map_sum, RCLike.mul_re,
    RCLike.ofReal_re, RCLike.ofReal_im, zero_mul, sub_zero]

private lemma eigenproj_coeff_zero_of_ker_le {A C : HermitianMat d 𝕜}
    (hker : A.ker ≤ C.ker) {i : d} (hi : A.H.eigenvalues i = 0) :
    RCLike.re ((C.mat * (A.H.eigenvectorUnitary.val * Matrix.single i i 1 * A.H.eigenvectorUnitary.val.conjTranspose)).trace) = 0 := by
  have h_eigenvector_in_ker_C : C.mat.mulVec (A.H.eigenvectorBasis i) = 0 := by
    have h_eigenvector_in_ker : (A.H.eigenvectorBasis i) ∈ LinearMap.ker A.lin.toLinearMap := by
      have := congr(WithLp.toLp 2 $(A.H.mulVec_eigenvectorBasis i))
      simp [hi] at this
      exact congr(WithLp.toLp 2 $this)
    specialize hker h_eigenvector_in_ker
    exact congr(WithLp.ofLp $hker)
  have h_trace_zero : (C.mat * (A.H.eigenvectorUnitary.val * Matrix.single i i 1 * A.H.eigenvectorUnitary.val.conjTranspose)).trace = (star (A.H.eigenvectorBasis i)) ⬝ᵥ (C.mat.mulVec (A.H.eigenvectorBasis i)) := by
    simp [Matrix.trace, Matrix.mulVec, dotProduct]
    simp [Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply]
    simp [Finset.sum_ite, Finset.filter_eq, Finset.filter_and, mul_comm, mul_left_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.sum_eq_single i]
    · simp_all only [Finset.mem_univ, ↓reduceIte, Finset.inter_univ, Finset.sum_singleton]
      rw [mul_assoc]
    · intro b a a_1
      simp_all only [Finset.mem_univ, ne_eq]
      split <;> simp_all only [not_true_eq_false, Finset.inter_empty, Finset.sum_empty]
    · intro a
      simp_all only [Finset.mem_univ, not_true_eq_false]
  simp [h_eigenvector_in_ker_C, h_trace_zero]

open scoped Topology in
private lemma inner_log_shift_tendsto {A C : HermitianMat d 𝕜} (hker : A.ker ≤ C.ker) :
    (𝓝[>] 0).Tendsto (fun (ε : ℝ) ↦ ⟪C, (A + ε • 1).log⟫) (𝓝 ⟪C, A.log⟫) := by
  simp only [log_add_eps_eq_cfc A]
  simp only [inner_cfc_eq_sum, HermitianMat.log]
  refine tendsto_finsetSum _ fun i _ ↦ ?_
  by_cases hi : A.H.eigenvalues i = 0
  · simp [eigenproj_coeff_zero_of_ker_le hker hi]
  · have h := log_add_eps_eq_cfc A
    simp_rw [HermitianMat.log] at h
    refine Filter.Tendsto.mul ?_ tendsto_const_nhds
    conv in 𝓝 (Real.log _) => rw [← add_zero (A.H.eigenvalues i)]
    apply (tendsto_const_nhds.add (Filter.tendsto_id.mono_left inf_le_left)).log
    rwa [add_zero]

private lemma HermitianMat.inner_log_mono_of_psd_of_le {A B C : HermitianMat d ℂ}
    (hA : 0 ≤ A) (hAB : A ≤ B) (hC : 0 ≤ C) (hker : A.ker ≤ C.ker) :
    ⟪C, A.log⟫ ≤ ⟪C, B.log⟫ := by
  open scoped Topology in
  have h_eventually : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ⟪C, (A + ε • 1).log⟫ ≤ ⟪C, (B + ε • 1).log⟫ := by
    refine eventually_nhdsWithin_of_forall fun ε hε ↦ ?_
    exact inner_log_mono_of_posDef_of_le hC (posDef_add_eps hA hε) (add_le_add_left hAB _)
  refine le_of_tendsto_of_tendsto ?_ ?_ h_eventually
  · exact inner_log_shift_tendsto hker
  · apply inner_log_shift_tendsto
    exact (ker_antitone hA hAB).trans hker

private lemma HermitianMat.inner_log_sub_le_log_alpha (ρ : MState d) {σ₁ σ₂ : MState d} {α : ℝ}
    (hσ : σ₂.M ≤ α • σ₁.M)
    (hker₁ : σ₁.M.ker ≤ ρ.M.ker) (hker₂ : σ₂.M.ker ≤ ρ.M.ker) :
    ⟪ρ.M, σ₂.M.log - σ₁.M.log⟫ ≤ Real.log α := by
  have h_log_mono : ⟪ρ.M, σ₂.M.log - (α • σ₁.M).log⟫ ≤ 0 := by
    have h_log_mono : ⟪ρ.M, σ₂.M.log⟫ ≤ ⟪ρ.M, (α • σ₁.M).log⟫ := by
      exact inner_log_mono_of_psd_of_le σ₂.nonneg hσ ρ.nonneg hker₂
    simpa [inner_sub_right] using sub_nonpos_of_le h_log_mono
  have h_log_smul : (α • σ₁.M).log = (Real.log α) • σ₁.M.supportProj + σ₁.M.log := by
    apply HermitianMat.log_smul_of_pos
    rintro rfl
    simpa using pos_of_MState_le_smul hσ
  rw [h_log_smul] at h_log_mono
  simp only [add_comm, sub_eq_add_neg, neg_add_rev] at h_log_mono h_log_smul ⊢
  have h_inner_support : ⟪ρ.M, σ₁.M.supportProj⟫ = 1 := by
    rw [HermitianMat.inner_supportProj_of_ker_le hker₁, ρ.tr]
  simp_all [← add_assoc, inner_add_right, inner_smul_right]

theorem qRelEntropy_le_add_of_le_smul (ρ : MState d) {σ₁ σ₂ : MState d} (hσ : σ₂.M ≤ α • σ₁.M) :
    𝐃(ρ‖σ₁) ≤ 𝐃(ρ‖σ₂) + ENNReal.ofReal (Real.log α)
    := by
  -- Consider two cases: when the kernel of σ₂ is contained in the kernel of ρ and when it is not.
  by_cases hker : σ₂.M.ker ≤ ρ.M.ker;
  · by_cases hker₁ : σ₁.M.ker ≤ ρ.M.ker;
    · -- Using `qRelativeEnt_ker` to get D(ρ‖σ₁).toEReal = ⟪ρ.M, ρ.M.log - σ₁.M.log⟫
      have h_log : ⟪ρ.M, σ₂.M.log - σ₁.M.log⟫ ≤ Real.log α := by
        apply HermitianMat.inner_log_sub_le_log_alpha
        · exact hσ
        · exact hker₁
        · exact hker
      have h_final : (qRelativeEnt ρ σ₁).toEReal ≤ (qRelativeEnt ρ σ₂).toEReal + ENNReal.toEReal (ENNReal.ofReal (Real.log α)) := by
        simp_all only [qRelativeEnt_ker, inner_sub_right, tsub_le_iff_right, EReal.coe_sub, EReal.coe_ennreal_ofReal]
        cases max_cases (Real.log α) 0
        <;> simp only [sup_of_le_left, *]
        <;> norm_cast at *
        <;> linarith [Real.log_nonneg one_le_two]
      have h_final' : qRelativeEnt ρ σ₁ ≤ qRelativeEnt ρ σ₂ + ENNReal.ofReal (Real.log α) := by
        exact_mod_cast h_final
      exact h_final'
    · by_contra h_contra;
      have hker_le : σ₁.M.ker ≤ σ₂.M.ker := by
        apply_rules [ HermitianMat.ker_le_of_le_smul, hσ ];
        · rintro rfl
          apply σ₂.pos.not_ge
          simpa using hσ
        · positivity
      exact hker₁ (hker_le.trans hker)
  · simp [hker, MState.sandwichedRelRentropy_eq_matrix, qRelativeEnt]

theorem qRelativeEnt_op_le {ρ σ : MState d} (h : ρ.M ≤ α • σ.M) :
    𝐃(ρ‖σ) ≤ .ofReal (Real.log α) := by
  simpa using qRelEntropy_le_add_of_le_smul ρ h

/-! ## Joint convexity

Joint convexity of the relative entropy follows from monotonicity under the partial trace, which
in turn is the operator strong subadditivity inequality `inner_log_traceRight_le` integrated
against `ρ`. Given the partial trace bound, one forms the *flag state*
`p ρ₁ ⊗ |0⟩⟨0| + (1-p) ρ₂ ⊗ |1⟩⟨1|` on `d × Fin 2`, whose right marginal is the mixture
`p [ρ₁ ↔ ρ₂]` and whose relative entropy against the corresponding flag state for the `σᵢ` is
exactly the convex combination `p 𝐃(ρ₁‖σ₁) + (1-p) 𝐃(ρ₂‖σ₂)`, because relative entropy of
block-diagonal states decomposes blockwise. -/

open scoped Topology in
private theorem tendsto_mul_const_nhdsGT {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun ε : ℝ ↦ ε * c) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Filter.Tendsto (fun ε : ℝ ↦ ε * c) (𝓝 0) (𝓝 (0 * c)) :=
      (continuous_mul_const c).tendsto 0
    rw [zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact mul_pos hε hc

open scoped Topology in
/-- Monotonicity of the quantum relative entropy under the partial trace. -/
theorem qRelativeEnt_traceRight_le (ρ σ : MState (dA × dB)) :
    𝐃(ρ.traceRight‖σ.traceRight) ≤ 𝐃(ρ‖σ) := by
  by_cases hker : σ.M.ker ≤ ρ.M.ker
  swap
  · rw [qRelativeEnt_eq_top hker]
    exact le_top
  have hkerR : σ.traceRight.M.ker ≤ ρ.traceRight.M.ker := by
    rw [MState.traceRight_M, MState.traceRight_M]
    exact HermitianMat.ker_traceRight_le σ.nonneg hker
  obtain ⟨_, _⟩ := nonempty_prod.mp ρ.nonempty
  have hcard : (0 : ℝ) < Fintype.card dB := by
    exact_mod_cast Fintype.card_pos
  have key : ⟪ρ.M, σ.M.log⟫ + Sᵥₙ ρ ≤ ⟪ρ.traceRight.M, σ.traceRight.M.log⟫ + Sᵥₙ ρ.traceRight := by
    have h_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ⟪ρ.M, (σ.M + ε • 1).log⟫ + Sᵥₙ ρ
          ≤ ⟪ρ.traceRight.M, (σ.traceRight.M + (ε * (Fintype.card dB : ℝ)) • 1).log⟫
              + Sᵥₙ ρ.traceRight := by
      refine eventually_nhdsWithin_of_forall fun ε hε ↦ ?_
      have h := inner_log_traceRight_le ρ (posDef_add_eps σ.nonneg hε)
      rwa [HermitianMat.traceRight_add_smul_one, ← MState.traceRight_M] at h
    refine le_of_tendsto_of_tendsto ?_ ?_ h_ev
    · exact (inner_log_shift_tendsto hker).add tendsto_const_nhds
    · exact ((inner_log_shift_tendsto hkerR).comp
        (tendsto_mul_const_nhdsGT hcard)).add tendsto_const_nhds
  rw [← EReal.coe_ennreal_le_coe_ennreal_iff, qRelativeEnt_ker hkerR, qRelativeEnt_ker hker,
    EReal.coe_le_coe_iff, HermitianMat.inner_sub_left, HermitianMat.inner_sub_left]
  rw [Sᵥₙ_eq_neg_trace_log ρ, Sᵥₙ_eq_neg_trace_log ρ.traceRight,
    HermitianMat.inner_comm ρ.M.log, HermitianMat.inner_comm ρ.traceRight.M.log] at key
  linarith

/-- The inner product of two block-diagonal matrices is the sum of the blockwise inner products. -/
theorem HermitianMat.inner_sum_kron_basisProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ι → HermitianMat d ℂ) :
    ⟪∑ i, A i ⊗ₖ HermitianMat.basisProj ℂ i, ∑ j, B j ⊗ₖ HermitianMat.basisProj ℂ j⟫
      = ∑ i, ⟪A i, B i⟫ := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [HermitianMat.inner_kron, HermitianMat.inner_basisProj, if_pos rfl, mul_one]
  · intro j _ hj
    rw [HermitianMat.inner_kron, HermitianMat.inner_basisProj, if_neg (Ne.symm hj), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The relative entropy inner product of two block-diagonal states decomposes as the
weighted sum of the blockwise relative entropies. -/
theorem inner_blocks_log_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) (hc : ∀ i, c i ≠ 0) (A B : ι → HermitianMat d ℂ) (hA : ∀ i, (A i).trace = 1)
    (hker : ∀ i, (B i).ker ≤ (A i).ker) :
    ⟪∑ i, (c i • A i) ⊗ₖ HermitianMat.basisProj ℂ i,
        (∑ i, (c i • A i) ⊗ₖ HermitianMat.basisProj ℂ i).log
          - (∑ i, (c i • B i) ⊗ₖ HermitianMat.basisProj ℂ i).log⟫
      = ∑ i, c i * ⟪A i, (A i).log - (B i).log⟫ := by
  rw [HermitianMat.inner_sub_left, HermitianMat.log_sum_kron_basisProj,
    HermitianMat.log_sum_kron_basisProj, HermitianMat.inner_sum_kron_basisProj,
    HermitianMat.inner_sum_kron_basisProj, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [HermitianMat.log_smul_of_pos (A i) (hc i), HermitianMat.log_smul_of_pos (B i) (hc i),
    HermitianMat.inner_smul_left, HermitianMat.inner_smul_left, HermitianMat.inner_add_right,
    HermitianMat.inner_add_right, HermitianMat.inner_smul_right, HermitianMat.inner_smul_right,
    HermitianMat.inner_supportProj_self, HermitianMat.inner_supportProj_of_ker_le (hker i),
    HermitianMat.inner_sub_left, hA i]
  ring

private theorem qRelativeEnt_ne_top_of_ker {ρ σ : MState d} (h : σ.M.ker ≤ ρ.M.ker) :
    𝐃(ρ‖σ) ≠ ⊤ := by
  intro htop
  have h2 := qRelativeEnt_ker h
  rw [htop] at h2
  simp at h2

/-- The quantum relative entropy is finite exactly when the support condition
`σ.M.ker ≤ ρ.M.ker` holds. -/
theorem qRelativeEnt_ne_top_iff {ρ σ : MState d} : 𝐃(ρ‖σ) ≠ ⊤ ↔ σ.M.ker ≤ ρ.M.ker := by
  refine ⟨fun h ↦ ?_, qRelativeEnt_ne_top_of_ker⟩
  by_contra hk
  exact h (qRelativeEnt_eq_top hk)

/-- The quantum relative entropy is `⊤` exactly when the support condition fails. -/
theorem qRelativeEnt_eq_top_iff {ρ σ : MState d} : 𝐃(ρ‖σ) = ⊤ ↔ ¬ σ.M.ker ≤ ρ.M.ker := by
  simpa using (not_congr (qRelativeEnt_ne_top_iff (ρ := ρ) (σ := σ)))
