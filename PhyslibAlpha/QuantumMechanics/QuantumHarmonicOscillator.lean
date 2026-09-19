/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
module
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
/-!
# Quantum harmonic oscillator
-/

noncomputable section

/-- Annihilation operator. -/
def a (x : ℕ → ℂ) : ℕ → ℂ := fun n => √(n + 1) * x (n + 1)

def aLin : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) := {
  toFun := a
  map_add' := by
    unfold a
    intro x y
    ext n
    simp only [Pi.add_apply]
    ring_nf
  map_smul' := by
    intro m x
    unfold a
    ext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring_nf
}

/-- Creation operator. -/
def a_dag (x : ℕ → ℂ) : ℕ → ℂ := fun n => ite (n = 0) 0 (√n * x (n - 1))

def a_dagLin : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) := {
  toFun := a_dag
  map_add' := by
    unfold a_dag
    intro x y
    ext n
    simp only [Pi.add_apply]
    ring_nf
    split_ifs <;> simp
  map_smul' := by
    intro m x
    unfold a_dag
    ext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_ite, mul_zero]
    ring_nf
}

def ε (n : ℕ) (c : ℂ) : ℕ → ℂ := fun i => ite (i = n) c 0

/-- Verify that a_dag really is the transpose of a. -/
lemma a_dag_eq (i j : ℕ) : a_dag (ε i 1) j = star (a (ε j 1) i) := by
    unfold a a_dag ε
    simp only [mul_ite, mul_one, mul_zero, RCLike.star_def]
    split_ifs with _ _ _ g₃
    all_goals try omega
    all_goals try exact Eq.symm ((fun {z} ↦ Complex.conj_eq_iff_re.mpr) rfl)
    rw [← g₃];simp

/-- Verify that a |n + 1⟩ = √(n + 1) |n ⟩ -/
lemma verify_a (n : ℕ) :
    a (ε (n + 1) 1) =
       ε n (√(n + 1))  := by
  unfold a ε
  ext i
  simp only [Nat.add_right_cancel_iff, mul_ite, mul_one, mul_zero]
  split_ifs with g₀
  · rw [g₀]
  · rfl

/-- Verify that a† ∣n⟩ = √(n+1) ∣n+1⟩. -/
lemma verify_a_dag (n : ℕ) :
    a_dag (ε n 1) = ε (n + 1) (√(n + 1))  := by
  unfold a_dag ε
  ext i
  split_ifs with _ _ _ h
  all_goals try omega
  · rfl
  · rw [h]; simp
  · simp

lemma verify_a_dag_a (n : ℕ) (x : ℕ → ℂ) :
    a_dag (a x) n = n * x n  := by
  unfold a_dag a
  split_ifs with g
  · rw [g];simp
  · have h : n - 1 + 1 = n := by omega
    repeat rw [h]
    norm_cast
    rw [h]
    rw [← mul_assoc]
    congr
    norm_cast
    refine Real.mul_self_sqrt ?_
    simp

lemma verify_a_a_dag (n : ℕ) (x : ℕ → ℂ) :
    a (a_dag x) n = (n + 1) * x n  := by
  unfold a_dag a
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.cast_add, Nat.cast_one,
    add_tsub_cancel_right]
  rw [← mul_assoc]
  congr
  norm_cast
  refine Real.mul_self_sqrt ?_
  norm_cast
  omega

lemma commutation_relation :
    a ∘ a_dag - a_dag ∘ a = id := by
  unfold a a_dag
  ext x i
  simp only [Pi.sub_apply, Function.comp_apply, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    ↓reduceIte, Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, id_eq]
  split_ifs with g₀
  · rw [g₀];simp
  · norm_cast
    have : i - 1 + 1 = i := by omega
    rw [this]
    repeat rw [← mul_assoc]
    have : (i + 1) * x i - i * x i = x i := by
        ring_nf
    rw [← this]
    congr
    · norm_cast
      refine Real.mul_self_sqrt ?_
      linarith
    · norm_cast
      refine Real.mul_self_sqrt ?_
      simp

def coherentState (α : ℂ) : ℕ → ℂ :=
    fun n : ℕ => Real.exp (-‖α‖^2 / 2) * α ^ n / √(n.factorial)

def probabilityOf (n : ℕ) (α : ℂ) : NNReal :=
    ⟨‖coherentState α n‖^2, by simp⟩

/-- Coherent state has a Poisson distribution. -/
lemma probabilityOf_eq_poisson_C (n : ℕ) (α : ℂ) :
    let Λ := ⟨‖α‖ ^ 2, sq_nonneg ‖α‖⟩
    probabilityOf n α =
    ProbabilityTheory.poissonMeasure Λ {n} := by
  unfold probabilityOf ProbabilityTheory.poissonMeasure coherentState
  simp only [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow,
    Complex.ofReal_ofNat, Complex.norm_div, Complex.norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, MeasurableSpace.measurableSet_top, MeasureTheory.Measure.sum_apply,
    MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.dirac_apply', Set.indicator_singleton,
    Pi.one_apply, smul_eq_mul]
  have : |√(n.factorial : ℝ)| = √(n.factorial : ℝ) := by simp
  simp_rw [this]
  simp only [Pi.single, Function.update, eq_rec_constant, Pi.zero_apply, dite_eq_ite, mul_ite,
    mul_one, mul_zero, tsum_ite_eq]
  simp_rw [← mul_div]
  field_simp
  have : √↑n.factorial ^ 2 = (n.factorial : ℝ) := by
    refine Real.sq_sqrt ?_
    simp
  simp_rw [this]
  congr
  rw [max_eq_left]
  · have (a b : ℝ) (h : a = b) : a / n.factorial = b / n.factorial := by
        rw [h]
    apply this
    norm_cast
    have (a b c d : ℝ) (hab : a = b) (hcd : c = d) :
        a * c = b * d := by rw [hab,hcd]
    apply this
    · norm_cast
      have : ‖α‖^2 ≥ 0 := by simp
      have (r : ℝ) :
        Complex.exp (-(r/2)) = Real.exp (-(r/2)) := by simp
      rw [this]
      have (r : ℝ) : ‖Complex.ofReal (Real.exp r)‖ = Real.exp r := by simp
      rw [this]
      have h₀ (r : ℝ) : (Real.exp r) ^ (2:ℝ) = Real.exp (r * 2) :=
        Eq.symm (Real.exp_mul r 2)
      have h₁ (r : ℝ) : (Real.exp r) ^ (2:ℝ) = Real.exp r ^ 2 :=
        Real.rpow_two (Real.exp r)
      simp_rw [h₁] at h₀
      rw [h₀]
      congr
      simp only [neg_mul, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        IsUnit.div_mul_cancel, neg_inj]
      norm_cast
    · rw [pow_right_comm]
      congr
  · apply div_nonneg
    · apply mul_nonneg
      · apply Real.exp_nonneg
      · exact pow_nonneg (NNReal.coe_nonneg _) n
    · simp


/-- The only eigenvectors of `a` are the coherent states. -/
lemma coherentState_only_eigenvector (α : ℂ) (v : ℕ → ℂ) :
    a v = α • v ↔
    v = (Complex.exp (↑‖α‖ ^ 2 / 2) * v 0) • coherentState α := by
  constructor
  intro hv
  ext n
  induction n with
  | zero =>
    unfold coherentState
    simp only [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow,
      Complex.ofReal_ofNat, Pi.smul_apply, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one,
      Real.sqrt_one, Complex.ofReal_one, div_one, smul_eq_mul]
    field_simp
    rw [mul_assoc]
    rw [← Complex.exp_add]
    field_simp
    ring_nf
    simp
  | succ n hn =>
    unfold a at hv
    have h₀ := congrFun hv n
    simp only [Pi.smul_apply, smul_eq_mul] at h₀
    have : v (n + 1) = α * v n / √(n + 1) := by
      field_simp
      rw [← h₀, mul_comm]
    rw [this, hn]
    unfold coherentState
    field_simp
    ring_nf
    simp only [one_div, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat,
      Pi.smul_apply, smul_eq_mul]
    rw [pow_add]
    field_simp
    ring_nf
    repeat rw [mul_assoc]
    congr
    field_simp
    ring_nf
    rw [add_comm]
    nth_rw 2 [add_comm]
    have : (n+1).factorial = (n+1) * n.factorial := rfl
    rw [this]
    norm_num
    field_simp
  intro h
  rw [h]
  unfold a
  ext n
  have : (Complex.exp (↑‖α‖ ^ 2 / 2)) ≠ 0 := by simp
  field_simp
  unfold coherentState
  simp only [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow,
    Complex.ofReal_ofNat, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring_nf
  field_simp
  rw [mul_assoc, add_comm 1 n, add_comm 1 (n:ℝ)]
  have : (n+1).factorial = (n+1) * n.factorial := rfl
  rw [this]
  norm_num
  field_simp

lemma eigenvector_coherentState (α : ℂ) :
    a (coherentState α) = α • coherentState α := by
  rw [coherentState_only_eigenvector α (coherentState α)]
  have : Complex.exp (↑‖α‖ ^ 2 / 2) * coherentState α 0 = 1 := by
    unfold coherentState
    simp only [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow,
      Complex.ofReal_ofNat, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, Real.sqrt_one,
      Complex.ofReal_one, div_one]
    rw [← Complex.exp_add]
    field_simp
    ring_nf
    simp
  rw [this]
  simp

/-- None of the `coherentState` eigenvectors are proportional. -/
lemma distinct_eigenvectors_a (α β c : ℂ)
    (hc : coherentState α = c • coherentState β) : α = β := by
  have h₀ := congrFun hc 0
  have h₁ := congrFun hc 1
  simp [coherentState] at h₀ h₁
  by_cases hc₀ : c = 0
  · subst c
    simp at h₀
  generalize Complex.exp (-↑‖α‖ ^ 2 / 2) = A at *
  subst A
  field_simp at h₁
  exact h₁

/-- Formal eigenvectors for `a_dag` (not in `ℓ²(ℂ)`)
(fails at n=0) . -/
lemma a_dagalmost_eigenvector {α : ℂ} (hα : α ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    a_dag (fun n => √(n.factorial) / α^n) n =
      α • (fun n => √(n.factorial) / α^n) n := by
  unfold a_dag
  split_ifs with g₀
  · tauto
  · simp only [smul_eq_mul]
    rw [← Nat.mul_factorial_pred hn]
    norm_num
    have : Complex.ofReal √( (n-1).factorial) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero, Nat.cast_nonneg, Real.sqrt_eq_zero,
        Nat.cast_eq_zero]
      exact Nat.factorial_ne_zero (n - 1)
    field_simp
    have : α ^ n = α * α ^ (n - 1) := by
      exact Eq.symm (mul_pow_sub_one hn α)
    rw [this]
    ring_nf

lemma a_dag_nullspace
    {v : ℕ → ℂ} (hv : a_dag v = 0) : v = 0 := by
  unfold a_dag at hv
  ext n
  induction n with
  | zero =>
    have := congrFun hv 1
    simp at this ⊢
    tauto
  | succ n hn =>
    have := congrFun hv (n + 2)
    simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte, Nat.cast_add,
      Nat.cast_ofNat, Nat.add_one_sub_one, Pi.zero_apply, mul_eq_zero,
      Complex.ofReal_eq_zero] at this hn hv ⊢
    cases this with
    | inl h =>
      exfalso
      revert h
      refine Real.sqrt_ne_zero'.mpr ?_
      linarith
    | inr h =>
      tauto

lemma no_a_dag_eigenvector (α : ℂ) (v : ℕ → ℂ) :
    a_dag v = α • v ↔ v = 0 := by
  constructor
  · intro hv
    by_cases hα : α = 0
    · subst α; apply a_dag_nullspace; rw [hv]; simp
    have := congrFun hv 0
    unfold a_dag at this
    ext n
    induction n with
    | zero => simp at this ⊢;tauto
    | succ n hn =>
      unfold a_dag at hv
      have := congrFun hv (n+1)
      simp_all
  intro
  subst v
  unfold a_dag
  simp
  rfl

lemma commutationRelation : ⁅aLin, a_dagLin⁆ = 1 := by
  simp only [Bracket.bracket]
  unfold aLin a_dagLin
  ext x i
  change _ = id x i
  rw [← commutation_relation]
  simp


/-- The `coherentState` with parameter `0` is just the first basis vector. -/
example : coherentState 0 = fun n => ite (n = 0) 1 0 := by
  unfold coherentState
  ext n
  split_ifs with g₀
  · subst n;simp
  · rw [zero_pow g₀]
    simp



/-- The coherent state belongs to `ℓ²(ℂ)`. -/
def coherentState_ℓ2 (α : ℂ) : lp (fun _ : ℕ => ℂ) 2 := {
  val := coherentState α
  property := by
    simp only [lp, Memℓp, OfNat.ofNat_ne_zero, ↓reduceIte, ENNReal.ofNat_ne_top, Summable,
      ENNReal.toReal_ofNat, Real.rpow_ofNat]
    use (‖Complex.exp (-↑‖α‖ ^ 2 / 2)^2 * Complex.exp (‖α‖^2)‖)
    suffices HasSum (fun i : ℕ ↦ ( ‖α‖ ^ i
      / |√↑i.factorial|) ^ 2)
      ‖Complex.exp (↑‖α‖ ^ 2)‖ by
      simp_rw [div_pow] at this
      have h := this.mul_left (Real.exp (-‖α‖ ^ 2 / 2) ^ 2)
      convert h using 2 with i
      · unfold coherentState
        rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp, div_pow, mul_pow]
        ring
      · have hc : (-(↑‖α‖ : ℂ) ^ 2 / 2) = ((-‖α‖ ^ 2 / 2 : ℝ) : ℂ) := by
          push_cast
          ring
        rw [norm_mul, norm_pow, hc, Complex.norm_exp_ofReal]
    have (r : ℝ) : |√r| = √r := by
      rw [abs_eq_self]
      simp
    simp_rw [this, div_pow]
    have (i : ℕ) : (‖α‖ ^ i) ^ 2 = (‖α‖ ^ 2) ^ i := pow_right_comm ‖α‖ i 2
    simp_rw [this]
    rw [← Complex.ofReal_pow]
    generalize ‖α‖^2 = A
    simp only [Nat.cast_nonneg, Real.sq_sqrt, Complex.norm_exp_ofReal]
    convert! NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) A
    · simp [NormedSpace.expSeries]
      field_simp
    · exact Real.exp_eq_exp_ℝ
}
