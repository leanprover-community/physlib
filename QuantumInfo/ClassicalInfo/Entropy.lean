/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ClassicalInfo.Distribution
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import QuantumInfo.ClassicalInfo.ForMathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! # Shannon entropy

Definitions and facts about the Shannon entropy function -x*ln(x), both on a single
variable and on a distribution.

There is significant overlap with `Real.negMulLog` and `Real.binEntropy` in Mathlib,
and probably these files could be combined in some form. -/

@[expose] public section

noncomputable section
open NNReal

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The one-event entropy function, H₁(p) = -p*ln(p). Uses nits. -/
def H₁ : Prob → ℝ :=
  fun x ↦ Real.negMulLog x

/-- H₁ of 0 is zero.-/
@[simp]
lemma H₁_zero_eq_zero : H₁ 0 = 0 := by
  simp [H₁]

/-- H₁ of 1 is zero.-/
@[simp]
lemma H₁_one_eq_zero : H₁ 1 = 0 := by
  simp [H₁]

/-- Entropy is nonnegative. -/
theorem H₁_nonneg (p : Prob) : 0 ≤ H₁ p := by
  rw [H₁, Real.negMulLog, neg_mul, Left.nonneg_neg_iff]
  exact Real.mul_log_nonpos p.zero_le_coe p.coe_le_one

/-- Entropy is less than 1. -/
theorem H₁_le_1 (p : Prob) : H₁ p < 1 := by
  rw [H₁]
  by_cases h : p = 0
  · norm_num [h]
  · have hp0 : 0 < p := lt_of_le_of_ne' p.zero_le h
    have h₂ := Real.abs_log_mul_self_lt p hp0 p.coe_le_one
    rw [mul_comm, ← abs_neg, ← neg_mul] at h₂
    exact lt_of_abs_lt h₂

/-- Entropy is at most 1/e. -/
theorem H₁_le_exp_m1 (p : Prob) : H₁ p ≤ Real.exp (-1) :=
  Real.negMulLog_le_rexp_neg_one p.zero_le_coe

set_option backward.isDefEq.respectTransparency false in
theorem H₁_concave : ∀ (x y : Prob), ∀ (p : Prob), p[H₁ x ↔ H₁ y] ≤ H₁ (p[x ↔ y]) := by
  intros x y p
  simp only [H₁, smul_eq_mul, Prob.coe_one_minus, Mixable.mix, Mixable.mix_ab, Mixable.mkT_instUniv,
    Prob.mkT_mixable, Prob.to_U_mixable, Mixable.to_U_instUniv, Prob.to_U_mixable]
  by_cases hxy : x = y
  · subst hxy
    ring_nf
    exact le_refl _
  by_cases hp : (p:ℝ) = 0
  · norm_num [hp]
  by_cases hp₁ : (p:ℝ) = 1
  · norm_num [hp₁]
  rw [← ne_eq] at hxy hp hp₁
  have := Real.strictConcaveOn_negMulLog.2
  replace := @this x ?_ y ?_ ?_ p (1 - p) ?_ ?_ (by linarith)
  · simp only [smul_eq_mul] at this
    apply le_of_lt
    convert this
  · simp only [Set.mem_Ici, Prob.zero_le_coe]
  · simp only [Set.mem_Ici, Prob.zero_le_coe]
  · simpa only [Prob.ne_iff]
  · exact lt_of_le_of_ne p.zero_le_coe hp.symm
  · linarith (config := {splitNe := true}) [p.coe_le_one]

/-- The Shannon entropy of a discrete distribution, H(X) = ∑ H₁(p_x). -/
def Hₛ (d : ProbDistribution α) : ℝ :=
  Finset.sum Finset.univ (fun x ↦ H₁ (d.prob x))

/-- Shannon entropy of a distribution is nonnegative. -/
theorem Hₛ_nonneg (d : ProbDistribution α) : 0 ≤ Hₛ d :=
  Finset.sum_nonneg fun _ _ ↦ H₁_nonneg _

/-- Shannon entropy of a distribution is at most ln d. -/
theorem Hₛ_le_log_d (d : ProbDistribution α) : Hₛ d ≤ Real.log (Fintype.card α) := by
  --Thanks Aristotle
  by_cases h : Fintype.card α = 0
  · simp_all [Hₛ, Fintype.card_eq_zero_iff.mp h]
  -- Since the sum of the probabilities is 1, we can apply Jensen's inequality for the
    -- convex function -x log x.
  have h_jensen {p : α → ℝ} (hsum : ∑ i, p i = 1) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
      -∑ i, p i * (p i).log ≤ Real.log (Fintype.card α) := by
    have h_jensen : (∑ i, (Fintype.card α : ℝ)⁻¹ * p i) * (∑ i, (Fintype.card α : ℝ)⁻¹ * p i).log ≤
          (∑ i, (Fintype.card α : ℝ)⁻¹ * (p i * (p i).log)) := by
      have h_convex : ConvexOn ℝ (Set.Icc 0 1) (fun x ↦ x * Real.log x) :=
        Real.convexOn_mul_log.subset Set.Icc_subset_Ici_self (convex_Icc 0 1)
      convert h_convex.map_sum_le _ _ _ <;> aesop
    simp_rw [← Finset.mul_sum, hsum, mul_one, Real.log_inv] at h_jensen
    have : 0 < (Fintype.card α : ℝ)⁻¹ := by positivity
    have := mul_inv_cancel₀ <| show (Fintype.card α : ℝ) ≠ 0 by positivity
    nlinarith
  simpa [Hₛ, H₁, Real.negMulLog] using h_jensen d.2 (by grind)

/-- The shannon entropy of a constant variable is zero. -/
@[simp]
theorem Hₛ_constant_eq_zero {i : α} : Hₛ (ProbDistribution.constant i) = 0 := by
  simp [Hₛ, apply_ite]

/-- Shannon entropy of a uniform distribution is ln d. -/
theorem Hₛ_uniform [Nonempty α] :
    Hₛ (ProbDistribution.uniform (α := α)) = Real.log (Finset.univ.card (α := α)) := by
  simp [Hₛ, ProbDistribution.prob, H₁, Real.negMulLog]

/-- Shannon entropy of two-event distribution. -/
theorem Hₛ_coin (p : Prob) : Hₛ (ProbDistribution.coin p) = Real.binEntropy p := by
  simp [Hₛ, H₁, ProbDistribution.coin, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

lemma Hₛ_eq_of_multiset_map_eq (d₁ : ProbDistribution α) (d₂ : ProbDistribution β)
    (h : Multiset.map d₁.prob Finset.univ.val = Multiset.map d₂.prob Finset.univ.val) :
    Hₛ d₁ = Hₛ d₂ := by
  convert congr_arg (fun m ↦ m.map (fun x ↦ -Real.log x.1 * x.1 ) |> Multiset.sum ) h using 1
  <;> simp [Hₛ, H₁, mul_comm, Real.negMulLog]

--TODO:
-- * Shannon entropy is concave under mixing distributions.
-- * Shannon entropy as an expectation value
