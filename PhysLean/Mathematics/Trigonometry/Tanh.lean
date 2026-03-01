/-
Copyright (c) 2025 Afiq Hatta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Afiq Hatta
-/
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
/-!
# Properties of Tanh
We want to prove that the reflectionless potential is a Schwartz map.
This means proving that pointwise multiplication of a Schwartz map with tanh is a Schwartz map.
This means we need to prove that all derivatives of tanh are bounded and continuous, so that
the nth derivative of a function multiplied by tanh decays faster than any polynomial.

## TODO
- Add these to mathlib eventually
- Fill in the proofs for the properties of tanh
-/

open Real
open NNReal
open Field
open scoped ContDiff

/-- The derivative of tanh(x) is 1 - tanh(x)^2 -/
lemma deriv_tanh : deriv Real.tanh = fun x => 1 - Real.tanh x ^ 2 := by
  have h: deriv (sinh / cosh) = fun x => 1 - Real.tanh x ^ 2 := by
    funext x
    rw [deriv_div, Real.deriv_sinh, Real.deriv_cosh]
    field_simp
    rw [sq, sq, tanh_eq_sinh_div_cosh]
    field_simp
    · apply Real.differentiable_sinh
    · apply Real.differentiable_cosh
    · exact ne_of_gt (Real.cosh_pos x)
  have h': Real.tanh = (sinh / cosh) := by
    funext x
    rw [Pi.div_apply, tanh_eq_sinh_div_cosh]
  nth_rewrite 1 [h']
  apply h

/-- Tanh(x) is n times continuously differentiable for all n -/
lemma contDiff_tanh {n : ℕ} : ContDiff ℝ n tanh := by
  have hdiv : ContDiff ℝ n (fun x => Real.sinh x / Real.cosh x) := by
    apply ContDiff.div
    · exact contDiff_sinh
    · exact contDiff_cosh
    · intro x
      exact ne_of_gt (Real.cosh_pos x)
  conv =>
    enter [3, x]
    rw [tanh_eq_sinh_div_cosh]
  exact hdiv

/-- The nth derivative of Tanh(x) is a polynomial of Tanh(x) -/
lemma iteratedDeriv_tanh_is_polynomial_of_tanh (n : ℕ) : ∃ P : Polynomial ℝ, ∀ x,
    iteratedDeriv n Real.tanh x = P.eval (Real.tanh x) := by
  induction n with
  | zero =>
    rw [iteratedDeriv_zero]
    use Polynomial.X
    simp
  | succ n ih =>
    obtain ⟨P, h'⟩ := ih
    rw [iteratedDeriv_succ]
    have h'': iteratedDeriv n tanh = (fun x => Polynomial.eval (tanh x) P) := by
      funext x
      apply h'
    have h_comp : (fun x => Polynomial.eval (tanh x) P) = (fun t => P.eval t) ∘ tanh := by
      funext x
      simp [Function.comp_apply]
    rw [h'', h_comp]
    use Polynomial.derivative P * (1 - Polynomial.X^2)
    intro x
    rw [deriv_comp, Polynomial.deriv, deriv_tanh]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow,
      Polynomial.eval_X]
    case h.hh =>
      have h': Real.tanh = (sinh / cosh) := by
        funext x
        rw [Pi.div_apply, tanh_eq_sinh_div_cosh]
      rw [h']
      apply DifferentiableAt.div
      · apply Real.differentiable_sinh
      · apply Real.differentiable_cosh
      · exact ne_of_gt (Real.cosh_pos x)
    case h.hh₂ =>
      apply Polynomial.differentiableAt

/-- For a polynomial P, show it's bounded on any bounded interval -/
lemma polynomial_bounded_on_interval (P : Polynomial ℝ) (a b : ℝ) :
    ∃ M : ℝ, ∀ x : ℝ, x ∈ Set.Icc a b → |P.eval x| ≤ M := by
  -- Polynomials are continuous
  have hcont : Continuous (fun x => P.eval x) := P.continuous
  -- Closed bounded intervals are compact
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  -- Continuous functions on compact sets are bounded
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hcont.continuousOn
  use M
  exact hM

/-- For a polynomial P, show that P (tanh x) is bounded on the real line -/
lemma polynomial_tanh_bounded (P : Polynomial ℝ) :
    ∃ C : ℝ, ∀ x : ℝ, |P.eval (Real.tanh x)| ≤ C := by
  -- Since tanh maps to (-1, 1), it maps to [-1+ε, 1-ε] for any ε > 0
  -- But more directly, tanh maps to (-1, 1) ⊆ [-1, 1]
  have h_range : ∀ x : ℝ, Real.tanh x ∈ Set.Icc (-1) 1 := by
    intro x
    constructor
    · exact le_of_lt (neg_one_lt_tanh x)
    · exact le_of_lt (tanh_lt_one x)
  -- Apply polynomial boundedness on [-1, 1]
  obtain ⟨M, hM⟩ := polynomial_bounded_on_interval P (-1) 1
  use M
  intro x
  exact hM (Real.tanh x) (h_range x)

/-- The nth derivative of tanh is bounded on the real line -/
lemma iteratedDeriv_tanh_bounded (n : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, |iteratedDeriv n Real.tanh x| ≤ C := by
  obtain ⟨P, hP⟩ := iteratedDeriv_tanh_is_polynomial_of_tanh n
  obtain ⟨C, hC⟩ := polynomial_tanh_bounded P
  use C
  intro x
  rw [hP]
  exact hC x

/-- tanh is infinitely differentiable -/
lemma contDiff_top_tanh : ContDiff ℝ ∞ Real.tanh := by
    rw [contDiff_infty]
    apply contDiff_tanh

/-- tanh has temperate growth -/
lemma tanh_hasTemperateGrowth : Function.HasTemperateGrowth Real.tanh := by
  constructor
  · apply contDiff_top_tanh
  · intro n
    use 0
    obtain ⟨C, hC⟩ := iteratedDeriv_tanh_bounded n
    use C
    intro x
    have h_equiv : ‖iteratedFDeriv ℝ n Real.tanh x‖ = |iteratedDeriv n Real.tanh x| := by
      rw [← iteratedFDerivWithin_univ]
      rw [← iteratedDerivWithin_univ]
      rw [← norm_eq_abs]
      rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    rw [h_equiv]
    simp only [pow_zero, mul_one]
    exact hC x

/-- Iterated derivative for scaled tanh is differentiable -/
lemma iteratedDeriv_tanh_differentiable (n : ℕ) : Differentiable ℝ (iteratedDeriv n tanh) := by
  have h : ContDiff ℝ (n + 1) tanh := by
    apply contDiff_tanh
  apply h.differentiable_iteratedDeriv
  have h' : n < n + 1 := by
    apply Nat.lt_add_one
  norm_cast

/-- Norm of Iterated derivative for scaled tanh is equal to the norm of its Fderiv -/
lemma tanh_const_mul_iteratedDeriv_norm_eq_iteratedFDeriv_norm (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (fun x => tanh (κ * x)) x‖
    = |iteratedDeriv n (fun x => tanh (κ * x)) x| := by
  rw [← iteratedFDerivWithin_univ, ← iteratedDerivWithin_univ, ← norm_eq_abs,
      norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]

/-- Iterated derivative for scaled tanh -/
lemma iteratedDeriv_tanh_const_mul (n : ℕ) (κ : ℝ) : ∀ x : ℝ,
    iteratedDeriv n (fun y => Real.tanh (κ * y)) x = κ^n * (iteratedDeriv n Real.tanh) (κ * x) := by
  induction n with
  | zero =>
    rw [iteratedDeriv_zero]
    field_simp
    simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have h' : iteratedDeriv n (fun y => tanh (κ * y)) =
        fun x => κ ^ n * iteratedDeriv n tanh (κ * x) := by
      funext x
      rw [ih]
    rw [h']
    simp only [deriv_const_mul_field']
    have h'': (fun x => iteratedDeriv n tanh (κ * x)) =
        (iteratedDeriv n tanh) ∘ (fun x => κ * x) := by
      funext x
      simp
    rw [h'']
    intro x
    rw [deriv_comp, ← iteratedDeriv_succ]
    have h''': deriv (fun x => κ * x) = fun x => κ := by
      funext x
      rw [deriv_const_mul, ← Function.id_def]
      field_simp
      simp only [deriv_id', mul_one]
      apply differentiable_id
    rw [h''']
    field_simp
    ring
    apply iteratedDeriv_tanh_differentiable
    fun_prop

/-- tanh(κx) has temperate growth -/
lemma tanh_const_mul_hasTemperateGrowth (κ : ℝ) :
    Function.HasTemperateGrowth (fun x => Real.tanh (κ * x)) := by
  constructor
  · have h : (fun x => Real.tanh (κ * x)) = (Real.tanh ∘ (fun x => κ * x)) :=
      rfl
    have h' : ContDiff ℝ ∞ (fun x => κ * x) := by
      have h'': (fun x : ℝ => κ * x) = fun x => κ • x := rfl
      rw [contDiff_infty, h'']
      intro n
      apply contDiff_const_smul
    rw [h]
    apply ContDiff.comp contDiff_top_tanh h'
  · intro n
    obtain ⟨D, hD⟩ := iteratedDeriv_tanh_bounded n
    use 0
    use D * (|κ| ^ n)
    intro x
    rw [tanh_const_mul_iteratedDeriv_norm_eq_iteratedFDeriv_norm, iteratedDeriv_tanh_const_mul]
    field_simp
    rw [abs_mul, abs_pow, mul_comm, mul_comm, mul_comm D (|κ| ^ n)]
    apply mul_le_mul_of_nonneg_left
    apply hD
    simp only [abs_nonneg, pow_nonneg]
