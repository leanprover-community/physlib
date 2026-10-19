/-
Copyright (c) 2026 Emil Kubanychbek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emil Kubanychbek
-/
module

public import Physlib.QuantumMechanics.PoschlTeller.Basic
/-!

# Scattering states of the 1d Pöschl-Teller system

The Pöschl-Teller potential is reflectionless.

## i. Overview

At energy `E = ℏ² k² / (2 m)` the time-independent Schrödinger equation of the Pöschl-Teller
system has the exact solution `ψₖ(x) = Pₖ(tanh (κ x)) e^{i k x}`, where the polynomial `Pₖ` is
obtained by applying the operators `-∂ₓ + n κ tanh (κ x)`, for `n = 1, …, N`, to the plane wave
`e^{i k x}`. The operator `-∂ₓ + n κ tanh (κ x)` intertwines the Hamiltonians of the Pöschl-Teller
systems with family numbers `n - 1` and `n`, so it maps solutions of the one to solutions of the
other at the same energy.

Since `tanh (κ x) → ±1` as `x → ±∞`, the solution tends to `Pₖ(±1) e^{i k x}` at both ends.
For `k ≠ 0` it describes a wave incident from the left (`k > 0`) or from the right (`k < 0`)
which is fully transmitted: no reflected wave `e^{-i k x}` appears. This is the statement that the
Pöschl-Teller potential is reflectionless.

The polynomial in `tanh (κ x)` multiplying `e^{i k x}` is tracked as an element of `ℂ[X]`, so that
the intertwining relation becomes an identity of polynomials.

## ii. Key results

- `schrodingerOperator_scatteringState` : the scattering state solves the time-independent
  Schrödinger equation at energy `ℏ² k² / (2 m)`.
- `tendsto_scatteringState_mul_exp_atTop`, `tendsto_scatteringState_mul_exp_atBot` : the
  scattering state tends to `∏ₙ (n κ - i k) e^{i k x}` as `x → ∞` and to
  `∏ₙ (-n κ - i k) e^{i k x}` as `x → -∞`.
- `reflectionless` : the Pöschl-Teller potential is reflectionless.

## iii. Table of contents

- A. Polynomials in `tanh (κ x)`
  - A.1. Derivative, raising operator and Hamiltonian
  - A.2. The intertwining relation
  - A.3. The scattering polynomials
  - A.4. Values at `±1`
- B. The Schrödinger operator
- C. Waves modulated by polynomials in `tanh (κ x)`
  - C.1. Derivatives and smoothness
  - C.2. The Schrödinger operator
  - C.3. Asymptotics
- D. Scattering states
- E. Reflectionlessness

## iv. References

* https://arxiv.org/pdf/2411.14941. [ref: arxiv_2411_14941]
-/
@[expose] public section

noncomputable section

namespace QuantumMechanics

namespace PoschlTeller

open Complex Constants Polynomial Filter Topology
open scoped ContDiff

variable (Q : PoschlTeller)

/-!
## A. Polynomials in `tanh (κ x)`
-/

/-!
### A.1. Derivative, raising operator and Hamiltonian
-/

/-- The derivative acting on the polynomial of a wave `p(tanh (κ x)) e^{i k x}`,
  `p ↦ κ (1 - X²) p' + i k p`, so that
  `∂ₓ (p(tanh (κ x)) e^{i k x}) = (polyDeriv k p)(tanh (κ x)) e^{i k x}`. -/
def polyDeriv (k : ℝ) (p : ℂ[X]) : ℂ[X] :=
  C (Q.κ : ℂ) * (1 - X ^ 2) * derivative p + C (k * I) * p

/-- The raising operator `-∂ₓ + n κ tanh (κ x)` acting on the polynomial of a wave
  `p(tanh (κ x)) e^{i k x}`. -/
def polyRaise (k : ℝ) (n : ℕ) (p : ℂ[X]) : ℂ[X] := -Q.polyDeriv k p + C (n * Q.κ : ℂ) * X * p

/-- The operator `-∂ₓ² - n (n + 1) κ² / cosh² (κ x)` acting on the polynomial of a wave
  `p(tanh (κ x)) e^{i k x}`. This is `2 m / ℏ²` times the Hamiltonian of the Pöschl-Teller system
  with family number `n`. -/
def polyReducedHamiltonian (k : ℝ) (n : ℕ) (p : ℂ[X]) : ℂ[X] :=
  -Q.polyDeriv k (Q.polyDeriv k p) - C ((Q.κ : ℂ) ^ 2 * n * (n + 1)) * (1 - X ^ 2) * p

/-!
### A.2. The intertwining relation
-/

/-- The raising operator intertwines the Hamiltonians with family numbers `n` and `n + 1`. -/
lemma polyReducedHamiltonian_polyRaise (k : ℝ) (n : ℕ) (p : ℂ[X]) :
    Q.polyReducedHamiltonian k (n + 1) (Q.polyRaise k (n + 1) p) =
      Q.polyRaise k (n + 1) (Q.polyReducedHamiltonian k n p) := by
  simp only [polyReducedHamiltonian, polyRaise, polyDeriv, derivative_mul, derivative_add,
    derivative_sub, derivative_neg, derivative_C, derivative_X, derivative_X_sq, derivative_one,
    derivative_zero]
  simp only [map_mul, map_pow, map_add, map_natCast, map_one, map_ofNat, Nat.cast_add,
    Nat.cast_one]
  ring

/-- The derivative of a constant multiple of the plane wave `c e^{i k x}` is `i k c e^{i k x}`. -/
lemma polyDeriv_C (k : ℝ) (c : ℂ) : Q.polyDeriv k (C c) = C (k * I * c) := by
  simp only [polyDeriv, derivative_C, mul_zero, zero_add, C_mul]

/-- The raising operator is linear with respect to constant multiples. -/
lemma polyRaise_C_mul (k : ℝ) (n : ℕ) (c : ℂ) (p : ℂ[X]) :
    Q.polyRaise k n (C c * p) = C c * Q.polyRaise k n p := by
  simp only [polyRaise, polyDeriv, derivative_mul, derivative_C, zero_mul, zero_add]
  ring

/-!
### A.3. The scattering polynomials
-/

/-- The polynomial `Pₖ` of the scattering state `Pₖ(tanh (κ x)) e^{i k x}` of the Pöschl-Teller
  system with family number `n`, obtained by applying the raising operators with
  `1, …, n` to `1`. -/
def polyScattering (k : ℝ) : ℕ → ℂ[X]
  | 0 => 1
  | n + 1 => Q.polyRaise k (n + 1) (polyScattering k n)

/-- The scattering polynomial with family number `n` is an eigenvector of the reduced Hamiltonian
  with eigenvalue `k²`. -/
lemma polyReducedHamiltonian_polyScattering (k : ℝ) (n : ℕ) :
    Q.polyReducedHamiltonian k n (Q.polyScattering k n) =
      C ((k : ℂ) ^ 2) * Q.polyScattering k n := by
  induction n with
  | zero =>
    rw [polyScattering, polyReducedHamiltonian, ← C_1, Q.polyDeriv_C, Q.polyDeriv_C]
    simp only [Nat.cast_zero, mul_zero, zero_mul, map_zero, sub_zero, ← C_neg, ← C_mul]
    congr 1
    linear_combination (-(k : ℂ) ^ 2) * I_sq
  | succ n ih => rw [polyScattering, polyReducedHamiltonian_polyRaise, ih, polyRaise_C_mul]

/-!
### A.4. Values at `±1`
-/

/-- At `tanh (κ x) = 1` the raising operator acts as multiplication by `n κ - i k`. -/
lemma eval_one_polyRaise (k : ℝ) (n : ℕ) (p : ℂ[X]) :
    (Q.polyRaise k n p).eval 1 = (n * Q.κ - k * I) * p.eval 1 := by
  simp only [polyRaise, polyDeriv, map_mul, neg_add_rev, map_natCast, eval_add, eval_neg, eval_mul,
    eval_C, eval_sub, eval_one, eval_pow, eval_X, one_pow, sub_self, mul_zero, zero_mul, neg_zero,
    add_zero, eval_natCast, mul_one]
  ring

/-- At `tanh (κ x) = -1` the raising operator acts as multiplication by `-n κ - i k`. -/
lemma eval_neg_one_polyRaise (k : ℝ) (n : ℕ) (p : ℂ[X]) :
    (Q.polyRaise k n p).eval (-1) = (-(n * Q.κ) - k * I) * p.eval (-1) := by
  simp only [polyRaise, polyDeriv, map_mul, neg_add_rev, map_natCast, eval_add, eval_neg, eval_mul,
    eval_C, eval_sub, eval_one, eval_pow, eval_X, even_two, Even.neg_pow, one_pow, sub_self,
    mul_zero, zero_mul, neg_zero, add_zero, eval_natCast, mul_neg, mul_one, neg_mul]
  ring

/-- The value at `1` of the scattering polynomial is `∏ₙ (n κ - i k)`. -/
lemma polyScattering_eval_one (k : ℝ) (n : ℕ) :
    (Q.polyScattering k n).eval 1 = ∏ j ∈ Finset.range n, ((j + 1) * Q.κ - k * I) := by
  induction n with
  | zero => simp only [polyScattering, eval_one, Finset.range_zero, Finset.prod_empty]
  | succ n ih =>
    rw [polyScattering, eval_one_polyRaise, ih, Finset.prod_range_succ]
    push_cast
    ring

/-- The value at `-1` of the scattering polynomial is `∏ₙ (-n κ - i k)`. -/
lemma polyScattering_eval_neg_one (k : ℝ) (n : ℕ) :
    (Q.polyScattering k n).eval (-1) = ∏ j ∈ Finset.range n, (-((j + 1) * Q.κ) - k * I) := by
  induction n with
  | zero => simp only [polyScattering, eval_one, Finset.range_zero, Finset.prod_empty]
  | succ n ih =>
    rw [polyScattering, eval_neg_one_polyRaise, ih, Finset.prod_range_succ]
    push_cast
    ring

/-- The value at `1` of the scattering polynomial is non-zero. -/
lemma polyScattering_eval_one_ne_zero (k : ℝ) (n : ℕ) : (Q.polyScattering k n).eval 1 ≠ 0 := by
  rw [polyScattering_eval_one, Finset.prod_ne_zero_iff]
  intro j _ hj
  have hre := congrArg Complex.re hj
  simp only [sub_re, mul_re, add_re, natCast_re, one_re, ofReal_re, ofReal_im, I_re, I_im,
    zero_re] at hre
  have := Q.κ_pos
  nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

/-- The value at `-1` of the scattering polynomial is non-zero. -/
lemma polyScattering_eval_neg_one_ne_zero (k : ℝ) (n : ℕ) :
    (Q.polyScattering k n).eval (-1) ≠ 0 := by
  rw [polyScattering_eval_neg_one, Finset.prod_ne_zero_iff]
  intro j _ hj
  have hre := congrArg Complex.re hj
  simp only [sub_re, neg_re, mul_re, add_re, natCast_re, one_re, ofReal_re, ofReal_im, I_re,
    I_im, zero_re] at hre
  have := Q.κ_pos
  nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

/-!
## B. The Schrödinger operator
-/

/-- The Schrödinger operator of the Pöschl-Teller system acting on functions `ℝ → ℂ`,
  `ψ ↦ -ℏ² / (2 m) ψ'' + V ψ`. -/
def schrodingerOperator (ψ : ℝ → ℂ) : ℝ → ℂ := fun x =>
  -(ℏ ^ 2 / (2 * Q.m) : ℝ) * deriv (deriv ψ) x + Q.potential (Space.oneEquiv.symm x) * ψ x

/-!
## C. Waves modulated by polynomials in `tanh (κ x)`
-/

/-- The wave `x ↦ p(tanh (κ x)) e^{i k x}`. -/
def waveOfPoly (k : ℝ) (p : ℂ[X]) (x : ℝ) : ℂ :=
  p.eval (Real.tanh (Q.κ * x) : ℂ) * exp (k * x * I)

/-!
### C.1. Derivatives and smoothness
-/

/-- The derivative of `p(tanh (κ x)) e^{i k x}` is `(polyDeriv k p)(tanh (κ x)) e^{i k x}`. -/
lemma hasDerivAt_waveOfPoly (k : ℝ) (p : ℂ[X]) (x : ℝ) :
    HasDerivAt (Q.waveOfPoly k p) (Q.waveOfPoly k (Q.polyDeriv k p) x) x := by
  have ht : HasDerivAt (fun x => (Real.tanh (Q.κ * x) : ℂ))
      (((1 - Real.tanh (Q.κ * x) ^ 2) * (Q.κ * 1) : ℝ) : ℂ) x :=
    ((hasDerivAt_tanh _).comp x ((hasDerivAt_id x).const_mul Q.κ)).ofReal_comp
  have hp := (p.hasDerivAt _).comp x ht
  have he : HasDerivAt (fun x : ℝ => exp (k * x * I)) (exp (k * x * I) * (k * 1 * I)) x :=
    ((((hasDerivAt_id x).ofReal_comp).const_mul (k : ℂ)).mul_const I).cexp
  refine (hp.mul he).congr_deriv ?_
  simp only [waveOfPoly, polyDeriv, Function.comp_apply, eval_add, eval_mul, eval_C, eval_sub,
    eval_one, eval_pow, eval_X]
  push_cast
  ring

lemma deriv_waveOfPoly (k : ℝ) (p : ℂ[X]) :
    deriv (Q.waveOfPoly k p) = Q.waveOfPoly k (Q.polyDeriv k p) :=
  funext fun x => (Q.hasDerivAt_waveOfPoly k p x).deriv

lemma differentiable_waveOfPoly (k : ℝ) (p : ℂ[X]) : Differentiable ℝ (Q.waveOfPoly k p) :=
  fun x => (Q.hasDerivAt_waveOfPoly k p x).differentiableAt

/-- The wave `p(tanh (κ x)) e^{i k x}` is smooth. -/
lemma contDiff_waveOfPoly (k : ℝ) (p : ℂ[X]) : ContDiff ℝ ∞ (Q.waveOfPoly k p) := by
  rw [contDiff_infty]
  intro n
  induction n generalizing p with
  | zero => exact contDiff_zero.mpr (Q.differentiable_waveOfPoly k p).continuous
  | succ n ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv, deriv_waveOfPoly]
    exact ⟨Q.differentiable_waveOfPoly k p,
      by simp only [WithTop.natCast_ne_top, analyticOn_univ, IsEmpty.forall_iff], ih _⟩

/-!
### C.2. The Schrödinger operator
-/

/-- Multiplying the polynomial by a constant multiplies the wave by that constant. -/
lemma waveOfPoly_C_mul (k : ℝ) (c : ℂ) (p : ℂ[X]) :
    Q.waveOfPoly k (C c * p) = c • Q.waveOfPoly k p := by
  funext x
  simp only [waveOfPoly, ofReal_tanh, ofReal_mul, eval_mul, eval_C, mul_assoc, Pi.smul_apply,
    smul_eq_mul]

/-- The Schrödinger operator acts on `p(tanh (κ x)) e^{i k x}` through the reduced
  Hamiltonian with family number `N`. -/
lemma schrodingerOperator_waveOfPoly (k : ℝ) (p : ℂ[X]) :
    Q.schrodingerOperator (Q.waveOfPoly k p) =
      ((ℏ ^ 2 / (2 * Q.m) : ℝ) : ℂ) • Q.waveOfPoly k (Q.polyReducedHamiltonian k Q.N p) := by
  funext x
  simp only [schrodingerOperator, deriv_waveOfPoly, Q.potential_eq_tanh, Space.oneEquiv_symm_apply,
    depth]
  simp only [waveOfPoly, polyReducedHamiltonian, eval_sub, eval_neg, eval_mul, eval_C, eval_one,
    eval_pow, eval_X, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-!
### C.3. Asymptotics
-/

/-- Removing the plane wave factor from `p(tanh (κ x)) e^{i k x}` leaves `p(tanh (κ x))`. -/
lemma waveOfPoly_mul_exp (k : ℝ) (p : ℂ[X]) (x : ℝ) :
    Q.waveOfPoly k p x * exp (-(k * x * I)) = p.eval (Real.tanh (Q.κ * x) : ℂ) := by
  rw [waveOfPoly, mul_assoc, ← exp_add, add_neg_cancel, exp_zero, mul_one]

/-- As `x → ∞`, `p(tanh (κ x)) e^{i k x}` approaches `p(1) e^{i k x}`. -/
lemma tendsto_waveOfPoly_mul_exp_atTop (k : ℝ) (p : ℂ[X]) :
    Tendsto (fun x => Q.waveOfPoly k p x * exp (-(k * x * I))) atTop (𝓝 (p.eval 1)) := by
  simp_rw [Q.waveOfPoly_mul_exp]
  have ht : Tendsto (fun x => Real.tanh (Q.κ * x)) atTop (𝓝 1) :=
    tendsto_tanh_atTop.comp (tendsto_id.const_mul_atTop Q.κ_pos)
  have h := (p.continuous.tendsto _).comp ((continuous_ofReal.tendsto _).comp ht)
  simpa only [ofReal_tanh, ofReal_mul, Function.comp_def, ofReal_one] using h

/-- As `x → -∞`, `p(tanh (κ x)) e^{i k x}` approaches `p(-1) e^{i k x}`. -/
lemma tendsto_waveOfPoly_mul_exp_atBot (k : ℝ) (p : ℂ[X]) :
    Tendsto (fun x => Q.waveOfPoly k p x * exp (-(k * x * I))) atBot (𝓝 (p.eval (-1))) := by
  simp_rw [Q.waveOfPoly_mul_exp]
  have ht : Tendsto (fun x => Real.tanh (Q.κ * x)) atBot (𝓝 (-1)) :=
    tendsto_tanh_atBot.comp (tendsto_id.const_mul_atBot Q.κ_pos)
  have h := (p.continuous.tendsto _).comp ((continuous_ofReal.tendsto _).comp ht)
  simpa only [ofReal_tanh, ofReal_mul, Function.comp_def, ofReal_neg, ofReal_one] using h

/-!
## D. Scattering states
-/

/-- The scattering state of the Pöschl-Teller system with wavenumber `k`,
  `ψₖ(x) = Pₖ(tanh (κ x)) e^{i k x}`. -/
def scatteringState (k : ℝ) : ℝ → ℂ := Q.waveOfPoly k (Q.polyScattering k Q.N)

/-- The scattering state is smooth. -/
lemma contDiff_scatteringState (k : ℝ) : ContDiff ℝ ∞ (Q.scatteringState k) :=
  Q.contDiff_waveOfPoly k _

/-- The scattering state with wavenumber `k` solves the time-independent Schrödinger equation at
  energy `ℏ² k² / (2 m)`. -/
lemma schrodingerOperator_scatteringState (k : ℝ) :
    Q.schrodingerOperator (Q.scatteringState k) =
      ((ℏ ^ 2 * k ^ 2 / (2 * Q.m) : ℝ) : ℂ) • Q.scatteringState k := by
  rw [scatteringState, schrodingerOperator_waveOfPoly, polyReducedHamiltonian_polyScattering,
    waveOfPoly_C_mul, smul_smul]
  congr 1
  push_cast
  ring

/-- As `x → ∞`, the scattering state tends to `∏ₙ (n κ - i k) e^{i k x}`. -/
lemma tendsto_scatteringState_mul_exp_atTop (k : ℝ) :
    Tendsto (fun x => Q.scatteringState k x * exp (-(k * x * I))) atTop
      (𝓝 (∏ j ∈ Finset.range Q.N, ((j + 1) * Q.κ - k * I))) := by
  rw [← polyScattering_eval_one]
  exact Q.tendsto_waveOfPoly_mul_exp_atTop k _

/-- As `x → -∞`, the scattering state tends to `∏ₙ (-n κ - i k) e^{i k x}`. -/
lemma tendsto_scatteringState_mul_exp_atBot (k : ℝ) :
    Tendsto (fun x => Q.scatteringState k x * exp (-(k * x * I))) atBot
      (𝓝 (∏ j ∈ Finset.range Q.N, (-((j + 1) * Q.κ) - k * I))) := by
  rw [← polyScattering_eval_neg_one]
  exact Q.tendsto_waveOfPoly_mul_exp_atBot k _

/-!
## E. Reflectionlessness
-/

/-- A function `ψ` approaches the plane wave `T e^{i k x}` if and only if `ψ(x) e^{-i k x}`
  tends to `T`. -/
lemma tendsto_sub_mul_exp_iff (l : Filter ℝ) (ψ : ℝ → ℂ) (k : ℝ) (T : ℂ) :
    Tendsto (fun x => ψ x - T * exp (k * x * I)) l (𝓝 0) ↔
      Tendsto (fun x => ψ x * exp (-(k * x * I))) l (𝓝 T) := by
  conv_rhs => rw [tendsto_iff_norm_sub_tendsto_zero]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_congr fun x => ?_
  have h : ψ x - T * exp (k * x * I) = (ψ x * exp (-(k * x * I)) - T) * exp (k * x * I) := by
    rw [sub_mul, mul_assoc (ψ x), ← exp_add, neg_add_cancel, exp_zero, mul_one]
  rw [h, norm_mul, ← ofReal_mul, norm_exp_ofReal_mul_I, mul_one]

/-- **The Pöschl-Teller potential is reflectionless.** For every wavenumber `k` there is a smooth
  solution `ψ` of the time-independent Schrödinger equation at energy `ℏ² k² / (2 m)` which
  tends to the plane wave `T e^{i k x}` as `x → ∞` and to `T' e^{i k x}` as `x → -∞`, with
  `T, T' ≠ 0`. For `k ≠ 0` this is a wave which passes through the well with no reflected wave
  `e^{-i k x}`. -/
theorem reflectionless (k : ℝ) :
    ∃ ψ : ℝ → ℂ, ContDiff ℝ ∞ ψ ∧
      Q.schrodingerOperator ψ = ((ℏ ^ 2 * k ^ 2 / (2 * Q.m) : ℝ) : ℂ) • ψ ∧
      ∃ T T' : ℂ, T ≠ 0 ∧ T' ≠ 0 ∧
        Tendsto (fun x => ψ x - T * exp (k * x * I)) atTop (𝓝 0) ∧
        Tendsto (fun x => ψ x - T' * exp (k * x * I)) atBot (𝓝 0) := by
  refine ⟨Q.scatteringState k, Q.contDiff_scatteringState k,
    Q.schrodingerOperator_scatteringState k, _, _, Q.polyScattering_eval_one_ne_zero k Q.N,
    Q.polyScattering_eval_neg_one_ne_zero k Q.N, ?_, ?_⟩
  · rw [tendsto_sub_mul_exp_iff]
    exact Q.tendsto_waveOfPoly_mul_exp_atTop k _
  · rw [tendsto_sub_mul_exp_iff]
    exact Q.tendsto_waveOfPoly_mul_exp_atBot k _

end PoschlTeller
end QuantumMechanics
end
