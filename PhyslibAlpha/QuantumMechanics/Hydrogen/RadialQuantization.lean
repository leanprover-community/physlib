/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.Hydrogen.RadialFunctions
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!

# Quantisation of the hydrogen levels

Why the bound-state energies of hydrogen are discrete: a square integrable solution of the radial
equation of the form `ρ^(l+1) e^(-κρ) × (power series)` exists only for `κ = 1/ν` with a natural
number `ν > l`, and is then the radial function `u_{νl}` of `RadialFunctions`.

## i. Overview

In Rydberg units a bound state of energy `-κ²`, `κ > 0`, and angular momentum `l` has a reduced
radial function solving

`u'' = (l(l+1)/ρ² - 2/ρ + κ²) u`   on `(0, ∞)`.

We take the standard ansatz `u(ρ) = ρ^(l+1) e^(-κρ) Σ_k c_k ρ^k` with an everywhere convergent
power series and `c_0 ≠ 0` (`radialSeries`). Then:

- the series can be differentiated termwise (`hasDerivAt_psum`), and the radial equation turns
  into `ρ W'' + (2l + 2 - 2κρ) W' + (2 - 2κ(l + 1)) W = 0` for `W = Σ c_k ρ^k`; comparing
  coefficients (`coeff_eq_zero_of_psum`) gives the recursion
  `(k + 1)(k + 2l + 2) c_{k+1} = (2κ(k + l + 1) - 2) c_k` (`recursion_of_radial_ode`);
- if `κ(N + l + 1) = 1` for some `N`, the recursion stops after `c_N` and reproduces the Laguerre
  polynomial `L_N^(2l+1)(2κρ)`, so `u` is a multiple of `u_{νl}` with `ν = N + l + 1`
  (`radialSeries_eq_of_terminating`);
- otherwise all `c_k` are non-zero and eventually `c_{k+1}/c_k ≥ (3κ/2)/(k + 1)`, so
  `W(ρ) ≥ δ e^(3κρ/2) - (polynomial)`; then `u(ρ)² ≥ 1` for large `ρ` and `u` is not square
  integrable (`not_integrableOn_of_nonterminating`).

Together this is `radial_quantization`: normalisability forces `E = -1/ν²`.

What is assumed: the power series ansatz, i.e. that the solution regular at the origin is
`ρ^(l+1) e^(-κρ)` times an entire function. That every solution regular at the origin has this
form, and that the second, singular solution is excluded by the boundary condition at `ρ = 0`,
is not formalised here.

## ii. Key results

- `hasDerivAt_psum`, `coeff_eq_zero_of_psum`: termwise differentiation and the identity theorem
  for everywhere convergent power series on `(0, ∞)`.
- `recursion_of_radial_ode`: the coefficient recursion.
- `radialSeries_eq_of_terminating`: the terminating solutions are the hydrogen radial functions.
- `not_integrableOn_of_nonterminating`: non-terminating solutions are not normalisable.
- `radial_quantization`: the quantisation of the hydrogen levels.

## iii. Table of contents

- A. Power series with infinite radius of convergence
- B. The radial equation for a power series ansatz
- C. Terminating series: the Laguerre polynomials
- D. Non-terminating series are not normalisable
- E. Quantisation

## iv. References

- J. J. Sakurai and J. Napolitano, *Modern Quantum Mechanics*, 3rd ed., Cambridge University
  Press (2020), section 3.7.
- H. A. Bethe and E. E. Salpeter, *Quantum Mechanics of One- and Two-Electron Atoms*, Springer
  (1957).

## A. Power series with infinite radius of convergence

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Hydrogen

open MeasureTheory Set Filter Topology

/-- The coefficients `c` define a power series that converges absolutely on all of `ℝ`. -/
def EntireCoeff (c : ℕ → ℝ) : Prop := ∀ r : ℝ, 0 ≤ r → Summable fun k => |c k| * r ^ k

/-- The power series `Σ c_k x^k`. -/
def psum (c : ℕ → ℝ) (x : ℝ) : ℝ := ∑' k, c k * x ^ k

/-- The coefficients of the derivative, `(k + 1) c_{k+1}`. -/
def dcoeff (c : ℕ → ℝ) (k : ℕ) : ℝ := ((k : ℝ) + 1) * c (k + 1)

variable {c : ℕ → ℝ}

lemma succ_mul_pow_le_pow_succ {r : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    ((k : ℝ) + 1) * r ^ k ≤ (1 + r) ^ (k + 1) := by
  induction k with
  | zero => simp; linarith
  | succ k ih =>
    have h1 : r ^ (k + 1) ≤ (1 + r) ^ (k + 1) := pow_le_pow_left₀ hr (by linarith) _
    calc ((k + 1 : ℕ) + 1 : ℝ) * r ^ (k + 1) = r * (((k : ℝ) + 1) * r ^ k) + r ^ (k + 1) := by
          push_cast; ring
      _ ≤ r * (1 + r) ^ (k + 1) + (1 + r) ^ (k + 1) := by gcongr
      _ = (1 + r) ^ (k + 1 + 1) := by ring

lemma EntireCoeff.summable (hc : EntireCoeff c) (x : ℝ) : Summable fun k => c k * x ^ k := by
  refine Summable.of_norm_bounded (hc |x| (abs_nonneg x)) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]

lemma EntireCoeff.derivCoeff (hc : EntireCoeff c) : EntireCoeff (dcoeff c) := by
  intro r hr
  have h := (summable_nat_add_iff 1).mpr (hc (1 + r) (by linarith))
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) h
  rw [dcoeff, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
  calc ((k : ℝ) + 1) * |c (k + 1)| * r ^ k = |c (k + 1)| * (((k : ℝ) + 1) * r ^ k) := by ring
    _ ≤ |c (k + 1)| * (1 + r) ^ (k + 1) :=
      mul_le_mul_of_nonneg_left (succ_mul_pow_le_pow_succ hr k) (abs_nonneg _)

lemma EntireCoeff.shift (hc : EntireCoeff c) : EntireCoeff fun k => c (k + 1) := by
  intro r hr
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hc.derivCoeff r hr)
  rw [dcoeff, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
  have : |c (k + 1)| * r ^ k ≤ ((k : ℝ) + 1) * (|c (k + 1)| * r ^ k) :=
    le_mul_of_one_le_left (by positivity) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  linarith

lemma psum_eq_add (hc : EntireCoeff c) (x : ℝ) :
    psum c x = c 0 + x * psum (fun k => c (k + 1)) x := by
  rw [psum, (hc.summable x).tsum_eq_zero_add, psum, ← tsum_mul_left]
  simp only [pow_zero, mul_one]
  congr 1
  exact tsum_congr fun k => by ring

lemma psum_zero (c : ℕ → ℝ) : psum c 0 = c 0 := by
  rw [psum, tsum_eq_single 0 fun k hk => by simp [hk]]
  simp

/-- Termwise differentiation of an everywhere convergent power series. -/
lemma hasDerivAt_psum (hc : EntireCoeff c) (x : ℝ) :
    HasDerivAt (psum c) (psum (dcoeff c) x) x := by
  set R : ℝ := |x| + 1
  have hR : 0 ≤ R := by positivity
  have hu : Summable fun k => |c k| * ((k : ℝ) * R ^ (k - 1)) := by
    rw [← summable_nat_add_iff 1]
    refine (hc.derivCoeff R hR).congr fun k => ?_
    rw [dcoeff, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  have hd : HasDerivAt (fun z => ∑' k, c k * z ^ k) (∑' k, c k * ((k : ℝ) * x ^ (k - 1))) x := by
    refine hasDerivAt_tsum_of_isPreconnected (t := Metric.ball 0 R) (y₀ := 0) hu
      Metric.isOpen_ball (convex_ball 0 R).isPreconnected
      (fun k y _ => (hasDerivAt_pow k y).const_mul (c k)) (fun k y hy => ?_)
      (Metric.mem_ball_self (by positivity)) (hc.summable 0) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
      have hy' : |y| ≤ R := by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
        exact hy.le
      gcongr
    · rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
      linarith
  have hs : Summable fun k => c k * ((k : ℝ) * x ^ (k - 1)) := by
    refine Summable.of_norm_bounded hu fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    gcongr
    linarith
  rw [show psum c = fun z => ∑' k, c k * z ^ k from rfl]
  convert hd using 1
  rw [hs.tsum_eq_zero_add, psum]
  simp only [CharP.cast_eq_zero, zero_mul, mul_zero, zero_add, dcoeff, Nat.add_sub_cancel]
  exact tsum_congr fun k => by push_cast; ring

/-- A power series that vanishes on `(0, ∞)` has vanishing coefficients. -/
lemma coeff_eq_zero_of_psum (n : ℕ) : ∀ c : ℕ → ℝ, EntireCoeff c →
    (∀ x : ℝ, 0 < x → psum c x = 0) → c n = 0 := by
  induction n with
  | zero =>
    intro c hc h
    have h1 : Tendsto (psum c) (𝓝[>] 0) (𝓝 (psum c 0)) :=
      (hasDerivAt_psum hc 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (psum c) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun x hx => (h x hx).symm)
    rw [← psum_zero c]
    exact tendsto_nhds_unique h1 h2
  | succ n ih =>
    intro c hc h
    have h0 : c 0 = 0 := by
      have h1 : Tendsto (psum c) (𝓝[>] 0) (𝓝 (psum c 0)) :=
        (hasDerivAt_psum hc 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto (psum c) (𝓝[>] 0) (𝓝 0) :=
        tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun x hx => (h x hx).symm)
      rw [← psum_zero c]
      exact tendsto_nhds_unique h1 h2
    exact ih (fun k => c (k + 1)) hc.shift fun x hx => by
      have := h x hx
      rw [psum_eq_add hc, h0, zero_add] at this
      exact (mul_eq_zero.mp this).resolve_left hx.ne'

lemma EntireCoeff.unshift (h : EntireCoeff fun k => c (k + 1)) : EntireCoeff c := by
  intro r hr
  rw [← summable_nat_add_iff 1]
  exact ((h r hr).mul_left r).congr fun k => by rw [pow_succ]; ring

lemma EntireCoeff.add {c' : ℕ → ℝ} (hc : EntireCoeff c) (hc' : EntireCoeff c') :
    EntireCoeff fun k => c k + c' k := by
  intro r hr
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((hc r hr).add (hc' r hr))
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (by positivity)

lemma EntireCoeff.const_mul (hc : EntireCoeff c) (a : ℝ) : EntireCoeff fun k => a * c k := by
  intro r hr
  exact ((hc r hr).mul_left |a|).congr fun k => by rw [abs_mul]; ring

lemma psum_add {c' : ℕ → ℝ} (hc : EntireCoeff c) (hc' : EntireCoeff c') (x : ℝ) :
    psum (fun k => c k + c' k) x = psum c x + psum c' x := by
  rw [psum, psum, psum, ← (hc.summable x).tsum_add (hc'.summable x)]
  exact tsum_congr fun k => by ring

lemma psum_const_mul (c : ℕ → ℝ) (a x : ℝ) : psum (fun k => a * c k) x = a * psum c x := by
  rw [psum, psum, ← tsum_mul_left]
  exact tsum_congr fun k => by ring

lemma dcoeff_eq (c : ℕ → ℝ) : (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * c (k + 1)) = dcoeff c :=
  funext fun k => by rw [dcoeff]; push_cast; ring

lemma EntireCoeff.natMul (hc : EntireCoeff c) : EntireCoeff fun k => (k : ℝ) * c k := by
  refine EntireCoeff.unshift ?_
  rw [dcoeff_eq]
  exact hc.derivCoeff

/-- `x Σ_k (k + 1) c_{k+1} x^k = Σ_k k c_k x^k`. -/
lemma mul_psum_dcoeff (hc : EntireCoeff c) (x : ℝ) :
    x * psum (dcoeff c) x = psum (fun k => (k : ℝ) * c k) x := by
  rw [psum_eq_add hc.natMul x, dcoeff_eq]
  simp

/-!

## B. The radial equation for a power series ansatz

-/

/-- The ansatz `u(ρ) = ρ^(l+1) e^(-κρ) Σ_k c_k ρ^k` for a bound state of energy `-κ²`. -/
def radialSeries (κ : ℝ) (l : ℕ) (c : ℕ → ℝ) (ρ : ℝ) : ℝ :=
  ρ ^ (l + 1) * Real.exp (-(κ * ρ)) * psum c ρ

variable {κ : ℝ} {l : ℕ}

lemma hasDerivAt_exp_neg_mul (κ ρ : ℝ) :
    HasDerivAt (fun ρ => Real.exp (-(κ * ρ))) (Real.exp (-(κ * ρ)) * (-κ)) ρ := by
  simpa using ((hasDerivAt_id ρ).const_mul κ).neg.exp

/-- The first derivative of `radialSeries`. -/
def radialSeriesD (κ : ℝ) (l : ℕ) (c : ℕ → ℝ) (ρ : ℝ) : ℝ :=
  Real.exp (-(κ * ρ)) * ((((l : ℝ) + 1) * ρ ^ l - κ * ρ ^ (l + 1)) * psum c ρ +
    ρ ^ (l + 1) * psum (dcoeff c) ρ)

lemma hasDerivAt_radialSeries (hc : EntireCoeff c) (ρ : ℝ) :
    HasDerivAt (radialSeries κ l c) (radialSeriesD κ l c ρ) ρ := by
  have h := ((hasDerivAt_pow (l + 1) ρ).mul (hasDerivAt_exp_neg_mul κ ρ)).mul
    (hasDerivAt_psum hc ρ)
  refine h.congr_deriv ?_
  simp only [radialSeriesD, Nat.add_sub_cancel, Pi.mul_apply]
  push_cast
  ring

lemma hasDerivAt_radialSeriesD (hc : EntireCoeff c) (ρ : ℝ) :
    HasDerivAt (radialSeriesD κ l c) (Real.exp (-(κ * ρ)) *
      (-κ * ((((l : ℝ) + 1) * ρ ^ l - κ * ρ ^ (l + 1)) * psum c ρ +
        ρ ^ (l + 1) * psum (dcoeff c) ρ) +
      ((((l : ℝ) + 1) * (l * ρ ^ (l - 1)) - κ * (((l : ℝ) + 1) * ρ ^ l)) * psum c ρ +
        (((l : ℝ) + 1) * ρ ^ l - κ * ρ ^ (l + 1)) * psum (dcoeff c) ρ +
          ((((l : ℝ) + 1) * ρ ^ l) * psum (dcoeff c) ρ +
            ρ ^ (l + 1) * psum (dcoeff (dcoeff c)) ρ)))) ρ := by
  have hQ := (((hasDerivAt_pow l ρ).const_mul ((l : ℝ) + 1)).sub
    ((hasDerivAt_pow (l + 1) ρ).const_mul κ))
  have hB := (hQ.mul (hasDerivAt_psum hc ρ)).add
    ((hasDerivAt_pow (l + 1) ρ).mul (hasDerivAt_psum hc.derivCoeff ρ))
  have h := (hasDerivAt_exp_neg_mul κ ρ).mul hB
  refine h.congr_deriv ?_
  simp only [Nat.add_sub_cancel, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
  push_cast
  ring

/-- The radial operator applied to the ansatz, in terms of the series `W`, `W'`, `W''`. -/
lemma radial_identity (κ ρ W W₁ W₂ E : ℝ) (l : ℕ) (hρ : ρ ≠ 0) :
    E * (-κ * ((((l : ℝ) + 1) * ρ ^ l - κ * ρ ^ (l + 1)) * W + ρ ^ (l + 1) * W₁) +
      ((((l : ℝ) + 1) * (l * ρ ^ (l - 1)) - κ * (((l : ℝ) + 1) * ρ ^ l)) * W +
        (((l : ℝ) + 1) * ρ ^ l - κ * ρ ^ (l + 1)) * W₁ +
          ((((l : ℝ) + 1) * ρ ^ l) * W₁ + ρ ^ (l + 1) * W₂))) -
      ((l : ℝ) * (l + 1) / ρ ^ 2 - 2 / ρ + κ ^ 2) * (ρ ^ (l + 1) * E * W) =
    ρ ^ l * E * (ρ * W₂ + (2 * l + 2 - 2 * κ * ρ) * W₁ + (2 - 2 * κ * (l + 1)) * W) := by
  rcases l with _ | m
  · rw [Nat.zero_sub, pow_zero]
    push_cast
    field_simp
    ring
  · rw [show m + 1 - 1 = m by omega]
    push_cast
    field_simp
    ring

/-- **The coefficient recursion.** If the ansatz solves the radial equation with energy `-κ²`, the
coefficients satisfy `(k + 1)(k + 2l + 2) c_{k+1} = (2κ(k + l + 1) - 2) c_k`. -/
lemma recursion_of_radial_ode (hc : EntireCoeff c)
    (hode : ∀ ρ : ℝ, 0 < ρ → deriv (deriv (radialSeries κ l c)) ρ =
      ((l : ℝ) * (l + 1) / ρ ^ 2 - 2 / ρ + κ ^ 2) * radialSeries κ l c ρ) (k : ℕ) :
    ((k : ℝ) + 1) * (k + 2 * l + 2) * c (k + 1) = (2 * κ * (k + l + 1) - 2) * c k := by
  set d : ℕ → ℝ := fun k => (k : ℝ) * dcoeff c k + ((2 * (l : ℝ) + 2) * dcoeff c k +
    ((-2 * κ) * ((k : ℝ) * c k) + (2 - 2 * κ * ((l : ℝ) + 1)) * c k)) with hd
  have hdE : EntireCoeff d := hc.derivCoeff.natMul.add ((hc.derivCoeff.const_mul _).add
    ((hc.natMul.const_mul _).add (hc.const_mul _)))
  have hK : ∀ ρ : ℝ, 0 < ρ → psum d ρ = 0 := fun ρ hρ => by
    have h1 : deriv (radialSeries κ l c) = radialSeriesD κ l c :=
      funext fun x => (hasDerivAt_radialSeries hc x).deriv
    have h2 := hode ρ hρ
    rw [h1, (hasDerivAt_radialSeriesD hc ρ).deriv, radialSeries] at h2
    have hid := radial_identity κ ρ (psum c ρ) (psum (dcoeff c) ρ) (psum (dcoeff (dcoeff c)) ρ)
      (Real.exp (-(κ * ρ))) l hρ.ne'
    rw [show ρ ^ (l + 1) * Real.exp (-(κ * ρ)) * psum c ρ =
      ρ ^ (l + 1) * Real.exp (-(κ * ρ)) * psum c ρ from rfl, h2, sub_self] at hid
    have hpos : ρ ^ l * Real.exp (-(κ * ρ)) ≠ 0 := by positivity
    have hK0 := (mul_eq_zero.mp hid.symm).resolve_left hpos
    rw [hd, psum_add hc.derivCoeff.natMul _, psum_add (hc.derivCoeff.const_mul _) _,
      psum_add (hc.natMul.const_mul _) (hc.const_mul _), psum_const_mul, psum_const_mul,
      psum_const_mul, ← mul_psum_dcoeff hc.derivCoeff, ← mul_psum_dcoeff hc]
    · linear_combination hK0
    · exact (hc.natMul.const_mul _).add (hc.const_mul _)
    · exact (hc.derivCoeff.const_mul _).add ((hc.natMul.const_mul _).add (hc.const_mul _))
  have h := coeff_eq_zero_of_psum k d hdE hK
  simp only [hd, dcoeff] at h
  linear_combination h

/-!

## C. Terminating series: the Laguerre polynomials

-/

/-- The coefficient recursion `(k + 1)(k + 2l + 2) c_{k+1} = (2κ(k + l + 1) - 2) c_k`. -/
abbrev RadialRec (κ : ℝ) (l : ℕ) (c : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ((k : ℝ) + 1) * (k + 2 * l + 2) * c (k + 1) = (2 * κ * (k + l + 1) - 2) * c k

/-- If `κ (N + l + 1) = 1`, the recursion terminates after `c_N` and reproduces the coefficients
of `L_N^(2l+1)(2κρ)`. -/
lemma coeff_of_terminating (hrec : RadialRec κ l c) {N : ℕ} (hN : κ * (N + l + 1) = 1) :
    (∀ k, k ≤ N → c k = c 0 / laguerreCoeff N (2 * l + 1) 0 * laguerreCoeff N (2 * l + 1) k *
      (2 * κ) ^ k) ∧ ∀ k, N < k → c k = 0 := by
  have hL0 : laguerreCoeff N (2 * l + 1) 0 ≠ 0 := by
    simp only [laguerreCoeff, pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, div_one,
      Nat.sub_zero]
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  refine ⟨fun k => ?_, fun k hk => ?_⟩
  · induction k with
    | zero => intro _; field_simp
    | succ k ih =>
      intro hk
      have ih := ih (by omega)
      have hL := laguerreCoeff_succ_mul (N := N) (α := 2 * l + 1) (show k < N by omega)
      have hr := hrec k
      have hpos : ((k : ℝ) + 1) * (k + 2 * l + 2) ≠ 0 := by positivity
      apply mul_left_cancel₀ hpos
      rw [hr, ih, show (2 * κ * (k + l + 1) - 2) = -2 * κ * ((N : ℝ) - k) by
        linear_combination 2 * hN]
      push_cast at hL
      linear_combination (-(c 0 / laguerreCoeff N (2 * l + 1) 0 * (2 * κ) ^ (k + 1))) * hL
  · obtain ⟨j, rfl⟩ : ∃ j, k = N + 1 + j := ⟨k - (N + 1), by omega⟩
    induction j with
    | zero =>
      have hr := hrec N
      rw [show 2 * κ * ((N : ℝ) + l + 1) - 2 = 0 by linear_combination 2 * hN, zero_mul] at hr
      have hpos : ((N : ℝ) + 1) * (N + 2 * l + 2) ≠ 0 := by positivity
      exact (mul_eq_zero.mp hr).resolve_left hpos
    | succ j ih =>
      have hr := hrec (N + 1 + j)
      rw [ih (by omega), mul_zero] at hr
      have hpos : (((N + 1 + j : ℕ) : ℝ) + 1) * ((N + 1 + j : ℕ) + 2 * l + 2) ≠ 0 := by
        positivity
      exact (mul_eq_zero.mp hr).resolve_left hpos

/-- In the terminating case the ansatz is a multiple of the hydrogen radial function. -/
lemma radialSeries_eq_of_terminating (hrec : RadialRec κ l c) {N : ℕ}
    (hN : κ * (N + l + 1) = 1) (ρ : ℝ) :
    radialSeries κ l c ρ =
      c 0 / laguerreCoeff N (2 * l + 1) 0 * radialU (N + l + 1) l ρ := by
  obtain ⟨h1, h2⟩ := coeff_of_terminating hrec hN
  have hν : ((N + l + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hκ : κ = 1 / ((N + l + 1 : ℕ) : ℝ) := by
    push_cast
    field_simp
    linarith
  have hps : psum c ρ = c 0 / laguerreCoeff N (2 * l + 1) 0 *
      (laguerre N (2 * l + 1)).eval (2 * κ * ρ) := by
    rw [psum, tsum_eq_sum (s := Finset.range (N + 1)) fun k hk => by
      rw [h2 k (by simpa using hk), zero_mul], eval_laguerre, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [h1 k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)), mul_pow]
    ring
  rw [radialSeries, radialU, eval_radialPoly, hps, show N + l + 1 - l - 1 = N by omega, hκ]
  ring_nf

/-!

## D. Non-terminating series are not normalisable

-/

lemma tendsto_pow_mul_exp_neg_mul (hκ : 0 < κ) (k : ℕ) :
    Tendsto (fun ρ : ℝ => ρ ^ k * Real.exp (-(κ * ρ))) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
    (tendsto_id.const_mul_atTop hκ)
  have h' := h.const_mul (κ ^ k)⁻¹
  rw [mul_zero] at h'
  refine h'.congr fun ρ => ?_
  simp only [Function.comp_apply, id]
  rw [mul_pow]
  field_simp

lemma coeff_ne_zero (hrec : RadialRec κ l c) (hnt : ∀ N : ℕ, κ * (N + l + 1) ≠ 1)
    (h0 : c 0 ≠ 0) :
    ∀ k, c k ≠ 0 := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    intro hk
    have hr := hrec k
    rw [hk, mul_zero] at hr
    have hf : 2 * κ * ((k : ℝ) + l + 1) - 2 ≠ 0 := fun h => hnt k (by linarith)
    exact ih ((mul_eq_zero.mp hr.symm).resolve_left hf)

/-- **Non-terminating series grow like `e^(3κρ/2)`.** Then `u = ρ^(l+1) e^(-κρ) Σ c_k ρ^k` is not
square integrable. -/
lemma not_integrableOn_of_nonterminating (hκ : 0 < κ) (hc : EntireCoeff c)
    (hrec : RadialRec κ l c) (hnt : ∀ N : ℕ, κ * (N + l + 1) ≠ 1) (h0 : c 0 ≠ 0) :
    ¬IntegrableOn (fun ρ => radialSeries κ l c ρ ^ 2) (Ioi 0) := by
  intro hint
  have hne := coeff_ne_zero hrec hnt h0
  set K : ℕ := ⌈(2 * κ * ((l : ℝ) + 1) + 4) / κ⌉₊ with hK
  set lam : ℝ := 3 * κ / 2 with hlam
  have hlam0 : 0 < lam := by positivity
  have hcK := hne K
  set a : ℕ → ℝ := fun k => (c K)⁻¹ * c k with ha
  set δ : ℝ := (K.factorial : ℝ) / lam ^ K with hδ
  have hδ0 : 0 < δ := by positivity
  -- from `K` on, `a_{k+1} = r_k a_k` with `r_k ≥ λ/(k + 1)`
  have hstep : ∀ k, K ≤ k → ∃ r : ℝ, lam / ((k : ℝ) + 1) ≤ r ∧ a (k + 1) = r * a k := by
    intro k hk
    have hkK : (2 * κ * ((l : ℝ) + 1) + 4) / κ ≤ k :=
      le_trans (Nat.le_ceil _) (by rw [← hK]; exact_mod_cast hk)
    have hkK' : 2 * κ * ((l : ℝ) + 1) + 4 ≤ κ * k := by
      rw [div_le_iff₀ hκ] at hkK
      linarith
    have hpos : 0 < ((k : ℝ) + 1) * (k + 2 * l + 2) := by positivity
    have hck : c (k + 1) =
        (2 * κ * (k + l + 1) - 2) / (((k : ℝ) + 1) * (k + 2 * l + 2)) * c k := by
      rw [div_mul_eq_mul_div, eq_div_iff hpos.ne']
      linear_combination hrec k
    refine ⟨(2 * κ * (k + l + 1) - 2) / (((k : ℝ) + 1) * (k + 2 * l + 2)), ?_, ?_⟩
    · rw [div_le_div_iff₀ (by positivity) hpos, hlam]
      nlinarith
    · simp only [ha]
      rw [hck]
      ring
  -- hence `a_k ≥ δ λ^k / k!` for `k ≥ K`
  have hlow : ∀ j : ℕ, δ * lam ^ (K + j) / ((K + j).factorial : ℝ) ≤ a (K + j) := by
    intro j
    induction j with
    | zero =>
      simp only [add_zero, ha, hδ]
      rw [inv_mul_cancel₀ hcK]
      field_simp
      rfl
    | succ j ih =>
      obtain ⟨r, hr, hr'⟩ := hstep (K + j) (by omega)
      rw [← add_assoc, hr']
      have hX : 0 ≤ δ * lam ^ (K + j) / ((K + j).factorial : ℝ) := by positivity
      calc δ * lam ^ (K + j + 1) / ((K + j + 1).factorial : ℝ) =
            lam / (((K + j : ℕ) : ℝ) + 1) * (δ * lam ^ (K + j) / ((K + j).factorial : ℝ)) := by
            rw [Nat.factorial_succ]
            push_cast
            field_simp
            ring
        _ ≤ r * a (K + j) := mul_le_mul hr ih hX (le_trans (by positivity) hr)
  -- lower bound for the series
  set Q : ℝ → ℝ := fun ρ => ∑ k ∈ Finset.range K,
    (|a k| * ρ ^ k + δ * ((lam * ρ) ^ k / (k.factorial : ℝ))) with hQ
  have hW : ∀ ρ : ℝ, 0 < ρ → δ * Real.exp (lam * ρ) - Q ρ ≤ (c K)⁻¹ * psum c ρ := by
    intro ρ hρ
    have hexp : Real.exp (lam * ρ) = ∑' k : ℕ, (lam * ρ) ^ k / (k.factorial : ℝ) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    have hs1 : Summable fun k : ℕ => δ * ((lam * ρ) ^ k / (k.factorial : ℝ)) :=
      (Real.summable_pow_div_factorial (lam * ρ)).mul_left δ
    set g : ℕ → ℝ := fun k => if k < K then |a k| * ρ ^ k + δ * ((lam * ρ) ^ k /
      (k.factorial : ℝ)) else 0 with hg
    have hgsum : ∑' k, g k = Q ρ := by
      rw [tsum_eq_sum (s := Finset.range K) fun k hk => by
        simp only [hg, Finset.mem_range] at hk ⊢
        rw [ite_eq_right hk]]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [hg, ite_eq_left (Finset.mem_range.mp hk)]
    have hs2 : Summable g := summable_of_ne_finset_zero (s := Finset.range K) fun k hk => by
      simp only [hg, Finset.mem_range] at hk ⊢
      rw [ite_eq_right hk]
    have hs3 : Summable fun k => a k * ρ ^ k := (hc.const_mul (c K)⁻¹).summable ρ
    have hle : ∀ k, δ * ((lam * ρ) ^ k / (k.factorial : ℝ)) - g k ≤ a k * ρ ^ k := by
      intro k
      simp only [hg]
      split_ifs with hk
      · have : -(|a k| * ρ ^ k) ≤ a k * ρ ^ k := by
          rw [neg_le, ← neg_mul]
          exact mul_le_mul_of_nonneg_right (neg_le_abs _) (by positivity)
        linarith
      · obtain ⟨j, rfl⟩ : ∃ j, k = K + j := ⟨k - K, by omega⟩
        have := mul_le_mul_of_nonneg_right (hlow j) (by positivity : (0 : ℝ) ≤ ρ ^ (K + j))
        rw [mul_pow, sub_zero]
        calc δ * (lam ^ (K + j) * ρ ^ (K + j) / ((K + j).factorial : ℝ)) =
            δ * lam ^ (K + j) / ((K + j).factorial : ℝ) * ρ ^ (K + j) := by ring
          _ ≤ _ := this
    calc δ * Real.exp (lam * ρ) - Q ρ =
          ∑' k, (δ * ((lam * ρ) ^ k / (k.factorial : ℝ)) - g k) := by
          rw [hs1.tsum_sub hs2, tsum_mul_left, hgsum, hexp]
      _ ≤ ∑' k, a k * ρ ^ k := hs1.sub hs2 |>.tsum_le_tsum hle hs3
      _ = (c K)⁻¹ * psum c ρ := by rw [← psum_const_mul]; rfl
  -- asymptotics
  have hQlim : Tendsto (fun ρ => Q ρ * Real.exp (-(κ * ρ))) atTop (𝓝 0) := by
    have : (fun ρ => Q ρ * Real.exp (-(κ * ρ))) = fun ρ => ∑ k ∈ Finset.range K,
        ((|a k| + δ * lam ^ k / (k.factorial : ℝ)) * (ρ ^ k * Real.exp (-(κ * ρ)))) := by
      funext ρ
      rw [hQ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_pow]
      ring
    rw [this]
    have h0 : (0 : ℝ) = ∑ k ∈ Finset.range K, ((|a k| + δ * lam ^ k / (k.factorial : ℝ)) * 0) := by
      simp
    rw [h0]
    exact tendsto_finsetSum _ fun k _ => (tendsto_pow_mul_exp_neg_mul hκ k).const_mul _
  have hF : Tendsto (fun ρ => δ * Real.exp ((lam - κ) * ρ) + -(Q ρ * Real.exp (-(κ * ρ))))
      atTop atTop := by
    refine Tendsto.atTop_add ?_ (by simpa using hQlim.neg)
    exact (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by
      rw [hlam]; linarith))).const_mul_atTop hδ0
  have hev := (hF.eventually_ge_atTop (|c K|)⁻¹).and (eventually_ge_atTop (1 : ℝ))
  obtain ⟨R, hR⟩ := eventually_atTop.mp hev
  have hbig : ∀ ρ ∈ Ioi (max R 1), 1 ≤ radialSeries κ l c ρ ^ 2 := by
    intro ρ hρ
    have hρR : R ≤ ρ := le_trans (le_max_left _ _) (le_of_lt hρ)
    obtain ⟨h1, h2⟩ := hR ρ hρR
    have hρ0 : 0 < ρ := by linarith
    have hlow' := hW ρ hρ0
    have he : Real.exp (-(κ * ρ)) * Real.exp (lam * ρ) = Real.exp ((lam - κ) * ρ) := by
      rw [← Real.exp_add]; ring_nf
    have hkey : (|c K|)⁻¹ ≤ Real.exp (-(κ * ρ)) * ((c K)⁻¹ * psum c ρ) := by
      calc (|c K|)⁻¹ ≤ δ * Real.exp ((lam - κ) * ρ) + -(Q ρ * Real.exp (-(κ * ρ))) := h1
        _ = Real.exp (-(κ * ρ)) * (δ * Real.exp (lam * ρ) - Q ρ) := by rw [← he]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow' (Real.exp_pos _).le
    have habs : 1 ≤ |Real.exp (-(κ * ρ)) * psum c ρ| := by
      have h3 : (|c K|)⁻¹ ≤ |Real.exp (-(κ * ρ)) * psum c ρ| * (|c K|)⁻¹ := by
        calc (|c K|)⁻¹ ≤ Real.exp (-(κ * ρ)) * ((c K)⁻¹ * psum c ρ) := hkey
          _ ≤ |Real.exp (-(κ * ρ)) * ((c K)⁻¹ * psum c ρ)| := le_abs_self _
          _ = |Real.exp (-(κ * ρ)) * psum c ρ| * (|c K|)⁻¹ := by
            rw [abs_mul, abs_mul, abs_mul, abs_inv]; ring
      have hpos : 0 < (|c K|)⁻¹ := by positivity
      nlinarith
    have hρl : 1 ≤ ρ ^ (l + 1) := one_le_pow₀ (by linarith)
    rw [radialSeries, mul_assoc, mul_pow]
    have h4 : 1 ≤ (Real.exp (-(κ * ρ)) * psum c ρ) ^ 2 := by
      rw [← sq_abs]; nlinarith
    nlinarith [pow_le_pow_left₀ zero_le_one hρl 2]
  have hint' : IntegrableOn (fun ρ => radialSeries κ l c ρ ^ 2) (Ioi (max R 1)) :=
    hint.mono_set (Ioi_subset_Ioi (by positivity))
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi (max R 1)) := by
    refine Integrable.mono' hint' aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ρ hρ => ?_)
    rw [Real.norm_eq_abs, abs_one]
    exact hbig ρ hρ
  rw [integrableOn_const_iff] at h1
  rcases h1 with h1 | h1
  · simp at h1
  · rw [Real.volume_Ioi] at h1
    exact (lt_irrefl _ h1)

/-!

## E. Quantisation

-/

/-- **Quantisation of the hydrogen levels.** Let `u(ρ) = ρ^(l+1) e^(-κρ) Σ_k c_k ρ^k` with an
everywhere convergent power series, `c_0 ≠ 0` and `κ > 0`, solve the radial equation
`u'' = (l(l+1)/ρ² - 2/ρ + κ²) u` on `(0, ∞)`, i.e. be an eigenfunction with energy `-κ²` in Rydberg
units. If `u` is square integrable, then `κ = 1/ν` for a natural number `ν > l`, so the energy is
the Bohr level `-1/ν²`, and `u` is a multiple of the radial function `u_{νl}`. -/
lemma radial_quantization (hκ : 0 < κ) (hc : EntireCoeff c) (h0 : c 0 ≠ 0)
    (hode : ∀ ρ : ℝ, 0 < ρ → deriv (deriv (radialSeries κ l c)) ρ =
      ((l : ℝ) * (l + 1) / ρ ^ 2 - 2 / ρ + κ ^ 2) * radialSeries κ l c ρ)
    (hint : IntegrableOn (fun ρ => radialSeries κ l c ρ ^ 2) (Ioi 0)) :
    ∃ ν : ℕ, l < ν ∧ κ = 1 / (ν : ℝ) ∧
      ∃ C : ℝ, ∀ ρ, radialSeries κ l c ρ = C * radialU ν l ρ := by
  have hrec := recursion_of_radial_ode hc hode
  by_cases h : ∃ N : ℕ, κ * (N + l + 1) = 1
  · obtain ⟨N, hN⟩ := h
    refine ⟨N + l + 1, by omega, ?_, _, radialSeries_eq_of_terminating hrec hN⟩
    have : ((N + l + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    linarith
  · simp only [not_exists] at h
    exact absurd hint (not_integrableOn_of_nonterminating hκ hc hrec h h0)

end PhyslibAlpha.Hydrogen
