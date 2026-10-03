/-
Copyright (c) 2026 Dwanith C. Jayanth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dwanith C. Jayanth
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Physlib.QuantumMechanics.Blackbody.PlancksLaw

/-!

# Wien's displacement law, derived from Planck's law

## i. Overview

Wien's displacement law states that the peak of the blackbody spectrum shifts
inversely with temperature. In wavelength form: if `λ₁` maximizes
`B(λ, T₁)` and `λ₂` maximizes `B(λ, T₂)`, then

    `λ₁ T₁ = λ₂ T₂ = h c / (kB x₅)`,

where `x₅ ≈ 4.96511` is the unique positive solution of the transcendental
equation `x = 5 (1 - e⁻ˣ)`. In frequency form:

    `ν₁ / T₁ = ν₂ / T₂ = kB x₃ / h`,

where `x₃ ≈ 2.82144` is the unique positive solution of `x = 3 (1 - e⁻ˣ)`.
The two constants differ because the "peak" depends on the parametrization.

## ii. Key results

- `wienH`: the auxiliary function `h(x) = x - n (1 - e⁻ˣ)` whose positive zeros
  are the critical points of the Planck profile.
- `hasDerivAt_wienH`: its derivative is `1 - n e⁻ˣ`.
- `wienH_strictMonoOn` / `wienH_strictAntiOn`: monotonicity on either side of
  `log n`.
- `wien_exists_root`: existence of a root in `(log n, n)` for `n > 1`.
- `wien_unique_pos`: uniqueness of the positive root.
- `wienRoot`: the unique positive root, with `wienRoot_gt_log`, `wienRoot_lt`,
  `wienRoot_eq`, `wienRoot_pos`, `wienRoot_unique`.
- `wienConstant5` / `wienConstant3`: the named physical constants `x₅`, `x₃`,
  with `wienConstant5_mem`, `wienConstant3_mem`, `wienConstant5_pos`,
  `wienConstant3_pos`, `wienConstant5_ne_wienConstant3`.
- `wienRoot_five_mem`: `4 < wienRoot 5 < 5` (numerically `4.9651142317…`).
- `wienRoot_three_mem`: `2 < wienRoot 3 < 3` (numerically `2.8214393721…`).
- `wienProfile_crit_iff`: critical points of `xⁿ / (eˣ - 1)` are exactly the
  solutions of the Wien equation.
- `wienH_neg_on_Ioo` / `wienH_pos_on_Ioi`: sign of the auxiliary function
  on either side of the root.
- `wienProfile_deriv_eq`: factored derivative, showing `f'` has the opposite
  sign of `h`.
- `wienProfile_strictMonoOn` / `wienProfile_strictAntiOn`: the profile rises
  on `(0, x*]` and falls on `[x*, ∞)`.
- `wienProfile_isMaxOn`: the Wien root is the unique global maximizer —
  the "peak" of the spectrum.
- `wienProfile_continuousOn`: continuity of the profile on `(0, ∞)`.
- `wienProfile_tendsto_zero_atTop` / `wienProfile_tendsto_nhdsWithin_zero`:
  the profile vanishes at `∞` and at `0` (for `n ≥ 2`).
- `wave_crit_iff` / `freq_crit_iff`: critical points of the Planck curves.
- `waveVar_tendsto_nhdsWithin_atTop` / `waveVar_tendsto_atTop_nhdsWithin` /
  `freqVar_tendsto_atTop_atTop` / `freqVar_tendsto_nhdsWithin`: the
  dimensionless variables at the ends of the physical domain.
- `spectralRadianceWave_continuousOn` / `spectralRadianceFreq_continuousOn`:
  continuity of the physical curves on `(0, ∞)`.
- `spectralRadianceWave_tendsto_zero_atTop` /
  `spectralRadianceWave_tendsto_nhdsWithin_zero` /
  `spectralRadianceFreq_tendsto_zero_atTop` /
  `spectralRadianceFreq_tendsto_nhdsWithin_zero`: the curves vanish at both
  ends of the physical domain.
- `spectralRadianceWave_isMaxOn` / `spectralRadianceFreq_isMaxOn`: the
  critical wavelengths/frequencies are global maxima.
- `spectralRadianceWave_bddAbove` / `spectralRadianceFreq_bddAbove`:
  boundedness on `(0, ∞)`.
- `wien_displacement_wave` / `wien_displacement_freq`: the displacement laws
  `λ₁ T₁ = λ₂ T₂` and `ν₁ / T₁ = ν₂ / T₂`.
- `wien_peak_product` / `wien_peak_ratio`: the constant values
  `λ T = h c / (kB x₅)` and `ν / T = kB x₃ / h`.
- `wien_roots_differ`: the wavelength and frequency peaks are governed by
  different constants.

## iii. Table of contents

- A. The Wien auxiliary function and its derivative
- B. Monotonicity and the unique positive root
- C. Numerical enclosures for `n = 5` and `n = 3`
- C'. Named Wien constants
- D. Critical points of the Planck profile `xⁿ / (eˣ - 1)`
- D'. Profile behavior: sign, monotonicity, global maximum, asymptotics
- E. Critical points of the Planck curves
- E'. Physical curves: continuity, limits, global maxima, boundedness
- F. Wien's displacement laws

## iv. References

* https://en.wikipedia.org/wiki/Wien%27s_displacement_law
* W. Wien, "Eine neue Beziehung der Strahlung schwarzer Körper zum zweiten
  Hauptsatz der Wärmetheorie", Sitzungsber. Preuss. Akad. Wiss. (1893).
-/

@[expose] public section
noncomputable section

namespace Blackbody

open Set Filter Topology

/-- `(1 : ℝ) < 5`. Repeated throughout the file to avoid `by norm_num` clutter. -/
private lemma five_gt_one : (1 : ℝ) < 5 := by norm_num

/-- `(1 : ℝ) < 3`. Repeated throughout the file to avoid `by norm_num` clutter. -/
private lemma three_gt_one : (1 : ℝ) < 3 := by norm_num

/-- `1 ≤ (5 : ℕ)`. For `wienProfile_crit_iff` applications. -/
private lemma five_ge_one : 1 ≤ (5 : ℕ) := by norm_num

/-- `1 ≤ (3 : ℕ)`. For `wienProfile_crit_iff` applications. -/
private lemma three_ge_one : 1 ≤ (3 : ℕ) := by norm_num

/-- `(0 : ℝ) < 5`. -/
private lemma five_pos : (0 : ℝ) < 5 := lt_trans zero_lt_one five_gt_one

/-- `(0 : ℝ) < 3`. -/
private lemma three_pos : (0 : ℝ) < 3 := lt_trans zero_lt_one three_gt_one

/-- `(0 : ℝ) ≤ 2.7182818283`. Lower-bound constant for `Real.exp 1`. -/
private lemma expApprox_nonneg : (0 : ℝ) ≤ 2.7182818283 := by norm_num

/-!

## A. The Wien auxiliary function and its derivative

Setting `dB/dλ = 0` for the wavelength form (resp. `dB/dν = 0` for the frequency
form) and writing `x = h c / (λ kB T)` (resp. `x = h ν / (kB T)`) reduces the
extremum condition to `x = n (1 - e⁻ˣ)` with `n = 5` (resp. `n = 3`).
We study `h(x) = x - n (1 - e⁻ˣ)`.
-/

/-- The Wien auxiliary function `h(x) = x - n (1 - e⁻ˣ)`. Its zeros are the
  solutions of the Wien transcendental equation `x = n (1 - e⁻ˣ)`. -/
noncomputable def wienH (n x : ℝ) : ℝ := x - n * (1 - Real.exp (-x))

/-- Zero is always a (trivial) zero of the auxiliary function. -/
lemma wienH_zero (n : ℝ) : wienH n 0 = 0 := by
  simp [wienH]

/-- The auxiliary function is continuous. -/
lemma wienH_continuous (n : ℝ) : Continuous (wienH n) := by
  unfold wienH
  fun_prop

/-- Derivative of the auxiliary function: `h'(x) = 1 - n e⁻ˣ`. -/
lemma hasDerivAt_wienH (n x : ℝ) : HasDerivAt (wienH n) (1 - n * Real.exp (-x)) x := by
  unfold wienH
  have h1 : HasDerivAt (fun x : ℝ => -x) (-1) x := (hasDerivAt_id' x).neg
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-x) * -1) x :=
    (Real.hasDerivAt_exp (-x)).comp x h1
  have h3 : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) (0 - Real.exp (-x) * -1) x :=
    (hasDerivAt_const x (1 : ℝ)).sub h2
  have h4 : HasDerivAt (fun x : ℝ => n * (1 - Real.exp (-x)))
      (n * (0 - Real.exp (-x) * -1)) x := h3.const_mul n
  have h5 : HasDerivAt (fun x : ℝ => x - n * (1 - Real.exp (-x)))
      (1 - n * (0 - Real.exp (-x) * -1)) x := (hasDerivAt_id' x).sub h4
  have heq : (1 : ℝ) - n * (0 - Real.exp (-x) * -1) = 1 - n * Real.exp (-x) := by ring
  exact h5.congr_deriv heq

/-- The derivative is negative exactly below `log n`. -/
lemma wienH_deriv_neg_iff (n x : ℝ) (hn : 0 < n) :
    1 - n * Real.exp (-x) < 0 ↔ x < Real.log n := by
  have hbase : (1 : ℝ) - n * Real.exp (-x) < 0 ↔ 1 < n * Real.exp (-x) := by
    constructor <;> intro h <;> linarith
  rw [hbase, Real.exp_neg, ← div_eq_mul_inv, lt_div_iff₀ (Real.exp_pos x), one_mul]
  conv_lhs => rw [← Real.exp_log hn]
  rw [StrictMono.lt_iff_lt Real.exp_strictMono]

/-- The derivative is positive exactly above `log n`. -/
lemma wienH_deriv_pos_iff (n x : ℝ) (hn : 0 < n) :
    0 < 1 - n * Real.exp (-x) ↔ Real.log n < x := by
  have hbase : (0 : ℝ) < 1 - n * Real.exp (-x) ↔ n * Real.exp (-x) < 1 := by
    constructor <;> intro h <;> linarith
  rw [hbase, Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos x), one_mul]
  conv_lhs => rw [← Real.exp_log hn]
  rw [StrictMono.lt_iff_lt Real.exp_strictMono]

/-!

## B. Monotonicity and the unique positive root

Since `h'(x) = 1 - n e⁻ˣ` changes sign once (at `x = log n`), `h` strictly
decreases on `(-∞, log n]` and strictly increases on `[log n, ∞)`. Combined
with `h(0) = 0`, `h(log n) < 0` and `h(n) > 0`, this yields exactly one
positive root, located in `(log n, n)`.
-/

/-- `h` is strictly increasing on `[log n, ∞)`. -/
lemma wienH_strictMonoOn (n : ℝ) (hn : 1 < n) :
    StrictMonoOn (wienH n) (Ici (Real.log n)) := by
  have hn0 : 0 < n := lt_trans zero_lt_one hn
  refine strictMonoOn_of_deriv_pos (convex_Ici _) (wienH_continuous n).continuousOn ?_
  intro x hx
  rw [interior_Ici] at hx
  rw [(hasDerivAt_wienH n x).deriv]
  exact (wienH_deriv_pos_iff n x hn0).mpr hx

/-- `h` is strictly decreasing on `(-∞, log n]`. -/
lemma wienH_strictAntiOn (n : ℝ) (hn : 1 < n) :
    StrictAntiOn (wienH n) (Iic (Real.log n)) := by
  have hn0 : 0 < n := lt_trans zero_lt_one hn
  refine strictAntiOn_of_deriv_neg (convex_Iic _) (wienH_continuous n).continuousOn ?_
  intro x hx
  rw [interior_Iic] at hx
  rw [(hasDerivAt_wienH n x).deriv]
  exact (wienH_deriv_neg_iff n x hn0).mpr hx

/-- `h(log n) < 0` for `n > 1` (from `log n + 1 < n`). -/
lemma wienH_at_log_neg (n : ℝ) (hn : 1 < n) : wienH n (Real.log n) < 0 := by
  have hnPos : 0 < n := lt_trans zero_lt_one hn
  have hn0 : n ≠ 0 := ne_of_gt hnPos
  have hlog_pos : 0 < Real.log n := Real.log_pos hn
  have hexp : Real.log n + 1 < Real.exp (Real.log n) :=
    Real.add_one_lt_exp (ne_of_gt hlog_pos)
  rw [Real.exp_log hnPos] at hexp
  have hexpNeg : Real.exp (-Real.log n) = 1 / n := by
    rw [Real.exp_neg, Real.exp_log hnPos, one_div]
  have hnn : n * (1 - 1 / n) = n - 1 := by
    rw [mul_sub, mul_one, mul_one_div, div_self hn0]
  unfold wienH
  rw [hexpNeg, hnn]
  linarith

/-- `h(n) = n e⁻ⁿ > 0` for `n > 1`. -/
lemma wienH_at_self_pos (n : ℝ) (hn : 1 < n) : 0 < wienH n n := by
  have hnPos : 0 < n := lt_trans zero_lt_one hn
  have hpos : 0 < n * Real.exp (-n) := mul_pos hnPos (Real.exp_pos _)
  have heq : n - n * (1 - Real.exp (-n)) = n * Real.exp (-n) := by ring
  unfold wienH
  rw [heq]
  exact hpos

/-- Existence of a root in `(log n, n)` for `n > 1`, by the intermediate value
  theorem applied on `[log n, n]`. -/
lemma wien_exists_root (n : ℝ) (hn : 1 < n) :
    ∃ r, Real.log n < r ∧ r < n ∧ wienH n r = 0 := by
  have hnPos : 0 < n := lt_trans zero_lt_one hn
  have hlog_neg : wienH n (Real.log n) < 0 := wienH_at_log_neg n hn
  have hself_pos : 0 < wienH n n := wienH_at_self_pos n hn
  have hlog : Real.log n + 1 < n := by
    have hexp : Real.log n + 1 < Real.exp (Real.log n) :=
      Real.add_one_lt_exp (ne_of_gt (Real.log_pos hn))
    rwa [Real.exp_log hnPos] at hexp
  have hlt : Real.log n < n := by linarith
  have hcont : ContinuousOn (wienH n) (Icc (Real.log n) n) :=
    (wienH_continuous n).continuousOn
  have hmem : (0 : ℝ) ∈ Ioo (wienH n (Real.log n)) (wienH n n) :=
    ⟨hlog_neg, hself_pos⟩
  obtain ⟨r, hrmem, hreq⟩ := intermediate_value_Ioo (le_of_lt hlt) hcont hmem
  exact ⟨r, hrmem.1, hrmem.2, hreq⟩

/-- Uniqueness of the positive root: any positive zero coincides with a root in
  `(log n, n)`. On `(0, log n]` the function is strictly below `h(0) = 0`, and
  on `[log n, ∞)` it is strictly monotone. -/
lemma wien_unique_pos (n : ℝ) (hn : 1 < n) (x : ℝ) (hx : 0 < x)
    (hx0 : wienH n x = 0) (r : ℝ) (hr1 : Real.log n < r)
    (hr0 : wienH n r = 0) :
    x = r := by
  rcases le_total x (Real.log n) with hle | hge
  · have hanti := wienH_strictAntiOn n hn
    have h0mem : (0 : ℝ) ∈ Iic (Real.log n) :=
      mem_Iic.mpr (le_trans hx.le hle)
    have hxmem : x ∈ Iic (Real.log n) := mem_Iic.mpr hle
    have hlt' : wienH n x < wienH n 0 := hanti h0mem hxmem hx
    rw [wienH_zero, hx0] at hlt'
    exact absurd hlt' (lt_irrefl 0)
  · have hmono := wienH_strictMonoOn n hn
    have hxmem : x ∈ Ici (Real.log n) := mem_Ici.mpr hge
    have hrmem : r ∈ Ici (Real.log n) := mem_Ici.mpr hr1.le
    exact hmono.injOn hxmem hrmem (by rw [hx0, hr0])

/-- The unique positive solution of the Wien equation `x = n (1 - e⁻ˣ)`. -/
noncomputable def wienRoot (n : ℝ) (hn : 1 < n) : ℝ :=
  Classical.choose (wien_exists_root n hn)

/-- The Wien root lies above `log n`. -/
lemma wienRoot_gt_log (n : ℝ) (hn : 1 < n) : Real.log n < wienRoot n hn :=
  (Classical.choose_spec (wien_exists_root n hn)).1

/-- The Wien root lies below `n`. -/
lemma wienRoot_lt (n : ℝ) (hn : 1 < n) : wienRoot n hn < n :=
  (Classical.choose_spec (wien_exists_root n hn)).2.1

/-- The Wien root satisfies the Wien equation. -/
lemma wienRoot_eq (n : ℝ) (hn : 1 < n) : wienH n (wienRoot n hn) = 0 :=
  (Classical.choose_spec (wien_exists_root n hn)).2.2

/-- The Wien root is positive. -/
lemma wienRoot_pos (n : ℝ) (hn : 1 < n) : 0 < wienRoot n hn :=
  lt_trans (Real.log_pos hn) (wienRoot_gt_log n hn)

/-- Any positive solution of the Wien equation equals the Wien root. -/
lemma wienRoot_unique (n : ℝ) (hn : 1 < n) (x : ℝ) (hx : 0 < x)
    (hx0 : wienH n x = 0) : x = wienRoot n hn :=
  wien_unique_pos n hn x hx hx0 _ (wienRoot_gt_log n hn) (wienRoot_eq n hn)

/-!

## C. Numerical enclosures for `n = 5` and `n = 3`

High-precision numerical evaluation (see `wien_constant.py`) gives
`x₅ = 4.965114231744276…` and `x₃ = 2.821439372122078…`. Here we verify
rigorous coarse enclosures inside Lean: `4 < x₅ < 5` and `2 < x₃ < 3`.
The upper bounds are free from `wienRoot_lt`; the lower bounds follow from
`h(4) = 5 e⁻⁴ - 1 < 0` (i.e. `5 < e⁴`) and `h(2) = 3 e⁻² - 1 < 0`
(i.e. `3 < e²`), using `e > 2.718281828`.
-/

/-- Exponential lower bound `5 < e⁴`. -/
lemma exp_four_gt_five : (5 : ℝ) < Real.exp 4 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : Real.exp (4 : ℝ) = (Real.exp 1) ^ 4 := by
    have h4 : (4 : ℝ) = ((4 : ℕ) : ℝ) * 1 := by norm_num
    rw [h4, Real.exp_nat_mul]
  have hle : (2.7182818283 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 :=
    pow_le_pow_left₀ expApprox_nonneg (le_of_lt h1) 4
  have h54 : (5 : ℝ) < 2.7182818283 ^ 4 := by norm_num
  rw [h2]
  linarith

/-- Exponential lower bound `3 < e²`. -/
lemma exp_two_gt_three : (3 : ℝ) < Real.exp 2 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : Real.exp (2 : ℝ) = (Real.exp 1) ^ 2 := by
    have h4 : (2 : ℝ) = ((2 : ℕ) : ℝ) * 1 := by norm_num
    rw [h4, Real.exp_nat_mul]
  have hle : (2.7182818283 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 :=
    pow_le_pow_left₀ expApprox_nonneg (le_of_lt h1) 2
  have h32 : (3 : ℝ) < 2.7182818283 ^ 2 := by norm_num
  rw [h2]
  linarith

/-- `h(4) < 0` for `n = 5`. -/
lemma wienH_five_at_four : wienH 5 4 < 0 := by
  have h : Real.exp (-(4 : ℝ)) = 1 / Real.exp 4 := by
    rw [Real.exp_neg, one_div]
  have h5 : (5 : ℝ) * Real.exp (-4) < 1 := by
    rw [h, mul_one_div, div_lt_one (Real.exp_pos 4)]
    exact exp_four_gt_five
  unfold wienH
  linarith

/-- `h(2) < 0` for `n = 3`. -/
lemma wienH_three_at_two : wienH 3 2 < 0 := by
  have h : Real.exp (-(2 : ℝ)) = 1 / Real.exp 2 := by
    rw [Real.exp_neg, one_div]
  have h3 : (3 : ℝ) * Real.exp (-2) < 1 := by
    rw [h, mul_one_div, div_lt_one (Real.exp_pos 2)]
    exact exp_two_gt_three
  unfold wienH
  linarith

/-- Lower bound `4 < x₅` by strict monotonicity and `h(4) < 0 = h(x₅)`. -/
lemma wienRoot_five_gt_four : 4 < wienRoot 5 five_gt_one := by
  have hr0 : wienH 5 (wienRoot 5 five_gt_one) = 0 := wienRoot_eq 5 _
  have h4 : wienH 5 4 < 0 := wienH_five_at_four
  have hmono := (wienH_strictMonoOn 5 five_gt_one).monotoneOn
  have hlog5 : Real.log 5 < 4 := by
    have hexp : Real.log 5 + 1 < 5 := by
      have h := Real.add_one_lt_exp
        (ne_of_gt (Real.log_pos five_gt_one))
      rwa [Real.exp_log five_pos] at h
    linarith
  have hrIci : wienRoot 5 five_gt_one ∈ Ici (Real.log 5) :=
    mem_Ici.mpr (le_of_lt (wienRoot_gt_log 5 _))
  have h4Ici : (4 : ℝ) ∈ Ici (Real.log 5) := mem_Ici.mpr (le_of_lt hlog5)
  by_contra hcon
  simp only [not_lt] at hcon
  have hle := hmono hrIci h4Ici hcon
  rw [hr0] at hle
  linarith

/-- Enclosure `4 < x₅ < 5` for the wavelength Wien constant. -/
theorem wienRoot_five_mem :
    4 < wienRoot 5 five_gt_one ∧ wienRoot 5 five_gt_one < 5 :=
  ⟨wienRoot_five_gt_four, wienRoot_lt 5 _⟩

/-- Lower bound `2 < x₃` by strict monotonicity and `h(2) < 0 = h(x₃)`. -/
lemma wienRoot_three_gt_two : 2 < wienRoot 3 three_gt_one := by
  have hr0 : wienH 3 (wienRoot 3 three_gt_one) = 0 := wienRoot_eq 3 _
  have h2 : wienH 3 2 < 0 := wienH_three_at_two
  have hmono := (wienH_strictMonoOn 3 three_gt_one).monotoneOn
  have hlog3 : Real.log 3 < 2 := by
    have hexp : Real.log 3 + 1 < 3 := by
      have h := Real.add_one_lt_exp
        (ne_of_gt (Real.log_pos three_gt_one))
      rwa [Real.exp_log three_pos] at h
    linarith
  have hrIci : wienRoot 3 three_gt_one ∈ Ici (Real.log 3) :=
    mem_Ici.mpr (le_of_lt (wienRoot_gt_log 3 _))
  have h2Ici : (2 : ℝ) ∈ Ici (Real.log 3) := mem_Ici.mpr (le_of_lt hlog3)
  by_contra hcon
  simp only [not_lt] at hcon
  have hle := hmono hrIci h2Ici hcon
  rw [hr0] at hle
  linarith

/-- Enclosure `2 < x₃ < 3` for the frequency Wien constant. -/
theorem wienRoot_three_mem :
    2 < wienRoot 3 three_gt_one ∧ wienRoot 3 three_gt_one < 3 :=
  ⟨wienRoot_three_gt_two, wienRoot_lt 3 _⟩

/-- The wavelength and frequency Wien constants differ (the peak depends on the
  parametrization). -/
theorem wien_roots_differ :
    wienRoot 3 three_gt_one ≠ wienRoot 5 five_gt_one := by
  have h3 := wienRoot_three_mem
  have h5 := wienRoot_five_mem
  intro hcon
  rw [hcon] at h3
  linarith

/-!

## C'. Named Wien constants

The two physical constants that appear in Wien's displacement laws,
packaged as opaque real numbers with their enclosures and characterizations.
-/

/-- The Wien constant for wavelength: the unique positive root of
  `x = 5(1 - e⁻ˣ)`, numerically `x₅ ≈ 4.9651142317`. -/
noncomputable def wienConstant5 : ℝ := wienRoot 5 five_gt_one

/-- The Wien constant for frequency: the unique positive root of
  `x = 3(1 - e⁻ˣ)`, numerically `x₃ ≈ 2.8214393721`. -/
noncomputable def wienConstant3 : ℝ := wienRoot 3 three_gt_one

/-- `4 < x₅ < 5`. -/
theorem wienConstant5_mem : 4 < wienConstant5 ∧ wienConstant5 < 5 :=
  wienRoot_five_mem

/-- `2 < x₃ < 3`. -/
theorem wienConstant3_mem : 2 < wienConstant3 ∧ wienConstant3 < 3 :=
  wienRoot_three_mem

/-- `x₅ ≠ x₃` — the wavelength and frequency peaks differ. -/
theorem wienConstant5_ne_wienConstant3 : wienConstant5 ≠ wienConstant3 := by
  unfold wienConstant5 wienConstant3
  exact Ne.symm wien_roots_differ

/-- `x₅ > 0`. -/
theorem wienConstant5_pos : 0 < wienConstant5 := wienRoot_pos 5 five_gt_one

/-- `x₃ > 0`. -/
theorem wienConstant3_pos : 0 < wienConstant3 := wienRoot_pos 3 three_gt_one

/-!

## D. Critical points of the Planck profile `xⁿ / (eˣ - 1)`

The shape function governing every parametrization is `f(x) = xⁿ / (eˣ - 1)`.
Its derivative vanishes exactly on solutions of the Wien equation.
-/

/-- The Planck shape function `xⁿ / (eˣ - 1)`. -/
noncomputable def wienProfile (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n / (Real.exp x - 1)

/-- Derivative of the Planck shape function. -/
lemma hasDerivAt_wienProfile (n : ℕ) (x : ℝ)
    (he : Real.exp x - 1 ≠ 0) :
    HasDerivAt (wienProfile n)
      ((n * x ^ (n - 1) * (Real.exp x - 1) - x ^ n * Real.exp x)
        / (Real.exp x - 1) ^ 2) x := by
  unfold wienProfile
  have hpow : HasDerivAt (fun x : ℝ => x ^ n) ((n : ℝ) * x ^ (n - 1)) x := by
    simpa using hasDerivAt_pow n x
  have hexp : HasDerivAt (fun x : ℝ => Real.exp x - 1) (Real.exp x) x :=
    (Real.hasDerivAt_exp x).sub_const 1
  exact hpow.div hexp he

/-- The Planck profile `xⁿ / (eˣ - 1)` vanishes at `x = 0` (no radiation
  at zero energy). -/
lemma wienProfile_zero_at_zero (n : ℕ) : wienProfile n 0 = 0 := by
  unfold wienProfile
  simp

/-- The Planck profile `xⁿ / (eˣ - 1)` is strictly positive for positive `x`
  (positive radiation energy at finite frequency). -/
lemma wienProfile_pos (n : ℕ) (x : ℝ) (hx : 0 < x) :
    0 < wienProfile n x := by
  unfold wienProfile
  apply div_pos (pow_pos hx n)
  linarith [Real.one_lt_exp_iff.mpr hx]

/-- The Planck profile `xⁿ / (eˣ - 1)` is non-negative for non-negative `x`. -/
lemma wienProfile_nonneg (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ wienProfile n x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [wienProfile_zero_at_zero]
  · exact le_of_lt (wienProfile_pos n x hx)

/-- Critical points of the Planck profile are exactly the solutions of the Wien
  equation `x = n (1 - e⁻ˣ)`. -/
theorem wienProfile_crit_iff (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 0 < x) :
    deriv (wienProfile n) x = 0 ↔ x = (n : ℝ) * (1 - Real.exp (-x)) := by
  have hexp_gt : (1 : ℝ) < Real.exp x := by
    have h := Real.exp_strictMono hx
    rwa [Real.exp_zero] at h
  have hE1 : (0 : ℝ) < Real.exp x - 1 := sub_pos.mpr hexp_gt
  have he : Real.exp x - 1 ≠ 0 := ne_of_gt hE1
  have hden : (Real.exp x - 1) ^ 2 ≠ 0 := pow_ne_zero 2 he
  rw [(hasDerivAt_wienProfile n x he).deriv, div_eq_zero_iff]
  have hxpow : (0 : ℝ) < x ^ (n - 1) := pow_pos hx _
  have hxpow0 : x ^ (n - 1) ≠ 0 := ne_of_gt hxpow
  have hpow : x ^ n = x ^ (n - 1) * x := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ]
  have hfac : (n : ℝ) * x ^ (n - 1) * (Real.exp x - 1) - x ^ n * Real.exp x
      = x ^ (n - 1) * ((n : ℝ) * (Real.exp x - 1) - x * Real.exp x) := by
    rw [hpow]
    ring
  have hN : ((n : ℝ) * x ^ (n - 1) * (Real.exp x - 1) - x ^ n * Real.exp x) = 0
      ↔ ((n : ℝ) * (Real.exp x - 1) - x * Real.exp x) = 0 := by
    rw [hfac, mul_eq_zero]
    constructor
    · rintro (h | h)
      · exact absurd h hxpow0
      · exact h
    · intro h
      exact Or.inr h
  have hE0 : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have hexpNeg : Real.exp (-x) = 1 / Real.exp x := by
    rw [Real.exp_neg, one_div]
  have hshape : (n : ℝ) * (1 - 1 / Real.exp x)
      = (n : ℝ) * (Real.exp x - 1) / Real.exp x := by
    field_simp
  have hM : ((n : ℝ) * (Real.exp x - 1) - x * Real.exp x) = 0
      ↔ x = (n : ℝ) * (1 - Real.exp (-x)) := by
    rw [hexpNeg, hshape, eq_div_iff hE0]
    constructor
    · intro h
      have h1 : (n : ℝ) * (Real.exp x - 1) = x * Real.exp x := sub_eq_zero.mp h
      exact h1.symm
    · intro h
      exact sub_eq_zero.mpr h.symm
  constructor
  · rintro (h | h)
    · exact (hM.mp (hN.mp h))
    · exact absurd h hden
  · intro h
    exact Or.inl (hN.mpr (hM.mpr h))

/-!

## D'. Profile behavior: sign, monotonicity, global maximum, asymptotics

The derivative of the profile has the opposite sign of the auxiliary
function (up to positive factors), so `f` strictly increases on
`(0, x*]` and strictly decreases on `[x*, ∞)`, where `x*` is the Wien
root. Hence `x*` is the unique global maximizer on `(0, ∞)`. The profile
also vanishes at both ends: at `0` (for `n ≥ 2`) and at `∞` (the
exponential dominates the polynomial).
-/

/-- The auxiliary function is negative strictly between `0` and the Wien
  root: it falls from `h(0) = 0` on `(0, log n]` and rises back to
  `h(x*) = 0` on `[log n, x*)`. -/
lemma wienH_neg_on_Ioo (n : ℝ) (hn : 1 < n) (x : ℝ) (hx0 : 0 < x)
    (hxr : x < wienRoot n hn) : wienH n x < 0 := by
  rcases le_total x (Real.log n) with hle | hge
  · have hanti := wienH_strictAntiOn n hn
    have h0mem : (0 : ℝ) ∈ Iic (Real.log n) :=
      mem_Iic.mpr (le_trans hx0.le hle)
    have hxmem : x ∈ Iic (Real.log n) := mem_Iic.mpr hle
    have hlt : wienH n x < wienH n 0 := hanti h0mem hxmem hx0
    rwa [wienH_zero] at hlt
  · have hmono := wienH_strictMonoOn n hn
    have hxmem : x ∈ Ici (Real.log n) := mem_Ici.mpr hge
    have hrmem : wienRoot n hn ∈ Ici (Real.log n) :=
      mem_Ici.mpr (le_of_lt (wienRoot_gt_log n hn))
    have hlt : wienH n x < wienH n (wienRoot n hn) :=
      hmono hxmem hrmem hxr
    rwa [wienRoot_eq] at hlt

/-- The auxiliary function is positive strictly above the Wien root, by
  strict monotonicity on `[log n, ∞)`. -/
lemma wienH_pos_on_Ioi (n : ℝ) (hn : 1 < n) (x : ℝ)
    (hxr : wienRoot n hn < x) : 0 < wienH n x := by
  have hmono := wienH_strictMonoOn n hn
  have hrmem : wienRoot n hn ∈ Ici (Real.log n) :=
    mem_Ici.mpr (le_of_lt (wienRoot_gt_log n hn))
  have hxmem : x ∈ Ici (Real.log n) :=
    mem_Ici.mpr (le_trans (le_of_lt (wienRoot_gt_log n hn)) hxr.le)
  have hlt : wienH n (wienRoot n hn) < wienH n x := hmono hrmem hxmem hxr
  rwa [wienRoot_eq] at hlt

/-- The Planck profile is continuous on `(0, ∞)`. -/
lemma wienProfile_continuousOn (n : ℕ) :
    ContinuousOn (wienProfile n) (Ioi 0) := by
  unfold wienProfile
  apply ContinuousOn.div (continuousOn_pow n)
    ((Real.continuousOn_exp).sub continuousOn_const) _
  intro x hx
  exact ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx))

/-- Factored form of the profile derivative: the sign of `f'(x)` for `x > 0`
  is the opposite of the sign of the auxiliary function. -/
lemma wienProfile_deriv_eq (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (he : Real.exp x - 1 ≠ 0) :
    deriv (wienProfile n) x
      = -(x ^ (n - 1) * Real.exp x * wienH n x) / (Real.exp x - 1) ^ 2 := by
  have hpow : x ^ n = x ^ (n - 1) * x := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ]
  rw [(hasDerivAt_wienProfile n x he).deriv, hpow]
  unfold wienH
  have hE0 : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  rw [Real.exp_neg]
  field_simp
  ring

/-- The Planck profile is strictly increasing on `(0, x*]`, where `x*` is the
  Wien root: there `h < 0`, so `f' > 0`. -/
lemma wienProfile_strictMonoOn (n : ℕ) (hn : 2 ≤ n) :
    StrictMonoOn (wienProfile n)
      (Ioc 0 (wienRoot n (by exact_mod_cast lt_of_lt_of_le one_lt_two hn))) := by
  have hnR : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_lt_two hn
  have hn1 : 1 ≤ n := le_trans one_le_two hn
  refine strictMonoOn_of_deriv_pos (convex_Ioc _ _) ?hcont ?hderiv
  · exact (wienProfile_continuousOn n).mono Ioc_subset_Ioi_self
  · intro x hx
    rw [interior_Ioc] at hx
    obtain ⟨hx0, hxr⟩ := hx
    have he : Real.exp x - 1 ≠ 0 :=
      ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx0))
    have hw : wienH (n : ℝ) x < 0 := wienH_neg_on_Ioo _ hnR x hx0 hxr
    rw [wienProfile_deriv_eq n hn1 x he]
    apply div_pos _ (pow_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx0)) 2)
    exact neg_pos.mpr
      (mul_neg_of_pos_of_neg (mul_pos (pow_pos hx0 _) (Real.exp_pos _)) hw)

/-- The Planck profile is strictly decreasing on `[x*, ∞)`, where `x*` is the
  Wien root: there `h > 0`, so `f' < 0`. -/
lemma wienProfile_strictAntiOn (n : ℕ) (hn : 2 ≤ n) :
    StrictAntiOn (wienProfile n)
      (Ici (wienRoot n (by exact_mod_cast lt_of_lt_of_le one_lt_two hn))) := by
  have hnR : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_lt_two hn
  have hn1 : 1 ≤ n := le_trans one_le_two hn
  have hrpos : 0 < wienRoot n hnR :=
    lt_trans (Real.log_pos hnR) (wienRoot_gt_log n hnR)
  refine strictAntiOn_of_deriv_neg (convex_Ici _) ?hcont ?hderiv
  · exact (wienProfile_continuousOn n).mono
      (fun x hx => lt_of_lt_of_le hrpos hx)
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hrpos (le_of_lt hx)
    have he : Real.exp x - 1 ≠ 0 :=
      ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx0))
    have hw : 0 < wienH (n : ℝ) x := wienH_pos_on_Ioi _ hnR x hx
    rw [wienProfile_deriv_eq n hn1 x he]
    apply div_neg_of_neg_of_pos _ (pow_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx0)) 2)
    exact neg_lt_zero.mpr
      (mul_pos (mul_pos (pow_pos hx0 _) (Real.exp_pos _)) hw)

/-- The Planck profile attains its unique global maximum on `(0, ∞)` at the
  Wien root. This is the mathematical core of Wien's displacement law: the
  "peak" of the blackbody spectrum. -/
theorem wienProfile_isMaxOn (n : ℕ) (hn : 2 ≤ n) :
    IsMaxOn (wienProfile n) (Ioi 0)
      (wienRoot n (by exact_mod_cast lt_of_lt_of_le one_lt_two hn)) := by
  have hnR : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_lt_two hn
  have hrpos : 0 < wienRoot n hnR :=
    lt_trans (Real.log_pos hnR) (wienRoot_gt_log n hnR)
  intro x hx
  rcases le_total x (wienRoot n hnR) with hle | hge
  · have hmono := wienProfile_strictMonoOn n hn
    have hxmem : x ∈ Ioc 0 (wienRoot n hnR) := ⟨hx, hle⟩
    have hrmem : wienRoot n hnR ∈ Ioc 0 (wienRoot n hnR) := ⟨hrpos, le_rfl⟩
    exact hmono.monotoneOn hxmem hrmem hle
  · have hanti := wienProfile_strictAntiOn n hn
    have hxmem : x ∈ Ici (wienRoot n hnR) := mem_Ici.mpr hge
    have hrmem : wienRoot n hnR ∈ Ici (wienRoot n hnR) := mem_Ici.mpr le_rfl
    exact hanti.antitoneOn hrmem hxmem hge

/-- The Planck profile vanishes at infinity: the exponential in the
  denominator dominates the polynomial numerator. -/
lemma wienProfile_tendsto_zero_atTop (n : ℕ) :
    Tendsto (fun x => wienProfile n x) atTop (𝓝 0) := by
  have hexp2 : ∀ᶠ x : ℝ in atTop, (2 : ℝ) ≤ Real.exp x := by
    filter_upwards [eventually_ge_atTop 1] with x hx
    calc (2 : ℝ) ≤ Real.exp 1 := le_of_lt (by linarith [Real.exp_one_gt_d9])
      _ ≤ Real.exp x := Real.exp_strictMono.monotone (by linarith)
  have hle : ∀ᶠ x : ℝ in atTop, wienProfile n x ≤ 2 * (x ^ n * Real.exp (-x)) := by
    filter_upwards [eventually_ge_atTop 1, hexp2] with x hx h2
    have hden : (0 : ℝ) < Real.exp x - 1 := by linarith
    have hnn : (0 : ℝ) ≤ x ^ n := pow_nonneg (by linarith) n
    have hE0 : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
    have hinv : (Real.exp x)⁻¹ ≤ 2⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos x) zero_lt_two).mpr h2
    have hprod : (Real.exp x)⁻¹ * Real.exp x = 1 := inv_mul_cancel₀ hE0
    have h0 : (0 : ℝ) ≤ 1 - 2 * (Real.exp x)⁻¹ := by linarith
    have key : 2 * (x ^ n * (Real.exp x)⁻¹) * (Real.exp x - 1)
        = x ^ n + x ^ n * (1 - 2 * (Real.exp x)⁻¹) := by
      linear_combination 2 * x ^ n * hprod
    unfold wienProfile
    rw [Real.exp_neg, div_le_iff₀ hden, key]
    exact le_add_of_nonneg_right (mul_nonneg hnn h0)
  have hnn' : ∀ᶠ x : ℝ in atTop, 0 ≤ wienProfile n x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    exact wienProfile_nonneg n x hx
  have hlim : Tendsto (fun x : ℝ => 2 * (x ^ n * Real.exp (-x))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).const_mul 2
    simpa using h
  exact squeeze_zero' hnn' hle hlim

/-- The Planck profile vanishes at the origin (for `n ≥ 2`) : near `x = 0`,
  `eˣ - 1 ≥ x` gives `f(x) ≤ xⁿ⁻¹ → 0`. -/
lemma wienProfile_tendsto_nhdsWithin_zero (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun x => wienProfile n x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hn1 : 1 ≤ n := le_trans one_le_two hn
  have hle : ∀ᶠ x : ℝ in 𝓝[>] 0, wienProfile n x ≤ x ^ (n - 1) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := hx
    have hden : (0 : ℝ) < Real.exp x - 1 :=
      sub_pos.mpr (Real.one_lt_exp_iff.mpr hx0)
    have hge : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
    have hpow : x ^ n = x ^ (n - 1) * x := by
      conv_lhs => rw [← Nat.sub_add_cancel hn1]
      rw [pow_succ]
    unfold wienProfile
    rw [div_le_iff₀ hden, hpow]
    exact mul_le_mul_of_nonneg_left hge (pow_nonneg hx0.le _)
  have hnn' : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ wienProfile n x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact wienProfile_nonneg n x (le_of_lt hx)
  have hlim : Tendsto (fun x : ℝ => x ^ (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun x : ℝ => x ^ (n - 1)) 0 :=
      continuousAt_pow 0 (n - 1)
    have h : Tendsto (fun x : ℝ => x ^ (n - 1)) (𝓝[>] (0 : ℝ))
        (𝓝 ((0 : ℝ) ^ (n - 1))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    rwa [zero_pow (by omega : n - 1 ≠ 0)] at h
  exact squeeze_zero' hnn' hle hlim

/-!

## E. Critical points of the Planck curves

For fixed temperature, the wavelength curve is a positive constant multiple of
the profile `f₅(x)` composed with `x = h c / (λ kB T)`, and the frequency curve
is a positive constant multiple of `f₃(x)` composed with `x = h ν / (kB T)`.
Since the outer affine factors have nonzero derivative, critical points of the
physical curves correspond exactly to solutions of the Wien equation.
-/

/-- Wavelength prefactor `C(T) = 2 (kB T)⁵ / (h⁴ c³)`. -/
noncomputable def wavePrefactor (h c kB T : ℝ) : ℝ :=
  2 * (kB * T) ^ 5 / (h ^ 4 * c ^ 3)

/-- Frequency prefactor `D(T) = 2 (kB T)³ / (h² c²)`. -/
noncomputable def freqPrefactor (h c kB T : ℝ) : ℝ :=
  2 * (kB * T) ^ 3 / (h ^ 2 * c ^ 2)

/-- Dimensionless wavelength variable `x = h c / (λ kB T)`. -/
noncomputable def waveVar (h c kB T lam : ℝ) : ℝ := h * c / (lam * kB * T)

/-- Dimensionless frequency variable `x = h ν / (kB T)`. -/
noncomputable def freqVar (h kB T nu : ℝ) : ℝ := h * nu / (kB * T)

/-- The wavelength prefactor is positive for positive parameters. -/
lemma wavePrefactor_pos (h c kB T : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hT : 0 < T) : 0 < wavePrefactor h c kB T := by
  unfold wavePrefactor
  apply div_pos
  · exact mul_pos zero_lt_two (pow_pos (mul_pos hk hT) 5)
  · exact mul_pos (pow_pos hh 4) (pow_pos hc 3)

/-- The frequency prefactor is positive for positive parameters. -/
lemma freqPrefactor_pos (h c kB T : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hT : 0 < T) : 0 < freqPrefactor h c kB T := by
  unfold freqPrefactor
  apply div_pos
  · exact mul_pos zero_lt_two (pow_pos (mul_pos hk hT) 3)
  · exact mul_pos (pow_pos hh 2) (pow_pos hc 2)

/-- The dimensionless wavelength variable is positive for positive parameters. -/
lemma waveVar_pos (h c kB T lam : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hT : 0 < T) (hlam : 0 < lam) :
    0 < waveVar h c kB T lam := by
  unfold waveVar
  exact div_pos (mul_pos hh hc) (mul_pos (mul_pos hlam hk) hT)

/-- The dimensionless frequency variable is positive for positive parameters. -/
lemma freqVar_pos (h kB T nu : ℝ) (hh : 0 < h)
    (hk : 0 < kB) (hT : 0 < T) (hν : 0 < nu) :
    0 < freqVar h kB T nu := by
  unfold freqVar
  exact div_pos (mul_pos hh hν) (mul_pos hk hT)

/-- The wavelength curve factors through the `n = 5` profile on `λ > 0`. -/
lemma spectralRadianceWave_eq_profile (h c kB T lam : ℝ) (hh : 0 < h)
    (hc : 0 < c) (hk : 0 < kB) (hT : 0 < T) (hlam : 0 < lam) :
    spectralRadianceWave h c kB lam T
      = wavePrefactor h c kB T * wienProfile 5 (waveVar h c kB T lam) := by
  have h1 : 0 < lam ∧ 0 < T := ⟨hlam, hT⟩
  unfold spectralRadianceWave wavePrefactor wienProfile waveVar
  rw [if_pos h1]
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hh' : h ≠ 0 := ne_of_gt hh
  have hc' : c ≠ 0 := ne_of_gt hc
  have hk' : kB ≠ 0 := ne_of_gt hk
  have hT' : T ≠ 0 := ne_of_gt hT
  have hE : Real.exp (h * c / (lam * kB * T)) - 1 ≠ 0 := by
    have harg : 0 < h * c / (lam * kB * T) :=
      div_pos (mul_pos hh hc) (mul_pos (mul_pos hlam hk) hT)
    have h1e : 1 < Real.exp (h * c / (lam * kB * T)) := Real.one_lt_exp_iff.mpr harg
    exact ne_of_gt (sub_pos.mpr h1e)
  field_simp

/-- The frequency curve factors through the `n = 3` profile on `ν > 0`. -/
lemma spectralRadianceFreq_eq_profile (h c kB T nu : ℝ) (hh : 0 < h)
    (hc : 0 < c) (hk : 0 < kB) (hT : 0 < T) (hν : 0 < nu) :
    spectralRadianceFreq h c kB nu T
      = freqPrefactor h c kB T * wienProfile 3 (freqVar h kB T nu) := by
  have h1 : 0 < nu ∧ 0 < T := ⟨hν, hT⟩
  unfold spectralRadianceFreq freqPrefactor wienProfile freqVar
  rw [if_pos h1]
  have hν' : nu ≠ 0 := ne_of_gt hν
  have hh' : h ≠ 0 := ne_of_gt hh
  have hc' : c ≠ 0 := ne_of_gt hc
  have hk' : kB ≠ 0 := ne_of_gt hk
  have hT' : T ≠ 0 := ne_of_gt hT
  have hE : Real.exp (h * nu / (kB * T)) - 1 ≠ 0 := by
    have harg : 0 < h * nu / (kB * T) :=
      div_pos (mul_pos hh hν) (mul_pos hk hT)
    have h1e : 1 < Real.exp (h * nu / (kB * T)) := Real.one_lt_exp_iff.mpr harg
    exact ne_of_gt (sub_pos.mpr h1e)
  field_simp

/-- Derivative of the wavelength curve at `λ > 0`, via the chain rule. -/
lemma hasDerivAt_wave (h c kB T lam : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hT : 0 < T) (hlam : 0 < lam) :
    HasDerivAt (fun lam => spectralRadianceWave h c kB lam T)
      (wavePrefactor h c kB T
        * (deriv (wienProfile 5) (waveVar h c kB T lam)
          * (-(h * c / (kB * T)) / lam ^ 2))) lam := by
  have hK : 0 < h * c / (kB * T) :=
    div_pos (mul_pos hh hc) (mul_pos hk hT)
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hk' : kB ≠ 0 := ne_of_gt hk
  have hT' : T ≠ 0 := ne_of_gt hT
  have hkT : kB * T ≠ 0 := mul_ne_zero hk' hT'
  have hlamkT : lam * kB * T ≠ 0 := mul_ne_zero (mul_ne_zero hlam' hk') hT'
  have hpt : h * c / (kB * T) / lam = waveVar h c kB T lam := by
    unfold waveVar
    field_simp
  have hpt_pos : 0 < h * c / (kB * T) / lam := by
    rw [hpt]
    exact waveVar_pos h c kB T lam hh hc hk hT hlam
  have hexp_gt : (1 : ℝ) < Real.exp (h * c / (kB * T) / lam) := by
    have hlt := Real.exp_strictMono hpt_pos
    rwa [Real.exp_zero] at hlt
  have he : Real.exp (h * c / (kB * T) / lam) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr hexp_gt)
  -- derivative of the inner variable `K / lam`
  have hinner : HasDerivAt (fun lam => h * c / (kB * T) / lam)
      ((0 * lam - h * c / (kB * T) * 1) / lam ^ 2) lam :=
    (hasDerivAt_const lam (h * c / (kB * T))).div (hasDerivAt_id' lam)
      (ne_of_gt hlam)
  -- the profile composed with the inner variable
  have hcomp : HasDerivAt (wienProfile 5 ∘ (fun lam => h * c / (kB * T) / lam))
      (deriv (wienProfile 5) (h * c / (kB * T) / lam)
        * ((0 * lam - h * c / (kB * T) * 1) / lam ^ 2)) lam := by
    have hprof := hasDerivAt_wienProfile 5 (h * c / (kB * T) / lam) he
    have hcc := HasDerivAt.comp lam hprof hinner
    rwa [← hprof.deriv] at hcc
  -- transfer to the `waveVar` formulation on a neighborhood of `lam`
  have hev : (wienProfile 5 ∘ (fun lam => h * c / (kB * T) / lam))
      =ᶠ[𝓝 lam] (fun lam => wienProfile 5 (waveVar h c kB T lam)) := by
    have hkT' : kB * T ≠ 0 := mul_ne_zero hk' hT'
    apply Filter.eventually_of_mem (Ioi_mem_nhds hlam)
    intro y hy
    rw [mem_Ioi] at hy
    have hy' : y ≠ 0 := ne_of_gt hy
    have hAy : h * c / (kB * T) / y = waveVar h c kB T y := by
      unfold waveVar
      field_simp
    simp only [Function.comp_apply]
    rw [hAy]
  have hC : HasDerivAt
      (fun lam => wavePrefactor h c kB T * wienProfile 5 (waveVar h c kB T lam))
      (wavePrefactor h c kB T
        * (deriv (wienProfile 5) (waveVar h c kB T lam)
          * (-(h * c / (kB * T)) / lam ^ 2))) lam := by
    have hcomp2 := hcomp.congr_of_eventuallyEq hev.symm
    rw [hpt] at hcomp2
    have hder : deriv (wienProfile 5) (waveVar h c kB T lam)
          * ((0 * lam - h * c / (kB * T) * 1) / lam ^ 2)
        = deriv (wienProfile 5) (waveVar h c kB T lam)
          * (-(h * c / (kB * T)) / lam ^ 2) := by ring
    have hcomp3 := hcomp2.congr_deriv hder
    exact hcomp3.const_mul (wavePrefactor h c kB T)
  -- the physical curve agrees with the factored form near `lam`
  have heq : (fun lam => spectralRadianceWave h c kB lam T)
      =ᶠ[𝓝 lam] (fun lam => wavePrefactor h c kB T
        * wienProfile 5 (waveVar h c kB T lam)) := by
    apply Filter.eventually_of_mem (Ioi_mem_nhds hlam)
    intro y hy
    rw [mem_Ioi] at hy
    exact spectralRadianceWave_eq_profile h c kB T y hh hc hk hT hy
  exact hC.congr_of_eventuallyEq heq

/-- Critical-point equation for the wavelength curve: `deriv = 0` iff the
  dimensionless variable satisfies the `n = 5` Wien equation. -/
theorem wave_crit_iff (h c kB T lam : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hT : 0 < T) (hlam : 0 < lam) :
    deriv (fun lam => spectralRadianceWave h c kB lam T) lam = 0
      ↔ waveVar h c kB T lam
        = 5 * (1 - Real.exp (-(waveVar h c kB T lam))) := by
  have hC0 : wavePrefactor h c kB T ≠ 0 :=
    ne_of_gt (wavePrefactor_pos h c kB T hh hc hk hT)
  have hK0 : (-(h * c / (kB * T)) / lam ^ 2) ≠ 0 := by
    apply div_ne_zero
    · exact neg_ne_zero.mpr (ne_of_gt (div_pos (mul_pos hh hc) (mul_pos hk hT)))
    · exact pow_ne_zero 2 (ne_of_gt hlam)
  have hx : 0 < waveVar h c kB T lam := waveVar_pos h c kB T lam hh hc hk hT hlam
  rw [(hasDerivAt_wave h c kB T lam hh hc hk hT hlam).deriv]
  constructor
  · intro hzero
    have hmul := (mul_eq_zero.mp hzero).resolve_left hC0
    have hderiv := (mul_eq_zero.mp hmul).resolve_right hK0
    have hcrit := (wienProfile_crit_iff 5 five_ge_one
      (waveVar h c kB T lam) hx).mp hderiv
    simpa using hcrit
  · intro hsol
    have hderiv : deriv (wienProfile 5) (waveVar h c kB T lam) = 0 :=
      (wienProfile_crit_iff 5 five_ge_one (waveVar h c kB T lam) hx).mpr
        (by simpa using hsol)
    rw [hderiv, zero_mul, mul_zero]

/-- Derivative of the frequency curve at `ν > 0`, via the chain rule. -/
lemma hasDerivAt_freq (h c kB T nu : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hT : 0 < T) (hν : 0 < nu) :
    HasDerivAt (fun nu => spectralRadianceFreq h c kB nu T)
      (freqPrefactor h c kB T
        * (deriv (wienProfile 3) (freqVar h kB T nu) * (h / (kB * T)))) nu := by
  have hx : 0 < freqVar h kB T nu := freqVar_pos h kB T nu hh hk hT hν
  have hexp_gt : (1 : ℝ) < Real.exp (freqVar h kB T nu) := by
    have hlt := Real.exp_strictMono hx
    rwa [Real.exp_zero] at hlt
  have he : Real.exp (freqVar h kB T nu) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr hexp_gt)
  have hinner : HasDerivAt (fun nu => h / (kB * T) * nu)
      (0 * nu + h / (kB * T) * 1) nu :=
    (hasDerivAt_const nu (h / (kB * T))).mul (hasDerivAt_id' nu)
  have hpt : h / (kB * T) * nu = freqVar h kB T nu := by
    unfold freqVar
    ring
  have hept : Real.exp (h / (kB * T) * nu) - 1 ≠ 0 := by
    rw [hpt]
    exact he
  have hprof := hasDerivAt_wienProfile 3 (h / (kB * T) * nu) hept
  have hcomp : HasDerivAt (wienProfile 3 ∘ (fun nu => h / (kB * T) * nu))
      (deriv (wienProfile 3) (h / (kB * T) * nu)
        * (0 * nu + h / (kB * T) * 1)) nu := by
    have hcc := HasDerivAt.comp nu hprof hinner
    rwa [← hprof.deriv] at hcc
  have hC : HasDerivAt
      (fun nu => freqPrefactor h c kB T * wienProfile 3 (freqVar h kB T nu))
      (freqPrefactor h c kB T
        * (deriv (wienProfile 3) (freqVar h kB T nu) * (h / (kB * T)))) nu := by
    have hev : (wienProfile 3 ∘ (fun nu => h / (kB * T) * nu))
        =ᶠ[𝓝 nu] (fun nu => wienProfile 3 (freqVar h kB T nu)) := by
      apply Filter.eventually_of_mem (Ioi_mem_nhds hν)
      intro y hy
      rw [mem_Ioi] at hy
      have hAy : h / (kB * T) * y = freqVar h kB T y := by
        unfold freqVar
        ring
      simp only [Function.comp_apply]
      rw [hAy]
    have hcomp2 := hcomp.congr_of_eventuallyEq hev.symm
    rw [hpt] at hcomp2
    have hder : deriv (wienProfile 3) (freqVar h kB T nu)
          * (0 * nu + h / (kB * T) * 1)
        = deriv (wienProfile 3) (freqVar h kB T nu) * (h / (kB * T)) := by
      ring
    have hcomp3 := hcomp2.congr_deriv hder
    exact hcomp3.const_mul (freqPrefactor h c kB T)
  have heq : (fun nu => spectralRadianceFreq h c kB nu T)
      =ᶠ[𝓝 nu] (fun nu => freqPrefactor h c kB T
        * wienProfile 3 (freqVar h kB T nu)) := by
    apply Filter.eventually_of_mem (Ioi_mem_nhds hν)
    intro y hy
    rw [mem_Ioi] at hy
    exact spectralRadianceFreq_eq_profile h c kB T y hh hc hk hT hy
  exact hC.congr_of_eventuallyEq heq

/-- Critical-point equation for the frequency curve: `deriv = 0` iff the
  dimensionless variable satisfies the `n = 3` Wien equation. -/
theorem freq_crit_iff (h c kB T nu : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hT : 0 < T) (hν : 0 < nu) :
    deriv (fun nu => spectralRadianceFreq h c kB nu T) nu = 0
      ↔ freqVar h kB T nu
        = 3 * (1 - Real.exp (-(freqVar h kB T nu))) := by
  have hC0 : freqPrefactor h c kB T ≠ 0 :=
    ne_of_gt (freqPrefactor_pos h c kB T hh hc hk hT)
  have hK0 : (h / (kB * T)) ≠ 0 :=
    div_ne_zero (ne_of_gt hh) (mul_ne_zero (ne_of_gt hk) (ne_of_gt hT))
  have hx : 0 < freqVar h kB T nu := freqVar_pos h kB T nu hh hk hT hν
  rw [(hasDerivAt_freq h c kB T nu hh hc hk hT hν).deriv]
  constructor
  · intro hzero
    have hmul := (mul_eq_zero.mp hzero).resolve_left hC0
    have hderiv := (mul_eq_zero.mp hmul).resolve_right hK0
    have hcrit := (wienProfile_crit_iff 3 three_ge_one
      (freqVar h kB T nu) hx).mp hderiv
    simpa using hcrit
  · intro hsol
    have hderiv : deriv (wienProfile 3) (freqVar h kB T nu) = 0 :=
      (wienProfile_crit_iff 3 three_ge_one (freqVar h kB T nu) hx).mpr
        (by simpa using hsol)
    rw [hderiv, zero_mul, mul_zero]

/-!

## E'. Physical curves: continuity, limits, global maxima, boundedness

The dimensionless variables tend to `0` or `∞` at the ends of the physical
domain, so the profile asymptotics transfer to the Planck curves by
composition. The curves are continuous on `(0, ∞)`, vanish at both ends,
and attain their unique global maximum where the dimensionless variable
hits the Wien root.
-/

/-- The wavelength variable tends to `0⁺` as `λ → ∞`. -/
lemma waveVar_tendsto_nhdsWithin_atTop (h c kB T : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hT : 0 < T) :
    Tendsto (fun lam => waveVar h c kB T lam) atTop (𝓝[>] (0 : ℝ)) := by
  have hK : (0 : ℝ) < h * c / (kB * T) :=
    div_pos (mul_pos hh hc) (mul_pos hk hT)
  have hfun : ∀ lam : ℝ,
      waveVar h c kB T lam = (h * c / (kB * T)) * lam⁻¹ := by
    intro lam
    unfold waveVar
    have hlam : lam = 0 ∨ lam ≠ 0 := eq_or_ne lam 0
    rcases hlam with rfl | hne
    · simp
    · have hk' : kB ≠ 0 := ne_of_gt hk
      have hT' : T ≠ 0 := ne_of_gt hT
      field_simp
  have hbase : Tendsto (fun lam : ℝ => (h * c / (kB * T)) * lam⁻¹) atTop (𝓝 0) := by
    have h := tendsto_inv_atTop_zero.const_mul (h * c / (kB * T))
    simpa using h
  have hpos : ∀ᶠ lam : ℝ in atTop, (h * c / (kB * T)) * lam⁻¹ ∈ Ioi (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with lam hlam
    exact mem_Ioi.mpr (mul_pos hK (inv_pos.mpr hlam))
  have hlim := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    _ hbase hpos
  exact hlim.congr (fun lam => (hfun lam).symm)

/-- The wavelength variable tends to `∞` as `λ → 0⁺`. -/
lemma waveVar_tendsto_atTop_nhdsWithin (h c kB T : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hT : 0 < T) :
    Tendsto (fun lam => waveVar h c kB T lam) (𝓝[>] (0 : ℝ)) atTop := by
  have hK : (0 : ℝ) < h * c / (kB * T) :=
    div_pos (mul_pos hh hc) (mul_pos hk hT)
  have hfun : ∀ lam : ℝ,
      waveVar h c kB T lam = lam⁻¹ * (h * c / (kB * T)) := by
    intro lam
    unfold waveVar
    rcases eq_or_ne lam 0 with rfl | hne
    · simp
    · have hk' : kB ≠ 0 := ne_of_gt hk
      have hT' : T ≠ 0 := ne_of_gt hT
      field_simp
  have hlim : Tendsto (fun lam : ℝ => lam⁻¹ * (h * c / (kB * T))) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.atTop_mul_const hK
  exact hlim.congr (fun lam => (hfun lam).symm)

/-- The frequency variable tends to `∞` as `ν → ∞` (linear with positive
  slope). -/
lemma freqVar_tendsto_atTop_atTop (h kB T : ℝ) (hh : 0 < h)
    (hk : 0 < kB) (hT : 0 < T) :
    Tendsto (fun nu => freqVar h kB T nu) atTop atTop := by
  have hK : (0 : ℝ) < h / (kB * T) :=
    div_pos hh (mul_pos hk hT)
  have hfun : ∀ nu : ℝ, freqVar h kB T nu = nu * (h / (kB * T)) := by
    intro nu
    unfold freqVar
    ring
  have hlim : Tendsto (fun nu : ℝ => nu * (h / (kB * T))) atTop atTop :=
    tendsto_id.atTop_mul_const hK
  exact hlim.congr (fun nu => (hfun nu).symm)

/-- The frequency variable tends to `0⁺` as `ν → 0⁺` (linear with positive
  slope). -/
lemma freqVar_tendsto_nhdsWithin (h kB T : ℝ) (hh : 0 < h)
    (hk : 0 < kB) (hT : 0 < T) :
    Tendsto (fun nu => freqVar h kB T nu) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  have hK : (0 : ℝ) < h / (kB * T) :=
    div_pos hh (mul_pos hk hT)
  have hfun : ∀ nu : ℝ, freqVar h kB T nu = (h / (kB * T)) * nu := by
    intro nu
    unfold freqVar
    ring
  have hbase : Tendsto (fun nu : ℝ => (h / (kB * T)) * nu) (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    have h := hid.const_mul (h / (kB * T))
    simpa using h
  have hlim := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    _ hbase (a := (0 : ℝ)) (s := Ioi 0) (l := 𝓝[>] (0 : ℝ)) ?_
  · exact hlim.congr (fun nu => (hfun nu).symm)
  · filter_upwards [self_mem_nhdsWithin] with nu hnu
    exact mem_Ioi.mpr (mul_pos hK hnu)

/-- The wavelength curve is continuous on `(0, ∞)`. -/
lemma spectralRadianceWave_continuousOn (h c kB T : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hT : 0 < T) :
    ContinuousOn (fun lam => spectralRadianceWave h c kB lam T) (Ioi 0) := by
  have heq : EqOn (fun lam => spectralRadianceWave h c kB lam T)
      (fun lam => wavePrefactor h c kB T * wienProfile 5 (waveVar h c kB T lam))
      (Ioi 0) := by
    intro lam hlam
    exact spectralRadianceWave_eq_profile h c kB T lam hh hc hk hT hlam
  have hcont : ContinuousOn
      (fun lam => wavePrefactor h c kB T * wienProfile 5 (waveVar h c kB T lam))
      (Ioi 0) := by
    apply ContinuousOn.mul continuousOn_const _
    apply (wienProfile_continuousOn 5).comp _ _
    · unfold waveVar
      apply ContinuousOn.div continuousOn_const _ _
      · apply ContinuousOn.mul _ continuousOn_const
        apply ContinuousOn.mul _ continuousOn_const
        exact continuousOn_id
      · intro lam hlam
        exact mul_ne_zero (mul_ne_zero (ne_of_gt hlam) (ne_of_gt hk))
          (ne_of_gt hT)
    · intro lam hlam
      exact waveVar_pos h c kB T lam hh hc hk hT hlam
  exact hcont.congr heq

/-- The frequency curve is continuous on `(0, ∞)`. -/
lemma spectralRadianceFreq_continuousOn (h c kB T : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hT : 0 < T) :
    ContinuousOn (fun nu => spectralRadianceFreq h c kB nu T) (Ioi 0) := by
  have heq : EqOn (fun nu => spectralRadianceFreq h c kB nu T)
      (fun nu => freqPrefactor h c kB T * wienProfile 3 (freqVar h kB T nu))
      (Ioi 0) := by
    intro nu hnu
    exact spectralRadianceFreq_eq_profile h c kB T nu hh hc hk hT hnu
  have hcont : ContinuousOn
      (fun nu => freqPrefactor h c kB T * wienProfile 3 (freqVar h kB T nu))
      (Ioi 0) := by
    apply ContinuousOn.mul continuousOn_const _
    apply (wienProfile_continuousOn 3).comp _ _
    · unfold freqVar
      apply ContinuousOn.div _ continuousOn_const _
      · apply ContinuousOn.mul continuousOn_const continuousOn_id
      · intro nu hnu
        exact mul_ne_zero (ne_of_gt hk) (ne_of_gt hT)
    · intro nu hnu
      exact freqVar_pos h kB T nu hh hk hT hnu
  exact hcont.congr heq

/-- The wavelength curve vanishes at infinity: `B(λ, T) → 0` as `λ → ∞`. -/
lemma spectralRadianceWave_tendsto_zero_atTop (h c kB T : ℝ) (hh : 0 < h)
    (hc : 0 < c) (hk : 0 < kB) (hT : 0 < T) :
    Tendsto (fun lam => spectralRadianceWave h c kB lam T) atTop (𝓝 0) := by
  have hxlim := waveVar_tendsto_nhdsWithin_atTop h c kB T hh hc hk hT
  have hflim : Tendsto (fun lam : ℝ => wienProfile 5 (waveVar h c kB T lam))
      atTop (𝓝 0) :=
    (wienProfile_tendsto_nhdsWithin_zero 5 (by decide)).comp hxlim
  have heq : (fun lam => spectralRadianceWave h c kB lam T) =ᶠ[atTop]
      (fun lam => wavePrefactor h c kB T
        * wienProfile 5 (waveVar h c kB T lam)) := by
    filter_upwards [eventually_gt_atTop 0] with lam hlam
    exact spectralRadianceWave_eq_profile h c kB T lam hh hc hk hT hlam
  have hC := hflim.const_mul (wavePrefactor h c kB T)
  rw [mul_zero] at hC
  exact hC.congr' heq.symm

/-- The wavelength curve vanishes at the origin: `B(λ, T) → 0` as `λ → 0⁺`. -/
lemma spectralRadianceWave_tendsto_nhdsWithin_zero (h c kB T : ℝ) (hh : 0 < h)
    (hc : 0 < c) (hk : 0 < kB) (hT : 0 < T) :
    Tendsto (fun lam => spectralRadianceWave h c kB lam T) (𝓝[>] 0) (𝓝 0) := by
  have hxlim := waveVar_tendsto_atTop_nhdsWithin h c kB T hh hc hk hT
  have hflim : Tendsto (fun lam : ℝ => wienProfile 5 (waveVar h c kB T lam))
      (𝓝[>] 0) (𝓝 0) :=
    (wienProfile_tendsto_zero_atTop 5).comp hxlim
  have heq : (fun lam => spectralRadianceWave h c kB lam T) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun lam => wavePrefactor h c kB T
        * wienProfile 5 (waveVar h c kB T lam)) := by
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    exact spectralRadianceWave_eq_profile h c kB T lam hh hc hk hT hlam
  have hC := hflim.const_mul (wavePrefactor h c kB T)
  rw [mul_zero] at hC
  exact hC.congr' heq.symm

/-- The frequency curve vanishes at infinity: `B(ν, T) → 0` as `ν → ∞`. -/
lemma spectralRadianceFreq_tendsto_zero_atTop (h c kB T : ℝ) (hh : 0 < h)
    (hc : 0 < c) (hk : 0 < kB) (hT : 0 < T) :
    Tendsto (fun nu => spectralRadianceFreq h c kB nu T) atTop (𝓝 0) := by
  have hxlim := freqVar_tendsto_atTop_atTop h kB T hh hk hT
  have hflim : Tendsto (fun nu : ℝ => wienProfile 3 (freqVar h kB T nu))
      atTop (𝓝 0) :=
    (wienProfile_tendsto_zero_atTop 3).comp hxlim
  have heq : (fun nu => spectralRadianceFreq h c kB nu T) =ᶠ[atTop]
      (fun nu => freqPrefactor h c kB T
        * wienProfile 3 (freqVar h kB T nu)) := by
    filter_upwards [eventually_gt_atTop 0] with nu hnu
    exact spectralRadianceFreq_eq_profile h c kB T nu hh hc hk hT hnu
  have hC := hflim.const_mul (freqPrefactor h c kB T)
  rw [mul_zero] at hC
  exact hC.congr' heq.symm

/-- The frequency curve vanishes at the origin: `B(ν, T) → 0` as `ν → 0⁺`. -/
lemma spectralRadianceFreq_tendsto_nhdsWithin_zero (h c kB T : ℝ) (hh : 0 < h)
    (hc : 0 < c) (hk : 0 < kB) (hT : 0 < T) :
    Tendsto (fun nu => spectralRadianceFreq h c kB nu T) (𝓝[>] 0) (𝓝 0) := by
  have hxlim := freqVar_tendsto_nhdsWithin h kB T hh hk hT
  have hflim : Tendsto (fun nu : ℝ => wienProfile 3 (freqVar h kB T nu))
      (𝓝[>] 0) (𝓝 0) :=
    (wienProfile_tendsto_nhdsWithin_zero 3 (by decide)).comp hxlim
  have heq : (fun nu => spectralRadianceFreq h c kB nu T) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun nu => freqPrefactor h c kB T
        * wienProfile 3 (freqVar h kB T nu)) := by
    filter_upwards [self_mem_nhdsWithin] with nu hnu
    exact spectralRadianceFreq_eq_profile h c kB T nu hh hc hk hT hnu
  have hC := hflim.const_mul (freqPrefactor h c kB T)
  rw [mul_zero] at hC
  exact hC.congr' heq.symm

/-- The wavelength curve attains its unique global maximum on `(0, ∞)` at
  `λ* = h c / (kB T x₅)`: the peak of the blackbody spectrum. -/
theorem spectralRadianceWave_isMaxOn (h c kB T : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hT : 0 < T) :
    IsMaxOn (fun lam => spectralRadianceWave h c kB lam T) (Ioi 0)
      (h * c / (kB * T * wienConstant5)) := by
  have hrpos : 0 < wienConstant5 := wienConstant5_pos
  have hlamstar : 0 < h * c / (kB * T * wienConstant5) :=
    div_pos (mul_pos hh hc) (mul_pos (mul_pos hk hT) hrpos)
  have hstar : waveVar h c kB T (h * c / (kB * T * wienConstant5))
      = wienConstant5 := by
    unfold waveVar
    have hk' : kB ≠ 0 := ne_of_gt hk
    have hT' : T ≠ 0 := ne_of_gt hT
    have hx5 : wienConstant5 ≠ 0 := ne_of_gt hrpos
    have hden : kB * T * wienConstant5 ≠ 0 :=
      mul_ne_zero (mul_ne_zero hk' hT') hx5
    field_simp
  have hC : 0 ≤ wavePrefactor h c kB T :=
    le_of_lt (wavePrefactor_pos h c kB T hh hc hk hT)
  intro lam hlam
  change spectralRadianceWave h c kB lam T
    ≤ spectralRadianceWave h c kB (h * c / (kB * T * wienConstant5)) T
  have hx : 0 < waveVar h c kB T lam :=
    waveVar_pos h c kB T lam hh hc hk hT hlam
  have hprof := (isMaxOn_iff.mp (wienProfile_isMaxOn 5 (by decide))) _ hx
  have hprof' : wienProfile 5 (waveVar h c kB T lam)
      ≤ wienProfile 5 wienConstant5 := hprof
  have e1 := spectralRadianceWave_eq_profile h c kB T lam hh hc hk hT hlam
  have e2 := spectralRadianceWave_eq_profile h c kB T _ hh hc hk hT hlamstar
  rw [e1, e2, hstar]
  exact mul_le_mul_of_nonneg_left hprof' hC

/-- The frequency curve attains its unique global maximum on `(0, ∞)` at
  `ν* = kB T x₃ / h`. -/
theorem spectralRadianceFreq_isMaxOn (h c kB T : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hT : 0 < T) :
    IsMaxOn (fun nu => spectralRadianceFreq h c kB nu T) (Ioi 0)
      (kB * T * wienConstant3 / h) := by
  have hrpos : 0 < wienConstant3 := wienConstant3_pos
  have hnustar : 0 < kB * T * wienConstant3 / h :=
    div_pos (mul_pos (mul_pos hk hT) hrpos) hh
  have hstar : freqVar h kB T (kB * T * wienConstant3 / h) = wienConstant3 := by
    unfold freqVar
    have hh' : h ≠ 0 := ne_of_gt hh
    have hk' : kB ≠ 0 := ne_of_gt hk
    have hT' : T ≠ 0 := ne_of_gt hT
    field_simp
  have hC : 0 ≤ freqPrefactor h c kB T :=
    le_of_lt (freqPrefactor_pos h c kB T hh hc hk hT)
  intro nu hnu
  change spectralRadianceFreq h c kB nu T
    ≤ spectralRadianceFreq h c kB (kB * T * wienConstant3 / h) T
  have hx : 0 < freqVar h kB T nu := freqVar_pos h kB T nu hh hk hT hnu
  have hprof := (isMaxOn_iff.mp (wienProfile_isMaxOn 3 (by decide))) _ hx
  have hprof' : wienProfile 3 (freqVar h kB T nu)
      ≤ wienProfile 3 wienConstant3 := hprof
  have e1 := spectralRadianceFreq_eq_profile h c kB T nu hh hc hk hT hnu
  have e2 := spectralRadianceFreq_eq_profile h c kB T _ hh hc hk hT hnustar
  rw [e1, e2, hstar]
  exact mul_le_mul_of_nonneg_left hprof' hC

/-- The wavelength curve is bounded above on `(0, ∞)` (by its peak value). -/
lemma spectralRadianceWave_bddAbove (h c kB T : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hT : 0 < T) :
    BddAbove (Set.range (fun lam => spectralRadianceWave h c kB lam T)) := by
  have hlamstar : 0 < h * c / (kB * T * wienConstant5) :=
    div_pos (mul_pos hh hc)
      (mul_pos (mul_pos hk hT) wienConstant5_pos)
  refine ⟨spectralRadianceWave h c kB (h * c / (kB * T * wienConstant5)) T, ?_⟩
  rintro _ ⟨lam, rfl⟩
  change spectralRadianceWave h c kB lam T
    ≤ spectralRadianceWave h c kB (h * c / (kB * T * wienConstant5)) T
  by_cases hlam : 0 < lam
  · exact (isMaxOn_iff.mp
      (spectralRadianceWave_isMaxOn h c kB T hh hc hk hT)) lam hlam
  · have h0 : spectralRadianceWave h c kB lam T = 0 :=
      spectralRadianceWave_eq_zero_of_nonpos_wave h c kB lam T (not_lt.mp hlam)
    rw [h0]
    exact le_of_lt
      (spectralRadianceWave_pos h c kB _ T hh hc hk hlamstar hT)

/-- The frequency curve is bounded above on `(0, ∞)` (by its peak value). -/
lemma spectralRadianceFreq_bddAbove (h c kB T : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hT : 0 < T) :
    BddAbove (Set.range (fun nu => spectralRadianceFreq h c kB nu T)) := by
  have hnustar : 0 < kB * T * wienConstant3 / h :=
    div_pos (mul_pos (mul_pos hk hT) wienConstant3_pos) hh
  refine ⟨spectralRadianceFreq h c kB (kB * T * wienConstant3 / h) T, ?_⟩
  rintro _ ⟨nu, rfl⟩
  change spectralRadianceFreq h c kB nu T
    ≤ spectralRadianceFreq h c kB (kB * T * wienConstant3 / h) T
  by_cases hnu : 0 < nu
  · exact (isMaxOn_iff.mp
      (spectralRadianceFreq_isMaxOn h c kB T hh hc hk hT)) nu hnu
  · have h0 : spectralRadianceFreq h c kB nu T = 0 :=
      spectralRadianceFreq_eq_zero_of_nonpos_freq h c kB nu T (not_lt.mp hnu)
    rw [h0]
    exact le_of_lt
      (spectralRadianceFreq_pos h c kB _ T hh hc hk hnustar hT)

/-!

## F. Wien's displacement laws

A critical point in `λ` forces `x = h c / (λ kB T)` to be a positive solution
of the Wien equation, hence equal to the Wien root by uniqueness. The product
`λ T` is therefore the same constant `h c / (kB x₅)` at every temperature;
likewise `ν / T = kB x₃ / h`.
-/

/-- Wien's displacement law (wavelength form) : critical wavelengths at different
  temperatures satisfy `λ₁ T₁ = λ₂ T₂`. -/
theorem wien_displacement_wave (h c kB T₁ T₂ lam₁ lam₂ : ℝ) (hh : 0 < h)
    (hc : 0 < c) (hk : 0 < kB) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hcrit₁ : deriv (fun lam => spectralRadianceWave h c kB lam T₁) lam₁ = 0)
    (hcrit₂ : deriv (fun lam => spectralRadianceWave h c kB lam T₂) lam₂ = 0) :
    lam₁ * T₁ = lam₂ * T₂ := by
  have hx₁ : 0 < waveVar h c kB T₁ lam₁ :=
    waveVar_pos h c kB T₁ lam₁ hh hc hk hT₁ hlam₁
  have hx₂ : 0 < waveVar h c kB T₂ lam₂ :=
    waveVar_pos h c kB T₂ lam₂ hh hc hk hT₂ hlam₂
  have e₁ := (wave_crit_iff h c kB T₁ lam₁ hh hc hk hT₁ hlam₁).mp hcrit₁
  have e₂ := (wave_crit_iff h c kB T₂ lam₂ hh hc hk hT₂ hlam₂).mp hcrit₂
  have hx₁' : wienH 5 (waveVar h c kB T₁ lam₁) = 0 := by
    unfold wienH
    linarith [e₁]
  have hx₂' : wienH 5 (waveVar h c kB T₂ lam₂) = 0 := by
    unfold wienH
    linarith [e₂]
  -- uniqueness forces the dimensionless variables to agree
  have huniq₁ := wienRoot_unique 5 five_gt_one _ hx₁ hx₁'
  have huniq₂ := wienRoot_unique 5 five_gt_one _ hx₂ hx₂'
  have hxx : waveVar h c kB T₁ lam₁ = waveVar h c kB T₂ lam₂ := by
    rw [huniq₁, huniq₂]
  -- hence `λ₁ T₁ = λ₂ T₂`
  have hh' : h ≠ 0 := ne_of_gt hh
  have hc' : c ≠ 0 := ne_of_gt hc
  have hk' : kB ≠ 0 := ne_of_gt hk
  unfold waveVar at hxx
  field_simp at hxx ⊢
  linarith [hxx]

/-- Wien's displacement law (frequency form) : critical frequencies at different
  temperatures satisfy `ν₁ / T₁ = ν₂ / T₂`. -/
theorem wien_displacement_freq (h c kB T₁ T₂ nu₁ nu₂ : ℝ) (hh : 0 < h)
    (hc : 0 < c) (hk : 0 < kB) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (hν₁ : 0 < nu₁) (hν₂ : 0 < nu₂)
    (hcrit₁ : deriv (fun nu => spectralRadianceFreq h c kB nu T₁) nu₁ = 0)
    (hcrit₂ : deriv (fun nu => spectralRadianceFreq h c kB nu T₂) nu₂ = 0) :
    nu₁ / T₁ = nu₂ / T₂ := by
  have hx₁ : 0 < freqVar h kB T₁ nu₁ := freqVar_pos h kB T₁ nu₁ hh hk hT₁ hν₁
  have hx₂ : 0 < freqVar h kB T₂ nu₂ := freqVar_pos h kB T₂ nu₂ hh hk hT₂ hν₂
  have e₁ := (freq_crit_iff h c kB T₁ nu₁ hh hc hk hT₁ hν₁).mp hcrit₁
  have e₂ := (freq_crit_iff h c kB T₂ nu₂ hh hc hk hT₂ hν₂).mp hcrit₂
  have hx₁' : wienH 3 (freqVar h kB T₁ nu₁) = 0 := by
    unfold wienH
    linarith [e₁]
  have hx₂' : wienH 3 (freqVar h kB T₂ nu₂) = 0 := by
    unfold wienH
    linarith [e₂]
  have huniq₁ := wienRoot_unique 3 three_gt_one _ hx₁ hx₁'
  have huniq₂ := wienRoot_unique 3 three_gt_one _ hx₂ hx₂'
  have hxx : freqVar h kB T₁ nu₁ = freqVar h kB T₂ nu₂ := by
    rw [huniq₁, huniq₂]
  have hh' : h ≠ 0 := ne_of_gt hh
  have hk' : kB ≠ 0 := ne_of_gt hk
  have hT₁' : T₁ ≠ 0 := ne_of_gt hT₁
  have hT₂' : T₂ ≠ 0 := ne_of_gt hT₂
  unfold freqVar at hxx
  field_simp at hxx ⊢
  linarith [hxx]

/-- The peak product `λ T` equals `h c / (kB x₅)` (wavelength Wien constant). -/
theorem wien_peak_product (h c kB T lam : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hT : 0 < T) (hlam : 0 < lam)
    (hcrit : deriv (fun lam => spectralRadianceWave h c kB lam T) lam = 0) :
    lam * T = h * c / (kB * wienRoot 5 five_gt_one) := by
  have hx : 0 < waveVar h c kB T lam := waveVar_pos h c kB T lam hh hc hk hT hlam
  have e := (wave_crit_iff h c kB T lam hh hc hk hT hlam).mp hcrit
  have hx' : wienH 5 (waveVar h c kB T lam) = 0 := by
    unfold wienH
    linarith [e]
  have huniq := wienRoot_unique 5 five_gt_one _ hx hx'
  have hrpos := wienRoot_pos 5 five_gt_one
  have hh' : h ≠ 0 := ne_of_gt hh
  have hc' : c ≠ 0 := ne_of_gt hc
  have hk' : kB ≠ 0 := ne_of_gt hk
  have hT' : T ≠ 0 := ne_of_gt hT
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hr' : wienRoot 5 five_gt_one ≠ 0 := ne_of_gt hrpos
  unfold waveVar at huniq
  field_simp at huniq ⊢
  linarith [huniq]

/-- The peak ratio `ν / T` equals `kB x₃ / h` (frequency Wien constant). -/
theorem wien_peak_ratio (h c kB T nu : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hk : 0 < kB) (hT : 0 < T) (hν : 0 < nu)
    (hcrit : deriv (fun nu => spectralRadianceFreq h c kB nu T) nu = 0) :
    nu / T = kB * wienRoot 3 three_gt_one / h := by
  have hx : 0 < freqVar h kB T nu := freqVar_pos h kB T nu hh hk hT hν
  have e := (freq_crit_iff h c kB T nu hh hc hk hT hν).mp hcrit
  have hx' : wienH 3 (freqVar h kB T nu) = 0 := by
    unfold wienH
    linarith [e]
  have huniq := wienRoot_unique 3 three_gt_one _ hx hx'
  have hh' : h ≠ 0 := ne_of_gt hh
  have hk' : kB ≠ 0 := ne_of_gt hk
  have hT' : T ≠ 0 := ne_of_gt hT
  unfold freqVar at huniq
  have h1 : h * nu = kB * T * wienRoot 3 three_gt_one := by
    field_simp at huniq; exact huniq
  field_simp
  linarith

/-- The Wien root is non-zero (it is a positive root of `h(x) = 0`). -/
lemma wienRoot_ne_zero (n : ℝ) (hn : 1 < n) : wienRoot n hn ≠ 0 :=
  ne_of_gt (wienRoot_pos n hn)

/-- The Wien root is at most `n` (non-strict version of `wienRoot_lt`). -/
lemma wienRoot_le_n (n : ℝ) (hn : 1 < n) : wienRoot n hn ≤ n :=
  le_of_lt (wienRoot_lt n hn)

end Blackbody
