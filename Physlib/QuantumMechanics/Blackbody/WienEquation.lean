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
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Topology.Order.IntermediateValue

/-!

# The Wien equation and the Planck profile

The transcendental equation `x = n (1 - e⁻ˣ)`, its unique positive root, and
the dimensionless Planck profile `xⁿ / (eˣ - 1)`. This file contains only the
mathematical preliminaries; the physical spectral radiance and Wien's
displacement laws are in the `WiensLaw` module.

## i. Overview

For `n > 1` the auxiliary function `h(x) = x - n (1 - e⁻ˣ)` has a unique
positive zero `x*`, which lies in `(log n, n)`. The named physical cases are
`x₅` (wavelength) and `x₃` (frequency).

Everything downstream goes through `wienRoot`, so once the Lambert W function
lands in Mathlib (or in `Physlib.Mathematics.ForMathlib`), `wienRoot` can be
redefined in terms of the principal branch as `n + W₀(-n * e⁻ⁿ)` without
rebuilding this file.

The Planck profile `f(x) = xⁿ / (eˣ - 1)` is positive on `(0, ∞)`, rises
strictly up to `x*`, falls strictly afterwards, and vanishes at both ends.
Consequently `x*` is a global maximizer of `f` on `(0, ∞)`.

## ii. Key results

- `wienH`: the auxiliary function `h(x) = x - n (1 - e⁻ˣ)`.
- `hasDerivAt_wienH`: its derivative is `1 - n e⁻ˣ`.
- `wienH_strictMonoOn` / `wienH_strictAntiOn`: monotonicity on either side of
  `log n`.
- `wien_exists_root`: existence of a root in `(log n, n)` for `n > 1`.
- `wienRoot`: the unique positive root.
- `wienRoot_unique`: every positive solution of the Wien equation is `wienRoot`.
- `wienConstant5` / `wienConstant3`: the named roots for `n = 5` and `n = 3`.
- `wienProfile`: the dimensionless Planck profile `xⁿ / (eˣ - 1)`.
- `wienProfile_crit_iff`: critical points solve the Wien equation.
- `wienProfile_deriv_eq`: factored derivative of the profile.
- `wienProfile_isMaxOn`: the Wien root is the global maximizer of the profile.
- `wienProfile_tendsto_zero_atTop` / `wienProfile_tendsto_nhdsWithin_zero`:
  the profile vanishes at both ends.

## iii. Table of contents

- A. The Wien auxiliary function
- B. The named Wien constants
- C. The Planck profile and its critical points
- D. The profile maximum and its boundary behaviour

## iv. References

* https://en.wikipedia.org/wiki/Wien%27s_displacement_law
* W. Wien, "Eine neue Beziehung der Strahlung schwarzer Körper zum zweiten
  Hauptsatz der Wärmetheorie", Sitzungsber. Preuss. Akad. Wiss. (1893).
-/

@[expose] public section
noncomputable section

namespace BlackBody

open Set Filter Topology

/-!

## A. The Wien auxiliary function

The function `h(x) = x - n (1 - e⁻ˣ)` vanishes exactly when the derivative of
the Planck profile vanishes. Its shape is elementary: decreasing up to
`log n`, increasing afterwards, with `h(0) = 0` and `h(log n) < 0`, so it has
one positive zero in `(log n, n)`.
-/

/-- The Wien auxiliary function `h(x) = x - n (1 - e⁻ˣ)`. Its positive zeros
  are the solutions of the Wien equation `x = n (1 - e⁻ˣ)`. -/
noncomputable def wienH (n x : ℝ) : ℝ := x - n * (1 - Real.exp (-x))

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
  argument applied on `[log n, n]`. -/
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

/-- The unique positive solution of the Wien equation `x = n (1 - e⁻ˣ)`. -/
noncomputable def wienRoot (n : ℝ) (hn : 1 < n) : ℝ :=
  Classical.choose (wien_exists_root n hn)

/-- The Wien root lies above `log n`. -/
lemma wienRoot_gt_log (n : ℝ) (hn : 1 < n) : Real.log n < wienRoot n hn :=
  (Classical.choose_spec (wien_exists_root n hn)).1

/-- The Wien root satisfies the Wien equation. -/
lemma wienRoot_eq (n : ℝ) (hn : 1 < n) : wienH n (wienRoot n hn) = 0 :=
  (Classical.choose_spec (wien_exists_root n hn)).2.2

/-- The Wien root is positive. -/
lemma wienRoot_pos (n : ℝ) (hn : 1 < n) : 0 < wienRoot n hn :=
  lt_trans (Real.log_pos hn) (wienRoot_gt_log n hn)

/-- Any positive solution of the Wien equation equals the Wien root: on
  `(0, log n]` the auxiliary function is strictly negative, and on
  `[log n, ∞)` it is strictly increasing. -/
lemma wienRoot_unique (n : ℝ) (hn : 1 < n) (x : ℝ) (hx : 0 < x)
    (hx0 : wienH n x = 0) : x = wienRoot n hn := by
  rcases le_total x (Real.log n) with hle | hge
  · have hanti := wienH_strictAntiOn n hn
    have h0mem : (0 : ℝ) ∈ Iic (Real.log n) :=
      mem_Iic.mpr (le_trans hx.le hle)
    have hxmem : x ∈ Iic (Real.log n) := mem_Iic.mpr hle
    have hlt : wienH n x < wienH n 0 := hanti h0mem hxmem hx
    rw [show wienH n 0 = 0 by simp [wienH], hx0] at hlt
    exact absurd hlt (lt_irrefl 0)
  · have hmono := wienH_strictMonoOn n hn
    have hxmem : x ∈ Ici (Real.log n) := mem_Ici.mpr hge
    have hrmem : wienRoot n hn ∈ Ici (Real.log n) :=
      mem_Ici.mpr (wienRoot_gt_log n hn).le
    exact hmono.injOn hxmem hrmem (by rw [hx0, wienRoot_eq n hn])

/-!

## B. The named Wien constants

The named roots for the two physical cases: `x₅ ≈ 4.9651142317` for wavelength
and `x₃ ≈ 2.8214393721` for frequency. They are the peaks of the respective
Planck curves; their equality or difference is not needed to state or prove the
displacement laws.
-/

/-- The Wien constant for wavelength: the unique positive root of
  `x = 5(1 - e⁻ˣ)`, numerically `x₅ ≈ 4.9651142317`. -/
noncomputable def wienConstant5 : ℝ := wienRoot 5 (by norm_num)

/-- The Wien constant for frequency: the unique positive root of
  `x = 3(1 - e⁻ˣ)`, numerically `x₃ ≈ 2.8214393721`. -/
noncomputable def wienConstant3 : ℝ := wienRoot 3 (by norm_num)

/-- `x₅ > 0`. -/
lemma wienConstant5_pos : 0 < wienConstant5 := wienRoot_pos 5 (by norm_num)

/-- `x₃ > 0`. -/
lemma wienConstant3_pos : 0 < wienConstant3 := wienRoot_pos 3 (by norm_num)

/-!

## C. The Planck profile and its critical points

The profile `f(x) = xⁿ / (eˣ - 1)` is the dimensionless shape shared by every
parametrization of Planck's law. Its critical points are exactly the positive
solutions of the Wien equation.
-/

/-- The Planck shape function `xⁿ / (eˣ - 1)`. -/
noncomputable def wienProfile (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n / (Real.exp x - 1)

/-- The Planck profile is strictly positive for positive `x` (positive
  radiation energy at finite frequency). -/
lemma wienProfile_pos (n : ℕ) (x : ℝ) (hx : 0 < x) :
    0 < wienProfile n x := by
  unfold wienProfile
  apply div_pos (pow_pos hx n)
  linarith [Real.one_lt_exp_iff.mpr hx]

/-- The Planck profile is non-negative for non-negative `x`. -/
lemma wienProfile_nonneg (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ wienProfile n x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [wienProfile]
  · exact le_of_lt (wienProfile_pos n x hx)

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

/-- Critical points of the Planck profile are exactly the solutions of the Wien
  equation `x = n (1 - e⁻ˣ)`. -/
lemma wienProfile_crit_iff (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 0 < x) :
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
    simpa [wienH] using hlt
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

/-!

## D. The profile maximum and its boundary behaviour

The sign of `f'` is the opposite of the sign of `h`, so `f` rises strictly on
`(0, x*]` and falls strictly on `[x*, ∞)`. Mathlib's derivative test packages
this directly into the statement that `x*` is a global maximizer. The profile
also vanishes at both ends: at `∞` the exponential beats the polynomial, and
at `0` the bound `eˣ - 1 ≥ x` gives `f(x) ≤ xⁿ⁻¹`.
-/

/-- The Planck profile attains its global maximum on `(0, ∞)` at the Wien root.
  This is the mathematical core of Wien's displacement law: the "peak" of the
  blackbody spectrum. -/
lemma wienProfile_isMaxOn (n : ℕ) (hn : 2 ≤ n) :
    IsMaxOn (wienProfile n) (Ioi 0)
      (wienRoot n (by exact_mod_cast lt_of_lt_of_le one_lt_two hn)) := by
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hn
  have hn1 : 1 ≤ n := le_trans one_le_two hn
  set r := wienRoot n hnR with hr
  have hrpos : 0 < r := lt_trans (Real.log_pos hnR) (wienRoot_gt_log n hnR)
  have hexp : ∀ y : ℝ, 0 < y → Real.exp y - 1 ≠ 0 := fun y hy =>
    ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hy))
  have hdiff0 : DifferentiableOn ℝ (wienProfile n) (Ioo 0 r) := by
    intro x hx
    exact (hasDerivAt_wienProfile n x (hexp x hx.1)).differentiableAt.differentiableWithinAt
  have hdiff1 : DifferentiableOn ℝ (wienProfile n) (Ioi r) := by
    intro x hx
    exact (hasDerivAt_wienProfile n x
      (hexp x (lt_trans hrpos hx))).differentiableAt.differentiableWithinAt
  refine isMaxOn_Ioi_of_deriv ((hasDerivAt_wienProfile n r (hexp r hrpos)).continuousAt)
    hdiff0 hdiff1 ?_ ?_
  · intro x hx
    obtain ⟨hx0, hxr⟩ := hx
    have he : Real.exp x - 1 ≠ 0 :=
      ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx0))
    rw [wienProfile_deriv_eq n hn1 x he]
    apply le_of_lt
    apply div_pos _ (pow_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx0)) 2)
    exact neg_pos.mpr (mul_neg_of_pos_of_neg
      (mul_pos (pow_pos hx0 _) (Real.exp_pos _))
      (wienH_neg_on_Ioo n hnR x hx0 (by simpa [hr] using hxr)))
  · intro x hx
    have hx0 : 0 < x := lt_trans hrpos hx
    have he : Real.exp x - 1 ≠ 0 :=
      ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx0))
    rw [wienProfile_deriv_eq n hn1 x he]
    apply le_of_lt
    apply div_neg_of_neg_of_pos _ (pow_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx0)) 2)
    exact neg_lt_zero.mpr (mul_pos (mul_pos (pow_pos hx0 _) (Real.exp_pos _))
      (wienH_pos_on_Ioi n hnR x (by simpa [hr] using hx)))

/-- The Planck profile vanishes at infinity: the exponential in the
  denominator dominates the polynomial numerator. -/
lemma wienProfile_tendsto_zero_atTop (n : ℕ) :
    Tendsto (fun x => wienProfile n x) atTop (𝓝 0) := by
  have hnum : Tendsto (fun x : ℝ => x ^ n * Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n
  have hden : Tendsto (fun x : ℝ => 1 - Real.exp (-x)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub Real.tendsto_exp_neg_atTop_nhds_zero
  have hlim : Tendsto (fun x : ℝ => x ^ n * Real.exp (-x) / (1 - Real.exp (-x)))
      atTop (𝓝 (0 / 1)) := hnum.div hden (by norm_num)
  rw [zero_div] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold wienProfile
  rw [Real.exp_neg]
  field_simp

/-- The Planck profile vanishes at the origin (for `n ≥ 2`): near `x = 0`,
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

end BlackBody
