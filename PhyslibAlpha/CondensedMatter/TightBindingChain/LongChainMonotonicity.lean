/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.LongChainLimit
public import Mathlib.Analysis.Real.Pi.Bounds
/-!

# `C_Nava` grows with the length of the chain

## i. Overview

From four sites on, `C_Nava` of the maximal current state is strictly increasing in the number
of sites `N`, and so it stays strictly below its long chain limit `√(π² / 3 - 2)`. With
`x = π / (N + 1)`, the closed form of `C_Nava²` is
`((π² / x² - 2π / x - 4 + 8x / π) / 3) tan² x - 2 + 4x / π`, whose derivative is negative on
`0 < x ≤ π / 5`. The sign follows from Taylor bounds for `sin` and `cos`, the bounds
`3.141592 < π < 3.141593`, and a Bernstein certificate for one polynomial of degree twelve.

## ii. Key results

- `cNavaSqForm_strictMonoOn` : the closed form of `C_Nava²` is strictly increasing on `n ≥ 5`.
- `CNava_lt_CNava` : `C_Nava` strictly increases with `N` from four sites on.
- `CNava_lt_sqrt_pi_sq_div_three_sub_two` : `C_Nava < √(π² / 3 - 2)` from four sites on.

## iii. Table of contents

- A. Taylor bounds
- B. A polynomial certificate
- C. The closed form in the angle
- D. Monotonicity

## iv. References

* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]
-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open Set Filter Topology
variable (T : TightBindingChain)

/-!

## A. Taylor bounds

-/

private lemma cos_le_taylor {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hderiv (t : ℝ) : deriv f t = -t + t ^ 3 / 6 + Real.sin t := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop) fun t ht => ?_
    rw [interior_Ici] at ht
    rw [hderiv]
    nlinarith [Real.sin_ge_sub_cube ht.le]
  have h := hmono (by simp) hx hx
  simp only [f, Real.cos_zero] at h
  linarith

private lemma sin_le_taylor {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let f : ℝ → ℝ := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t
  have hderiv (t : ℝ) : deriv f t = 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop) fun t ht => ?_
    rw [interior_Ici] at ht
    rw [hderiv]
    linarith [cos_le_taylor ht.le]
  have h := hmono (by simp) hx hx
  simp only [f, Real.sin_zero] at h
  linarith

/-!

## B. A polynomial certificate

-/

/-- The remainder of the derivative: a polynomial in `x` and `p = π`, of degree three in `p`. -/
private noncomputable def remainder (x p : ℝ) : ℝ :=
  (5 * x ^ 12 - 180 * x ^ 10 + 1880 * x ^ 8 - 7552 * x ^ 6 + 6720 * x ^ 4 + 34560 * x ^ 2 +
      69120) +
    (-384 * x ^ 5 + 7680 * x ^ 3 - 46080 * x) * p +
    (-160 * x ^ 6 + 2048 * x ^ 4 - 5760 * x ^ 2 - 11520) * p ^ 2 +
    (160 * x ^ 5 - 2144 * x ^ 3 + 7680 * x) * p ^ 3

/-- The remainder with `π` replaced by rational bounds, `3.141592` in the terms of degree one and
two in `p` and `3.141593` in the term of degree three, is negative on `0 ≤ x ≤ 1571 / 2500`:
all thirteen Bernstein coefficients are negative. -/
private lemma bound_poly_neg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1571 / 2500) :
    (5 * x ^ 12 - 180 * x ^ 10 + 1880 * x ^ 8 - 7552 * x ^ 6 + 6720 * x ^ 4 + 34560 * x ^ 2 +
        69120) +
      (-384 * x ^ 5 + 7680 * x ^ 3 - 46080 * x) * (3141592 / 1000000) +
      (-160 * x ^ 6 + 2048 * x ^ 4 - 5760 * x ^ 2 - 11520) * (3141592 / 1000000) ^ 2 +
      (160 * x ^ 5 - 2144 * x ^ 3 + 7680 * x) * (3141593 / 1000000) ^ 3 < 0 := by
  let u : ℝ := 2500 / 1571 * x
  have hu0 : 0 ≤ u := by positivity
  have hu1 : 0 ≤ 1 - u := by dsimp only [u]; linarith
  have hb0 : 0 ≤ u ^ 0 * (1 - u) ^ 12 := by positivity
  have hb1 : 0 ≤ u ^ 1 * (1 - u) ^ 11 := by positivity
  have hb2 : 0 ≤ u ^ 2 * (1 - u) ^ 10 := by positivity
  have hb3 : 0 ≤ u ^ 3 * (1 - u) ^ 9 := by positivity
  have hb4 : 0 ≤ u ^ 4 * (1 - u) ^ 8 := by positivity
  have hb5 : 0 ≤ u ^ 5 * (1 - u) ^ 7 := by positivity
  have hb6 : 0 ≤ u ^ 6 * (1 - u) ^ 6 := by positivity
  have hb7 : 0 ≤ u ^ 7 * (1 - u) ^ 5 := by positivity
  have hb8 : 0 ≤ u ^ 8 * (1 - u) ^ 4 := by positivity
  have hb9 : 0 ≤ u ^ 9 * (1 - u) ^ 3 := by positivity
  have hb10 : 0 ≤ u ^ 10 * (1 - u) ^ 2 := by positivity
  have hb11 : 0 ≤ u ^ 11 * (1 - u) ^ 1 := by positivity
  have hb12 : 0 ≤ u ^ 12 * (1 - u) ^ 0 := by positivity
  dsimp only [u] at hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 ⊢
  ring_nf at hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 ⊢
  linarith [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12]

/-- The remainder `P(x, π)` of the derivative is negative for `0 ≤ x ≤ 1571 / 2500`. -/
private lemma remainder_neg {x p : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1571 / 2500)
    (hp0 : 3141592 / 1000000 ≤ p) (hp1 : p ≤ 3141593 / 1000000) :
    remainder x p < 0 := by
  unfold remainder
  have hx2 : x ^ 2 ≤ 1 / 2 := by nlinarith
  have hB : -384 * x ^ 5 + 7680 * x ^ 3 - 46080 * x ≤ 0 := by nlinarith [sq_nonneg (x ^ 2)]
  have hC : -160 * x ^ 6 + 2048 * x ^ 4 - 5760 * x ^ 2 - 11520 ≤ 0 := by
    nlinarith [sq_nonneg (x ^ 2), pow_nonneg hx0 6]
  have hD : 0 ≤ 160 * x ^ 5 - 2144 * x ^ 3 + 7680 * x := by
    nlinarith [sq_nonneg (x ^ 2), pow_nonneg hx0 5, pow_nonneg hx0 3]
  have h1 := mul_le_mul_of_nonpos_left hp0 hB
  have h2 := mul_le_mul_of_nonpos_left (pow_le_pow_left₀ (by norm_num) hp0 2) hC
  have h3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hp1 3) hD
  linarith [bound_poly_neg hx0 hx1]

/-!

## C. The closed form in the angle

-/

/-- The closed form of `C_Nava²` in the angle `x = π / n`. -/
private noncomputable def angleForm (x : ℝ) : ℝ :=
  ((Real.pi ^ 2 / x ^ 2 - 2 * Real.pi / x - 4 + 8 * x / Real.pi) / 3) * Real.tan x ^ 2 - 2 +
    4 * x / Real.pi

private lemma cNavaSqForm_eq_angleForm {n : ℝ} (hn : 2 < n) :
    cNavaSqForm n = angleForm (Real.pi / n) := by
  have hn0 : n ≠ 0 := by positivity
  have hx : Real.pi / n ≠ 0 := div_ne_zero Real.pi_ne_zero hn0
  have hx0 : 0 < Real.pi / n := by positivity
  have hcos : Real.cos (Real.pi / n) ≠ 0 := by
    refine (Real.cos_pos_of_mem_Ioo (Set.mem_Ioo.mpr (And.intro ?_ ?_))).ne'
    · linarith [Real.pi_pos]
    · rw [div_lt_div_iff_of_pos_left Real.pi_pos (by linarith) two_pos]
      exact hn
  rw [cNavaSqForm, angleForm, Real.sinc_of_ne_zero hx, Real.tan_eq_sin_div_cos]
  simp only [div_pow, Real.sin_sq]
  field_simp
  ring

private lemma hasDerivAt_angleForm {x : ℝ} (hx : x ≠ 0) (hcos : Real.cos x ≠ 0) :
    HasDerivAt angleForm
      (((-2 * Real.pi ^ 2 / x ^ 3 + 2 * Real.pi / x ^ 2 + 8 / Real.pi) * Real.sin x ^ 2 *
          Real.cos x + 2 * (Real.pi ^ 2 / x ^ 2 - 2 * Real.pi / x - 4 + 8 * x / Real.pi) *
          Real.sin x + 12 / Real.pi * Real.cos x ^ 3) / (3 * Real.cos x ^ 3)) x := by
  unfold angleForm
  have da := (hasDerivAt_const x (Real.pi ^ 2)).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx)
  have db := (hasDerivAt_const x (2 * Real.pi)).div (hasDerivAt_id x) hx
  have dd := ((hasDerivAt_const x (8 : ℝ)).mul (hasDerivAt_id x)).div_const Real.pi
  have de := ((hasDerivAt_const x (4 : ℝ)).mul (hasDerivAt_id x)).div_const Real.pi
  have h := (((((da.sub db).sub (hasDerivAt_const x (4 : ℝ))).add dd).div_const 3).mul
    ((Real.hasDerivAt_tan hcos).pow 2)).sub (hasDerivAt_const x (2 : ℝ)) |>.add de
  refine h.congr_deriv ?_
  simp only [id_eq, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.div_apply]
  field_simp
  rw [show Real.sin x = Real.tan x * Real.cos x by rw [Real.tan_eq_sin_div_cos]; field_simp]
  ring

private lemma deriv_angleForm_neg {x : ℝ} (hx0 : 0 < x) (hx5 : x ≤ Real.pi / 5) :
    deriv angleForm x < 0 := by
  have hpL : (3141592 / 1000000 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d6]
  have hpU : Real.pi ≤ 3141593 / 1000000 := by linarith [Real.pi_lt_d6]
  have hx1 : x ≤ 1571 / 2500 := by linarith
  have hcospos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hx2 : x ^ 2 < 6 := by nlinarith
  have hsin0 : 0 < x - x ^ 3 / 6 := by nlinarith [mul_pos hx0 (show 0 < 6 - x ^ 2 by linarith)]
  have hcl0 : 0 < 1 - x ^ 2 / 2 := by nlinarith
  set q := Real.pi ^ 2 / x ^ 2 - 2 * Real.pi / x - 4 + 8 * x / Real.pi with hq
  set qp := -2 * Real.pi ^ 2 / x ^ 3 + 2 * Real.pi / x ^ 2 + 8 / Real.pi with hqp
  have hqpos : 0 < q := by
    rw [hq, show Real.pi ^ 2 / x ^ 2 - 2 * Real.pi / x - 4 + 8 * x / Real.pi =
      (Real.pi ^ 3 - 2 * Real.pi ^ 2 * x - 4 * Real.pi * x ^ 2 + 8 * x ^ 3) /
        (x ^ 2 * Real.pi) by field_simp]
    apply div_pos _ (by positivity)
    nlinarith [mul_pos hx0 Real.pi_pos, sq_nonneg x]
  have hqpneg : qp < 0 := by
    rw [hqp, show -2 * Real.pi ^ 2 / x ^ 3 + 2 * Real.pi / x ^ 2 + 8 / Real.pi =
      (-2 * Real.pi ^ 3 + 2 * Real.pi ^ 2 * x + 8 * x ^ 3) / (x ^ 3 * Real.pi) by
        field_simp]
    apply div_neg_of_neg_of_pos _ (by positivity)
    nlinarith [mul_pos hx0 Real.pi_pos, sq_nonneg x]
  have hsl := Real.sin_ge_sub_cube hx0.le
  have hsu := sin_le_taylor hx0.le
  have hcl : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  have hcu := cos_le_taylor hx0.le
  have hprod : (x - x ^ 3 / 6) ^ 2 * (1 - x ^ 2 / 2) ≤ Real.sin x ^ 2 * Real.cos x :=
    mul_le_mul (pow_le_pow_left₀ hsin0.le hsl 2) hcl hcl0.le (sq_nonneg _)
  have hupper : qp * (Real.sin x ^ 2 * Real.cos x) + 2 * q * Real.sin x +
      12 / Real.pi * Real.cos x ^ 3 ≤ qp * ((x - x ^ 3 / 6) ^ 2 * (1 - x ^ 2 / 2)) +
        2 * q * (x - x ^ 3 / 6 + x ^ 5 / 120) +
        12 / Real.pi * (1 - x ^ 2 / 2 + x ^ 4 / 24) ^ 3 := by
    have h1 := mul_le_mul_of_nonpos_left hprod hqpneg.le
    have h2 := mul_le_mul_of_nonneg_left hsu (by positivity : 0 ≤ 2 * q)
    have h3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hcospos.le hcu 3)
      (by positivity : 0 ≤ 12 / Real.pi)
    linarith
  have hrem : Real.pi * (qp * ((x - x ^ 3 / 6) ^ 2 * (1 - x ^ 2 / 2)) +
      2 * q * (x - x ^ 3 / 6 + x ^ 5 / 120) + 12 / Real.pi * (1 - x ^ 2 / 2 + x ^ 4 / 24) ^ 3) =
      remainder x Real.pi / 5760 := by
    rw [hq, hqp, remainder]
    field_simp
    ring
  have hneg := remainder_neg hx0.le hx1 hpL hpU
  have hnum : qp * (Real.sin x ^ 2 * Real.cos x) + 2 * q * Real.sin x +
      12 / Real.pi * Real.cos x ^ 3 < 0 := by
    refine hupper.trans_lt (neg_of_mul_neg_right ?_ Real.pi_pos.le)
    rw [hrem]
    linarith
  rw [(hasDerivAt_angleForm hx0.ne' hcospos.ne').deriv]
  refine div_neg_of_neg_of_pos ?_ (by positivity)
  rw [← hq, ← hqp]
  linarith

private lemma angleForm_strictAntiOn : StrictAntiOn angleForm (Ioc 0 (Real.pi / 5)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioc 0 (Real.pi / 5)) (fun x hx => ?_) fun x hx => ?_
  · have hcos : 0 < Real.cos x :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
    exact (hasDerivAt_angleForm hx.1.ne' hcos.ne').continuousAt.continuousWithinAt
  · rw [interior_Ioc] at hx
    exact deriv_angleForm_neg hx.1 hx.2.le

/-!

## D. Monotonicity

-/

private lemma CNava_nonneg : 0 ≤ T.CNava := div_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)

/-- The closed form of `C_Nava²` is strictly increasing on `n ≥ 5`, that is, from four sites on. -/
lemma cNavaSqForm_strictMonoOn : StrictMonoOn cNavaSqForm (Ici 5) := by
  intro m hm n hn hmn
  have hm' : (5 : ℝ) ≤ m := hm
  have hn' : (5 : ℝ) ≤ n := hn
  rw [cNavaSqForm_eq_angleForm (by linarith), cNavaSqForm_eq_angleForm (by linarith)]
  refine angleForm_strictAntiOn ⟨div_pos Real.pi_pos (by linarith), ?_⟩
    ⟨div_pos Real.pi_pos (by linarith), ?_⟩ ?_
  · exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)
  · exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hm'
  · exact div_lt_div_of_pos_left Real.pi_pos (by linarith) hmn

/-- **Monotonicity.** From four sites on, `C_Nava` strictly increases with the number of sites. -/
theorem CNava_lt_CNava {T T' : TightBindingChain} (ht : T.t ≠ 0) (ht' : T'.t ≠ 0)
    (hN : 4 ≤ T.N) (hNN' : T.N < T'.N) : T.CNava < T'.CNava := by
  have h4 : (5 : ℝ) ≤ T.N + 1 := by
    have : (4 : ℝ) ≤ T.N := by exact_mod_cast hN
    linarith
  have hlt : (T.N : ℝ) + 1 < T'.N + 1 := by exact_mod_cast Nat.succ_lt_succ hNN'
  have h := cNavaSqForm_strictMonoOn h4 (show (5 : ℝ) ≤ T'.N + 1 by linarith) hlt
  rw [← CNava_sq_eq_cNavaSqForm T ht (by omega),
    ← CNava_sq_eq_cNavaSqForm T' ht' (by omega)] at h
  exact lt_of_pow_lt_pow_left₀ 2 (CNava_nonneg _) h

/-- From four sites on, `C_Nava` stays strictly below its long chain limit `√(π² / 3 - 2)`. -/
theorem CNava_lt_sqrt_pi_sq_div_three_sub_two (ht : T.t ≠ 0) (hN : 4 ≤ T.N) :
    T.CNava < √(Real.pi ^ 2 / 3 - 2) := by
  have h5 : (5 : ℝ) ≤ T.N + 1 := by
    have : (4 : ℝ) ≤ T.N := by exact_mod_cast hN
    linarith
  have hle : cNavaSqForm (T.N + 2) ≤ Real.pi ^ 2 / 3 - 2 := by
    refine ge_of_tendsto tendsto_cNavaSqForm ?_
    filter_upwards [eventually_ge_atTop ((T.N : ℝ) + 2)] with n hn
    exact cNavaSqForm_strictMonoOn.monotoneOn (by simp; linarith) (by simp; linarith) hn
  have hlt := cNavaSqForm_strictMonoOn h5 (show (5 : ℝ) ≤ T.N + 2 by linarith)
    (by linarith : (T.N : ℝ) + 1 < T.N + 2)
  rw [← CNava_sq_eq_cNavaSqForm T ht (by omega)] at hlt
  rw [← Real.sqrt_sq (CNava_nonneg T)]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) (hlt.trans_le hle)

end TightBindingChain
end CondensedMatter
