/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Calculus.IteratedFDerivBounds
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!

# Exponential twists of compactly supported functions

Multiplying a compactly supported function by `exp (a ℓ x)` moves it by `O (|a|)` in every
derivative.

## i. Overview

For a continuous linear functional `ℓ` the twist `x ↦ exp (a ℓ x)` is smooth. Its derivatives of
order `i` are bounded by `(|a| ‖ℓ‖)^i exp (|a| ‖ℓ‖ ‖x‖)`. The twist minus one is bounded by
`|a| ‖ℓ‖ ‖x‖ exp (|a| ‖ℓ‖ ‖x‖)`. A Leibniz estimate turns these into a bound for the derivatives
of `twist * v - v` by `|a|` times a constant and the derivative bounds of `v`.

## ii. Key results

- `ExpTwist.twist` : the function `x ↦ exp (a ℓ x)`.
- `ExpTwist.norm_iteratedFDeriv_twist_le` : the derivatives of the twist.
- `ExpTwist.norm_iteratedFDeriv_twist_mul_sub_le` : the derivatives of `twist * v - v`.

## iii. Table of contents

- A. The twist
- B. The Leibniz estimate

## iv. References

None.

## A. The twist

- `ExpTwist.twist` : the function `x ↦ exp (a ℓ x)`.
- `ExpTwist.norm_iteratedFDeriv_twist_le` : the derivatives of the twist.

## B. The Leibniz estimate

- `ExpTwist.norm_iteratedFDeriv_twist_mul_sub_le` : the derivatives of `twist * v - v`.
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace ExpTwist

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- exp (a ℓ x) -/
def twist (ℓ : E →L[ℝ] ℝ) (a : ℝ) (x : E) : ℝ := Real.exp (a * ℓ x)

lemma contDiff_twist (ℓ : E →L[ℝ] ℝ) (a : ℝ) : ContDiff ℝ ∞ (twist ℓ a) :=
  Real.contDiff_exp.comp (contDiff_const.mul ℓ.contDiff)

lemma norm_iteratedFDeriv_exp (i : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ i Real.exp y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma norm_iteratedFDeriv_twist_le (ℓ : E →L[ℝ] ℝ) (a : ℝ) (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (twist ℓ a) x‖ ≤ (|a| * ‖ℓ‖) ^ i * Real.exp (|a| * ‖ℓ‖ * ‖x‖) := by
  have h : twist ℓ a = Real.exp ∘ ((a • ℓ : E →L[ℝ] ℝ)) := by
    funext x; simp [twist]
  have h1 : ‖iteratedFDeriv ℝ i (Real.exp ∘ ⇑(a • ℓ)) x‖ ≤
      ‖iteratedFDeriv ℝ i Real.exp ((a • ℓ) x)‖ * ‖a • ℓ‖ ^ i := by
    rw [ContinuousLinearMap.iteratedFDeriv_comp_right (a • ℓ) Real.contDiff_exp x
      (by exact_mod_cast le_top)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h]
  refine h1.trans ?_
  rw [norm_iteratedFDeriv_exp]
  have hn : ‖a • ℓ‖ ≤ |a| * ‖ℓ‖ := by
    simp [norm_smul]
  have hx : (a • ℓ) x ≤ |a| * ‖ℓ‖ * ‖x‖ := by
    calc (a • ℓ) x ≤ ‖(a • ℓ) x‖ := le_abs_self _
      _ ≤ ‖a • ℓ‖ * ‖x‖ := (a • ℓ).le_opNorm x
      _ ≤ _ := by gcongr
  rw [mul_comm]
  gcongr

lemma abs_exp_sub_one_le (y : ℝ) : |Real.exp y - 1| ≤ |y| * Real.exp |y| := by
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy, abs_of_nonneg (by linarith [Real.add_one_le_exp y])]
    have := Real.add_one_le_exp (-y)
    rw [Real.exp_neg] at this
    have h2 : 0 < Real.exp y := Real.exp_pos y
    have : (1 - y) * Real.exp y ≤ 1 := by
      calc (1 - y) * Real.exp y ≤ (Real.exp y)⁻¹ * Real.exp y := by gcongr; linarith
        _ = 1 := inv_mul_cancel₀ h2.ne'
    nlinarith
  · rw [abs_of_nonpos hy, abs_of_nonpos (by linarith [Real.exp_le_one_iff.2 hy])]
    have := Real.add_one_le_exp y
    have h3 : 1 ≤ Real.exp (-y) := Real.one_le_exp (by linarith)
    nlinarith [mul_nonneg (neg_nonneg.2 hy) (sub_nonneg.2 h3)]

lemma abs_twist_sub_one_le (ℓ : E →L[ℝ] ℝ) (a : ℝ) (x : E) :
    |twist ℓ a x - 1| ≤ |a| * ‖ℓ‖ * ‖x‖ * Real.exp (|a| * ‖ℓ‖ * ‖x‖) := by
  have h := abs_exp_sub_one_le (a * ℓ x)
  have h1 : |a * ℓ x| ≤ |a| * ‖ℓ‖ * ‖x‖ := by
    rw [abs_mul, mul_assoc]
    gcongr
    simpa using ℓ.le_opNorm x
  refine h.trans ?_
  calc |a * ℓ x| * Real.exp |a * ℓ x| ≤ _ := by
        gcongr

lemma norm_iteratedFDeriv_twist_sub_one_le (ℓ : E →L[ℝ] ℝ) {a R : ℝ} (ha : |a| ≤ 1) {x : E}
    (hx : ‖x‖ ≤ R) (k i : ℕ) (hi : i ≤ k) :
    ‖iteratedFDeriv ℝ i (fun y => twist ℓ a y - 1) x‖ ≤
      |a| * ((1 + R) * (1 + ‖ℓ‖) ^ (k + 1) * Real.exp (‖ℓ‖ * R)) := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hx
  have hE : Real.exp (|a| * ‖ℓ‖ * ‖x‖) ≤ Real.exp (‖ℓ‖ * R) := by
    apply Real.exp_le_exp.2
    calc |a| * ‖ℓ‖ * ‖x‖ ≤ 1 * ‖ℓ‖ * R := by gcongr
      _ = _ := by ring
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp only [norm_iteratedFDeriv_zero]
    refine (abs_twist_sub_one_le ℓ a x).trans ?_
    calc |a| * ‖ℓ‖ * ‖x‖ * Real.exp (|a| * ‖ℓ‖ * ‖x‖)
        = |a| * (‖ℓ‖ * ‖x‖) * Real.exp (|a| * ‖ℓ‖ * ‖x‖) := by ring
      _ ≤ |a| * (‖ℓ‖ * R) * Real.exp (‖ℓ‖ * R) := by gcongr
      _ ≤ |a| * ((1 + R) * (1 + ‖ℓ‖) ^ (k + 1) * Real.exp (‖ℓ‖ * R)) := by
          have h1 : ‖ℓ‖ * R ≤ (1 + R) * (1 + ‖ℓ‖) ^ (k + 1) := by
            have : 1 + ‖ℓ‖ ≤ (1 + ‖ℓ‖) ^ (k + 1) := by
              simpa using pow_le_pow_right₀ (a := 1 + ‖ℓ‖) (by linarith [norm_nonneg ℓ])
                (Nat.le_add_left 1 k)
            nlinarith [norm_nonneg ℓ]
          calc |a| * (‖ℓ‖ * R) * Real.exp (‖ℓ‖ * R)
              = |a| * ((‖ℓ‖ * R) * Real.exp (‖ℓ‖ * R)) := by ring
            _ ≤ _ := by
              have hh := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (‖ℓ‖ * R)).le
              nlinarith [abs_nonneg a]
  · have hsub : iteratedFDeriv ℝ i (fun y => twist ℓ a y - 1) x =
        iteratedFDeriv ℝ i (twist ℓ a) x := by
      have h := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := i) (f := twist ℓ a)
        (g := fun _ : E => (1 : ℝ)) (x := x)
        (((contDiff_twist ℓ a).of_le (by exact_mod_cast le_top)).contDiffAt)
        ((contDiff_const (c := (1 : ℝ))).contDiffAt)
      rw [iteratedFDeriv_const_of_ne hpos.ne'] at h
      have h2 := h
      simp only [Pi.zero_apply, sub_zero] at h2
      exact h2
    rw [hsub]
    refine (norm_iteratedFDeriv_twist_le ℓ a i x).trans ?_
    have hai : |a| ^ i ≤ |a| := by
      calc |a| ^ i ≤ |a| ^ 1 := pow_le_pow_of_le_one (abs_nonneg a) ha hpos
        _ = |a| := pow_one _
    have hli : ‖ℓ‖ ^ i ≤ (1 + ‖ℓ‖) ^ (k + 1) :=
      (pow_le_pow_left₀ (norm_nonneg _) (by linarith) i).trans
        (pow_le_pow_right₀ (by linarith [norm_nonneg ℓ]) (by omega))
    rw [mul_pow]
    calc |a| ^ i * ‖ℓ‖ ^ i * Real.exp (|a| * ‖ℓ‖ * ‖x‖)
        ≤ |a| * (1 + ‖ℓ‖) ^ (k + 1) * Real.exp (‖ℓ‖ * R) := by gcongr
      _ ≤ _ := by
        have : 1 ≤ 1 + R := by linarith
        have h0 : 0 ≤ |a| * ((1 + ‖ℓ‖) ^ (k + 1) * Real.exp (‖ℓ‖ * R)) := by positivity
        nlinarith [mul_nonneg h0 hR]

/-- **The twist moves a compactly supported function by `O(|a|)` in every derivative.** -/
lemma norm_iteratedFDeriv_twist_mul_sub_le (ℓ : E →L[ℝ] ℝ) {a R : ℝ} (hR : 0 ≤ R) (ha : |a| ≤ 1)
    (v : E → ℝ) (hv : ContDiff ℝ ∞ v) (hvs : tsupport v ⊆ Metric.closedBall 0 R) (k : ℕ) {S : ℝ}
    (hS : ∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j v y‖ ≤ S) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y => twist ℓ a y * v y - v y) x‖ ≤
      2 ^ k * (|a| * ((1 + R) * (1 + ‖ℓ‖) ^ (k + 1) * Real.exp (‖ℓ‖ * R))) * S := by
  have hfun : (fun y => twist ℓ a y * v y - v y) = fun y => (twist ℓ a y - 1) * v y := by
    funext y; ring
  rw [hfun]
  by_cases hx : ‖x‖ ≤ R
  · exact IteratedFDerivBounds.norm_iteratedFDeriv_mul_le_two_pow _ v
      (((contDiff_twist ℓ a).sub contDiff_const)) hv x k
      (fun i hi => norm_iteratedFDeriv_twist_sub_one_le ℓ ha hx k i hi) (fun j _ => hS j ‹_› x)
  · have hxs : x ∉ tsupport v := fun h => hx (by simpa using hvs h)
    have h0 : iteratedFDeriv ℝ k (fun y => (twist ℓ a y - 1) * v y) x = 0 := by
      by_contra hne
      have hmem : x ∈ Function.support (iteratedFDeriv ℝ k fun y => (twist ℓ a y - 1) * v y) := hne
      have := support_iteratedFDeriv_subset (𝕜 := ℝ) k hmem
      exact hxs (tsupport_mul_subset_right this)
    rw [h0, norm_zero]
    have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0 (Nat.zero_le _) x)
    positivity

end ExpTwist
