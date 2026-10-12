/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.Mathematics.TauCeti.Analysis.PositiveDefinite.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Continuity of positive-definite functions

This file records the standard continuity upgrade for positive-definite functions on a seminormed
additive group with the negation involution.

## i. Overview

This file records the standard continuity upgrade for positive-definite functions on a seminormed
additive group with the negation involution. A positive-definite function that is continuous at
the origin is uniformly continuous. The file also records the local estimates
`‖F x - F y‖² ≤ 2 F(0).re ((F 0).re - (F (x + star y)).re)` and
`‖F x - F y‖² ≤ 2 F(0).re ‖F (x + star y) - F 0‖` at points satisfying
`x + star x = 0` and `y + star y = 0`, together with their specializations to additive groups
whose involution is negation.

This advances Part C of the `OneParameterSemigroups` roadmap, whose positive-definite-function
API asks for the basic fact "continuity at `0` ⇒ uniform continuity" before Bochner's theorem.

## ii. Key results

In the namespace `TauCeti.IsPositiveDefinite`:

* `norm_sub_sq_le_two_mul_map_zero_re_mul_re_sub_of_star_eq_neg`:
  the local real-part continuity estimate.
* `norm_sub_sq_le_two_mul_map_zero_re_mul_re_sub_of_add_star_eq_zero`:
  the monoid-level local real-part continuity estimate.
* `norm_sub_sq_le_two_mul_map_zero_re_mul_norm_sub_of_star_eq_neg`:
  the local norm-valued continuity estimate.
* `norm_sub_sq_le_two_mul_map_zero_re_mul_norm_sub_of_add_star_eq_zero`:
  the monoid-level local norm-valued continuity estimate.
* `norm_sub_sq_le_two_mul_map_zero_re_mul_re_sub_of_forall_star_eq_neg` and
  `norm_sub_sq_le_two_mul_map_zero_re_mul_norm_sub_of_forall_star_eq_neg`:
  specializations to a globally negating involution.
* `uniformContinuous_of_continuousAt_zero_of_forall_star_eq_neg`:
  continuity at `0` implies uniform continuity.

## iii. Table of contents

- A. Development

## iv. References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

/-! ## A. Development -/

open ComplexConjugate
open scoped ComplexOrder

namespace TauCeti

namespace IsPositiveDefinite

section Algebra

variable {E : Type*} [AddMonoid E] [StarAddMonoid E] {F : E → ℂ}

private lemma gram_three_add_star_expand_of_values
    {x y : E} {lam : ℂ} {c : Fin 3 → ℂ} {p : Fin 3 → E}
    (hc0 : c 0 = 1) (hc1 : c 1 = -1) (hc2 : c 2 = lam)
    (hp0 : p 0 = x) (hp1 : p 1 = y) (hp2 : p 2 = 0) (hx : x + star x = 0) (hy : y + star y = 0)
    (hyx : F (y + star x) = conj (F (x + star y)))
    (hnx : F (star x) = conj (F x)) (hny : F (0 + star y) = conj (F y)) : (∑ i : Fin 3, ∑ j : Fin 3,
      c i * conj (c j) * F (p i + star (p j)))
      = F 0 - F (x + star y) + conj lam * F x - conj (F (x + star y)) + F 0
        - conj lam * F y + lam * conj (F x) - lam * conj (F y)
        + lam * conj lam * F 0 := by
  simp only [Fin.sum_univ_three, hc0, hc1, hc2, hp0, hp1, hp2]
  rw [hx, hy, star_zero, zero_add, add_zero, hyx, hnx, hny]
  simp only [map_one, mul_one, one_mul, map_neg, mul_neg, neg_mul, neg_neg, add_zero]
  ring_nf

private lemma gram_three_add_star_expand {x y : E} (hx : x + star x = 0) (hy : y + star y = 0)
    (hyx : F (y + star x) = conj (F (x + star y)))
    (hnx : F (star x) = conj (F x)) (hny : F (0 + star y) = conj (F y)) {lam : ℂ} :
    (∑ i : Fin 3, ∑ j : Fin 3,
      ![1, -1, lam] i * conj (![1, -1, lam] j) *
        F (![x, y, 0] i + star (![x, y, 0] j)))
      = F 0 - F (x + star y) + conj lam * F x - conj (F (x + star y)) + F 0
        - conj lam * F y + lam * conj (F x) - lam * conj (F y)
        + lam * conj lam * F 0 := by
  exact gram_three_add_star_expand_of_values (F := F) (x := x) (y := y)
    (c := ![1, -1, lam]) (p := ![x, y, 0]) rfl rfl rfl rfl rfl rfl
    hx hy hyx hnx hny

-- The remaining calculation is pure complex algebra after `F 0` has been normalized to a
-- positive real scalar and `lam = -d / F 0` has been substituted.
private lemma gram_three_sub_re_complex_algebra {r : ℝ} {z d lam : ℂ}
    (hlam : lam = -d / (r : ℂ)) (hr : 0 < r) :
    ((r : ℂ) - z + conj lam * d - conj z + (r : ℂ) + lam * conj d
        + lam * conj lam * (r : ℂ)).re
      = 2 * r - 2 * z.re - Complex.normSq d / r := by
  rw [hlam]
  field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
  simp [Complex.normSq_apply]
  field_simp [hr.ne']
  ring_nf

private lemma gram_three_add_star_re_algebra (hF : IsPositiveDefinite F)
    {x y : E} (hx : x + star x = 0) (hy : y + star y = 0)
    (hyx : F (y + star x) = conj (F (x + star y)))
    (hnx : F (star x) = conj (F x)) (hny : F (0 + star y) = conj (F y)) {C d lam : ℂ}
    (hC : C = F 0) (hd : d = F x - F y) (hlam : lam = -d / C) (hCpos : 0 < (F 0).re) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      ![1, -1, lam] i * conj (![1, -1, lam] j) *
        F (![x, y, 0] i + star (![x, y, 0] j))).re
      = 2 * (F 0).re - 2 * (F (x + star y)).re - Complex.normSq d / (F 0).re := by
  rw [gram_three_add_star_expand hx hy hyx hnx hny]
  have hCreal : F 0 = ((F 0).re : ℂ) := hF.map_zero_eq_ofReal_re
  have hstructured :
      (F 0 - F (x + star y) + conj lam * F x - conj (F (x + star y)) + F 0
          - conj lam * F y + lam * conj (F x) - lam * conj (F y)
          + lam * conj lam * F 0).re
        = (((F 0).re : ℂ) - F (x + star y) + conj lam * d - conj (F (x + star y))
          + ((F 0).re : ℂ) + lam * conj d
          + lam * conj lam * ((F 0).re : ℂ)).re := by
    rw [hCreal, hd]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, neg_mul, sub_neg_eq_add, mul_neg, Complex.mul_im, Complex.ofReal_im,
      mul_zero, sub_zero, map_sub, Complex.sub_im, add_left_inj]
    ring_nf
  rw [hstructured]
  have hlam' : lam = -d / ((F 0).re : ℂ) := by
    rw [hC, hCreal] at hlam
    exact hlam
  exact gram_three_sub_re_complex_algebra hlam' hCpos

private lemma gram_three_add_star_re_eq (hF : IsPositiveDefinite F)
    {x y : E} (hx : x + star x = 0) (hy : y + star y = 0) {C d lam : ℂ}
    (hC : C = F 0) (hd : d = F x - F y) (hlam : lam = -d / C) (hCpos : 0 < (F 0).re) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      ![1, -1, lam] i * conj (![1, -1, lam] j) *
        F (![x, y, 0] i + star (![x, y, 0] j))).re
      = 2 * (F 0).re - 2 * (F (x + star y)).re - Complex.normSq d / (F 0).re := by
  have hyx : F (y + star x) = conj (F (x + star y)) := by
    have h := hF.conj_symm x y
    simpa using congrArg conj h
  have hnx : F (star x) = conj (F x) := by
    have h := hF.conj_symm x 0
    simpa using congrArg conj h
  have hny : F (0 + star y) = conj (F y) := by
    have h := hF.conj_symm y 0
    simpa using congrArg conj h
  exact hF.gram_three_add_star_re_algebra hx hy hyx hnx hny hC hd hlam hCpos

/-- The local monoid-level real-part form of the standard positive-definite continuity estimate. -/
lemma norm_sub_sq_le_two_mul_map_zero_re_mul_re_sub_of_add_star_eq_zero
    (hF : IsPositiveDefinite F) {x y : E} (hx : x + star x = 0) (hy : y + star y = 0) :
    ‖F x - F y‖ ^ 2
      ≤ 2 * (F 0).re * ((F 0).re - (F (x + star y)).re) := by
  by_cases hC0 : (F 0).re = 0
  · simp [hF.apply_eq_zero_of_map_zero_re_eq_zero hC0]
  have hCpos : 0 < (F 0).re := lt_of_le_of_ne hF.map_zero_re_nonneg (Ne.symm hC0)
  let C : ℂ := F 0
  let d : ℂ := F x - F y
  let lam : ℂ := -d / C
  have hQ := hF 3 ![1, -1, lam] ![x, y, 0]
  have hQre : 0 ≤ (∑ i : Fin 3, ∑ j : Fin 3,
      ![1, -1, lam] i * conj (![1, -1, lam] j) *
        F (![x, y, 0] i + star (![x, y, 0] j))).re :=
    (Complex.nonneg_iff.mp hQ).1
  have hQcalc :
      (∑ i : Fin 3, ∑ j : Fin 3,
        ![1, -1, lam] i * conj (![1, -1, lam] j) *
          F (![x, y, 0] i + star (![x, y, 0] j))).re
        = 2 * (F 0).re - 2 * (F (x + star y)).re - Complex.normSq d / (F 0).re := by
    exact hF.gram_three_add_star_re_eq hx hy rfl rfl rfl hCpos
  have hmain : Complex.normSq d ≤ (F 0).re *
      (2 * (F 0).re - 2 * (F (x + star y)).re) := by
    have hdiv :
        Complex.normSq d / (F 0).re ≤ 2 * (F 0).re - 2 * (F (x + star y)).re := by
      linarith
    have hmul := (div_le_iff₀ hCpos).mp hdiv
    nlinarith
  calc
    ‖F x - F y‖ ^ 2 = Complex.normSq d := by
      simp [d, Complex.normSq_eq_norm_sq]
    _ ≤ (F 0).re * (2 * (F 0).re - 2 * (F (x + star y)).re) := hmain
    _ = 2 * (F 0).re * ((F 0).re - (F (x + star y)).re) := by ring

/-- The local monoid-level norm-valued form of the standard positive-definite continuity
estimate. -/
lemma norm_sub_sq_le_two_mul_map_zero_re_mul_norm_sub_of_add_star_eq_zero
    (hF : IsPositiveDefinite F) {x y : E} (hx : x + star x = 0) (hy : y + star y = 0) :
    ‖F x - F y‖ ^ 2 ≤ 2 * (F 0).re * ‖F (x + star y) - F 0‖ := by
  have hre :
      (F 0).re - (F (x + star y)).re ≤ ‖F (x + star y) - F 0‖ := by
    have h₁ : (F 0).re - (F (x + star y)).re
        = -((F (x + star y) - F 0).re) := by
      simp [Complex.sub_re]
    rw [h₁]
    exact (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  exact (hF.norm_sub_sq_le_two_mul_map_zero_re_mul_re_sub_of_add_star_eq_zero hx hy).trans
    (mul_le_mul_of_nonneg_left hre (mul_nonneg zero_le_two hF.map_zero_re_nonneg))

end Algebra

section GroupAlgebra

variable {E : Type*} [AddGroup E] [StarAddMonoid E] {F : E → ℂ}

/-- The local real-part form of the standard positive-definite continuity estimate. -/
lemma norm_sub_sq_le_two_mul_map_zero_re_mul_re_sub_of_star_eq_neg (hF : IsPositiveDefinite F)
    {x y : E} (hx : star x = -x) (hy : star y = -y) :
    ‖F x - F y‖ ^ 2
      ≤ 2 * (F 0).re * ((F 0).re - (F (x - y)).re) := by
  have hx0 : x + star x = 0 := by rw [hx, add_neg_cancel]
  have hy0 : y + star y = 0 := by rw [hy, add_neg_cancel]
  simpa [hy, sub_eq_add_neg] using
    hF.norm_sub_sq_le_two_mul_map_zero_re_mul_re_sub_of_add_star_eq_zero hx0 hy0

/-- The real-part form of the standard positive-definite continuity estimate under a globally
negating involution. -/
lemma norm_sub_sq_le_two_mul_map_zero_re_mul_re_sub_of_forall_star_eq_neg
    (hF : IsPositiveDefinite F) (hstar : ∀ x : E, star x = -x) (x y : E) :
    ‖F x - F y‖ ^ 2
      ≤ 2 * (F 0).re * ((F 0).re - (F (x - y)).re) :=
  hF.norm_sub_sq_le_two_mul_map_zero_re_mul_re_sub_of_star_eq_neg (hstar x) (hstar y)

/-- The local norm-valued form of the standard positive-definite continuity estimate. -/
lemma norm_sub_sq_le_two_mul_map_zero_re_mul_norm_sub_of_star_eq_neg (hF : IsPositiveDefinite F)
    {x y : E} (hx : star x = -x) (hy : star y = -y) :
    ‖F x - F y‖ ^ 2 ≤ 2 * (F 0).re * ‖F (x - y) - F 0‖ := by
  have hx0 : x + star x = 0 := by rw [hx, add_neg_cancel]
  have hy0 : y + star y = 0 := by rw [hy, add_neg_cancel]
  simpa [hy, sub_eq_add_neg] using
    hF.norm_sub_sq_le_two_mul_map_zero_re_mul_norm_sub_of_add_star_eq_zero hx0 hy0

/-- The norm-valued form of the standard positive-definite continuity estimate under a globally
negating involution. -/
lemma norm_sub_sq_le_two_mul_map_zero_re_mul_norm_sub_of_forall_star_eq_neg
    (hF : IsPositiveDefinite F) (hstar : ∀ x : E, star x = -x) (x y : E) :
    ‖F x - F y‖ ^ 2 ≤ 2 * (F 0).re * ‖F (x - y) - F 0‖ :=
  hF.norm_sub_sq_le_two_mul_map_zero_re_mul_norm_sub_of_star_eq_neg (hstar x) (hstar y)

end GroupAlgebra

section Topology

variable {E : Type*} [SeminormedAddGroup E] [StarAddMonoid E] {F : E → ℂ}

/-- A positive-definite function on a seminormed additive group with the negation involution is
uniformly continuous as soon as it is continuous at the origin. -/
lemma uniformContinuous_of_continuousAt_zero_of_forall_star_eq_neg (hF : IsPositiveDefinite F)
    (hstar : ∀ x : E, star x = -x) (hcont : ContinuousAt F 0) :
    UniformContinuous F := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  by_cases hC0 : (F 0).re = 0
  · refine ⟨1, zero_lt_one, fun x y _ => ?_⟩
    simp [hF.apply_eq_zero_of_map_zero_re_eq_zero hC0, hε]
  have hCpos : 0 < (F 0).re := lt_of_le_of_ne hF.map_zero_re_nonneg (Ne.symm hC0)
  let η : ℝ := ε ^ 2 / (2 * (F 0).re)
  have hη : 0 < η := div_pos (sq_pos_of_pos hε) (mul_pos zero_lt_two hCpos)
  have hev := (Metric.tendsto_nhds.mp hcont) η hη
  rcases Metric.eventually_nhds_iff.mp hev with ⟨δ, hδ, hδF⟩
  refine ⟨δ, hδ, fun x y hxy => ?_⟩
  have hadd_comm : ∀ a b : E, a + b = b + a := by
    intro a b
    have hneg_comm : -(-a) + -(-b) = -(-b) + -(-a) := by
      calc
        -(-a) + -(-b) = star (-a) + star (-b) := by rw [hstar, hstar]
        _ = star ((-a) + (-b)) := (star_add (-a) (-b)).symm
        _ = -((-a) + (-b)) := hstar ((-a) + (-b))
        _ = -(-b) + -(-a) := neg_add_rev (-a) (-b)
    simpa using hneg_comm
  have hxy_norm : ‖x + -y‖ < δ := by
    rw [SeminormedAddGroup.dist_eq] at hxy
    simpa [sub_eq_add_neg, hadd_comm, ← norm_neg (x + -y)] using hxy
  have hdist : dist (x - y) 0 < δ := by
    simpa [SeminormedAddGroup.dist_eq, sub_eq_add_neg, ← norm_neg (x + -y)] using hxy_norm
  have hsmall : ‖F (x - y) - F 0‖ < η := by
    simpa [dist_eq_norm] using hδF hdist
  have hsquare_le : ‖F x - F y‖ ^ 2 < ε ^ 2 := by
    have hbound :=
      hF.norm_sub_sq_le_two_mul_map_zero_re_mul_norm_sub_of_forall_star_eq_neg hstar x y
    calc
      ‖F x - F y‖ ^ 2 ≤ 2 * (F 0).re * ‖F (x - y) - F 0‖ := hbound
      _ < 2 * (F 0).re * η := mul_lt_mul_of_pos_left hsmall (mul_pos zero_lt_two hCpos)
      _ = 2 * (F 0).re * (ε ^ 2 / (2 * (F 0).re)) := by rfl
      _ = ε ^ 2 := by
        field_simp [(mul_pos zero_lt_two hCpos).ne']
  have habs := sq_lt_sq.mp hsquare_le
  simpa [dist_eq_norm, abs_of_nonneg hε.le] using habs

end Topology

end IsPositiveDefinite

end TauCeti
