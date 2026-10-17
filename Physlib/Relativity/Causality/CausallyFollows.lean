/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import Physlib.Relativity.Causality.TimeLike
public import Physlib.Relativity.Causality.LightLike
/-!

# Vectors in the causal future of the origin

## i. Overview

A vector `u` with `causallyFollows 0 u` is future-directed causal: time-like or light-like with a
nonnegative time component (`causallyFollows_zero_iff`). For two such vectors of Minkowski space
(signature `+---`), the Minkowski product dominates the product of the Minkowski norms,
`⟪u, v⟫ₘ ≥ √⟪u, u⟫ₘ √⟪v, v⟫ₘ` (reverse Cauchy-Schwarz inequality), and the Minkowski norm of the
sum dominates the sum of the norms, `√⟪u + v, u + v⟫ₘ ≥ √⟪u, u⟫ₘ + √⟪v, v⟫ₘ` (reverse triangle
inequality). The proofs reduce to the elementary inequality `√(a² - c²) √(b² - d²) ≤ a b - c d` for
`0 ≤ c ≤ a`, `0 ≤ d ≤ b`, applied to the time components and the Euclidean norms of the spatial
parts, together with the Euclidean Cauchy-Schwarz inequality.

## ii. Key results

- `causallyFollows_zero_iff`: `causallyFollows 0 u ↔ 0 ≤ ⟪u, u⟫ₘ ∧ 0 ≤ u⁰`;
  `causallyFollows_zero_sub`: `q - p` is in the causal future of `0` when `q` causally follows `p`.
- `norm_spatialPart_le_timeComponent_of_causallyFollows`: `‖u_spatial‖ ≤ u⁰`.
- `sqrt_mul_sqrt_le_minkowskiProduct_of_causallyFollows`: the reverse Cauchy-Schwarz inequality.
- `sqrt_add_sqrt_le_sqrt_add_of_causallyFollows`: the reverse triangle inequality;
  `causallyFollows_zero_add_of_causallyFollows`.
- `minkowskiProduct_eq_iff_of_causallyFollows`: equality in the reverse Cauchy-Schwarz inequality
  holds if and only if the two vectors are proportional (with a nonnegative factor).
- `sqrt_add_eq_iff_of_causallyFollows`: equality in the reverse triangle inequality holds if and
  only if equality holds in the reverse Cauchy-Schwarz inequality.

## iii. Table of contents

- A. The causal future of the origin
- B. The reverse Cauchy-Schwarz inequality
- C. The reverse triangle inequality
- D. The equality cases

-/

@[expose] public section

namespace Lorentz

namespace Vector

open InnerProductSpace

/-!

## A. The causal future of the origin

-/

/-- A vector is in the causal future of the origin if and only if it is time-like or light-like
  (`0 ≤ ⟪u, u⟫ₘ`) with a nonnegative time component. -/
lemma causallyFollows_zero_iff {d : ℕ} {u : Vector d} :
    causallyFollows 0 u ↔ 0 ≤ ⟪u, u⟫ₘ ∧ 0 ≤ u.timeComponent := by
  simp only [causallyFollows, interiorFutureLightCone, futureLightConeBoundary, Set.mem_ofPred_eq,
    sub_zero, timeLike_iff_norm_sq_pos, lightLike_iff_norm_sq_zero]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1.le, h2.le⟩
    · exact ⟨h1.ge, h2⟩
  · rintro ⟨h1, h2⟩
    rcases h1.lt_or_eq with h1 | h1
    · left
      refine ⟨h1, lt_of_le_of_ne h2 fun h0 => ?_⟩
      have h := minkowskiProduct_self_le_timeComponent_sq u
      have h0' : u.timeComponent = 0 := h0.symm
      rw [h0'] at h
      norm_num at h
      linarith
    · right
      exact ⟨h1.symm, h2⟩

/-- The vector from `p` to `q` is in the causal future of the origin when `q` causally
  follows `p`. -/
lemma causallyFollows_zero_sub {d : ℕ} {p q : Vector d} (h : causallyFollows p q) :
    causallyFollows 0 (q - p) := by
  simpa only [causallyFollows, interiorFutureLightCone, futureLightConeBoundary, Set.mem_ofPred_eq,
    sub_zero] using h

/-!

## B. The reverse Cauchy-Schwarz inequality

-/

/-- For a vector in the causal future of the origin, the Euclidean norm of the spatial part is at
  most the time component. -/
lemma norm_spatialPart_le_timeComponent_of_causallyFollows {d : ℕ} {u : Vector d}
    (hu : causallyFollows 0 u) : ‖u.spatialPart‖ ≤ u.timeComponent := by
  obtain ⟨h1, _⟩ := causallyFollows_zero_iff.mp hu
  rw [minkowskiProduct_self_eq_sq_sub] at h1
  nlinarith [norm_nonneg u.spatialPart]

/-- The reverse Cauchy-Schwarz inequality: for `u`, `v` in the causal future of the origin,
  `√⟪u, u⟫ₘ √⟪v, v⟫ₘ ≤ ⟪u, v⟫ₘ`. -/
lemma sqrt_mul_sqrt_le_minkowskiProduct_of_causallyFollows {d : ℕ} {u v : Vector d}
    (hu : causallyFollows 0 u) (hv : causallyFollows 0 v) : √⟪u, u⟫ₘ * √⟪v, v⟫ₘ ≤ ⟪u, v⟫ₘ := by
  have hu' := norm_spatialPart_le_timeComponent_of_causallyFollows hu
  have hv' := norm_spatialPart_le_timeComponent_of_causallyFollows hv
  rw [minkowskiProduct_self_eq_sq_sub u, minkowskiProduct_self_eq_sq_sub v,
    minkowskiProduct_eq_timeComponent_spatialPart u v]
  have hcs := real_inner_le_norm u.spatialPart v.spatialPart
  set a := u.timeComponent
  set c := ‖u.spatialPart‖
  set b := v.timeComponent
  set e := ‖v.spatialPart‖
  have hc0 : 0 ≤ c := norm_nonneg _
  have he0 : 0 ≤ e := norm_nonneg _
  have helem : √(a ^ 2 - c ^ 2) * √(b ^ 2 - e ^ 2) ≤ a * b - c * e := by
    -- the elementary inequality `√(a² - c²) √(b² - e²) ≤ a b - c e` for `0 ≤ c ≤ a`, `0 ≤ e ≤ b`:
    -- indeed `(a b - c e)² - (a² - c²)(b² - e²) = (a e - b c)²`
    have h1 : 0 ≤ a ^ 2 - c ^ 2 := by nlinarith
    have h2 : 0 ≤ a * b - c * e := by nlinarith
    calc √(a ^ 2 - c ^ 2) * √(b ^ 2 - e ^ 2) = √((a ^ 2 - c ^ 2) * (b ^ 2 - e ^ 2)) :=
          (Real.sqrt_mul h1 _).symm
      _ ≤ √((a * b - c * e) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a * e - b * c)])
      _ = a * b - c * e := Real.sqrt_sq h2
  linarith

/-!

## C. The reverse triangle inequality

-/

/-- The reverse triangle inequality: for `u`, `v` in the causal future of the origin,
  `√⟪u, u⟫ₘ + √⟪v, v⟫ₘ ≤ √⟪u + v, u + v⟫ₘ`. -/
lemma sqrt_add_sqrt_le_sqrt_add_of_causallyFollows {d : ℕ} {u v : Vector d}
    (hu : causallyFollows 0 u) (hv : causallyFollows 0 v) :
    √⟪u, u⟫ₘ + √⟪v, v⟫ₘ ≤ √⟪u + v, u + v⟫ₘ := by
  have hcs := sqrt_mul_sqrt_le_minkowskiProduct_of_causallyFollows hu hv
  have hu1 := (causallyFollows_zero_iff.mp hu).1
  have hv1 := (causallyFollows_zero_iff.mp hv).1
  have hsum : (√⟪u, u⟫ₘ + √⟪v, v⟫ₘ) ^ 2 ≤ ⟪u + v, u + v⟫ₘ := by
    rw [minkowskiProduct_add_self, add_sq, Real.sq_sqrt hu1, Real.sq_sqrt hv1]
    linarith
  exact Real.le_sqrt_of_sq_le hsum

/-- The sum of two vectors in the causal future of the origin is in the causal future of the
  origin. -/
lemma causallyFollows_zero_add_of_causallyFollows {d : ℕ} {u v : Vector d}
    (hu : causallyFollows 0 u) (hv : causallyFollows 0 v) : causallyFollows 0 (u + v) := by
  obtain ⟨hu1, hu2⟩ := causallyFollows_zero_iff.mp hu
  obtain ⟨hv1, hv2⟩ := causallyFollows_zero_iff.mp hv
  refine causallyFollows_zero_iff.mpr ⟨?_, ?_⟩
  · have hcs := sqrt_mul_sqrt_le_minkowskiProduct_of_causallyFollows hu hv
    have hsq : 0 ≤ (√⟪u, u⟫ₘ + √⟪v, v⟫ₘ) ^ 2 := sq_nonneg _
    rw [add_sq, Real.sq_sqrt hu1, Real.sq_sqrt hv1] at hsq
    rw [minkowskiProduct_add_self]
    linarith
  · show 0 ≤ (u + v) (Sum.inl 0)
    rw [apply_add]
    exact add_nonneg hu2 hv2

/-!

## D. The equality cases

-/

/-- Equality in the reverse Cauchy-Schwarz inequality: for `u`, `v` in the causal future of the
  origin, `⟪u, v⟫ₘ = √⟪u, u⟫ₘ √⟪v, v⟫ₘ` if and only if one of the vectors is a nonnegative
  multiple of the other. -/
lemma minkowskiProduct_eq_iff_of_causallyFollows {d : ℕ} {u v : Vector d} (hu : causallyFollows 0 u)
    (hv : causallyFollows 0 v) :
    ⟪u, v⟫ₘ = √⟪u, u⟫ₘ * √⟪v, v⟫ₘ ↔ ∃ μ : ℝ, 0 ≤ μ ∧ (v = μ • u ∨ u = μ • v) := by
  have hu1 := (causallyFollows_zero_iff.mp hu).1
  have hu2 := (causallyFollows_zero_iff.mp hu).2
  have hv1 := (causallyFollows_zero_iff.mp hv).1
  have hv2 := (causallyFollows_zero_iff.mp hv).2
  constructor
  · intro heq
    have hu' := norm_spatialPart_le_timeComponent_of_causallyFollows hu
    have hv' := norm_spatialPart_le_timeComponent_of_causallyFollows hv
    have hcs := real_inner_le_norm u.spatialPart v.spatialPart
    rw [minkowskiProduct_self_eq_sq_sub u, minkowskiProduct_self_eq_sq_sub v,
      minkowskiProduct_eq_timeComponent_spatialPart u v] at heq
    set a := u.timeComponent with ha
    set c := ‖u.spatialPart‖ with hc
    set b := v.timeComponent with hb
    set e := ‖v.spatialPart‖ with he
    have hc0 : 0 ≤ c := norm_nonneg _
    have he0 : 0 ≤ e := norm_nonneg _
    -- the elementary inequality `√(a² - c²) √(b² - e²) ≤ a b - c e` for `0 ≤ c ≤ a`, `0 ≤ e ≤ b`:
    -- indeed `(a b - c e)² - (a² - c²)(b² - e²) = (a e - b c)²`
    have helem : √(a ^ 2 - c ^ 2) * √(b ^ 2 - e ^ 2) ≤ a * b - c * e := by
      have h1 : 0 ≤ a ^ 2 - c ^ 2 := by nlinarith
      have h2 : 0 ≤ a * b - c * e := by nlinarith
      calc √(a ^ 2 - c ^ 2) * √(b ^ 2 - e ^ 2) = √((a ^ 2 - c ^ 2) * (b ^ 2 - e ^ 2)) :=
            (Real.sqrt_mul h1 _).symm
        _ ≤ √((a * b - c * e) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a * e - b * c)])
        _ = a * b - c * e := Real.sqrt_sq h2
    have hinner : ⟪u.spatialPart, v.spatialPart⟫_ℝ = c * e := by linarith
    have hsq : √(a ^ 2 - c ^ 2) * √(b ^ 2 - e ^ 2) = a * b - c * e := by linarith
    have h1 : (a ^ 2 - c ^ 2) * (b ^ 2 - e ^ 2) = (a * b - c * e) ^ 2 := by
      have := congrArg (· ^ 2) hsq
      rw [mul_pow, Real.sq_sqrt (by nlinarith), Real.sq_sqrt (by nlinarith)] at this
      exact this
    have hadbc : a * e - b * c = 0 := by
      have : (a * e - b * c) ^ 2 = 0 := by linear_combination (-1 : ℝ) * h1
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    have hpar := inner_eq_norm_mul_iff_real.mp hinner
    have hcomp : ∀ i, e * u (Sum.inr i) = c * v (Sum.inr i) := fun i => by
      have := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) hpar
      simpa [spatialPart_apply_eq_toCoord] using this
    by_cases ha0 : a = 0
    · have hcz : c = 0 := le_antisymm (ha0 ▸ hu') hc0
      have hu0 : u = 0 :=
        eq_zero_of_timeComponent_of_spatialPart ha0 (norm_eq_zero.mp hcz)
      exact ⟨0, le_rfl, Or.inr (by rw [hu0, zero_smul])⟩
    · have hapos : 0 < a := lt_of_le_of_ne hu2 (Ne.symm ha0)
      refine ⟨b / a, div_nonneg hv2 hapos.le, Or.inl ?_⟩
      refine ext_of_apply fun i => ?_
      rw [apply_smul]
      rcases i with i | i
      · fin_cases i
        show b = b / a * a
        field_simp
      · have key : a * v (Sum.inr i) = b * u (Sum.inr i) := by
          by_cases hcz : c = 0
          · have hez : e = 0 := by
              have : a * e = 0 := by rw [hcz] at hadbc; linarith
              exact (mul_eq_zero.mp this).resolve_left ha0
            rw [apply_inr_eq_zero_of_norm_spatialPart hcz,
              apply_inr_eq_zero_of_norm_spatialPart hez]
            ring
          · have h := hcomp i
            apply mul_left_cancel₀ hcz
            linear_combination (-a) * h + u (Sum.inr i) * hadbc
        show v (Sum.inr i) = b / a * u (Sum.inr i)
        field_simp
        linarith
  · rintro ⟨μ, hμ, h | h⟩
    · subst h
      rw [sqrt_minkowskiProduct_smul_self hμ u, map_smul, smul_eq_mul]
      have := Real.mul_self_sqrt hu1
      linear_combination μ * this.symm
    · subst h
      rw [sqrt_minkowskiProduct_smul_self hμ v, map_smul, smul_apply, smul_eq_mul]
      have := Real.mul_self_sqrt hv1
      linear_combination μ * this.symm

/-- Equality in the reverse triangle inequality holds if and only if equality holds in the
  reverse Cauchy-Schwarz inequality. -/
lemma sqrt_add_eq_iff_of_causallyFollows {d : ℕ} {u v : Vector d} (hu : causallyFollows 0 u)
    (hv : causallyFollows 0 v) :
    √⟪u + v, u + v⟫ₘ = √⟪u, u⟫ₘ + √⟪v, v⟫ₘ ↔ ⟪u, v⟫ₘ = √⟪u, u⟫ₘ * √⟪v, v⟫ₘ := by
  have hu1 := (causallyFollows_zero_iff.mp hu).1
  have hv1 := (causallyFollows_zero_iff.mp hv).1
  have hsum := minkowskiProduct_add_self u v
  have hnn := (causallyFollows_zero_iff.mp (causallyFollows_zero_add_of_causallyFollows hu hv)).1
  constructor
  · intro h
    have h2 := congrArg (· ^ 2) h
    rw [Real.sq_sqrt hnn, add_sq, Real.sq_sqrt hu1, Real.sq_sqrt hv1] at h2
    linarith
  · intro h
    rw [Real.sqrt_eq_iff_mul_self_eq hnn (by positivity), hsum, h]
    have := Real.mul_self_sqrt hu1
    have := Real.mul_self_sqrt hv1
    ring_nf
    nlinarith [Real.mul_self_sqrt hu1, Real.mul_self_sqrt hv1]

end Vector

end Lorentz
