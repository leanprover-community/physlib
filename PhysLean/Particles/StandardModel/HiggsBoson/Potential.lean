/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.StandardModel.HiggsBoson.Basic
public import Mathlib.Tactic.Cases
/-!
# The potential of the Higgs field

We define the potential of the Higgs field.

We show that the potential is a smooth function on spacetime.

-/

@[expose] public section

noncomputable section

namespace StandardModel

namespace HiggsField

open Manifold
open Matrix
open Complex
open ComplexConjugate
open SpaceTime

/-!

## The Higgs potential

-/

/-- The structure `Potential` is defined with two fields, `μ2` corresponding
  to the mass-squared of the Higgs boson, and `l` corresponding to the coefficient
  of the quartic term in the Higgs potential. Note that `l` is usually denoted `λ`. -/
structure Potential where
  /-- The mass-squared of the Higgs boson. -/
  μ2 : ℝ
  /-- The quartic coupling of the Higgs boson. Usually denoted λ. -/
  𝓵 : ℝ

namespace Potential

variable (P : Potential)

/-- Given a element `P` of `Potential`, `P.toFun` is Higgs potential.
  It is defined for a Higgs field `φ` and a spacetime point `x` as

  `-μ² ‖φ‖_H^2 x + l * ‖φ‖_H^2 x * ‖φ‖_H^2 x`. -/
def toFun (φ : HiggsField) (x : SpaceTime) : ℝ :=
  - P.μ2 * ‖φ‖_H^2 x + P.𝓵 * ‖φ‖_H^2 x * ‖φ‖_H^2 x

/-- The potential is smooth. -/
lemma toFun_smooth (φ : HiggsField) :
    ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℝ) ⊤ (fun x => P.toFun φ x) := by
  simp only [toFun, normSq, neg_mul]
  exact (contMDiff_const.smul φ.normSq_smooth).neg.add
    ((contMDiff_const.smul φ.normSq_smooth).smul φ.normSq_smooth)

/-- The Higgs potential formed by negating the mass squared and the quartic coupling. -/
def neg : Potential where
  μ2 := - P.μ2
  𝓵 := - P.𝓵

@[simp]
lemma toFun_neg (φ : HiggsField) (x : SpaceTime) : P.neg.toFun φ x = - P.toFun φ x := by
  simp only [toFun, neg, neg_neg, normSq, neg_mul, neg_add_rev]
  ring

@[simp]
lemma μ2_neg : P.neg.μ2 = - P.μ2 := by rfl

@[simp]
lemma 𝓵_neg : P.neg.𝓵 = - P.𝓵 := by rfl

/-!

## Basic properties

-/

@[simp]
lemma toFun_zero (x : SpaceTime) : P.toFun 0 x = 0 := by
  simp [toFun]

lemma complete_square (h : P.𝓵 ≠ 0) (φ : HiggsField) (x : SpaceTime) :
    P.toFun φ x = P.𝓵 * (‖φ‖_H^2 x - P.μ2 / (2 * P.𝓵)) ^ 2 - P.μ2 ^ 2 / (4 * P.𝓵) := by
  simp only [toFun]
  field_simp
  ring

/-- The quadratic equation satisfied by the Higgs potential at a spacetime point `x`. -/
lemma as_quad (φ : HiggsField) (x : SpaceTime) :
    P.𝓵 * ‖φ‖_H^2 x * ‖φ‖_H^2 x + (- P.μ2) * ‖φ‖_H^2 x + (- P.toFun φ x) = 0 := by
  simp only [normSq, neg_mul, toFun, neg_add_rev, neg_neg]
  ring

/-- The Higgs potential is zero iff and only if the higgs field is zero, or the
  higgs field has norm-squared `P.μ2 / P.𝓵`, assuming `P.𝓁 = 0`. -/
lemma toFun_eq_zero_iff (h : P.𝓵 ≠ 0) (φ : HiggsField) (x : SpaceTime) :
    P.toFun φ x = 0 ↔ φ x = 0 ∨ ‖φ‖_H^2 x = P.μ2 / P.𝓵 := by
  refine Iff.intro (fun hV => ?_) (fun hD => ?_)
  · have h1 := P.as_quad φ x
    rw [hV] at h1
    have h2 : ‖φ‖_H^2 x * (P.𝓵 * ‖φ‖_H^2 x + - P.μ2) = 0 := by
      linear_combination h1
    simp only [normSq, mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      norm_eq_zero] at h2
    cases' h2 with h2 h2
    · simp_all
    · apply Or.inr
      field_simp at h2 ⊢
      ring_nf
      simp only [normSq]
      linear_combination h2
  · cases' hD with hD hD
    · simp [toFun, hD]
    · simp only [toFun, neg_mul]
      rw [hD]
      field_simp
      simp

/-!

## The discriminant

-/

/-- The discriminant of the quadratic equation formed by the Higgs potential. -/
def quadDiscrim (φ : HiggsField) (x : SpaceTime) : ℝ := discrim P.𝓵 (- P.μ2) (- P.toFun φ x)

/-- The discriminant of the quadratic formed by the potential is non-negative. -/
lemma quadDiscrim_nonneg (h : P.𝓵 ≠ 0) (φ : HiggsField) (x : SpaceTime) :
    0 ≤ P.quadDiscrim φ x := by
  have h1 := P.as_quad φ x
  rw [mul_assoc, quadratic_eq_zero_iff_discrim_eq_sq] at h1
  · simp only [quadDiscrim, h1]
    exact sq_nonneg (2 * P.𝓵 * ‖φ‖_H^2 x + - P.μ2)
  · exact h

lemma quadDiscrim_eq_sqrt_mul_sqrt (h : P.𝓵 ≠ 0) (φ : HiggsField) (x : SpaceTime) :
    P.quadDiscrim φ x = Real.sqrt (P.quadDiscrim φ x) * Real.sqrt (P.quadDiscrim φ x) :=
  (Real.mul_self_sqrt (P.quadDiscrim_nonneg h φ x)).symm

lemma quadDiscrim_eq_zero_iff (h : P.𝓵 ≠ 0) (φ : HiggsField) (x : SpaceTime) :
    P.quadDiscrim φ x = 0 ↔ P.toFun φ x = - P.μ2 ^ 2 / (4 * P.𝓵) := by
  rw [quadDiscrim, discrim]
  refine Iff.intro (fun hD => ?_) (fun hV => ?_)
  · field_simp
    linear_combination hD
  · simp only [even_two, Even.neg_pow, hV, mul_neg, sub_neg_eq_add]
    field_simp
    simp

lemma quadDiscrim_eq_zero_iff_normSq (h : P.𝓵 ≠ 0) (φ : HiggsField) (x : SpaceTime) :
    P.quadDiscrim φ x = 0 ↔ ‖φ‖_H^2 x = P.μ2 / (2 * P.𝓵) := by
  rw [P.quadDiscrim_eq_zero_iff h]
  refine Iff.intro (fun hV => ?_) (fun hF => ?_)
  · have h1 := P.as_quad φ x
    rw [mul_assoc, quadratic_eq_zero_iff_of_discrim_eq_zero h
      ((P.quadDiscrim_eq_zero_iff h φ x).mpr hV)] at h1
    simp_rw [h1, neg_neg]
  · rw [toFun, hF]
    field_simp
    ring

/-- For an element `P` of `Potential`, if `l < 0` then the following upper bound for the potential
  exists

  `P.toFun φ x ≤ - μ2 ^ 2 / (4 * 𝓵)`. -/
lemma neg_𝓵_quadDiscrim_zero_bound (h : P.𝓵 < 0) (φ : HiggsField) (x : SpaceTime) :
    P.toFun φ x ≤ - P.μ2 ^ 2 / (4 * P.𝓵) := by
  have h1 := P.quadDiscrim_nonneg (ne_of_lt h) φ x
  simp only [quadDiscrim, discrim, even_two, Even.neg_pow] at h1
  ring_nf at h1
  rw [← neg_le_iff_add_nonneg',
    show P.𝓵 * P.toFun φ x * 4 = (- 4 * P.𝓵) * (- P.toFun φ x) by ring] at h1
  have h2 := le_neg_of_le_neg <| (div_le_iff₀' (by linarith : 0 < - 4 * P.𝓵)).mpr h1
  ring_nf at h2 ⊢
  exact h2

/-- For an element `P` of `Potential`, if `0 < l` then the following lower bound for the potential
  exists

  `- μ2 ^ 2 / (4 * 𝓵) ≤ P.toFun φ x`. -/
lemma pos_𝓵_quadDiscrim_zero_bound (h : 0 < P.𝓵) (φ : HiggsField) (x : SpaceTime) :
    - P.μ2 ^ 2 / (4 * P.𝓵) ≤ P.toFun φ x := by
  have h1 := P.neg.neg_𝓵_quadDiscrim_zero_bound (by simpa [neg] using h) φ x
  simp only [toFun_neg, μ2_neg, even_two, Even.neg_pow, 𝓵_neg, mul_neg, neg_div_neg_eq] at h1
  rw [neg_le, neg_div'] at h1
  exact h1

/-- If `P.𝓵` is negative, then if `P.μ2` is greater than zero, for all space-time points,
  the potential is negative `P.toFun φ x ≤ 0`. -/
lemma neg_𝓵_toFun_neg (h : P.𝓵 < 0) (φ : HiggsField) (x : SpaceTime) :
    (0 < P.μ2 ∧ P.toFun φ x ≤ 0) ∨ P.μ2 ≤ 0 := by
  by_cases hμ2 : P.μ2 ≤ 0
  · simp [hμ2]
  simp only [toFun, normSq, neg_mul, neg_add_le_iff_le_add, add_zero, hμ2, or_false]
  apply And.intro (lt_of_not_ge hμ2)
  have h1 : 0 ≤ P.μ2 * ‖φ x‖ ^ 2 := by
    refine Left.mul_nonneg ?ha ?hb
    · exact le_of_not_ge hμ2
    · exact sq_nonneg ‖φ x‖
  refine le_trans ?_ h1
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (le_of_lt h)
    (sq_nonneg ‖φ x‖)) (sq_nonneg ‖φ x‖)

/-- If `P.𝓵` is bigger then zero, then if `P.μ2` is less than zero, for all space-time points,
  the potential is positive `0 ≤ P.toFun φ x`. -/
lemma pos_𝓵_toFun_pos (h : 0 < P.𝓵) (φ : HiggsField) (x : SpaceTime) :
    (P.μ2 < 0 ∧ 0 ≤ P.toFun φ x) ∨ 0 ≤ P.μ2 := by
  simpa using P.neg.neg_𝓵_toFun_neg (by simpa using h) φ x

/-- For an element `P` of `Potential` with `l < 0` and a real `c : ℝ`, there exists
  a Higgs field `φ` and a spacetime point `x` such that `P.toFun φ x = c` iff one of the
  following two conditions hold:
- `0 < μ2` and `c ≤ 0`. That is, if `l` is negative and `μ2` positive, then the potential
  takes every non-positive value.
- or `μ2 ≤ 0` and `c ≤ - μ2 ^ 2 / (4 * 𝓵)`. That is, if `l` is negative and `μ2` non-positive,
  then the potential takes every value less then or equal to its bound.
-/
lemma neg_𝓵_sol_exists_iff (h𝓵 : P.𝓵 < 0) (c : ℝ) : (∃ φ x, P.toFun φ x = c) ↔ (0 < P.μ2 ∧ c ≤ 0) ∨
    (P.μ2 ≤ 0 ∧ c ≤ - P.μ2 ^ 2 / (4 * P.𝓵)) := by
  refine Iff.intro (fun ⟨φ, x, hV⟩ => ?_) (fun h => ?_)
  · rcases P.neg_𝓵_toFun_neg h𝓵 φ x with hr | hr
    · rw [← hV]
      exact Or.inl hr
    · rw [← hV]
      exact Or.inr (And.intro hr (P.neg_𝓵_quadDiscrim_zero_bound h𝓵 φ x))
  · simp only [toFun, neg_mul]
    simp only [← sub_eq_zero, sub_zero]
    ring_nf
    let a := (P.μ2 - Real.sqrt (discrim P.𝓵 (- P.μ2) (- c))) / (2 * P.𝓵)
    have ha : 0 ≤ a := by
      simp only [discrim, even_two, Even.neg_pow, mul_neg, sub_neg_eq_add, a]
      rw [div_nonneg_iff]
      refine Or.inr (And.intro ?_ ?_)
      · rw [sub_nonpos]
        by_cases hμ : P.μ2 < 0
        · have h1 : 0 ≤ √(P.μ2 ^ 2 + 4 * P.𝓵 * c) := Real.sqrt_nonneg (P.μ2 ^ 2 + 4 * P.𝓵 * c)
          linarith
        · refine Real.le_sqrt_of_sq_le ?_
          rw [le_add_iff_nonneg_right]
          refine mul_nonneg_of_nonpos_of_nonpos ?_ ?_
          · refine mul_nonpos_of_nonneg_of_nonpos ?_ ?_
            · linarith
            · linarith
          · rcases h with h | h
            · linarith
            · have h1 : P.μ2 = 0 := by linarith
              rw [h1] at h
              simpa using h.2
      · linarith
    use (const (HiggsVec.ofReal a))
    use 0
    simp [HiggsVec.ofReal_normSq ha]
    trans P.𝓵 * a * a + (- P.μ2) * a + (- c)
    · ring
    have hd : 0 ≤ (discrim P.𝓵 (- P.μ2) (-c)) := by
      simp only [discrim, even_two, Even.neg_pow, mul_neg, sub_neg_eq_add]
      rcases h with h | h
      · refine Left.add_nonneg (sq_nonneg P.μ2) ?_
        refine mul_nonneg_of_nonpos_of_nonpos ?_ h.2
        linarith
      · rw [← @neg_le_iff_add_nonneg']
        rw [← le_div_iff_of_neg']
        · exact h.2
        · linarith
    have hdd : discrim P.𝓵 (- P.μ2) (-c) = Real.sqrt (discrim P.𝓵 (- P.μ2) (-c))
        * Real.sqrt (discrim P.𝓵 (- P.μ2) (-c)) := by
      exact (Real.mul_self_sqrt hd).symm
    rw [mul_assoc]
    refine (quadratic_eq_zero_iff (ne_of_gt h𝓵).symm hdd _).mpr ?_
    simp only [neg_neg, or_true, a]

/-- For an element `P` of `Potential` with `0 < l` and a real `c : ℝ`, there exists
  a Higgs field `φ` and a spacetime point `x` such that `P.toFun φ x = c` iff one of the
  following two conditions hold:
- `μ2 < 0` and `0 ≤ c`. That is, if `l` is positive and `μ2` negative, then the potential
  takes every non-negative value.
- or `0 ≤ μ2` and `- μ2 ^ 2 / (4 * 𝓵) ≤ c`. That is, if `l` is positive and `μ2` non-negative,
  then the potential takes every value greater then or equal to its bound.
-/
lemma pos_𝓵_sol_exists_iff (h𝓵 : 0 < P.𝓵) (c : ℝ) : (∃ φ x, P.toFun φ x = c) ↔ (P.μ2 < 0 ∧ 0 ≤ c) ∨
    (0 ≤ P.μ2 ∧ - P.μ2 ^ 2 / (4 * P.𝓵) ≤ c) := by
  have h1 := P.neg.neg_𝓵_sol_exists_iff (by simpa using h𝓵) (- c)
  simp only [toFun_neg, neg_inj, μ2_neg, Left.neg_pos_iff, Left.neg_nonpos_iff, even_two,
    Even.neg_pow, 𝓵_neg, mul_neg, neg_div_neg_eq] at h1
  rw [neg_le, neg_div'] at h1
  exact h1

/-!

## Boundedness of the potential

-/

/-- Given a element `P` of `Potential`, the proposition `IsBounded P` is true if and only if
  there exists a real `c` such that for all Higgs fields `φ` and spacetime points `x`,
  the Higgs potential corresponding to `φ` at `x` is greater then or equal to`c`. I.e.

  `∀ Φ x, c ≤ P.toFun Φ x`. -/
def IsBounded : Prop :=
  ∃ c, ∀ Φ x, c ≤ P.toFun Φ x

/-- Given a element `P` of `Potential` which is bounded,
  the quartic coefficient `𝓵` of `P` is non-negative. -/
lemma isBounded_𝓵_nonneg (h : P.IsBounded) : 0 ≤ P.𝓵 := by
  by_contra hl
  rw [not_le] at hl
  obtain ⟨c, hc⟩ := h
  by_cases hμ : P.μ2 ≤ 0
  · by_cases hcz : c ≤ - P.μ2 ^ 2 / (4 * P.𝓵)
    · have hcm1 : ∃ φ x, P.toFun φ x = c - 1 := by
        rw [P.neg_𝓵_sol_exists_iff hl (c - 1)]
        apply Or.inr
        simp_all only [tsub_le_iff_right, true_and]
        linarith
      obtain ⟨φ, x, hφ⟩ := hcm1
      have hc2 := hc φ x
      rw [hφ] at hc2
      linarith
    · rw [not_le] at hcz
      have hcm1 : ∃ φ x, P.toFun φ x = - P.μ2 ^ 2 / (4 * P.𝓵) - 1 := by
        rw [P.neg_𝓵_sol_exists_iff hl _]
        apply Or.inr
        simp_all
      obtain ⟨φ, x, hφ⟩ := hcm1
      have hc2 := hc φ x
      rw [hφ] at hc2
      linarith
  · rw [not_le] at hμ
    by_cases hcz : c ≤ 0
    · have hcm1 : ∃ φ x, P.toFun φ x = c - 1 := by
        rw [P.neg_𝓵_sol_exists_iff hl (c - 1)]
        apply Or.inl
        simp_all only [tsub_le_iff_right, zero_add, true_and]
        linarith
      obtain ⟨φ, x, hφ⟩ := hcm1
      have hc2 := hc φ x
      rw [hφ] at hc2
      linarith
    · have hcm1 : ∃ φ x, P.toFun φ x = 0 := by
        rw [P.neg_𝓵_sol_exists_iff hl 0]
        apply Or.inl
        simp_all
      obtain ⟨φ, x, hφ⟩ := hcm1
      have hc2 := hc φ x
      rw [hφ] at hc2
      linarith

/-- Given a element `P` of `Potential` with `0 < 𝓵`, then the potential is bounded. -/
lemma isBounded_of_𝓵_pos (h : 0 < P.𝓵) : P.IsBounded := by
  simp only [IsBounded]
  have h2 := P.pos_𝓵_quadDiscrim_zero_bound h
  by_contra hn
  simp only [not_exists, not_forall, not_le] at hn
  obtain ⟨φ, x, hx⟩ := hn (-P.μ2 ^ 2 / (4 * P.𝓵))
  have h2' := h2 φ x
  linarith

/-- When there is no quartic coupling, the potential is bounded iff the mass squared is
non-positive, i.e., for `P : Potential` then `P.IsBounded` iff `P.μ2 ≤ 0`. That is to say
`- P.μ2 * ‖φ‖_H^2 x` is bounded below iff `P.μ2 ≤ 0`. -/
informal_lemma isBounded_iff_of_𝓵_zero where
  deps := [`StandardModel.HiggsField.Potential.IsBounded, `StandardModel.HiggsField.Potential]
  tag := "6V2K5"

/-!

## Minimum and maximum

-/

lemma eq_zero_iff_of_μSq_nonpos_𝓵_pos (h𝓵 : 0 < P.𝓵) (hμ2 : P.μ2 ≤ 0) (φ : HiggsField)
    (x : SpaceTime) : P.toFun φ x = 0 ↔ φ x = 0 := by
  rw [P.toFun_eq_zero_iff (ne_of_lt h𝓵).symm]
  simp only [or_iff_left_iff_imp]
  intro h
  have h1 := div_nonpos_of_nonpos_of_nonneg hμ2 (le_of_lt h𝓵)
  rw [← h] at h1
  have hx := normSq_nonneg φ x
  have hx' : ‖φ‖_H^2 x = 0 := by linarith
  simpa using hx'

lemma isMinOn_iff_of_μSq_nonpos_𝓵_pos (h𝓵 : 0 < P.𝓵) (hμ2 : P.μ2 ≤ 0) (φ : HiggsField)
    (x : SpaceTime) : IsMinOn (fun (φ, x) => P.toFun φ x) Set.univ (φ, x)
    ↔ P.toFun φ x = 0 := by
  have h1 := P.pos_𝓵_sol_exists_iff h𝓵
  rw [isMinOn_univ_iff]
  simp only [Prod.forall]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · have h1' : P.toFun φ x ≤ 0 := by
      simpa using h 0 0
    have h1'' : 0 ≤ P.toFun φ x := by
      have hx := (h1 (P.toFun φ x)).mp ⟨φ, x, rfl⟩
      rcases hx with hx | hx
      · exact hx.2
      · have hμ2' : P.μ2 = 0 := by
          linarith
        simpa [hμ2'] using hx.2
    linarith
  · rw [h]
    intro φ' x'
    have h1' := (h1 (P.toFun φ' x')).mp ⟨φ', x', rfl⟩
    rcases h1' with h1' | h1'
    · exact h1'.2
    · have hμ2' : P.μ2 = 0 := by
        linarith
      simpa [hμ2'] using h1'.2

lemma isMinOn_iff_field_of_μSq_nonpos_𝓵_pos (h𝓵 : 0 < P.𝓵) (hμ2 : P.μ2 ≤ 0) (φ : HiggsField)
    (x : SpaceTime) : IsMinOn (fun (φ, x) => P.toFun φ x) Set.univ (φ, x)
    ↔ φ x = 0 := by
  rw [P.isMinOn_iff_of_μSq_nonpos_𝓵_pos h𝓵 hμ2 φ x]
  exact P.eq_zero_iff_of_μSq_nonpos_𝓵_pos h𝓵 hμ2 φ x

lemma isMinOn_iff_of_μSq_nonneg_𝓵_pos (h𝓵 : 0 < P.𝓵) (hμ2 : 0 ≤ P.μ2) (φ : HiggsField)
    (x : SpaceTime) : IsMinOn (fun (φ, x) => P.toFun φ x) Set.univ (φ, x) ↔
    P.toFun φ x = - P.μ2 ^ 2 / (4 * P.𝓵) := by
  have h1 := P.pos_𝓵_sol_exists_iff h𝓵
  simp only [not_lt.mpr hμ2, false_and, hμ2, true_and, false_or] at h1
  rw [isMinOn_univ_iff]
  simp only [Prod.forall]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · obtain ⟨φ', x', hφ'⟩ := (h1 (- P.μ2 ^ 2 / (4 * P.𝓵))).mpr (by rfl)
    have h' := h φ' x'
    rw [hφ'] at h'
    have hφ := (h1 (P.toFun φ x)).mp ⟨φ, x, rfl⟩
    linarith
  · intro φ' x'
    rw [h]
    exact (h1 (P.toFun φ' x')).mp ⟨φ', x', rfl⟩

lemma isMinOn_iff_field_of_μSq_nonneg_𝓵_pos (h𝓵 : 0 < P.𝓵) (hμ2 : 0 ≤ P.μ2) (φ : HiggsField)
    (x : SpaceTime) : IsMinOn (fun (φ, x) => P.toFun φ x) Set.univ (φ, x) ↔
    ‖φ‖_H^2 x = P.μ2 /(2 * P.𝓵) := by
  rw [P.isMinOn_iff_of_μSq_nonneg_𝓵_pos h𝓵 hμ2 φ x, ← P.quadDiscrim_eq_zero_iff_normSq
    (Ne.symm (ne_of_lt h𝓵)), P.quadDiscrim_eq_zero_iff (Ne.symm (ne_of_lt h𝓵))]

/-- Given an element `P` of `Potential` with `0 < l`, then the Higgs field `φ` and
  spacetime point `x` minimize the potential if and only if one of the following conditions
  holds
- `0 ≤ μ2` and `‖φ‖_H^2 x = μ2 / (2 * 𝓵)`.
- or `μ2 < 0` and `φ x = 0`.
-/
theorem isMinOn_iff_field_of_𝓵_pos (h𝓵 : 0 < P.𝓵) (φ : HiggsField) (x : SpaceTime) :
    IsMinOn (fun (φ, x) => P.toFun φ x) Set.univ (φ, x) ↔
    (0 ≤ P.μ2 ∧ ‖φ‖_H^2 x = P.μ2 /(2 * P.𝓵)) ∨ (P.μ2 < 0 ∧ φ x = 0) := by
  by_cases hμ2 : 0 ≤ P.μ2
  · simpa [not_lt.mpr hμ2, hμ2] using P.isMinOn_iff_field_of_μSq_nonneg_𝓵_pos h𝓵 hμ2 φ x
  · simpa [hμ2, lt_of_not_ge hμ2] using P.isMinOn_iff_field_of_μSq_nonpos_𝓵_pos h𝓵 (by linarith) φ x

lemma isMaxOn_iff_isMinOn_neg (φ : HiggsField) (x : SpaceTime) :
    IsMaxOn (fun (φ, x) => P.toFun φ x) Set.univ (φ, x) ↔
    IsMinOn (fun (φ, x) => P.neg.toFun φ x) Set.univ (φ, x) := by
  simp only [toFun_neg]
  rw [isMaxOn_univ_iff, isMinOn_univ_iff]
  simp_all only [Prod.forall, neg_le_neg_iff]

/-- Given an element `P` of `Potential` with `l < 0`, then the Higgs field `φ` and
  spacetime point `x` maximizes the potential if and only if one of the following conditions
  holds
- `μ2 ≤ 0` and `‖φ‖_H^2 x = μ2 / (2 * 𝓵)`.
- or `0 < μ2` and `φ x = 0`.
-/
lemma isMaxOn_iff_field_of_𝓵_neg (h𝓵 : P.𝓵 < 0) (φ : HiggsField) (x : SpaceTime) :
    IsMaxOn (fun (φ, x) => P.toFun φ x) Set.univ (φ, x) ↔
    (P.μ2 ≤ 0 ∧ ‖φ‖_H^2 x = P.μ2 /(2 * P.𝓵)) ∨ (0 < P.μ2 ∧ φ x = 0) := by
  rw [P.isMaxOn_iff_isMinOn_neg,
    P.neg.isMinOn_iff_field_of_𝓵_pos (by simpa using h𝓵)]
  simp

end Potential

end HiggsField

end StandardModel
end
