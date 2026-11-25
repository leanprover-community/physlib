/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolai Kashcheev, Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.HiggsBoson.Basic
/-!
# The potential of the Higgs field

The classical Higgs potential, its bounds, and its extrema.

## i. Overview

The potential depends only on the squared norm of the field at a spacetime point. It is a
polynomial of degree at most two in that squared norm, and constant fields realize every
nonnegative squared norm. The bounds and extrema below compare values of the potential at
points; they do not involve the kinetic term or an energy integral.

## ii. Key results

- `Potential.toFun_smooth`: the potential evaluated on a Higgs field is smooth.
- `Potential.isBounded_iff`: the criterion for boundedness below.
- `Potential.isMinOn_iff_field_of_𝓵_zero`: the minimizing field values at zero quartic coupling.

## iii. Table of contents

- A. The Higgs potential
- B. Basic properties
- C. The discriminant
- D. Boundedness of the potential
- E. Minimum and maximum

## iv. References

* None.

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

## A. The Higgs potential

-/

/-- The parameters of the classical Higgs potential. With `s` the squared norm of the field
  value, the potential is `-μ2 * s + 𝓵 * s ^ 2`. -/
structure Potential where
  /-- The mass parameter of the potential; its negative is the coefficient of the squared norm. -/
  μ2 : ℝ
  /-- The quartic coupling, usually denoted `λ`. -/
  𝓵 : ℝ

namespace Potential

variable (P : Potential)

TODO "Define a CoeFun instance for the Higgs Potential (or similar), instead of relying on
  `P.toFun`."

/-- Evaluate the classical Higgs potential on the value of the field `φ` at the point `x`. -/
def toFun (φ : HiggsField) (x : SpaceTime) : ℝ :=
  - P.μ2 * ‖φ‖_H^2 x + P.𝓵 * ‖φ‖_H^2 x * ‖φ‖_H^2 x

/-- With zero quartic coupling and a nonnegative coefficient of the squared norm, each value
  of the Higgs potential is nonnegative. -/
private lemma toFun_nonneg_of_𝓵_zero (h𝓵 : P.𝓵 = 0) (hμ : P.μ2 ≤ 0) (φ : HiggsField)
    (x : SpaceTime) : 0 ≤ P.toFun φ x := by
  simpa only [toFun, h𝓵, zero_mul, add_zero] using
    mul_nonneg (neg_nonneg.mpr hμ) (normSq_nonneg φ x)

/-- The potential is smooth. -/
lemma toFun_smooth (φ : HiggsField) :
    ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℝ) ⊤ (fun x => P.toFun φ x) := by
  simp only [toFun, normSq, neg_mul]
  exact ((contMDiff_const (I' := 𝓘(ℝ, ℝ)) (M' := ℝ)).smul φ.normSq_smooth).neg.add
    (((contMDiff_const (I' := 𝓘(ℝ, ℝ)) (M' := ℝ)).smul φ.normSq_smooth).smul φ.normSq_smooth)

/-- The Higgs potential formed by negating both parameters. -/
def neg : Potential where
  μ2 := - P.μ2
  𝓵 := - P.𝓵

@[simp]
lemma toFun_neg (φ : HiggsField) (x : SpaceTime) : P.neg.toFun φ x = - P.toFun φ x := by
  simp only [toFun, neg]
  ring

@[simp]
lemma μ2_neg : P.neg.μ2 = - P.μ2 := by rfl

@[simp]
lemma 𝓵_neg : P.neg.𝓵 = - P.𝓵 := by rfl

/-!

## B. Basic properties

-/

@[simp]
lemma toFun_zero (x : SpaceTime) : P.toFun 0 x = 0 := by
  simp [toFun]

/-- The Higgs potential is gauge invariant: at a spacetime point `x`, it takes the same value on
  two Higgs fields whose values at `x` are related by an element of the gauge group. -/
lemma toFun_eq_of_repGaugeGroupI (g : GaugeGroupI) (φ ψ : HiggsField) (x : SpaceTime)
    (h : ψ x = HiggsVec.repGaugeGroupI g (φ x)) : P.toFun ψ x = P.toFun φ x := by
  simp [toFun, h, HiggsVec.repGaugeGroupI_norm]

lemma complete_square (h : P.𝓵 ≠ 0) (φ : HiggsField) (x : SpaceTime) :
    P.toFun φ x = P.𝓵 * (‖φ‖_H^2 x - P.μ2 / (2 * P.𝓵)) ^ 2 - P.μ2 ^ 2 / (4 * P.𝓵) := by
  simp only [toFun]
  field_simp
  ring

/-- The quadratic equation satisfied by the Higgs potential at a spacetime point `x`. -/
lemma as_quad (φ : HiggsField) (x : SpaceTime) :
    P.𝓵 * ‖φ‖_H^2 x * ‖φ‖_H^2 x + (- P.μ2) * ‖φ‖_H^2 x + (- P.toFun φ x) = 0 := by
  simp only [toFun]
  ring

/-- With nonzero quartic coupling, the potential vanishes exactly when the field value is zero
  or has squared norm `P.μ2 / P.𝓵`. -/
lemma toFun_eq_zero_iff (h : P.𝓵 ≠ 0) (φ : HiggsField) (x : SpaceTime) :
    P.toFun φ x = 0 ↔ φ x = 0 ∨ ‖φ‖_H^2 x = P.μ2 / P.𝓵 := by
  refine Iff.intro (fun hV => ?_) (fun hD => ?_)
  · have h1 := P.as_quad φ x
    rw [hV] at h1
    have h2 : ‖φ‖_H^2 x * (P.𝓵 * ‖φ‖_H^2 x + - P.μ2) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h2 | h2
    · exact Or.inl (by simpa [normSq] using h2)
    · exact Or.inr (by rw [eq_div_iff h]; linear_combination h2)
  · cases' hD with hD hD
    · simp [toFun, hD]
    · simp only [toFun, hD]
      field_simp
      ring

/-!

## C. The discriminant

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
  · rw [hV]
    field_simp
    ring

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
  rw [le_div_iff_of_neg (show (4:ℝ) * P.𝓵 < 0 by linarith)]
  nlinarith [h1]

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
  refine Or.inl ⟨lt_of_not_ge hμ2, ?_⟩
  simp only [toFun, normSq, neg_mul]
  nlinarith [mul_nonneg (sq_nonneg ‖φ x‖) (sq_nonneg ‖φ x‖), sq_nonneg ‖φ x‖,
    h, lt_of_not_ge hμ2]

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
  · rw [← hV]
    rcases P.neg_𝓵_toFun_neg h𝓵 φ x with hr | hr
    · exact Or.inl hr
    · exact Or.inr ⟨hr, P.neg_𝓵_quadDiscrim_zero_bound h𝓵 φ x⟩
  · simp only [toFun, neg_mul]
    simp only [← sub_eq_zero, sub_zero]
    let a := (P.μ2 - Real.sqrt (discrim P.𝓵 (- P.μ2) (- c))) / (2 * P.𝓵)
    have ha : 0 ≤ a := by
      simp only [discrim, even_two, Even.neg_pow, mul_neg, sub_neg_eq_add, a]
      rw [div_nonneg_iff]
      refine Or.inr ⟨?_, by linarith⟩
      rw [sub_nonpos]
      rcases h with h | h
      · exact Real.le_sqrt_of_sq_le (by nlinarith [h.2])
      · exact h.1.trans (Real.sqrt_nonneg _)
    use (const (HiggsVec.ofReal a))
    use 0
    simp [HiggsVec.ofReal_normSq ha]
    trans P.𝓵 * a * a + (- P.μ2) * a + (- c)
    · ring
    have hd : 0 ≤ (discrim P.𝓵 (- P.μ2) (-c)) := by
      simp only [discrim, even_two, Even.neg_pow, mul_neg, sub_neg_eq_add]
      rcases h with h | h
      · nlinarith [sq_nonneg P.μ2, h.2]
      · rw [← @neg_le_iff_add_nonneg', ← le_div_iff_of_neg']
        · exact h.2
        · linarith
    have hdd := (Real.mul_self_sqrt hd).symm
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

## D. Boundedness of the potential

-/

/-- The Higgs potential has a uniform lower bound over all field values at spacetime points. -/
def IsBounded : Prop :=
  ∃ c, ∀ Φ x, c ≤ P.toFun Φ x

/-- Given a element `P` of `Potential` which is bounded,
  the quartic coefficient `𝓵` of `P` is non-negative. -/
lemma isBounded_𝓵_nonneg (h : P.IsBounded) : 0 ≤ P.𝓵 := by
  by_contra hl
  rw [not_le] at hl
  obtain ⟨c, hc⟩ := h
  have c_le_of_attainable : ∀ v : ℝ, ((0 < P.μ2 ∧ v ≤ 0) ∨
      (P.μ2 ≤ 0 ∧ v ≤ - P.μ2 ^ 2 / (4 * P.𝓵))) → c ≤ v := by
    intro v hv
    obtain ⟨φ, x, rfl⟩ := (P.neg_𝓵_sol_exists_iff hl v).mpr hv
    exact hc φ x
  by_cases hμ : P.μ2 ≤ 0
  · by_cases hcz : c ≤ - P.μ2 ^ 2 / (4 * P.𝓵)
    · linarith [c_le_of_attainable (c - 1) (Or.inr ⟨hμ, by linarith⟩)]
    · rw [not_le] at hcz
      linarith [c_le_of_attainable (- P.μ2 ^ 2 / (4 * P.𝓵) - 1) (Or.inr ⟨hμ, by linarith⟩)]
  · rw [not_le] at hμ
    by_cases hcz : c ≤ 0
    · linarith [c_le_of_attainable (c - 1) (Or.inl ⟨hμ, by linarith⟩)]
    · rw [not_le] at hcz
      linarith [c_le_of_attainable 0 (Or.inl ⟨hμ, by linarith⟩)]

/-- Given a element `P` of `Potential` with `0 < 𝓵`, then the potential is bounded. -/
lemma isBounded_of_𝓵_pos (h : 0 < P.𝓵) : P.IsBounded := by
  simp only [IsBounded]
  have h2 := P.pos_𝓵_quadDiscrim_zero_bound h
  by_contra hn
  simp only [not_exists, not_forall, not_le] at hn
  obtain ⟨φ, x, hx⟩ := hn (-P.μ2 ^ 2 / (4 * P.𝓵))
  have h2' := h2 φ x
  linarith

/-- With zero quartic coupling, the Higgs potential is bounded below exactly when the
coefficient `-P.μ2` of the squared norm is nonnegative. -/
lemma isBounded_iff_of_𝓵_zero (h𝓵 : P.𝓵 = 0) : P.IsBounded ↔ P.μ2 ≤ 0 := by
  constructor
  · rintro ⟨b, hb⟩
    by_contra! hμ
    -- A constant field realizes a squared norm large enough to violate the proposed bound.
    let s := (|b| + 1) / P.μ2
    have hs : 0 ≤ s := div_nonneg (by positivity) hμ.le
    have h := hb (HiggsField.const (HiggsVec.ofReal s)) 0
    rw [toFun, const_normSq, HiggsVec.ofReal_normSq hs, h𝓵, zero_mul, zero_mul, add_zero] at h
    have hprod : s * P.μ2 = |b| + 1 := div_mul_cancel₀ _ hμ.ne'
    linarith [neg_abs_le b]
  · intro hμ
    exact ⟨0, P.toFun_nonneg_of_𝓵_zero h𝓵 hμ⟩

/-- The Higgs potential is bounded below exactly when the quartic coupling is positive or is
  zero with a nonnegative coefficient of the squared norm. -/
lemma isBounded_iff : P.IsBounded ↔ 0 < P.𝓵 ∨ P.𝓵 = 0 ∧ P.μ2 ≤ 0 := by
  constructor
  · intro h
    rcases eq_or_lt_of_le (P.isBounded_𝓵_nonneg h) with h𝓵 | h𝓵
    · exact Or.inr ⟨h𝓵.symm, (P.isBounded_iff_of_𝓵_zero h𝓵.symm).mp h⟩
    · exact Or.inl h𝓵
  · rintro (h𝓵 | ⟨h𝓵, hμ⟩)
    · exact P.isBounded_of_𝓵_pos h𝓵
    · exact (P.isBounded_iff_of_𝓵_zero h𝓵).mpr hμ

/-!

## E. Minimum and maximum

-/

lemma eq_zero_iff_of_μSq_nonpos_𝓵_pos (h𝓵 : 0 < P.𝓵) (hμ2 : P.μ2 ≤ 0) (φ : HiggsField)
    (x : SpaceTime) : P.toFun φ x = 0 ↔ φ x = 0 := by
  rw [P.toFun_eq_zero_iff (ne_of_lt h𝓵).symm]
  simp only [or_iff_left_iff_imp]
  intro h
  have hx' : ‖φ‖_H^2 x = 0 :=
    le_antisymm (h.trans_le (div_nonpos_of_nonpos_of_nonneg hμ2 h𝓵.le)) (normSq_nonneg φ x)
  simpa using hx'

lemma isMinOn_iff_of_μSq_nonpos_𝓵_pos (h𝓵 : 0 < P.𝓵) (hμ2 : P.μ2 ≤ 0) (φ : HiggsField)
    (x : SpaceTime) : IsMinOn (fun (φ, x) => P.toFun φ x) Set.univ (φ, x)
    ↔ P.toFun φ x = 0 := by
  have h1 := P.pos_𝓵_sol_exists_iff h𝓵
  have attainable_nonneg : ∀ v : ℝ, ((P.μ2 < 0 ∧ 0 ≤ v) ∨
      (0 ≤ P.μ2 ∧ - P.μ2 ^ 2 / (4 * P.𝓵) ≤ v)) → 0 ≤ v := by
    rintro v (⟨_, hv⟩ | ⟨h0, hv⟩)
    · exact hv
    · simpa [le_antisymm hμ2 h0] using hv
  rw [isMinOn_univ_iff]
  simp only [Prod.forall]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · have h1' : P.toFun φ x ≤ 0 := by simpa using h 0 0
    have h1'' := attainable_nonneg _ ((h1 (P.toFun φ x)).mp ⟨φ, x, rfl⟩)
    linarith
  · rw [h]
    exact fun φ' x' => attainable_nonneg _ ((h1 (P.toFun φ' x')).mp ⟨φ', x', rfl⟩)

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

/-- With zero quartic coupling, every field value minimizes the potential if the coefficient
  of the squared norm is zero. If that coefficient is positive, only the zero field value
  minimizes it. If the coefficient is negative, the potential has no minimum. -/
lemma isMinOn_iff_field_of_𝓵_zero (h𝓵 : P.𝓵 = 0) (φ : HiggsField) (x : SpaceTime) :
    IsMinOn (fun (ψ, y) => P.toFun ψ y) Set.univ (φ, x) ↔
      P.μ2 = 0 ∨ (P.μ2 < 0 ∧ φ x = 0) := by
  rw [isMinOn_univ_iff]
  constructor
  · intro hmin
    have hb : P.IsBounded := ⟨P.toFun φ x, fun ψ y => hmin (ψ, y)⟩
    rcases eq_or_lt_of_le ((P.isBounded_iff_of_𝓵_zero h𝓵).mp hb) with hμ | hμ
    · exact Or.inl hμ
    · refine Or.inr ⟨hμ, ?_⟩
      have hle : -P.μ2 * ‖φ‖_H^2 x ≤ 0 := by
        have h := hmin ((0 : HiggsField), x)
        change P.toFun φ x ≤ P.toFun 0 x at h
        rw [toFun_zero] at h
        simpa only [toFun, h𝓵, zero_mul, add_zero] using h
      have hs := le_antisymm (nonpos_of_mul_nonpos_right hle (neg_pos.mpr hμ)) (normSq_nonneg φ x)
      simpa using hs
  · rintro (hμ | ⟨hμ, hφ⟩) ⟨ψ, y⟩
    · simp [toFun, h𝓵, hμ]
    · change P.toFun φ x ≤ P.toFun ψ y
      have hzero : P.toFun φ x = 0 := by simp [toFun, normSq, hφ]
      rw [hzero]
      exact P.toFun_nonneg_of_𝓵_zero h𝓵 hμ.le ψ y

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
