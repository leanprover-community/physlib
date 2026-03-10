/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.SpaceAndTime.Space.Integrals.RadialAngularMeasure
public import PhysLean.SpaceAndTime.Time.Derivatives
public import Mathlib.Tactic.Cases
/-!

# Functions on `Space d` which can be made into distributions

## i. Overview

In this module, for functions `f : Space d → F`, we define the property `IsDistBounded f`.
Functions satisfying this property can be used to create distributions `Space d →d[ℝ] F`
by integrating them against Schwartz maps.

The condition `IsDistBounded f` essentially says that `f` is bounded by a finite sum of terms
of the form `c * ‖x + g‖ ^ p` for constants `c`, `g` and `- (d - 1) ≤ p ` where `d` is the dimension
of the space.

## ii. Key results

- `IsDistBounded` : The boundedness condition on functions `Space d → F` for them to
  form distributions.
- `IsDistBounded.integrable_space` : If `f` satisfies `IsDistBounded f`, then
  `fun x => η x • f x` is integrable for any Schwartz map `η : 𝓢(Space d, ℝ)`.
- `IsDistBounded.integrable_time_space` : If `f` satisfies `IsDistBounded f`, then
  `fun x => η x • f x.2` is integrable for any Schwartz map
  `η : 𝓢(Time × Space d, ℝ)`.
- `IsDistBounded.mono` : If `f₁` satisfies `IsDistBounded f₁` and
  `‖f₂ x‖ ≤ ‖f₁ x‖` for all `x`, then `f₂` satisfies `IsDistBounded f₂`.

## iii. Table of contents

- A. The predicate `IsDistBounded f`
- B. Integrability properties of functions satisfying `IsDistBounded f`
  - B.1. `AEStronglyMeasurable` conditions
  - B.2. Integrability with respect to Schwartz maps on space
  - B.3. Integrability with respect to Schwartz maps on time and space
  - B.4. Integrability with respect to inverse powers
- C. Integral on Schwartz maps is bounded by seminorms
- D. Construction rules for `IsDistBounded f`
  - D.1. Addition
  - D.2. Finite sums
  - D.3. Scalar multiplication
  - D.4. Components of functions
  - D.5. Compositions with additions and subtractions
  - D.6. Congruence with respect to the norm
  - D.7. Monotonicity with respect to the norm
  - D.8. Inner products
  - D.9. Scalar multiplication with constant
- E. Specific functions that are `IsDistBounded`
  - E.1. Constant functions
  - E.2. Powers of norms
- F. Multiplication by norms and components

## iv. References

-/

@[expose] public section
open SchwartzMap NNReal
noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F] [NormedSpace ℝ F']

namespace Space

variable [NormedSpace ℝ E]

open MeasureTheory

/-!

## A. The predicate `IsDistBounded f`

-/

/-- The boundedness condition on a function ` EuclideanSpace ℝ (Fin dm1.succ) → F`
  for it to form a distribution. -/
@[fun_prop]
def IsDistBounded {d : ℕ} (f : Space d → F) : Prop :=
  AEStronglyMeasurable (fun x => f x) volume ∧
  ∃ n, ∃ c : Fin n → ℝ, ∃ g : Fin n → Space d,
    ∃ p : Fin n → ℤ,
    (∀ i, 0 ≤ c i) ∧
    (∀ i, - (d - 1 : ℕ) ≤ p i) ∧
    ∀ x, ‖f x‖ ≤ ∑ i, c i * ‖x + g i‖ ^ p i

namespace IsDistBounded

/-!

## B. Integrability properties of functions satisfying `IsDistBounded f`

-/

/-!

### B.1. `AEStronglyMeasurable` conditions

-/
omit [NormedSpace ℝ F] in
@[fun_prop]
lemma aestronglyMeasurable {d : ℕ} {f : Space d → F} (hf : IsDistBounded f) :
    AEStronglyMeasurable (fun x => f x) volume := hf.1

@[fun_prop]
lemma aeStronglyMeasurable_schwartzMap_smul {d : ℕ} {f : Space d → F}
    (hf : IsDistBounded f) (η : 𝓢(Space d, ℝ)) :
    AEStronglyMeasurable (fun x => η x • f x) := by
  fun_prop

@[fun_prop]
lemma aeStronglyMeasurable_fderiv_schwartzMap_smul {d : ℕ} {f : Space d → F}
    (hf : IsDistBounded f) (η : 𝓢(Space d, ℝ)) (y : Space d) :
    AEStronglyMeasurable (fun x => fderiv ℝ η x y • f x) := by
  fun_prop

@[fun_prop]
lemma aeStronglyMeasurable_inv_pow {d r : ℕ} {f : Space d → F}
    (hf : IsDistBounded f) :
    AEStronglyMeasurable (fun x => ‖((1 + ‖x‖) ^ r)⁻¹‖ • f x) := by
  apply AEStronglyMeasurable.smul
  · apply AEMeasurable.aestronglyMeasurable
    fun_prop
  · fun_prop

@[fun_prop]
lemma aeStronglyMeasurable_time_schwartzMap_smul {d : ℕ} {f : Space d → F}
    (hf : IsDistBounded f) (η : 𝓢(Time × Space d, ℝ)) :
    AEStronglyMeasurable (fun x => η x • f x.2) := by
  apply AEStronglyMeasurable.smul
  · fun_prop
  · apply MeasureTheory.AEStronglyMeasurable.comp_snd
    fun_prop

/-!

### B.2. Integrability with respect to Schwartz maps on space

-/

@[fun_prop]
lemma integrable_space {d : ℕ} {f : Space d → F} (hf : IsDistBounded f)
    (η : 𝓢(Space d, ℝ)) :
    Integrable (fun x : Space d => η x • f x) volume := by
  /- Reducing the problem to `Integrable (fun x : Space d => η x * ‖x + c‖ ^ p)` -/
  suffices h2 : ∀ (p : ℤ) (hp : - (d - 1 : ℕ) ≤ p) (c : Space d) (η : 𝓢(Space d, ℝ)),
      Integrable (fun x : Space d => η x * ‖x + c‖ ^ p) volume by
    obtain ⟨n, c, g, p, c_nonneg, p_bound, bound⟩ := hf.2
    apply Integrable.mono (g := fun x => ∑ i, (c i * (‖η x‖ * ‖x + g i‖ ^ p i))) _
    · fun_prop
    · filter_upwards with x
      rw [norm_smul]
      apply le_trans (mul_le_mul_of_nonneg_left (bound x) (norm_nonneg (η x)))
      apply le_of_eq
      simp only [Real.norm_eq_abs]
      rw [Finset.abs_sum_of_nonneg (fun i _ => mul_nonneg (c_nonneg i) (by positivity)),
        Finset.mul_sum]
      ring_nf
    · apply MeasureTheory.integrable_finset_sum
      intro i _
      apply Integrable.const_mul
      specialize h2 (p i) (p_bound i) (g i) η
      rw [← MeasureTheory.integrable_norm_iff] at h2
      simpa using h2
      apply AEMeasurable.aestronglyMeasurable
      fun_prop
  /- Reducing the problem to `Integrable (fun x : Space d => η x * ‖x‖ ^ p)` -/
  suffices h0 : ∀ (p : ℤ) (hp : - (d - 1 : ℕ) ≤ p) (η : 𝓢(Space d, ℝ)),
      Integrable (fun x : Space d => η x * ‖x‖ ^ p) volume by
    intro p hp c η
    suffices h1 : Integrable (fun x => η ((x + c) - c) * ‖x + c‖ ^ p) volume by
      simpa using h1
    apply MeasureTheory.Integrable.comp_add_right (g := c) (f := fun x => η (x - c) * ‖x‖ ^ p)
    apply h0 p hp (η.compCLM (𝕜 := ℝ) ?_ ?_)
    · apply Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1 + ‖c‖)
      · convert Function.HasTemperateGrowth.const (ContinuousLinearMap.id ℝ (Space d))
        simp [fderiv_sub_const]
      · fun_prop
      · refine fun x => (norm_sub_le _ _).trans (le_of_sub_nonneg ?_)
        ring_nf
        positivity
    · refine ⟨1, (1 + ‖c‖), fun x => (norm_le_norm_add_norm_sub' x c).trans (le_of_sub_nonneg ?_)⟩
      ring_nf
      positivity
  /- Proving `Integrable (fun x : Space d => η x * ‖x + c‖ ^ p)` -/
  intro p hp η
  have h1 : AEStronglyMeasurable (fun (x : Space d) => ‖x‖ ^ p) volume :=
      AEMeasurable.aestronglyMeasurable <| by fun_prop
  rw [← MeasureTheory.integrable_norm_iff (by fun_prop)]
  simp only [norm_mul, norm_zpow, norm_norm]
  match d with
  | 0 => simp only [Real.norm_eq_abs, Integrable.of_finite]
  | d + 1 =>
  by_cases hp' : p = 0
  · subst hp'
    simp only [zpow_zero, mul_one]
    apply Integrable.norm
    exact η.integrable
  suffices h1 : Integrable (fun x => ‖η x‖ * ‖x‖ ^ (p + d)) (radialAngularMeasure (d := (d + 1))) by
    rw [integrable_radialAngularMeasure_iff] at h1
    convert h1 using 1
    funext x
    have hx : 0 ≤ ‖x‖ := norm_nonneg x
    generalize ‖x‖ = r at *
    simp only [Real.norm_eq_abs, add_tsub_cancel_right, one_div, smul_eq_mul]
    trans |η x| * ((r ^ d)⁻¹ *r ^ (p + d)); swap
    · ring
    congr
    by_cases hr : r = 0
    · subst hr
      simp [zero_pow_eq, zero_zpow_eq, hp']
      omega
    field_simp
    rw [zpow_add₀ hr]
    rfl
  convert integrable_pow_mul_iteratedFDeriv radialAngularMeasure η (p + d).toNat 0 using 1
  funext x
  simp only [Real.norm_eq_abs, norm_iteratedFDeriv_zero]
  rw [mul_comm]
  congr 1
  rw [← zpow_natCast]
  congr
  refine Int.eq_natCast_toNat.mpr ?_
  omega

@[fun_prop]
lemma integrable_space_mul {d : ℕ} {f : Space d → ℝ} (hf : IsDistBounded f)
    (η : 𝓢(Space d, ℝ)) :
    Integrable (fun x : Space d => η x * f x) volume := by
  exact hf.integrable_space η

@[fun_prop]
lemma integrable_space_fderiv {d : ℕ} {f : Space d → F} (hf : IsDistBounded f)
    (η : 𝓢(Space d, ℝ)) (y : Space d) :
    Integrable (fun x : Space d => fderiv ℝ η x y • f x) volume := by
  exact hf.integrable_space (LineDeriv.lineDerivOpCLM ℝ _ y η)

@[fun_prop]
lemma integrable_space_fderiv_mul {d : ℕ} {f : Space d → ℝ} (hf : IsDistBounded f)
    (η : 𝓢(Space d, ℝ)) (y : Space d) :
    Integrable (fun x : Space d => fderiv ℝ η x y * f x) volume := by
  exact hf.integrable_space (LineDeriv.lineDerivOpCLM ℝ _ y η)

/-!

### B.3. Integrability with respect to Schwartz maps on time and space

-/

instance {D1 : Type} [NormedAddCommGroup D1] [MeasurableSpace D1]
    {D2 : Type} [NormedAddCommGroup D2] [MeasurableSpace D2]
    (μ1 : Measure D1) (μ2 : Measure D2)
    [Measure.HasTemperateGrowth μ1] [Measure.HasTemperateGrowth μ2]
    [OpensMeasurableSpace (D1 × D2)] :
    Measure.HasTemperateGrowth (μ1.prod μ2) where
  exists_integrable := by
    obtain ⟨rt1, h1⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := μ1)
    obtain ⟨rt2, h2⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := μ2)
    use rt1 + rt2
    apply Integrable.mono' (h1.mul_prod h2)
    · apply AEMeasurable.aestronglyMeasurable
      fun_prop
    filter_upwards with x
    simp only [Nat.cast_add, neg_add_rev, Real.norm_eq_abs, Real.rpow_neg_natCast, zpow_neg,
      zpow_natCast]
    calc _
      _ = |(1 + ‖x‖) ^ (-(rt1 : ℝ)) * (1 + ‖x‖) ^ (-(rt2 : ℝ))| := by
        rw [Real.rpow_add (by positivity), mul_comm]
      _ = (1 + ‖x‖) ^ (-(rt1 : ℝ)) * (1 + ‖x‖) ^ (-(rt2 : ℝ)) := by
        rw [abs_of_nonneg (by positivity)]
    simp only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
    apply mul_le_mul _ _ (by positivity) (by positivity)
    · refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ rt1)
      rcases x
      simp
    · refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ rt2)
      rcases x
      simp

@[fun_prop]
lemma integrable_time_space {d : ℕ} {f : Space d → F} (hf : IsDistBounded f)
    (η : 𝓢(Time × Space d, ℝ)) :
    Integrable (fun x : Time × Space d => η x • f x.2) volume := by
  /- Reducing the problem to `Integrable (fun x : Time × Space d => η x * ‖x.2 + c‖ ^ p)` -/
  suffices h2 : ∀ (p : ℤ) (hp : - (d - 1 : ℕ) ≤ p) (c : Space d) (η : 𝓢(Time × Space d, ℝ)),
      Integrable (fun x : Time × Space d => η x * ‖x.2 + c‖ ^ p) volume by
    obtain ⟨n, c, g, p, c_nonneg, p_bound, bound⟩ := hf.2
    apply Integrable.mono (g := fun x => ∑ i, (c i * (‖η x‖ * ‖x.2 + g i‖ ^ p i))) _
    · fun_prop
    · filter_upwards with x
      rw [norm_smul]
      apply le_trans (mul_le_mul_of_nonneg_left (bound x.2) (norm_nonneg (η x)))
      apply le_of_eq
      simp only [Real.norm_eq_abs]
      rw [Finset.abs_sum_of_nonneg (fun i _ => mul_nonneg (c_nonneg i) (by positivity)),
        Finset.mul_sum]
      ring_nf
    · apply MeasureTheory.integrable_finset_sum
      intro i _
      apply Integrable.const_mul
      specialize h2 (p i) (p_bound i) (g i) η
      rw [← MeasureTheory.integrable_norm_iff] at h2
      simpa using h2
      apply AEMeasurable.aestronglyMeasurable
      fun_prop
  /- Reducing the problem to `Integrable (fun x : Space d => η x * ‖x‖ ^ p)` -/
  suffices h0 : ∀ (p : ℤ) (hp : - (d - 1 : ℕ) ≤ p) (η : 𝓢(Time × Space d, ℝ)),
      Integrable (fun x : Time × Space d => η x * ‖x.2‖ ^ p) volume by
    intro p hp c η
    suffices h1 : Integrable (fun (x : Time × Space d) =>
        η ((x + (0, c)) - (0, c)) * ‖(x + (0, c)).2‖ ^ p) (volume.prod volume) by
      simpa using h1
    apply MeasureTheory.Integrable.comp_add_right (g := (0, c))
      (f := fun x => η (x - (0, c)) * ‖x.2‖ ^ p)
    apply h0 p hp (η.compCLM (𝕜 := ℝ) ?_ ?_)
    · apply Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1 + ‖c‖)
      · convert Function.HasTemperateGrowth.const (ContinuousLinearMap.id ℝ (Time × Space d))
        simp [fderiv_sub_const]
      · fun_prop
      · refine fun x => (norm_sub_le _ _).trans (le_of_sub_nonneg ?_)
        ring_nf
        simp only [Prod.norm_mk, norm_zero, norm_nonneg, sup_of_le_right,
          add_add_sub_cancel]
        positivity
    · refine ⟨1, (1 + ‖((0, c) : Time × Space d)‖),
        fun x => (norm_le_norm_add_norm_sub' x (0,c)).trans (le_of_sub_nonneg ?_)⟩
      ring_nf
      positivity
  /- Proving `Integrable (fun x : Space d => η x * ‖x.2‖ ^ p)` -/
  intro p hp η
  rw [← MeasureTheory.integrable_norm_iff (AEMeasurable.aestronglyMeasurable (by fun_prop))]
  simp only [norm_mul, norm_zpow, norm_norm]
  by_cases hp : p = 0
  · subst hp
    simp only [zpow_zero, mul_one]
    apply Integrable.norm
    change Integrable (⇑η) (volume.prod volume)
    exact η.integrable
  suffices h1 : Integrable (fun x => ‖η x‖ * ‖x.2‖ ^ (p + (d - 1 : ℕ)))
      (volume.prod (radialAngularMeasure (d := d))) by
    match d with
    | 0 => simpa using h1
    | d + 1 =>
    rw [radialAngularMeasure, MeasureTheory.prod_withDensity_right] at h1
    erw [integrable_withDensity_iff_integrable_smul₀ (by fun_prop)] at h1
    convert h1 using 1
    funext x
    simp only [Real.norm_eq_abs, one_div]
    rw [Real.toNNReal_of_nonneg, NNReal.smul_def]
    simp only [inv_nonneg, norm_nonneg, pow_nonneg, coe_mk, smul_eq_mul]
    ring_nf
    rw [mul_assoc]
    congr
    have hx : 0 ≤ ‖x.2‖ := norm_nonneg x.2
    generalize ‖x.2‖ = r at *
    by_cases hr : r = 0
    · subst hr
      simp only [inv_zero]
      rw [zero_pow_eq, zero_zpow_eq, zero_zpow_eq]
      split_ifs <;> simp
      any_goals omega
    · simp only [inv_pow]
      field_simp
      rw [zpow_add₀ hr]
      simp
    · simp
    · fun_prop
  apply Integrable.mono' (integrable_pow_mul_iteratedFDeriv _ η (p + (d - 1 : ℕ)).toNat 0)
  · apply AEMeasurable.aestronglyMeasurable
    fun_prop
  filter_upwards with x
  simp only [Real.norm_eq_abs, norm_iteratedFDeriv_zero]
  rw [mul_comm]
  rw [← zpow_natCast]
  rw [abs_of_nonneg (by positivity)]
  apply mul_le_mul _ (by rfl) (by positivity) (by positivity)
  rw [zpow_natCast]
  trans ‖x.2‖ ^ ((p + (d - 1 : ℕ)).toNat : ℤ)
  · apply le_of_eq
    congr
    refine Int.eq_natCast_toNat.mpr (by omega)
  rw [zpow_natCast]
  ring_nf
  apply pow_le_pow_left₀ (by positivity) _ (p + (d - 1 : ℕ)).toNat
  rcases x
  simp

/-!

### B.4. Integrability with respect to inverse powers

-/

lemma integrable_mul_inv_pow {d : ℕ}
    {f : Space d → F} (hf : IsDistBounded f) :
    ∃ r, Integrable (fun x => ‖((1 + ‖x‖) ^ r)⁻¹‖ • f x) volume := by
  suffices h0 : ∀ pmax, ∃ r, ∀ (p : ℤ) (hp : - (d - 1 : ℕ) ≤ p) (c : Space d)
      (p_le : p ≤ pmax),
      Integrable (fun x => ‖((1 + ‖x‖) ^ r)⁻¹‖ * ‖x + c‖ ^ p) volume by
    obtain ⟨n, c, g, p, c_nonneg, p_bound, bound⟩ := hf.2
    match n with
    | 0 => simp at bound; simp [bound]
    | n + 1 =>
    let pMax := Finset.max' (Finset.image p Finset.univ) (by simp)
    have pMax_max (i : Fin n.succ) : p i ≤ pMax := by
      simp [pMax]
      apply Finset.le_max'
      simp
    obtain ⟨r, hr⟩ := h0 pMax
    use r
    apply Integrable.mono (g := fun x => ∑ i, (c i * (‖((1 + ‖x‖) ^ r)⁻¹‖ * ‖x + g i‖ ^ p i))) _
    · fun_prop
    · filter_upwards with x
      rw [norm_smul]
      apply le_trans (mul_le_mul_of_nonneg_left (bound x) (by positivity))
      apply le_of_eq
      simp only [norm_inv, norm_pow, Real.norm_eq_abs, abs_abs]
      rw [Finset.abs_sum_of_nonneg (fun i _ => mul_nonneg (c_nonneg i) (by positivity)),
        Finset.mul_sum]
      ring_nf
    · apply MeasureTheory.integrable_finset_sum
      intro i _
      apply Integrable.const_mul
      apply (hr (p i) (p_bound i) (g i) (pMax_max i)).mono
      · fun_prop
      · filter_upwards with x
        simp
  match d with
  | 0 => simp
  | d + 1 =>
  suffices h0 : ∀ (q : ℕ) (c : Space (d + 1)), Integrable (fun x => ‖x + c‖ ^ (q - d : ℤ)
        * ‖((1 + ‖x‖) ^ (q + (radialAngularMeasure (d := d + 1)).integrablePower))⁻¹‖) volume by
    intro pMax
    use (pMax + d).toNat + (radialAngularMeasure (d := d + 1)).integrablePower
    intro p hp c p_le
    apply (h0 (p + d).toNat c).mono
    · fun_prop
    · filter_upwards with x
      simp only [norm_inv, norm_pow, Real.norm_eq_abs, norm_mul, abs_abs, norm_zpow,
        Int.ofNat_toNat]
      rw [mul_comm]
      refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · rw [max_eq_left (by omega)]
        simp
      · refine inv_pow_le_inv_pow_of_le ?_ ?_
        · rw [abs_of_nonneg (by positivity)]
          simp
        · simp_all
  let m := (radialAngularMeasure (d := (d + 1))).integrablePower
  suffices h0 : ∀ (q : ℕ) (c : Space (d + 1)),
      Integrable (fun x => ‖x‖ ^ (q - d : ℤ) * ‖((1 + ‖x - c‖) ^ (q + m))⁻¹‖) volume by
    intro q c
    convert (h0 q c).comp_add_right c using 1
    funext x
    simp [m]
  suffices h0 : ∀ (q : ℕ) (v : Space (d + 1)),
      Integrable (fun x => ‖x‖ ^ q * ‖((1 + ‖x - v‖) ^ (q + m))⁻¹‖) radialAngularMeasure by
    intro q v
    specialize h0 q v
    rw [integrable_radialAngularMeasure_iff] at h0
    apply Integrable.congr h0
    rw [Filter.eventuallyEq_iff_exists_mem]
    use {0}ᶜ
    constructor
    · rw [compl_mem_ae_iff, measure_singleton]
    intro x hx
    simp [← mul_assoc]
    left
    rw [zpow_sub₀ (by simpa using hx), zpow_natCast, zpow_natCast]
    field_simp
  intro q v
  have hr1 (x : Space (d + 1)) :
        ‖((1 + ‖x - v‖) ^ (q + m))⁻¹‖ = ((1 + ‖x - v‖) ^ (q + m))⁻¹ := by
      simp only [norm_inv, norm_pow, Real.norm_eq_abs, inv_inj]
      rw [abs_of_nonneg (by positivity)]
  apply integrable_of_le_of_pow_mul_le (C₁ := 1) (C₂ :=2 ^ (q + m - 1) * (‖v‖ ^ (q + m) + 1))
  · simp
    intro x
    refine inv_le_one_of_one_le₀ ?_
    rw [abs_of_nonneg (by positivity)]
    refine one_le_pow₀ ?_
    simp
  · intro x
    rw [hr1]
    refine mul_inv_le_of_le_mul₀ ?_ (by positivity) ?_
    · positivity
    change ‖x‖^ (q + m) ≤ _
    by_cases hzero : m = 0 ∧ q = 0
    · rcases hzero with ⟨hm, hq⟩
      generalize hm : m = m' at *
      subst hm hq
      rw [pow_zero, pow_zero]
      simp
    trans (‖v‖ + ‖x - v‖) ^ (q + m)
    · rw [pow_le_pow_iff_left₀]
      · apply norm_le_norm_add_norm_sub'
      · positivity
      · positivity
      simp only [ne_eq, Nat.add_eq_zero_iff, not_and]
      intro hq
      omega
    apply (add_pow_le _ _ _).trans
    trans 2 ^ (q + m - 1) * (‖v‖ ^ (q + m) + ‖x - v‖ ^ (q + m)) + (2 ^ (q + m - 1)
      + 2 ^ (q + m - 1) * ‖v‖ ^ (q + m) * ‖x - v‖ ^ (q + m))
    · simp
      positivity
    trans (2 ^ (q + m - 1) * (‖v‖ ^ (q + m) + 1)) * (1 + ‖x - v‖ ^ (q + m))
    · ring_nf
      apply le_of_eq
      rfl
    refine mul_le_mul_of_nonneg (by rfl) ?_ ?_ ?_
    · trans 1 ^ (q + m) + ‖x - v‖ ^ (q + m)
      · simp
      apply pow_add_pow_le
      · simp
      · positivity
      · simp
        omega
    · positivity
    · positivity
    · positivity
    · positivity
  · refine Measurable.aestronglyMeasurable ?_
    fun_prop

/-!

## C. Integral on Schwartz maps is bounded by seminorms

-/

lemma integral_mul_schwartzMap_bounded {d : ℕ} {f : Space d → F} (hf : IsDistBounded f) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),
    0 ≤ C ∧ ∀ (η : 𝓢(Space d, ℝ)),
    ‖∫ (x : Space d), η x • f x‖ ≤ C * (s.sup (schwartzSeminormFamily ℝ (Space d) ℝ)) η := by
  obtain ⟨r, hr⟩ := hf.integrable_mul_inv_pow
  use Finset.Iic (r, 0), 2 ^ r * ∫ x, ‖f x‖ * ‖((1 + ‖x‖) ^ r)⁻¹‖
  refine ⟨by positivity, fun η ↦ (norm_integral_le_integral_norm _).trans ?_⟩
  rw [← integral_const_mul, ← integral_mul_const]
  refine integral_mono_of_nonneg ?_ ?_ ?_
  · filter_upwards with x
    positivity
  · apply Integrable.mul_const
    apply Integrable.const_mul
    apply Integrable.congr' hr
    · apply AEStronglyMeasurable.mul
      · fun_prop
      · apply AEMeasurable.aestronglyMeasurable
        fun_prop
    filter_upwards with x
    simp [norm_smul, mul_comm]
  · filter_upwards with x
    simp [norm_smul]
    trans (2 ^ r *
      ((Finset.Iic (r, 0)).sup (schwartzSeminormFamily ℝ (Space d) ℝ)) η
      *(|1 + ‖x‖| ^ r)⁻¹) * ‖f x‖; swap
    · apply le_of_eq
      ring
    apply mul_le_mul_of_nonneg ?_ (by rfl) (by positivity) (by positivity)
    have h0 := one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (r, 0))
      (k := r) (n := 0) le_rfl le_rfl η x
    rw [Lean.Grind.Field.IsOrdered.le_mul_inv_iff_mul_le _ _ (by positivity)]
    convert h0 using 1
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    ring_nf
    congr
    rw [abs_of_nonneg (by positivity)]

/-!

## D. Construction rules for `IsDistBounded f`

-/

section constructors

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']

@[fun_prop]
lemma zero {d} : IsDistBounded (0 : Space d → F) := by
  apply And.intro
  · fun_prop
  use 1, fun _ => 0, fun _ => 0, fun _ => 0
  simp

/-!

### D.1. Addition

-/
@[fun_prop]
lemma add {d : ℕ} {f g : Space d → F}
    (hf : IsDistBounded f) (hg : IsDistBounded g) : IsDistBounded (f + g) := by
  apply And.intro
  · fun_prop
  rcases hf with ⟨hae1, ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩⟩
  rcases hg with ⟨hae2, ⟨n2, c2, g2, p2, c2_nonneg, p2_bound, bound2⟩⟩
  refine ⟨n1 + n2, Fin.append c1 c2, Fin.append g1 g2, Fin.append p1 p2, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    match i with
    | .inl i =>
      simp only [finSumFinEquiv_apply_left, Fin.append_left, ge_iff_le]
      exact c1_nonneg i
    | .inr i =>
      simp only [finSumFinEquiv_apply_right, Fin.append_right, ge_iff_le]
      exact c2_nonneg i
  · intro i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    match i with
    | .inl i =>
      simp only [finSumFinEquiv_apply_left, Fin.append_left, ge_iff_le]
      exact p1_bound i
    | .inr i =>
      simp only [finSumFinEquiv_apply_right, Fin.append_right, ge_iff_le]
      exact p2_bound i
  · intro x
    apply (norm_add_le _ _).trans
    apply (add_le_add (bound1 x) (bound2 x)).trans
    apply le_of_eq
    rw [← finSumFinEquiv.sum_comp]
    simp

@[fun_prop]
lemma fun_add {d : ℕ} {f g : Space d → F}
    (hf : IsDistBounded f) (hg : IsDistBounded g) : IsDistBounded (fun x => f x + g x) := by
  exact hf.add hg

/-!

### D.2. Finite sums

-/

lemma sum {ι : Type*} {s : Finset ι} {d : ℕ} {f : ι → Space d → F}
    (hf : ∀ i ∈ s, IsDistBounded (f i)) : IsDistBounded (∑ i ∈ s, f i) := by
  classical
  induction' s using Finset.induction with i s hi ih
  · simp
    fun_prop
  rw [Finset.sum_insert]
  apply IsDistBounded.add
  · exact hf i (s.mem_insert_self i)
  · exact ih (fun j hj => hf j (s.mem_insert_of_mem hj))
  exact hi

lemma sum_fun {ι : Type*} {s : Finset ι} {d : ℕ} {f : ι → Space d → F}
    (hf : ∀ i ∈ s, IsDistBounded (f i)) : IsDistBounded (fun x => ∑ i ∈ s, f i x) := by
  convert sum hf using 1
  funext x
  simp

/-!

### D.3. Scalar multiplication

-/

@[fun_prop]
lemma const_smul {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded f) (c : ℝ) : IsDistBounded (c • f) := by
  rcases hf with ⟨hae1, ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩⟩
  apply And.intro
  · fun_prop
  refine ⟨n1, ‖c‖ • c1, g1, p1, ?_, p1_bound, ?_⟩
  · intro i
    simp only [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul]
    have hi := c1_nonneg i
    positivity
  · intro x
    simp [norm_smul]
    conv_rhs => enter [2, x]; rw [mul_assoc]
    rw [← Finset.mul_sum]
    refine mul_le_mul (by rfl) (bound1 x) ?_ ?_
    · exact norm_nonneg (f x)
    · exact abs_nonneg c

@[fun_prop]
lemma neg {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded f) : IsDistBounded (fun x => - f x) := by
  convert hf.const_smul (-1) using 1
  funext x
  simp

@[fun_prop]
lemma const_fun_smul {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded f) (c : ℝ) : IsDistBounded (fun x => c • f x) := by
  convert hf.const_smul c using 1

@[fun_prop]
lemma const_mul_fun {d : ℕ}
    {f : Space d → ℝ}
    (hf : IsDistBounded f) (c : ℝ) : IsDistBounded (fun x => c * f x) := by
  convert hf.const_smul c using 1

@[fun_prop]
lemma mul_const_fun {d : ℕ}
    {f : Space d → ℝ}
    (hf : IsDistBounded f) (c : ℝ) : IsDistBounded (fun x => f x * c) := by
  convert hf.const_smul c using 2
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-!

### D.4. Components of functions

-/

@[fun_prop]
lemma pi_comp {d n : ℕ}
    {f : Space d → EuclideanSpace ℝ (Fin n)}
    (hf : IsDistBounded f) (j : Fin n) : IsDistBounded (fun x => f x j) := by
  rcases hf with ⟨hae1, ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩⟩
  apply And.intro
  · fun_prop
  refine ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, ?_⟩
  intro x
  apply le_trans ?_ (bound1 x)
  simp only [Real.norm_eq_abs]
  rw [@PiLp.norm_eq_of_L2]
  refine Real.abs_le_sqrt ?_
  trans ∑ i ∈ {j}, ‖(f x) i‖ ^ 2
  · simp
  apply Finset.sum_le_univ_sum_of_nonneg
  intro y
  exact sq_nonneg ‖f x y‖

lemma vector_component {d n : ℕ} {f : Space d → Lorentz.Vector n}
    (hf : IsDistBounded f) (j : Fin 1 ⊕ Fin n) : IsDistBounded (fun x => f x j) := by
  rcases hf with ⟨hae1, ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩⟩
  apply And.intro
  · fun_prop
  refine ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, ?_⟩
  intro x
  apply le_trans ?_ (bound1 x)
  simp [Real.norm_eq_abs]

/-!

### D.5. Compositions with additions and subtractions

-/

lemma comp_add_right {d : ℕ} {f : Space d → F}
    (hf : IsDistBounded f) (c : Space d) :
    IsDistBounded (fun x => f (x + c)) := by
  rcases hf with ⟨hae1, ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩⟩
  apply And.intro
  · simp
    apply AEStronglyMeasurable.comp_measurable
    · rw [Measure.IsAddRightInvariant.map_add_right_eq_self]
      fun_prop
    · fun_prop
  refine ⟨n1, c1, fun i => g1 i + c, p1, c1_nonneg, p1_bound, ?_⟩
  intro x
  apply (bound1 (x + c)).trans
  apply le_of_eq
  congr 1
  funext x
  congr 3
  module

lemma comp_sub_right {d : ℕ} {f : Space d → F}
    (hf : IsDistBounded f) (c : Space d) :
    IsDistBounded (fun x => f (x - c)) := by
  convert hf.comp_add_right (- c) using 1

/-!

### D.6. Congruence with respect to the norm

-/

omit [NormedSpace ℝ F'] in
lemma congr {d : ℕ} {f : Space d → F}
    {g : Space d → F'}
    (hf : IsDistBounded f) (hae : AEStronglyMeasurable g) (hfg : ∀ x, ‖g x‖ = ‖f x‖) :
      IsDistBounded g := by
  rcases hf with ⟨hae1, ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩⟩
  apply And.intro
  · exact hae
  refine ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, ?_⟩
  intro x
  rw [hfg x]
  exact bound1 x

/-!

### D.7. Monotonicity with respect to the norm

-/

omit [NormedSpace ℝ F'] in
lemma mono {d : ℕ} {f : Space d → F}
    {g : Space d → F'}
    (hf : IsDistBounded f) (hae : AEStronglyMeasurable g)
    (hfg : ∀ x, ‖g x‖ ≤ ‖f x‖) : IsDistBounded g := by
  rcases hf with ⟨hae1, ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩⟩
  apply And.intro
  · exact hae
  refine ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, ?_⟩
  intro x
  exact (hfg x).trans (bound1 x)

/-!

### D.8. Inner products

-/

open InnerProductSpace
@[fun_prop]
lemma inner_left {d n : ℕ}
    {f : Space d → EuclideanSpace ℝ (Fin n) }
    (hf : IsDistBounded f) (y : EuclideanSpace ℝ (Fin n)) :
    IsDistBounded (fun x => ⟪f x, y⟫_ℝ) := by
  rcases hf with ⟨hae1, ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩⟩
  apply And.intro
  · fun_prop
  refine ⟨n1, fun i => ‖y‖ * c1 i, g1, p1, ?_, p1_bound, ?_⟩
  · intro i
    simp only
    have hi := c1_nonneg i
    positivity
  · intro x
    apply (norm_inner_le_norm (f x) y).trans
    rw [mul_comm]
    conv_rhs => enter [2, i]; rw [mul_assoc]
    rw [← Finset.mul_sum]
    refine mul_le_mul (by rfl) (bound1 x) ?_ ?_
    · exact norm_nonneg (f x)
    · exact norm_nonneg y

/-!

### D.9. Scalar multiplication with constant
-/

@[fun_prop]
lemma smul_const {d : ℕ} [NormedSpace ℝ F] {c : Space d → ℝ}
    (hc : IsDistBounded c) (f : F) : IsDistBounded (fun x => c x • f) := by
  apply IsDistBounded.congr (f := fun x => (c x) * ‖f‖)
  · fun_prop
  · fun_prop
  · intro x
    simp [norm_smul]
/-!

## E. Specific functions that are `IsDistBounded`

-/

/-!

### E.1. Constant functions

-/

@[fun_prop]
lemma const {d : ℕ} (f : F) :
    IsDistBounded (d := d) (fun _ : Space d => f) := by
  apply And.intro
  · fun_prop
  use 1, fun _ => ‖f‖, fun _ => 0, fun _ => 0
  simp

/-!

### E.2. Powers of norms

-/

@[fun_prop]
lemma pow {d : ℕ} (n : ℤ) (hn : - (d - 1 : ℕ) ≤ n) :
    IsDistBounded (d := d) (fun x => ‖x‖ ^ n) := by
  apply And.intro
  · apply AEMeasurable.aestronglyMeasurable
    fun_prop
  refine ⟨1, fun _ => 1, fun _ => 0, fun _ => n, ?_, ?_, ?_⟩
  · simp
  · simp
    exact hn
  · intro x
    simp

@[fun_prop]
lemma pow_shift {d : ℕ} (n : ℤ)
    (g : Space d) (hn : - (d - 1 : ℕ) ≤ n) :
    IsDistBounded (d := d) (fun x => ‖x - g‖ ^ n) := by
  apply And.intro
  · apply AEMeasurable.aestronglyMeasurable
    fun_prop
  refine ⟨1, fun _ => 1, fun _ => (- g), fun _ => n, ?_, ?_, ?_⟩
  · simp
  · simp
    exact hn
  · intro x
    simp
    rfl

@[fun_prop]
lemma inv_shift {d : ℕ}
    (g : Space d.succ.succ) :
    IsDistBounded (d := d.succ.succ) (fun x => ‖x - g‖⁻¹) := by
  convert IsDistBounded.pow_shift (d := d.succ.succ) (-1) g (by simp) using 1
  ext1 x
  simp
@[fun_prop]
lemma nat_pow {d : ℕ} (n : ℕ) :
    IsDistBounded (d := d) (fun x => ‖x‖ ^ n) := by
  exact IsDistBounded.pow (d := d) (n : ℤ) (by omega)

@[fun_prop]
lemma norm_add_nat_pow {d : ℕ} (n : ℕ) (a : ℝ) :
    IsDistBounded (d := d) (fun x => (‖x‖ + a) ^ n) := by
  conv =>
    enter [1, x]
    rw [add_pow]
  apply IsDistBounded.sum_fun
  intro i _
  fun_prop

@[fun_prop]
lemma norm_add_pos_nat_zpow {d : ℕ} (n : ℤ) (a : ℝ) (ha : 0 < a) :
    IsDistBounded (d := d) (fun x => (‖x‖ + a) ^ n) := by
  match n with
  | Int.ofNat n => fun_prop
  | Int.negSucc n =>
    apply IsDistBounded.mono (f := fun x => (a ^ ((n + 1)))⁻¹)
    · fun_prop
    · apply AEMeasurable.aestronglyMeasurable
      fun_prop
    · intro x
      simp only [zpow_negSucc, norm_inv, norm_pow, Real.norm_eq_abs]
      refine inv_anti₀ (by positivity) ?_
      refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by simp)).mpr ?_
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      simp

@[fun_prop]
lemma nat_pow_shift {d : ℕ} (n : ℕ)
    (g : Space d) :
    IsDistBounded (d := d) (fun x => ‖x - g‖ ^ n) := by
  exact IsDistBounded.pow_shift (d := d) (n : ℤ) g (by omega)

@[fun_prop]
lemma norm_sub {d : ℕ} (g : Space d) :
    IsDistBounded (d := d) (fun x => ‖x - g‖) := by
  convert IsDistBounded.nat_pow_shift (d := d) 1 g using 1
  ext1 x
  simp

@[fun_prop]
lemma norm_add {d : ℕ} (g : Space d) :
    IsDistBounded (d := d) (fun x => ‖x + g‖) := by
  convert IsDistBounded.nat_pow_shift (d := d) 1 (- g) using 1
  ext1 x
  simp

@[fun_prop]
lemma inv {n : ℕ} :
    IsDistBounded (d := n.succ.succ) (fun x => ‖x‖⁻¹) := by
  convert IsDistBounded.pow (d := n.succ.succ) (-1) (by simp) using 1
  ext1 x
  simp

@[fun_prop]
lemma norm {d : ℕ} : IsDistBounded (d := d) (fun x => ‖x‖) := by
  convert IsDistBounded.nat_pow (d := d) 1 using 1
  ext1 x
  simp

@[fun_prop]
lemma log_norm {d : ℕ} :
    IsDistBounded (d := d.succ.succ) (fun x => Real.log ‖x‖) := by
  apply IsDistBounded.mono (f := fun x => ‖x‖⁻¹ + ‖x‖)
  · fun_prop
  · apply AEMeasurable.aestronglyMeasurable
    fun_prop
  · intro x
    simp only [Nat.succ_eq_add_one, Real.norm_eq_abs]
    conv_rhs => rw [abs_of_nonneg (by positivity)]
    have h1 := Real.neg_inv_le_log (x := ‖x‖) (by positivity)
    have h2 := Real.log_le_rpow_div (x := ‖x‖) (by positivity) (ε := 1) (by positivity)
    simp_all
    rw [abs_le']
    generalize Real.log ‖x‖ = r at *
    apply And.intro
    · apply h2.trans
      simp
    · rw [neg_le]
      apply le_trans _ h1
      simp

lemma zpow_smul_self {d : ℕ} (n : ℤ) (hn : - (d - 1 : ℕ) - 1 ≤ n) :
    IsDistBounded (d := d) (fun x => ‖x‖ ^ n • x) := by
  by_cases hzero : n = -1
  · apply IsDistBounded.mono (f := fun x => (1 : ℝ))
    · fun_prop
    · apply AEMeasurable.aestronglyMeasurable
      fun_prop
    · intro x
      simp [norm_smul]
      subst hzero
      simp only [Int.reduceNeg, zpow_neg, zpow_one]
      by_cases hx : x = 0
      · subst hx
        simp
      rw [inv_mul_cancel₀]
      simpa using hx
  apply IsDistBounded.congr (f := fun x => ‖x‖ ^ (n + 1))
  · apply pow
    omega
  · apply AEMeasurable.aestronglyMeasurable
    fun_prop
  · intro x
    by_cases hx : x = 0
    · subst hx
      simp only [norm_zero, smul_zero, norm_zpow]
      rw [@zero_zpow_eq]
      rw [if_neg]
      omega
    · simp [norm_smul]
      rw [zpow_add₀]
      simp only [zpow_one]
      ring_nf
      simpa using hx

lemma zpow_smul_repr_self {d : ℕ} (n : ℤ) (hn : - (d - 1 : ℕ) - 1 ≤ n) :
    IsDistBounded (d := d) (fun x => ‖x‖ ^ n • basis.repr x) := by
  apply IsDistBounded.congr (f := fun x => ‖x‖ ^ n • x)
  · apply zpow_smul_self
    exact hn
  · apply AEMeasurable.aestronglyMeasurable
    fun_prop
  · intro x
    simp [norm_smul]

lemma zpow_smul_repr_self_sub {d : ℕ} (n : ℤ) (hn : - (d - 1 : ℕ) - 1 ≤ n)
    (y : Space d) :
    IsDistBounded (d := d) (fun x => ‖x - y‖ ^ n • basis.repr (x - y)) := by
  apply (zpow_smul_repr_self n hn).comp_sub_right y

lemma inv_pow_smul_self {d : ℕ} (n : ℕ) (hn : - (d - 1 : ℕ) - 1 ≤ (- n : ℤ)) :
    IsDistBounded (d := d) (fun x => ‖x‖⁻¹ ^ n • x) := by
  convert zpow_smul_self (n := - (n : ℤ)) (by omega) using 1
  funext x
  simp

lemma inv_pow_smul_repr_self {d : ℕ} (n : ℕ) (hn : - (d - 1 : ℕ) - 1 ≤ (- n : ℤ)) :
    IsDistBounded (d := d) (fun x => ‖x‖⁻¹ ^ n • basis.repr x) := by
  convert zpow_smul_repr_self (n := - (n : ℤ)) (by omega) using 1
  funext x
  simp

/-!

## F. Multiplication by norms and components

-/

lemma norm_smul_nat_pow {d} (p : ℕ) (c : Space d) :
    IsDistBounded (fun x => ‖x‖ * ‖x + c‖ ^ p) := by
  apply IsDistBounded.mono (f := fun x => ‖x‖ * (‖x‖ + ‖c‖) ^ p)
  · conv =>
      enter [1, x]
      rw [add_pow]
      rw [Finset.mul_sum]
    apply IsDistBounded.sum_fun
    intro i _
    conv =>
      enter [1, x]
      rw [← mul_assoc, ← mul_assoc]
    apply IsDistBounded.mul_const_fun
    apply IsDistBounded.mul_const_fun
    convert IsDistBounded.nat_pow (n := i + 1) using 1
    funext x
    ring
  · apply AEMeasurable.aestronglyMeasurable
    fun_prop
  · intro x
    simp [norm_mul, norm_pow, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    have h1 : ‖x + c‖ ≤ ‖x‖ + ‖c‖ := norm_add_le x c
    have h2 : ‖x + c‖ ^ p ≤ (‖x‖ + ‖c‖) ^ p := by
      refine pow_le_pow_left₀ (by positivity) h1 p
    apply (mul_le_mul (by rfl) h2 (by positivity) (by positivity)).trans
    rfl

lemma norm_smul_zpow {d} (p : ℤ) (c : Space d) (hn : - (d - 1 : ℕ) ≤ p) :
    IsDistBounded (fun x => ‖x‖ * ‖x + c‖ ^ p) := by
  match p with
  | Int.ofNat p => exact norm_smul_nat_pow p c
  | Int.negSucc p =>
    suffices h0 : IsDistBounded (fun x => ‖x - c‖ * (‖x‖ ^ (p + 1))⁻¹) by
      convert h0.comp_sub_right (- c) using 1
      funext x
      simp
    suffices h0 : IsDistBounded (fun x => (‖x‖ + ‖c‖) * (‖x‖ ^ (p + 1))⁻¹) by
      apply h0.mono
      · fun_prop
      · intro x
        simp [norm_mul, norm_inv, norm_pow, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
        apply mul_le_mul (norm_sub_le x c) (by rfl) (by positivity) (by positivity)
    suffices h0 : IsDistBounded (fun x => ‖x‖ * (‖x‖ ^ (p + 1))⁻¹ + ‖c‖ * (‖x‖ ^ (p + 1))⁻¹) by
      convert h0 using 1
      funext x
      ring
    suffices h0 : IsDistBounded (fun x => ‖x‖ * (‖x‖ ^ (p + 1))⁻¹) by
      apply h0.add
      · apply IsDistBounded.const_mul_fun
        exact IsDistBounded.pow (d := d) (n := -(p + 1)) (by grind)
    by_cases hp : p = 0
    · subst hp
      simp only [zero_add, pow_one]
      apply IsDistBounded.mono (f := fun x => (1 : ℝ))
      · fun_prop
      · apply AEMeasurable.aestronglyMeasurable
        fun_prop
      · intro x
        simp only [norm_mul, norm_norm, norm_inv, one_mem, CStarRing.norm_of_mem_unitary]
        by_cases hx : ‖x‖ ≠ 0
        · rw [mul_inv_cancel₀ (by positivity)]
        · simp at hx
          subst hx
          simp
    convert IsDistBounded.pow (d := d) (n := - p) (by grind) using 1
    funext x
    trans (‖x‖ ^ p)⁻¹; swap
    · rw [@zpow_neg]
      simp
    by_cases hx : ‖x‖ ≠ 0
    field_simp
    ring
    simp at hx
    subst hx
    simp only [norm_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, inv_zero, mul_zero, zero_eq_inv]
    rw [@zero_pow_eq]
    simp [hp]

@[fun_prop]
lemma norm_smul_isDistBounded {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded f) :
    IsDistBounded (fun x => ‖x‖ • f x) := by
  obtain ⟨hae, ⟨n, c, g, p, c_nonneg, p_bound, bound⟩⟩ := hf
  apply IsDistBounded.mono (f := fun x => ‖x‖ * ∑ i, (c i * ‖x + g i‖ ^ (p i)))
  · apply IsDistBounded.congr (f := fun x => ∑ i, (c i * (‖x‖ * ‖x + g i‖ ^ (p i))))
    · apply IsDistBounded.sum_fun
      intro i _
      apply IsDistBounded.const_mul_fun
      exact norm_smul_zpow (p i) (g i) (p_bound i)
    · fun_prop
    · intro x
      congr
      rw [Finset.mul_sum]
      congr
      funext i
      ring
  · fun_prop
  · intro x
    simp [_root_.norm_smul]
    apply (mul_le_mul (by rfl) (bound x) (by positivity) (by positivity)).trans
    rw [abs_of_nonneg]
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg
    · exact c_nonneg i
    · positivity

@[fun_prop]
lemma norm_mul_isDistBounded {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) :
    IsDistBounded (fun x => ‖x‖ * f x) := by
  convert hf.norm_smul_isDistBounded using 1

@[fun_prop]
lemma component_smul_isDistBounded {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded f) (i : Fin d) :
    IsDistBounded (fun x => x i • f x) := by
  apply IsDistBounded.mono (f := fun x => ‖x‖ • f x)
  · fun_prop
  · apply AEStronglyMeasurable.smul
    · have h1 : AEStronglyMeasurable (fun x => Space.coordCLM i x) := by
        fun_prop
      convert h1 using 1
      funext i
      simp [coordCLM_apply, coord_apply]
    · fun_prop
  · intro x
    simp [norm_smul]
    apply mul_le_mul ?_ (by rfl) (by positivity) (by positivity)
    exact abs_eval_le_norm x i

@[fun_prop]
lemma component_mul_isDistBounded {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) (i : Fin d) :
    IsDistBounded (fun x => x i * f x) := by
  convert hf.component_smul_isDistBounded i using 2

@[fun_prop]
lemma isDistBounded_smul_self {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) : IsDistBounded (fun x => f x • x) := by
  apply IsDistBounded.congr (f := fun x => ‖x‖ * f x)
  · fun_prop
  · apply AEStronglyMeasurable.smul
    · fun_prop
    · fun_prop
  · intro x
    simp [norm_smul]
    ring

@[fun_prop]
lemma isDistBounded_smul_self_repr {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) : IsDistBounded (fun x => f x • basis.repr x) := by
  apply IsDistBounded.congr (f := fun x => ‖x‖ * f x)
  · fun_prop
  · apply AEStronglyMeasurable.smul
    · fun_prop
    · fun_prop
  · intro x
    simp [norm_smul]
    ring

@[fun_prop]
lemma isDistBounded_smul_inner {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded f) (y : Space d) : IsDistBounded (fun x => ⟪y, x⟫_ℝ • f x) := by
  have h1 (x : Space d) : ⟪y, x⟫_ℝ • f x = ∑ i, (y i * x i) • f x := by
    rw [inner_eq_sum, ← Finset.sum_smul]
  conv =>
    enter [1, x]
    rw [h1 x]
  apply IsDistBounded.sum_fun
  intro i _
  simp [← smul_smul]
  refine const_fun_smul ?_ (y i)
  fun_prop

lemma isDistBounded_smul_inner_of_smul_norm {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded (fun x => ‖x‖ • f x)) (hae : AEStronglyMeasurable f) (y : Space d) :
    IsDistBounded (fun x => ⟪y, x⟫_ℝ • f x) := by
  have h1 (x : Space d) : ⟪y, x⟫_ℝ • f x = ∑ i, (y i * x i) • f x := by
    rw [inner_eq_sum, ← Finset.sum_smul]
  conv =>
    enter [1, x]
    rw [h1 x]
  apply IsDistBounded.sum_fun
  intro i _
  simp [← smul_smul]
  refine const_fun_smul ?_ (y i)
  apply hf.mono
  · fun_prop
  · intro x
    simp [norm_smul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact abs_eval_le_norm x i

@[fun_prop]
lemma isDistBounded_mul_inner {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) (y : Space d) : IsDistBounded (fun x => ⟪y, x⟫_ℝ * f x) := by
  convert hf.isDistBounded_smul_inner y using 2

lemma isDistBounded_mul_inner' {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) (y : Space d) : IsDistBounded (fun x => ⟪x, y⟫_ℝ * f x) := by
  convert hf.isDistBounded_smul_inner y using 2
  rw [real_inner_comm]
  simp

lemma isDistBounded_mul_inner_of_smul_norm {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded (fun x => ‖x‖ * f x)) (hae : AEStronglyMeasurable f) (y : Space d) :
    IsDistBounded (fun x => ⟪y, x⟫_ℝ * f x) := by
  convert hf.isDistBounded_smul_inner_of_smul_norm hae y using 2

@[fun_prop]
lemma mul_inner_pow_neg_two {d : ℕ}
    (y : Space d.succ.succ) :
    IsDistBounded (fun x => ⟪y, x⟫_ℝ * ‖x‖ ^ (- 2 : ℤ)) := by
  apply IsDistBounded.mono (f := fun x => (‖y‖ * ‖x‖) * ‖x‖ ^ (- 2 : ℤ))
  · simp [mul_assoc]
    apply IsDistBounded.const_mul_fun
    apply IsDistBounded.congr (f := fun x => ‖x‖ ^ (- 1 : ℤ))
    · apply IsDistBounded.pow (d := d.succ.succ) (-1) (by simp)
    · apply AEMeasurable.aestronglyMeasurable
      fun_prop
    · intro x
      simp only [norm_mul, norm_norm, norm_inv, norm_zpow, Int.reduceNeg, zpow_neg, zpow_one]
      by_cases hx : x = 0
      · subst hx
        simp
      have hx' : ‖x‖ ≠ 0 := by
        simpa using hx
      field_simp
  · apply AEMeasurable.aestronglyMeasurable
    fun_prop
  · intro x
    simp
    apply mul_le_mul_of_nonneg _ (by rfl) (by positivity) (by positivity)
    exact abs_real_inner_le_norm y x

end constructors
end IsDistBounded
