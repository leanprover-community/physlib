/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.Space.Integrals.RadialAngularMeasure
public import Physlib.SpaceAndTime.Time.InnerProductSpace
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
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

* None.
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

/-- The boundedness condition on a function `Space d → F`
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
    AEStronglyMeasurable (fun x => ‖((1 + ‖x‖) ^ r)⁻¹‖ • f x) :=
  AEStronglyMeasurable.smul (AEMeasurable.aestronglyMeasurable (by fun_prop)) (by fun_prop)

@[fun_prop]
lemma aeStronglyMeasurable_time_schwartzMap_smul {d : ℕ} {f : Space d → F}
    (hf : IsDistBounded f) (η : 𝓢(Time × Space d, ℝ)) :
    AEStronglyMeasurable (fun x => η x • f x.2) :=
  AEStronglyMeasurable.smul (by fun_prop) (AEStronglyMeasurable.comp_snd (by fun_prop))

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
      refine (mul_le_mul_of_nonneg_left (bound x) (norm_nonneg (η x))).trans (le_of_eq ?_)
      simp only [Real.norm_eq_abs]
      rw [Finset.abs_sum_of_nonneg (fun i _ => mul_nonneg (c_nonneg i) (by positivity)),
        Finset.mul_sum]
      ring_nf
    · refine MeasureTheory.integrable_finsetSum _ fun i _ => Integrable.const_mul ?_ _
      simpa using (h2 (p i) (p_bound i) (g i) η).norm
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
  rw [← MeasureTheory.integrable_norm_iff (AEMeasurable.aestronglyMeasurable (by fun_prop))]
  simp only [norm_mul, norm_zpow, norm_norm]
  match d with
  | 0 => simp only [Real.norm_eq_abs, Integrable.of_finite]
  | d + 1 =>
  by_cases hp' : p = 0
  · subst hp'
    simpa using η.integrable.norm
  suffices h1 : Integrable (fun x => ‖η x‖ * ‖x‖ ^ (p + d)) (radialAngularMeasure (d := (d + 1))) by
    rw [integrable_radialAngularMeasure_iff] at h1
    convert h1 using 1
    funext x
    generalize ‖x‖ = r
    simp only [Real.norm_eq_abs, add_tsub_cancel_right, one_div, smul_eq_mul]
    rw [mul_left_comm]
    congr 1
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
  rw [mul_comm, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]

@[fun_prop]
lemma integrable_space_mul {d : ℕ} {f : Space d → ℝ} (hf : IsDistBounded f)
    (η : 𝓢(Space d, ℝ)) :
    Integrable (fun x : Space d => η x * f x) volume := by
  exact hf.integrable_space η

@[fun_prop]
lemma integrable_space_fderiv {d : ℕ} {f : Space d → F} (hf : IsDistBounded f)
    (η : 𝓢(Space d, ℝ)) (y : Space d) :
    Integrable (fun x : Space d => fderiv ℝ η x y • f x) volume :=
  hf.integrable_space (LineDeriv.lineDerivOpCLM ℝ _ y η)

@[fun_prop]
lemma integrable_space_fderiv_mul {d : ℕ} {f : Space d → ℝ} (hf : IsDistBounded f)
    (η : 𝓢(Space d, ℝ)) (y : Space d) :
    Integrable (fun x : Space d => fderiv ℝ η x y * f x) volume :=
  hf.integrable_space (LineDeriv.lineDerivOpCLM ℝ _ y η)

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
    · exact inv_anti₀ (by positivity)
        (pow_le_pow_left₀ (by positivity) (by simpa using norm_fst_le x) rt1)
    · exact inv_anti₀ (by positivity)
        (pow_le_pow_left₀ (by positivity) (by simpa using norm_snd_le x) rt2)

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
      refine (mul_le_mul_of_nonneg_left (bound x.2) (norm_nonneg (η x))).trans (le_of_eq ?_)
      simp only [Real.norm_eq_abs]
      rw [Finset.abs_sum_of_nonneg (fun i _ => mul_nonneg (c_nonneg i) (by positivity)),
        Finset.mul_sum]
      ring_nf
    · refine MeasureTheory.integrable_finsetSum _ fun i _ => Integrable.const_mul ?_ _
      simpa using (h2 (p i) (p_bound i) (g i) η).norm
  /- Reducing the problem to `Integrable (fun x : Space d => η x * ‖x‖ ^ p)` -/
  suffices h0 : ∀ (p : ℤ) (hp : - (d - 1 : ℕ) ≤ p) (η : 𝓢(Time × Space d, ℝ)),
      Integrable (fun x : Time × Space d => η x * ‖x.2‖ ^ p) volume by
    intro p hp c η
    suffices h1 : Integrable (fun (x : Time × Space d) =>
        η ((x + (0, c)) - (0, c)) * ‖(x + (0, c)).2‖ ^ p) (volume.prod volume) by
      simp_all only [add_sub_cancel_right, Prod.snd_add]
      exact h1
    apply MeasureTheory.Integrable.comp_add_right (g := (0, c))
      (f := fun x => η (x - (0, c)) * ‖x.2‖ ^ p)
    apply h0 p hp (η.compCLM (𝕜 := ℝ) ?_ ?_)
    · apply Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1 + ‖c‖)
      · convert Function.HasTemperateGrowth.const (ContinuousLinearMap.id ℝ (Time × Space d))
        simp [fderiv_sub_const]
      · fun_prop
      · refine fun x => (norm_sub_le _ _).trans (le_of_sub_nonneg ?_)
        ring_nf
        simp only [Prod.norm_mk, norm_zero, norm_nonneg, sup_of_le_right]
        ring_nf
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
    | 0 =>
      simp_all only [zero_tsub, CharP.cast_eq_zero, neg_zero, Real.norm_eq_abs, add_zero,
        radialAngularMeasure_zero_eq_volume]
      exact h1
    | d + 1 =>
    rw [radialAngularMeasure, MeasureTheory.prod_withDensity_right] at h1
    erw [integrable_withDensity_iff_integrable_smul₀ (by fun_prop)] at h1
    convert! h1 using 1
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
    (AEMeasurable.aestronglyMeasurable (by fun_prop))
  filter_upwards with x
  simp only [Real.norm_eq_abs, norm_iteratedFDeriv_zero]
  rw [abs_of_nonneg (by positivity), mul_comm, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  exact mul_le_mul_of_nonneg_right
    (zpow_le_zpow_left₀ (by omega) (norm_nonneg _) (norm_snd_le x)) (abs_nonneg _)

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
    have pMax_max (i : Fin n.succ) : p i ≤ pMax :=
      Finset.le_max' _ _ (Finset.mem_image_of_mem p (Finset.mem_univ i))
    obtain ⟨r, hr⟩ := h0 pMax
    use r
    apply Integrable.mono (g := fun x => ∑ i, (c i * (‖((1 + ‖x‖) ^ r)⁻¹‖ * ‖x + g i‖ ^ p i))) _
    · fun_prop
    · filter_upwards with x
      rw [norm_smul]
      refine (mul_le_mul_of_nonneg_left (bound x) (by positivity)).trans (le_of_eq ?_)
      simp only [norm_inv, norm_pow, Real.norm_eq_abs, abs_abs]
      rw [Finset.abs_sum_of_nonneg (fun i _ => mul_nonneg (c_nonneg i) (by positivity)),
        Finset.mul_sum]
      ring_nf
    · refine MeasureTheory.integrable_finsetSum _ fun i _ => Integrable.const_mul ?_ _
      refine (hr (p i) (p_bound i) (g i) (pMax_max i)).mono (by fun_prop) ?_
      filter_upwards with x
      simp
  match d with
  | 0 => simp
  | d + 1 =>
  suffices h0 : ∀ (q : ℕ) (c : Space (d + 1)), Integrable (fun x => ‖x + c‖ ^ (q - d : ℤ)
        * ‖((1 + ‖x‖) ^ (q + (radialAngularMeasure (d := d + 1)).integrablePower))⁻¹‖) volume by
    intro pMax
    use (pMax + d).toNat + (radialAngularMeasure (d := d + 1)).integrablePower
    intro p hp c p_le
    refine (h0 (p + d).toNat c).mono (by fun_prop) ?_
    filter_upwards with x
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
    refine h0.congr (Filter.eventuallyEq_of_mem (compl_mem_ae_iff.mpr (measure_singleton 0))
      fun x hx => ?_)
    simp [← mul_assoc]
    left
    rw [zpow_sub₀ (by simpa using hx), zpow_natCast, zpow_natCast]
    field_simp
  intro q v
  have hr1 (x : Space (d + 1)) :
        ‖((1 + ‖x - v‖) ^ (q + m))⁻¹‖ = ((1 + ‖x - v‖) ^ (q + m))⁻¹ := by
      simp only [norm_inv, norm_pow, Real.norm_eq_abs, inv_inj]
      rw [abs_of_nonneg (by positivity)]
  apply integrable_of_le_of_pow_mul_le (C₁ := 1) (C₂ := (1 + ‖v‖) ^ (q + m))
  · intro x
    rw [hr1]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by simp))
  · intro x
    rw [hr1]
    refine mul_inv_le_of_le_mul₀ ?_ (by positivity) ?_
    · positivity
    change ‖x‖ ^ (q + m) ≤ _
    calc ‖x‖ ^ (q + m) ≤ ((1 + ‖v‖) * (1 + ‖x - v‖)) ^ (q + m) := by
          refine pow_le_pow_left₀ (norm_nonneg x) ?_ _
          nlinarith [norm_le_norm_add_norm_sub' x v, norm_nonneg (x - v), norm_nonneg v]
      _ = (1 + ‖v‖) ^ (q + m) * (1 + ‖x - v‖) ^ (q + m) := mul_pow _ _ _
  · exact Measurable.aestronglyMeasurable (by fun_prop)

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
  · refine (Integrable.congr' hr (AEStronglyMeasurable.mul (by fun_prop)
      (AEMeasurable.aestronglyMeasurable (by fun_prop))) ?_).const_mul _ |>.mul_const _
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
    rw [le_mul_inv_iff₀ (by positivity)]
    convert! h0 using 1
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
lemma zero {d} : IsDistBounded (0 : Space d → F) :=
  ⟨by fun_prop, 1, fun _ => 0, fun _ => 0, fun _ => 0, by simp⟩

/-!

### D.1. Addition

-/
@[fun_prop]
lemma add {d : ℕ} {f g : Space d → F}
    (hf : IsDistBounded f) (hg : IsDistBounded g) : IsDistBounded (f + g) := by
  rcases hf with ⟨hae1, ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩⟩
  rcases hg with ⟨hae2, ⟨n2, c2, g2, p2, c2_nonneg, p2_bound, bound2⟩⟩
  refine ⟨by fun_prop, n1 + n2, Fin.append c1 c2, Fin.append g1 g2, Fin.append p1 p2, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left i => simpa using c1_nonneg i
    | right i => simpa using c2_nonneg i
  · intro i
    induction i using Fin.addCases with
    | left i => simpa using p1_bound i
    | right i => simpa using p2_bound i
  · intro x
    refine ((norm_add_le _ _).trans (add_le_add (bound1 x) (bound2 x))).trans_eq ?_
    simp [Fin.sum_univ_add]

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
  induction s using Finset.induction with
  | empty => simpa using zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (s.mem_insert_self i)).add (ih fun j hj => hf j (s.mem_insert_of_mem hj))

lemma sum_fun {ι : Type*} {s : Finset ι} {d : ℕ} {f : ι → Space d → F}
    (hf : ∀ i ∈ s, IsDistBounded (f i)) : IsDistBounded (fun x => ∑ i ∈ s, f i x) :=
  Finset.sum_fn s f ▸ sum hf

/-!

### D.3. Scalar multiplication

-/

@[fun_prop]
lemma const_smul {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded f) (c : ℝ) : IsDistBounded (c • f) := by
  rcases hf with ⟨hae1, ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩⟩
  refine ⟨by fun_prop, n1, ‖c‖ • c1, g1, p1,
    fun i => mul_nonneg (norm_nonneg c) (c1_nonneg i), p1_bound, fun x => ?_⟩
  simp only [Pi.smul_apply, norm_smul, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (bound1 x) (norm_nonneg c)

@[fun_prop]
lemma neg {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded f) : IsDistBounded (fun x => - f x) := by
  simpa [Pi.neg_def] using hf.const_smul (-1)

@[fun_prop]
lemma const_fun_smul {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded f) (c : ℝ) : IsDistBounded (fun x => c • f x) := hf.const_smul c

@[fun_prop]
lemma const_mul_fun {d : ℕ}
    {f : Space d → ℝ}
    (hf : IsDistBounded f) (c : ℝ) : IsDistBounded (fun x => c * f x) := hf.const_smul c

@[fun_prop]
lemma mul_const_fun {d : ℕ}
    {f : Space d → ℝ}
    (hf : IsDistBounded f) (c : ℝ) : IsDistBounded (fun x => f x * c) := by
  simpa [Pi.smul_def, mul_comm] using hf.const_smul c

/-!

### D.4. Components of functions

-/

@[fun_prop]
lemma pi_comp {d n : ℕ}
    {f : Space d → EuclideanSpace ℝ (Fin n)}
    (hf : IsDistBounded f) (j : Fin n) : IsDistBounded (fun x => f x j) := by
  rcases hf with ⟨hae1, ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩⟩
  exact ⟨by fun_prop, n1, c1, g1, p1, c1_nonneg, p1_bound,
    fun x => (PiLp.norm_apply_le (f x) j).trans (bound1 x)⟩

lemma vector_component {d n : ℕ} {f : Space d → Lorentz.Vector n}
    (hf : IsDistBounded f) (j : Fin 1 ⊕ Fin n) : IsDistBounded (fun x => f x j) := by
  rcases hf with ⟨hae1, ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩⟩
  refine ⟨by fun_prop, n1, c1, g1, p1, c1_nonneg, p1_bound, fun x => le_trans ?_ (bound1 x)⟩
  simp [Real.norm_eq_abs]

/-!

### D.5. Compositions with additions and subtractions

-/

lemma comp_add_right {d : ℕ} {f : Space d → F}
    (hf : IsDistBounded f) (c : Space d) :
    IsDistBounded (fun x => f (x + c)) := by
  rcases hf with ⟨hae1, ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩⟩
  refine ⟨hae1.comp_measurePreserving (measurePreserving_add_right volume c),
    n1, c1, fun i => g1 i + c, p1, c1_nonneg, p1_bound, fun x => ?_⟩
  refine (bound1 (x + c)).trans_eq (Finset.sum_congr rfl fun i _ => ?_)
  rw [add_right_comm, add_assoc]

lemma comp_sub_right {d : ℕ} {f : Space d → F}
    (hf : IsDistBounded f) (c : Space d) :
    IsDistBounded (fun x => f (x - c)) := hf.comp_add_right (- c)

/-!

### D.6. Congruence with respect to the norm

-/

omit [NormedSpace ℝ F'] in
lemma congr {d : ℕ} {f : Space d → F}
    {g : Space d → F'}
    (hf : IsDistBounded f) (hae : AEStronglyMeasurable g) (hfg : ∀ x, ‖g x‖ = ‖f x‖) :
      IsDistBounded g := by
  rcases hf with ⟨hae1, ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩⟩
  exact ⟨hae, n1, c1, g1, p1, c1_nonneg, p1_bound, fun x => (hfg x).le.trans (bound1 x)⟩

/-!

### D.7. Monotonicity with respect to the norm

-/

omit [NormedSpace ℝ F'] in
lemma mono {d : ℕ} {f : Space d → F}
    {g : Space d → F'}
    (hf : IsDistBounded f) (hae : AEStronglyMeasurable g)
    (hfg : ∀ x, ‖g x‖ ≤ ‖f x‖) : IsDistBounded g := by
  rcases hf with ⟨hae1, ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩⟩
  exact ⟨hae, n1, c1, g1, p1, c1_nonneg, p1_bound, fun x => (hfg x).trans (bound1 x)⟩

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
  refine ⟨by fun_prop, n1, fun i => ‖y‖ * c1 i, g1, p1,
    fun i => mul_nonneg (norm_nonneg y) (c1_nonneg i), p1_bound, fun x => ?_⟩
  simp only [mul_assoc, ← Finset.mul_sum]
  exact ((norm_inner_le_norm (f x) y).trans_eq (mul_comm _ _)).trans
    (mul_le_mul_of_nonneg_left (bound1 x) (norm_nonneg y))

/-!

### D.9. Scalar multiplication with constant
-/

@[fun_prop]
lemma smul_const {d : ℕ} [NormedSpace ℝ F] {c : Space d → ℝ}
    (hc : IsDistBounded c) (f : F) : IsDistBounded (fun x => c x • f) :=
  (hc.mul_const_fun ‖f‖).congr (by fun_prop) fun x => by simp [norm_smul]
/-!

## E. Specific functions that are `IsDistBounded`

-/

/-!

### E.1. Constant functions

-/

@[fun_prop]
lemma const {d : ℕ} (f : F) :
    IsDistBounded (d := d) (fun _ : Space d => f) :=
  ⟨by fun_prop, 1, fun _ => ‖f‖, fun _ => 0, fun _ => 0, by simp⟩

/-!

### E.2. Powers of norms

-/

@[fun_prop]
lemma pow {d : ℕ} (n : ℤ) (hn : - (d - 1 : ℕ) ≤ n) :
    IsDistBounded (d := d) (fun x => ‖x‖ ^ n) :=
  ⟨AEMeasurable.aestronglyMeasurable (by fun_prop), 1, fun _ => 1, fun _ => 0, fun _ => n,
    fun _ => zero_le_one, fun _ => hn, fun x => by simp⟩

@[fun_prop]
lemma pow_shift {d : ℕ} (n : ℤ)
    (g : Space d) (hn : - (d - 1 : ℕ) ≤ n) :
    IsDistBounded (d := d) (fun x => ‖x - g‖ ^ n) :=
  ⟨AEMeasurable.aestronglyMeasurable (by fun_prop), 1, fun _ => 1, fun _ => - g, fun _ => n,
    fun _ => zero_le_one, fun _ => hn, fun x => by simp [sub_eq_add_neg]⟩

@[fun_prop]
lemma inv_shift {d : ℕ} (g : Space d) (hd : 2 ≤ d := by omega) :
    IsDistBounded (d := d) (fun x => ‖x - g‖⁻¹) := by
  simpa using IsDistBounded.pow_shift (d := d) (-1) g (by omega)
@[fun_prop]
lemma nat_pow {d : ℕ} (n : ℕ) :
    IsDistBounded (d := d) (fun x => ‖x‖ ^ n) := by
  exact IsDistBounded.pow (d := d) (n : ℤ) (by omega)

@[fun_prop]
lemma norm_add_nat_pow {d : ℕ} (n : ℕ) (a : ℝ) :
    IsDistBounded (d := d) (fun x => (‖x‖ + a) ^ n) := by
  simp only [add_pow]
  exact sum_fun fun i _ => by fun_prop

@[fun_prop]
lemma norm_add_pos_nat_zpow {d : ℕ} (n : ℤ) (a : ℝ) (ha : 0 < a) :
    IsDistBounded (d := d) (fun x => (‖x‖ + a) ^ n) := by
  match n with
  | Int.ofNat n => fun_prop
  | Int.negSucc n =>
    refine IsDistBounded.mono (f := fun x => (a ^ ((n + 1)))⁻¹) (by fun_prop)
      (AEMeasurable.aestronglyMeasurable (by fun_prop)) fun x => ?_
    simp only [zpow_negSucc, norm_inv, norm_pow, Real.norm_eq_abs, abs_of_nonneg ha.le,
      abs_of_nonneg (show (0:ℝ) ≤ ‖x‖ + a by positivity)]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le (by simp) _)

@[fun_prop]
lemma nat_pow_shift {d : ℕ} (n : ℕ)
    (g : Space d) :
    IsDistBounded (d := d) (fun x => ‖x - g‖ ^ n) :=
  IsDistBounded.pow_shift (d := d) (n : ℤ) g (by omega)

@[fun_prop]
lemma norm_sub {d : ℕ} (g : Space d) :
    IsDistBounded (d := d) (fun x => ‖x - g‖) := by
  simpa using IsDistBounded.nat_pow_shift (d := d) 1 g

@[fun_prop]
lemma norm_add {d : ℕ} (g : Space d) :
    IsDistBounded (d := d) (fun x => ‖x + g‖) := by
  simpa using IsDistBounded.nat_pow_shift (d := d) 1 (- g)

@[fun_prop]
lemma inv {d : ℕ} (hd: 2 ≤ d := by omega):
    IsDistBounded (d := d) (fun x => ‖x‖⁻¹) := by
  simpa using IsDistBounded.pow (d := d) (-1) (by omega)

@[fun_prop]
lemma norm {d : ℕ} : IsDistBounded (d := d) (fun x => ‖x‖) := by
  simpa using IsDistBounded.nat_pow (d := d) 1

@[fun_prop]
lemma log_norm {d : ℕ} (hd : 2 ≤ d := by omega) :
    IsDistBounded (d := d) (fun x => Real.log ‖x‖) := by
  refine IsDistBounded.mono (f := fun x => ‖x‖⁻¹ + ‖x‖) (by fun_prop)
    (AEMeasurable.aestronglyMeasurable (by fun_prop)) fun x => ?_
  have h1 := Real.neg_inv_le_log (x := ‖x‖) (norm_nonneg x)
  have h2 := Real.log_le_rpow_div (x := ‖x‖) (norm_nonneg x) one_pos
  simp only [Real.rpow_one, div_one] at h2
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (show (0:ℝ) ≤ ‖x‖⁻¹ + ‖x‖ by positivity), abs_le']
  constructor
  · exact h2.trans (by simp)
  · linarith [norm_nonneg x]

lemma zpow_smul_self {d : ℕ} (n : ℤ) (hn : - (d - 1 : ℕ) - 1 ≤ n) :
    IsDistBounded (d := d) (fun x => ‖x‖ ^ n • x) := by
  by_cases hzero : n = -1
  · subst hzero
    refine IsDistBounded.mono (f := fun x => (1 : ℝ)) (by fun_prop)
      (AEMeasurable.aestronglyMeasurable (by fun_prop)) fun x => ?_
    simpa [norm_smul, inv_mul_eq_div] using div_self_le_one ‖x‖
  refine IsDistBounded.congr (f := fun x => ‖x‖ ^ (n + 1)) (pow _ (by omega))
    (AEMeasurable.aestronglyMeasurable (by fun_prop)) fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp [zero_zpow (n + 1) (by omega)]
  · simp [norm_smul, zpow_add₀ (norm_ne_zero_iff.mpr hx), mul_comm]

lemma zpow_smul_repr_self {d : ℕ} (n : ℤ) (hn : - (d - 1 : ℕ) - 1 ≤ n) :
    IsDistBounded (d := d) (fun x => ‖x‖ ^ n • basis.repr x) :=
  (zpow_smul_self n hn).congr (AEMeasurable.aestronglyMeasurable (by fun_prop))
    fun x => by simp [norm_smul]

lemma zpow_smul_repr_self_sub {d : ℕ} (n : ℤ) (hn : - (d - 1 : ℕ) - 1 ≤ n)
    (y : Space d) :
    IsDistBounded (d := d) (fun x => ‖x - y‖ ^ n • basis.repr (x - y)) :=
  (zpow_smul_repr_self n hn).comp_sub_right y

lemma inv_pow_smul_self {d : ℕ} (n : ℕ) (hn : - (d - 1 : ℕ) - 1 ≤ (- n : ℤ)) :
    IsDistBounded (d := d) (fun x => ‖x‖⁻¹ ^ n • x) := by
  simpa using zpow_smul_self (n := - (n : ℤ)) (by omega)

lemma inv_pow_smul_repr_self {d : ℕ} (n : ℕ) (hn : - (d - 1 : ℕ) - 1 ≤ (- n : ℤ)) :
    IsDistBounded (d := d) (fun x => ‖x‖⁻¹ ^ n • basis.repr x) := by
  simpa using zpow_smul_repr_self (n := - (n : ℤ)) (by omega)

/-!

## F. Multiplication by norms and components

-/

lemma norm_smul_nat_pow {d} (p : ℕ) (c : Space d) :
    IsDistBounded (fun x => ‖x‖ * ‖x + c‖ ^ p) := by
  refine IsDistBounded.mono (f := fun x => ‖x‖ * (‖x‖ + ‖c‖) ^ p) ?_
    (AEMeasurable.aestronglyMeasurable (by fun_prop)) fun x => ?_
  · simp only [add_pow, Finset.mul_sum, ← mul_assoc]
    refine IsDistBounded.sum_fun fun i _ => mul_const_fun (mul_const_fun ?_ _) _
    simpa [pow_succ'] using IsDistBounded.nat_pow (d := d) (i + 1)
  · simp [norm_mul, norm_pow, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    gcongr
    exact norm_add_le x c

lemma norm_smul_zpow {d} (p : ℤ) (c : Space d) (hn : - (d - 1 : ℕ) ≤ p) :
    IsDistBounded (fun x => ‖x‖ * ‖x + c‖ ^ p) := by
  match p with
  | Int.ofNat p => exact norm_smul_nat_pow p c
  | Int.negSucc p =>
    suffices h0 : IsDistBounded (fun x => ‖x - c‖ * (‖x‖ ^ (p + 1))⁻¹) by
      simpa using h0.comp_sub_right (- c)
    suffices h0 : IsDistBounded (fun x => (‖x‖ + ‖c‖) * (‖x‖ ^ (p + 1))⁻¹) by
      refine h0.mono (by fun_prop) fun x => ?_
      simp [norm_mul, norm_inv, norm_pow, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      gcongr
      exact norm_sub_le x c
    suffices h0 : IsDistBounded (fun x => ‖x‖ * (‖x‖ ^ (p + 1))⁻¹ + ‖c‖ * (‖x‖ ^ (p + 1))⁻¹) by
      simpa [add_mul] using h0
    suffices h0 : IsDistBounded (fun x => ‖x‖ * (‖x‖ ^ (p + 1))⁻¹) by
      refine h0.add (const_mul_fun ?_ ‖c‖)
      exact IsDistBounded.pow (d := d) (n := -(p + 1)) (by grind)
    by_cases hp : p = 0
    · subst hp
      simp only [zero_add, pow_one]
      refine IsDistBounded.mono (f := fun x => (1 : ℝ)) (by fun_prop)
        (AEMeasurable.aestronglyMeasurable (by fun_prop)) fun x => ?_
      simpa [← div_eq_mul_inv] using div_self_le_one ‖x‖
    convert IsDistBounded.pow (d := d) (n := - p) (by grind) using 1
    funext x
    rw [zpow_neg, zpow_natCast]
    rcases eq_or_ne ‖x‖ 0 with hx | hx
    · simp [hx, zero_pow hp]
    · field_simp
      ring

@[fun_prop]
lemma norm_smul_isDistBounded {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded f) :
    IsDistBounded (fun x => ‖x‖ • f x) := by
  obtain ⟨hae, ⟨n, c, g, p, c_nonneg, p_bound, bound⟩⟩ := hf
  refine IsDistBounded.mono (f := fun x => ‖x‖ * ∑ i, (c i * ‖x + g i‖ ^ (p i)))
    (IsDistBounded.congr (f := fun x => ∑ i, (c i * (‖x‖ * ‖x + g i‖ ^ (p i))))
      (sum_fun fun i _ => const_mul_fun (norm_smul_zpow (p i) (g i) (p_bound i)) (c i))
      (by fun_prop) fun x => ?_) (by fun_prop) fun x => ?_
  · rw [Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
  · have h : (0:ℝ) ≤ ∑ i, c i * ‖x + g i‖ ^ p i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (c_nonneg i) (by positivity)
    simp only [_root_.norm_smul, Real.norm_eq_abs, abs_mul, abs_norm, abs_of_nonneg h]
    exact mul_le_mul_of_nonneg_left (bound x) (norm_nonneg x)

@[fun_prop]
lemma norm_mul_isDistBounded {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) :
    IsDistBounded (fun x => ‖x‖ * f x) := hf.norm_smul_isDistBounded

@[fun_prop]
lemma component_smul_isDistBounded {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded f) (i : Fin d) :
    IsDistBounded (fun x => x i • f x) := by
  refine IsDistBounded.mono (f := fun x => ‖x‖ • f x) (by fun_prop)
    (AEStronglyMeasurable.smul ?_ (by fun_prop)) fun x => ?_
  · simpa [coordCLM_apply, coord_apply] using
      (by fun_prop : AEStronglyMeasurable (fun x => Space.coordCLM i x))
  · simp [norm_smul]
    exact mul_le_mul_of_nonneg_right (abs_eval_le_norm x i) (by positivity)

@[fun_prop]
lemma component_mul_isDistBounded {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) (i : Fin d) :
    IsDistBounded (fun x => x i * f x) := hf.component_smul_isDistBounded i

@[fun_prop]
lemma isDistBounded_smul_self {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) : IsDistBounded (fun x => f x • x) := by
  refine IsDistBounded.congr (f := fun x => ‖x‖ * f x) (by fun_prop)
    (AEStronglyMeasurable.smul (f := f) (g := fun x => x) (by fun_prop) (by fun_prop)) fun x => ?_
  simp [norm_smul, mul_comm]

@[fun_prop]
lemma isDistBounded_smul_self_repr {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) : IsDistBounded (fun x => f x • basis.repr x) := by
  refine IsDistBounded.congr (f := fun x => ‖x‖ * f x) (by fun_prop)
    (AEStronglyMeasurable.smul (f := f) (g := fun x => basis.repr x) (by fun_prop) (by fun_prop))
      fun x => ?_
  simp [norm_smul, mul_comm]

@[fun_prop]
lemma isDistBounded_smul_inner {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded f) (y : Space d) : IsDistBounded (fun x => ⟪y, x⟫_ℝ • f x) := by
  have h1 (x : Space d) : ⟪y, x⟫_ℝ • f x = ∑ i, (y i * x i) • f x := by
    rw [inner_eq_sum, ← Finset.sum_smul]
  simp only [h1, ← smul_smul]
  exact sum_fun fun i _ => const_fun_smul (by fun_prop) (y i)

lemma isDistBounded_smul_inner_of_smul_norm {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded (fun x => ‖x‖ • f x)) (hae : AEStronglyMeasurable f) (y : Space d) :
    IsDistBounded (fun x => ⟪y, x⟫_ℝ • f x) := by
  have h1 (x : Space d) : ⟪y, x⟫_ℝ • f x = ∑ i, (y i * x i) • f x := by
    rw [inner_eq_sum, ← Finset.sum_smul]
  simp only [h1, ← smul_smul]
  refine sum_fun fun i _ => const_fun_smul (hf.mono (by fun_prop) fun x => ?_) (y i)
  simp [norm_smul]
  exact mul_le_mul_of_nonneg_right (abs_eval_le_norm x i) (by positivity)

@[fun_prop]
lemma isDistBounded_mul_inner {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) (y : Space d) : IsDistBounded (fun x => ⟪y, x⟫_ℝ * f x) :=
  hf.isDistBounded_smul_inner y

lemma isDistBounded_mul_inner' {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) (y : Space d) : IsDistBounded (fun x => ⟪x, y⟫_ℝ * f x) := by
  simpa only [smul_eq_mul, real_inner_comm y] using hf.isDistBounded_smul_inner y

lemma isDistBounded_mul_inner_of_smul_norm {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded (fun x => ‖x‖ * f x)) (hae : AEStronglyMeasurable f) (y : Space d) :
    IsDistBounded (fun x => ⟪y, x⟫_ℝ * f x) := hf.isDistBounded_smul_inner_of_smul_norm hae y

@[fun_prop]
lemma mul_inner_pow_neg_two {d : ℕ} (y : Space d) (hd : 2 ≤ d := by omega) :
    IsDistBounded (fun x => ⟪y, x⟫_ℝ * ‖x‖ ^ (- 2 : ℤ)) := by
  refine IsDistBounded.mono (f := fun x => (‖y‖ * ‖x‖) * ‖x‖ ^ (- 2 : ℤ)) ?_
    (AEMeasurable.aestronglyMeasurable (by fun_prop)) fun x => ?_
  · simp only [mul_assoc]
    refine IsDistBounded.const_mul_fun (IsDistBounded.congr (f := fun x => ‖x‖ ^ (- 1 : ℤ))
      (IsDistBounded.pow (d := d) (-1) (by omega))
      (AEMeasurable.aestronglyMeasurable (by fun_prop)) fun x => ?_) ‖y‖
    simp only [norm_mul, norm_norm, norm_inv, norm_zpow, Int.reduceNeg, zpow_neg, zpow_one]
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · field_simp [norm_ne_zero_iff.mpr hx]
  · simp
    exact mul_le_mul_of_nonneg (abs_real_inner_le_norm y x) (by rfl) (by positivity) (by positivity)

end constructors
end IsDistBounded
