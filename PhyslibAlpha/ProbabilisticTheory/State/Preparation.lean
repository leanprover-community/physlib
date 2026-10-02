/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Measurement.Postprocessing
public import PhyslibAlpha.ProbabilisticTheory.State.Metric
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Preparation procedures

## i. Overview

A preparation procedure rolls a die and, depending on the outcome `x`, prepares the state
`prepare x`. The die is any classical random variable, with law `law`. Whoever does not see the roll
is left with the average of the prepared states: the state the procedure prepares.

A measurement `M` performed after the procedure has an outcome whose law depends on the roll. Roll
and outcome together are a pair of random variables. Their joint law is the law of the roll combined
with the outcome law given the roll. Forgetting the roll, the outcome has the Born law of the
prepared state.

## ii. Key results

- `Preparation E X` : a preparation procedure with a die taking values in `X`.
- `Preparation.state` : the state a procedure prepares.
- `Preparation.state_isNormal` : a prepared state is normal.
- `Preparation.ofMix` : preparing one of two states at random.
- `Preparation.conditionalState` : the state prepared given that the roll lies in an event.
- `Preparation.outcome` : the outcome law of a measurement given the roll.
- `Preparation.outcome_comp_law` : forgetting the roll, the outcome has the Born law of the
  prepared state.
- `UnitalPositiveLinearMap.IsNormal.of_mix_left` : the components of a normal mixture are normal.

## iii. Table of contents

- A. Normal components of mixtures
- B. Preparation procedures
- C. Preparing one of two states
- D. Conditional states
- E. Measurement outcomes

-/

@[expose] public section

namespace ProbabilisticTheory

open MeasureTheory ProbabilityTheory Filter Topology

universe u v w

variable {E : Type u} {X : Type v} {Ω : Type w} [OrderUnitSpace E]
  [MeasurableSpace X] [MeasurableSpace Ω]

namespace UnitalPositiveLinearMap

/-! ## A. Normal components of mixtures -/

/-- A state dominated by a positive multiple of a normal state is normal. -/
lemma IsNormal.of_smul_le {ω φ : 𝓢[ℝ, E]} (hω : ω.IsNormal) {c : ℝ} (hc : 0 < c)
    (h : ∀ A, 0 ≤ A → c * φ A ≤ ω A) : φ.IsNormal := by
  intro f A hf hA
  have hle (n : ℕ) : f n ≤ A := hA.1 ⟨n, rfl⟩
  have hω' : Tendsto (fun n => ω (f n)) atTop (𝓝 (ω A)) :=
    tendsto_atTop_isLUB (ω.toPositiveLinearMap.monotone'.comp hf) (hω f A hf hA)
  have hbound : Tendsto (fun n => c⁻¹ * (ω A - ω (f n))) atTop (𝓝 0) := by
    simpa using (hω'.const_sub (ω A)).const_mul c⁻¹
  have hgap : Tendsto (fun n => φ A - φ (f n)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => sub_nonneg.2 (φ.toPositiveLinearMap.monotone' (hle n)))
      (fun n => ?_) hbound
    rw [le_inv_mul_iff₀ hc, ← map_sub, ← map_sub]
    exact h _ (sub_nonneg.2 (hle n))
  have hφ : Tendsto (fun n => φ (f n)) atTop (𝓝 (φ A)) := by
    simpa using hgap.const_sub (φ A)
  exact isLUB_of_tendsto_atTop (φ.toPositiveLinearMap.monotone'.comp hf) hφ

/-- If a proper mixture is normal, so is its first component. -/
lemma IsNormal.of_mix_left {φ ψ : 𝓢[ℝ, E]} {t : unitInterval} (h : (mix φ ψ t).IsNormal)
    (ht : t ≠ 0) : φ.IsNormal :=
  h.of_smul_le (unitInterval.pos_iff_ne_zero.2 ht) fun _ hA =>
    le_add_of_nonneg_right (mul_nonneg (sub_nonneg.2 t.2.2) (map_nonneg ψ hA))

/-- If a proper mixture is normal, so is its second component. -/
lemma IsNormal.of_mix_right {φ ψ : 𝓢[ℝ, E]} {t : unitInterval} (h : (mix φ ψ t).IsNormal)
    (ht : t ≠ 1) : ψ.IsNormal :=
  h.of_smul_le (sub_pos.2 (unitInterval.lt_one_iff_ne_one.2 ht)) fun _ hA =>
    le_add_of_nonneg_left (mul_nonneg t.2.1 (map_nonneg φ hA))

end UnitalPositiveLinearMap

/-! ## B. Preparation procedures -/

/-- A preparation procedure: roll a die with values in `X` and law `law`, and on the roll `x`
prepare the normal state `prepare x`. -/
structure Preparation (E : Type u) [OrderUnitSpace E] (X : Type v) [MeasurableSpace X] where
  /-- The law of the die. -/
  law : ProbabilityMeasure X
  /-- The state prepared on each roll. -/
  prepare : X → 𝓢[ℝ, E]
  /-- The state prepared on each roll is normal. -/
  normal : ∀ x, (prepare x).IsNormal
  /-- Every expectation value depends measurably on the roll. -/
  measurable_prepare : ∀ A : E, Measurable fun x => prepare x A

namespace Preparation

open UnitalPositiveLinearMap

/-- Every expectation value is integrable in the roll. -/
lemma integrable_prepare (p : Preparation E X) (A : E) :
    Integrable (fun x => p.prepare x A) (p.law : Measure X) := by
  obtain ⟨n, hlo, hhi⟩ := OrderUnitSpace.exists_two_sided_bound A
  refine .of_bound (p.measurable_prepare A).aestronglyMeasurable n (.of_forall fun x => ?_)
  have h₁ := map_nonneg (p.prepare x) (sub_nonneg.2 hlo)
  have h₂ := map_nonneg (p.prepare x) (sub_nonneg.2 hhi)
  simp only [map_sub, map_neg, map_nsmul, map_one, nsmul_eq_mul, mul_one] at h₁ h₂
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- The state a procedure prepares, once the roll is forgotten: the average of the prepared
states. -/
noncomputable def state (p : Preparation E X) : 𝓢[ℝ, E] :=
  ofLinearMap
    { toFun A := ∫ x, p.prepare x A ∂(p.law : Measure X)
      map_add' A B := by
        simp only [map_add]
        exact integral_add (p.integrable_prepare A) (p.integrable_prepare B)
      map_smul' c A := by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
    (fun _ hA => integral_nonneg fun x => map_nonneg (p.prepare x) hA)
    (by simp)

lemma state_apply (p : Preparation E X) (A : E) :
    p.state A = ∫ x, p.prepare x A ∂(p.law : Measure X) :=
  rfl

/-- A prepared state is normal. -/
lemma state_isNormal (p : Preparation E X) : p.state.IsNormal := by
  intro f A hf hA
  have hω : Tendsto (fun n => p.state (f n)) atTop (𝓝 (p.state A)) :=
    integral_tendsto_of_tendsto_of_monotone (fun n => p.integrable_prepare (f n))
      (p.integrable_prepare A)
      (.of_forall fun x => (p.prepare x).toPositiveLinearMap.monotone'.comp hf)
      (.of_forall fun x => tendsto_atTop_isLUB
        ((p.prepare x).toPositiveLinearMap.monotone'.comp hf) (p.normal x f A hf hA))
  exact isLUB_of_tendsto_atTop (p.state.toPositiveLinearMap.monotone'.comp hf) hω

/-! ## C. Preparing one of two states -/

/-- Prepare `φ` with probability `t` and `ψ` otherwise. -/
noncomputable def ofMix (φ ψ : 𝓢[ℝ, E]) (t : unitInterval) (hφ : φ.IsNormal)
    (hψ : ψ.IsNormal) : Preparation E Bool where
  law := ⟨ENNReal.ofReal t • .dirac true + ENNReal.ofReal (1 - t) • .dirac false,
    ⟨by simp [← ENNReal.ofReal_add t.2.1 (sub_nonneg.2 t.2.2)]⟩⟩
  prepare b := cond b φ ψ
  normal := Bool.forall_bool.2 ⟨hψ, hφ⟩
  measurable_prepare _ := .of_discrete

/-- Preparing one of two states at random prepares their mixture. -/
lemma state_ofMix (φ ψ : 𝓢[ℝ, E]) (t : unitInterval) (hφ : φ.IsNormal) (hψ : ψ.IsNormal) :
    (ofMix φ ψ t hφ hψ).state = mix φ ψ t := by
  refine ext fun A => ?_
  change ∫ b, cond b φ ψ A ∂(ENNReal.ofReal t • Measure.dirac true +
    ENNReal.ofReal (1 - t) • Measure.dirac false) = _
  rw [integral_add_measure (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top)
    (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac, ENNReal.toReal_ofReal t.2.1,
    ENNReal.toReal_ofReal (sub_nonneg.2 t.2.2)]
  rfl

/-- When both states have positive probability, a property holds almost surely exactly when it
holds for both rolls. -/
lemma ae_ofMix_iff {φ ψ : 𝓢[ℝ, E]} {t : unitInterval} {hφ : φ.IsNormal} {hψ : ψ.IsNormal}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) {P : Bool → Prop} :
    (∀ᵐ b ∂((ofMix φ ψ t hφ hψ).law : Measure Bool), P b) ↔ P true ∧ P false := by
  change (∀ᵐ b ∂(ENNReal.ofReal t • Measure.dirac true +
    ENNReal.ofReal (1 - t) • Measure.dirac false), P b) ↔ _
  rw [ae_add_measure_iff,
    Measure.ae_ennreal_smul_measure_iff
      (ENNReal.ofReal_pos.2 (unitInterval.pos_iff_ne_zero.2 ht0)).ne',
    Measure.ae_ennreal_smul_measure_iff
      (ENNReal.ofReal_pos.2 (sub_pos.2 (show (t : ℝ) < 1 from
        unitInterval.lt_one_iff_ne_one.2 ht1))).ne',
    ae_dirac_iff .of_discrete, ae_dirac_iff .of_discrete]

/-! ## D. Conditional states -/

/-- The state prepared given that the roll lies in an event of positive probability. -/
noncomputable def conditionalState (p : Preparation E X) (s : Set X)
    (hpos : 0 < (p.law : Measure X).real s) : 𝓢[ℝ, E] :=
  ofLinearMap
    { toFun A := ((p.law : Measure X).real s)⁻¹ * ∫ x in s, p.prepare x A ∂(p.law : Measure X)
      map_add' A B := by
        simp only [map_add]
        rw [integral_add (p.integrable_prepare A).integrableOn
          (p.integrable_prepare B).integrableOn]
        ring
      map_smul' c A := by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply, integral_const_mul]
        ring }
    (fun _ hA => mul_nonneg (inv_nonneg.2 hpos.le)
      (integral_nonneg fun x => map_nonneg (p.prepare x) hA))
    (by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, map_one, setIntegral_const, smul_eq_mul,
        mul_one]
      exact inv_mul_cancel₀ hpos.ne')

@[simp]
lemma conditionalState_apply (p : Preparation E X) (s : Set X)
    (hpos : 0 < (p.law : Measure X).real s) (A : E) :
    p.conditionalState s hpos A =
      ((p.law : Measure X).real s)⁻¹ * ∫ x in s, p.prepare x A ∂(p.law : Measure X) :=
  rfl

/-- The prepared state is the mixture of the states conditioned on an event and on its complement,
weighted by their probabilities. -/
lemma mix_conditionalState_compl (p : Preparation E X) {s : Set X} (hs : MeasurableSet s)
    (hpos : 0 < (p.law : Measure X).real s) (hposc : 0 < (p.law : Measure X).real sᶜ) :
    mix (p.conditionalState s hpos) (p.conditionalState sᶜ hposc)
      ⟨(p.law : Measure X).real s, measureReal_nonneg, measureReal_le_one⟩ = p.state := by
  refine ext fun A => ?_
  have hq : 1 - (p.law : Measure X).real s = (p.law : Measure X).real sᶜ := by
    rw [← probReal_add_probReal_compl (μ := (p.law : Measure X)) hs]; ring
  simp only [mix_apply, conditionalState_apply, hq, mul_inv_cancel_left₀ hpos.ne',
    mul_inv_cancel_left₀ hposc.ne', integral_add_compl hs (p.integrable_prepare A), state_apply]

/-! ## E. Measurement outcomes -/

/-- The outcome law of the measurement `M` given the roll. -/
noncomputable def outcome (p : Preparation E X) (M : Measurement Ω E) : Kernel X Ω where
  toFun x := M.probabilityLaw (p.prepare x) (p.normal x)
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs => by
    simp only [Measurement.probabilityLaw_apply M _ _ s hs]
    exact ENNReal.measurable_ofReal.comp (p.measurable_prepare (M s hs))

lemma outcome_apply (p : Preparation E X) (M : Measurement Ω E) (x : X) :
    p.outcome M x = M.probabilityLaw (p.prepare x) (p.normal x) :=
  rfl

instance (p : Preparation E X) (M : Measurement Ω E) : IsMarkovKernel (p.outcome M) :=
  ⟨fun x => by rw [outcome_apply]; infer_instance⟩

/-- Forgetting the roll, the outcome of `M` has the Born law of the prepared state. -/
lemma outcome_comp_law (p : Preparation E X) (M : Measurement Ω E) :
    p.outcome M ∘ₘ (p.law : Measure X) = M.probabilityLaw p.state p.state_isNormal := by
  ext s hs
  rw [Measure.bind_apply hs (p.outcome M).aemeasurable,
    Measurement.probabilityLaw_apply _ _ _ s hs, state_apply,
    ofReal_integral_eq_lintegral_ofReal (p.integrable_prepare _)
      (.of_forall fun x => map_nonneg _ (M s hs).2.1)]
  simp only [outcome_apply, Measurement.probabilityLaw_apply _ _ _ s hs]

/-- The outcome law of `M` when the roll is forgotten: the Born law of the prepared state, whatever
the roll. -/
noncomputable def forgetfulOutcome (p : Preparation E X) (M : Measurement Ω E) :
    Kernel X Ω :=
  Kernel.const X (M.probabilityLaw p.state p.state_isNormal)

instance (p : Preparation E X) (M : Measurement Ω E) :
    IsMarkovKernel (p.forgetfulOutcome M) := by
  unfold forgetfulOutcome; infer_instance

/-- Forgetting the roll is a post-processing of the outcome law given the roll. -/
lemma forgetfulOutcome_isPostprocessing (p : Preparation E X) (M : Measurement Ω E) :
    Kernel.FactorsThrough (p.forgetfulOutcome M) (p.outcome M) :=
  Kernel.const_factorsThrough _ _

end Preparation

end ProbabilisticTheory
