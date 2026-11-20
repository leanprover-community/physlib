/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ClassicalMechanics.Observables.NormalState
public import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
public import Mathlib.Probability.ConditionalProbability

/-!
# Pure classical states

The pure normal states of a classical system are its configurations.

## i. Overview

Conditioning a probability distribution on an event `s` and on its complement splits its state
into a mixture of two states with weight `μ s`. In a pure state both parts equal the state
itself. Conditioning on `s` then leaves the distribution unchanged, which forces `μ s` to be `0`
or `1`. The distribution of a pure normal state therefore only takes the values `0` and `1`.

On a standard Borel configuration space such a distribution sits at a single configuration. Every
pure normal state is then a Dirac state, and different configurations give different Dirac
states. The configurations of the system are exactly its pure normal states.

## ii. Key results

- `ProbabilisticTheory.Classical.isZeroOneMeasure_of_isPure` : the distribution of a pure normal
  state only takes the values `0` and `1`.
- `ProbabilisticTheory.Classical.pureStateEquiv` : on a standard Borel space the configurations
  are the pure normal states.

## iii. Table of contents

- A. Conditioning on events
- B. Configurations are the pure normal states

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory.Classical

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## A. Conditioning on events -/

/-- Conditioning on an event and on its complement splits the state of a distribution into a
mixture with weight the probability of the event. -/
lemma mix_ofMeasure_cond (μ : ProbabilityMeasure Ω) {s : Set Ω} (hs : MeasurableSet s)
    (h0 : (μ : Measure Ω) s ≠ 0) (h1 : (μ : Measure Ω) sᶜ ≠ 0) :
    State.mix (ofMeasure ⟨_, cond_isProbabilityMeasure h0⟩)
      (ofMeasure ⟨_, cond_isProbabilityMeasure h1⟩)
      ⟨(μ : Measure Ω).real s, measureReal_nonneg, measureReal_le_one⟩ = ofMeasure μ := by
  refine Channel.ext fun f ↦ ?_
  change (μ : Measure Ω).real s * ∫ x, toFun f x ∂(μ : Measure Ω)[|s] +
    (1 - (μ : Measure Ω).real s) * ∫ x, toFun f x ∂(μ : Measure Ω)[|sᶜ] = ∫ x, toFun f x ∂μ
  simp only [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
    ← measureReal_def, ← probReal_compl_eq_one_sub hs]
  rw [mul_inv_cancel_left₀ ((measureReal_ne_zero_iff).mpr h0),
    mul_inv_cancel_left₀ ((measureReal_ne_zero_iff).mpr h1),
    integral_add_compl hs (integrable_toFun f _)]

/-- Conditioning the distribution of a pure state on an event of probability strictly between
`0` and `1` leaves it unchanged. -/
lemma cond_eq_of_isPure (μ : ProbabilityMeasure Ω) (h : (ofMeasure μ).IsPure) {s : Set Ω}
    (hs : MeasurableSet s) (h0 : (μ : Measure Ω) s ≠ 0) (h1 : (μ : Measure Ω) sᶜ ≠ 0) :
    (μ : Measure Ω)[|s] = μ :=
  congrArg Subtype.val <| normalStateEquiv.symm.injective <| Subtype.ext <|
    (State.isPure_iff_forall_mix_eq.mp h _ _ _ (ENNReal.toReal_pos h0 (measure_ne_top _ _))
      (show (μ : Measure Ω).real s < 1 from sub_pos.mp <| probReal_compl_eq_one_sub hs (μ := μ) ▸
        ENNReal.toReal_pos h1 (measure_ne_top _ _)) (mix_ofMeasure_cond μ hs h0 h1)).1

/-- The distribution of a pure state only takes the values `0` and `1`. -/
lemma isZeroOneMeasure_of_isPure (μ : ProbabilityMeasure Ω) (h : (ofMeasure μ).IsPure) :
    IsZeroOneMeasure (μ : Measure Ω) where
  zero_one₀ s hs := by
    by_contra! hne
    have h1 : (μ : Measure Ω) sᶜ ≠ 0 := by
      rw [prob_compl_eq_one_sub hs]
      exact (tsub_pos_of_lt (lt_of_le_of_ne prob_le_one hne.2)).ne'
    have := congrArg (· s) (cond_eq_of_isPure μ h hs hne.1 h1)
    exact hne.2 (by simpa [cond_apply_self, hne.1] using this.symm)

/-! ## B. Configurations are the pure normal states -/

/-- On a standard Borel space every pure normal state is a Dirac state. -/
lemma exists_dirac_eq_of_isPure [StandardBorelSpace Ω] {ω : ClassicalState Ω}
    (hω : ω.IsNormal) (h : ω.IsPure) : ∃ x, dirac x = ω := by
  obtain ⟨μ, rfl⟩ : ∃ μ, ofMeasure μ = ω := ⟨_, congrArg Subtype.val
    (normalStateEquiv.symm_apply_apply ⟨ω, hω⟩)⟩
  have := isZeroOneMeasure_of_isPure μ h
  obtain ⟨x, hx⟩ := IsZeroOneMeasure.exists_eq_dirac (μ := (μ : Measure Ω))
  exact ⟨x, (ofMeasure_dirac x).symm.trans
    (congrArg ofMeasure (ProbabilityMeasure.toMeasure_injective hx.symm))⟩

/-- On a standard Borel configuration space the configurations of a classical system are its
pure normal states. -/
noncomputable def pureStateEquiv [StandardBorelSpace Ω] :
    Ω ≃ {ω : ClassicalState Ω // ω.IsNormal ∧ ω.IsPure} where
  toFun x := ⟨dirac x, isNormal_dirac x, isPure_dirac x⟩
  invFun ω := (exists_dirac_eq_of_isPure ω.2.1 ω.2.2).choose
  left_inv x :=
    dirac_injective (exists_dirac_eq_of_isPure (isNormal_dirac x) (isPure_dirac x)).choose_spec
  right_inv ω := Subtype.ext (exists_dirac_eq_of_isPure ω.2.1 ω.2.2).choose_spec

end ProbabilisticTheory.Classical
