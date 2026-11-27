/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Classical.NormalState

/-!
# Pure classical states

The pure normal states of a classical system are its configurations.

## i. Overview

Conditioning a probability distribution on an event `s` and on its complement splits its state
into a mixture of two states with weight `μ s`. In a pure state both parts equal the state
itself. Conditioning on `s` then leaves the distribution unchanged, which forces `μ s` to be `0`
or `1`. The distribution of a pure normal state therefore only takes the values `0` and `1`.

On a standard Borel configuration space such a distribution sits at a single configuration. Every
pure normal state is then a Dirac state. Different configurations give different Dirac
states. The configurations of the system are exactly its pure normal states.

## ii. Key results

- `ProbabilisticTheory.Classical.isZeroOneMeasure_of_isPure` : the distribution of a pure normal
  state only takes the values `0` and `1`.
- `ProbabilisticTheory.Classical.configurationEquiv` : on a standard Borel space the configurations
  are the pure normal states.

## iii. Table of contents

- A. Conditioning on events
- B. Configurations are the pure normal states

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory.Classical

open MeasureTheory ProbabilityTheory

variable {X : Type*} [MeasurableSpace X]

/-! ## A. Conditioning on events -/

/-- Conditioning the distribution of a pure state on an event of probability strictly between
`0` and `1` leaves it unchanged. Conditioning on the event and on its complement splits the
state into a mixture with weight the probability of the event. -/
lemma cond_eq_of_isPure (μ : Measure X) [IsProbabilityMeasure μ] (h : (ofDistribution μ).IsPure)
    {s : Set X} (hs : MeasurableSet s) (h0 : μ s ≠ 0) (h1 : μ sᶜ ≠ 0) : μ[|s] = μ := by
  have := cond_isProbabilityMeasure h0
  have := cond_isProbabilityMeasure h1
  have hmix : State.mix (ofDistribution μ[|s]) (ofDistribution μ[|sᶜ])
      ⟨μ.real s, measureReal_nonneg, measureReal_le_one⟩ = ofDistribution μ := by
    refine Channel.ext fun f ↦ ?_
    change μ.real s * ∫ x, f x ∂μ[|s] + (1 - μ.real s) * ∫ x, f x ∂μ[|sᶜ] = ∫ x, f x ∂μ
    simp only [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
      ← measureReal_def, ← probReal_compl_eq_one_sub hs]
    rw [mul_inv_cancel_left₀ ((measureReal_ne_zero_iff).mpr h0),
      mul_inv_cancel_left₀ ((measureReal_ne_zero_iff).mpr h1),
      integral_add_compl hs (integrable f _)]
  exact ofDistribution_injective _ (State.isPure_iff_forall_mix_eq.mp h _ _ _
    (ENNReal.toReal_pos h0 (measure_ne_top _ _)) (show μ.real s < 1 from sub_pos.mp <|
      probReal_compl_eq_one_sub hs (μ := μ) ▸ ENNReal.toReal_pos h1 (measure_ne_top _ _)) hmix).1

/-- The distribution of a pure state only takes the values `0` and `1`. -/
lemma isZeroOneMeasure_of_isPure (μ : Measure X) [IsProbabilityMeasure μ]
    (h : (ofDistribution μ).IsPure) : IsZeroOneMeasure μ where
  zero_one₀ s hs := by
    by_contra! hne
    have h1 : μ sᶜ ≠ 0 := by
      rw [prob_compl_eq_one_sub hs]
      exact (tsub_pos_of_lt (lt_of_le_of_ne prob_le_one hne.2)).ne'
    have := congrArg (· s) (cond_eq_of_isPure μ h hs hne.1 h1)
    exact hne.2 (by simpa [cond_apply_self, hne.1] using this.symm)

/-! ## B. Configurations are the pure normal states -/

/-- On a standard Borel space every pure normal state is a Dirac state. -/
lemma exists_dirac_eq_of_isPure [StandardBorelSpace X] {ω : State (measurable X)}
    (hω : ω.IsNormal) (h : ω.IsPure) : ∃ x, dirac _ x = ω := by
  have := isZeroOneMeasure_of_isPure _ (by rwa [ofDistribution_distribution ω hω])
  obtain ⟨x, hx⟩ := IsZeroOneMeasure.exists_eq_dirac (μ := distribution ω hω)
  refine ⟨x, ext_of_isNormal (isNormal_dirac x) hω fun s ↦ ?_⟩
  rw [← measureReal_distribution ω hω s, hx, ← ofDistribution_indicator,
    ofDistribution_dirac]

/-- On a standard Borel configuration space the configurations of a classical system are its
pure normal states. -/
noncomputable def configurationEquiv [StandardBorelSpace X] :
    X ≃ {ω : State (measurable X) // ω.IsNormal ∧ ω.IsPure} where
  toFun x := ⟨dirac _ x, isNormal_dirac x, isPure_dirac x⟩
  invFun ω := (exists_dirac_eq_of_isPure ω.2.1 ω.2.2).choose
  left_inv x :=
    dirac_injective (exists_dirac_eq_of_isPure (isNormal_dirac x) (isPure_dirac x)).choose_spec
  right_inv ω := Subtype.ext (exists_dirac_eq_of_isPure ω.2.1 ω.2.2).choose_spec

end ProbabilisticTheory.Classical
