/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Measurement.Binary
public import PhyslibAlpha.Mathematics.Probability.Kernel.Factorization
public import PhyslibAlpha.ProbabilisticTheory.State.Preparation
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Purity is the absence of side information

A normal state is pure exactly when no preparation of it carries side information.

## i. Overview

Roll a die and, depending on the roll, prepare a state; then perform a measurement. Someone who is
only told the prepared state predicts the outcome with its Born law. Someone who is also told how
the state was prepared, and sees the roll, may predict better: the roll is side information. It is
useless exactly when the roll and the outcome are independent random variables.

**A state is pure exactly when it has no side information:** however it is prepared, the roll and
the outcome of any yes/no measurement are independent. Being handed the state is as good as being
handed the state together with the procedure that prepared it. Conversely, every mixed state can be
prepared by choosing between two states in such a way that some yes/no measurement detects the
choice. For a pure state, the roll is also independent of the outcome of any measurement with a
countably generated outcome space.

Behind this lies a sharper statement: a state is pure exactly when every preparation of it is
trivial, with every expectation value almost surely independent of the roll.

## ii. Key results

- `Preparation.NoSideInfo` : the roll and the outcome of a measurement are independent.
- `UnitalPositiveLinearMap.HasNoSideInfo` : however the state is prepared, the roll and the outcome
  of any yes/no measurement are independent.
- `UnitalPositiveLinearMap.isPure_iff_hasNoSideInfo` : a normal state is pure exactly when it has
  no side information.
- `UnitalPositiveLinearMap.isMixed_iff_exists_sideInfo` : a normal state is mixed exactly when it
  can be prepared from two states so that some yes/no measurement detects the choice.
- `Preparation.noSideInfo_of_isPure` : preparing a pure state, the roll is independent of the
  outcome of every measurement with a countably generated outcome space.
- `Preparation.noSideInfo_iff_postprocessEquivAE` : no side information means that the outcome law
  given the roll is no more informative than the outcome law ignoring it.

## iii. Table of contents

- A. Trivial preparations
- B. Preparations of pure states
- C. Pure states from trivial preparations
- D. Side information
- E. Purity is the absence of side information

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

open MeasureTheory ProbabilityTheory UnitalPositiveLinearMap

universe u v w

variable {E : Type u} {X : Type v} {Ω : Type w} [ArchimedeanOrderUnitSpace E]
  [MeasurableSpace X] [MeasurableSpace Ω]

namespace Preparation

/-! ## A. Trivial preparations -/

/-- A preparation is trivial when, for every observable, almost every roll prepares a state with
the same expectation value as the prepared state. -/
def IsTrivial (p : Preparation E X) : Prop :=
  ∀ A : E, ∀ᵐ x ∂(p.law : Measure X), p.prepare x A = p.state A

/-- A preparation is trivial as soon as it is trivial on effects. -/
lemma isTrivial_of_effect (p : Preparation E X)
    (h : ∀ e : Effect E, ∀ᵐ x ∂(p.law : Measure X), p.prepare x e = p.state e) :
    p.IsTrivial := by
  intro A
  obtain ⟨n, hlo, -⟩ := OrderUnitSpace.exists_two_sided_bound A
  obtain ⟨c, hc, he⟩ := Effect.exists_pos_smul_mem (neg_le_iff_add_nonneg.1 hlo)
  filter_upwards [h ⟨_, he⟩] with x hx
  simpa [hc.ne'] using hx

/-! ## B. Preparations of pure states -/

/-- Conditioning a preparation of a pure state on an event whose probability is neither `0` nor `1`
gives back the pure state. -/
lemma conditionalState_eq_of_isPure (p : Preparation E X) (hω : p.state.IsPure) {s : Set X}
    (hs : MeasurableSet s) (hpos : 0 < (p.law : Measure X).real s)
    (hposc : 0 < (p.law : Measure X).real sᶜ) : p.conditionalState s hpos = p.state := by
  have ht1 : (p.law : Measure X).real s ≠ 1 := by
    linarith [probReal_add_probReal_compl (μ := (p.law : Measure X)) hs]
  exact (hω.eq_of_mix _ (fun h => hpos.ne' (congrArg Subtype.val h))
    (fun h => ht1 (congrArg Subtype.val h)) (p.mix_conditionalState_compl hs hpos hposc)).1

/-- Preparing a pure state, the expectation value restricted to any event of rolls is the
probability of the event times the expectation value. -/
lemma setIntegral_prepare_of_isPure (p : Preparation E X) (hω : p.state.IsPure) {s : Set X}
    (hs : MeasurableSet s) (A : E) :
    ∫ x in s, p.prepare x A ∂(p.law : Measure X) = (p.law : Measure X).real s * p.state A := by
  have hnull {t : Set X} (h : 0 = (p.law : Measure X).real t) :
      ∫ x in t, p.prepare x A ∂(p.law : Measure X) = 0 :=
    setIntegral_measure_zero _ ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 h.symm)
  have hsum := integral_add_compl hs (p.integrable_prepare A)
  have hq := probReal_add_probReal_compl (μ := (p.law : Measure X)) hs
  rw [← state_apply] at hsum
  rcases (measureReal_nonneg (s := s)).eq_or_lt with h0 | hpos
  · rw [hnull h0, ← h0, zero_mul]
  rcases (measureReal_nonneg (s := sᶜ)).eq_or_lt with h0 | hposc
  · rw [hnull h0, add_zero] at hsum
    rw [hsum, show (p.law : Measure X).real s = 1 by linarith, one_mul]
  have h := congrArg (· A) (p.conditionalState_eq_of_isPure hω hs hpos hposc)
  simp only [conditionalState_apply] at h
  rw [← h, mul_inv_cancel_left₀ hpos.ne']

/-- Every preparation of a pure state is trivial. -/
lemma isTrivial_of_isPure (p : Preparation E X) (hω : p.state.IsPure) : p.IsTrivial := fun A =>
  Integrable.ae_eq_of_forall_setIntegral_eq _ _ (p.integrable_prepare A) (integrable_const _)
    fun s hs _ => by rw [p.setIntegral_prepare_of_isPure hω hs, setIntegral_const, smul_eq_mul]

end Preparation

/-! ## C. Pure states from trivial preparations -/

namespace UnitalPositiveLinearMap

variable {ω : 𝓢[ℝ, E]}

/-- A normal state all of whose preparations from two states are trivial is pure. -/
lemma isPure_of_isTrivial (hω : ω.IsNormal)
    (h : ∀ p : Preparation E Bool, p.state = ω → p.IsTrivial) : ω.IsPure := by
  refine isPure_iff_forall_mix_eq.2 fun φ ψ t ht0 ht1 hmix => ?_
  subst hmix
  let p := Preparation.ofMix φ ψ t (hω.of_mix_left ht0) (hω.of_mix_right ht1)
  have hp : p.state = mix φ ψ t := Preparation.state_ofMix ..
  have hA (A : E) := (Preparation.ae_ofMix_iff ht0 ht1).1 (h p hp A)
  exact ⟨ext fun A => (hA A).1.trans (by rw [hp]), ext fun A => (hA A).2.trans (by rw [hp])⟩

/-- A normal state is pure exactly when all its preparations are trivial. -/
lemma isPure_iff_forall_isTrivial (hω : ω.IsNormal) :
    ω.IsPure ↔ ∀ (X : Type) [MeasurableSpace X] (p : Preparation E X), p.state = ω →
      p.IsTrivial :=
  ⟨fun h _ _ p hp => p.isTrivial_of_isPure (hp ▸ h),
    fun h => isPure_of_isTrivial hω (h Bool)⟩

end UnitalPositiveLinearMap

namespace Preparation

/-! ## D. Side information -/

/-- The roll carries no side information about the measurement `M`: the roll and the outcome of `M`
are independent random variables. -/
def NoSideInfo (p : Preparation E X) (M : Measurement Ω E) : Prop :=
  IndepFun Prod.fst Prod.snd ((p.law : Measure X) ⊗ₘ p.outcome M)

/-- The roll carries no side information about `M` exactly when the joint law of roll and outcome
is the one obtained by ignoring the roll. -/
lemma noSideInfo_iff_compProd_eq (p : Preparation E X) (M : Measurement Ω E) :
    p.NoSideInfo M ↔
      (p.law : Measure X) ⊗ₘ p.outcome M = (p.law : Measure X) ⊗ₘ p.forgetfulOutcome M := by
  rw [NoSideInfo, indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
    measurable_snd.aemeasurable, forgetfulOutcome, Measure.compProd_const]
  change _ = (Measure.fst _).prod (Measure.snd _) ↔ _
  rw [Measure.fst_compProd, Measure.snd_compProd, outcome_comp_law]
  simp

/-- If the outcome law given the roll almost surely ignores the roll, the roll carries no side
information. -/
lemma noSideInfo_of_ae_eq (p : Preparation E X) {M : Measurement Ω E}
    (h : p.outcome M =ᵐ[(p.law : Measure X)] p.forgetfulOutcome M) : p.NoSideInfo M :=
  (p.noSideInfo_iff_compProd_eq M).2 (Measure.compProd_congr h)

/-- With a countably generated outcome space, the roll carries no side information exactly when the
outcome law given the roll almost surely ignores the roll. -/
lemma noSideInfo_iff_ae_eq [MeasurableSpace.CountablyGenerated Ω] (p : Preparation E X)
    (M : Measurement Ω E) :
    p.NoSideInfo M ↔ p.outcome M =ᵐ[(p.law : Measure X)] p.forgetfulOutcome M :=
  ⟨fun h => Kernel.ae_eq_of_compProd_eq ((p.noSideInfo_iff_compProd_eq M).1 h),
    p.noSideInfo_of_ae_eq⟩

/-- With a countably generated outcome space, the roll carries no side information exactly when the
outcome law given the roll is no more informative than the outcome law ignoring it. -/
lemma noSideInfo_iff_postprocessEquivAE [MeasurableSpace.CountablyGenerated Ω]
    (p : Preparation E X) (M : Measurement Ω E) :
    p.NoSideInfo M ↔
      Kernel.MutuallyFactorAE (p.law : Measure X) (p.outcome M) (p.forgetfulOutcome M) := by
  refine ⟨fun h => Kernel.mutuallyFactorAE_of_ae_eq _ ((p.noSideInfo_iff_ae_eq M).1 h),
    fun ⟨⟨κ, _, hκ⟩, _⟩ => ?_⟩
  rw [NoSideInfo, Measure.compProd_congr hκ, forgetfulOutcome, Kernel.comp_const,
    Measure.compProd_const]
  exact indepFun_prod measurable_id measurable_id

/-- In a trivial preparation, the outcome law of a measurement with a countably generated outcome
space almost surely ignores the roll. -/
lemma IsTrivial.outcome_ae_eq [MeasurableSpace.CountablyGenerated Ω] {p : Preparation E X}
    (h : p.IsTrivial) (M : Measurement Ω E) :
    p.outcome M =ᵐ[(p.law : Measure X)] p.forgetfulOutcome M :=
  Kernel.ae_eq_of_forall_ae_apply_eq fun s hs => by
    filter_upwards [h (M s hs)] with x hx
    rw [outcome_apply, forgetfulOutcome, Kernel.const_apply,
      Measurement.probabilityLaw_apply _ _ _ s hs, Measurement.probabilityLaw_apply _ _ _ s hs, hx]

/-- If the roll carries no side information about the yes/no measurement of `e`, almost every roll
predicts the probability of `e` in the prepared state. -/
lemma ae_prepare_eq_of_noSideInfo (p : Preparation E X) (e : Effect E)
    (h : p.NoSideInfo (Effect.binaryMeasurement e)) :
    ∀ᵐ x ∂(p.law : Measure X), p.prepare x e = p.state e := by
  filter_upwards [(p.noSideInfo_iff_ae_eq _).1 h] with x hx
  have hx' := congrArg (· {true}) hx
  simp only [outcome_apply, forgetfulOutcome, Kernel.const_apply,
    Measurement.probabilityLaw_apply _ _ _ _ (.singleton true),
    Effect.binaryMeasurement_true] at hx'
  exact (ENNReal.ofReal_eq_ofReal_iff (map_nonneg _ e.2.1) (map_nonneg _ e.2.1)).1 hx'

/-- A preparation is trivial exactly when the roll carries no side information about any yes/no
measurement. -/
lemma isTrivial_iff_noSideInfo (p : Preparation E X) :
    p.IsTrivial ↔ ∀ e : Effect E, p.NoSideInfo (Effect.binaryMeasurement e) :=
  ⟨fun h _ => p.noSideInfo_of_ae_eq (h.outcome_ae_eq _),
    fun h => p.isTrivial_of_effect fun e => p.ae_prepare_eq_of_noSideInfo e (h e)⟩

/-- Preparing a pure state, the roll carries no side information about any measurement with a
countably generated outcome space. -/
lemma noSideInfo_of_isPure [MeasurableSpace.CountablyGenerated Ω] (p : Preparation E X)
    (hω : p.state.IsPure) (M : Measurement Ω E) : p.NoSideInfo M :=
  p.noSideInfo_of_ae_eq ((p.isTrivial_of_isPure hω).outcome_ae_eq M)

end Preparation

/-! ## E. Purity is the absence of side information -/

namespace UnitalPositiveLinearMap

variable {ω : 𝓢[ℝ, E]}

/-- A state has no side information when, however it is prepared, the roll and the outcome of any
yes/no measurement are independent. -/
def HasNoSideInfo (ω : 𝓢[ℝ, E]) : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (p : Preparation E X), p.state = ω →
    ∀ e : Effect E, p.NoSideInfo (Effect.binaryMeasurement e)

/-- **Purity is the absence of side information.** A normal state is pure exactly when, however it
is prepared, the roll and the outcome of any yes/no measurement are independent: knowing how the
state was prepared never helps to predict a measurement. -/
lemma isPure_iff_hasNoSideInfo (hω : ω.IsNormal) : ω.IsPure ↔ ω.HasNoSideInfo := by
  simp only [HasNoSideInfo, isPure_iff_forall_isTrivial hω, Preparation.isTrivial_iff_noSideInfo]

/-- **A mixed state leaks side information.** A normal state is mixed exactly when it can be
prepared by choosing between two states so that some yes/no measurement detects the choice. -/
lemma isMixed_iff_exists_sideInfo (hω : ω.IsNormal) :
    ω.IsMixed ↔ ∃ p : Preparation E Bool, p.state = ω ∧
      ∃ e : Effect E, ¬ p.NoSideInfo (Effect.binaryMeasurement e) := by
  refine ⟨fun h => ?_, fun ⟨p, hp, e, h⟩ hpure =>
    h ((isPure_iff_hasNoSideInfo hω).1 hpure Bool p hp e)⟩
  by_contra! hno
  exact h (isPure_of_isTrivial hω fun p hp => p.isTrivial_iff_noSideInfo.2 (hno p hp))

end UnitalPositiveLinearMap

end ProbabilisticTheory
