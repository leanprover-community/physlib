/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Classical.Basic
public import Physlib.ProbabilisticTheory.State.Convex

/-!
# Dirac states of classical function algebras

Every configuration of a classical system gives a pure state by evaluation of observables.

## i. Overview

A Dirac state represents a classical system in a definite configuration `x ∈ X`. It assigns each
observable its value at that configuration, without statistical uncertainty. Every observable
therefore has zero variance.

Dirac states are pure: they cannot be expressed as nontrivial mixtures of other states.

## ii. Key results

- `ProbabilisticTheory.Classical.eval` : evaluation at a configuration as a complex state.
- `ProbabilisticTheory.Classical.dirac` : the Dirac state, evaluation on the observables.
- `ProbabilisticTheory.Classical.dirac_sub_mul_self_eq_zero` : a definite configuration has zero
  variance.
- `ProbabilisticTheory.Classical.eq_dirac_of_forall_apply_sub_mul_self_eq_zero` : vanishing squared
  deviations characterize the Dirac state.
- `ProbabilisticTheory.Classical.isPure_dirac` : Dirac states are pure.

## iii. Table of contents

- A. Dirac states
- B. Vanishing variance
- C. Purity

## iv. References

* None.

-/

@[expose] public section

open scoped ComplexOrder

namespace ProbabilisticTheory

namespace Classical

variable {X : Type*} {S : StarSubalgebra ℂ (X → ℂ)}

/-! ## A. Dirac states -/

/-- Evaluation at a configuration `x` as a state on all functions of `S`. -/
noncomputable def eval (x : X) : 𝓢[ℂ, S] :=
  .ofLinearMap ((LinearMap.proj x).comp S.subtype.toLinearMap) (fun _ hf ↦ hf x) rfl

@[simp]
lemma eval_apply (x : X) (f : S) : eval x f = (f : X → ℂ) x := rfl

/-- The Dirac state at a configuration `x`: evaluation at `x` on the observables. -/
noncomputable def dirac [IsBounded S] (x : X) : 𝓢[ℝ, Observable S] :=
  (eval x).onObservables

/-- The Dirac state assigns each observable its value at the configuration. -/
@[simp]
lemma coe_dirac_apply [IsBounded S] (x : X) (f : Observable S) :
    (dirac x f : ℂ) = ((f : S) : X → ℂ) x :=
  UnitalPositiveLinearMap.coe_onObservables_apply (eval x) f

/-! ## B. Vanishing variance -/

/-- Squares of classical observables are nonnegative. -/
lemma mul_self_nonneg (g : Observable S) : 0 ≤ g * g := by
  rw [le_iff_apply_le]
  intro x
  simpa [star_apply] using star_mul_self_nonneg (((g : S) : X → ℂ) x)

/-- Expansion of the square of an observable shifted by a constant. -/
lemma sub_smul_one_mul_self (g : Observable S) (a : ℝ) :
    (g - a • 1) * (g - a • 1) = g * g - (2 * a) • g + (a ^ 2) • 1 := by
  refine Subtype.ext (Subtype.ext (funext ?_))
  intro x
  simp only [selfAdjoint.val_mul, AddSubgroupClass.coe_sub, selfAdjoint.val_smul,
    selfAdjoint.val_one, MulMemClass.coe_mul, SetLike.val_smul_of_tower, OneMemClass.coe_one,
    Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, Complex.real_smul, mul_one,
    AddSubgroup.coe_add, AddMemClass.coe_add, Pi.add_apply, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_pow]
  ring

/-- The square of the mean does not exceed the mean of the square. -/
lemma sq_apply_le_apply_mul_self [IsBounded S] (ω : 𝓢[ℝ, Observable S]) (g : Observable S) :
    ω g ^ 2 ≤ ω (g * g) := by
  have h := map_nonneg ω (mul_self_nonneg (g - ω g • 1))
  rw [sub_smul_one_mul_self, map_add, map_sub, map_smul, map_smul, map_one, smul_eq_mul,
    smul_eq_mul, mul_one] at h
  nlinarith

/-- Every observable has zero variance in a Dirac state. -/
lemma dirac_sub_mul_self_eq_zero [IsBounded S] (x : X) (f : Observable S) :
    dirac x ((f - dirac x f • 1) * (f - dirac x f • 1)) = 0 := by
  apply Complex.ofReal_injective
  rw [coe_dirac_apply, Complex.ofReal_zero]
  simp only [selfAdjoint.val_mul, AddSubgroupClass.coe_sub, selfAdjoint.val_smul,
    selfAdjoint.val_one, MulMemClass.coe_mul, SetLike.val_smul_of_tower, OneMemClass.coe_one,
    Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, Complex.real_smul, mul_one]
  rw [← coe_dirac_apply x f, sub_self, zero_mul]

/-- Vanishing squared deviations from the values at `x` characterize `dirac x`. -/
lemma eq_dirac_of_forall_apply_sub_mul_self_eq_zero [IsBounded S] (ω : 𝓢[ℝ, Observable S])
    (x : X) (h : ∀ f : Observable S, ω ((f - dirac x f • 1) * (f - dirac x f • 1)) = 0) :
    ω = dirac x := by
  ext f
  have hsq := sq_apply_le_apply_mul_self ω (f - dirac x f • 1)
  rw [h, map_sub, map_smul, map_one, smul_eq_mul, mul_one] at hsq
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hsq (sq_nonneg _)))

/-! ## C. Purity -/

/-- Dirac states are extreme points of the classical state space. -/
lemma isPure_dirac [IsBounded S] (x : X) : (dirac x : 𝓢[ℝ, Observable S]).IsPure := by
  refine UnitalPositiveLinearMap.isPure_iff_forall_mix_eq.mpr ?_
  intro φ ψ t ht0 ht1 hmix
  have ht : 0 < (t : ℝ) := ht0
  have ht' : 0 < 1 - (t : ℝ) := sub_pos.mpr ht1
  have hzero (f : Observable S) :
      φ ((f - dirac x f • 1) * (f - dirac x f • 1)) = 0 ∧
        ψ ((f - dirac x f • 1) * (f - dirac x f • 1)) = 0 := by
    have h := DFunLike.congr_fun hmix ((f - dirac x f • 1) * (f - dirac x f • 1))
    have hφ := map_nonneg φ (mul_self_nonneg (f - dirac x f • 1))
    have hψ := map_nonneg ψ (mul_self_nonneg (f - dirac x f • 1))
    rw [UnitalPositiveLinearMap.mix_apply, dirac_sub_mul_self_eq_zero] at h
    constructor <;> nlinarith
  exact ⟨eq_dirac_of_forall_apply_sub_mul_self_eq_zero φ x (forall_and.mp hzero).1,
    eq_dirac_of_forall_apply_sub_mul_self_eq_zero ψ x (forall_and.mp hzero).2⟩

end Classical

end ProbabilisticTheory
