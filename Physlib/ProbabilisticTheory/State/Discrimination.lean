/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.State.Metric
public import Physlib.ProbabilisticTheory.Effect.Complement
public import Mathlib.Algebra.Order.Group.CompleteLattice

/-!
# State discrimination

Optimal binary discrimination probabilities and their relation to the state distance.

## i. Overview

A system is prepared in state `ω₀` (with probability `p`) or `ω₁` (with probability `1 - p`). We
get to run a single yes/no test on it — an effect `e` — and have to guess which state it was,
based only on whether `e` "clicked". We guess `ω₀` on a click and `ω₁` otherwise; `successProb`
is the probability that guess is right.

Always guessing `ω₁`, without even looking at the system, is already right with probability
`1 - p` — that's our baseline. Running a test can only add to it: its `advantage` is how much
extra success probability it buys over that baseline. Taking the supremum over all tests gives the
classic Helstrom bound (`optimalSuccessProb_eq`), without assuming an optimizing test exists.

For equal priors (`p = 1/2`) the bound simplifies to `1/2 + dist ω₀ ω₁ / 4`.
Two equally likely states are easier to tell apart exactly when they sit farther apart.

## ii. Key results

- `UnitalPositiveLinearMap.optimalSuccessProb_eq` : the Helstrom bound.
- `UnitalPositiveLinearMap.optimalSuccessProb_half_half_eq` : for equal priors, the bound is the
  state distance.

## iii. Table of contents

- A. Success probability and the advantage of a test
- B. The Helstrom bound
- C. Equal priors: the bound is the state distance

## iv. References

- C.W. Helstrom, *Quantum Detection and Estimation Theory*, Academic Press, 1976.

-/

@[expose] public section

open ProbabilisticTheory Effect

namespace UnitalPositiveLinearMap

section OrderUnitSpace

variable {E : Type*} [OrderUnitSpace E]

/-! ## A. Success probability and the advantage of a test -/

/-- Probability of guessing right between `ω₀` (prior `p`) and `ω₁` (prior `1 - p`) using test
`e`: guess `ω₀` on a click, `ω₁` otherwise. -/
def successProb (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) (e : Effect E) : ℝ :=
  p * ω₀ e + (1 - p) * ω₁ (complement e)

/-- How much test `e` improves on the baseline of always guessing `ω₁`. -/
def advantage (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) (e : Effect E) : ℝ :=
  p * ω₀ e - (1 - p) * ω₁ e

/-- Success probability equals the baseline `1 - p` plus the advantage of test `e`. -/
lemma successProb_eq_add_advantage (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) (e : Effect E) :
    successProb ω₀ ω₁ p e = (1 - p) + advantage ω₀ ω₁ p e := by
  simp [successProb, advantage, complement]
  ring

/-! ## B. The Helstrom bound -/

/-- No test's advantage beats the prior weight `p` of the state it favors. -/
lemma advantage_le (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) (e : Effect E) :
    advantage ω₀ ω₁ p e ≤ p := by
  exact (sub_le_self _ (mul_nonneg (sub_nonneg.mpr p.2.2) (map_nonneg ω₁ e.2.1))).trans
    (by simpa using mul_le_mul_of_nonneg_left (ω₀.apply_le_one e.2.2) p.2.1)

/-- Advantages of tests are bounded above. -/
lemma bddAbove_advantage (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) :
    BddAbove (Set.range (advantage ω₀ ω₁ p)) :=
  ⟨p, by rintro _ ⟨e, rfl⟩; exact advantage_le ω₀ ω₁ p e⟩

/-- The best a single test can do. -/
noncomputable def optimalSuccessProb (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) : ℝ :=
  ⨆ e : Effect E, successProb ω₀ ω₁ p e

/-- The Helstrom bound: optimal success probability is the baseline `1 - p` plus the best
advantage any test can give. -/
lemma optimalSuccessProb_eq (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) :
    optimalSuccessProb ω₀ ω₁ p = (1 - p) + ⨆ e : Effect E, advantage ω₀ ω₁ p e := by
  simp_rw [optimalSuccessProb, successProb_eq_add_advantage,
    ← add_ciSup (bddAbove_advantage ω₀ ω₁ p)]

/-! ## C. Equal priors: the bound is the state distance -/

/-- Complementing an effect negates `ω₀ e - ω₁ e`. -/
lemma sub_complement_eq_neg_sub (ω₀ ω₁ : 𝓢[ℝ, E]) (e : Effect E) :
    ω₀ (complement e) - ω₁ (complement e) = -(ω₀ e - ω₁ e) := by
  simp [complement]

/-- The differences `|ω₀ e - ω₁ e|` over effects are bounded above. -/
lemma bddAbove_abs_sub (ω₀ ω₁ : 𝓢[ℝ, E]) :
    BddAbove (Set.range fun e : Effect E => |ω₀ e - ω₁ e|) := by
  use 1
  rintro _ ⟨e, rfl⟩
  exact abs_sub_le_of_nonneg_of_le (map_nonneg ω₀ e.2.1) (ω₀.apply_le_one e.2.2)
    (map_nonneg ω₁ e.2.1) (ω₁.apply_le_one e.2.2)

/-- The differences `ω₀ e - ω₁ e` over effects are bounded above. -/
lemma bddAbove_sub (ω₀ ω₁ : 𝓢[ℝ, E]) :
    BddAbove (Set.range fun e : Effect E => ω₀ e - ω₁ e) := by
  use 1
  rintro _ ⟨e, rfl⟩
  exact (sub_le_self _ (map_nonneg ω₁ e.2.1)).trans (ω₀.apply_le_one e.2.2)

/-- The supremum of the state-value difference equals that of its absolute value: complementing
an effect flips the sign. -/
lemma ciSup_sub_eq_ciSup_abs_sub (ω₀ ω₁ : 𝓢[ℝ, E]) :
    (⨆ e : Effect E, (ω₀ e - ω₁ e)) = ⨆ e : Effect E, |ω₀ e - ω₁ e| := by
  refine le_antisymm
    (ciSup_le fun e => (le_abs_self _).trans (le_ciSup (bddAbove_abs_sub ω₀ ω₁) e))
    (ciSup_le fun e => abs_le.mpr ⟨?_, le_ciSup (bddAbove_sub ω₀ ω₁) e⟩)
  simpa only [sub_complement_eq_neg_sub, neg_le] using
    le_ciSup (bddAbove_sub ω₀ ω₁) (complement e)

end OrderUnitSpace

section Archimedean

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

open ArchimedeanOrderUnitSpace

/-- The state distance is the supremum of the differences on recentered effects. -/
lemma dist_eq_ciSup_abs_sub (ω₀ ω₁ : 𝓢[ℝ, E]) :
    dist ω₀ ω₁ =
      ⨆ e : Effect E, |ω₀ (effectEquiv e) - ω₁ (effectEquiv e)| :=
  effectEquiv.iSup_comp.symm

/-- The state distance is twice the largest state-value difference over all effects. -/
lemma dist_eq_two_mul_ciSup_sub (ω₀ ω₁ : 𝓢[ℝ, E]) :
    dist ω₀ ω₁ = 2 * ⨆ e : Effect E, (ω₀ e - ω₁ e) := by
  rw [ciSup_sub_eq_ciSup_abs_sub, dist_eq_ciSup_abs_sub, Real.mul_iSup_of_nonneg zero_le_two]
  simp [apply_effectEquiv, ← mul_sub, abs_mul]

/-- For equal priors, the Helstrom bound is `1/2` plus a quarter of the state distance. -/
lemma optimalSuccessProb_half_half_eq (ω₀ ω₁ : 𝓢[ℝ, E]) :
    optimalSuccessProb ω₀ ω₁ ⟨1 / 2, by norm_num, by norm_num⟩ = 1 / 2 + dist ω₀ ω₁ / 4 := by
  rw [optimalSuccessProb_eq, dist_eq_two_mul_ciSup_sub]
  norm_num [advantage]
  simp_rw [← mul_sub, ← Real.mul_iSup_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  ring

end Archimedean

end UnitalPositiveLinearMap
