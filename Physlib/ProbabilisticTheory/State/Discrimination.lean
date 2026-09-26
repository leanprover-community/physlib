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

namespace UnitalPositiveLinearMap

section OrderUnitSpace

variable {E : Type*} [OrderUnitSpace E]

/-! ## A. Success probability and the advantage of a test -/

/-- Probability of guessing right between `ω₀` (prior `p`) and `ω₁` (prior `1 - p`) using test
`e`: guess `ω₀` on a click, `ω₁` otherwise. -/
def successProb (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) (e : Effect E) : ℝ :=
  (p : ℝ) * ω₀ (e : E) + (1 - (p : ℝ)) * ω₁ ((Effect.complement e : E))

/-- How much test `e` improves on the baseline of always guessing `ω₁`. -/
def advantage (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) (e : Effect E) : ℝ :=
  (p : ℝ) * ω₀ (e : E) - (1 - (p : ℝ)) * ω₁ (e : E)

/-- Success probability equals the baseline `1 - p` plus the advantage of test `e`. -/
lemma successProb_eq_add_advantage (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) (e : Effect E) :
    successProb ω₀ ω₁ p e = (1 - (p : ℝ)) + advantage ω₀ ω₁ p e := by
  show (p : ℝ) * ω₀ (e : E) + (1 - (p : ℝ)) * ω₁ (1 - (e : E))
      = (1 - (p : ℝ)) + ((p : ℝ) * ω₀ (e : E) - (1 - (p : ℝ)) * ω₁ (e : E))
  rw [map_sub, map_one]
  ring

/-! ## B. The Helstrom bound -/

/-- No test's advantage beats the prior weight `p` of the state it favors. -/
lemma advantage_le (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) (e : Effect E) :
    advantage ω₀ ω₁ p e ≤ (p : ℝ) := by
  show (p : ℝ) * ω₀ (e : E) - (1 - (p : ℝ)) * ω₁ (e : E) ≤ (p : ℝ)
  have h1 : ω₀ (e : E) ≤ 1 := (ω₀.monotone' e.2.2).trans_eq (map_one ω₀)
  have h2 : 0 ≤ ω₁ (e : E) := map_nonneg ω₁ e.2.1
  nlinarith [p.2.1, p.2.2]

lemma bddAbove_advantage (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) :
    BddAbove (Set.range (advantage ω₀ ω₁ p)) :=
  ⟨p, by rintro _ ⟨e, rfl⟩; exact advantage_le ω₀ ω₁ p e⟩

lemma bddAbove_successProb (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) :
    BddAbove (Set.range (successProb ω₀ ω₁ p)) :=
  ⟨1, by rintro _ ⟨e, rfl⟩; rw [successProb_eq_add_advantage]; linarith [advantage_le ω₀ ω₁ p e]⟩

/-- The best a single test can do. -/
noncomputable def optimalSuccessProb (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) : ℝ :=
  ⨆ e : Effect E, successProb ω₀ ω₁ p e

/-- The Helstrom bound: optimal success probability is the baseline `1 - p` plus the best
advantage any test can give. -/
lemma optimalSuccessProb_eq (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) :
    optimalSuccessProb ω₀ ω₁ p = (1 - (p : ℝ)) + ⨆ e : Effect E, advantage ω₀ ω₁ p e := by
  simp_rw [optimalSuccessProb, successProb_eq_add_advantage,
    ← add_ciSup (bddAbove_advantage ω₀ ω₁ p)]

end OrderUnitSpace

/-! ## C. Equal priors: the bound is the state distance -/

section Archimedean

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

open ArchimedeanOrderUnitSpace

/-- Complementing an effect negates `ω₀ e - ω₁ e`. -/
lemma sub_complement_eq_neg_sub (ω₀ ω₁ : 𝓢[ℝ, E]) (e : Effect E) :
    ω₀ ((Effect.complement e : E)) - ω₁ ((Effect.complement e : E))
      = -(ω₀ (e : E) - ω₁ (e : E)) := by
  show ω₀ (1 - (e : E)) - ω₁ (1 - (e : E)) = _
  simp only [map_sub, map_one]; ring

lemma bddAbove_abs_sub (ω₀ ω₁ : 𝓢[ℝ, E]) :
    BddAbove (Set.range fun e : Effect E => |ω₀ (e : E) - ω₁ (e : E)|) :=
  ⟨1, by
    rintro _ ⟨e, rfl⟩
    exact abs_sub_le_of_nonneg_of_le (map_nonneg ω₀ e.2.1)
      ((ω₀.monotone' e.2.2).trans_eq (map_one ω₀)) (map_nonneg ω₁ e.2.1)
      ((ω₁.monotone' e.2.2).trans_eq (map_one ω₁))⟩

lemma bddAbove_sub (ω₀ ω₁ : 𝓢[ℝ, E]) :
    BddAbove (Set.range fun e : Effect E => ω₀ (e : E) - ω₁ (e : E)) :=
  let ⟨b, hb⟩ := bddAbove_abs_sub ω₀ ω₁
  ⟨b, by rintro _ ⟨e, rfl⟩; exact (le_abs_self _).trans (hb ⟨e, rfl⟩)⟩

/-- The supremum of the state-value difference equals that of its absolute value: complementing
an effect flips the sign. -/
lemma ciSup_sub_eq_ciSup_abs_sub (ω₀ ω₁ : 𝓢[ℝ, E]) :
    (⨆ e : Effect E, (ω₀ (e : E) - ω₁ (e : E))) = ⨆ e : Effect E, |ω₀ (e : E) - ω₁ (e : E)| := by
  have hbdd := bddAbove_sub ω₀ ω₁
  have hbdd' := bddAbove_abs_sub ω₀ ω₁
  apply le_antisymm
  · exact ciSup_le fun e => (le_abs_self _).trans (le_ciSup hbdd' e)
  · apply ciSup_le
    intro e
    have h1 := le_ciSup hbdd e
    have h2 := le_ciSup hbdd (Effect.complement e)
    rw [sub_complement_eq_neg_sub] at h2
    exact abs_le.mpr ⟨by linarith, h1⟩

/-- The state distance is the largest `|ω₀ e - ω₁ e|` over unit-ball effects
(`Effect.equivBall`). -/
lemma dist_eq_ciSup_abs_sub (ω₀ ω₁ : 𝓢[ℝ, E]) :
    dist ω₀ ω₁ =
      ⨆ e : Effect E, |ω₀ ((Effect.equivBall e : E)) - ω₁ ((Effect.equivBall e : E))| := by
  have hbdd' : BddAbove (Set.range
      fun e : Effect E => |ω₀ ((Effect.equivBall e : E)) - ω₁ ((Effect.equivBall e : E))|) := by
    obtain ⟨b, hb⟩ := dist_bddAbove ω₀ ω₁
    exact ⟨b, by rintro _ ⟨e, rfl⟩; exact hb (Set.mem_range_self (Effect.equivBall e))⟩
  apply le_antisymm
  · apply ciSup_le
    intro A
    rw [← Effect.equivBall.apply_symm_apply A]
    exact le_ciSup hbdd' (Effect.equivBall.symm A)
  · exact ciSup_le fun e => le_ciSup (dist_bddAbove ω₀ ω₁) (Effect.equivBall e)

/-- The state distance is twice the largest state-value difference over all effects. -/
lemma dist_eq_two_mul_ciSup_sub (ω₀ ω₁ : 𝓢[ℝ, E]) :
    dist ω₀ ω₁ = 2 * ⨆ e : Effect E, (ω₀ (e : E) - ω₁ (e : E)) := by
  rw [ciSup_sub_eq_ciSup_abs_sub, dist_eq_ciSup_abs_sub, Real.mul_iSup_of_nonneg zero_le_two]
  congr 1 with e
  rw [apply_equivBall, apply_equivBall, ← abs_two, ← abs_mul]
  ring_nf

/-- For equal priors, the Helstrom bound is `1/2` plus a quarter of the state distance. -/
lemma optimalSuccessProb_half_half_eq (ω₀ ω₁ : 𝓢[ℝ, E]) :
    optimalSuccessProb ω₀ ω₁ ⟨1 / 2, by norm_num, by norm_num⟩ = 1 / 2 + dist ω₀ ω₁ / 4 := by
  rw [optimalSuccessProb_eq, dist_eq_two_mul_ciSup_sub]
  have hfun (e : Effect E) : advantage ω₀ ω₁ ⟨1 / 2, by norm_num, by norm_num⟩ e =
      1 / 2 * (ω₀ (e : E) - ω₁ (e : E)) := by
    simp only [advantage]; ring
  simp_rw [hfun, ← Real.mul_iSup_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  ring

end Archimedean

end UnitalPositiveLinearMap
