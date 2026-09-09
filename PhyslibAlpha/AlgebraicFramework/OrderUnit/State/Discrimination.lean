/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.Basic
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Effect.Basic

/-!

# State discrimination

## i. Overview

A system is prepared in state `ω₀` with prior probability `p₀`, or `ω₁` with prior `p₁`. Guess
which from a single yes/no test (an effect `e`): guess `0` if `e` clicks, `1` otherwise. The
optimal guess succeeds with probability

  `optimalSuccessProb ω₀ ω₁ p₀ p₁ = p₁ + sup_e (p₀ * ω₀ e - p₁ * ω₁ e)`
  (`optimalSuccessProb_eq`)

— the Helstrom bound, in the same spirit as the familiar `(1 + ‖p₀ρ₀ - p₁ρ₁‖₁) / 2` trace-distance
formula, here with the effect supremum playing the trace norm's role directly.

## ii. Key definitions and results

- `successProb`, `optimalSuccessProb`
- `optimalSuccessProb_eq`

## iii. Table of contents

- A. Success probability of a fixed test
- B. Optimal success probability
- C. The abstract Helstrom formula

-/

@[expose] public section

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]
  [PosSMulMono ℝ E] [One E] [IsOrderUnit E]

namespace UnitalPositiveLinearMap

/-! ## A. Success probability of a fixed test -/

/-- The probability of correctly guessing between `ω₀` (prior `p₀`) and `ω₁` (prior `p₁`) using
the test `e`: guess `0` when `e` clicks, `1` when its complement does. -/
def successProb (ω₀ ω₁ : 𝓢[ℝ, E]) (p₀ p₁ : ℝ) (e : Effect E) : ℝ :=
  p₀ * ω₀ (e : E) + p₁ * ω₁ ((Effect.complement e : E))

omit [PosSMulMono ℝ E] [IsOrderUnit E] in
/-- A test's success probability is the prior of guessing `1` outright, plus the advantage the
test itself adds. -/
lemma successProb_eq_add_advantage (ω₀ ω₁ : 𝓢[ℝ, E]) (p₀ p₁ : ℝ) (e : Effect E) :
    successProb ω₀ ω₁ p₀ p₁ e = p₁ + (p₀ * ω₀ (e : E) - p₁ * ω₁ (e : E)) := by
  show p₀ * ω₀ (e : E) + p₁ * ω₁ (1 - (e : E)) = p₁ + (p₀ * ω₀ (e : E) - p₁ * ω₁ (e : E))
  rw [map_sub, map_one]
  ring

/-! ## B. Optimal success probability -/

/-- The best a single test can do: the supremum of `successProb` over every possible effect. -/
noncomputable def optimalSuccessProb (ω₀ ω₁ : 𝓢[ℝ, E]) (p₀ p₁ : ℝ) : ℝ :=
  sSup (Set.range (successProb ω₀ ω₁ p₀ p₁))

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] in
/-- No effect's advantage in telling `ω₀` from `ω₁` ever beats `p₀`: certainty, weighted by its
own prior. -/
lemma advantage_le (ω₀ ω₁ : 𝓢[ℝ, E]) {p₀ p₁ : ℝ} (hp₀ : 0 ≤ p₀) (hp₁ : 0 ≤ p₁) (e : Effect E) :
    p₀ * ω₀ (e : E) - p₁ * ω₁ (e : E) ≤ p₀ := by
  have h1 : ω₀ (e : E) ≤ 1 := by simpa using ω₀.monotone' e.2.2
  have h2 : 0 ≤ ω₁ (e : E) := ω₁.map_nonneg e.2.1
  nlinarith

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] in
/-- The largest gap a single effect can open up between the two weighted states — the abstract
distinguishing power of `ω₀` against `ω₁`, bounded above by `advantage_le`. -/
lemma bddAbove_advantage (ω₀ ω₁ : 𝓢[ℝ, E]) {p₀ p₁ : ℝ} (hp₀ : 0 ≤ p₀) (hp₁ : 0 ≤ p₁) :
    BddAbove (Set.range fun e : Effect E => p₀ * ω₀ (e : E) - p₁ * ω₁ (e : E)) :=
  ⟨p₀, by rintro _ ⟨e, rfl⟩; exact advantage_le ω₀ ω₁ hp₀ hp₁ e⟩

/-! ## C. The abstract Helstrom formula -/

omit [PosSMulMono ℝ E] in
/-- The abstract Helstrom bound: the optimal one-shot success probability of distinguishing `ω₀`
(prior `p₀`) from `ω₁` (prior `p₁`) is `p₁` plus the largest advantage a single effect gives. -/
theorem optimalSuccessProb_eq (ω₀ ω₁ : 𝓢[ℝ, E]) {p₀ p₁ : ℝ} (hp₀ : 0 ≤ p₀) (hp₁ : 0 ≤ p₁) :
    optimalSuccessProb ω₀ ω₁ p₀ p₁
      = p₁ + sSup (Set.range fun e : Effect E => p₀ * ω₀ (e : E) - p₁ * ω₁ (e : E)) := by
  unfold optimalSuccessProb
  set g : Effect E → ℝ := fun e => p₀ * ω₀ (e : E) - p₁ * ω₁ (e : E) with hg
  have hbdd : BddAbove (Set.range g) := bddAbove_advantage ω₀ ω₁ hp₀ hp₁
  have hne : (Set.range g).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hbdd' : BddAbove (Set.range (successProb ω₀ ω₁ p₀ p₁)) := by
    obtain ⟨b, hb⟩ := hbdd
    refine ⟨p₁ + b, ?_⟩
    rintro _ ⟨e, rfl⟩
    rw [successProb_eq_add_advantage]
    have hge : g e ≤ b := hb (Set.mem_range_self e)
    linarith
  have hne' : (Set.range (successProb ω₀ ω₁ p₀ p₁)).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  apply le_antisymm
  · apply csSup_le hne'
    rintro _ ⟨e, rfl⟩
    rw [successProb_eq_add_advantage]
    have hge : g e ≤ sSup (Set.range g) := le_csSup hbdd (Set.mem_range_self e)
    linarith
  · have hle : sSup (Set.range g) ≤ sSup (Set.range (successProb ω₀ ω₁ p₀ p₁)) - p₁ := by
      apply csSup_le hne
      rintro _ ⟨e, rfl⟩
      have h1 : successProb ω₀ ω₁ p₀ p₁ e ≤ sSup (Set.range (successProb ω₀ ω₁ p₀ p₁)) :=
        le_csSup hbdd' (Set.mem_range_self e)
      rw [successProb_eq_add_advantage] at h1
      linarith
    linarith

end UnitalPositiveLinearMap
