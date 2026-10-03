/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Channel.Normal
public import PhyslibAlpha.ProbabilisticTheory.State.WeightEquivalence

/-!

# Normal states give normal weights

The weight of a normal state is a normal weight.

## i. Overview

The weight of a normal state is normal: suprema of directed families of nonnegative observables are
suprema in the whole space, where the state is normal.

## ii. Key results

- `UnitalPositiveLinearMap.IsNormal.toWeight_isNormal` : normal states give normal weights.

## iii. Table of contents

- A. Normal weights from normal states

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped ENNReal

variable {E : Type*} [OrderUnitSpace E]

/-! ## A. Normal weights from normal states -/

namespace UnitalPositiveLinearMap

/-- A normal state induces a normal weight.  No new normality predicate is introduced: the proof
transports a nonempty directed positive set to `E`, applies the canonical state predicate, and
then transports the nonnegative scalar supremum through `ENNReal.ofReal`. -/
lemma IsNormal.toWeight_isNormal {s : 𝓢[ℝ, E]} (hs : s.IsNormal) : s.toWeight.IsNormal := by
  intro D x hD hLUB
  have hLUBcoe : IsLUB (Set.range fun n => (D n : E)) (x : E) := by
    constructor
    · rintro z ⟨n, rfl⟩
      exact hLUB.1 ⟨n, rfl⟩
    · intro y hy
      have hy_nonneg : (0 : E) ≤ y := by
        exact (D 0).2.trans (hy ⟨0, rfl⟩)
      let y' : PosCone E := ⟨y, hy_nonneg⟩
      have hxy : x ≤ y' := hLUB.2 fun z hz => by
        obtain ⟨n, rfl⟩ := hz
        exact hy ⟨n, rfl⟩
      exact hxy
  have hmonocoe : Monotone (fun n => (D n : E)) := fun _ _ h => hD h
  have hsLUB := hs (fun n => (D n : E)) (x : E) hmonocoe hLUBcoe
  have hENN : IsLUB (Set.range fun n => ENNReal.ofReal (s (D n : E)))
      (ENNReal.ofReal (s (x : E))) := by
    constructor
    · rintro r ⟨n, rfl⟩
      exact ENNReal.ofReal_mono (hsLUB.1 ⟨n, rfl⟩)
    · intro b hb
      by_cases htop : b = ⊤
      · subst b
        exact le_top
      · rw [ENNReal.ofReal_le_iff_le_toReal htop]
        apply hsLUB.2
        rintro r ⟨n, rfl⟩
        rw [← ENNReal.ofReal_le_iff_le_toReal htop]
        exact hb ⟨n, rfl⟩
  have hrange : Set.range (s.toWeight ∘ D) =
      Set.range (fun n => ENNReal.ofReal (s (D n : E))) := by
    ext r
    simp [toWeight_apply]
  rw [hrange, toWeight_apply]
  exact hENN

end UnitalPositiveLinearMap

end ProbabilisticTheory
