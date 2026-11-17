/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
module

public import Mathlib.Data.Fin.SuccPred
/-!
# Removing a known-distinct index from `Fin n`

The position of an index of `Fin n` once a different index has been removed.

## i. Overview

Given `i ≠ k` in `Fin n`, `Fin.predAboveOfNe` sends `i` to its position in `Fin (n - 1)` once
`k` is deleted: `i` moves down by one if it lies above `k`, and stays where it is otherwise.
Unlike `Fin.predAbove`, it takes the proof `i ≠ k` instead of a `Fin (n - 1)` pivot, so it
applies when only `n` (and not `n - 1 + 1`) is in hand. This map is injective.

## ii. Key results

- `Fin.predAboveOfNe` : the position of `i` in `Fin (n - 1)` once `k ≠ i` is removed.
- `Fin.predAboveOfNe_injective` : that map is injective.

## iii. Table of contents

- A. Removing a known-distinct index

## iv. References

- Zulip discussion: https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/succAbove.20and.20predAbove.20lemmas/with/584270574

-/

@[expose] public section

namespace Fin

/-!

## A. Removing a known-distinct index

-/

/-- The position of `i` in `Fin (n - 1)` once a different index `k` is removed from `Fin n`:
`i` moves down by one if it lies above `k`, and stays where it is otherwise.
See discussion at https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/succAbove.20and.20predAbove.20lemmas/with/584270574
-/
def predAboveOfNe {n : ℕ} {k i : Fin n}
    (h : i ≠ k) : Fin (n - 1) := by
  by_cases H : i.1 > k.1
  · exact ⟨i.1 - 1, by omega⟩
  · exact ⟨i.1, by omega⟩

/-- A "missing lemma" for `Fin` types. -/
lemma predAboveOfNe_injective (n : ℕ) (k x y : Fin n)
    (hx : x ≠ k) (hy : y ≠ k)
    (heq : Fin.predAboveOfNe hx = Fin.predAboveOfNe hy) : x = y := by
  unfold predAboveOfNe at heq
  split_ifs at heq
  all_goals
  · simp only [mk.injEq] at heq
    omega

end Fin
