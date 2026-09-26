/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Effect.Convex

/-!
# Complementary effects

## i. Overview

The complement of an effect `e` is the yes/no test that fires exactly when `e` doesn't: `1 - e`.
Physically, a state's probability of "no" is always `1` minus its probability of "yes".

## ii. Key results

- `Effect.complement` : the complementary effect `1 - e`.
- `Effect.complement_antitone` : the complement reverses order.
- `Effect.complement_mix` : the complement of a mixture is the mixture of the complements.

## iii. Table of contents

- A. The complement
- B. Monotonicity of the complement
- C. The complement and mixtures

-/

@[expose] public section

namespace Effect

variable {E : Type*} [OrderUnitSpace E]

/-!

## A. The complement

-/

/-- The complementary effect. -/
def complement (e : Effect E) : Effect E :=
  ⟨1 - e.1, sub_nonneg.mpr e.2.2, sub_le_self 1 e.2.1⟩

@[simp]
lemma complement_complement (e : Effect E) : complement (complement e) = e :=
  Subtype.ext (by simp [complement])

/-!

## B. Monotonicity of the complement

-/

/-- The complement reverses order: a more certain test's complement is a less certain one. -/
lemma complement_antitone : Antitone (complement (E := E)) :=
  fun _ _ h => sub_le_sub_left (show (_ : E) ≤ _ from h) 1

@[simp]
lemma complement_zero : complement (0 : Effect E) = 1 := Subtype.ext (by simp [complement])

@[simp]
lemma complement_one : complement (1 : Effect E) = 0 := Subtype.ext (by simp [complement])

/-!

## C. The complement and mixtures

-/

/-- Mixing commutes with taking the complement. -/
lemma complement_mix (e f : Effect E) (t : unitInterval) :
    complement (mix e f t) = mix (complement e) (complement f) t :=
  Subtype.ext (show (1 : E) - ((t : ℝ) • (e : E) + (1 - (t : ℝ)) • (f : E))
      = (t : ℝ) • ((1 : E) - (e : E)) + (1 - (t : ℝ)) • ((1 : E) - (f : E)) from by module)

end Effect
