/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QFT.QED.AnomalyCancellation.Sorts
/-!
# Vector like charges

For the `n`-even case we define the property of a charge assignment being vector like.

-/

@[expose] public section

open Nat
open Finset
open BigOperators

namespace PureU1

variable {n : ℕ}

/--
  Given a natural number `n`, this lemma proves that `n + n` is equal to `2 * n`.
-/
lemma split_equal (n : ℕ) : n + n = 2 * n := (Nat.two_mul n).symm

lemma split_odd (n : ℕ) : n + 1 + n = 2 * n + 1 := by omega

/-- A charge configuration for n even is vector like if when sorted the `i`th element
is equal to the negative of the `n + i`th element. -/
@[simp]
def VectorLikeEven (S : (PureU1 (2 * n)).Charges) : Prop :=
  ∀ (i : Fin n), (sort S) (Fin.cast (split_equal n) (Fin.castAdd n i))
  = - (sort S) (Fin.cast (split_equal n) (Fin.natAdd n i))

end PureU1
