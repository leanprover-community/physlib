/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QFT.PerturbationTheory.WickAlgebra.StaticWickTerm
/-!

# Static Wick's theorem

-/

@[expose] public section

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open FieldOpFreeAlgebra

open PhysLean.List
open WickContraction
open FieldStatistic
namespace WickAlgebra

/--
For a list `φs` of `𝓕.FieldOp`, the static version of Wick's theorem states that

`φs = ∑ φsΛ, φsΛ.staticWickTerm`

where the sum is over all Wick contraction `φsΛ`.

The proof is via induction on `φs`.
- The base case `φs = []` is handled by `staticWickTerm_empty_nil`.

The inductive step works as follows:

For the LHS:
1. The proof considers `φ₀…φₙ` as `φ₀(φ₁…φₙ)` and uses the induction hypothesis on `φ₁…φₙ`.
2. This gives terms of the form `φ * φsΛ.staticWickTerm` on which
  `mul_staticWickTerm_eq_sum` is used where `φsΛ` is a Wick contraction of `φ₁…φₙ`,
  to rewrite terms as a sum over optional uncontracted elements of `φsΛ`

On the LHS we now have a sum over Wick contractions `φsΛ` of `φ₁…φₙ` (from 1) and optional
uncontracted elements of `φsΛ` (from 2)

For the RHS:
1. The sum over Wick contractions of `φ₀…φₙ` on the RHS
  is split via `insertLift_sum` into a sum over Wick contractions `φsΛ` of `φ₁…φₙ` and
  sum over optional uncontracted elements of `φsΛ`.

Both sides are now sums over the same thing and their terms equate by the nature of the
lemmas used.

-/
theorem static_wick_theorem : (φs : List 𝓕.FieldOp) →
    ofFieldOpList φs = ∑ (φsΛ : WickContraction φs.length), φsΛ.staticWickTerm
  | [] => by
    simp only [ofFieldOpList, ofFieldOpListF_nil, map_one, List.length_nil]
    rw [sum_WickContraction_nil]
    rw [staticWickTerm_empty_nil]
  | φ :: φs => by
    rw [ofFieldOpList_cons, static_wick_theorem φs]
    rw [show (φ :: φs) = φs.insertIdx (⟨0, Nat.zero_lt_succ φs.length⟩ : Fin φs.length.succ) φ
      from rfl]
    conv_rhs => rw [insertLift_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [mul_staticWickTerm_eq_sum]
    rfl

end WickAlgebra
end FieldSpecification
