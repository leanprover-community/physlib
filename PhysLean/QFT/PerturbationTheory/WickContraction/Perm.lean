/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QFT.PerturbationTheory.WickAlgebra.WickTerm
public import PhysLean.QFT.PerturbationTheory.WickContraction.IsFull
public import PhysLean.Meta.Informal.SemiFormal
/-!

# Permutations of Wick contractions

We define two Wick contractions to be permutations of each other
if the Wick term they produce is equal.

## TODO

The long term aim is to simplify this condition as much as possible,
so that it can eventually be made decidable.

It should become apparent that two Wick contractions are permutations of each other
if they correspond to the same Feynman diagram.
Please speak to JTS before working in this direction.

-/

@[expose] public section

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open PhysLean.List
open WickAlgebra
open FieldStatistic
noncomputable section

/-- For a list `φs` of `𝓕.FieldOp`, and two Wick contractions `φsΛ₁` and `φsΛ₂` of `φs`,
  we say that `φsΛ₁` and `φsΛ₂` are permutations of each other if they have the same Wick term. -/
def Perm {φs : List 𝓕.FieldOp} (φsΛ₁ φsΛ₂ : WickContraction φs.length) : Prop :=
  φsΛ₁.wickTerm = φsΛ₂.wickTerm

namespace Perm

variable {φs : List 𝓕.FieldOp} {φsΛ φsΛ₁ φsΛ₂ φsΛ₃ : WickContraction φs.length}

/-- The reflexivity of the `Perm` relation. -/
@[refl]
lemma refl : Perm φsΛ φsΛ := by
  rw [Perm]

/-- The symmetry of the `Perm` relation. -/
@[symm]
lemma symm (h : Perm φsΛ₁ φsΛ₂) : Perm φsΛ₂ φsΛ₁ := by
  rw [Perm] at h ⊢
  exact h.symm

/-- The transitivity of the `Perm` relation. -/
@[trans]
lemma trans (h12 : Perm φsΛ₁ φsΛ₂) (h23 : Perm φsΛ₂ φsΛ₃) :
    Perm φsΛ₁ φsΛ₃ := by
  rw [Perm] at h12 h23 ⊢
  exact h12.trans h23

/-- If `Perm φsΛ₁ φsΛ₂` then if `φsΛ₁` is a full Wick contraction
  then `φsΛ₂` is a full Wick contraction..

Implementation note: Please contact JTS before attempting this. -/
@[sorryful]
lemma isFull_of_isFull (h : Perm φsΛ₁ φsΛ₂) (hf : IsFull φsΛ₁) : IsFull φsΛ₂ := by
  sorry

/-- If `Perm φsΛ₁ φsΛ₂` then the uncontracted lists of
  `φsΛ₁` and `φsΛ₂` are permutations of each other. -/
@[sorryful]
lemma perm_uncontractedList (h : Perm φsΛ₁ φsΛ₂) : [φsΛ₁]ᵘᶜ.Perm [φsΛ₂]ᵘᶜ := by
  sorry

end Perm

end
end WickContraction
