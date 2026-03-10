/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QFT.PerturbationTheory.WickContraction.Basic
public import PhysLean.QFT.PerturbationTheory.Koszul.KoszulSign
/-!

# Sign associated with a contraction

-/

@[expose] public section

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open PhysLean.List
open FieldStatistic

/-- Given a Wick contraction `c : WickContraction n` and `i1 i2 : Fin n` the finite set
  of elements of `Fin n` between `i1` and `i2` which are either uncontracted
  or are contracted but are contracted with an element occurring after `i1`.
  In other words, the elements of `Fin n` between `i1` and `i2` which are not
  contracted with before `i1`.
  One should assume `i1 < i2` otherwise this finite set is empty. -/
def signFinset (c : WickContraction n) (i1 i2 : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i1 < i ∧ i < i2 ∧
  (c.getDual? i = none ∨ ∀ (h : (c.getDual? i).isSome), i1 < (c.getDual? i).get h))

/-- For a list `φs` of `𝓕.FieldOp`, and a Wick contraction `φsΛ` of `φs`,
  the complex number `φsΛ.sign` is defined to be the sign (`1` or `-1`) corresponding
  to the number of `fermionic`-`fermionic` exchanges that must be done to put
  contracted pairs within `φsΛ` next to one another, starting recursively
  from the contracted pair
  whose first element occurs at the left-most position.

  As an example, if `[φ1, φ2, φ3, φ4]` correspond to fermionic fields then the sign
  associated with
- `{{0, 1}}` is `1`
- `{{0, 1}, {2, 3}}` is `1`
- `{{0, 2}, {1, 3}}` is `-1`
-/
def sign (φs : List 𝓕.FieldOp) (φsΛ : WickContraction φs.length) : ℂ :=
  ∏ (a : φsΛ.1), 𝓢(𝓕 |>ₛ φs[φsΛ.sndFieldOfContract a],
    𝓕 |>ₛ ⟨φs.get, φsΛ.signFinset (φsΛ.fstFieldOfContract a) (φsΛ.sndFieldOfContract a)⟩)

lemma sign_empty (φs : List 𝓕.FieldOp) :
    sign φs empty = 1 := by
  rw [sign]
  simp [empty]

lemma sign_congr {φs φs' : List 𝓕.FieldOp} (h : φs = φs') (φsΛ : WickContraction φs.length) :
    sign φs' (congr (by simp [h]) φsΛ) = sign φs φsΛ := by
  subst h
  rfl

end WickContraction
