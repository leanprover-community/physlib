/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Folner
public import PhyslibAlpha.CondensedMatter.Crystal.QuasiLocal
public import PhyslibAlpha.CondensedMatter.QuasiLocal.InvariantLimit

/-!

# Translation invariant states of an infinite crystal

Every state of the quasi-local algebra of the crystal `ℤ^d` with a finite unit cell has a
translation invariant limit state, and so does every thermodynamic limit state of an interaction.

## i. Overview

The translations of the crystal `ℤ^d` act on its quasi-local algebra by `*`-automorphisms
(`translationAction`). The averages of a state over the translations by the points of the cube
`{0, …, n}^d` become invariant as `n → ∞`, because the cubes satisfy the Følner condition
(`isRightFolner_boxes`). A limit point of the averages along an ultrafilter is therefore an
invariant state of the infinite crystal. Applied to the thermodynamic limit state of a canonical
ensemble, this gives a translation invariant state of the interacting infinite system, which is
the input to the reduction of the many-body problem to momentum sectors.

## ii. Key results

- `exists_translation_invariant_state` : every state has a translation invariant limit state.
- `Interaction.translationInvariantState` : the translation invariant state of the canonical
  ensemble of an interaction.

## iii. Table of contents

- A. Invariant states of the crystal

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 1,
  Section 4.3.

-/

@[expose] public section

noncomputable section

namespace CondensedMatter

namespace Crystal

open ProbabilisticTheory ProbabilisticTheory.QuasiLocal QuasiLocal Filter

variable {d : ℕ} {F : Type*} [Fintype F] [DecidableEq F]
variable (Ω₀ : Type*) [Fintype Ω₀] [DecidableEq Ω₀]

/-! ## A. Invariant states of the crystal -/

/-- An ultrafilter on the sizes of the cubes, finer than the filter of large cubes. -/
def cubeUltrafilter : Ultrafilter ℕ := Ultrafilter.of atTop

lemma cubeUltrafilter_le : (cubeUltrafilter : Filter ℕ) ≤ atTop := Ultrafilter.of_le _

/-- **The translation invariant limit of a state of the crystal `ℤ^d`**: the limit of its
averages over the translations by the points of the cubes. -/
def translationInvariantLimit (φ : AlgState (crystalAlgebra Ω₀ (Fin d → ℤ) F)) :
    AlgState (crystalAlgebra Ω₀ (Fin d → ℤ) F) :=
  AlgState.invariantLimit (translationAction Ω₀) (boxes d)
    (fun n => ⟨1, by simp [boxes, box]⟩) φ
    (AlgebraNet.isBounded_of_isLocallyBounded quantumNet_isLocallyBounded) cubeUltrafilter

omit [Fintype F] in
/-- **The translation invariant limit of a state is invariant under the translations.** -/
lemma translationInvariantLimit_invariant (φ : AlgState (crystalAlgebra Ω₀ (Fin d → ℤ) F))
    (a : Fin d → ℤ) (x : crystalAlgebra Ω₀ (Fin d → ℤ) F) :
    translationInvariantLimit Ω₀ φ (translationAction Ω₀ (Multiplicative.ofAdd a) x) =
      translationInvariantLimit Ω₀ φ x :=
  AlgState.invariantLimit_invariant _ _ _ φ _ _ (isRightFolner_boxes d _ cubeUltrafilter_le) _ x

variable {Ω₀}

/-- **The translation invariant state of the canonical ensemble** of an interaction on the crystal
`ℤ^d`: the translation average of a thermodynamic limit state of the finite boxes. -/
def _root_.CondensedMatter.QuasiLocal.Interaction.translationInvariantState [Nonempty Ω₀]
    (I : Interaction (fun _ : CellSite (Fin d → ℤ) F => Ω₀)) (β : ℝ) :
    AlgState (crystalAlgebra Ω₀ (Fin d → ℤ) F) :=
  translationInvariantLimit Ω₀
    (I.canonicalLimitState β (Ultrafilter.of atTop) (Ultrafilter.of_le _))

omit [Fintype F] in
/-- The translation invariant state of an interaction is invariant under the translations. -/
lemma translationInvariantState_invariant [Nonempty Ω₀]
    (I : Interaction (fun _ : CellSite (Fin d → ℤ) F => Ω₀)) (β : ℝ) (a : Fin d → ℤ)
    (x : crystalAlgebra Ω₀ (Fin d → ℤ) F) :
    I.translationInvariantState β (translationAction Ω₀ (Multiplicative.ofAdd a) x) =
      I.translationInvariantState β x :=
  translationInvariantLimit_invariant Ω₀ _ a x

end Crystal

end CondensedMatter

end
