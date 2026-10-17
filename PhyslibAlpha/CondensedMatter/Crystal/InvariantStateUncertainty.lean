/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.InvariantState
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.StateUncertainty

/-!

# Uncertainty relations in the invariant states of an infinite crystal

Robertson's relation for several observables holds in the translation invariant state of an
interaction on the crystal `ℤ^d`, and the translations that fix the state fix entries of `Σ`
and `Ω`.

## i. Overview

The translation invariant state of the canonical ensemble of an interaction is a state on the
quasi-local algebra of the crystal, so `AlgState.robertson_det` applies to it: for every finite
family of observables, `|det Ω| ≤ det Σ`.

The state is invariant under every translation `t_a`. If `t_a` fixes an observable `A` and
reverses an observable `B`, as a translation by one site does for the uniform and the staggered
magnetization of a finite block of an antiferromagnet, then `Σ_AB = Ω_AB = 0` by
`AlgState.covariance_eq_zero_of_symm`. A state that breaks the translation by `a`, such as a
Néel state, need not satisfy this.

## ii. Key results

- `robertson_det_translationInvariantState` : `|det Ω| ≤ det Σ` in the translation invariant
  state of an interaction.
- `covariance_translationInvariantState_eq_zero`,
  `bracket_translationInvariantState_eq_zero` : an observable fixed and one reversed by a
  translation have `Σ_AB = Ω_AB = 0`.

## iii. Table of contents

- A. Uncertainty relations in the invariant state

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 1,
  Section 4.3.

-/

@[expose] public section

namespace CondensedMatter

namespace Crystal

open ProbabilisticTheory ProbabilisticTheory.QuasiLocal QuasiLocal
open scoped selfAdjoint

variable {d : ℕ} {F : Type*} [DecidableEq F]
variable {Ω₀ : Type*} [Fintype Ω₀] [DecidableEq Ω₀] [Nonempty Ω₀]
variable (I : Interaction (fun _ : CellSite (Fin d → ℤ) F => Ω₀)) (β : ℝ)

/-! ## A. Uncertainty relations in the invariant state -/

/-- **Robertson's relation for several observables in the translation invariant state** of an
interaction on the crystal `ℤ^d`. -/
lemma robertson_det_translationInvariantState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → selfAdjoint (crystalAlgebra Ω₀ (Fin d → ℤ) F)) :
    |((I.translationInvariantState β).bracketMatrix a).det| ≤
      ((I.translationInvariantState β).covarianceMatrix a).det :=
  (I.translationInvariantState β).robertson_det a

variable {I β} {a : Fin d → ℤ} {A B : selfAdjoint (crystalAlgebra Ω₀ (Fin d → ℤ) F)}
  (hA : translationAction Ω₀ (Multiplicative.ofAdd a) (A : crystalAlgebra Ω₀ (Fin d → ℤ) F) =
    A)
  (hB : translationAction Ω₀ (Multiplicative.ofAdd a) (B : crystalAlgebra Ω₀ (Fin d → ℤ) F) =
    -(B : crystalAlgebra Ω₀ (Fin d → ℤ) F))
include hA hB

/-- In the translation invariant state, an observable fixed and one reversed by a translation
are uncorrelated. -/
lemma covariance_translationInvariantState_eq_zero :
    (I.translationInvariantState β).covariance A B = 0 :=
  AlgState.covariance_eq_zero_of_symm _ _ (translationInvariantState_invariant I β a) hA hB

/-- In the translation invariant state, an observable fixed and one reversed by a translation
have a bracket of expectation zero. -/
lemma bracket_translationInvariantState_eq_zero :
    (I.translationInvariantState β).bracket A B = 0 :=
  AlgState.bracket_eq_zero_of_symm _ _ (translationInvariantState_invariant I β a) hA hB

end Crystal

end CondensedMatter
