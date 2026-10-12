/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.QuasiLocal.LimitState
public import PhyslibAlpha.CondensedMatter.QuasiLocal.Symmetry
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Invariant

/-!

# Symmetric thermodynamic limit states

Averaging the thermodynamic limit state of a lattice system over a group of site symmetries gives
a state of the infinite system that is invariant under the group.

## i. Overview

The Gibbs states of finite boxes break the symmetries of the lattice, because a box has a
boundary. Their limit points need not be invariant, and indeed are not in a phase with broken
symmetry. A limit point that is invariant is obtained by averaging over the group before taking
the limit: if the finite sets `F i` of group elements are asymptotically invariant (a Følner
condition), the limit of the averages of any state over them is invariant under the group.

For a lattice system with site symmetry group `Γ`, for instance the translations of a crystal, the
quasi-local algebra carries the action `symAction` of `Γ` by `*`-automorphisms. This gives a
translation invariant state of the infinite crystal, which is the hypothesis of the reduction of
the many-body problem to momentum sectors.

## ii. Key results

- `exists_invariant_state` : every state of the quasi-local algebra of a uniform lattice system has
  an invariant limit state.
- `Interaction.invariantLimitState` : the invariant state obtained from the canonical ensemble of
  an interaction.

## iii. Table of contents

- A. Invariant states of a uniform lattice system
- B. The ensembles of an interaction

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Section 6.2.3.

-/

@[expose] public section

noncomputable section

namespace CondensedMatter

namespace QuasiLocal

open ProbabilisticTheory ProbabilisticTheory.QuasiLocal Filter

variable {S : Type*} [DecidableEq S] {Γ : Type*} [Group Γ] [DecidableEq Γ] [MulAction Γ S]
variable {Ω₀ : Type*} [Fintype Ω₀] [DecidableEq Ω₀]
variable {ι : Type*}

/-! ## A. Invariant states of a uniform lattice system -/

/-- **The invariant limit of a state of a uniform lattice system**: the Følner limit of its
averages over the site symmetries. -/
def invariantLimit (φ : AlgState (uniformNet (S := S) Ω₀).Quasilocal) (F : ι → Finset Γ)
    (hne : ∀ i, (F i).Nonempty) (𝒰 : Ultrafilter ι) :
    AlgState (uniformNet (S := S) Ω₀).Quasilocal :=
  AlgState.invariantLimit (symAction (Γ := Γ) (Ω₀ := Ω₀)) F hne φ
    (AlgebraNet.isBounded_of_isLocallyBounded quantumNet_isLocallyBounded) 𝒰

/-- **The invariant limit of a state is invariant under the site symmetries.** -/
lemma invariantLimit_invariant (φ : AlgState (uniformNet (S := S) Ω₀).Quasilocal)
    (F : ι → Finset Γ) (hne : ∀ i, (F i).Nonempty) (𝒰 : Ultrafilter ι)
    (hF : IsRightFolner F 𝒰) (γ : Γ) (a : (uniformNet (S := S) Ω₀).Quasilocal) :
    invariantLimit φ F hne 𝒰 (symAction (Ω₀ := Ω₀) γ a) = invariantLimit φ F hne 𝒰 a :=
  AlgState.invariantLimit_invariant _ F hne φ _ 𝒰 hF γ a

/-- **Existence of invariant states**: if the finite sets of site symmetries are asymptotically
invariant, every state of the quasi-local algebra has an invariant limit state. -/
lemma exists_invariant_state (φ : AlgState (uniformNet (S := S) Ω₀).Quasilocal)
    (F : ι → Finset Γ) (hne : ∀ i, (F i).Nonempty) (𝒰 : Ultrafilter ι)
    (hF : IsRightFolner F 𝒰) :
    ∃ ψ : AlgState (uniformNet (S := S) Ω₀).Quasilocal,
      ∀ (γ : Γ) a, ψ (symAction (Ω₀ := Ω₀) γ a) = ψ a :=
  ⟨invariantLimit φ F hne 𝒰, invariantLimit_invariant φ F hne 𝒰 hF⟩

/-! ## B. The ensembles of an interaction -/

variable [Nonempty Ω₀]

/-- **The symmetric thermodynamic limit state of the canonical ensemble** of an interaction on a
uniform lattice system. -/
def Interaction.invariantLimitState (I : Interaction (fun _ : S => Ω₀)) (β : ℝ)
    (𝒰₀ : Ultrafilter (Finset S)) (h𝒰₀ : (𝒰₀ : Filter (Finset S)) ≤ atTop) (F : ι → Finset Γ)
    (hne : ∀ i, (F i).Nonempty) (𝒰 : Ultrafilter ι) :
    AlgState (uniformNet (S := S) Ω₀).Quasilocal :=
  invariantLimit (I.canonicalLimitState β 𝒰₀ h𝒰₀) F hne 𝒰

/-- The symmetric limit state of an interaction is invariant under the site symmetries. -/
lemma Interaction.invariantLimitState_invariant (I : Interaction (fun _ : S => Ω₀)) (β : ℝ)
    (𝒰₀ : Ultrafilter (Finset S)) (h𝒰₀ : (𝒰₀ : Filter (Finset S)) ≤ atTop) (F : ι → Finset Γ)
    (hne : ∀ i, (F i).Nonempty) (𝒰 : Ultrafilter ι) (hF : IsRightFolner F 𝒰) (γ : Γ)
    (a : (uniformNet (S := S) Ω₀).Quasilocal) :
    I.invariantLimitState β 𝒰₀ h𝒰₀ F hne 𝒰 (symAction (Ω₀ := Ω₀) γ a) =
      I.invariantLimitState β 𝒰₀ h𝒰₀ F hne 𝒰 a :=
  invariantLimit_invariant _ F hne 𝒰 hF γ a

end QuasiLocal

end CondensedMatter

end
