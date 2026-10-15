/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Channel.Basic
public import Physlib.ProbabilisticTheory.OrderUnit.Basic
public import Mathlib.Algebra.Colimit.Module

/-!
# Local nets of observables

Observables of subsystems and their inclusion into larger subsystems.

## i. Overview

Let `R` index subsystems, with `X ≤ Y` meaning that `X` is contained in `Y`. The observables of
`X` form an order-unit space `A X`. A local net assigns to `X ≤ Y` a channel
`N.incl h : Channel (A X) (A Y)`, which regards an observable of `X` as one of `Y`. Here a channel
means a positive linear map that preserves the order unit `1`.

For a tensor product system with `H_Y ≃ H_X ⊗ H_rest`, take `A X` to be the Hermitian operators
on `H_X`. Then `N.incl h` is the familiar map `M ↦ M ⊗ 1`: the observable acts as `M` on `X` and
as the identity on the remaining factors. The net laws say that including into the same
subsystem does nothing and that successive inclusions agree with direct inclusion.

The class `N.IsOrderEmbedding` requires these maps to reflect inequalities. Thus two observables
of `X` have the same order relation whether compared in `X` or in a larger subsystem `Y`.

The local observables can also be viewed in one space, `N.Global`, which identifies an observable
with its image in any larger subsystem. For a directed family of subsystems, two local observables
represent the same global observable exactly when they agree in a common larger subsystem.

## ii. Key results

- `LocalNet`: subsystem observables with channels into larger subsystems.
- `LocalNet.IsOrderEmbedding`: the inclusion maps reflect order.
- `LocalNet.incl_le_incl_iff`: inclusion preserves and reflects inequalities.
- `LocalNet.incl_injective`: order-embedding inclusion maps are injective.
- `LocalNet.Global`: the algebraic direct limit of the local observable spaces.
- `LocalNet.Global.of`: regard an observable of one subsystem as a global observable.
- `LocalNet.Global.of_eq_iff`: equality of global observables can be checked in a common larger
  subsystem.
- `LocalNet.Global.of_injective`: order-embedding inclusions keep local observables distinct.

## iii. Table of contents

- A. Subsystems and inclusions
- B. Order-embedding inclusions
- C. The global observable space
- D. Local observables in the global space

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

variable {R : Type*} [Preorder R] {A : R → Type*} [∀ X, OrderUnitSpace (A X)]

/-! ## A. Subsystems and inclusions -/

/-- The observables of each subsystem, with channels into larger subsystems. -/
@[ext]
structure LocalNet (R : Type*) [Preorder R] (A : R → Type*)
    [∀ X, OrderUnitSpace (A X)] where
  /-- Regard an observable of `X` as an observable of `Y` when `X ≤ Y`. -/
  incl : ∀ {X Y : R}, X ≤ Y → A X →ₚ₁[ℝ] A Y
  /-- An observable is unchanged by inclusion into the same subsystem. -/
  incl_refl : ∀ (X : R) (a : A X), incl (le_refl X) a = a
  /-- Including through an intermediate subsystem agrees with direct inclusion. -/
  incl_trans : ∀ {X Y Z : R} (h₁ : X ≤ Y) (h₂ : Y ≤ Z) (a : A X),
    incl (h₁.trans h₂) a = incl h₂ (incl h₁ a)

attribute [simp] LocalNet.incl_refl

namespace LocalNet

variable (N : LocalNet R A) {X Y Z : R}

/-! ## B. Order-embedding inclusions -/

/-- The inclusion maps are order embeddings if each reflects positivity. -/
class IsOrderEmbedding (N : LocalNet R A) : Prop where
  /-- An observable that is positive in a larger subsystem is already positive in the smaller. -/
  nonneg_of_incl_nonneg : ∀ {X Y : R} (h : X ≤ Y) {a : A X}, 0 ≤ N.incl h a → 0 ≤ a

section OrderEmbedding

variable [N.IsOrderEmbedding]

/-- Inclusion in an order-embedding net preserves and reflects inequalities. -/
lemma incl_le_incl_iff (h : X ≤ Y) {a b : A X} :
    N.incl h a ≤ N.incl h b ↔ a ≤ b := by
  rw [← sub_nonneg, ← map_sub, ← sub_nonneg (a := b) (b := a)]
  exact ⟨IsOrderEmbedding.nonneg_of_incl_nonneg h, map_nonneg _⟩

/-- The inclusion maps of an order-embedding net are injective. -/
lemma incl_injective (h : X ≤ Y) : Function.Injective (N.incl h) :=
  (OrderEmbedding.ofMapLEIff (N.incl h) fun _ _ => N.incl_le_incl_iff h).injective

end OrderEmbedding

variable [DecidableEq R]

/-!

## C. The global observable space

For a directed family of subsystems, observables from different subsystems can be included in a
common larger one and combined there. The direct limit identifies all such local descriptions
consistently and supplies the resulting real vector space.

-/

/-- The inclusions as linear maps: the transition maps of the direct limit defining `N.Global`. -/
abbrev inclLin (N : LocalNet R A) ⦃X Y : R⦄ (h : X ≤ Y) : A X →ₗ[ℝ] A Y :=
  (N.incl h).toLinearMap

/-- The inclusions form a directed system: including a subsystem into itself does nothing, and
successive inclusions compose. -/
instance directedSystem (N : LocalNet R A) : DirectedSystem A fun _ _ h => N.inclLin h where
  map_self _ x := N.incl_refl _ x
  map_map _ _ _ hij hjk x := (N.incl_trans hij hjk x).symm

/-- The algebraic direct limit of the local observable spaces. -/
def Global (N : LocalNet R A) : Type _ :=
  Module.DirectLimit A N.inclLin

namespace Global

variable {N : LocalNet R A}

/-- Global observables add, as elements of a direct limit of vector spaces. -/
noncomputable instance : AddCommGroup N.Global :=
  inferInstanceAs (AddCommGroup (Module.DirectLimit A N.inclLin))

/-- Global observables can be scaled by real numbers. -/
noncomputable instance : Module ℝ N.Global :=
  inferInstanceAs (Module ℝ (Module.DirectLimit A N.inclLin))

/-!

## D. Local observables in the global space

The map `of N i` takes an observable of subsystem `i` to the global observable it represents.
-/

variable (N) in
/-- Regard an observable of subsystem `i` as a global observable. -/
noncomputable def of (i : R) : A i →ₗ[ℝ] N.Global :=
  Module.DirectLimit.of ℝ R A N.inclLin i

/-- Including an observable in a larger subsystem does not change its global representation. -/
lemma of_incl {i j : R} (h : i ≤ j) (a : A i) : of N j (N.incl h a) = of N i a :=
  Module.DirectLimit.of_f (hij := h) (x := a)

section Directed

variable [IsDirectedOrder R]

/-- Two local observables represent the same global observable exactly when they agree in a
common larger subsystem. -/
lemma of_eq_iff {i j : R} (a : A i) (b : A j) :
    of N i a = of N j b ↔ ∃ k, ∃ (hik : i ≤ k) (hjk : j ≤ k), N.incl hik a = N.incl hjk b := by
  refine ⟨fun h => ?_, fun ⟨k, hik, hjk, h⟩ => by rw [← of_incl hik, ← of_incl hjk, h]⟩
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  obtain ⟨l, hkl, hl⟩ := Module.DirectLimit.exists_eq_of_of_eq
    (G := A) (f := N.inclLin)
    (show of N k (N.incl hik a) = of N k (N.incl hjk b) by rw [of_incl, of_incl, h])
  exact ⟨l, hik.trans hkl, hjk.trans hkl,
    (N.incl_trans hik hkl a).trans (hl.trans (N.incl_trans hjk hkl b).symm)⟩

variable [N.IsOrderEmbedding] in
/-- Order-embedding inclusions keep distinct local observables distinct in the global space. -/
lemma of_injective (i : R) : Function.Injective (of N i) :=
  fun _ _ h => let ⟨_, hik, _, h⟩ := (of_eq_iff _ _).1 h; N.incl_injective hik h

variable [Nonempty R]

/-- Every global observable has a representative in some subsystem. -/
lemma exists_local (x : N.Global) : ∃ (i : R) (a : A i), of N i a = x :=
  Module.DirectLimit.exists_of x

/-- Any two global observables have representatives in a common subsystem. -/
lemma exists_local₂ (x y : N.Global) :
    ∃ (i : R) (a b : A i), of N i a = x ∧ of N i b = y :=
  Module.DirectLimit.exists_of₂ x y

end Directed

end Global

end LocalNet

end ProbabilisticTheory
