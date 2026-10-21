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
`X` form an order-unit space `A X`. A local net assigns to `X ≤ Y` a channel,
which regards an observable of `X` as one of `Y`.

For a tensor product system with `H_Y ≃ H_X ⊗ H_rest`, take `A X` to be the Hermitian operators
on `H_X`. Then the inclusion is the familiar map `M ↦ M ⊗ 1`: the observable acts as `M` on `X` and
as the identity on the remaining factors.

The local observables can also be viewed in one space, `N.Quasilocal`, the algebraic direct limit
of the local observable spaces. It is a real vector space and carries no norm. Completing it in a
norm, which needs more structure than is assumed here, gives the quasilocal algebra of the physics
literature. Inductive limits of order-unit spaces are developed in [ref: arxiv_1705_04663].

## ii. Key results

- `LocalNet`: subsystem observables with channels into larger subsystems.
- `LocalNet.IsOrderEmbedding`: the inclusion maps reflect order.
- `LocalNet.map_le_map_iff`: inclusion preserves and reflects inequalities.
- `LocalNet.incl_injective`: order-embedding inclusion maps are injective.
- `LocalNet.Quasilocal`: the algebraic direct limit of the local observable spaces.
- `LocalNet.toQuasilocal`: regard an observable of one subsystem as a quasilocal observable.
- `LocalNet.toQuasilocal_eq_iff`: equality of quasilocal observables can be checked in a common
  larger subsystem.
- `LocalNet.toQuasilocal_injective`: order-embedding inclusions keep local observables distinct.
- `LocalNet.exists_toQuasilocal_eq`, `exists_toQuasilocal_eq₂`: quasilocal observables have
  representatives in a single subsystem, and any two have representatives in a common one.

## iii. Table of contents

- A. Subsystems and inclusions
- B. Order-embedding inclusions
- C. The quasilocal observable space
- D. Embedding the local observables
- E. Directed families of subsystems

## iv. References

* L. Mawhinney, I. G. Todorov, *Inductive limits in the operator system and related categories*,
  arXiv:1705.04663. [ref: arxiv_1705_04663]

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
  /-- Inclusion into the same subsystem is the identity. -/
  incl_refl : ∀ X : R, incl (le_refl X) = .id ℝ (A X)
  /-- Including through an intermediate subsystem agrees with direct inclusion. -/
  incl_trans : ∀ {X Y Z : R} (h₁ : X ≤ Y) (h₂ : Y ≤ Z) (h₃ : X ≤ Z),
    incl h₃ = (incl h₂).comp (incl h₁)

namespace LocalNet

variable (N : LocalNet R A) {X Y Z : R}

/-- An observable is unchanged by inclusion into the same subsystem. -/
@[simp] lemma incl_refl_apply (X : R) (a : A X) : N.incl (le_refl X) a = a := by
  simp [N.incl_refl]

/-- Including an observable through an intermediate subsystem agrees with direct inclusion. -/
lemma incl_trans_apply (h₁ : X ≤ Y) (h₂ : Y ≤ Z) (h₃ : X ≤ Z) (a : A X) :
    N.incl h₃ a = N.incl h₂ (N.incl h₁ a) := by
  simp [N.incl_trans h₁ h₂ h₃]

/-! ## B. Order-embedding inclusions -/

/-- The inclusion maps are order embeddings if each reflects positivity. -/
class IsOrderEmbedding (N : LocalNet R A) : Prop where
  /-- An observable that is positive in a larger subsystem is already positive in the smaller. -/
  nonneg_of_incl_nonneg : ∀ {X Y : R} (h : X ≤ Y) {a : A X}, 0 ≤ N.incl h a → 0 ≤ a

/-- Inclusion in an order-embedding net preserves and reflects inequalities. -/
lemma map_le_map_iff [N.IsOrderEmbedding] (h : X ≤ Y) {a b : A X} :
    N.incl h a ≤ N.incl h b ↔ a ≤ b := by
  rw [← sub_nonneg, ← map_sub, ← sub_nonneg (a := b) (b := a)]
  exact ⟨IsOrderEmbedding.nonneg_of_incl_nonneg h, map_nonneg _⟩

/-- The inclusion maps of an order-embedding net are injective. -/
lemma incl_injective [N.IsOrderEmbedding] (h : X ≤ Y) : Function.Injective (N.incl h) :=
  (OrderEmbedding.ofMapLEIff (N.incl h) fun _ _ => N.map_le_map_iff h).injective

open scoped Classical

/-!

## C. The quasilocal observable space

For a directed family of subsystems, observables from different subsystems can be included in a
common larger one and combined there. The direct limit identifies all such local descriptions
consistently and supplies the resulting real vector space.

-/

/-- The inclusions as linear maps: the transition maps of the direct limit defining
`N.Quasilocal`. -/
abbrev inclLin (N : LocalNet R A) ⦃X Y : R⦄ (h : X ≤ Y) : A X →ₗ[ℝ] A Y :=
  (N.incl h).toLinearMap

/-- The inclusions form a directed system: including a subsystem into itself does nothing, and
successive inclusions compose. -/
instance directedSystem (N : LocalNet R A) : DirectedSystem A fun _ _ h => N.inclLin h where
  map_self _ x := N.incl_refl_apply _ x
  map_map _ _ _ hij hjk x := (N.incl_trans_apply hij hjk _ x).symm

/-- The algebraic direct limit of the local observable spaces. -/
def Quasilocal (N : LocalNet R A) : Type _ :=
  Module.DirectLimit A N.inclLin

variable {N}

/-- Quasilocal observables add, as elements of a direct limit of vector spaces. -/
noncomputable instance : AddCommGroup N.Quasilocal :=
  inferInstanceAs (AddCommGroup (Module.DirectLimit A N.inclLin))

/-- Quasilocal observables can be scaled by real numbers. -/
noncomputable instance : Module ℝ N.Quasilocal :=
  inferInstanceAs (Module ℝ (Module.DirectLimit A N.inclLin))

/-!

## D. Embedding the local observables

The map `toQuasilocal N i` takes an observable of subsystem `i` to the quasilocal observable it
represents.
-/

variable (N) in
/-- Regard an observable of subsystem `i` as a quasilocal observable. -/
noncomputable def toQuasilocal (i : R) : A i →ₗ[ℝ] N.Quasilocal :=
  Module.DirectLimit.of ℝ R A N.inclLin i

/-- Including an observable in a larger subsystem does not change its quasilocal representation. -/
lemma toQuasilocal_incl {i j : R} (h : i ≤ j) (a : A i) :
    toQuasilocal N j (N.incl h a) = toQuasilocal N i a :=
  Module.DirectLimit.of_f (hij := h) (x := a)

/-- Observables that agree in a common larger subsystem represent the same quasilocal
observable. -/
lemma toQuasilocal_eq_of_incl_eq {i j k : R} (hik : i ≤ k) (hjk : j ≤ k) {a : A i} {b : A j}
    (h : N.incl hik a = N.incl hjk b) : toQuasilocal N i a = toQuasilocal N j b := by
  rw [← toQuasilocal_incl hik, ← toQuasilocal_incl hjk, h]

/-!

## E. Directed families of subsystems

If any two subsystems are contained in a common larger one, the quasilocal observable space is
described by representatives in single subsystems.

-/

section DirectedSubsystems

variable [IsDirectedOrder R]

/-- Observables representing the same quasilocal observable agree in a common larger
subsystem. -/
lemma exists_incl_eq_of_toQuasilocal_eq {i j : R} {a : A i} {b : A j}
    (h : toQuasilocal N i a = toQuasilocal N j b) :
    ∃ (k : R) (hik : i ≤ k) (hjk : j ≤ k), N.incl hik a = N.incl hjk b := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have h' : toQuasilocal N k (N.incl hik a) = toQuasilocal N k (N.incl hjk b) := by
    rw [toQuasilocal_incl, toQuasilocal_incl, h]
  obtain ⟨l, hkl, hl⟩ := Module.DirectLimit.exists_eq_of_of_eq (G := A) (f := N.inclLin) h'
  exact ⟨l, hik.trans hkl, hjk.trans hkl,
    (N.incl_trans_apply hik hkl _ a).trans (hl.trans (N.incl_trans_apply hjk hkl _ b).symm)⟩

/-- Two local observables represent the same quasilocal observable exactly when they agree in a
common larger subsystem. -/
lemma toQuasilocal_eq_iff {i j : R} (a : A i) (b : A j) :
    toQuasilocal N i a = toQuasilocal N j b ↔
      ∃ (k : R) (hik : i ≤ k) (hjk : j ≤ k), N.incl hik a = N.incl hjk b :=
  ⟨exists_incl_eq_of_toQuasilocal_eq, fun ⟨_, hik, hjk, h⟩ => toQuasilocal_eq_of_incl_eq hik hjk h⟩

/-- Order-embedding inclusions keep distinct local observables distinct in the quasilocal space. -/
lemma toQuasilocal_injective [N.IsOrderEmbedding] (i : R) :
    Function.Injective (toQuasilocal N i) := by
  intro a b hab
  obtain ⟨k, hik, _, h⟩ := (toQuasilocal_eq_iff a b).1 hab
  exact N.incl_injective hik h

variable [Nonempty R]

/-- Every quasilocal observable has a representative in some subsystem. -/
lemma exists_toQuasilocal_eq (x : N.Quasilocal) : ∃ (i : R) (a : A i), toQuasilocal N i a = x :=
  Module.DirectLimit.exists_of x

/-- Any two quasilocal observables have representatives in a common subsystem. -/
lemma exists_toQuasilocal_eq₂ (x y : N.Quasilocal) :
    ∃ (i : R) (a b : A i), toQuasilocal N i a = x ∧ toQuasilocal N i b = y :=
  Module.DirectLimit.exists_of₂ x y

end DirectedSubsystems

end LocalNet

end ProbabilisticTheory
