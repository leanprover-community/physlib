/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Data.Multiset.Bind
public import Mathlib.Data.Multiset.Sort
/-!

## The data type FourTree

We define a tree-like structure, called `FourTree`, for storing values of a
type `α1 × α2 × α3 × α4`.

It is defined recursively, with the following structure:
- A `leaf` contains a value of type `α4`.
- A `twig` contains a value of type `α3`, and a multiset of `leaf`s.
- A `branch` contains a value of type `α2`, and a multiset of `twig`s.
- A `trunk` contains a value of type `α1`, and a multiset of `branch`s.
- A `FourTree` contains a multiset of `trunk`s.

-/

@[expose] public section

namespace PhysLean

namespace FourTree

/-- A leaf contains has the data of a term of type `α4`. -/
inductive Leaf (α4 : Type)
  | leaf : α4 → Leaf α4
deriving DecidableEq

/-- A twig has the data of a term of type `α3` and a multiset of type `Leaf α4`. -/
inductive Twig (α3 α4 : Type)
  | twig : α3 → Multiset (Leaf α4) → Twig α3 α4

/-- A branch has the data of a term of type `α2` and a multiset of type `Twig α3 α4`. -/
inductive Branch (α2 α3 α4 : Type)
  | branch : α2 → Multiset (Twig α3 α4) → Branch α2 α3 α4

/-- A trunk has the data of a term of type `α1` and a multiset of type `Branch α2 α3 α4`. -/
inductive Trunk (α1 α2 α3 α4 : Type)
  | trunk : α1 → Multiset (Branch α2 α3 α4) → Trunk α1 α2 α3 α4

end FourTree

/-- A `FourTree` has the data of a multiset of type `Trunk α1 α2 α3 α4`. -/
inductive FourTree (α1 α2 α3 α4 : Type)
  | root : Multiset (FourTree.Trunk α1 α2 α3 α4) → FourTree α1 α2 α3 α4

namespace FourTree

open Leaf Twig Branch Trunk

/-!

## Repr instances for the FourTree

These instances allow the `FourTree` to be printed in a human-readable format,
and copied and pasted.

-/

unsafe instance (α4 : Type) [Repr α4] : Repr (Leaf α4) where
  reprPrec x _ :=
    match x with
    | .leaf xs => "leaf " ++ reprStr xs

unsafe instance (α3 α4 : Type) [Repr α3] [Repr α4] : Repr (Twig α3 α4) where
  reprPrec x _ :=
    match x with
    | .twig xs a => "twig " ++ reprStr xs ++ " " ++ reprStr a

unsafe instance (α2 α3 α4: Type) [Repr α2] [Repr α3] [Repr α4] :
    Repr (Branch α2 α3 α4) where
  reprPrec x _ :=
    match x with
    | .branch xa a => "branch (" ++ reprStr xa ++ ") " ++ reprStr a

unsafe instance (α1 α2 α3 α4: Type) [Repr α1] [Repr α2] [Repr α3] [Repr α4] :
    Repr (Trunk α1 α2 α3 α4) where
  reprPrec x _ :=
    match x with
    | .trunk xa a => "trunk (" ++ reprStr xa ++ ") " ++ reprStr a

unsafe instance (α1 α2 α3 α4: Type) [Repr α1] [Repr α2] [Repr α3] [Repr α4] :
    Repr (FourTree α1 α2 α3 α4) where
  reprPrec x _ :=
    match x with
    | .root xs => "root " ++ reprStr xs

/-!

## Conversion between FourTree and Multiset

-/

/-- A `FourTree` from a multiset of `α1 × α2 × α3 × α4`. -/
def fromMultiset {α1 α2 α3 α4 : Type} [DecidableEq α1]
    [DecidableEq α2] [DecidableEq α3] [DecidableEq α4]
    (l : Multiset (α1 × α2 × α3 × α4)) : FourTree α1 α2 α3 α4 :=
  let A1 : Multiset α1 := (l.map fun x => x.1).dedup
  root <| A1.map fun xa => trunk xa <|
    let B2 := (l.filter fun y => y.1 = xa)
    let C2 : Multiset (α2 × α3 × α4) := (B2.map fun y => y.2).dedup
    let A2 : Multiset α2 := (C2.map fun x => x.1).dedup
    A2.map fun xb => branch xb <|
      let B3 := (C2.filter fun y => y.1 = xb)
      let C3 : Multiset (α3 × α4) := (B3.map fun y => y.2).dedup
      let A3 : Multiset α3 := (C3.map fun x => x.1).dedup
      A3.map fun xc => twig xc <|
        let B4 := (C3.filter fun y => y.1 = xc)
        let C4 : Multiset α4 := (B4.map fun y => y.2).dedup
        C4.map fun xd => leaf xd

/-- A `FourTree` to a multiset of `α1 × α2 × α3 × α4`. -/
def toMultiset {α1 α2 α3 α4 : Type} (T : FourTree α1 α2 α3 α4) : Multiset (α1 × α2 × α3 × α4) :=
  match T with
  | .root trunks =>
    trunks.bind fun (trunk xT branches) =>
        branches.bind fun (branch xB twigs) =>
            twigs.bind fun (twig xTw leafs) =>
                leafs.map fun (leaf xL) => (xT, xB, xTw, xL)

/-!

## Cardinality of the tree

-/

/-- The cardinality of a `Twig` is the number of leafs. -/
def Twig.card {α3 α4 : Type} (T : Twig α3 α4) : Nat :=
  match T with
  | .twig _ leafs => leafs.card

/-- The cardinality of a `Branch` is the total number of leafs. -/
def Branch.card {α2 α3 α4 : Type} (T : Branch α2 α3 α4) : Nat :=
  match T with
  | .branch _ twigs => (twigs.map Twig.card).sum

/-- The cardinality of a `Trunk` is the total number of leafs. -/
def Trunk.card {α1 α2 α3 α4 : Type} (T : Trunk α1 α2 α3 α4) : Nat :=
  match T with
  | .trunk _ branches => (branches.map Branch.card).sum

/-- The cardinality of a `FourTree` is the total number of leafs. -/
def card {α1 α2 α3 α4 : Type} (T : FourTree α1 α2 α3 α4) : Nat :=
  match T with
  | .root trunks => (trunks.map Trunk.card).sum

lemma card_eq_toMultiset_card (T : FourTree α1 α2 α3 α4s) :
    T.card = T.toMultiset.card := by
  match T with
  | .root trunks =>
    simp only [card, toMultiset, Multiset.card_bind, Function.comp_apply, Multiset.card_map]
    rfl

/-!

## Membership of a FourTree

Based on the tree structure we can define a faster membership criterion, which
is equivalent to membership based on multisets.

-/

variable {α1 α2 α3 α4 : Type}

/-- An element of `a : α4` is a member of `Leaf α4` if the underlying element of the `Leaf`
  is `a`. -/
def Leaf.mem {α4} (T : Leaf α4) (x : α4) : Prop :=
  match T with
  | .leaf xs => xs = x

instance {α4} [DecidableEq α4] (T : Leaf α4) (x : α4) : Decidable (T.mem x) :=
  inferInstanceAs (Decidable (match T with | .leaf xs => xs = x))

/-- An element of `a : α3 × α4` is a member of `Twig α3 α4` if the underlying `α3` element of the
  `Twig` is `a.1` and `a.2` is a member of one of the `Leaf`. -/
def Twig.mem (T : Twig α3 α4) (x : α3 × α4) : Prop :=
  match T with
  | .twig xs leafs => xs = x.1 ∧ ∃ leaf ∈ leafs, leaf.mem x.2

instance {α3 α4} [DecidableEq α3] [DecidableEq α4] (T : Twig α3 α4) (x : α3 × α4) :
    Decidable (T.mem x) :=
  match T with
  | .twig _ leafs =>
    haveI : Decidable (∃ leaf ∈ leafs, leaf.mem x.2) := Multiset.decidableExistsMultiset
    instDecidableAnd

/-- An element of `a : α2 × α3 × α4` is a member of `Branch α2 α3 α4` if the underlying `α2`
  element of the `Branch` is `a.1` and `a.2` is a member of one of the `Twig`. -/
def Branch.mem (T : Branch α2 α3 α4) (x : α2 × α3 × α4) : Prop :=
  match T with
  | .branch xo twigs => xo = x.1 ∧ ∃ twig ∈ twigs, twig.mem x.2

instance [DecidableEq α2] [DecidableEq α3] [DecidableEq α4] (T : Branch α2 α3 α4)
    (x : α2 × α3 × α4) : Decidable (T.mem x) :=
  match T with
  | .branch _ twigs =>
    haveI : Decidable (∃ twig ∈ twigs, twig.mem x.2) := Multiset.decidableExistsMultiset
    instDecidableAnd

/-- An element of `a : α1 × α2 × α3 × α4` is a member of `Trunk α1 α2 α3 α4` if the underlying `α1`
  element of the `Trunk` is `a.1` and `a.2` is a member of one of the `Branch`. -/
def Trunk.mem (T : Trunk α1 α2 α3 α4) (x : α1 × α2 × α3 × α4) : Prop :=
  match T with
  | .trunk xo branches => xo = x.1 ∧ ∃ branch ∈ branches, branch.mem x.2

instance [DecidableEq α1] [DecidableEq α2] [DecidableEq α3] [DecidableEq α4]
    (T : Trunk α1 α2 α3 α4) (x : α1 × α2 × α3 × α4) : Decidable (T.mem x) :=
  match T with
  | .trunk _ branches =>
    haveI : Decidable (∃ branch ∈ branches, branch.mem x.2) := Multiset.decidableExistsMultiset
    instDecidableAnd

/-- An element of `a : α1 × α2 × α3 × α4` is a member of `FourTree α1 α2 α3 α4` if
  `a` is a member of one of the `Trunk`. -/
def mem (T : FourTree α1 α2 α3 α4) (x : α1 × α2 × α3 × α4) : Prop :=
  match T with
  | .root trunks => ∃ trunk ∈ trunks, trunk.mem x

instance [DecidableEq α1] [DecidableEq α2] [DecidableEq α3] [DecidableEq α4]
    (T : FourTree α1 α2 α3 α4) (x : α1 × α2 × α3 × α4) : Decidable (T.mem x) :=
  Multiset.decidableExistsMultiset

instance : Membership (α1 × α2 × α3 × α4) (FourTree α1 α2 α3 α4) where
  mem := mem

instance [DecidableEq α1] [DecidableEq α2] [DecidableEq α3] [DecidableEq α4]
    (T : FourTree α1 α2 α3 α4) (x : α1 × α2 × α3 × α4) : Decidable (x ∈ T) :=
  Multiset.decidableExistsMultiset

lemma mem_iff_mem_toMultiset (T : FourTree α1 α2 α3 α4) (x : α1 × α2 × α3 × α4) :
    x ∈ T ↔ x ∈ T.toMultiset := by
  match T with
  | .root trunks =>
  conv_lhs => simp [Membership.mem, mem]
  simp [toMultiset]
  constructor
  · intro h
    obtain ⟨trunk, hTrunkMem, hbranch⟩ := h
    refine ⟨trunk, hTrunkMem, ?_⟩
    match trunk with
    | .trunk qHd branches =>
    simp [Trunk.mem] at hbranch
    obtain ⟨hqHu, branch, hBranchMem, htwig⟩ := hbranch
    simp only
    refine ⟨branch, hBranchMem, ?_⟩
    match branch with
    | .branch qHu twigs =>
    simp [Branch.mem] at htwig
    obtain ⟨hqHu, twig, hTwigMem, hleaf⟩ := htwig
    simp only
    refine ⟨twig, hTwigMem, ?_⟩
    match twig with
    | .twig Q5 leafs =>
    simp [Twig.mem] at hleaf
    obtain ⟨hqHu, leaf, hLeafMem, hxs⟩ := hleaf
    simp only
    refine ⟨leaf, hLeafMem, ?_⟩
    match leaf with
    | .leaf Q10 =>
    simp [Leaf.mem] at hxs
    simp_all
  · intro h
    obtain ⟨trunk, hTrunkMem, ⟨branch, hbranchMem, ⟨twig, htwigMem, ⟨leaf, hleafMem, heq⟩⟩⟩⟩ := h
    use trunk
    subst heq
    refine ⟨hTrunkMem, ?_⟩
    simp [Trunk.mem]
    use branch
    refine ⟨hbranchMem, ?_⟩
    simp [Branch.mem]
    use twig
    refine ⟨htwigMem, ?_⟩
    simp [Twig.mem]
    use leaf
    refine ⟨hleafMem, ?_⟩
    simp [Leaf.mem]

lemma mem_of_parts {T : FourTree α1 α2 α3 α4} {C : α1 × α2 × α3 × α4}
    (trunk : Trunk α1 α2 α3 α4)
    (branch : Branch α2 α3 α4)
    (twig : Twig α3 α4) (leaf : Leaf α4)
    (trunk_mem : trunk ∈ T.1) (branch_mem : branch ∈ trunk.2)
    (twig_mem : twig ∈ branch.2) (leaf_mem : leaf ∈ twig.2)
    (heq : C = (trunk.1, branch.1, twig.1, leaf.1)) :
    C ∈ T := by
  rw [mem_iff_mem_toMultiset]
  simp [toMultiset]
  use trunk
  simp_all
  use branch
  simp_all
  use twig
  simp_all
  use leaf

end FourTree

end PhysLean
