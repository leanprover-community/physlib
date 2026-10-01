/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.ForMathlib.DataStructures.FourTree.Basic
/-!

## Unique maps for `FourTree`

We define the `uniqueMap4` and `uniqueMap3` functions for `FourTree`.
For a given `f : α4 → α4` or `f : α3 → α3`, these functions the elements of a `FourTree`,
and leave only new elements which are not already present in the tree (if
the tree has no duplicates).

-/

@[expose] public section

namespace Physlib

namespace FourTree

/-!

## uniqueMap4

-/

section uniqueMap4

variable {α1 α2 α3 α4 : Type} [DecidableEq α4] (f : α4 → α4)

/-- Given a map `f : α4 → α4` the map from `Leaf α4 → Leaf α4` mapping the underlying
  elements. -/
def Leaf.uniqueMap4 : Leaf α4 → Leaf α4
  | .leaf x => .leaf (f x)

/-- Given a map `f : α4 → α4` the map from `Twig α3 α4 → Twig α3 α4` mapping the underlying
  leafs and deleting any that appear in the original Twig. -/
def Twig.uniqueMap4 (T : Twig α3 α4) : Twig α3 α4 :=
  match T with
  | .twig xs leafs =>
    let leafFinst := leafs.map (fun l => match l with
      | .leaf ys => ys)
    let sub : Multiset α4 := leafFinst.filterMap (fun ys =>
      if ¬ f ys ∈ leafFinst then
        some (f ys)
      else
        none)
    .twig xs (sub.map (fun ys => .leaf ys))

/-- Given a map `f : α4 → α4` the map from `Branch α2 α3 α4 → Branch α2 α3 α4`
  mapping the underlying leafs and deleting any that appear in the original Twig. -/
def Branch.uniqueMap4 (T : Branch α2 α3 α4) :
    Branch α2 α3 α4:=
  match T with
  | .branch xo twigs =>
    .branch xo (twigs.map fun ts => (Twig.uniqueMap4 f ts))

/-- Given a map `f : α4 → α4` the map from `Trunk α1 α2 α3 α4 → Trunk α1 α2 α3 α4`
  mapping the underlying leafs and deleting any that appear in the original Twig. -/
def Trunk.uniqueMap4 (T : Trunk α1 α2 α3 α4) : Trunk α1 α2 α3 α4 :=
  match T with
  | .trunk xo branches =>
    .trunk xo (branches.map fun bs => (Branch.uniqueMap4 f bs))

/-- Given a map `f : α4 → α4` the map from `FourTree α1 α2 α3 α4 → FourTree α1 α2 α3 α4`
  mapping the underlying leafs and deleting any that appear in the original twig of that
  leaf. -/
def uniqueMap4 (T : FourTree α1 α2 α3 α4) : FourTree α1 α2 α3 α4 :=
  match T with
  | .root trunks =>
    .root (trunks.map fun ts => (ts.uniqueMap4 f))

lemma map_mem_uniqueMap4 {T : FourTree α1 α2 α3 α4}
    (x : α1 × α2 × α3 × α4) (hx : x ∈ T) (f : α4 → α4) :
    (x.1, x.2.1, x.2.2.1, f x.2.2.2) ∈ T.uniqueMap4 f ∨
    (x.1, x.2.1, x.2.2.1, f x.2.2.2) ∈ T := by
  by_cases hnotMem : (x.1, x.2.1, x.2.2.1, f x.2.2.2) ∈ T
  · simp [hnotMem]
  left
  simp [mem_iff_mem_toMultiset, toMultiset] at hx
  obtain ⟨trunk, htrunk, branch, hbranch, twig, htwig, leaf, hleaf, heq⟩ := hx
  apply mem_of_parts (trunk.uniqueMap4 f) (branch.uniqueMap4 f) (twig.uniqueMap4 f)
    (.leaf (f leaf.1))
  · exact Multiset.mem_map_of_mem _ htrunk
  · exact Multiset.mem_map_of_mem _ hbranch
  · exact Multiset.mem_map_of_mem _ htwig
  · simp [Twig.uniqueMap4, -existsAndEq]
    refine ⟨leaf, hleaf, ?_, rfl⟩
    intro y hy hn
    exact hnotMem
      (mem_of_parts trunk branch twig y htrunk hbranch htwig hy (by subst heq; simp [hn]))
  · subst heq
    simp [Trunk.uniqueMap4, Branch.uniqueMap4, Twig.uniqueMap4]

lemma exists_of_mem_uniqueMap4 {T : FourTree α1 α2 α3 α4}
    (C : α1 × α2 × α3 × α4) (h : C ∈ T.uniqueMap4 f) :
    ∃ qHd qHu Q5 Q10, C = (qHd, qHu, Q5, f Q10) ∧ (qHd, qHu, Q5, Q10) ∈ T := by
  rw [mem_iff_mem_toMultiset] at h
  simp [toMultiset] at h
  obtain ⟨trunkI, trunkI_mem, branchI, branchI_mem, twigI, twigI_mem,
    leafI, leafI_mem, heq⟩ := h
  -- obtaining trunkT
  simp [uniqueMap4] at trunkI_mem
  obtain ⟨trunkT, trunkT_mem, rfl⟩ := trunkI_mem
  -- obtaining branchT
  simp [Trunk.uniqueMap4] at branchI_mem
  obtain ⟨branchT, branchT_mem, rfl⟩ := branchI_mem
  -- obtaining twigT
  simp only [Branch.uniqueMap4, Multiset.mem_map] at twigI_mem
  obtain ⟨twigT, twigT_mem, rfl⟩ := twigI_mem
  -- obtaining leafT
  simp only [Twig.uniqueMap4, Multiset.mem_map, Multiset.mem_filterMap,
    Option.ite_none_right_eq_some, Option.some.injEq, exists_exists_and_eq_and] at leafI_mem
  obtain ⟨Q10, ⟨leafT, leafT_mem, hQ10⟩, hPresent⟩ := leafI_mem
  subst heq
  refine ⟨trunkT.1, branchT.1, twigT.1, leafT.1, ?_,
    mem_of_parts trunkT branchT twigT leafT trunkT_mem branchT_mem twigT_mem leafT_mem rfl⟩
  rw [← hPresent]
  simp [Trunk.uniqueMap4, Branch.uniqueMap4, Twig.uniqueMap4, hQ10.2]

end uniqueMap4

/-!

## uniqueMap3

-/

section uniqueMap3

variable {α1 α2 α3 α4 : Type} [DecidableEq α2] [DecidableEq α3] [DecidableEq α4] (f : α3 → α3)

/-- Given a map `f : α3 → α3` the map from `Twig α3 α4 → Twig α3 α4` mapping the underlying
  first value of the twig. -/
def Twig.uniqueMap3 (T : Twig α3 α4) : Twig α3 α4 :=
  match T with
  | .twig xs leafs => .twig (f xs) leafs

/-- Given a map `f : α3 → α3` the map from `Branch α2 α3 α4 → Branch α2 α3 α4` mapping the
  underlying first value of the twig, and deleting any new leafs that appeared
  in the old branch. -/
def Branch.uniqueMap3 (T : Branch α2 α3 α4) : Branch α2 α3 α4 :=
  match T with
  | .branch qHu twigs =>
    let insertTwigs := twigs.map (fun (.twig Q5 leafs) => Twig.twig (f Q5)
      (leafs.filter (fun (.leaf Q10) => ¬ Branch.mem (.branch qHu twigs)
      (qHu, (f Q5), Q10))))
    .branch qHu insertTwigs

/-- Given a map `f : α3 → α3` the map from `Trunk α1 α2 α3 α4 → Trunk α1 α2 α3 α4` mapping the
  underlying first value of the twig, and deleting any new leafs that appeared
  in the old branch. -/
def Trunk.uniqueMap3 (T : Trunk α1 α2 α3 α4) : Trunk α1 α2 α3 α4 :=
  match T with
  | .trunk qHd branches =>
    .trunk qHd (branches.map fun bs => (bs.uniqueMap3 f))

/-- Given a map `f : α3 → α3` the map from `FourTree α1 α2 α3 α4 → FourTree α1 α2 α3 α4` mapping the
  underlying first value of the twig, and deleting any new leafs that appeared
  in the old branch. -/
def uniqueMap3 (T : FourTree α1 α2 α3 α4) : FourTree α1 α2 α3 α4:=
  match T with
  | .root trunks =>
    .root (trunks.map fun ts => (ts.uniqueMap3 f))

lemma map_mem_uniqueMap3 {T : FourTree α1 α2 α3 α4}
    (x : α1 × α2 × α3 × α4) (hx : x ∈ T) (f : α3 → α3) :
    (x.1, x.2.1, f x.2.2.1, x.2.2.2) ∈ T.uniqueMap3 f ∨
    (x.1, x.2.1, f x.2.2.1, x.2.2.2) ∈ T := by
  by_cases hnotMem : (x.1, x.2.1, f x.2.2.1, x.2.2.2) ∈ T
  · simp [hnotMem]
  left
  simp [mem_iff_mem_toMultiset, toMultiset] at hx
  obtain ⟨trunk, htrunk, branch, hbranch, twig, htwig, leaf, hleaf, heq⟩ := hx
  match branch with
  | .branch qHu twigs =>
  match twig with
  | .twig Q5 leafs =>
  apply mem_of_parts (trunk.uniqueMap3 f) ((Branch.branch qHu twigs).uniqueMap3 f)
    (.twig (f Q5) (leafs.filter (fun (.leaf Q10) =>
      ¬ Branch.mem (.branch qHu twigs) (qHu, f Q5, Q10)))) leaf
  · exact Multiset.mem_map_of_mem _ htrunk
  · exact Multiset.mem_map_of_mem _ hbranch
  · exact Multiset.mem_map_of_mem _ htwig
  · refine Multiset.mem_filter.mpr ⟨hleaf, ?_⟩
    show ¬ (Branch.branch qHu twigs).mem (qHu, f Q5, leaf.1)
    by_contra hn
    apply hnotMem
    subst heq
    exact ⟨trunk, htrunk, rfl, .branch qHu twigs, hbranch, hn⟩
  · subst heq
    simp [Trunk.uniqueMap3, Branch.uniqueMap3]

lemma exists_of_mem_uniqueMap3 {T : FourTree α1 α2 α3 α4}
    (C : α1 × α2 × α3 × α4) (h : C ∈ T.uniqueMap3 f) :
    ∃ qHd qHu Q5 Q10, C = (qHd, qHu, f Q5, Q10) ∧
      (qHd, qHu, Q5, Q10) ∈ T := by
  rw [mem_iff_mem_toMultiset] at h
  simp [toMultiset] at h
  obtain ⟨trunkI, trunkI_mem, branchI, branchI_mem, twigI, twigI_mem,
    leafI, leafI_mem, heq⟩ := h
  -- obtaining trunkT
  simp [uniqueMap3] at trunkI_mem
  obtain ⟨trunkT, trunkT_mem, rfl⟩ := trunkI_mem
  -- obtaining branchT
  simp [Trunk.uniqueMap3] at branchI_mem
  obtain ⟨branchT, branchT_mem, rfl⟩ := branchI_mem
  -- obtaining twigT
  simp only [Branch.uniqueMap3, Multiset.mem_map] at twigI_mem
  obtain ⟨twigT, twigT_mem, rfl⟩ := twigI_mem
  -- obtaining leafT
  simp at leafI_mem
  obtain ⟨leftI_mem, h_not_mem⟩ := leafI_mem
  subst heq
  refine ⟨trunkT.1, branchT.1, twigT.1, leafI.1, ?_,
    mem_of_parts trunkT branchT twigT leafI trunkT_mem branchT_mem twigT_mem leftI_mem rfl⟩
  simp [Trunk.uniqueMap3, Branch.uniqueMap3]

end uniqueMap3

end FourTree

end Physlib
