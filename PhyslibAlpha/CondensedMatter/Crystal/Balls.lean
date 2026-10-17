/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Symmetry

/-!

# Balls in the bond graph of a crystal

The sites within a given number of bonds of a site, and their behaviour under symmetries.

## i. Overview

The *ball* of radius `n` around a site is the set of sites reached by at most `n` bonds. It is a
finite set, as every site has finitely many neighbours. A group acting on the sites and preserving
the bonds carries balls to balls. Balls give the finite regions on which a finite-range
interaction acts: the interactions of a region only reach its bond neighbours.

## ii. Key results

- `PeriodicGraph.ball` : the sites within `n` bonds of a site.
- `PeriodicGraph.mem_ball_add` : following `m` bonds and then `n` bonds stays within `m + n` bonds.
- `PeriodicGraph.mem_ball_smul_iff` : bond preserving group actions carry balls to balls.

## iii. Table of contents

- A. Balls

## iv. References

* None.

-/

@[expose] public section

namespace CondensedMatter.Crystal

/-! ## A. Balls -/

namespace PeriodicGraph

variable {G : Type*} [AddGroup G] {C : Crystal G} [DecidableEq C.Site] (g : PeriodicGraph C)

/-- The sites within `n` bonds of a site. -/
def ball : ℕ → C.Site → Finset C.Site
  | 0, x => {x}
  | n + 1, x => ball n x ∪ (ball n x).biUnion g.neighbors

lemma self_mem_ball (n : ℕ) (x : C.Site) : x ∈ g.ball n x := by
  induction n with
  | zero => simp [ball]
  | succ n ih => exact Finset.mem_union_left _ ih

lemma ball_mono {m n : ℕ} (h : m ≤ n) (x : C.Site) : g.ball m x ⊆ g.ball n x := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans Finset.subset_union_left

/-- Following `m` bonds and then `n` bonds stays within `m + n` bonds. -/
lemma mem_ball_add {m n : ℕ} {a b c : C.Site} (hb : b ∈ g.ball n a) (hc : c ∈ g.ball m b) :
    c ∈ g.ball (m + n) a := by
  induction m generalizing c with
  | zero =>
    simp only [ball, Finset.mem_singleton] at hc
    subst hc
    simpa using hb
  | succ m ih =>
    simp only [ball, Finset.mem_union, Finset.mem_biUnion] at hc
    rcases hc with hc | ⟨y, hy, hcy⟩
    · exact g.ball_mono (by omega) a (ih hc)
    · rw [show m + 1 + n = (m + n) + 1 by omega]
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨y, ih hy, hcy⟩)

variable {H : Type*} [Group H] [MulAction H C.Site]

omit [DecidableEq C.Site] in
/-- A group action preserving the bonds carries the neighbours of a site to the neighbours of
its image. -/
lemma mem_neighbors_smul_iff (hH : ∀ (h : H) (x y : C.Site),
    g.toSimpleGraph.Adj (h • x) (h • y) ↔ g.toSimpleGraph.Adj x y) (h : H) (x y : C.Site) :
    h • y ∈ g.neighbors (h • x) ↔ y ∈ g.neighbors x := by
  rw [mem_neighbors, mem_neighbors, hH]

/-- A group action preserving the bonds carries balls to balls. -/
lemma mem_ball_smul_iff (hH : ∀ (h : H) (x y : C.Site),
    g.toSimpleGraph.Adj (h • x) (h • y) ↔ g.toSimpleGraph.Adj x y) (h : H) (n : ℕ)
    (x y : C.Site) : h • y ∈ g.ball n (h • x) ↔ y ∈ g.ball n x := by
  induction n generalizing y with
  | zero => simp [ball]
  | succ n ih =>
    simp only [ball, Finset.mem_union, Finset.mem_biUnion, ih]
    constructor
    · rintro (h1 | ⟨z, hz, hyz⟩)
      · exact Or.inl h1
      · refine Or.inr ⟨h⁻¹ • z, ?_, ?_⟩
        · rw [← ih, smul_inv_smul]; exact hz
        · have := (g.mem_neighbors_smul_iff hH h (h⁻¹ • z) y).1
          rw [smul_inv_smul] at this
          exact this hyz
    · rintro (h1 | ⟨z, hz, hyz⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨h • z, (ih _).2 hz, (g.mem_neighbors_smul_iff hH h z y).2 hyz⟩

end PeriodicGraph

end CondensedMatter.Crystal
