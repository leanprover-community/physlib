/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.Axis
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
/-!
# Boost weights of representations of `SL(2,ℂ)`

## i. Overview

An element of a representation of `SL(2,ℂ)` has boost weight `k` along the `i`-th spatial
axis when the one-parameter boost family along that axis scales it by `t ^ k`;
`boostWeightSubmodule rep i k` collects these elements. Weights add under multiplication,
and the weight spaces sit in eigenspaces of a single boost at distinct eigenvalues, so they
are independent. That is all the Standard Model needs of them: an invariant of the group has
boost weight zero along every axis, so a weight-zero vector of a join of weight spaces lies
in the weight-zero one.

A `WeightDecomposition` records a finitely supported family of subspaces of pure boost
weight joining to a given submodule; it is transported along equalities and joined here. The
product of two decompositions, which needs only multiplicativity of the representation, is
built where it is used, in `CovAlgebraRealization/YukawaSector/MassDimLTEight.lean`, together
with the parity argument that a submodule of odd boost weights carries no invariant.

## ii. Key results

- `boostWeightSubmodule` : the weight-`k` space along the `i`-th axis.
- `mul_mem_boostWeightSubmodule` : weights add under multiplication.
- `boostWeightSubmodule_iSupIndep` : the weight spaces are independent.
- `mem_boostWeightSubmodule_zero_of_invariant` and `mem_of_mem_iSup_of_boostWeight_zero` :
  an invariant has weight zero, and lies in the weight-zero term of any join of weight
  spaces containing it.
- `WeightDecomposition`, with its transport `copy` and join `sup`.

## iii. Table of contents

- A. Boost weights
- B. Independence of the weight spaces
- C. Weight decompositions of submodules

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups

/-!

## A. Boost weights

-/

namespace BoostWeight

variable {K : Type*} [Field K] [Algebra ℝ K]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable {i : Fin 3}

private lemma algebraMap_ne_zero {t : ℝ} (ht : t ≠ 0) : (algebraMap ℝ K t) ≠ 0 :=
  fun h => ht ((algebraMap ℝ K).injective (by simpa using h))

/-- The weight-`w` space of a representation along the `i`-th axis: the vectors scaling by
  `t ^ w` under the boost along that axis at parameter `t`. -/
def boostWeightSubmodule (rep : Representation K SL(2,ℂ) M) (i : Fin 3) (w : ℤ) :
    Submodule K M where
  carrier := {x | ∀ (t : ℝ) (ht : t ≠ 0),
    rep (Lorentz.SL2C.boostAxis i t ht) x = (algebraMap ℝ K t) ^ w • x}
  add_mem' {a b} ha hb := fun t ht => by rw [map_add, ha t ht, hb t ht, smul_add]
  zero_mem' := fun t ht => by rw [map_zero, smul_zero]
  smul_mem' c x hx := fun t ht => by rw [map_smul, hx t ht, smul_comm]

lemma mem_boostWeightSubmodule {rep : Representation K SL(2,ℂ) M} {i : Fin 3} {w : ℤ} {x : M} :
    x ∈ boostWeightSubmodule rep i w ↔ ∀ (t : ℝ) (ht : t ≠ 0),
      rep (Lorentz.SL2C.boostAxis i t ht) x = (algebraMap ℝ K t) ^ w • x := Iff.rfl

variable {A : Type*} [Ring A] [Algebra K A]

/-- Weights add under multiplication, when the representation is multiplicative. -/
lemma mul_mem_boostWeightSubmodule {rep : Representation K SL(2,ℂ) A}
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : A), rep Λ (x * y) = rep Λ x * rep Λ y)
    {a b : ℤ} {x y : A} (hx : x ∈ boostWeightSubmodule rep i a)
    (hy : y ∈ boostWeightSubmodule rep i b) :
    x * y ∈ boostWeightSubmodule rep i (a + b) := by
  intro t ht
  rw [hmul, hx t ht, hy t ht, smul_mul_smul_comm, zpow_add₀ (algebraMap_ne_zero (K := K) ht)]

/-!

## B. Independence of the weight spaces

The weight-`k` space lies in the `2 ^ k` eigenspace of the boost at parameter two, and
distinct weights give distinct eigenvalues, so the weight spaces are independent. An
invariant of the group has weight zero along every axis; written as a sum of vectors of
definite weight it is therefore the weight-zero term, and a weight-zero vector of a join of
weight spaces lies in the weight-zero one.

-/

/-- The weight space of weight `k` sits inside the `2 ^ k` eigenspace of the boost at
  parameter two. -/
lemma boostWeightSubmodule_le_eigenspace (rep : Representation K SL(2,ℂ) M) (k : ℤ) :
    boostWeightSubmodule rep i k ≤
      Module.End.eigenspace (rep (Lorentz.SL2C.boostAxis i 2 two_ne_zero))
      ((algebraMap ℝ K 2) ^ k) := by
  intro x hx
  rw [Module.End.mem_eigenspace_iff]
  exact hx 2 two_ne_zero

private lemma zpow_algebraMap_two_injective :
    Function.Injective (fun k : ℤ => ((algebraMap ℝ K 2) ^ k)) := by
  intro a b hab
  simp only [← map_zpow₀] at hab
  exact zpow_right_injective₀ (by norm_num) (by norm_num) ((algebraMap ℝ K).injective hab)

/-- The weight spaces are independent: a decomposition into homogeneous parts is unique
  when it exists. -/
lemma boostWeightSubmodule_iSupIndep (rep : Representation K SL(2,ℂ) M) :
    iSupIndep (boostWeightSubmodule rep i) :=
  ((Module.End.eigenspaces_iSupIndep
      (rep (Lorentz.SL2C.boostAxis i 2 two_ne_zero) : Module.End K M)).comp
    zpow_algebraMap_two_injective).mono fun k => boostWeightSubmodule_le_eigenspace rep k

/-- A vector fixed by the whole group has boost weight zero along every axis. -/
lemma mem_boostWeightSubmodule_zero_of_invariant {rep : Representation K SL(2,ℂ) M} {x : M}
    (hinv : ∀ g : SL(2,ℂ), rep g x = x) (i : Fin 3) :
    x ∈ boostWeightSubmodule rep i 0 := by
  rw [mem_boostWeightSubmodule]
  intro t ht
  rw [hinv, zpow_zero, one_smul]

/-- Vectors of distinct boost weights adding to zero are each zero. -/
lemma eq_zero_of_sum_mem_boostWeightSubmodule {rep : Representation K SL(2,ℂ) M}
    {s : Finset ℤ} {w : ℤ → M} (hw : ∀ m ∈ s, w m ∈ boostWeightSubmodule rep i m)
    (hsum : ∑ m ∈ s, w m = 0) : ∀ m ∈ s, w m = 0 := by
  intro m₀ hm₀
  refine Submodule.disjoint_def.1
    (iSupIndep_def.1 (boostWeightSubmodule_iSupIndep rep) m₀) (w m₀) (hw m₀ hm₀) ?_
  have h : w m₀ = -∑ m ∈ s.erase m₀, w m :=
    eq_neg_of_add_eq_zero_left (by rw [Finset.add_sum_erase s w hm₀]; exact hsum)
  rw [h]
  exact neg_mem (sum_mem fun m hm => Submodule.mem_iSup_of_mem m
    (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hm)
      (hw m (Finset.mem_of_mem_erase hm))))

/-- A weight-zero vector written as a sum of definite weights equals the weight-zero
  term. -/
lemma eq_component_zero_of_mem_boostWeightSubmodule {rep : Representation K SL(2,ℂ) M}
    {s : Finset ℤ} {w : ℤ → M} {x : M} (hx : x ∈ boostWeightSubmodule rep i 0)
    (hw : ∀ m ∈ s, w m ∈ boostWeightSubmodule rep i m) (h0 : (0 : ℤ) ∈ s)
    (hsum : x = ∑ m ∈ s, w m) : x = w 0 := by
  have hv : ∀ m ∈ s, Function.update w 0 (w 0 - x) m ∈ boostWeightSubmodule rep i m := by
    intro m hm
    by_cases h : m = 0
    · subst h
      rw [Function.update_self]
      exact sub_mem (hw 0 h0) hx
    · rw [Function.update_of_ne h]
      exact hw m hm
  have hsum0 : ∑ m ∈ s, Function.update w 0 (w 0 - x) m = 0 := by
    rw [Finset.sum_update_of_mem h0, hsum, ← Finset.add_sum_erase s w h0, Finset.erase_eq]
    abel
  have h := eq_zero_of_sum_mem_boostWeightSubmodule hv hsum0 0 h0
  rw [Function.update_self] at h
  exact (sub_eq_zero.1 h).symm

/-- If each `S m` lies in the weight-`m` space, a weight-zero vector of their join lies in
  `S 0`. -/
lemma mem_of_mem_iSup_of_boostWeight_zero {rep : Representation K SL(2,ℂ) M} {i : Fin 3}
    {S : ℤ → Submodule K M} (hS : ∀ m : ℤ, S m ≤ boostWeightSubmodule rep i m) {x : M}
    (hx : x ∈ ⨆ m, S m) (h0 : x ∈ boostWeightSubmodule rep i 0) : x ∈ S 0 := by
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hx
  have hkey := eq_component_zero_of_mem_boostWeightSubmodule (i := i)
    (s := insert 0 f.support) (w := fun m => f m) h0
    (fun m _ => hS m (hf m)) (Finset.mem_insert_self 0 _) ?_
  · rw [hkey]
    exact hf 0
  · rw [Finsupp.sum]
    by_cases h : (0 : ℤ) ∈ f.support
    · rw [Finset.insert_eq_self.2 h]
    · rw [Finset.sum_insert h, Finsupp.notMem_support_iff.1 h, zero_add]

/-!

## C. Weight decompositions of submodules

-/

/-- A weight decomposition of a submodule `V`: a finitely supported family of subspaces of
  pure boost weight whose supremum is `V`. -/
structure WeightDecomposition (rep : Representation K SL(2,ℂ) M) (i : Fin 3)
    (V : Submodule K M) where
  /-- The weight-`k` piece of the decomposition. -/
  piece : ℤ → Submodule K M
  /-- The finite set of weights that occur. -/
  supp : Finset ℤ
  piece_le : ∀ k, piece k ≤ boostWeightSubmodule rep i k
  piece_eq_bot : ∀ k ∉ supp, piece k = ⊥
  iSup_piece : (⨆ k, piece k) = V

namespace WeightDecomposition

variable {rep : Representation K SL(2,ℂ) M} {V₁ V₂ : Submodule K M}

/-- Transport a weight decomposition along an equality of submodules. -/
def copy (d₁ : WeightDecomposition rep i V₁) (hV : V₁ = V₂) : WeightDecomposition rep i V₂ where
  piece := d₁.piece
  supp := d₁.supp
  piece_le := d₁.piece_le
  piece_eq_bot := d₁.piece_eq_bot
  iSup_piece := d₁.iSup_piece.trans hV

@[simp]
lemma copy_piece (d₁ : WeightDecomposition rep i V₁) (hV : V₁ = V₂) (k : ℤ) :
    (d₁.copy hV).piece k = d₁.piece k := rfl

/-- The join of two weight decompositions along the same axis: the weight-`k` piece of the
  join is the join of the weight-`k` pieces. -/
def sup (d₁ : WeightDecomposition rep i V₁) (d₂ : WeightDecomposition rep i V₂) :
    WeightDecomposition rep i (V₁ ⊔ V₂) where
  piece k := d₁.piece k ⊔ d₂.piece k
  supp := d₁.supp ∪ d₂.supp
  piece_le k := sup_le (d₁.piece_le k) (d₂.piece_le k)
  piece_eq_bot k hk := by
    rw [d₁.piece_eq_bot k fun hk' => hk (Finset.mem_union_left _ hk'),
      d₂.piece_eq_bot k fun hk' => hk (Finset.mem_union_right _ hk'), bot_sup_eq]
  iSup_piece := by rw [iSup_sup_eq, d₁.iSup_piece, d₂.iSup_piece]

@[simp]
lemma sup_piece (d₁ : WeightDecomposition rep i V₁) (d₂ : WeightDecomposition rep i V₂)
    (k : ℤ) : (d₁.sup d₂).piece k = d₁.piece k ⊔ d₂.piece k := rfl

end WeightDecomposition

end BoostWeight

end Lorentz

end
