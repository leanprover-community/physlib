/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.Mathematics.LadderSystem.Basic
public import Mathlib.Data.List.Perm.Lattice
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Lie.Submodule
/-!

# Vacuum states and creation-operator words

## i. Overview

A vacuum `Ω` of a `LadderSystem` is a nonzero vector killed by every annihilation operator. This
file develops creation-operator words `acᵢ₁acᵢ₂⋯acᵢₙΩ` and the excitation-number sector they span,
`vacuumSpan`. This sector is bundled as a `gl(d)` Lie submodule. Its occupation-number basis is
constructed in `OccupationBasis.lean`, and its irreducibility is proved in `Irreducibility.lean`.

## ii. Key results

Definitions:
- `LadderSystem.HasVacuum` : `Ω` is nonzero and killed by every `a i`.
- `LadderSystem.word` : a word of creation operators applied to a vector.
- `LadderSystem.vacuumSpan` : the span of all length-`n` words over a vacuum -- the
    `n`-particle sector.
- `LadderSystem.vacuumSpanLieSubmodule` : `vacuumSpan`, bundled as a `gl(d)` Lie submodule.

Theorems:
- `LadderSystem.word_perm` : a word depends only on the multiset of colors it represents.
- `LadderSystem.word_peel` : `aᵢ` applied to a word removes one occurrence of color `i`, scaled
    by its count.
- `LadderSystem.E_word`, `LadderSystem.N_word` : how `E i j`/`N i` act on a word.
- `LadderSystem.E_mem_vacuumSpan` : `vacuumSpan` is closed under every `gl(d)` generator `E i j`.

## iii. Table of contents

- A. Vacuum states
- B. Words
- C. The excitation-number sector
  - C.1. `gl(d)`-invariance

## iv. References

* None.
-/

@[expose] public section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LadderSystem

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {d : ℕ} (L : LadderSystem K V d)

/-!

## A. Vacuum states

-/

/-- A vacuum: a nonzero vector killed by every annihilation operator. -/
structure HasVacuum (Ω : V) : Prop where
  /-- A vacuum is nonzero. -/
  ne_zero : Ω ≠ 0
  /-- A vacuum is killed by every annihilation operator. -/
  ann : ∀ i, L.a i Ω = 0

variable {L}

/-!

## B. Words

-/

/-- A word of creation operators applied to a fixed vector. -/
def word (L : LadderSystem K V d) (v : List (Fin d)) (x : V) : V :=
  (v.map L.ac).prod x

lemma word_cons (L : LadderSystem K V d) (i : Fin d) (v : List (Fin d)) (x : V) :
    L.word (i :: v) x = L.ac i (L.word v x) := by
  simp [word, Module.End.mul_apply]

/-- A word depends only on the multiset of colors it represents, not their order. -/
lemma word_perm (L : LadderSystem K V d) {v v' : List (Fin d)} (h : v.Perm v') (x : V) :
    L.word v x = L.word v' x := by
  induction h with
  | nil => rfl
  | cons i _ ih => rw [word_cons, word_cons, ih]
  | swap i j v =>
    have hcomm : (L.ac i * L.ac j : Module.End K V) = L.ac j * L.ac i := by
      have h := L.comm_ac_ac i j
      rwa [LieRing.of_associative_ring_bracket, sub_eq_zero] at h
    simp only [word_cons]
    exact congrArg (fun f : Module.End K V => f (L.word v x)) hcomm.symm
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

/-- Peeling: `a i` applied to a word removes one occurrence of color `i`, scaled by its count. -/
lemma word_peel (L : LadderSystem K V d) (i : Fin d) {x : V} (hx : L.a i x = 0) :
    ∀ v : List (Fin d), L.a i (L.word v x) = (v.count i) • L.word (v.erase i) x
  | [] => by simp [word, hx]
  | c :: v' => by
    have hcomm : L.a i * L.ac c
        = L.ac c * L.a i + (if i = c then (1 : Module.End K V) else 0) := by
      have h := L.comm_a_ac i c
      rw [LieRing.of_associative_ring_bracket] at h
      exact sub_eq_iff_eq_add'.mp h
    have step : L.a i (L.word (c :: v') x)
        = L.ac c (L.a i (L.word v' x)) + (if i = c then L.word v' x else 0) := by
      rw [word_cons]
      have happly := congrArg (fun f : Module.End K V => f (L.word v' x)) hcomm
      simpa [Module.End.mul_apply, apply_ite (fun f : Module.End K V => f (L.word v' x))]
        using happly
    rw [step, word_peel L i hx v']
    by_cases hic : i = c
    · subst hic
      rw [ite_eq_left rfl, List.count_cons_self, List.erase_cons_head]
      by_cases hmem : i ∈ v'
      · have hperm : L.word v' x = L.word (i :: v'.erase i) x :=
          word_perm L (List.perm_cons_erase hmem) x
        rw [succ_nsmul, map_nsmul, ← word_cons, ← hperm]
      · have hcount : v'.count i = 0 := List.count_eq_zero_of_not_mem hmem
        simp [hcount]
    · rw [ite_eq_right hic, List.count_cons_of_ne (Ne.symm hic),
        List.erase_cons_tail (by simpa using Ne.symm hic), map_nsmul, ← word_cons, add_zero]

/-- How `E i j` acts on a word: removes one occurrence of `j`, adds one of `i`, scaled by `j`'s
count. -/
lemma E_word (L : LadderSystem K V d) {x : V} (hx : ∀ i, L.a i x = 0) (i j : Fin d)
    (v : List (Fin d)) :
    (L.E i j) (L.word v x) = (v.count j) • L.word (i :: v.erase j) x := by
  show (L.ac i * L.a j) (L.word v x) = _
  rw [Module.End.mul_apply, word_peel L j (hx j) v, map_nsmul, ← word_cons]

/-- Words are eigenvectors of the number operator, with eigenvalue their own color count. -/
lemma N_word (L : LadderSystem K V d) {x : V} (hx : ∀ i, L.a i x = 0) (i : Fin d)
    (v : List (Fin d)) : (L.N i) (L.word v x) = (v.count i) • L.word v x := by
  rw [N, E_word L hx i i v]
  by_cases hmem : i ∈ v
  · rw [← word_perm L (List.perm_cons_erase hmem) x]
  · simp [List.count_eq_zero_of_not_mem hmem]

/-!

## C. The excitation-number sector

-/

/-- The canonical word representing a count function `α`: `α c` copies of color `c`, in
increasing order. -/
def countWord (d : ℕ) (α : Fin d → ℕ) : List (Fin d) :=
  (List.finRange d).flatMap (fun c => List.replicate (α c) c)

/-- `countWord α` has exactly `α i` copies of color `i`. -/
lemma count_countWord {d : ℕ} (α : Fin d → ℕ) (i : Fin d) :
    (countWord d α).count i = α i := by
  have key : ∀ (l : List (Fin d)), l.Nodup → i ∈ l →
      (l.flatMap (fun c => List.replicate (α c) c)).count i = α i := by
    intro l
    induction l with
    | nil => intro _ hi; exact absurd hi List.not_mem_nil
    | cons c l' ih =>
      intro hnodup hi
      obtain ⟨hcl', hnodup'⟩ := List.nodup_cons.mp hnodup
      rw [List.flatMap_cons, List.count_append]
      rcases List.mem_cons.mp hi with hic | hil'
      · subst hic
        have hzero : (l'.flatMap (fun c => List.replicate (α c) c)).count i = 0 := by
          apply List.count_eq_zero_of_not_mem
          intro hmem
          obtain ⟨c', hc', hmem'⟩ := List.mem_flatMap.mp hmem
          exact hcl' ((List.eq_of_mem_replicate hmem') ▸ hc')
        rw [List.count_replicate, hzero]
        simp
      · have hine : i ≠ c := fun h => hcl' (h ▸ hil')
        rw [List.count_replicate, ite_eq_right (by simpa using hine.symm), zero_add]
        exact ih hnodup' hil'
  exact key (List.finRange d) (List.nodup_finRange d) (List.mem_finRange i)

/-- A word's length is the sum of its per-color counts. -/
lemma sum_count_eq_length {d : ℕ} : ∀ v : List (Fin d), (∑ c : Fin d, v.count c) = v.length
  | [] => by simp
  | a :: v' => by
    have hcount : ∀ c : Fin d, (a :: v').count c = v'.count c + (if a = c then 1 else 0) := by
      intro c
      rw [List.count_cons]
      simp only [beq_iff_eq]
    have hone : (∑ c : Fin d, if a = c then (1 : ℕ) else 0) = 1 := by
      rw [Finset.sum_eq_single a (fun b _ hb => ite_eq_right (Ne.symm hb))
        (fun h => absurd (Finset.mem_univ a) h)]
      simp
    simp only [hcount, List.length_cons]
    rw [Finset.sum_add_distrib, sum_count_eq_length v', hone]

/-- The `n`-th excitation-number sector generated by a vacuum: the span of all length-`n`
creation words. -/
def vacuumSpan (L : LadderSystem K V d) (Ω : V) (n : ℕ) : Submodule K V :=
  Submodule.span K (Set.range fun w : Fin n → Fin d => L.word (List.ofFn w) Ω)

lemma exists_ofFn_eq_of_length_eq {l : List (Fin d)} {n : ℕ} (h : l.length = n) :
    ∃ w : Fin n → Fin d, List.ofFn w = l := by
  refine ⟨fun i => l.get (Fin.cast h.symm i), List.ext_get_iff.mpr ⟨by simp [h], ?_⟩⟩
  intro k h1 h2
  rw [List.get_ofFn]
  rfl

/-- Any word of the right length lies in `vacuumSpan`. -/
lemma word_mem_vacuumSpan_of_length_eq (L : LadderSystem K V d) (Ω : V) {n : ℕ}
    {l : List (Fin d)} (h : l.length = n) : L.word l Ω ∈ vacuumSpan L Ω n := by
  obtain ⟨w, rfl⟩ := exists_ofFn_eq_of_length_eq h
  exact Submodule.subset_span ⟨w, rfl⟩

/-!

### C.1. `gl(d)`-invariance

-/

/-- `E`-invariance of a submodule extends to full `gl(d)`-invariance, by linearity off the
matrix-unit basis. -/
lemma forall_toGlHomLinear_mem_of_forall_E_mem (L : LadderSystem K V d) {W : Submodule K V}
    (hW : ∀ i j, ∀ w ∈ W, (L.E i j) w ∈ W) (x : Matrix (Fin d) (Fin d) K) {w : V}
    (hw : w ∈ W) : L.toGlHomLinear x w ∈ W := by
  have hx : x ∈ (⊤ : Submodule K (Matrix (Fin d) (Fin d) K)) := Submodule.mem_top
  rw [← (Matrix.stdBasis K (Fin d) (Fin d)).span_eq] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨i, j⟩, rfl⟩ := hy
    rw [L.toGlHomLinear_stdBasis]
    exact hW i j w hw
  | zero => simp [W.zero_mem]
  | add y y' _ _ ihy ihy' => rw [map_add, LinearMap.add_apply]; exact W.add_mem ihy ihy'
  | smul c y _ ihy => rw [map_smul, LinearMap.smul_apply]; exact W.smul_mem c ihy

/-- `vacuumSpan` is closed under every `gl(d)` generator `E i j`. Unconditional: no
`FiniteDimensional`/spanning hypothesis on the ambient `V` is used or needed. -/
lemma E_mem_vacuumSpan (L : LadderSystem K V d) {Ω : V} (P : L.HasVacuum Ω) (n : ℕ)
    (i j : Fin d) : ∀ v ∈ vacuumSpan L Ω n, (L.E i j) v ∈ vacuumSpan L Ω n := by
  intro v hv
  rw [vacuumSpan] at hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    rw [L.E_word P.ann i j (List.ofFn w)]
    rcases Nat.eq_zero_or_pos ((List.ofFn w).count j) with h0 | hpos
    · simp [h0]
    · have hmem : j ∈ List.ofFn w := List.count_pos_iff.mp hpos
      have hlen : (i :: (List.ofFn w).erase j).length = n := by
        rw [List.length_cons, List.length_erase_of_mem hmem, List.length_ofFn]
        have hn0 : 0 < n := List.length_ofFn (f := w) ▸ List.length_pos_of_mem hmem
        omega
      exact nsmul_mem (word_mem_vacuumSpan_of_length_eq L Ω hlen) _
  | zero => simp
  | add y z _ _ ihy ihz => rw [map_add]; exact Submodule.add_mem _ ihy ihz
  | smul c y _ ih => rw [map_smul]; exact Submodule.smul_mem _ c ih

/-- `vacuumSpan`, bundled as a genuine `gl(d)` Lie submodule. -/
def vacuumSpanLieSubmodule (L : LadderSystem K V d) {Ω : V} (P : L.HasVacuum Ω) (n : ℕ) :
    haveI := L.toLieRingModule
    LieSubmodule K (Matrix (Fin d) (Fin d) K) V := by
  letI := L.toLieRingModule
  refine { toSubmodule := vacuumSpan L Ω n, lie_mem := ?_ }
  intro x m hm
  show (L.toGlHom x) m ∈ vacuumSpan L Ω n
  have heq : L.toGlHom x = L.toGlHomLinear x := rfl
  rw [heq]
  exact forall_toGlHomLinear_mem_of_forall_E_mem L (E_mem_vacuumSpan L P n) x hm

@[simp] theorem coe_vacuumSpanLieSubmodule (L : LadderSystem K V d) {Ω : V} (P : L.HasVacuum Ω)
    (n : ℕ) : (vacuumSpanLieSubmodule L P n : Submodule K V) = vacuumSpan L Ω n := rfl

end LadderSystem
