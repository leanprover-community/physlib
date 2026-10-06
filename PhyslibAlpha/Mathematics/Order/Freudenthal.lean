/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Order.VectorLattice
public import PhyslibAlpha.Mathematics.Order.StrongUnit
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Step approximation in vector lattices

Freudenthal's spectral theorem: vector lattice elements are uniformly close to step functions.

## i. Overview

Fix a nonnegative element `u` of a real vector lattice, a strong unit: every element is below some
multiple of `u`. Every element is then close to a step function: split `u` into finitely many
disjoint pieces, and on each piece replace the element by a constant multiple of the piece. The
pieces form a partition of `u`: nonnegative, pairwise disjoint, adding up to `u`.

Finding the pieces needs least upper bounds of increasing sequences below `u`. Given `y`, the
increasing sequence `n • y⁺ ⊓ u` approaches the part of `u` on which `y` is positive: its support.
For an element `x` and a level `a`, the support of `x - a • u` is the piece on which `x` exceeds
`a`.
Cutting `u` at finitely many levels produces a partition on whose pieces `x` varies by at most the
spacing of the levels. Several elements are handled by intersecting their partitions.

## ii. Key results

- `VectorLattice.IsPartition` : a partition of `u`.
- `VectorLattice.IsPartition.le_sum` : local upper bounds on the pieces of a partition give a
  global upper bound.
- `VectorLattice.support_inf_sub` : the support of an element is a component of `u`.
- `VectorLattice.exists_partition_approx` : finitely many elements are uniformly close to step
  functions on one common partition. This is Freudenthal's spectral theorem.

## iii. Table of contents

- A. Partitions
- B. Step functions
- C. From local to global bounds
- D. Supports
- E. Partitions along one element
- F. Common refinements
- G. Components below a multiple of the unit

## iv. References

- W. A. J. Luxemburg and A. C. Zaanen, *Riesz Spaces I*, North-Holland, 1971, §40.

-/

@[expose] public section

namespace VectorLattice

variable {G : Type*} [AddCommGroup G] [Lattice G] [IsOrderedAddMonoid G] {u : G}

/-! ## A. Partitions -/

omit [IsOrderedAddMonoid G] in
/-- Disjointness passes to smaller nonnegative elements. -/
lemma inf_eq_zero_of_le {w v v' : G} (hw : 0 ≤ w) (hv : 0 ≤ v) (hvv : v ≤ v') (h : w ⊓ v' = 0) :
    w ⊓ v = 0 :=
  le_antisymm ((inf_le_inf_left w hvv).trans h.le) (le_inf hw hv)

variable (u) in
/-- A partition of `u`: nonnegative, pairwise disjoint pieces that add up to `u`. -/
def IsPartition {ι : Type*} [Fintype ι] (s : ι → G) : Prop :=
  (∀ i, 0 ≤ s i) ∧ Pairwise (fun i j => s i ⊓ s j = 0) ∧ ∑ i, s i = u

variable {ι : Type*} [Fintype ι] {s : ι → G}

/-- The pieces of a partition other than `i` add up to an element disjoint from `s i`. -/
lemma IsPartition.inf_sum_erase [DecidableEq ι] (hs : IsPartition u s) (i : ι) :
    s i ⊓ ∑ j ∈ Finset.univ.erase i, s j = 0 :=
  inf_sum_eq_zero _ (hs.1 i) s (fun j _ => hs.1 j) fun _ hj =>
    hs.2.1 (Finset.ne_of_mem_erase hj).symm

lemma IsPartition.le (hs : IsPartition u s) (i : ι) : s i ≤ u :=
  hs.2.2 ▸ Finset.single_le_sum (fun j _ => hs.1 j) (Finset.mem_univ i)

/-- A piece of a partition is disjoint from its complement. -/
lemma IsPartition.inf_sub [DecidableEq ι] (hs : IsPartition u s) (i : ι) : s i ⊓ (u - s i) = 0 := by
  rw [← hs.2.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_left]
  exact hs.inf_sum_erase i

/-- Differences of an antitone sequence of components from `u` to `0` form a partition. -/
lemma isPartition_sub_succ {N : ℕ} {e : ℕ → G} (he : Antitone e) (h0 : e 0 = u) (hN : e N = 0)
    (hnn : ∀ j, 0 ≤ e j) (hle : ∀ j, e j ≤ u) (hc : ∀ j, e j ⊓ (u - e j) = 0) :
    IsPartition u fun j : Fin N => e j - e (j + 1) := by
  have hpos (j : ℕ) : 0 ≤ e j - e (j + 1) := sub_nonneg.2 (he (Nat.le_succ _))
  have key : ∀ j k : ℕ, j < k → (e j - e (j + 1)) ⊓ (e k - e (k + 1)) = 0 := fun j k h => by
    refine le_antisymm ?_ (le_inf (hpos j) (hpos k))
    calc (e j - e (j + 1)) ⊓ (e k - e (k + 1)) ≤ (u - e k) ⊓ e k :=
          inf_le_inf ((sub_le_sub_right (hle j) _).trans (sub_le_sub_left (he h) u))
            (sub_le_self _ (hnn _))
      _ = 0 := by rw [inf_comm, hc]
  refine ⟨fun j => hpos j, fun j k hjk => ?_, ?_⟩
  · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hjk) with h | h
    · exact key _ _ h
    · rw [inf_comm]; exact key _ _ h
  · rw [Fin.sum_univ_eq_sum_range (fun j => e j - e (j + 1)), Finset.sum_range_sub', h0, hN,
      sub_zero]

/-- The pairwise infima of two partitions form a partition. -/
lemma IsPartition.inf_prod (hs : IsPartition u s) {κ : Type*} [Fintype κ] {t : κ → G}
    (ht : IsPartition u t) : IsPartition u fun p : ι × κ => s p.1 ⊓ t p.2 := by
  refine ⟨fun p => le_inf (hs.1 _) (ht.1 _), fun p q hpq => ?_, ?_⟩
  · refine le_antisymm ?_ (le_inf (le_inf (hs.1 _) (ht.1 _)) (le_inf (hs.1 _) (ht.1 _)))
    by_cases h : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h h2)
      exact (inf_le_inf inf_le_right inf_le_right).trans (ht.2.1 h2).le
    · exact (inf_le_inf inf_le_left inf_le_left).trans (hs.2.1 h).le
  · rw [Fintype.sum_prod_type]
    calc ∑ i, ∑ j, s i ⊓ t j = ∑ i, s i ⊓ ∑ j, t j := Finset.sum_congr rfl fun i _ =>
          (inf_sum_of_pairwise _ (hs.1 i) t (fun j _ => ht.1 j) fun j _ k _ h => ht.2.1 h).symm
      _ = u := by simp only [ht.2.2, fun i => inf_of_le_left (hs.le i), hs.2.2]

omit [IsOrderedAddMonoid G] in
lemma IsPartition.comp_equiv (hs : IsPartition u s) {κ : Type*} [Fintype κ] (e : κ ≃ ι) :
    IsPartition u (s ∘ e) :=
  ⟨fun _ => hs.1 _, fun _ _ h => hs.2.1 (e.injective.ne h), by
    rw [← hs.2.2]; exact e.sum_comp s⟩

/-! ## B. Step functions -/

variable [Module ℝ G] [PosSMulMono ℝ G]

/-- A nonnegative element splits along a partition: `x ⊓ M • u` is the sum of `x ⊓ M • s i`. -/
lemma IsPartition.inf_smul (hs : IsPartition u s) {x : G} (hx : 0 ≤ x) {M : ℝ} (hM : 0 ≤ M) :
    x ⊓ M • u = ∑ i, x ⊓ M • s i := by
  rw [← hs.2.2, Finset.smul_sum]
  exact inf_sum_of_pairwise _ hx _ (fun i _ => smul_nonneg hM (hs.1 i)) fun i _ j _ hij => by
    rw [← smul_inf hM, hs.2.1 hij, smul_zero]

/-- A step function whose levels on the nonzero pieces are at most `ε` is at most `ε • u`. -/
lemma IsPartition.sum_smul_le (hs : IsPartition u s) {c : ι → ℝ} {ε : ℝ}
    (h : ∀ i, s i ≠ 0 → c i ≤ ε) : ∑ i, c i • s i ≤ ε • u := by
  rw [← hs.2.2, Finset.smul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : s i = 0
  · simp [hi]
  · exact smul_le_smul_of_nonneg_right (h i hi) (hs.1 i)

/-- A step function whose levels on the nonzero pieces are at least `ε` is at least `ε • u`. -/
lemma IsPartition.le_sum_smul (hs : IsPartition u s) {c : ι → ℝ} {ε : ℝ}
    (h : ∀ i, s i ≠ 0 → ε ≤ c i) : ε • u ≤ ∑ i, c i • s i := by
  have := hs.sum_smul_le (c := fun i => -c i) (ε := -ε) fun i hi => neg_le_neg (h i hi)
  simp only [neg_smul, Finset.sum_neg_distrib] at this
  exact neg_le_neg_iff.1 this

/-! ## C. From local to global bounds -/

section LocalGlobal

variable [DecidableEq ι] (hs : IsPartition u s)
include hs

/-- Away from the piece `s i`, a step function differs from its level on `s i` by at most the
spacing of the levels. -/
lemma IsPartition.sub_sum_le (x : G) (b : ι → ℝ) (i : ι) :
    x - ∑ j, b j • s j ≤ (x - b i • u)⁺ + ∑ j ∈ Finset.univ.erase i, |b i - b j| • s j := by
  have e : x - ∑ j, b j • s j = (x - b i • u) + ∑ j, (b i - b j) • s j := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, hs.2.2]; abel
  have hle : ∑ j, (b i - b j) • s j ≤ ∑ j ∈ Finset.univ.erase i, |b i - b j| • s j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), sub_self, zero_smul, zero_add]
    exact Finset.sum_le_sum fun j _ => smul_le_smul_of_nonneg_right (le_abs_self _) (hs.1 j)
  rw [e]
  exact add_le_add (le_posPart _) hle

/-- The other pieces of a partition, scaled, are disjoint from a scaled piece. -/
lemma IsPartition.sum_erase_inf_smul {c : ι → ℝ} (hc : ∀ j, 0 ≤ c j) (i : ι) {M : ℝ}
    (hM : 0 ≤ M) : (∑ j ∈ Finset.univ.erase i, c j • s j) ⊓ M • s i = 0 := by
  rw [inf_comm]
  exact inf_sum_eq_zero _ (smul_nonneg hM (hs.1 i)) _ (fun j _ => smul_nonneg (hc j) (hs.1 j))
    fun j hj => smul_inf_smul_eq_zero (hs.1 i) (hs.1 j)
      (hs.2.1 (Finset.ne_of_mem_erase hj).symm) hM (hc j)

/-- If `x` is at most `b i` on each piece, the excess of `x` over the step function vanishes on
each piece. -/
lemma IsPartition.posPart_sub_sum_inf {x : G} {b : ι → ℝ} (h : ∀ i, (x - b i • u)⁺ ⊓ s i = 0)
    (i : ι) {M : ℝ} (hM : 0 ≤ M) : (x - ∑ j, b j • s j)⁺ ⊓ M • s i = 0 := by
  set w := ∑ j ∈ Finset.univ.erase i, |b i - b j| • s j
  have hw : 0 ≤ w := Finset.sum_nonneg fun j _ => smul_nonneg (abs_nonneg _) (hs.1 j)
  have hMs := smul_nonneg hM (hs.1 i)
  refine le_antisymm ?_ (le_inf le_sup_right hMs)
  calc (x - ∑ j, b j • s j)⁺ ⊓ M • s i ≤ ((x - b i • u)⁺ + w) ⊓ M • s i :=
        inf_le_inf_right _ (posPart_le_of_le (hs.sub_sum_le x b i) (add_nonneg le_sup_right hw))
    _ ≤ (x - b i • u)⁺ ⊓ M • s i := add_inf_le_of_inf_eq_zero le_sup_right hw hMs
        (hs.sum_erase_inf_smul (fun _ => abs_nonneg _) i hM)
    _ = 0 := inf_smul_eq_zero le_sup_right (hs.1 i) (h i) hM

/-- **Local to global.** If on each piece `s i` of a partition the element `x` is at most `b i`,
then `x` is at most the step function `∑ b i • s i`. -/
lemma IsPartition.le_sum (hunit : IsStrongUnit u) {x : G} {b : ι → ℝ}
    (h : ∀ i, (x - b i • u)⁺ ⊓ s i = 0) : x ≤ ∑ i, b i • s i := by
  obtain ⟨n, hn⟩ := hunit (x - ∑ i, b i • s i)⁺
  rw [← Nat.cast_smul_eq_nsmul ℝ] at hn
  have : (x - ∑ i, b i • s i)⁺ = 0 := calc
    _ = (x - ∑ i, b i • s i)⁺ ⊓ (n : ℝ) • u := (inf_of_le_left hn).symm
    _ = ∑ j, (x - ∑ i, b i • s i)⁺ ⊓ (n : ℝ) • s j := hs.inf_smul le_sup_right n.cast_nonneg
    _ = 0 := Finset.sum_eq_zero fun j _ => hs.posPart_sub_sum_inf h j n.cast_nonneg
  exact sub_nonpos.1 (posPart_eq_zero.1 this)

/-- **Local to global, from below.** If on each piece `s i` of a partition the element `x` is at
least `a i`, then `x` is at least the step function `∑ a i • s i`. -/
lemma IsPartition.sum_le (hunit : IsStrongUnit u) {x : G} {a : ι → ℝ}
    (h : ∀ i, (a i • u - x)⁺ ⊓ s i = 0) : ∑ i, a i • s i ≤ x := by
  have := hs.le_sum hunit (x := -x) (b := fun i => -a i) fun i => by
    rw [neg_smul, sub_neg_eq_add, neg_add_eq_sub]; exact h i
  simp only [neg_smul, Finset.sum_neg_distrib] at this
  exact neg_le_neg_iff.1 this

end LocalGlobal

/-! ## D. Supports -/

variable (u) in
/-- Increasing sequences below `u` have least upper bounds. -/
def HasMonotoneSups : Prop :=
  ∀ a : ℕ → G, Monotone a → (∀ n, a n ≤ u) → ∃ c, IsLUB (Set.range a) c

lemma monotone_smul_posPart_inf (y : G) : Monotone fun n : ℕ => (n : ℝ) • y⁺ ⊓ u :=
  fun _ _ h => inf_le_inf_right _ (smul_le_smul_of_nonneg_right (by exact_mod_cast h) le_sup_right)

section Support

variable (hsup : HasMonotoneSups u)
include hsup

lemma exists_isLUB_support (y : G) :
    ∃ c, IsLUB (Set.range fun n : ℕ => (n : ℝ) • y⁺ ⊓ u) c :=
  hsup _ (monotone_smul_posPart_inf y) fun _ => inf_le_right

/-- The support of `y`: the part of `u` on which `y` is positive, the limit of `n • y⁺ ⊓ u`. -/
noncomputable def support (y : G) : G := (exists_isLUB_support hsup y).choose

lemma isLUB_support (y : G) :
    IsLUB (Set.range fun n : ℕ => (n : ℝ) • y⁺ ⊓ u) (support hsup y) :=
  (exists_isLUB_support hsup y).choose_spec

lemma le_support (y : G) (n : ℕ) : (n : ℝ) • y⁺ ⊓ u ≤ support hsup y :=
  (isLUB_support hsup y).1 ⟨n, rfl⟩

lemma support_le (y : G) : support hsup y ≤ u :=
  (isLUB_support hsup y).2 <| Set.forall_mem_range.2 fun _ => inf_le_right

lemma support_mono {y y' : G} (h : y ≤ y') : support hsup y ≤ support hsup y' :=
  (isLUB_support hsup y).2 <| Set.forall_mem_range.2 fun n =>
    (inf_le_inf_right _ (smul_le_smul_of_nonneg_left (posPart_mono h) n.cast_nonneg)).trans
      (le_support hsup y' n)

variable (hu : 0 ≤ u)
include hu

lemma support_nonneg (y : G) : 0 ≤ support hsup y := by
  have h := le_support hsup y 0
  rwa [Nat.cast_zero, zero_smul, inf_of_le_left hu] at h

/-- The support is a component of `u`: it is disjoint from its complement. -/
lemma support_inf_sub (y : G) : support hsup y ⊓ (u - support hsup y) = 0 := by
  set c := support hsup y
  have hdouble :
      IsLUB (Set.range fun n : ℕ => (2 : ℝ) • ((n : ℝ) • y⁺ ⊓ u) ⊓ u) ((2 : ℝ) • c ⊓ u) :=
    isLUB_inf (isLUB_smul (isLUB_support hsup y) two_pos) u
  have hle : (2 : ℝ) • c ⊓ u ≤ c := hdouble.2 <| Set.forall_mem_range.2 fun n => by
    have h12 : u ≤ (2 : ℝ) • u := by rw [two_smul]; exact le_add_of_nonneg_left hu
    calc (2 : ℝ) • ((n : ℝ) • y⁺ ⊓ u) ⊓ u = ((2 * n : ℕ) : ℝ) • y⁺ ⊓ u := by
          rw [smul_inf two_pos.le, inf_assoc, inf_of_le_right h12, smul_smul]; push_cast; rfl
      _ ≤ c := le_support hsup y _
  refine le_antisymm ?_ (le_inf (support_nonneg hsup hu y) (sub_nonneg.2 (support_le hsup y)))
  have : (2 : ℝ) • c ⊓ u - c = c ⊓ (u - c) := by
    rw [sub_eq_add_neg, inf_add, two_smul]; congr 1 <;> abel
  rw [← this]
  exact sub_nonpos.2 hle

/-- A nonnegative element disjoint from `y⁺` is disjoint from the support of `y`. -/
lemma inf_support_eq_zero {w y : G} (hw : 0 ≤ w) (h : w ⊓ y⁺ = 0) : w ⊓ support hsup y = 0 := by
  have hl := isLUB_inf (isLUB_support hsup y) w
  have h0 : ∀ n : ℕ, (n : ℝ) • y⁺ ⊓ u ⊓ w = 0 := fun n => le_antisymm
    (by
      calc (n : ℝ) • y⁺ ⊓ u ⊓ w ≤ (n : ℝ) • y⁺ ⊓ w := inf_le_inf_right _ inf_le_left
        _ = 0 := by rw [inf_comm]; exact inf_smul_eq_zero hw le_sup_right h n.cast_nonneg)
    (le_inf (le_inf (smul_nonneg n.cast_nonneg le_sup_right) hu) hw)
  simp only [h0, Set.range_const] at hl
  rw [inf_comm]
  exact hl.unique isLUB_singleton

/-- `y⁺` lives on the support of `y`: it is disjoint from the complement. -/
lemma posPart_inf_sub_support (y : G) : y⁺ ⊓ (u - support hsup y) = 0 := by
  refine le_antisymm ?_ (le_inf le_sup_right (sub_nonneg.2 (support_le hsup y)))
  calc y⁺ ⊓ (u - support hsup y) = (y⁺ ⊓ u) ⊓ (u - support hsup y) := by
        rw [inf_assoc, inf_of_le_right (sub_le_self _ (support_nonneg hsup hu y))]
    _ ≤ support hsup y ⊓ (u - support hsup y) :=
        inf_le_inf_right _ (by simpa using le_support hsup y 1)
    _ = 0 := support_inf_sub hsup hu y

lemma support_eq_zero {y : G} (hy : y ≤ 0) : support hsup y = 0 := by
  have hl := isLUB_support hsup y
  simp only [posPart_eq_zero.2 hy, smul_zero, inf_of_le_left hu, Set.range_const] at hl
  exact hl.unique isLUB_singleton

omit hu in
lemma support_eq_self {y : G} (hy : u ≤ y) : support hsup y = u := by
  refine le_antisymm (support_le hsup y) ?_
  have : (1 : ℝ) • y⁺ ⊓ u = u := by
    rw [one_smul, inf_of_le_right (hy.trans (le_posPart y))]
  have h := le_support hsup y 1
  rwa [Nat.cast_one, this] at h

/-- Where `x` exceeds `a`, it is at least `a`: `(a • u - x)⁺` is disjoint from the support of
`x - a • u`. -/
lemma posPart_sub_inf_support (x : G) (a : ℝ) :
    (a • u - x)⁺ ⊓ support hsup (x - a • u) = 0 := by
  refine inf_support_eq_zero hsup hu le_sup_right ?_
  rw [show a • u - x = -(x - a • u) by abel, inf_comm]
  exact posPart_inf_negPart_eq_zero _

end Support

/-! ## E. Partitions along one element -/

section Levels

variable (hsup : HasMonotoneSups u) (x : G)

/-- The support of `x - (L + j * δ) • u`: the piece of `u` on which `x` exceeds the `j`-th level. -/
noncomputable def levelSupport (L δ : ℝ) (j : ℕ) : G := support hsup (x - (L + j * δ) • u)

variable {L δ : ℝ} (hu : 0 ≤ u) (hδ : 0 < δ)
include hu hδ

lemma levelSupport_antitone : Antitone (levelSupport hsup x L δ) := fun j k h =>
  support_mono hsup (sub_le_sub_left (smul_le_smul_of_nonneg_right (by
    have := hδ.le; gcongr) hu) x)

/-- Cutting `u` at the levels `L + j * δ` gives a partition once the levels pass below and above
`x`. -/
lemma isPartition_levelSupport {N : ℕ} (h0 : u ≤ x - L • u) (hN : x ≤ (L + N * δ) • u) :
    IsPartition u fun j : Fin N => levelSupport hsup x L δ j - levelSupport hsup x L δ (j + 1) :=
  isPartition_sub_succ (levelSupport_antitone hsup x hu hδ)
    (support_eq_self hsup (by simpa [levelSupport] using h0))
    (support_eq_zero hsup hu (sub_nonpos.2 hN)) (fun _ => support_nonneg hsup hu _)
    (fun _ => support_le hsup _) (fun _ => support_inf_sub hsup hu _)

/-- On the `j`-th piece, `x` lies between the `j`-th and the `(j + 1)`-th level. -/
lemma levelSupport_approx (j : ℕ) :
    (x - (L + j * δ + δ) • u)⁺ ⊓ (levelSupport hsup x L δ j - levelSupport hsup x L δ (j + 1)) = 0
      ∧ ((L + j * δ) • u - x)⁺ ⊓
        (levelSupport hsup x L δ j - levelSupport hsup x L δ (j + 1)) = 0 := by
  have hnn := sub_nonneg.2 (levelSupport_antitone hsup x (L := L) hu hδ (Nat.le_succ j))
  have e : L + j * δ + δ = L + ((j + 1 : ℕ) : ℝ) * δ := by push_cast; ring
  rw [e]
  exact ⟨inf_eq_zero_of_le le_sup_right hnn (sub_le_sub_right (support_le hsup _) _)
      (posPart_inf_sub_support hsup hu _),
    inf_eq_zero_of_le le_sup_right hnn (sub_le_self _ (support_nonneg hsup hu _))
      (posPart_sub_inf_support hsup hu x _)⟩

end Levels

/-- One element is within `δ` of a step function: cut `u` at levels spaced by `δ`. -/
lemma exists_partition_approx_one (hsup : HasMonotoneSups u) (hu : 0 ≤ u)
    (hunit : IsStrongUnit u) (x : G) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (s : Fin N → G) (a : Fin N → ℝ), IsPartition u s ∧
      ∀ j, (x - (a j + δ) • u)⁺ ⊓ s j = 0 ∧ (a j • u - x)⁺ ⊓ s j = 0 := by
  obtain ⟨n, hlo, hhi⟩ := hunit.exists_two_sided hu x
  rw [← Nat.cast_smul_eq_nsmul ℝ] at hlo hhi
  set N := ⌈(2 * n + 1) / δ⌉₊
  have hN : (n : ℝ) ≤ -((n : ℝ) + 1) + N * δ := by
    have := Nat.le_ceil ((2 * n + 1) / δ)
    rw [div_le_iff₀ hδ] at this
    linarith
  have h0 : u ≤ x - (-((n : ℝ) + 1)) • u := by
    rw [neg_smul, sub_neg_eq_add, add_smul, one_smul]
    calc u = -((n : ℝ) • u) + ((n : ℝ) • u + u) := by abel
      _ ≤ x + ((n : ℝ) • u + u) := by gcongr
  exact ⟨N, _, fun j => -((n : ℝ) + 1) + ((j : ℕ) : ℝ) * δ,
    isPartition_levelSupport hsup x hu hδ h0 (hhi.trans (smul_le_smul_of_nonneg_right hN hu)),
    fun j => levelSupport_approx hsup x hu hδ j⟩

/-! ## F. Common refinements -/

omit [IsOrderedAddMonoid G] [PosSMulMono ℝ G] in
/-- Bounds on the pieces of a partition hold on the pieces of every refinement. -/
lemma approx_of_le {x c c' : G} {a δ : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c')
    (h : (x - (a + δ) • u)⁺ ⊓ c' = 0 ∧ (a • u - x)⁺ ⊓ c' = 0) :
    (x - (a + δ) • u)⁺ ⊓ c = 0 ∧ (a • u - x)⁺ ⊓ c = 0 :=
  ⟨inf_eq_zero_of_le le_sup_right hc hcc h.1, inf_eq_zero_of_le le_sup_right hc hcc h.2⟩

/-- **Freudenthal's spectral theorem.** Finitely many elements are within `δ` of step functions on
one common partition of `u`. -/
lemma exists_partition_approx (hsup : HasMonotoneSups u) (hu : 0 ≤ u) (hunit : IsStrongUnit u)
    {n : ℕ} (x : Fin n → G) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (m : ℕ) (s : Fin m → G) (a : Fin m → Fin n → ℝ), IsPartition u s ∧
      ∀ i k, (x k - (a i k + δ) • u)⁺ ⊓ s i = 0 ∧ (a i k • u - x k)⁺ ⊓ s i = 0 := by
  induction n with
  | zero =>
    exact ⟨1, fun _ => u, fun _ k => k.elim0, ⟨fun _ => hu,
      fun i j h => absurd (Subsingleton.elim i j) h, by simp⟩, fun _ k => k.elim0⟩
  | succ n ih =>
    obtain ⟨m, s, a, hs, has⟩ := ih (Fin.init x)
    obtain ⟨N, t, b, ht, hbt⟩ := exists_partition_approx_one hsup hu hunit (x (Fin.last n)) hδ
    refine ⟨m * N, _, fun p => Fin.lastCases (b (finProdFinEquiv.symm p).2)
      (a (finProdFinEquiv.symm p).1), (hs.inf_prod ht).comp_equiv finProdFinEquiv.symm,
      fun p k => ?_⟩
    have hnn := le_inf (hs.1 (finProdFinEquiv.symm p).1) (ht.1 (finProdFinEquiv.symm p).2)
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simpa using approx_of_le hnn inf_le_right (hbt _)
    · simpa [Fin.init] using approx_of_le hnn inf_le_left (has (finProdFinEquiv.symm p).1 k)

/-! ## G. Components below a multiple of the unit -/

/-- A component of `u` that is strictly below `u` in the sense `c ≤ t • u`, `t < 1`, vanishes. -/
lemma eq_zero_of_le_smul (hu : 0 ≤ u) {c : G} (hc0 : 0 ≤ c) (hc : c ⊓ (u - c) = 0) {t : ℝ}
    (ht : t < 1) (h : c ≤ t • u) : c = 0 := by
  rcases le_or_gt t 0 with ht0 | ht0
  · exact le_antisymm (h.trans (smul_nonpos_of_nonpos_of_nonneg ht0 hu)) hc0
  have hc1 : c ≤ u := h.trans (by simpa using smul_le_smul_of_nonneg_right ht.le hu)
  have h₁ : (1 - t) • c ≤ c := smul_le_of_le_one_left hc0 (by linarith)
  have h₂ : (1 - t) • c ≤ u - c := calc
    (1 - t) • c ≤ (1 - t) • u := smul_le_smul_of_nonneg_left hc1 (by linarith)
    _ = u - t • u := by rw [sub_smul, one_smul]
    _ ≤ u - c := sub_le_sub_left h u
  have h₃ : (1 - t) • c ≤ 0 := hc ▸ le_inf h₁ h₂
  refine le_antisymm ?_ hc0
  have := smul_le_smul_of_nonneg_left h₃ (inv_nonneg.2 (by linarith : (0 : ℝ) ≤ 1 - t))
  rwa [smul_zero, inv_smul_smul₀ (by linarith : (1 - t : ℝ) ≠ 0)] at this

end VectorLattice
