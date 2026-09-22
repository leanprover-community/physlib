/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComponentIdx.Single
public import Physlib.Relativity.Tensors.Contraction.SuccSuccAbove
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Tactic.Cases
public import Mathlib.GroupTheory.Perm.Fin
/-!

# Reindexing of tensor components

In this file we give results related to the reindexing of tensors.
If a tensor has indices specified by a list of colors `c : Fin n → C`, then reindexing the
tensor corresponds to a bijection `σ : Fin m → Fin n` such that `c ∘ σ = c1` for some other
list of colors `c1 : Fin m → C`. A reindexing might take a tensor ψⁱⱼ to a tensor ψʲᵢ
by reordering the indices, or it might take a tensor ψⁱⱼᵏ to a tensor ψⁱᵏ.

We are interested in the interaction of reindexing with the following operations on tensors:
- `Fin.append` corresponds to the product of tensors.
- `Fin.succAbove` corresponds to the evaluation of a tensor at a given index.
- `Fin.succSuccAbove` corresponds to the contraction of a tensor at two given indices.

-/

@[expose] public section

open Module

namespace Fin

/-!

## Index maps

The finite index maps out of which the reindexings below are built: `Fin.append` for products and
`Fin.succAbove` for a deleted slot. The lemmas on `Fin.succSuccAbove`, for a deleted pair, are in
`Physlib.Relativity.Tensors.Contraction.SuccSuccAbove`.

-/

/-- Splitting `Fin (m + n)` into its two blocks and reassembling them is the identity. -/
lemma append_castAdd_natAdd_eq_id {m n : ℕ} :
    Fin.append (Fin.castAdd n) (Fin.natAdd m) = (id : Fin (m + n) → Fin (m + n)) := by
  simpa using Fin.append_castAdd_natAdd (f := (id : Fin (m + n) → Fin (m + n)))

/-- Moving slot `i` to the end is the cycle `[i, last]`: the block map that lists the
  `i.succAbove` survivors in order and then `i` is `Fin.cycleIcc i (Fin.last n)`. -/
lemma append_succAbove_const_eq_cycleIcc {n : ℕ} (i : Fin (n + 1)) :
    Fin.append i.succAbove (fun _ : Fin 1 => i) = ⇑(Fin.cycleIcc i (Fin.last n)) := by
  funext y
  refine Fin.addCases (fun a => ?_) (fun a => ?_) y
  · rw [Fin.append_left]
    have h := congrFun (Fin.cycleIcc_comp_succAbove i (Fin.last n) (Fin.le_last i)) a
    rw [Fin.succAbove_last] at h
    exact h.symm
  · rw [Fin.append_right]
    have : (Fin.natAdd n a : Fin (n + 1)) = Fin.last n := by
      apply Fin.ext; simp [Fin.val_natAdd]
    rw [this, Fin.cycleIcc_of_le_of_le (Fin.le_last _) (Fin.le_last _), ite_eq_left rfl]

end Fin

namespace TensorSpecies

variable {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    (S : TensorSpecies k C G V basisIdx rep b)

namespace Tensor

/-- Given two lists of indices `c : Fin n → C` and `c1 : Fin m → C` a map
  `σ : Fin m → Fin n` satisfies the condition `IsReindexing c c1 σ` if it is:
- A bijection
- Forms a commutative triangle with `c` and `c1`.
-/
def IsReindexing {n m : ℕ} (c : Fin n → C) (c1 : Fin m → C)
    (σ : Fin m → Fin n) : Prop :=
  Function.Bijective σ ∧ ∀ i, c (σ i) = c1 i

namespace IsReindexing

/-!

## Properties of the underlying function

-/

lemma injective {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ) : Function.Injective σ := h.1.1

lemma surjective {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ) : Function.Surjective σ := h.1.2


lemma auto {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ := by {simp [IsReindexing]; try decide}) :
    IsReindexing c c1 σ := h


@[simp]
lemma on_id {n : ℕ} {c c1 : Fin n → C} :
    IsReindexing c c1 (id : Fin n → Fin n) ↔ ∀ i, c i = c1 i := by
  simp [IsReindexing]

lemma on_id_symm {n : ℕ} {c c1 : Fin n → C} (h : IsReindexing c1 c id) :
    IsReindexing c c1 (id : Fin n → Fin n) := by
  simp at h ⊢
  exact fun i => (h i).symm

/-- For a map `σ` satisfying `IsReindexing c c1 σ`, the inverse of that map. -/
def inv {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    (σ : Fin m → Fin n) (h : IsReindexing c c1 σ) : Fin n → Fin m :=
  Fintype.bijInv h.1

/-- For a map `σ : Fin m → Fin n` satisfying `IsReindexing c c1 σ`,
  that map lifted to an equivalence between
  `Fin n` and `Fin m`. -/
def toEquiv {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ) :
    Fin n ≃ Fin m where
  toFun := inv σ h
  invFun := σ
  left_inv := Fintype.rightInverse_bijInv h.1
  right_inv := Fintype.leftInverse_bijInv h.1

lemma apply_inv_apply {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    (σ : Fin m → Fin n) (h : IsReindexing c c1 σ) (x : Fin m) :
    h.inv σ (σ x) = x := by
  change h.toEquiv (h.toEquiv.symm x) = x
  simp

lemma inv_apply_apply {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    (σ : Fin m → Fin n) (h : IsReindexing c c1 σ) (x : Fin n) :
    σ (h.inv σ x) = x := by
  change h.toEquiv.symm (h.toEquiv x) = x
  simp

lemma inv_eq_self_of_pointwise_eq {n : ℕ} {c c1 : Fin n → C} {σ : Fin n → Fin n}
    (h : IsReindexing c c1 σ) (hσ : ∀ x, σ x = x) (x : Fin n) :
    h.inv σ x = x := by
  have hx := h.inv_apply_apply σ x
  rw [hσ] at hx
  exact hx

lemma inv_id_eq {n : ℕ} {c c1 : Fin n → C}
    (h : IsReindexing c c1 (id : Fin n → Fin n)) (x : Fin n) :
    h.inv (id : Fin n → Fin n) x = x :=
  h.inv_apply_apply (id : Fin n → Fin n) x

lemma inv_cast_eq {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C} (e : m = n)
    (h : IsReindexing c c1 (Fin.cast e)) (x : Fin n) :
    h.inv (Fin.cast e) x = Fin.cast e.symm x := by
  have hx := h.inv_apply_apply (Fin.cast e) x
  have hval : (h.inv (Fin.cast e) x).val = x.val := congrArg Fin.val hx
  exact Fin.val_inj.mp hval

lemma inv_equiv_symm_eq {n : ℕ} {c c1 : Fin n → C} (e : Equiv.Perm (Fin n))
    (h : IsReindexing c c1 ⇑e.symm) (x : Fin n) :
    h.inv ⇑e.symm x = e x := by
  have hx := h.inv_apply_apply ⇑e.symm x
  apply e.symm.injective
  rw [hx, Equiv.symm_apply_apply]

lemma preserve_color {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ) :
    ∀ (x : Fin m), c1 x = (c ∘ σ) x := by
  intro x
  obtain ⟨y, rfl⟩ := h.toEquiv.surjective x
  simp only [Function.comp_apply]
  rw [h.2]

set_option warning.simp.varHead false in
@[simp]
lemma inv_perserve_color {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ) (x : Fin n) :
    c1 (h.inv σ x) = c x := by
  obtain ⟨x, rfl⟩ := h.toEquiv.symm.surjective x
  change c1 (h.toEquiv _) = _
  simp only [Equiv.apply_symm_apply]
  rw [h.preserve_color]
  rfl

set_option warning.simp.varHead false in
@[simp]
lemma toEquiv_symm_perserve_color {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ) (x : Fin m) :
    c (h.toEquiv.symm x) = c1 x := by
  obtain ⟨x, rfl⟩ := h.toEquiv.surjective x
  rw [h.preserve_color]
  rfl

/-!

## Constructors

-/
open Fin

lemma swap {n : ℕ} {c : Fin n → C} (i j : Fin n) :
    IsReindexing c (c ∘ Equiv.swap i j) (Equiv.swap i j) := by
  simp [IsReindexing]

/-- The inverse of a map satisfying `IsReindexing c c1 σ` is a reindexing of `c1` by `c`. -/
lemma symm {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ) : IsReindexing c1 c (h.inv σ) :=
  ⟨h.toEquiv.bijective, h.inv_perserve_color⟩

lemma symm_of_id {n : ℕ} {c c1 : Fin n → C} (h : IsReindexing c c1 id) :
    IsReindexing c1 c id := by
  simp at h ⊢
  exact fun i => (h i).symm

/-- The composition of two maps satisfying `IsReindexing` also satisfies the `IsReindexing`. -/
lemma comp {n n1 n2 : ℕ} {c : Fin n → C} {c1 : Fin n1 → C}
    {c2 : Fin n2 → C} {σ : Fin n1 → Fin n} {σ2 : Fin n2 → Fin n1}
    (h : IsReindexing c c1 σ) (h2 : IsReindexing c1 c2 σ2) : IsReindexing c c2 (σ ∘ σ2) :=
  ⟨h.1.comp h2.1, fun x => (h.2 (σ2 x)).trans (h2.2 x)⟩

lemma append_congr_left {n n' n2 : ℕ} {c : Fin n → C} {c' : Fin n' → C}
    {σ : Fin n' → Fin n} (c2 : Fin n2 → C) (h : IsReindexing c c' σ) :
    IsReindexing (Fin.append c c2) (Fin.append c' c2)
      (Fin.append (Fin.castAdd n2 ∘ σ) (Fin.natAdd n)) := by
  refine ⟨?_, fun i => ?_⟩
  · have heq : (Fin.append (Fin.castAdd n2 ∘ σ) (Fin.natAdd n) : Fin (n' + n2) → Fin (n + n2)) =
        ⇑(finSumFinEquiv.symm.trans
          (((Equiv.ofBijective σ h.1).sumCongr (Equiv.refl (Fin n2))).trans finSumFinEquiv)) := by
      ext i
      refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
        simp [Fin.append_left, Fin.append_right]
    rw [heq]
    exact Equiv.bijective _
  · refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
      simp [Fin.append_left, Fin.append_right, h.2]

lemma append_congr_right {n n' n2 : ℕ} {c : Fin n → C} {c' : Fin n' → C}
    {σ : Fin n' → Fin n} (c2 : Fin n2 → C) (h : IsReindexing c c' σ) :
    IsReindexing (Fin.append c2 c) (Fin.append c2 c')
      (Fin.append (Fin.castAdd n) (Fin.natAdd n2 ∘ σ)) := by
  refine ⟨?_, fun i => ?_⟩
  · have heq : (Fin.append (Fin.castAdd n) (Fin.natAdd n2 ∘ σ) : Fin (n2 + n') → Fin (n2 + n)) =
        ⇑(finSumFinEquiv.symm.trans
          (((Equiv.refl (Fin n2)).sumCongr (Equiv.ofBijective σ h.1)).trans finSumFinEquiv)) := by
      ext i
      refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
        simp [Fin.append_left, Fin.append_right]
    rw [heq]
    exact Equiv.bijective _
  · refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
      simp [Fin.append_left, Fin.append_right, h.2]

lemma append_zero_right {n} {c : Fin n → C}
    {c1 : Fin 0 → C} : IsReindexing c (Fin.append c c1) id := by
  simp only [Nat.add_zero, IsReindexing.on_id]
  have P : ∀ (i : Fin (n + 0)), c i = Fin.append c c1 i := by
    rw [Fin.forall_fin_add]
    simp only [Fin.append_left, Fin.append_right, IsEmpty.forall_iff, and_true]
    simp only [Fin.castAdd_zero, Fin.cast_eq_self, implies_true]
  exact P

lemma append_swap {n n2 : ℕ} {c : Fin n → C} {c2 : Fin n2 → C} :
    IsReindexing (Fin.append c c2) (Fin.append c2 c)
      (Fin.append (Fin.natAdd n) (Fin.castAdd n2)) := by
  refine ⟨?_, fun i => ?_⟩
  · have heq : (Fin.append (Fin.natAdd n) (Fin.castAdd n2) : Fin (n2 + n) → Fin (n + n2)) =
        ⇑(finSumFinEquiv.symm.trans
          ((Equiv.sumComm (Fin n2) (Fin n)).trans finSumFinEquiv)) := by
      ext i
      refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
        simp [Fin.append_left, Fin.append_right]
    rw [heq]
    exact Equiv.bijective _
  · refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
      simp [Fin.append_left, Fin.append_right]

lemma append_assoc_right   {n1 n2 n3 : ℕ} {c : Fin n1 → C} {c2 : Fin n2 → C} {c3 : Fin n3 → C} :
    IsReindexing (Fin.append c (Fin.append c2 c3)) (Fin.append (Fin.append c c2) c3)
      (Fin.cast (by grind)) :=
  ⟨(finCongr (by grind)).bijective, fun i => (congrFun (Fin.append_assoc c c2 c3) i).symm⟩

lemma append_assoc_left {n1 n2 n3 : ℕ} {c : Fin n1 → C} {c2 : Fin n2 → C} {c3 : Fin n3 → C} :
    IsReindexing (Fin.append (Fin.append c c2) c3) (Fin.append c (Fin.append c2 c3))
      (Fin.cast (by grind)) :=
  ⟨(finCongr (by grind)).bijective, fun i => congrFun (Fin.append_assoc c c2 c3) _⟩

lemma append_succAbove_natAdd {n n1 : ℕ} {c : Fin n → C} {c1 : Fin (n1 + 1) → C}
    (i : Fin (n1 + 1)) :
    IsReindexing (Fin.append c c1 ∘ (Fin.natAdd n i).succAbove)
      (Fin.append c (c1 ∘ i.succAbove)) id := by
  refine ⟨Function.bijective_id, fun x => ?_⟩
  simp only [Function.comp_apply, id_eq]
  refine Fin.addCases (fun a => ?_) (fun a => ?_) x
  · have hidx : (Fin.natAdd n i).succAbove (Fin.castAdd n1 a) = Fin.castAdd (n1 + 1) a := by
      rw [Fin.succAbove_of_castSucc_lt]
      · ext
        simp
      · simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_castAdd, Fin.val_natAdd]
        omega
    simp [hidx, Fin.append_left]
  · have hidx : (Fin.natAdd n i).succAbove (Fin.natAdd n a) = Fin.natAdd n (i.succAbove a) := by
      have hcond : ((Fin.natAdd n a).castSucc < Fin.natAdd n i) ↔ (a.castSucc < i) := by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_natAdd]
        omega
      simp only [Fin.succAbove, hcond]
      split_ifs <;> ext <;> simp [Nat.add_assoc]
    simp [hidx, Fin.append_right]

lemma append_succAbove_castAdd {n n1 : ℕ} {c : Fin (n + 1) → C} {c1 : Fin (n1 + 1) → C}
    (i : Fin (n + 1)) :
    IsReindexing (Fin.append c c1 ∘ (Fin.castAdd (n1 + 1) i).succAbove)
      (Fin.append (c ∘ i.succAbove) c1) (Fin.cast (by grind)) := by
  refine ⟨(finCongr (by grind)).bijective, fun y => ?_⟩
  simp only [Function.comp_apply]
  refine Fin.addCases (fun a => ?_) (fun a => ?_) y
  · have hidx : (Fin.castAdd (n1 + 1) i).succAbove (Fin.cast (by grind) (Fin.castAdd (n1 + 1) a))
        = Fin.castAdd (n1 + 1) (i.succAbove a) := by
      have hcond : ((Fin.cast (by grind) (Fin.castAdd (n1 + 1) a)).castSucc <
          Fin.castAdd (n1 + 1) i) ↔ (a.castSucc < i) := by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_cast, Fin.val_castAdd]
      simp only [Fin.succAbove, hcond]
      split_ifs <;> ext <;> simp
    simp [hidx, Fin.append_left]
  · have hidx : (Fin.castAdd (n1 + 1) i).succAbove (Fin.cast (by grind) (Fin.natAdd n a))
        = Fin.natAdd (n + 1) a := by
      rw [Fin.succAbove_of_le_castSucc]
      · ext
        simp [Nat.add_right_comm]
      · simp only [Fin.le_def, Fin.val_castSucc, Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd]
        omega
    simp [hidx, Fin.append_right]

/-- Removing two entries from the right component of `Fin.append c1 c` commutes with the
  append: removing the `i`-th and `j`-th entries of `c` and then appending `c1` matches
  removing the corresponding entries of `Fin.append c1 c`, via the identity permutation.
  This is used for the commutation of taking a *product* of tensors
  with *contraction* of indices. -/
lemma append_succSuccAbove_natAdd {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin n1 → C} (i j : Fin (n + 1 + 1)) :
    IsReindexing (Fin.append c1 c ∘ (Fin.natAdd n1 i).succSuccAbove (Fin.natAdd n1 j))
      (Fin.append c1 (c ∘ i.succSuccAbove j)) id := by
  apply And.intro (Function.bijective_id)
  simp [forall_fin_add, succSuccAbove_comm_natAdd i j, succSuccAbove_natAdd_apply_castAdd i j]

/-- Given a reindexing of `c` by `c1` via `σ` for which the index `i` is sent to `0`,
  removing the `i`-th entry of `c1` and the first entry of `c` yields a reindexing of
  `c ∘ Fin.succ` by `c1 ∘ i.succAbove` via the map sending `j` to the predecessor of
  `σ (i.succAbove j)`. -/
lemma succAbove_of_eq_zero {n n1 : ℕ} {c : Fin (n + 1) → C} {c1 : Fin (n1 + 1) → C}
    {σ : Fin (n1 + 1) → Fin (n + 1)} (i : Fin (n1 + 1))
    (h : IsReindexing c c1 σ) (hi : σ i = 0) :
    IsReindexing (c ∘ Fin.succ) (c1 ∘ i.succAbove)
      (fun j => (σ (i.succAbove j)).pred (by simp [← hi, h.injective.eq_iff])) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x1 x2 h1
    simpa [h.injective.eq_iff] using h1
  · intro k
    suffices ha : ∃ a, σ (i.succAbove a) = k.succ by
      obtain ⟨a, ha⟩ := ha
      use a
      simp [ha]
    obtain ⟨j, hj⟩ := h.surjective k.succ
    simp only [← hj, h.injective.eq_iff, Fin.exists_succAbove_eq_iff, ne_eq]
    grind
  · intro x
    simp [h.preserve_color]

/-- Given a reindexing of `c` by `c1` via `σ` for which the index `i` is not sent to `0`,
  removing the `i`-th entry of `c1` and the `(σ i)`-th entry of `c` yields a reindexing of
  `c ∘ (σ i).succAbove` by `c1 ∘ i.succAbove` via the map
  `(σ i).pred.predAbove ∘ σ ∘ i.succAbove`. -/
lemma succAbove_of_neq_zero {n n1 : ℕ} {c : Fin (n + 1) → C} {c1 : Fin (n1 + 1) → C}
    {σ : Fin (n1 + 1) → Fin (n + 1)} (i : Fin (n1 + 1))
    (h : IsReindexing c c1 σ) (hi : σ i ≠ 0) :
    IsReindexing (c ∘ (σ i).succAbove) (c1 ∘ i.succAbove)
      ((Fin.pred (σ i) hi).predAbove  ∘ σ ∘ i.succAbove) := by
  have hpr : σ i = ((σ i).pred hi).succ := (Fin.succ_pred _ _).symm
  have hne : ∀ x, σ (i.succAbove x) ≠ σ i := fun x heq =>
    Fin.succAbove_ne i x (h.injective heq)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x1 x2 h2
    simp only [Function.comp_apply] at h2
    apply i.succAbove_right_injective (h.injective ?_)
    suffices h' :
        ((σ i).pred hi).succ.succAbove (((σ i).pred hi).predAbove (σ (i.succAbove x1))) =
        ((σ i).pred hi).succ.succAbove (((σ i).pred hi).predAbove (σ (i.succAbove x2))) by
      rwa [Fin.succ_succAbove_predAbove (hpr ▸ hne x1),
        Fin.succ_succAbove_predAbove (hpr ▸ hne x2)] at h'
    simpa using h2
  · intro k
    simp only [Function.comp_apply]
    suffices h' : ∃ a, σ (i.succAbove a) = (σ i).succAbove k by
      conv => enter [1, a]; rw [← ((σ i).pred hi).succ.succAbove_right_injective.eq_iff]
      obtain ⟨a, h'⟩ := h'
      exact ⟨a, by rw [Fin.succ_succAbove_predAbove (hpr ▸ hne a), ← hpr]; exact h'⟩
    obtain ⟨j, hj⟩ := h.surjective ((σ i).succAbove k)
    simp only [← hj, h.injective.eq_iff, Fin.exists_succAbove_eq_iff, ne_eq]
    rintro rfl
    simp at hj
  · intro x
    simp only [h.preserve_color, Function.comp_apply]
    congr 1
    conv_lhs => enter[1]; rw [hpr]
    exact Fin.succ_succAbove_predAbove (hpr ▸ hne x)

/-- Given a reindexing of `c` by `c1` via `σ`, removing the `i`-th entry of `c1` and the
  `(σ i)`-th entry of `c` yields a reindexing of `c ∘ (σ i).succAbove` by `c1 ∘ i.succAbove`.
  This unifies `succAbove_of_eq_zero` and `succAbove_of_neq_zero` via a case split on
  whether `σ i = 0`. This is used for the commutation of *permutation*
  of indices with *evaluation* of indices. -/
lemma succAbove {n n1 : ℕ} {c : Fin (n + 1) → C} {c1 : Fin (n1 + 1) → C}
    {σ : Fin (n1 + 1) → Fin (n + 1)} (i : Fin (n1 + 1))
    (h : IsReindexing c c1 σ) :
    IsReindexing (c ∘ (σ i).succAbove) (c1 ∘ i.succAbove)
      (if hi : σ i = 0 then fun j => (σ (i.succAbove j)).pred (by simp [← hi, h.injective.eq_iff])
      else (Fin.pred (σ i) hi).predAbove  ∘ σ ∘ i.succAbove) := by
  by_cases hi : σ i = 0
  · simpa [hi] using IsReindexing.succAbove_of_eq_zero i h hi
  · simpa [hi] using IsReindexing.succAbove_of_neq_zero i h hi

/-- The conclusion of `succAbove` from an explicit survivor relabelling: if `σ'` fills the square
  `(σ i).succAbove ∘ σ' = σ ∘ i.succAbove`, carrying the complement of `i` to the complement of
  `σ i`, then it is a reindexing of the two shortened colour lists. The square forces `σ'` to be
  injective, hence bijective, so no bijectivity hypothesis is needed; this is why the statement is
  restricted to equal lengths.

  Where `succAbove` builds the relabelling from `σ` as a `dite` composite, the map here is the
  caller's, which is what lets it stand in the statement of a lemma the caller instantiates. -/
lemma succAbove_of_succAbove_eq {n : ℕ} {c c1 : Fin (n + 1) → C}
    {σ : Fin (n + 1) → Fin (n + 1)} {σ' : Fin n → Fin n} (i : Fin (n + 1))
    (h : IsReindexing c c1 σ) (hσ' : (σ i).succAbove ∘ σ' = σ ∘ i.succAbove) :
    IsReindexing (c ∘ (σ i).succAbove) (c1 ∘ i.succAbove) σ' := by
  have key : ∀ a, (σ i).succAbove (σ' a) = σ (i.succAbove a) := congrFun hσ'
  refine ⟨Finite.injective_iff_bijective.mp (fun a b hab => ?_), fun a => ?_⟩
  · exact Fin.succAbove_right_injective (h.injective (by rw [← key a, ← key b, hab]))
  · simpa only [Function.comp_apply, key a] using h.2 (i.succAbove a)

/-- Given a reindexing of `c` by `c1` via `σ` and two distinct indices `i ≠ j`, removing the
  `i`-th and `j`-th entries of `c1` and the `(σ i)`-th and `(σ j)`-th entries of `c` yields a
  reindexing of `c ∘ (σ i).succSuccAbove (σ j)` by `c1 ∘ i.succSuccAbove j`.
  This is used for the commutation of *permutation* of indices with
  *contraction* of indices. -/
lemma succSuccAbove {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin (n1 + 1 + 1) → C}
    (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    {σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)} (hσ : IsReindexing c c1 σ) :
    IsReindexing (c ∘  (σ i).succSuccAbove (σ j))
      (c1 ∘ i.succSuccAbove j) (i.funPredPredAbove j hij σ hσ.1) := by
  apply And.intro
  · exact Fin.funPredPredAbove_bijective i j hij σ hσ.left
  · intro m
    simp [Fin.funPredPredAbove, hσ.2]

/-- Removing two pairs of entries from `c` in either order gives the same colour list:
  removing the `i1`-th and `j1`-th entries and then the (shifted) `i2`-th and `j2`-th entries
  matches removing the `i2`-th and `j2`-th entries first and then the (shifted) `i1`-th and
  `j1`-th entries, via the identity permutation.
  This is used for the commutation of two *contractions*. -/
lemma succSuccAbove_comm {n : ℕ} {c : Fin (n + 1 + 1 + 1 + 1) → C}
    (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) :
    let i2' := (i1.succSuccAbove j1 i2);
    let j2' := (i1.succSuccAbove j1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', hij2];
    let i1' := (predPredAbove i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (predPredAbove i2' j2' hi2j2' j1 (by simp [i2', j2']));
    IsReindexing ((c ∘ i2'.succSuccAbove j2') ∘ i1'.succSuccAbove j1')
      ((c ∘ i1.succSuccAbove j1) ∘ i2.succSuccAbove j2) id := by
  apply And.intro (Function.bijective_id)
  simp only [id_eq, Function.comp_apply]
  intro i
  rw [succSuccAbove_comm_apply]
  · simp [hij1]
  · simp [hij2]

open Fin in
/-- Removing one entry and then a pair of entries from `c` in either order gives the same
  colour list: removing the `k`-th entry and then the (shifted) `i`-th and `j`-th entries
  matches removing the `i`-th and `j`-th entries first and then the (shifted) `k`-th entry,
  via the identity permutation.
  This is used for the commutation of a *contraction* with an *evaluation*. -/
lemma succAbove_succSuccAbove_comm {n : ℕ} {c : Fin (n + 1 + 1 + 1) → C}
    (k : Fin (n + 1 + 1 + 1)) (i j : Fin (n + 1 + 1)) (hij : i ≠ j) :
    let i' := k.succAbove i;
    let j' := k.succAbove j;
    have hij' : i' ≠ j' := by simp [i', j', hij];
    let k' := predPredAbove i' j' hij' k (by simp [i', j', Ne.symm]);
    IsReindexing ((c ∘ i'.succSuccAbove j') ∘ k'.succAbove)
      ((c ∘ k.succAbove) ∘ i.succSuccAbove j) id := by
  intro i' j' hij' k'
  refine ⟨Function.bijective_id, fun m => ?_⟩
  simp only [id_eq, Function.comp_apply]
  congr 1
  show i'.succSuccAbove j' (k'.succAbove m) = k.succAbove (i.succSuccAbove j m)
  apply Fin.val_injective
  simp only [i', j', k', Fin.succSuccAbove, Fin.succAbove, Fin.predPredAbove, lt_def, val_castSucc,
    val_succ, apply_ite Fin.val, apply_dite Fin.val]
  grind (splits := 60)

lemma succSuccAbove_succAbove_comm {n : ℕ} {c : Fin (n + 1 + 1 + 1) → C}
    (k : Fin (n + 1)) (i j : Fin (n + 1 + 1 + 1)) :
    -- The corresponding position of k in the full list.
    let k' := Fin.succSuccAbove i j k
    let k'' := Fin.predAbove 0 k'
    -- The position of i after removing k'
    let i' := k''.predAbove i
    -- The position of j after removing k'
    let j' := k''.predAbove j
    IsReindexing ((c ∘ k'.succAbove) ∘ i'.succSuccAbove j')
      ((c ∘ i.succSuccAbove j) ∘ k.succAbove) id := by
  refine ⟨Function.bijective_id, fun m => ?_⟩
  simp only [id_eq, Function.comp_apply]
  congr 1
  exact Fin.succSuccAbove_succAbove_comm_apply i j k m

/-- Removing two single entries from `c` in either order gives the same colour list:
  removing the `k1`-th entry and then the (shifted) `k2`-th entry matches removing the
  `k2`-th entry first and then the (shifted) `k1`-th entry, via the identity permutation.
  This is used for the commutation of two *evaluations* of indices. -/
lemma succAbove_succAbove_comm {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (k1 : Fin (n + 1 + 1)) (k2 : Fin (n + 1)) :
    let k2' := k1.succAbove k2;
    let k1' := k2.predAbove k1;
    IsReindexing ((c ∘ k2'.succAbove) ∘ k1'.succAbove)
      ((c ∘ k1.succAbove) ∘ k2.succAbove) id := by
  intro k2' k1'
  refine ⟨Function.bijective_id, fun m => ?_⟩
  simp only [id_eq, Function.comp_apply]
  congr 1
  exact Fin.succAbove_succAbove_succAbove_predAbove k1 k2 m


/-- Splitting a list of colours `c : Fin (n + 1) → C` into its first `n` entries and its
  last entry recovers `c`: the identity permutation matches
  `Fin.append (c ∘ (Fin.last n).succAbove) ![c (Fin.last n)]` with `c`. -/
lemma append_succ_last {n : ℕ} (c : Fin (n + 1) → C) :
    IsReindexing (Fin.append (c ∘ (Fin.last n).succAbove) ![c (Fin.last n)]) c id := by
  rw [Fin.succAbove_last, on_id]
  refine Fin.addCases (fun i => ?_) (fun i => ?_)
  · simp only [Fin.append_left, Function.comp_apply]; rfl
  · fin_cases i; simp only [Fin.append_right, Matrix.cons_val_fin_one]; rfl

/-- Splitting a list of colours `c : Fin (n + 1) → C` at an arbitrary slot `i`, rather than at the
  last one as in `append_succ_last`: the block map that lists the `i.succAbove` survivors and then
  `i` itself matches `c` with the survivors of `i` followed by the surviving entry `c1 1` of a
  rank-two list `c1` whose second entry is slot `i`'s colour. -/
lemma move_last {n : ℕ} {c : Fin (n + 1) → C} {c1 : Fin 2 → C} (i : Fin (n + 1))
    (hc : c i = c1 1) :
    IsReindexing c
      (Fin.append (c ∘ i.succAbove) (c1 ∘ (0 : Fin 2).succAbove))
      (Fin.append i.succAbove (fun _ : Fin 1 => i)) :=
  ⟨by
      rw [Fin.append_succAbove_const_eq_cycleIcc i]
      exact (Fin.cycleIcc i (Fin.last n)).bijective,
    fun x => by
      refine Fin.addCases (fun a => ?_) (fun a => ?_) x
      · simp [Fin.append_left]
      · fin_cases a
        simp [Fin.append_right, hc]⟩

/-- Updating slot `i` of `c` to `d` and then back to `e = c i` returns `c`, no other slot moving:
  the colour cast a round trip of two contractions at slot `i` generates. -/
lemma update_update_of_eq {n : ℕ} {c : Fin n → C} {d e : C} (i : Fin n) (he : c i = e) :
    IsReindexing c (Function.update (Function.update c i d) i e) (id : Fin n → Fin n) :=
  on_id.mpr (fun j => by by_cases h : j = i <;> simp [h, Function.update_of_ne, he])

/-- Splitting a list of colours `c : Fin (n + 1) → C` into its first entry and its remaining
  `n` entries recovers `c`: the canonical reindexing `Fin (1 + n) ≃ Fin (n + 1)` matches
  `Fin.append ![c 0] (c ∘ Fin.succAbove 0)` with `c`. -/
lemma append_of_first {n : ℕ} (c : Fin (n + 1) → C) :
    IsReindexing (Fin.append ![c 0] (c ∘ Fin.succAbove 0)) c (Fin.cast (by grind)) := by
  refine ⟨(finCongr (by grind)).bijective, fun i => ?_⟩
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rfl
  · simpa using congrArg (Fin.append ![c 0] (c ∘ Fin.succ)) (a₁ := Fin.cast _ i.succ)
      (a₂ := Fin.natAdd 1 i) (by ext; grind)

/-- Casting the domain along an equality `n1 = n` of lengths is a reindexing of `c` by
  `c ∘ Fin.cast h`. -/
lemma fin_cast_isReindexing (n n1 : ℕ) {c : Fin n → C} (h : n1 = n) :
    IsReindexing c (c ∘ Fin.cast h) (Fin.cast h) := by
  apply And.intro
  · exact Equiv.bijective (finCongr h)
  · intro i
    rfl

end IsReindexing

end Tensor

end TensorSpecies
