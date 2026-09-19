/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.SuccPred
/-!

# Defining succSuccAbove

In Mathlib there is the `Fin.succAbove` function which gives an embedding of `Fin n` into
`Fin (n + 1)` by leaving a hole at a specified index. We will need a version of this which
gives an embedding of `Fin n` into `Fin (n + 1 + 1)` by leaving holes at
two specified indices. We call this `succSuccAbove`.

We will also need an explicit inverse of this map from
`Fin (n + 1 + 1)` to `Fin n` which is defined on the complement of the two specified indices.
This is similar to `Fin.predAbove` (although not exactly the same),
for this reason we call it `predPredAbove`.

## Implementation

In previous versions of Physlib the function which is now called `succSuccAbove`
was previously called `dropPairEmb` and the function which is now called `predPredAbove` was
previously called `dropPairEmbPre`.

-/

@[expose] public section

namespace Fin

variable {n : ℕ} {c : Fin (n + 1 + 1) → C}

/-!

## Defining succSuccAbove

-/

/-!
The definition below is deliberately explicit. Later lemmas identify it with
`Finset.orderEmbOfFin` and `Finset.orderIsoOfFin`, giving a bridge to the Mathlib
API while keeping this form convenient for computation and goals solved by
`decide`.
-/

/-- The embedding of `Fin n` into `Fin (n + 1 + 1)` which leaves a hole
  at `i` and `j`. -/
def succSuccAbove (i j : Fin (n + 1 + 1)) (m : Fin n) : Fin (n + 1 + 1) :=
  if m.1 < i.1 ∧ m.1 < j.1 then
    ⟨m, by omega⟩
  else if m.1 + 1 < i.1 ∧ j.1 ≤ m.1 then
    ⟨m + 1, by omega⟩
  else if i.1 ≤ m.1 ∧ m.1 + 1 < j.1 then
    ⟨m + 1, by omega⟩
  else
    ⟨m + 2, by omega⟩

lemma succSuccAbove_val (i j : Fin (n + 1 + 1)) (m : Fin n) :
    (succSuccAbove i j m).val = if m.1 < i.1 ∧ m.1 < j.1 then m.1
    else if m.1 + 1 < i.1 ∧ j.1 ≤ m.1 then m.1 + 1
    else if i.1 ≤ m.1 ∧ m.1 + 1 < j.1 then m.1 + 1
    else m.1 + 2 := by
  simp only [succSuccAbove]
  grind

lemma succSuccAbove_self_apply (i : Fin (n + 1 + 1)) (m : Fin n) :
    succSuccAbove i i m = if m.1 < i.1 then ⟨m.1, by omega⟩ else ⟨m.1 + 2, by omega⟩ := by
  simp only [succSuccAbove, and_self]
  grind

lemma succSuccAbove_eq_succAbove_succAbove (i : Fin (n + 1 + 1)) (j : Fin (n + 1)) :
    succSuccAbove i (i.succAbove j) = i.succAbove ∘ j.succAbove := by
  ext m
  simp only [succSuccAbove, succAbove, lt_def, val_castSucc, Function.comp_apply]
  grind

lemma succSuccAbove_eq_predAbove {i j : Fin (n + 1 + 1)} (hij : i ≠ j) :
    succSuccAbove i j = fun x => i.succAbove (((Fin.predAbove 0 i).predAbove j).succAbove x) := by
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · contradiction
  · ext x
    rw [succSuccAbove_eq_succAbove_succAbove, Function.comp_apply]
    congr
    rcases eq_or_ne i 0 with rfl | hi
    · rfl
    · rw [Fin.predAbove_zero_of_ne_zero hi]
      rcases lt_or_ge (i.pred hi).castSucc (i.succAbove j) with h | h
      · rw [Fin.predAbove_of_castSucc_lt _ _ h, Fin.pred_succAbove]
        rw [← Fin.lt_succAbove_iff_le_castSucc]
        exact lt_of_le_of_ne ((Fin.castSucc_pred_lt_iff hi).mp h) hij
      · rw [Fin.predAbove_of_le_castSucc _ _ h, Fin.castPred_succAbove]
        rw [Fin.castSucc_lt_iff_succ_le, ← Fin.succAbove_lt_iff_succ_le]
        exact (Fin.le_castSucc_pred_iff hi).mp h

lemma succSuccAbove_injective {n : ℕ}
    (i j : Fin (n + 1 + 1)) : Function.Injective (succSuccAbove i j) := by
  intro a b
  simp only [Fin.ext_iff, succSuccAbove_val]
  grind (splits := 20)

@[simp]
lemma succSuccAbove_eq_iff_eq {n : ℕ}
    (i j : Fin (n + 1 + 1)) (m1 m2 : Fin n) :
    succSuccAbove i j m1 = succSuccAbove i j m2 ↔ m1 = m2 := by
  rw [(succSuccAbove_injective i j).eq_iff]

@[simp]
lemma succSuccAbove_leq_iff_leq {n : ℕ}
    (i j : Fin (n + 1 + 1)) (m1 m2 : Fin n) :
    succSuccAbove i j m1 ≤ succSuccAbove i j m2 ↔ m1 ≤ m2 := by
  simp only [Fin.le_def, Fin.succSuccAbove_val]
  grind (splits := 20)

@[simp]
lemma succSuccAbove_lt_iff_lt {n : ℕ}
    (i j : Fin (n + 1 + 1)) (m1 m2 : Fin n) :
    succSuccAbove i j m1 < succSuccAbove i j m2 ↔ m1 < m2 := by
  simp only [Fin.lt_def, Fin.succSuccAbove_val]
  grind (splits := 20)

@[simp]
lemma succSuccAbove_monotone {n : ℕ} (i j : Fin (n + 1 + 1)) :
    Monotone (succSuccAbove i j) := by
  intro a b
  simp

lemma succSuccAbove_strictMono {n : ℕ} (i j : Fin (n + 1 + 1)) :
    StrictMono (succSuccAbove i j) :=
  (succSuccAbove_monotone i j).strictMono_of_injective (succSuccAbove_injective i j)

@[simp]
lemma succSuccAbove_range {i j : Fin (n + 1 + 1)} (hij : i ≠ j) :
    Set.range (succSuccAbove i j) = {i, j}ᶜ := by
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · simp_all
  rw [succSuccAbove_eq_succAbove_succAbove, Set.range_comp, Fin.range_succAbove]
  ext a
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_image]
  apply Iff.intro
  · intro h
    obtain ⟨b, h1, rfl⟩ := h
    simpa using h1
  · intro h
    simp at h
    rcases Fin.eq_self_or_eq_succAbove i a with rfl | ⟨a, rfl⟩
    · simp_all
    use a
    simp_all

lemma succSuccAbove_eq_orderEmbOfFin {n : ℕ}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) :
    succSuccAbove i j = Finset.orderEmbOfFin {i, j}ᶜ
    (by rw [Finset.card_compl]; simp [Finset.card_pair hij]) := by
  apply ((succSuccAbove_strictMono i j).range_inj_of_wellFoundedLT
    (OrderEmbedding.strictMono _)).mp
  simp only [succSuccAbove_range hij, Finset.range_orderEmbOfFin, Finset.coe_compl,
      Finset.coe_insert, Finset.coe_singleton]

lemma succSuccAbove_symm (i j : Fin (n + 1 + 1)) :
    succSuccAbove i j = succSuccAbove j i := by
  ext m
  simp only [succSuccAbove_val]
  grind (splits := 5)

set_option warning.simp.varHead false in
@[simp]
lemma apply_succSuccAbove_symm {c : Fin (n + 1 + 1) → C} (i j : Fin (n + 1 + 1))
    (k : Fin n) : c (succSuccAbove i j k) = c (succSuccAbove j i k) := by
  rw [succSuccAbove_symm]

lemma succSuccAbove_apply_eq_orderIsoOfFin {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (m : Fin n) :
    (succSuccAbove i j) m = (Finset.orderIsoOfFin {i, j}ᶜ
      (by rw [Finset.card_compl]; simp [Finset.card_pair hij])) m := by
  simp [succSuccAbove_eq_orderEmbOfFin i j hij]

lemma succSuccAbove_image_compl {i j : Fin (n + 1 + 1)} (hij : i ≠ j)
    (X : Set (Fin n)) :
    (succSuccAbove i j) '' Xᶜ = ({i, j} ∪ succSuccAbove i j '' X)ᶜ := by
  rw [← compl_inj_iff, Function.Injective.compl_image_eq (succSuccAbove_injective i j)]
  simp only [compl_compl, succSuccAbove_range hij]
  exact Set.union_comm ((succSuccAbove i j) '' X) {i, j}

@[simp]
lemma fst_ne_succSuccAbove_pre (i j : Fin (n + 1 + 1)) (m : Fin n) :
    ¬ i = succSuccAbove i j m := by
  simp only [Fin.ext_iff, succSuccAbove_val]
  grind (splits := 5)

@[simp]
lemma succSuccAbove_ne_fst (i j : Fin (n + 1 + 1)) (m : Fin n) :
    ¬ succSuccAbove i j m = i := by
  simp only [Fin.ext_iff, succSuccAbove_val]
  grind (splits := 5)

@[simp]
lemma snd_ne_succSuccAbove_pre (i j : Fin (n + 1 + 1)) (m : Fin n) :
    ¬ j = (succSuccAbove i j) m := by
  rw [succSuccAbove_symm]
  exact fst_ne_succSuccAbove_pre j i m

@[simp]
lemma succSuccAbove_ne_snd (i j : Fin (n + 1 + 1)) (m : Fin n) :
    ¬ succSuccAbove i j m = j := by
  apply Ne.symm
  simp

lemma eq_or_exists_succSuccAbove(i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1)) :
    m = i ∨ m = j ∨ ∃ m', m = succSuccAbove i j m' := by
  by_cases h : m = i
  · simp [h]
  · by_cases h' : m = j
    · simp [h']
    · obtain ⟨m', rfl⟩ : ∃ y, succSuccAbove i j y = m := by
        simp_all [← Set.mem_range, succSuccAbove_eq_orderEmbOfFin]
      simp

lemma succSuccAbove_apply_lt_lt {n : ℕ}
    (i j : Fin (n + 1 + 1)) (m : Fin n) (hi : m.val < i.val) (hj : m.val < j.val) :
    succSuccAbove i j m = m.castSucc.castSucc := by
  ext
  simp [succSuccAbove, hi, hj]

lemma succSuccAbove_natAdd_apply_castAdd {n n1 : ℕ}
    (i j : Fin (n + 1 + 1)) (m : Fin n1) :
    (succSuccAbove (n := n1 + n) (Fin.natAdd n1 i) (Fin.natAdd n1 j))
    (Fin.castAdd n m) = Fin.castAdd (n + 1 + 1) (m) := by
  simp only [Fin.ext_iff, succSuccAbove_val, natAdd, castAdd]
  grind (splits := 20)

/-- Reinserting a left-block survivor `a` after removing the `i`-th slot of the left block and the
  `j`-th slot of the right block of `Fin ((nA + 1) + (nB + 1))`, the removal read at the contracted
  length `(nA + nB) + 1 + 1`. Unlike `succSuccAbove_natAdd_apply_castAdd` the two holes straddle the
  two blocks, so the statement carries the reshaping `Fin.cast`s. -/
lemma succSuccAbove_castAdd_natAdd_apply_castAdd {nA nB : ℕ} (i : Fin (nA + 1)) (j : Fin (nB + 1))
    (a : Fin nA) :
    Fin.cast (show (nA + nB) + 1 + 1 = (nA + 1) + (nB + 1) by omega)
        ((Fin.cast (show (nA + 1) + (nB + 1) = (nA + nB) + 1 + 1 by omega)
            (Fin.castAdd (nB + 1) i)).succSuccAbove
          (Fin.cast (show (nA + 1) + (nB + 1) = (nA + nB) + 1 + 1 by omega)
            (Fin.natAdd (nA + 1) j)) (Fin.castAdd nB a))
      = Fin.castAdd (nB + 1) (i.succAbove a) := by
  apply Fin.ext
  simp only [Fin.succSuccAbove_val, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
    Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ, apply_ite Fin.val]
  split_ifs <;> omega

/-- Reinserting a right-block survivor, the mirror of
  `Fin.succSuccAbove_castAdd_natAdd_apply_castAdd`. -/
lemma succSuccAbove_castAdd_natAdd_apply_natAdd {nA nB : ℕ} (i : Fin (nA + 1)) (j : Fin (nB + 1))
    (a : Fin nB) :
    Fin.cast (show (nA + nB) + 1 + 1 = (nA + 1) + (nB + 1) by omega)
        ((Fin.cast (show (nA + 1) + (nB + 1) = (nA + nB) + 1 + 1 by omega)
            (Fin.castAdd (nB + 1) i)).succSuccAbove
          (Fin.cast (show (nA + 1) + (nB + 1) = (nA + nB) + 1 + 1 by omega)
            (Fin.natAdd (nA + 1) j)) (Fin.natAdd nA a))
      = Fin.natAdd (nA + 1) (j.succAbove a) := by
  apply Fin.ext
  simp only [Fin.succSuccAbove_val, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, Fin.succAbove,
    Fin.lt_def, Fin.val_castSucc, Fin.val_succ, apply_ite Fin.val]
  split_ifs <;> omega

lemma succSuccAbove_natAdd_image_range_castAdd {n n1 : ℕ}
    (i j : Fin (n + 1 + 1)) :
    (succSuccAbove (n := n1 + n) (Fin.natAdd n1 i) (Fin.natAdd n1 j)) ''
    (Set.range (Fin.castAdd (m := n) (n := n1))) = {i | i.1 < n1} := by
  ext a
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Set.mem_ofPred_eq]
  conv_lhs =>
    enter [1, b]
    rw [succSuccAbove_natAdd_apply_castAdd i j]
  apply Iff.intro
  · rintro ⟨b, rfl⟩
    simp
  · exact fun h ↦ ⟨⟨a, by omega⟩, by simp⟩

lemma succSuccAbove_comm_natAdd {n n1 : ℕ}
    (i j : Fin (n + 1 + 1)) (m : Fin n) :
    succSuccAbove (n := n1 + n) (Fin.natAdd n1 i) (Fin.natAdd n1 j) (Fin.natAdd n1 m)
    = Fin.natAdd (n1) (succSuccAbove i j m) := by
  simp only [succSuccAbove, val_natAdd, add_lt_add_iff_left, add_le_add_iff_left, Fin.ext_iff]
  grind

/-!

## predPredAbove

-/

/-- The preimage of `m` under `succSuccAbove i j hij` given that `m` is not equal
  to `i` or `j`. -/
def predPredAbove (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1))
    (hm : m ≠ i ∧ m ≠ j) : Fin n :=
  if h1 : m.1 < i.1 ∧ m.1 < j.1 then
      ⟨m, by grind⟩
    else if h2 : m.1 - 1 < i.1 ∧ j.1 ≤ m.1 then
      ⟨m - 1, by grind⟩
    else if h3 : i.1 - 1 ≤ m.1 ∧ m.1 < j.1 then
      ⟨m - 1, by grind⟩
    else
      ⟨m - 2, by grind⟩

lemma predPredAbove_val (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1))
    (hm : m ≠ i ∧ m ≠ j) :
    (predPredAbove i j hij m hm).val = if m.1 < i.1 ∧ m.1 < j.1 then m.1
    else if m.1 - 1 < i.1 ∧ j.1 ≤ m.1 then m.1 - 1
    else if i.1 - 1 ≤ m.1 ∧ m.1 < j.1 then m.1 - 1
    else m.1 - 2 := by
  simp only [predPredAbove]
  grind

@[simp]
lemma succSuccAbove_predPredAbove (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1))
    (hm : m ≠ i ∧ m ≠ j) :
    succSuccAbove i j (predPredAbove i j hij m hm) = m := by
  dsimp [succSuccAbove, predPredAbove]
  grind

lemma predPredAbove_eq_orderIsoOfFin (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1))
    (hm : m ≠ i ∧ m ≠ j) :
    predPredAbove i j hij m hm =
    (Finset.orderIsoOfFin {i, j}ᶜ (by rw [Finset.card_compl]; simp [Finset.card_pair hij])).symm
    ⟨m, by simp [hm]⟩ := by
  apply succSuccAbove_injective i j
  conv_rhs => rw [succSuccAbove_apply_eq_orderIsoOfFin hij]
  simp

@[simp]
lemma predPredAbove_injective (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (m1 m2 : Fin (n + 1 + 1)) (hm1 : m1 ≠ i ∧ m1 ≠ j) (hm2 : m2 ≠ i ∧ m2 ≠ j) :
    predPredAbove i j hij m1 hm1 = predPredAbove i j hij m2 hm2 ↔ m1 = m2 := by
  rw [← Function.Injective.eq_iff (succSuccAbove_injective i j)]
  simp

lemma predPredAbove_surjective (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (m : Fin n) : ∃ m' : Fin (n + 1 + 1), ∃ (h : m' ≠ i ∧ m' ≠ j),
    predPredAbove i j hij m' h = m := by
  refine ⟨succSuccAbove i j m, by simp [Ne.symm], succSuccAbove_injective i j ?_⟩
  simp

@[simp]
lemma predPredAbove_succSuccAbove (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (m : Fin n) :
    predPredAbove i j hij (succSuccAbove i j m) (by simp) = m := by
  apply succSuccAbove_injective i j
  simp

/-!

## Commutativity of succSuccAbove

-/
lemma succSuccAbove_comm (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) :
    let i2' := (succSuccAbove i1 j1 i2);
    let j2' := (succSuccAbove i1 j1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', hij2];
    let i1' := (predPredAbove i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (predPredAbove i2' j2' hi2j2' j1 (by simp [i2', j2']));
    succSuccAbove i1 j1 ∘ succSuccAbove i2 j2 =
    succSuccAbove i2' j2' ∘ succSuccAbove i1' j1':= by
  ext m
  simp only [Function.comp_apply, predPredAbove_val, succSuccAbove_val]
  grind (splits := 20)

lemma succSuccAbove_comm_apply (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) (m : Fin n) :
    let i2' := (succSuccAbove i1 j1 i2);
    let j2' := (succSuccAbove i1 j1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', hij2];
    let i1' := (predPredAbove i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (predPredAbove i2' j2' hi2j2' j1 (by simp [i2', j2']));
    succSuccAbove i2' j2' (succSuccAbove i1' j1' m) =
    succSuccAbove i1 j1 (succSuccAbove i2 j2 m) := by
  intro i2' j2' hi2j2' i1' j1'
  change _ = (succSuccAbove i1 j1 ∘ succSuccAbove i2 j2) m
  rw [succSuccAbove_comm i1 j1 i2 j2 hij1 hij2]
  rfl

/-!

## funPredPredAbove

-/

/-- Given a bijection `Fin (n1 + 1 + 1) → Fin (n + 1 + 1))` and a pair `i j : Fin (n1 + 1 + 1)`,
  then `funPredPredAbove i j _ σ _ : Fin n1 → Fin n` corresponds to the induced bijection
  formed by dropping `i` and `j` in the source and their image in the target. -/
def funPredPredAbove {n n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : Function.Bijective σ)
    (m : Fin n1) : Fin n :=
  predPredAbove (σ i) (σ j)
    (by simp [hσ.injective.eq_iff, hij])
    (σ (succSuccAbove i j m)) (by simp [hσ.injective.eq_iff, Ne.symm])

lemma funPredPredAbove_injective {n n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : Function.Bijective σ) :
    Function.Injective (funPredPredAbove i j hij σ hσ) := by
  intro m1 m2 h
  simpa [funPredPredAbove, hσ.injective.eq_iff] using h

lemma funPredPredAbove_surjective {n n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : Function.Bijective σ) :
    Function.Surjective (funPredPredAbove i j hij σ hσ) := by
  intro m
  simp only [funPredPredAbove]
  obtain ⟨m, hm, rfl⟩ := predPredAbove_surjective (σ i) (σ j)
    (by simp [hσ.injective.eq_iff, hij]) m
  simp only [predPredAbove_injective]
  obtain ⟨m', rfl⟩ := hσ.surjective m
  simp only [ne_eq, hσ.injective.eq_iff] at hm ⊢
  rcases eq_or_exists_succSuccAbove i j hij m' with rfl | rfl | ⟨m'', rfl⟩
  · simp_all
  · simp_all
  · exact ⟨m'', rfl⟩

lemma funPredPredAbove_bijective {n n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : Function.Bijective σ) :
    Function.Bijective (funPredPredAbove i j hij σ hσ) := by
  apply And.intro
  · apply funPredPredAbove_injective
  · apply funPredPredAbove_surjective

@[simp]
lemma funPredPredAbove_id { n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j) :
    funPredPredAbove i j hij id (Function.bijective_id) = id := by
  ext1 m
  simp [funPredPredAbove]

/-- Pointwise form of commuting deletion of one slot with deletion of a pair. -/
lemma succSuccAbove_succAbove_comm_apply {n : ℕ} (i j : Fin (n + 1 + 1 + 1))
    (k : Fin (n + 1)) (m : Fin n) :
    (i.succSuccAbove j k).succAbove
        (((Fin.predAbove 0 (i.succSuccAbove j k)).predAbove i).succSuccAbove
          ((Fin.predAbove 0 (i.succSuccAbove j k)).predAbove j) m) =
      i.succSuccAbove j (k.succAbove m) := by
  apply Fin.val_injective
  simp only [Fin.succSuccAbove, Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ, Fin.castPred, apply_ite Fin.val]
  grind (splits := 60)

end Fin
