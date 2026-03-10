/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
meta import Mathlib.Data.Fintype.Sigma
meta import PhysLean.QFT.PerturbationTheory.WickContraction.InsertAndContractNat
import all Init.Data.Fin.Fold
public import PhysLean.QFT.PerturbationTheory.WickContraction.InsertAndContractNat
/-!

# Equivalence extracting element from contraction

-/

@[expose] public section

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open PhysLean.List
open PhysLean.Fin

lemma extractEquiv_equiv {c1 c2 : (c : WickContraction n) × Option c.uncontracted}
    (h : c1.1 = c2.1) (ho : c1.2 = uncontractedCongr (by rw [h]) c2.2) : c1 = c2 := by
  cases c1
  cases c2
  simp_all only [Sigma.mk.inj_iff]
  simp only at h
  subst h
  simp only [uncontractedCongr, Equiv.optionCongr_apply, heq_eq_eq, true_and]
  rename_i a
  match a with
  | none => simp
  | some a =>
    simp only [Option.map_some, Option.some.injEq]
    ext
    simp

/-- The equivalence between `WickContraction n.succ` and the sigma type
  `(c : WickContraction n) × Option c.uncontracted` formed by inserting
  and erasing elements from a contraction. -/
def extractEquiv (i : Fin n.succ) : WickContraction n.succ ≃
    (c : WickContraction n) × Option c.uncontracted where
  toFun := fun c => ⟨erase c i, getDualErase c i⟩
  invFun := fun ⟨c, j⟩ => insertAndContractNat c i j
  left_inv f := by
    simp
  right_inv f := by
    refine extractEquiv_equiv ?_ ?_
    simp only [insertAndContractNat_erase]
    simp only [Nat.succ_eq_add_one]
    have h1 := insertAndContractNat_getDualErase f.fst i f.snd
    exact insertAndContractNat_getDualErase _ i _

lemma extractEquiv_symm_none_uncontracted (i : Fin n.succ) (c : WickContraction n) :
    ((extractEquiv i).symm ⟨c, none⟩).uncontracted =
    (Insert.insert i (c.uncontracted.map i.succAboveEmb)) := by
  exact insertAndContractNat_none_uncontracted c i

@[simp]
lemma extractEquiv_apply_congr_symm_apply {n m : ℕ} (k : ℕ)
    (hnk : k < n.succ) (hkm : k < m.succ) (hnm : n = m) (c : WickContraction n)
    (i : c.uncontracted) : congr (by rw [hnm]) ((extractEquiv ⟨k, hkm⟩
    (congr (by rw [hnm]) ((extractEquiv ⟨k, hnk⟩).symm ⟨c, i⟩)))).1 = c := by
  subst hnm
  simp

/-- The fintype instance of `WickContraction 0` defined through its single
  element `empty`. -/
instance fintype_zero : Fintype (WickContraction 0) where
  elems := {empty}
  complete := by
    intro c
    simp only [Finset.mem_singleton]
    apply Subtype.ext
    simp only [empty]
    ext a
    apply Iff.intro
    · intro h
      have hc := c.2.1 a h
      rw [Finset.card_eq_two] at hc
      obtain ⟨x, y, hxy, ha⟩ := hc
      exact Fin.elim0 x
    · simp

lemma sum_WickContraction_nil (f : WickContraction 0 → M) [AddCommMonoid M] :
    ∑ c, f c = f empty := by
  rw [Finset.sum_eq_single_of_mem]
  simp only [Finset.mem_univ]
  intro b hb
  fin_cases b
  simp

/-- The fintype instance of `WickContraction n`, for `n.succ` this is defined
  through the equivalence `extractEquiv`. -/
instance fintype_succ : (n : ℕ) → Fintype (WickContraction n)
  | 0 => fintype_zero
  | Nat.succ n => by
    letI := fintype_succ n
    exact Fintype.ofEquiv _ (extractEquiv 0).symm

lemma sum_extractEquiv_congr [AddCommMonoid M] {n m : ℕ} (i : Fin n) (f : WickContraction n → M)
    (h : n = m.succ) :
    ∑ c, f c = ∑ (c : WickContraction m), ∑ (k : Option c.uncontracted),
    f (congr h.symm ((extractEquiv (finCongr h i)).symm ⟨c, k⟩)) := by
  subst h
  simp only [finCongr_refl, Equiv.refl_apply, congr_refl]
  rw [← (extractEquiv i).symm.sum_comp]
  rw [Finset.sum_sigma']
  rfl

/-- For `n = 3` there are `4` possible Wick contractions:

- `∅`, corresponding to the case where no fields are contracted.
- `{{0, 1}}`, corresponding to the case where the field at position `0` and `1` are contracted.
- `{{0, 2}}`, corresponding to the case where the field at position `0` and `2` are contracted.
- `{{1, 2}}`, corresponding to the case where the field at position `1` and `2` are contracted.

The proof of this result uses the fact that Lean is an executable programming language
and can calculate all Wick contractions for a given `n`. -/
lemma mem_three (c : WickContraction 3) : c.1 ∈ ({∅, {{0, 1}}, {{0, 2}}, {{1, 2}}} :
    Finset (Finset (Finset (Fin 3)))) := by
  revert c
  decide +kernel

/-- For `n = 4` there are `10` possible Wick contractions including e.g.

- `∅`, corresponding to the case where no fields are contracted.
- `{{0, 1}, {2, 3}}`, corresponding to the case where the fields at position `0` and `1` are
  contracted, and the fields at position `2` and `3` are contracted.
- `{{0, 2}, {1, 3}}`, corresponding to the case where the fields at position `0` and `2` are
  contracted, and the fields at position `1` and `3` are contracted.

The proof of this result uses the fact that Lean is an executable programming language
and can calculate all Wick contractions for a given `n`.
-/
lemma mem_four (c : WickContraction 4) : c.1 ∈ ({∅,
    {{0, 1}}, {{0, 2}}, {{0, 3}}, {{1, 2}}, {{1, 3}}, {{2,3}},
    {{0, 1}, {2, 3}}, {{0, 2}, {1, 3}}, {{0, 3}, {1, 2}}} :
    Finset (Finset (Finset (Fin 4)))) := by
  revert c
  decide +kernel

end WickContraction
