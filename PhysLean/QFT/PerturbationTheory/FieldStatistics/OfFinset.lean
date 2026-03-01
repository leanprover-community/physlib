/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.PerturbationTheory.FieldStatistics.Basic
import Mathlib.Data.Finset.Sort
/-!

# Field statistics of a finite set.

-/

namespace FieldStatistic

variable {𝓕 : Type}

/-- The field statistic associated with a map `f : Fin n → 𝓕` (usually `.get` of a list)
  and a finite set of elements of `Fin n`. -/
def ofFinset {n : ℕ} (q : 𝓕 → FieldStatistic) (f : Fin n → 𝓕) (a : Finset (Fin n)) :
    FieldStatistic :=
  ofList q ((a.sort (· ≤ ·)).map f)

@[simp]
lemma ofFinset_empty (q : 𝓕 → FieldStatistic) (f : Fin n → 𝓕) :
    ofFinset q f ∅ = 1 := by
  simp only [ofFinset, Finset.sort_empty, List.map_nil, ofList_empty]
  rfl

lemma ofFinset_singleton {n : ℕ} (q : 𝓕 → FieldStatistic) (f : Fin n → 𝓕) (i : Fin n) :
    ofFinset q f {i} = q (f i) := by
  simp [ofFinset]

lemma ofFinset_finset_map {n m : ℕ}
    (q : 𝓕 → FieldStatistic) (i : Fin m → Fin n) (hi : Function.Injective i)
    (f : Fin n → 𝓕) (a : Finset (Fin m)) :
    ofFinset q (f ∘ i) a = ofFinset q f (a.map ⟨i, hi⟩) := by
  simp only [ofFinset]
  apply FieldStatistic.ofList_perm
  rw [← List.map_map]
  refine List.Perm.map f ?_
  apply List.perm_of_nodup_nodup_toFinset_eq
  · refine (List.nodup_map_iff_inj_on ?_).mpr ?_
    exact a.sort_nodup (fun x1 x2 => x1 ≤ x2)
    simp only [Finset.mem_sort]
    intro x hx y hy
    exact fun a => hi a
  · exact (Finset.map { toFun := i, inj' := hi } a).sort_nodup (fun x1 x2 => x1 ≤ x2)
  · ext a
    simp

lemma ofFinset_insert (q : 𝓕 → FieldStatistic) (φs : List 𝓕) (a : Finset (Fin φs.length))
    (i : Fin φs.length) (h : i ∉ a) :
    ofFinset q φs.get (Insert.insert i a) = (q φs[i]) * ofFinset q φs.get a := by
  simp only [ofFinset, instCommGroup, Fin.getElem_fin]
  rw [← ofList_cons_eq_mul]
  have h1 : (φs[↑i] :: List.map φs.get (a.sort (fun x1 x2 => x1 ≤ x2)))
      = List.map φs.get (i :: a.sort (fun x1 x2 => x1 ≤ x2)) := by
      simp
  erw [h1]
  apply ofList_perm
  refine List.Perm.map φs.get ?_
  refine (List.perm_ext_iff_of_nodup ?_ ?_).mpr ?_
  · exact (Insert.insert i a).sort_nodup (fun x1 x2 => x1 ≤ x2)
  · simp only [List.nodup_cons, Finset.mem_sort, Finset.sort_nodup, and_true]
    exact h
  intro a
  simp

lemma ofFinset_erase (q : 𝓕 → FieldStatistic) (φs : List 𝓕) (a : Finset (Fin φs.length))
    (i : Fin φs.length) (h : i ∈ a) :
    ofFinset q φs.get (a.erase i) = (q φs[i]) * ofFinset q φs.get a := by
  have ha : a = Insert.insert i (a.erase i) := by
    exact Eq.symm (Finset.insert_erase h)
  conv_rhs => rw [ha]
  rw [ofFinset_insert]
  rw [← mul_assoc]
  simp only [instCommGroup, Fin.getElem_fin, mul_self, one_mul]
  simp

lemma ofFinset_eq_prod (q : 𝓕 → FieldStatistic) (φs : List 𝓕) (a : Finset (Fin φs.length)) :
    ofFinset q φs.get a = ∏ (i : Fin φs.length), if i ∈ a then (q φs[i]) else 1 := by
  rw [ofFinset]
  rw [ofList_map_eq_finset_prod]
  congr
  funext i
  simp only [Finset.mem_sort, Fin.getElem_fin]
  exact a.sort_nodup (fun x1 x2 => x1 ≤ x2)

lemma ofFinset_union (q : 𝓕 → FieldStatistic) (φs : List 𝓕) (a b : Finset (Fin φs.length)) :
    ofFinset q φs.get a * ofFinset q φs.get b = ofFinset q φs.get ((a ∪ b) \ (a ∩ b)) := by
  rw [ofFinset_eq_prod, ofFinset_eq_prod, ofFinset_eq_prod]
  rw [← Finset.prod_mul_distrib]
  congr
  funext x
  simp only [instCommGroup, Fin.getElem_fin, mul_ite, ite_mul, mul_self, one_mul, mul_one,
    Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, not_and]
  split
  · rename_i h
    simp [h]
  · rename_i h
    simp [h]

lemma ofFinset_union_disjoint (q : 𝓕 → FieldStatistic) (φs : List 𝓕) (a b : Finset (Fin φs.length))
    (h : Disjoint a b) :
    ofFinset q φs.get a * ofFinset q φs.get b = ofFinset q φs.get (a ∪ b) := by
  rw [ofFinset_union, Finset.disjoint_iff_inter_eq_empty.mp h]
  simp

lemma ofFinset_filter_mul_neg (q : 𝓕 → FieldStatistic) (φs : List 𝓕) (a : Finset (Fin φs.length))
    (p : Fin φs.length → Prop) [DecidablePred p] :
    ofFinset q φs.get (Finset.filter p a) *
    ofFinset q φs.get (Finset.filter (fun i => ¬ p i) a) = ofFinset q φs.get a := by
  rw [ofFinset_union_disjoint]
  congr
  exact Finset.filter_union_filter_not_eq p a
  exact Finset.disjoint_filter_filter_not a a p

lemma ofFinset_filter (q : 𝓕 → FieldStatistic) (φs : List 𝓕) (a : Finset (Fin φs.length))
    (p : Fin φs.length → Prop) [DecidablePred p] :
    ofFinset q φs.get (Finset.filter p a) = ofFinset q φs.get (Finset.filter (fun i => ¬ p i) a) *
    ofFinset q φs.get a := by
  rw [← ofFinset_filter_mul_neg q φs a p]
  conv_rhs =>
    rhs
    rw [mul_comm]
  rw [← mul_assoc]
  simp

end FieldStatistic
