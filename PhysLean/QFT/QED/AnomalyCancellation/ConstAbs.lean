/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.QED.AnomalyCancellation.VectorLike
/-!
# Charges assignments with constant abs

We look at charge assignments in which all charges have the same absolute value.

-/

open Nat
open Finset
open BigOperators

namespace PureU1

variable {n : ℕ}

/-- The condition for two rationals to have the same square (equivalent to same abs). -/
def ConstAbsProp : ℚ × ℚ → Prop := fun s => s.1^2 = s.2^2

/-- The condition on a charge assignment `S` to have constant absolute value among charges. -/
@[simp]
def ConstAbs (S : (PureU1 n).Charges) : Prop := ∀ i j, (S i) ^ 2 = (S j) ^ 2

lemma constAbs_perm (S : (PureU1 n).Charges) (M :(FamilyPermutations n).group) :
    ConstAbs ((FamilyPermutations n).rep M S) ↔ ConstAbs S := by
  simp only [ConstAbs, PureU1_numberCharges, FamilyPermutations, PermGroup, permCharges,
    MonoidHom.coe_mk, OneHom.coe_mk, chargeMap_apply]
  refine Iff.intro (fun h i j => ?_) (fun h i j => h (M.invFun i) (M.invFun j))
  have h2 := h (M.toFun i) (M.toFun j)
  simp only [Equiv.toFun_as_coe, Equiv.Perm.coe_inv, Equiv.symm_apply_apply] at h2
  exact h2

lemma constAbs_sort {S : (PureU1 n).Charges} (CA : ConstAbs S) : ConstAbs (sort S) := by
  rw [sort]
  exact (constAbs_perm S _).mpr CA

/-- The condition for a set of charges to be `sorted`, and have `constAbs`-/
def ConstAbsSorted (S : (PureU1 n).Charges) : Prop := ConstAbs S ∧ Sorted S

namespace ConstAbsSorted
section charges

variable {S : (PureU1 n.succ).Charges} {A : (PureU1 n.succ).LinSols}
variable (hS : ConstAbsSorted S) (hA : ConstAbsSorted A.val)

include hS in
lemma lt_eq {k i : Fin n.succ} (hk : S k ≤ 0) (hik : i ≤ k) : S i = S k := by
  have hSS := hS.2 i k hik
  have ht := hS.1 i k
  rw [sq_eq_sq_iff_eq_or_eq_neg] at ht
  cases ht <;> rename_i h
  · exact h
  · linarith

include hS in
lemma val_le_zero {i : Fin n.succ} (hi : S i ≤ 0) : S i = S (0 : Fin n.succ) := by
  symm
  apply lt_eq hS hi
  exact Fin.zero_le i

include hS in
lemma gt_eq {k i: Fin n.succ} (hk : 0 ≤ S k) (hik : k ≤ i) : S i = S k := by
  have hSS := hS.2 k i hik
  have ht := hS.1 i k
  rw [sq_eq_sq_iff_eq_or_eq_neg] at ht
  cases ht <;> rename_i h
  · exact h
  · linarith

include hS in
lemma zero_gt (h0 : 0 ≤ S (0 : Fin n.succ)) (i : Fin n.succ) : S (0 : Fin n.succ) = S i := by
  symm
  refine gt_eq hS h0 (Fin.zero_le i)

include hS in
lemma opposite_signs_eq_neg {i j : Fin n.succ} (hi : S i ≤ 0) (hj : 0 ≤ S j) : S i = - S j := by
  have hSS := hS.1 i j
  rw [sq_eq_sq_iff_eq_or_eq_neg] at hSS
  cases' hSS with h h
  · simp_all
    linarith
  · exact h

include hS in
lemma is_zero (h0 : S (0 : Fin n.succ) = 0) : S = 0 := by
  funext i
  have ht := hS.1 i (0 : Fin n.succ)
  rw [h0] at ht
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, pow_eq_zero_iff] at ht
  exact ht

/-- A boundary of `S : (PureU1 n.succ).charges` (assumed sorted, constAbs and non-zero)
is defined as a element of `k ∈ Fin n` such that `S k.castSucc` and `S k.succ` are different signs.
-/
@[simp]
def Boundary (S : (PureU1 n.succ).Charges) (k : Fin n) : Prop := S k.castSucc < 0 ∧ 0 < S k.succ

include hS in
lemma boundary_castSucc {k : Fin n} (hk : Boundary S k) : S k.castSucc = S (0 : Fin n.succ) :=
  (lt_eq hS (le_of_lt hk.left) (Fin.zero_le k.castSucc : 0 ≤ k.castSucc)).symm

include hS in
lemma boundary_succ {k : Fin n} (hk : Boundary S k) : S k.succ = - S (0 : Fin n.succ) := by
  have hn := boundary_castSucc hS hk
  rw [opposite_signs_eq_neg hS (le_of_lt hk.left) (le_of_lt hk.right)] at hn
  linear_combination -(1 * hn)

lemma boundary_split (k : Fin n) : k.succ.val + (n.succ - k.succ.val) = n.succ := by
  omega

lemma boundary_accGrav' (k : Fin n) : accGrav n.succ S =
    ∑ i : Fin (k.succ.val + (n.succ - k.succ.val)), S (Fin.cast (boundary_split k) i) := by
  simp only [succ_eq_add_one, accGrav, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_succ,
    PureU1_numberCharges]
  erw [Finset.sum_equiv (Fin.castOrderIso (boundary_split k)).toEquiv]
  · intro i
    simp only [Fin.val_succ, mem_univ, RelIso.coe_fn_toEquiv]
  · exact fun _ _ => rfl

include hS in
lemma boundary_accGrav'' (k : Fin n) (hk : Boundary S k) :
    accGrav n.succ S = (2 * ↑↑k + 1 - ↑n) * S (0 : Fin n.succ) := by
  rw [boundary_accGrav' k]
  rw [Fin.sum_univ_add]
  have hfst (i : Fin k.succ.val) :
      S (Fin.cast (boundary_split k) (Fin.castAdd (n.succ - k.succ.val) i)) = S k.castSucc := by
    apply lt_eq hS (le_of_lt hk.left) (Fin.is_le i)
  have hsnd (i : Fin (n.succ - k.succ.val)) :
      S (Fin.cast (boundary_split k) (Fin.natAdd (k.succ.val) i)) = S k.succ := by
    apply gt_eq hS (le_of_lt hk.right) (by rw [Fin.le_def]; exact le.intro rfl)
  simp only [hfst, hsnd]
  simp only [Fin.val_succ, sum_const, Finset.card_fin, nsmul_eq_mul, cast_add, cast_one,
    succ_sub_succ_eq_sub, Fin.is_le', cast_sub]
  rw [boundary_castSucc hS hk, boundary_succ hS hk]
  ring

/-- A `S ∈ charges` has a boundary if there exists a `k ∈ Fin n` which is a boundary. -/
@[simp]
def HasBoundary (S : (PureU1 n.succ).Charges) : Prop :=
  ∃ (k : Fin n), Boundary S k

include hS in
lemma not_hasBoundary_zero_le (hnot : ¬ (HasBoundary S)) (h0 : S (0 : Fin n.succ) < 0) :
    ∀ i, S (0 : Fin n.succ) = S i := by
  intro ⟨i, hi⟩
  simp only [HasBoundary, Boundary, not_exists, not_and, not_lt] at hnot
  induction i
  · rfl
  · rename_i i hii
    have hnott := hnot ⟨i, succ_lt_succ_iff.mp hi⟩
    have hii := hii (lt_of_succ_lt hi)
    erw [← hii] at hnott
    exact (val_le_zero hS (hnott h0)).symm

include hS in
lemma not_hasBoundry_zero (hnot : ¬ (HasBoundary S)) (i : Fin n.succ) :
    S (0 : Fin n.succ) = S i := by
  by_cases hi : S (0 : Fin n.succ) < 0
  · exact not_hasBoundary_zero_le hS hnot hi i
  · simp only [not_lt] at hi
    exact zero_gt hS hi i

include hS in
lemma not_hasBoundary_grav (hnot : ¬ (HasBoundary S)) :
    accGrav n.succ S = n.succ * S (0 : Fin n.succ) := by
  simp [accGrav, ← not_hasBoundry_zero hS hnot]

include hA in
lemma AFL_hasBoundary (h : A.val (0 : Fin n.succ) ≠ 0) : HasBoundary A.val := by
  by_contra hn
  have h0 := not_hasBoundary_grav hA hn
  simp only [succ_eq_add_one, accGrav, LinearMap.coe_mk, AddHom.coe_mk, cast_add, cast_one] at h0
  rw [pureU1_linear A] at h0
  simp only [zero_eq_mul] at h0
  cases' h0
  · linarith
  · simp_all

lemma AFL_odd_noBoundary {A : (PureU1 (2 * n + 1)).LinSols} (h : ConstAbsSorted A.val)
    (hA : A.val (0 : Fin (2*n +1)) ≠ 0) : ¬ HasBoundary A.val := by
  by_contra hn
  obtain ⟨k, hk⟩ := hn
  have h0 := boundary_accGrav'' h k hk
  simp only [succ_eq_add_one, accGrav, LinearMap.coe_mk, AddHom.coe_mk, cast_mul, cast_ofNat] at h0
  rw [pureU1_linear A] at h0
  simp only [zero_eq_mul, hA, or_false] at h0
  have h1 : 2 * n = 2 * k.val + 1 := by
    rw [← @Nat.cast_inj ℚ]
    simp only [cast_mul, cast_ofNat, cast_add, cast_one]
    linear_combination - h0
  omega

lemma AFL_odd_zero {A : (PureU1 (2 * n + 1)).LinSols} (h : ConstAbsSorted A.val) :
    A.val (0 : Fin (2 * n + 1)) = 0 := by
  by_contra hn
  exact (AFL_odd_noBoundary h hn) (AFL_hasBoundary h hn)

theorem AFL_odd (A : (PureU1 (2 * n + 1)).LinSols) (h : ConstAbsSorted A.val) :
    A = 0 := by
  apply ACCSystemLinear.LinSols.ext
  exact is_zero h (AFL_odd_zero h)

lemma AFL_even_Boundary {A : (PureU1 (2 * n.succ)).LinSols} (h : ConstAbsSorted A.val)
    (hA : A.val (0 : Fin (2 * n.succ)) ≠ 0) {k : Fin (2 * n + 1)} (hk : Boundary A.val k) :
    k.val = n := by
  have h0 := boundary_accGrav'' h k hk
  change ∑ i, A.val i = _ at h0
  simp only [succ_eq_add_one, PureU1_numberCharges, mul_eq, cast_add, cast_mul, cast_ofNat,
    cast_one, add_sub_add_right_eq_sub] at h0
  rw [pureU1_linear A] at h0
  simp only [zero_eq_mul, hA, or_false] at h0
  rw [← @Nat.cast_inj ℚ]
  linear_combination h0 / 2

lemma AFL_even_below' {A : (PureU1 (2 * n.succ)).LinSols} (h : ConstAbsSorted A.val)
    (hA : A.val (0 : Fin (2 * n.succ)) ≠ 0) (i : Fin n.succ) :
    A.val (Fin.cast (split_equal n.succ) (Fin.castAdd n.succ i)) = A.val (0 : Fin (2*n.succ)) := by
  obtain ⟨k, hk⟩ := AFL_hasBoundary h hA
  rw [← boundary_castSucc h hk]
  apply lt_eq h (le_of_lt hk.left)
  rw [Fin.le_def]
  simp only [PureU1_numberCharges, Fin.val_cast, Fin.val_castAdd, mul_eq, Fin.val_castSucc]
  rw [AFL_even_Boundary h hA hk]
  exact Fin.is_le i

lemma AFL_even_below (A : (PureU1 (2 * n.succ)).LinSols) (h : ConstAbsSorted A.val)
    (i : Fin n.succ) :
    A.val (Fin.cast (split_equal n.succ) (Fin.castAdd n.succ i))
    = A.val (0 : Fin (2*n.succ)) := by
  by_cases hA : A.val (0 : Fin (2*n.succ)) = 0
  · rw [is_zero h hA]
    rfl
  · exact AFL_even_below' h hA i

lemma AFL_even_above' {A : (PureU1 (2 * n.succ)).LinSols} (h : ConstAbsSorted A.val)
    (hA : A.val (0 : Fin (2*n.succ)) ≠ 0) (i : Fin n.succ) :
    A.val (Fin.cast (split_equal n.succ) (Fin.natAdd n.succ i)) =
    - A.val (0 : Fin (2*n.succ)) := by
  obtain ⟨k, hk⟩ := AFL_hasBoundary h hA
  rw [← boundary_succ h hk]
  apply gt_eq h (le_of_lt hk.right)
  rw [Fin.le_def]
  simp only [mul_eq, Fin.val_succ, PureU1_numberCharges, Fin.val_cast, Fin.val_natAdd]
  rw [AFL_even_Boundary h hA hk]
  exact Nat.le_add_right (n + 1) ↑i

lemma AFL_even_above (A : (PureU1 (2 * n.succ)).LinSols) (h : ConstAbsSorted A.val)
    (i : Fin n.succ) :
    A.val (Fin.cast (split_equal n.succ) (Fin.natAdd n.succ i)) =
    - A.val (0 : Fin (2 * n.succ)) := by
  by_cases hA : A.val (0 : Fin (2 * n.succ)) = 0
  · rw [is_zero h hA]
    rfl
  · exact AFL_even_above' h hA i

end charges

end ConstAbsSorted

namespace ConstAbs

theorem boundary_value_odd (S : (PureU1 (2 * n + 1)).LinSols) (hs : ConstAbs S.val) :
    S = 0 :=
  have hS := And.intro (constAbs_sort hs) (sort_sorted S.val)
  sortAFL_zero S (ConstAbsSorted.AFL_odd (sortAFL S) hS)

theorem boundary_value_even (S : (PureU1 (2 * n.succ)).LinSols) (hs : ConstAbs S.val) :
    VectorLikeEven S.val := by
  have hS := And.intro (constAbs_sort hs) (sort_sorted S.val)
  intro i
  have h1 := ConstAbsSorted.AFL_even_below (sortAFL S) hS
  have h2 := ConstAbsSorted.AFL_even_above (sortAFL S) hS
  rw [sortAFL_val] at h1 h2
  rw [h1, h2]
  exact (InvolutiveNeg.neg_neg (sort S.val _)).symm

end ConstAbs

end PureU1
