/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.QED.AnomalyCancellation.BasisLinear
import PhysLean.QFT.QED.AnomalyCancellation.VectorLike
/-!

# Splitting the linear solutions in the even case into two ACC-satisfying planes

## i. Overview

We split the linear solutions of `PureU1 (2 * n.succ)` into two planes,
where every point in either plane satisfies both the linear and cubic anomaly cancellation
conditions.

## ii. Key results

- `P'` : The inclusion of the first plane into linear solutions
- `P_accCube` : The statement that chares from the first plane satisfy the cubic ACC
- `P!'` : The inclusion of the second plane.
- `P!_accCube` : The statement that charges from the second plane satisfy the cubic ACC
- `span_basis` : Every linear solution is the sum of a point from each plane.

## iii. Table of contents

- A. Splitting the charges up into groups
  - A.1. The even split: Spltting the charges up via `n.succ + n.succ`
  - A.2. The shifted even split: Spltting the charges up via `1 + (n + n + 1)`
  - A.3. Lemmas relating the two splittings
- B. The first plane
  - B.1. The basis vectors of the first plane as charges
  - B.2. Components of the basis vectors
  - B.3. The basis vectors satisfy the linear ACCs
  - B.4. The basis vectors satisfy the cubic ACC
  - B.5. The basis vectors as linear solutions
  - B.6. The inclusion of the first plane into charges
  - B.7. Components of the inclusion into charges
  - B.8. The inclusion into charges satisfies the linear and cubic ACCs
  - B.9. Kernel of the inclusion into charges
  - B.10. The inclusion of the plane into linear solutions
  - B.11. The basis vectors are linearly independent
  - B.12. Every vector-like even solution is in the span of the basis of the first plane
- C. The vectors of the basis spanning the second plane, via the shifted even split
  - C.2. Components of the vectors
  - C.3. The vectors satisfy the linear ACCs
  - C.4. The vectors satisfy the cubic ACC
  - C.6. The vectors as linear solutions
  - C.7. The inclusion of the second plane into charges
  - C.8. Components of the inclusion into charges
  - C.9. The inclusion into charges satisfies the cubic ACC
  - C.10. Kernel of the inclusion into charges
  - C.11. The inclusion of the second plane into the span of the basis
  - C.12. The inclusion of the plane into linear solutions
  - C.13. The basis vectors are linearly independent
  - C.14. Properties of the basis vectors relating to the span
  - C.15. Permutations as additions of basis vectors
- D. Mixed cubic ACCs involving points from both planes
- E. The combined basis
  - E.1. As a map into linear solutions
  - E.2. Inclusion of the span of the basis into charges
  - E.3. Components of the inclusion into charges
  - E.4. Kernel of the inclusion into charges
  - E.5. The inclusion of the span of the basis into linear solutions
  - E.6. The combined basis vectors are linearly independent
  - E.7. Injectivity of the inclusion into linear solutions
  - E.8. Cardinality of the basis
  - E.9. The basis vectors as a basis
- F. Every Lienar solution is the sum of a point from each plane
  - F.1. Relation under permutations

## iv. References

- https://arxiv.org/pdf/1912.04804.pdf

-/

open Nat Module Finset BigOperators

namespace PureU1

variable {n : ℕ}

namespace VectorLikeEvenPlane

/-!

## A. Splitting the charges up into groups

We have `2 * n.succ` charges, which we split up in the following ways:

`| evenFst j (0 to n) | evenSnd j (n.succ to n + n.succ)|`

```
| evenShiftZero (0) | evenShiftFst j (1 to n) |
  evenShiftSnd j (n.succ to 2 * n) | evenShiftLast (2 * n.succ - 1) |
```

-/

/-!

### A.1. The even split: Spltting the charges up via `n.succ + n.succ`

-/

/-- The inclusion of `Fin n.succ` into `Fin (n.succ + n.succ)` via the first `n.succ`,
  casted into `Fin (2 * n.succ)`. -/
def evenFst (j : Fin n.succ) : Fin (2 * n.succ) :=
  Fin.cast (split_equal n.succ) (Fin.castAdd n.succ j)

/-- The inclusion of `Fin n.succ` into `Fin (n.succ + n.succ)` via the second `n.succ`,
  casted into `Fin (2 * n.succ)`. -/
def evenSnd (j : Fin n.succ) : Fin (2 * n.succ) :=
  Fin.cast (split_equal n.succ) (Fin.natAdd n.succ j)

lemma ext_even (S T : Fin (2 * n.succ) → ℚ) (h1 : ∀ i, S (evenFst i) = T (evenFst i))
    (h2 : ∀ i, S (evenSnd i) = T (evenSnd i)) : S = T := by
  funext i
  by_cases hi : i.val < n.succ
  · let j : Fin n.succ := ⟨i, hi⟩
    have h2 := h1 j
    have h3 : evenFst j = i := rfl
    rw [h3] at h2
    exact h2
  · let j : Fin n.succ := ⟨i - n.succ, by omega⟩
    have h2 := h2 j
    have h3 : evenSnd j = i := by
      simp only [succ_eq_add_one, evenSnd, Fin.ext_iff, Fin.val_cast, Fin.val_natAdd, j]
      omega
    rw [h3] at h2
    exact h2

lemma sum_even (S : Fin (2 * n.succ) → ℚ) :
    ∑ i, S i = ∑ i : Fin n.succ, ((S ∘ evenFst) i + (S ∘ evenSnd) i) := by
  have h1 : ∑ i, S i = ∑ i : Fin (n.succ + n.succ), S (Fin.cast (split_equal n.succ) i) := by
    rw [Finset.sum_equiv (Fin.castOrderIso (split_equal n.succ)).symm.toEquiv]
    · intro i
      simp only [mem_univ, Fin.symm_castOrderIso, RelIso.coe_fn_toEquiv]
    · exact fun _ _=> rfl
  rw [h1, Fin.sum_univ_add, Finset.sum_add_distrib]
  rfl

/-!

### A.2. The shifted even split: Spltting the charges up via `1 + (n + n + 1)`

-/

lemma n_cond₂ (n : ℕ) : 1 + ((n + n) + 1) = 2 * n.succ := by
  linarith

/-- The inclusion of `Fin n` into `Fin (1 + (n + n + 1))` via the first `n`,
  casted into `Fin (2 * n.succ)`. -/
def evenShiftFst (j : Fin n) : Fin (2 * n.succ) := Fin.cast (n_cond₂ n)
  (Fin.natAdd 1 (Fin.castAdd 1 (Fin.castAdd n j)))

/-- The inclusion of `Fin n` into `Fin (1 + (n + n + 1))` via the second `n`,
  casted into `Fin (2 * n.succ)`. -/
def evenShiftSnd (j : Fin n) : Fin (2 * n.succ) := Fin.cast (n_cond₂ n)
  (Fin.natAdd 1 (Fin.castAdd 1 (Fin.natAdd n j)))

/-- The element of `Fin (1 + (n + n + 1))` corresponding to the first `1`,
  casted into `Fin (2 * n.succ)`. -/
def evenShiftZero : Fin (2 * n.succ) := (Fin.cast (n_cond₂ n) (Fin.castAdd ((n + n) + 1) 0))

/-- The element of `Fin (1 + (n + n + 1))` corresponding to the second `1`,
  casted into `Fin (2 * n.succ)`. -/
def evenShiftLast : Fin (2 * n.succ) := (Fin.cast (n_cond₂ n) (Fin.natAdd 1 (Fin.natAdd (n + n) 0)))

lemma sum_evenShift (S : Fin (2 * n.succ) → ℚ) :
    ∑ i, S i = S evenShiftZero + S evenShiftLast +
    ∑ i : Fin n, ((S ∘ evenShiftFst) i + (S ∘ evenShiftSnd) i) := by
  have h1 : ∑ i, S i = ∑ i : Fin (1 + ((n + n) + 1)), S (Fin.cast (n_cond₂ n) i) := by
    rw [Finset.sum_equiv (Fin.castOrderIso (n_cond₂ n)).symm.toEquiv]
    · intro i
      simp only [mem_univ, Fin.symm_castOrderIso, RelIso.coe_fn_toEquiv]
    · exact fun _ _ => rfl
  rw [h1]
  rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add, Finset.sum_add_distrib]
  simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton, Function.comp_apply]
  repeat rw [Rat.add_assoc]
  apply congrArg
  rw [Rat.add_comm]
  rw [← Rat.add_assoc]
  nth_rewrite 2 [Rat.add_comm]
  repeat rw [Rat.add_assoc]
  nth_rewrite 2 [Rat.add_comm]
  rfl

/-!

### A.3. Lemmas relating the two splittings

-/
lemma evenShiftZero_eq_evenFst_zero : @evenShiftZero n = evenFst 0 := rfl

lemma evenShiftLast_eq_evenSnd_last: @evenShiftLast n = evenSnd (Fin.last n) := by
  rw [Fin.ext_iff]
  simp only [succ_eq_add_one, evenShiftLast, Fin.isValue, Fin.val_cast, Fin.val_natAdd,
    Fin.val_eq_zero, add_zero, evenSnd, Fin.natAdd_last, Fin.val_last]
  omega

lemma evenShiftFst_eq_evenFst_succ (j : Fin n) : evenShiftFst j = evenFst j.succ := by
  rw [Fin.ext_iff, evenFst, evenShiftFst]
  simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd, Fin.val_succ]
  ring

lemma evenShiftSnd_eq_evenSnd_castSucc (j : Fin n) : evenShiftSnd j = evenSnd j.castSucc := by
  rw [Fin.ext_iff, evenSnd, evenShiftSnd]
  simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd, Fin.val_castSucc]
  ring_nf
  rw [Nat.succ_eq_add_one]
  ring

/-!

## B. The first plane

-/

/-!

### B.1. The basis vectors of the first plane as charges

-/

/-- The first part of the basis as charges. -/
def basisAsCharges (j : Fin n.succ) : (PureU1 (2 * n.succ)).Charges :=
  fun i =>
  if i = evenFst j then
    1
  else
    if i = evenSnd j then
      - 1
    else
      0

/-!

### B.2. Components of the basis vectors

-/

lemma basis_on_evenFst_self (j : Fin n.succ) : basisAsCharges j (evenFst j) = 1 := by
  simp [basisAsCharges]

lemma basis_on_evenFst_other {k j : Fin n.succ} (h : k ≠ j) :
    basisAsCharges k (evenFst j) = 0 := by
  simp only [basisAsCharges, succ_eq_add_one, PureU1_numberCharges, evenFst, evenSnd]
  split
  · rename_i h1
    rw [Fin.ext_iff] at h1
    simp_all
    rw [Fin.ext_iff] at h
    simp_all
  · split
    · rename_i h1 h2
      simp_all only [succ_eq_add_one, ne_eq, Fin.natAdd_eq_addNat, Fin.cast_inj, neg_eq_zero,
        one_ne_zero]
      rw [Fin.ext_iff] at h2
      simp only [Fin.val_castAdd, Fin.val_addNat] at h2
      omega
    · rfl

lemma basis_on_other {k : Fin n.succ} {j : Fin (2 * n.succ)} (h1 : j ≠ evenFst k)
    (h2 : j ≠ evenSnd k) : basisAsCharges k j = 0 := by
  simp only [basisAsCharges, succ_eq_add_one, PureU1_numberCharges]
  simp_all only [ne_eq, ↓reduceIte]

lemma basis_evenSnd_eq_neg_evenFst (j i : Fin n.succ) :
    basisAsCharges j (evenSnd i) = - basisAsCharges j (evenFst i) := by
  simp only [basisAsCharges, succ_eq_add_one, PureU1_numberCharges, evenSnd, evenFst]
  split <;> split
  any_goals split
  any_goals rfl
  any_goals split
  any_goals rfl
  all_goals
    rename_i h1 h2
    rw [Fin.ext_iff] at h1 h2
    simp_all
  all_goals
    rename_i h3
    rw [Fin.ext_iff] at h3
    simp_all
  all_goals omega

lemma basis_on_evenSnd_self (j : Fin n.succ) : basisAsCharges j (evenSnd j) = - 1 := by
  rw [basis_evenSnd_eq_neg_evenFst, basis_on_evenFst_self]

lemma basis_on_evenSnd_other {k j : Fin n.succ} (h : k ≠ j) : basisAsCharges k (evenSnd j) = 0 := by
  rw [basis_evenSnd_eq_neg_evenFst, basis_on_evenFst_other h]
  rfl

/-!

### B.3. The basis vectors satisfy the linear ACCs

-/

lemma basis_linearACC (j : Fin n.succ) : (accGrav (2 * n.succ)) (basisAsCharges j) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_even]
  simp [basis_evenSnd_eq_neg_evenFst]
/-!

### B.4. The basis vectors satisfy the cubic ACC

-/
lemma basis_accCube (j : Fin n.succ) :
    accCube (2 * n.succ) (basisAsCharges j) = 0 := by
  rw [accCube_explicit, sum_even]
  apply Finset.sum_eq_zero
  intro i _
  simp only [succ_eq_add_one, Function.comp_apply, basis_evenSnd_eq_neg_evenFst]
  ring

/-!

### B.5. The basis vectors as linear solutions

-/

/-- The first part of the basis as `LinSols`. -/
@[simps!]
def basis (j : Fin n.succ) : (PureU1 (2 * n.succ)).LinSols :=
  ⟨basisAsCharges j, by
    intro i
    simp only [succ_eq_add_one, PureU1_numberLinear] at i
    match i with
    | 0 =>
    exact basis_linearACC j⟩

/-!

### B.6. The inclusion of the first plane into charges

-/

/-- A point in the span of the first part of the basis as a charge. -/
def P (f : Fin n.succ → ℚ) : (PureU1 (2 * n.succ)).Charges := ∑ i, f i • basisAsCharges i

/-!

### B.7. Components of the inclusion into charges

-/

lemma P_evenFst (f : Fin n.succ → ℚ) (j : Fin n.succ) : P f (evenFst j) = f j := by
  rw [P, sum_of_charges]
  simp only [succ_eq_add_one, HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [basis_on_evenFst_self]
    exact Rat.mul_one (f j)
  · intro k _ hkj
    rw [basis_on_evenFst_other hkj]
    exact Rat.mul_zero (f k)
  · simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma P_evenSnd (f : Fin n.succ → ℚ) (j : Fin n.succ) : P f (evenSnd j) = - f j := by
  rw [P, sum_of_charges]
  simp only [succ_eq_add_one, HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · simp only [basis_on_evenSnd_self, mul_neg, mul_one]
  · intro k _ hkj
    simp only [basis_on_evenSnd_other hkj, mul_zero]
  · simp

lemma P_evenSnd_evenFst (f : Fin n.succ → ℚ) : P f ∘ evenSnd = - P f ∘ evenFst := by
  funext j
  simp only [PureU1_numberCharges, Function.comp_apply, Pi.neg_apply]
  rw [P_evenFst, P_evenSnd]

/-!

### B.8. The inclusion into charges satisfies the linear and cubic ACCs

-/

lemma P_linearACC (f : Fin n.succ → ℚ) : (accGrav (2 * n.succ)) (P f) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_even]
  simp [P_evenSnd, P_evenFst]

lemma P_accCube (f : Fin n.succ → ℚ) : accCube (2 * n.succ) (P f) = 0 := by
  rw [accCube_explicit, sum_even]
  apply Finset.sum_eq_zero
  intro i _
  simp only [succ_eq_add_one, Function.comp_apply, P_evenFst, P_evenSnd]
  ring

/-!

### B.9. Kernel of the inclusion into charges

-/

lemma P_zero (f : Fin n.succ → ℚ) (h : P f = 0) : ∀ i, f i = 0 := by
  intro i
  erw [← P_evenFst f]
  rw [h]
  rfl

/-!

### B.10. The inclusion of the plane into linear solutions

-/

/-- A point in the span of the first part of the basis. -/
def P' (f : Fin n.succ → ℚ) : (PureU1 (2 * n.succ)).LinSols := ∑ i, f i • basis i

lemma P'_val (f : Fin n.succ → ℚ) : (P' f).val = P f := by
  simp only [succ_eq_add_one, P', P]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  rfl

/-!

### B.11. The basis vectors are linearly independent

-/

theorem basis_linear_independent : LinearIndependent ℚ (@basis n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change P' f = 0 at h
  have h1 : (P' f).val = 0 :=
    (AddSemiconjBy.eq_zero_iff (ACCSystemLinear.LinSols.val 0)
    (congrFun (congrArg HAdd.hAdd (congrArg ACCSystemLinear.LinSols.val (id (Eq.symm h))))
    (ACCSystemLinear.LinSols.val 0))).mp rfl
  rw [P'_val] at h1
  exact P_zero f h1

/-!

### B.12. Every vector-like even solution is in the span of the basis of the first plane

-/

lemma vectorLikeEven_in_span (S : (PureU1 (2 * n.succ)).LinSols)
    (hS : VectorLikeEven S.val) : ∃ (M : (FamilyPermutations (2 * n.succ)).group),
      (FamilyPermutations (2 * n.succ)).linSolRep M S ∈ Submodule.span ℚ (Set.range basis) := by
  use (Tuple.sort S.val).symm
  change sortAFL S ∈ Submodule.span ℚ (Set.range basis)
  rw [Submodule.mem_span_range_iff_exists_fun ℚ]
  let f : Fin n.succ → ℚ := fun i => (sortAFL S).val (evenFst i)
  use f
  apply ACCSystemLinear.LinSols.ext
  rw [sortAFL_val]
  erw [P'_val]
  apply ext_even
  · intro i
    rw [P_evenFst]
    rfl
  · intro i
    rw [P_evenSnd]
    have ht := hS i
    change sort S.val (evenFst i) = - sort S.val (evenSnd i) at ht
    have h : sort S.val (evenSnd i) = - sort S.val (evenFst i) := by
      rw [ht]
      ring
    rw [h]
    rfl

/-!

## C. The vectors of the basis spanning the second plane, via the shifted even split

-/

/-- The second part of the basis as charges. -/
def basis!AsCharges (j : Fin n) : (PureU1 (2 * n.succ)).Charges :=
  fun i =>
  if i = evenShiftFst j then
    1
  else
    if i = evenShiftSnd j then
      - 1
    else
      0
/-!

### C.2. Components of the vectors

-/

lemma basis!_on_evenShiftFst_self (j : Fin n) : basis!AsCharges j (evenShiftFst j) = 1 := by
  simp [basis!AsCharges]

lemma basis!_on_other {k : Fin n} {j : Fin (2 * n.succ)} (h1 : j ≠ evenShiftFst k)
    (h2 : j ≠ evenShiftSnd k) : basis!AsCharges k j = 0 := by
  simp only [basis!AsCharges, succ_eq_add_one, PureU1_numberCharges]
  simp_all only [ne_eq, ↓reduceIte]

lemma basis!_on_evenShiftFst_other {k j : Fin n} (h : k ≠ j) :
    basis!AsCharges k (evenShiftFst j) = 0 := by
  simp only [basis!AsCharges, succ_eq_add_one, PureU1_numberCharges]
  simp only [evenShiftFst, succ_eq_add_one, evenShiftSnd]
  split
  · rename_i h1
    rw [Fin.ext_iff] at h1
    simp_all
    rw [Fin.ext_iff] at h
    simp_all
  · split
    · rename_i h1 h2
      simp_all
      rw [Fin.ext_iff] at h2
      simp only [Fin.val_castAdd, Fin.val_addNat] at h2
      omega
    · rfl

lemma basis!_evenShftSnd_eq_neg_evenShiftFst (j i : Fin n) :
    basis!AsCharges j (evenShiftSnd i) = - basis!AsCharges j (evenShiftFst i) := by
  simp only [basis!AsCharges, succ_eq_add_one, PureU1_numberCharges, evenShiftSnd, evenShiftFst]
  split <;> split
  any_goals split
  any_goals split
  any_goals rfl
  all_goals
    rename_i h1 h2
    rw [Fin.ext_iff] at h1 h2
    simp_all only [Fin.natAdd_eq_addNat, Fin.cast_inj, Fin.val_cast, Fin.val_natAdd,
      Fin.val_castAdd, add_right_inj, Fin.val_addNat, add_eq_left]
  · subst h1
    exact Fin.elim0 i
  all_goals
    rename_i h3
    rw [Fin.ext_iff] at h3
    simp_all only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_addNat, not_true_eq_false]
  all_goals
    omega

lemma basis!_on_evenShiftSnd_self (j : Fin n) : basis!AsCharges j (evenShiftSnd j) = - 1 := by
  rw [basis!_evenShftSnd_eq_neg_evenShiftFst, basis!_on_evenShiftFst_self]

lemma basis!_on_evenShiftSnd_other {k j : Fin n} (h : k ≠ j) :
    basis!AsCharges k (evenShiftSnd j) = 0 := by
  rw [basis!_evenShftSnd_eq_neg_evenShiftFst, basis!_on_evenShiftFst_other h]
  rfl

lemma basis!_on_evenShiftZero (j : Fin n) : basis!AsCharges j evenShiftZero = 0 := by
  simp only [basis!AsCharges, succ_eq_add_one, PureU1_numberCharges]
  split<;> rename_i h
  · simp only [evenShiftZero, succ_eq_add_one, Fin.isValue, evenShiftFst, Fin.ext_iff,
    Fin.val_cast, Fin.val_castAdd, Fin.val_eq_zero, Fin.val_natAdd] at h
    omega
  · split <;> rename_i h2
    · simp only [evenShiftZero, succ_eq_add_one, Fin.isValue, evenShiftSnd, Fin.ext_iff,
      Fin.val_cast, Fin.val_castAdd, Fin.val_eq_zero, Fin.val_natAdd] at h2
      omega
    · rfl

lemma basis!_on_evenShiftLast (j : Fin n) : basis!AsCharges j evenShiftLast = 0 := by
  simp only [basis!AsCharges, succ_eq_add_one, PureU1_numberCharges]
  split <;> rename_i h
  · rw [Fin.ext_iff] at h
    simp only [succ_eq_add_one, evenShiftLast, Fin.isValue, Fin.val_cast, Fin.val_natAdd,
      Fin.val_eq_zero, add_zero, evenShiftFst, Fin.val_castAdd, add_right_inj] at h
    omega
  · split <;> rename_i h2
    · rw [Fin.ext_iff] at h2
      simp only [succ_eq_add_one, evenShiftLast, Fin.isValue, Fin.val_cast, Fin.val_natAdd,
        Fin.val_eq_zero, add_zero, evenShiftSnd, Fin.val_castAdd, add_right_inj] at h2
      omega
    · rfl

/-!

### C.3. The vectors satisfy the linear ACCs

-/

lemma basis!_linearACC (j : Fin n) : (accGrav (2 * n.succ)) (basis!AsCharges j) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_evenShift, basis!_on_evenShiftZero, basis!_on_evenShiftLast]
  simp [basis!_evenShftSnd_eq_neg_evenShiftFst]

/-!

### C.4. The vectors satisfy the cubic ACC

-/

lemma basis!_accCube (j : Fin n) :
    accCube (2 * n.succ) (basis!AsCharges j) = 0 := by
  rw [accCube_explicit, sum_evenShift]
  rw [basis!_on_evenShiftLast, basis!_on_evenShiftZero]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Function.comp_apply,
    zero_add]
  apply Finset.sum_eq_zero
  intro i _
  simp only [basis!_evenShftSnd_eq_neg_evenShiftFst]
  ring

/-!

### C.6. The vectors as linear solutions

-/
/-- The second part of the basis as `LinSols`. -/
@[simps!]
def basis! (j : Fin n) : (PureU1 (2 * n.succ)).LinSols :=
  ⟨basis!AsCharges j, by
    intro i
    simp only [succ_eq_add_one, PureU1_numberLinear] at i
    match i with
    | 0 =>
    exact basis!_linearACC j⟩

/-!

### C.7. The inclusion of the second plane into charges

-/

/-- A point in the span of the second part of the basis as a charge. -/
def P! (f : Fin n → ℚ) : (PureU1 (2 * n.succ)).Charges := ∑ i, f i • basis!AsCharges i

/-!

### C.8. Components of the inclusion into charges

-/

lemma P!_evenShiftFst (f : Fin n → ℚ) (j : Fin n) : P! f (evenShiftFst j) = f j := by
  rw [P!, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [basis!_on_evenShiftFst_self]
    exact Rat.mul_one (f j)
  · intro k _ hkj
    rw [basis!_on_evenShiftFst_other hkj]
    exact Rat.mul_zero (f k)
  · simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma P!_evenShiftSnd (f : Fin n → ℚ) (j : Fin n) : P! f (evenShiftSnd j) = - f j := by
  rw [P!, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [basis!_on_evenShiftSnd_self]
    exact mul_neg_one (f j)
  · intro k _ hkj
    rw [basis!_on_evenShiftSnd_other hkj]
    exact Rat.mul_zero (f k)
  · simp

lemma P!_evenShiftZero (f : Fin n → ℚ) : P! f (evenShiftZero) = 0 := by
  rw [P!, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, basis!_on_evenShiftZero]

lemma P!_evenShiftLast (f : Fin n → ℚ) : P! f evenShiftLast = 0 := by
  rw [P!, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, basis!_on_evenShiftLast]

/-!

### C.9. The inclusion into charges satisfies the cubic ACC

-/

lemma P!_accCube (f : Fin n → ℚ) : accCube (2 * n.succ) (P! f) = 0 := by
  rw [accCube_explicit, sum_evenShift, P!_evenShiftZero, P!_evenShiftLast]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Function.comp_apply,
    zero_add]
  apply Finset.sum_eq_zero
  intro i _
  simp only [P!_evenShiftFst, P!_evenShiftSnd]
  ring

/-!

### C.10. Kernel of the inclusion into charges

-/

lemma P!_zero (f : Fin n → ℚ) (h : P! f = 0) : ∀ i, f i = 0 := by
  intro i
  rw [← P!_evenShiftFst f]
  rw [h]
  rfl

/-!

### C.11. The inclusion of the second plane into the span of the basis

-/

lemma P!_in_span (f : Fin n → ℚ) : P! f ∈ Submodule.span ℚ (Set.range basis!AsCharges) := by
  rw [(Submodule.mem_span_range_iff_exists_fun ℚ)]
  use f
  rfl

/-!

### C.12. The inclusion of the plane into linear solutions

-/

/-- A point in the span of the second part of the basis. -/
def P!' (f : Fin n → ℚ) : (PureU1 (2 * n.succ)).LinSols := ∑ i, f i • basis! i

lemma P!'_val (f : Fin n → ℚ) : (P!' f).val = P! f := by
  simp only [succ_eq_add_one, P!', P!]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  rfl

/-!

### C.13. The basis vectors are linearly independent

-/

theorem basis!_linear_independent : LinearIndependent ℚ (@basis! n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change P!' f = 0 at h
  have h1 : (P!' f).val = 0 :=
    (AddSemiconjBy.eq_zero_iff (ACCSystemLinear.LinSols.val 0)
    (congrFun (congrArg HAdd.hAdd (congrArg ACCSystemLinear.LinSols.val (id (Eq.symm h))))
    (ACCSystemLinear.LinSols.val 0))).mp rfl
  rw [P!'_val] at h1
  exact P!_zero f h1

/-!

### C.14. Properties of the basis vectors relating to the span

-/

lemma smul_basis!AsCharges_in_span (S : (PureU1 (2 * n.succ)).LinSols) (j : Fin n) :
    (S.val (evenShiftSnd j) - S.val (evenShiftFst j)) • basis!AsCharges j ∈
    Submodule.span ℚ (Set.range basis!AsCharges) := by
  apply Submodule.smul_mem
  apply SetLike.mem_of_subset
  · exact Submodule.subset_span
  · simp_all only [Set.mem_range, exists_apply_eq_apply]

/-!

### C.15. Permutations as additions of basis vectors

-/

/-- Swapping the elements evenShiftFst j and evenShiftSnd j is equivalent to
  adding a vector basis!AsCharges j. -/
lemma swap!_as_add {S S' : (PureU1 (2 * n.succ)).LinSols} (j : Fin n)
    (hS : ((FamilyPermutations (2 * n.succ)).linSolRep
    (Equiv.swap (evenShiftFst j) (evenShiftSnd j))) S = S') :
    S'.val = S.val + (S.val (evenShiftSnd j) - S.val (evenShiftFst j)) • basis!AsCharges j := by
  funext i
  rw [← hS, FamilyPermutations_anomalyFreeLinear_apply]
  by_cases hi : i = evenShiftFst j
  · subst hi
    simp [HSMul.hSMul, basis!_on_evenShiftFst_self, Equiv.swap_apply_left]
  · by_cases hi2 : i = evenShiftSnd j
    · simp [HSMul.hSMul, hi2, basis!_on_evenShiftSnd_self, Equiv.swap_apply_right]
    · simp only [succ_eq_add_one, Equiv.invFun_as_coe, HSMul.hSMul,
      ACCSystemCharges.chargesAddCommMonoid_add, ACCSystemCharges.chargesModule_smul]
      rw [basis!_on_other hi hi2]
      aesop
/-!

## D. Mixed cubic ACCs involving points from both planes

-/

lemma P_P_P!_accCube (g : Fin n.succ → ℚ) (j : Fin n) :
    accCubeTriLinSymm (P g) (P g) (basis!AsCharges j)
    = g (j.succ) ^ 2 - g (j.castSucc) ^ 2 := by
  simp only [succ_eq_add_one, accCubeTriLinSymm, PureU1Charges_numberCharges,
    TriLinearSymm.mk₃_toFun_apply_apply]
  rw [sum_evenShift, basis!_on_evenShiftZero, basis!_on_evenShiftLast]
  simp only [mul_zero, add_zero, Function.comp_apply, zero_add]
  rw [Finset.sum_eq_single j, basis!_on_evenShiftFst_self, basis!_on_evenShiftSnd_self]
  · simp only [evenShiftFst_eq_evenFst_succ, mul_one, evenShiftSnd_eq_evenSnd_castSucc, mul_neg]
    rw [P_evenFst, P_evenSnd]
    ring
  · intro k _ hkj
    erw [basis!_on_evenShiftFst_other hkj.symm, basis!_on_evenShiftSnd_other hkj.symm]
    simp only [mul_zero, add_zero]
  · simp

lemma P_P!_P!_accCube (g : Fin n → ℚ) (j : Fin n.succ) :
    accCubeTriLinSymm (P! g) (P! g) (basisAsCharges j)
    = (P! g (evenFst j))^2 - (P! g (evenSnd j))^2 := by
  simp only [succ_eq_add_one, accCubeTriLinSymm, PureU1Charges_numberCharges,
    TriLinearSymm.mk₃_toFun_apply_apply]
  rw [sum_even]
  simp only [Function.comp_apply]
  rw [Finset.sum_eq_single j, basis_on_evenFst_self, basis_on_evenSnd_self]
  · simp only [mul_one, mul_neg]
    ring
  · intro k _ hkj
    erw [basis_on_evenFst_other hkj.symm, basis_on_evenSnd_other hkj.symm]
    simp only [mul_zero, add_zero]
  · simp

/-!

## E. The combined basis

-/

/-!

### E.1. As a map into linear solutions

-/
/-- The whole basis as `LinSols`. -/
def basisa : (Fin n.succ) ⊕ (Fin n) → (PureU1 (2 * n.succ)).LinSols := fun i =>
  match i with
  | .inl i => basis i
  | .inr i => basis! i

/-!

### E.2. Inclusion of the span of the basis into charges

-/

/-- A point in the span of the basis as a charge. -/
def Pa (f : Fin n.succ → ℚ) (g : Fin n → ℚ) : (PureU1 (2 * n.succ)).Charges := P f + P! g

/-!

### E.3. Components of the inclusion into charges

-/

lemma Pa_evenShiftFst (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (j : Fin n) :
    Pa f g (evenShiftFst j) = f j.succ + g j := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [P!_evenShiftFst, evenShiftFst_eq_evenFst_succ, P_evenFst]

lemma Pa_evenShiftSnd (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (j : Fin n) :
    Pa f g (evenShiftSnd j) = - f j.castSucc - g j := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [P!_evenShiftSnd, evenShiftSnd_eq_evenSnd_castSucc, P_evenSnd]
  ring

lemma Pa_evenShitZero (f : Fin n.succ → ℚ) (g : Fin n → ℚ) : Pa f g (evenShiftZero) = f 0 := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [P!_evenShiftZero, evenShiftZero_eq_evenFst_zero, P_evenFst]
  exact Rat.add_zero (f 0)

lemma Pa_evenShiftLast (f : Fin n.succ → ℚ) (g : Fin n → ℚ) :
    Pa f g (evenShiftLast) = - f (Fin.last n) := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [P!_evenShiftLast, evenShiftLast_eq_evenSnd_last, P_evenSnd]
  exact Rat.add_zero (-f (Fin.last n))

/-!

### E.4. Kernel of the inclusion into charges

-/

lemma Pa_zero (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (h : Pa f g = 0) :
    ∀ i, f i = 0 := by
  have h₃ := Pa_evenShitZero f g
  rw [h] at h₃
  change 0 = f 0 at h₃
  intro i
  have hinduc (iv : ℕ) (hiv : iv < n.succ) : f ⟨iv, hiv⟩ = 0 := by
    induction iv
    exact h₃.symm
    rename_i iv hi
    have hivi : iv < n.succ := lt_of_succ_lt hiv
    have hi2 := hi hivi
    have h1 := Pa_evenShiftFst f g ⟨iv, succ_lt_succ_iff.mp hiv⟩
    have h2 := Pa_evenShiftSnd f g ⟨iv, succ_lt_succ_iff.mp hiv⟩
    rw [h] at h1 h2
    simp only [Fin.succ_mk, Fin.castSucc_mk] at h1 h2
    erw [hi2] at h2
    change 0 = _ at h2
    simp only [neg_zero, zero_sub, zero_eq_neg] at h2
    rw [h2] at h1
    exact right_eq_add.mp h1
  exact hinduc i.val i.prop

lemma Pa_zero! (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (h : Pa f g = 0) :
    ∀ i, g i = 0 := by
  have hf := Pa_zero f g h
  rw [Pa, P] at h
  simp only [succ_eq_add_one, hf, zero_smul, sum_const_zero, zero_add] at h
  exact P!_zero g h

/-!

### E.5. The inclusion of the span of the basis into linear solutions

-/
/-- A point in the span of the whole basis. -/
def Pa' (f : (Fin n.succ) ⊕ (Fin n) → ℚ) : (PureU1 (2 * n.succ)).LinSols :=
    ∑ i, f i • basisa i

lemma Pa'_P'_P!' (f : (Fin n.succ) ⊕ (Fin n) → ℚ) :
    Pa' f = P' (f ∘ Sum.inl) + P!' (f ∘ Sum.inr) := by
  exact Fintype.sum_sum_type _

/-!

### E.6. The combined basis vectors are linearly independent

-/

theorem basisa_linear_independent : LinearIndependent ℚ (@basisa n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change Pa' f = 0 at h
  have h1 : (Pa' f).val = 0 :=
    (AddSemiconjBy.eq_zero_iff (ACCSystemLinear.LinSols.val 0)
    (congrFun (congrArg HAdd.hAdd (congrArg ACCSystemLinear.LinSols.val (id (Eq.symm h))))
    (ACCSystemLinear.LinSols.val 0))).mp rfl
  rw [Pa'_P'_P!'] at h1
  change (P' (f ∘ Sum.inl)).val + (P!' (f ∘ Sum.inr)).val = 0 at h1
  rw [P!'_val, P'_val] at h1
  change Pa (f ∘ Sum.inl) (f ∘ Sum.inr) = 0 at h1
  have hf := Pa_zero (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  have hg := Pa_zero! (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  intro i
  simp_all
  cases i
  · simp_all
  · simp_all
/-!

### E.7. Injectivity of the inclusion into linear solutions

-/

lemma Pa'_eq (f f' : (Fin n.succ) ⊕ (Fin n) → ℚ) : Pa' f = Pa' f' ↔ f = f' := by
  refine Iff.intro (fun h => (funext (fun i => ?_))) (fun h => ?_)
  · rw [Pa', Pa'] at h
    have h1 : ∑ i : Fin (succ n) ⊕ Fin n, (f i + (- f' i)) • basisa i = 0 := by
      simp only [add_smul, neg_smul]
      rw [Finset.sum_add_distrib]
      rw [h]
      rw [← Finset.sum_add_distrib]
      simp
    have h2 : ∀ i, (f i + (- f' i)) = 0 := by
      exact Fintype.linearIndependent_iff.mp (@basisa_linear_independent n)
        (fun i => f i + -f' i) h1
    have h2i := h2 i
    linarith
  · rw [h]

lemma Pa'_elim_eq_iff (g g' : Fin n.succ → ℚ) (f f' : Fin n → ℚ) :
    Pa' (Sum.elim g f) = Pa' (Sum.elim g' f') ↔ Pa g f = Pa g' f' := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [Pa'_eq, Sum.elim_eq_iff] at h
    rw [h.left, h.right]
  · apply ACCSystemLinear.LinSols.ext
    rw [Pa'_P'_P!', Pa'_P'_P!']
    simp only [succ_eq_add_one, ACCSystemLinear.linSolsAddCommMonoid_add_val, P'_val, P!'_val]
    exact h

lemma Pa_eq (g g' : Fin n.succ → ℚ) (f f' : Fin n → ℚ) :
    Pa g f = Pa g' f' ↔ g = g' ∧ f = f' := by
  rw [← Pa'_elim_eq_iff, ← Sum.elim_eq_iff]
  exact Pa'_eq _ _

/-!

### E.8. Cardinality of the basis

-/

lemma basisa_card : Fintype.card ((Fin n.succ) ⊕ (Fin n)) =
    Module.finrank ℚ (PureU1 (2 * n.succ)).LinSols := by
  erw [BasisLinear.finrank_AnomalyFreeLinear]
  simp only [Fintype.card_sum, Fintype.card_fin, mul_eq]
  exact split_odd n

/-!

### E.9. The basis vectors as a basis

-/

/-- The basis formed out of our `basisa` vectors. -/
noncomputable def basisaAsBasis :
    Basis (Fin (succ n) ⊕ Fin n) ℚ (PureU1 (2 * succ n)).LinSols :=
  basisOfLinearIndependentOfCardEqFinrank (@basisa_linear_independent n) basisa_card

/-!

## F. Every Lienar solution is the sum of a point from each plane

-/

lemma span_basis (S : (PureU1 (2 * n.succ)).LinSols) :
    ∃ (g : Fin n.succ → ℚ) (f : Fin n → ℚ), S.val = P g + P! f := by
  have h := (Submodule.mem_span_range_iff_exists_fun ℚ).mp (Basis.mem_span basisaAsBasis S)
  obtain ⟨f, hf⟩ := h
  simp only [succ_eq_add_one, basisaAsBasis, coe_basisOfLinearIndependentOfCardEqFinrank,
    Fintype.sum_sum_type] at hf
  change P' _ + P!' _ = S at hf
  use f ∘ Sum.inl
  use f ∘ Sum.inr
  rw [← hf]
  simp only [succ_eq_add_one, ACCSystemLinear.linSolsAddCommMonoid_add_val, P'_val, P!'_val]
  rfl

/-!

### F.1. Relation under permutations

-/
lemma span_basis_swap! {S : (PureU1 (2 * n.succ)).LinSols} (j : Fin n)
    (hS : ((FamilyPermutations (2 * n.succ)).linSolRep
    (Equiv.swap (evenShiftFst j) (evenShiftSnd j))) S = S') (g : Fin n.succ → ℚ) (f : Fin n → ℚ)
    (h : S.val = P g + P! f) : ∃ (g' : Fin n.succ → ℚ) (f' : Fin n → ℚ),
      S'.val = P g' + P! f' ∧ P! f' = P! f +
      (S.val (evenShiftSnd j) - S.val (evenShiftFst j)) • basis!AsCharges j ∧ g' = g := by
  let X := P! f + (S.val (evenShiftSnd j) - S.val (evenShiftFst j)) • basis!AsCharges j
  have hX : X ∈ Submodule.span ℚ (Set.range (basis!AsCharges)) := by
    apply Submodule.add_mem
    exact (P!_in_span f)
    exact (smul_basis!AsCharges_in_span S j)
  have hXsum := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hX
  obtain ⟨f', hf'⟩ := hXsum
  use g
  use f'
  change P! f' = _ at hf'
  erw [hf']
  simp only [and_self, and_true, X]
  rw [← add_assoc, ← h]
  apply swap!_as_add at hS
  exact hS

end VectorLikeEvenPlane

end PureU1
