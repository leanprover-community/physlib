/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.QED.AnomalyCancellation.BasisLinear
import PhysLean.QFT.QED.AnomalyCancellation.VectorLike
/-!
# Splitting the linear solutions in the odd case into two ACC-satisfying planes

## i. Overview

We split the linear solutions of `PureU1 (2 * n + 1)` into two planes,
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
  - A.1. The symmetric split: Spltting the charges up via `(n + 1) + 1`
  - A.2. The shifted split: Spltting the charges up via `1 + n + n`
  - A.3. The shifte shifted split: Spltting the charges up via `((1+n)+1) + n.succ`
  - A.4. Relating the splittings together
- B. The first plane
  - B.1. The basis vectors of the first plane as charges
  - B.2. Components of the basis vectors as charges
  - B.3. The basis vectors satisfy the linear ACCs
  - B.4. The basis vectors as `LinSols`
  - B.5. The inclusion of the first plane into charges
  - B.6. Components of the first plane
  - B.7. Points on the first plane satisfies the ACCs
  - B.8. Kernel of the inclusion into charges
  - B.9. The basis vectors are linearly independent
- C. The second plane
  - C.1. The basis vectors of the second plane as charges
  - C.2. Components of the basis vectors as charges
  - C.3. The basis vectors satisfy the linear ACCs
  - C.4. The basis vectors as `LinSols`
  - C.5. Permutations equal adding basis vectors
  - C.6. The inclusion of the second plane into charges
  - C.7. Components of the second plane
  - C.8. Points on the second plane satisfies the ACCs
  - C.9. Kernel of the inclusion into charges
  - C.10. The inclusion of the second plane into LinSols
  - C.11. The basis vectors are linearly independent
- D. The mixed cubic ACC from points in both planes
- E. The combined basis
  - E.1. The combined basis as `LinSols`
  - E.2. The inclusion of the span of the combined basis into charges
  - E.3. Components of the inclusion
  - E.4. Kernel of the inclusion into charges
  - E.5. The inclusion of the span of the combined basis into LinSols
  - E.6. The combined basis vectors are linearly independent
  - E.7. Injectivity of the inclusion into linear solutions
  - E.8. Cardinality of the basis
  - E.9. The basis vectors as a basis
- F. Every Lienar solution is the sum of a point from each plane
  - F.1. Relation under permutations

## iv. References

- https://arxiv.org/pdf/1912.04804.pdf

-/

open Module Nat Finset BigOperators

namespace PureU1

variable {n : ℕ}

namespace VectorLikeOddPlane

/-!

## A. Splitting the charges up into groups

We have `2 * n + 1` charges, which we split up in the following ways:

`| evenFst j (0 to n) | evenSnd j (n.succ to n + n.succ)|`

```
| evenShiftZero (0) | evenShiftFst j (1 to n) |
  evenShiftSnd j (n.succ to 2 * n) | evenShiftLast (2 * n.succ - 1) |
```

-/

section theDeltas

/-!

### A.1. The symmetric split: Spltting the charges up via `(n + 1) + 1`

-/

lemma odd_shift_eq (n : ℕ) : (1 + n) + n = 2 * n +1 := by
  omega

/-- The inclusion of `Fin n` into `Fin ((n + 1) + n)` via the first `n`.
  This is then casted to `Fin (2 * n + 1)`. -/
def oddFst (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (split_odd n) (Fin.castAdd n (Fin.castAdd 1 j))

/-- The inclusion of `Fin n` into `Fin ((n + 1) + n)` via the second `n`.
  This is then casted to `Fin (2 * n + 1)`. -/
def oddSnd (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (split_odd n) (Fin.natAdd (n+1) j)

/-- The element representing `1` in `Fin ((n + 1) + n)`.
  This is then casted to `Fin (2 * n + 1)`. -/
def oddMid : Fin (2 * n + 1) :=
  Fin.cast (split_odd n) (Fin.castAdd n (Fin.natAdd n 1))

lemma sum_odd (S : Fin (2 * n + 1) → ℚ) :
    ∑ i, S i = S oddMid + ∑ i : Fin n, ((S ∘ oddFst) i + (S ∘ oddSnd) i) := by
  have h1 : ∑ i, S i = ∑ i : Fin (n + 1 + n), S (Fin.cast (split_odd n) i) := by
    rw [Finset.sum_equiv (Fin.castOrderIso (split_odd n)).symm.toEquiv]
    · intro i
      simp only [mem_univ, Fin.symm_castOrderIso, RelIso.coe_fn_toEquiv]
    · exact fun _ _ => rfl
  rw [h1]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton, Function.comp_apply]
  nth_rewrite 2 [add_comm]
  rw [add_assoc]
  rw [Finset.sum_add_distrib]
  rfl

/-!

### A.2. The shifted split: Spltting the charges up via `1 + n + n`

-/

/-- The inclusion of `Fin n` into `Fin (1 + n + n)` via the first `n`.
  This is then casted to `Fin (2 * n + 1)`. -/
def oddShiftFst (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (odd_shift_eq n) (Fin.castAdd n (Fin.natAdd 1 j))

/-- The inclusion of `Fin n` into `Fin (1 + n + n)` via the second `n`.
  This is then casted to `Fin (2 * n + 1)`. -/
def oddShiftSnd (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (odd_shift_eq n) (Fin.natAdd (1 + n) j)

/-- The element representing the `1` in `Fin (1 + n + n)`.
  This is then casted to `Fin (2 * n + 1)`. -/
def oddShiftZero : Fin (2 * n + 1) :=
  Fin.cast (odd_shift_eq n) (Fin.castAdd n (Fin.castAdd n 1))

lemma sum_oddShift (S : Fin (2 * n + 1) → ℚ) :
    ∑ i, S i = S oddShiftZero + ∑ i : Fin n, ((S ∘ oddShiftFst) i + (S ∘ oddShiftSnd) i) := by
  have h1 : ∑ i, S i = ∑ i : Fin ((1+n)+n), S (Fin.cast (odd_shift_eq n) i) := by
    rw [Finset.sum_equiv (Fin.castOrderIso (odd_shift_eq n)).symm.toEquiv]
    · intro i
      simp only [mem_univ, Fin.castOrderIso, RelIso.coe_fn_toEquiv]
    · exact fun _ _ => rfl
  rw [h1, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton, Function.comp_apply]
  rw [add_assoc, Finset.sum_add_distrib]
  rfl

/-!

### A.3. The shifte shifted split: Spltting the charges up via `((1+n)+1) + n.succ`

-/

lemma odd_shift_shift_eq (n : ℕ) : ((1+n)+1) + n.succ = 2 * n.succ + 1 := by
  omega

/-- The element representing the first `1` in `Fin (1 + n + 1 + n.succ)` casted
  to `Fin (2 * n.succ + 1)`. -/
def oddShiftShiftZero : Fin (2 * n.succ + 1) :=
  Fin.cast (odd_shift_shift_eq n) (Fin.castAdd n.succ (Fin.castAdd 1 (Fin.castAdd n 1)))

/-- The inclusion of `Fin n` into `Fin (1 + n + 1 + n.succ)` via the first `n` and casted
  to `Fin (2 * n.succ + 1)`. -/
def oddShiftShiftFst (j : Fin n) : Fin (2 * n.succ + 1) :=
  Fin.cast (odd_shift_shift_eq n) (Fin.castAdd n.succ (Fin.castAdd 1 (Fin.natAdd 1 j)))

/-- The element representing the second `1` in `Fin (1 + n + 1 + n.succ)` casted
  to `2 * n.succ + 1`. -/
def oddShiftShiftMid : Fin (2 * n.succ + 1) :=
  Fin.cast (odd_shift_shift_eq n) (Fin.castAdd n.succ (Fin.natAdd (1+n) 1))

/-- The inclusion of `Fin n.succ` into `Fin (1 + n + 1 + n.succ)` via the `n.succ` and casted
  to `Fin (2 * n.succ + 1)`. -/
def oddShiftShiftSnd (j : Fin n.succ) : Fin (2 * n.succ + 1) :=
  Fin.cast (odd_shift_shift_eq n) (Fin.natAdd ((1+n)+1) j)

/-!

### A.4. Relating the splittings together

-/
lemma oddShiftShiftZero_eq_oddFst_zero : @oddShiftShiftZero n = oddFst 0 :=
  Fin.rev_inj.mp rfl

lemma oddShiftShiftZero_eq_oddShiftZero : @oddShiftShiftZero n = oddShiftZero := rfl

lemma oddShiftShiftFst_eq_oddFst_succ (j : Fin n) :
    oddShiftShiftFst j = oddFst j.succ := by
  rw [Fin.ext_iff]
  simp only [succ_eq_add_one, oddShiftShiftFst, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
    oddFst, Fin.val_succ]
  exact Nat.add_comm 1 ↑j

lemma oddShiftShiftFst_eq_oddShiftFst_castSucc (j : Fin n) :
    oddShiftShiftFst j = oddShiftFst j.castSucc := by
  rfl

lemma oddShiftShiftMid_eq_oddMid : @oddShiftShiftMid n = oddMid := by
  rw [Fin.ext_iff]
  simp only [succ_eq_add_one, oddShiftShiftMid, Fin.isValue, Fin.val_cast, Fin.val_castAdd,
    Fin.val_natAdd, Fin.val_eq_zero, add_zero, oddMid]
  exact Nat.add_comm 1 n

lemma oddShiftShiftMid_eq_oddShiftFst_last : oddShiftShiftMid = oddShiftFst (Fin.last n) := by
  rfl

lemma oddShiftShiftSnd_eq_oddSnd (j : Fin n.succ) : oddShiftShiftSnd j = oddSnd j := by
  rw [Fin.ext_iff]
  simp only [succ_eq_add_one, oddShiftShiftSnd, Fin.val_cast, Fin.val_natAdd, oddSnd, add_left_inj]
  exact Nat.add_comm 1 n

lemma oddShiftShiftSnd_eq_oddShiftSnd (j : Fin n.succ) : oddShiftShiftSnd j = oddShiftSnd j := by
  rw [Fin.ext_iff]
  rfl

lemma oddSnd_eq_oddShiftSnd (j : Fin n) : oddSnd j = oddShiftSnd j := by
  rw [Fin.ext_iff]
  simp only [oddSnd, Fin.val_cast, Fin.val_natAdd, oddShiftSnd, add_left_inj]
  exact Nat.add_comm n 1

end theDeltas

/-!

## B. The first plane

-/

/-!

### B.1. The basis vectors of the first plane as charges

-/

/-- The first part of the basis as charge assignments. -/
def basisAsCharges (j : Fin n) : (PureU1 (2 * n + 1)).Charges :=
  fun i =>
  if i = oddFst j then
    1
  else
    if i = oddSnd j then
      - 1
    else
      0

/-!

### B.2. Components of the basis vectors as charges

-/

lemma basis_on_oddFst_self (j : Fin n) : basisAsCharges j (oddFst j) = 1 := by
  simp [basisAsCharges]

lemma basis_on_oddFst_other {k j : Fin n} (h : k ≠ j) :
    basisAsCharges k (oddFst j) = 0 := by
  simp only [basisAsCharges, PureU1_numberCharges]
  simp only [oddFst, oddSnd]
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
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h2
      omega
    · rfl

lemma basis_on_other {k : Fin n} {j : Fin (2 * n + 1)} (h1 : j ≠ oddFst k) (h2 : j ≠ oddSnd k) :
    basisAsCharges k j = 0 := by
  simp only [basisAsCharges, PureU1_numberCharges]
  simp_all only [ne_eq, ↓reduceIte]

lemma basis_oddSnd_eq_minus_oddFst (j i : Fin n) :
    basisAsCharges j (oddSnd i) = - basisAsCharges j (oddFst i) := by
  simp only [basisAsCharges, PureU1_numberCharges, oddSnd, oddFst]
  split <;> split
  any_goals split
  any_goals split
  any_goals rfl
  all_goals
    rename_i h1 h2
    rw [Fin.ext_iff] at h1 h2
    simp_all only [Fin.cast_inj, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, neg_neg,
      add_eq_right, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true]
  all_goals
    rename_i h3
    rw [Fin.ext_iff] at h3
    simp_all only [Fin.val_natAdd, Fin.val_castAdd, add_eq_right,
      AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true]
  all_goals
    omega

lemma basis_on_oddSnd_self (j : Fin n) : basisAsCharges j (oddSnd j) = - 1 := by
  rw [basis_oddSnd_eq_minus_oddFst, basis_on_oddFst_self]

lemma basis_on_oddSnd_other {k j : Fin n} (h : k ≠ j) : basisAsCharges k (oddSnd j) = 0 := by
  rw [basis_oddSnd_eq_minus_oddFst, basis_on_oddFst_other h]
  rfl

lemma basis_on_oddMid (j : Fin n) : basisAsCharges j oddMid = 0 := by
  simp only [basisAsCharges, PureU1_numberCharges]
  split <;> rename_i h
  · rw [Fin.ext_iff] at h
    simp only [oddMid, Fin.isValue, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, Fin.val_eq_zero,
      add_zero, oddFst] at h
    omega
  · split <;> rename_i h2
    · rw [Fin.ext_iff] at h2
      simp only [oddMid, Fin.isValue, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
        Fin.val_eq_zero, add_zero, oddSnd] at h2
      omega
    · rfl

/-!

### B.3. The basis vectors satisfy the linear ACCs

-/

lemma basis_linearACC (j : Fin n) : (accGrav (2 * n + 1)) (basisAsCharges j) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  erw [sum_odd]
  simp [basis_oddSnd_eq_minus_oddFst, basis_on_oddMid]

/-!

### B.4. The basis vectors as `LinSols`

-/

/-- The first part of the basis as `LinSols`. -/
@[simps!]
def basis (j : Fin n) : (PureU1 (2 * n + 1)).LinSols :=
  ⟨basisAsCharges j, by
    intro i
    simp only [PureU1_numberLinear] at i
    match i with
    | 0 =>
    exact basis_linearACC j⟩

/-!

### B.5. The inclusion of the first plane into charges

-/

/-- A point in the span of the first part of the basis as a charge. -/
def P (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).Charges := ∑ i, f i • basisAsCharges i

/-!

### B.6. Components of the first plane

-/

lemma P_oddFst (f : Fin n → ℚ) (j : Fin n) : P f (oddFst j) = f j := by
  rw [P, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [basis_on_oddFst_self]
    exact Rat.mul_one (f j)
  · intro k _ hkj
    rw [basis_on_oddFst_other hkj]
    exact Rat.mul_zero (f k)
  · simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma P_oddSnd (f : Fin n → ℚ) (j : Fin n) : P f (oddSnd j) = - f j := by
  rw [P, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [basis_on_oddSnd_self]
    exact mul_neg_one (f j)
  · intro k _ hkj
    rw [basis_on_oddSnd_other hkj]
    exact Rat.mul_zero (f k)
  · simp

lemma P_oddMid (f : Fin n → ℚ) : P f oddMid = 0 := by
  rw [P, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, basis_on_oddMid]

/-!

### B.7. Points on the first plane satisfies the ACCs

-/

lemma P_linearACC (f : Fin n → ℚ) : (accGrav (2 * n + 1)) (P f) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_odd]
  simp [P_oddSnd, P_oddFst, P_oddMid]

lemma P_accCube (f : Fin n → ℚ) : accCube (2 * n +1) (P f) = 0 := by
  rw [accCube_explicit, sum_odd, P_oddMid]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Function.comp_apply, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  simp only [P_oddFst, P_oddSnd]
  ring

/-!

### B.8. Kernel of the inclusion into charges

-/

lemma P_zero (f : Fin n → ℚ) (h : P f = 0) : ∀ i, f i = 0 := by
  intro i
  erw [← P_oddFst f]
  rw [h]
  rfl

/-- A point in the span of the first part of the basis. -/
def P' (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).LinSols := ∑ i, f i • basis i

lemma P'_val (f : Fin n → ℚ) : (P' f).val = P f := by
  simp only [P', P]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  rfl

/-!

### B.9. The basis vectors are linearly independent

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

## C. The second plane

-/

/-!

### C.1. The basis vectors of the second plane as charges

-/

/-- The second part of the basis as charge assignments. -/
def basis!AsCharges (j : Fin n) : (PureU1 (2 * n + 1)).Charges :=
  fun i =>
  if i = oddShiftFst j then
    1
  else
    if i = oddShiftSnd j then
      - 1
    else
      0

/-!

### C.2. Components of the basis vectors as charges

-/

lemma basis!_on_oddShiftFst_self (j : Fin n) : basis!AsCharges j (oddShiftFst j) = 1 := by
  simp [basis!AsCharges]

lemma basis!_on_oddShiftFst_other {k j : Fin n} (h : k ≠ j) :
    basis!AsCharges k (oddShiftFst j) = 0 := by
  simp only [basis!AsCharges, PureU1_numberCharges]
  simp only [oddShiftFst, oddShiftSnd]
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
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h2
      omega
    rfl

lemma basis!_on_other {k : Fin n} {j : Fin (2 * n + 1)}
    (h1 : j ≠ oddShiftFst k) (h2 : j ≠ oddShiftSnd k) :
    basis!AsCharges k j = 0 := by
  simp only [basis!AsCharges, PureU1_numberCharges]
  simp_all only [ne_eq, ↓reduceIte]

lemma basis!_oddShiftSnd_eq_minus_oddShiftFst (j i : Fin n) :
    basis!AsCharges j (oddShiftSnd i) = - basis!AsCharges j (oddShiftFst i) := by
  simp only [basis!AsCharges, PureU1_numberCharges, oddShiftSnd, oddShiftFst]
  split <;> split
  any_goals split
  any_goals split
  any_goals rfl
  all_goals rename_i h1 h2
  all_goals rw [Fin.ext_iff] at h1 h2
  all_goals simp_all
  · subst h1
    exact Fin.elim0 i
  all_goals rename_i h3
  all_goals rw [Fin.ext_iff] at h3
  all_goals simp_all
  all_goals omega

lemma basis!_on_oddShiftSnd_self (j : Fin n) : basis!AsCharges j (oddShiftSnd j) = - 1 := by
  rw [basis!_oddShiftSnd_eq_minus_oddShiftFst, basis!_on_oddShiftFst_self]

lemma basis!_on_oddShiftSnd_other {k j : Fin n} (h : k ≠ j) :
    basis!AsCharges k (oddShiftSnd j) = 0 := by
  rw [basis!_oddShiftSnd_eq_minus_oddShiftFst, basis!_on_oddShiftFst_other h]
  rfl

lemma basis!_on_oddShiftZero (j : Fin n) : basis!AsCharges j oddShiftZero = 0 := by
  simp only [basis!AsCharges, PureU1_numberCharges]
  split <;> rename_i h
  · rw [Fin.ext_iff] at h
    simp only [oddShiftZero, Fin.isValue, Fin.val_cast, Fin.val_castAdd, Fin.val_eq_zero,
      oddShiftFst, Fin.val_natAdd] at h
    omega
  · split <;> rename_i h2
    · rw [Fin.ext_iff] at h2
      simp only [oddShiftZero, Fin.isValue, Fin.val_cast, Fin.val_castAdd, Fin.val_eq_zero,
        oddShiftSnd, Fin.val_natAdd] at h2
      omega
    · rfl

/-!

### C.3. The basis vectors satisfy the linear ACCs

-/

lemma basis!_linearACC (j : Fin n) : (accGrav (2 * n + 1)) (basis!AsCharges j) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_oddShift, basis!_on_oddShiftZero]
  simp [basis!_oddShiftSnd_eq_minus_oddShiftFst]

/-!

### C.4. The basis vectors as `LinSols`

-/

/-- The second part of the basis as `LinSols`. -/
@[simps!]
def basis! (j : Fin n) : (PureU1 (2 * n + 1)).LinSols :=
  ⟨basis!AsCharges j, by
    intro i
    simp only [PureU1_numberLinear] at i
    match i with
    | 0 =>
    exact basis!_linearACC j⟩

/-!

### C.5. Permutations equal adding basis vectors

-/

/-- Swapping the elements oddShiftFst j and oddShiftSnd j is equivalent to adding a vector
  basis!AsCharges j. -/
lemma swap!_as_add {S S' : (PureU1 (2 * n + 1)).LinSols} (j : Fin n)
    (hS : ((FamilyPermutations (2 * n + 1)).linSolRep
    (Equiv.swap (oddShiftFst j) (oddShiftSnd j))) S = S') :
    S'.val = S.val + (S.val (oddShiftSnd j) - S.val (oddShiftFst j)) • basis!AsCharges j := by
  funext i
  rw [← hS, FamilyPermutations_anomalyFreeLinear_apply]
  by_cases hi : i = oddShiftFst j
  · subst hi
    simp [HSMul.hSMul, basis!_on_oddShiftFst_self, Equiv.swap_apply_left]
  · by_cases hi2 : i = oddShiftSnd j
    · subst hi2
      simp [HSMul.hSMul,basis!_on_oddShiftSnd_self, Equiv.swap_apply_right]
    · simp only [Equiv.invFun_as_coe, HSMul.hSMul, ACCSystemCharges.chargesAddCommMonoid_add,
      ACCSystemCharges.chargesModule_smul]
      rw [basis!_on_other hi hi2]
      aesop

/-!

### C.6. The inclusion of the second plane into charges

-/

/-- A point in the span of the second part of the basis as a charge. -/
def P! (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).Charges := ∑ i, f i • basis!AsCharges i

/-!

### C.7. Components of the second plane

-/

lemma P!_oddShiftFst (f : Fin n → ℚ) (j : Fin n) : P! f (oddShiftFst j) = f j := by
  rw [P!, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [basis!_on_oddShiftFst_self]
    exact Rat.mul_one (f j)
  · intro k _ hkj
    rw [basis!_on_oddShiftFst_other hkj]
    exact Rat.mul_zero (f k)
  · simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma P!_oddShiftSnd (f : Fin n → ℚ) (j : Fin n) : P! f (oddShiftSnd j) = - f j := by
  rw [P!, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [basis!_on_oddShiftSnd_self]
    exact mul_neg_one (f j)
  · intro k _ hkj
    rw [basis!_on_oddShiftSnd_other hkj]
    exact Rat.mul_zero (f k)
  · simp

lemma P!_oddShiftZero (f : Fin n → ℚ) : P! f oddShiftZero = 0 := by
  rw [P!, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, basis!_on_oddShiftZero]

/-!

### C.8. Points on the second plane satisfies the ACCs

-/

lemma P!_linearACC (f : Fin n → ℚ) : (accGrav (2 * n + 1)) (P! f) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_oddShift]
  simp [P!_oddShiftSnd, P!_oddShiftFst, P!_oddShiftZero]

lemma P!_accCube (f : Fin n → ℚ) : accCube (2 * n +1) (P! f) = 0 := by
  rw [accCube_explicit, sum_oddShift, P!_oddShiftZero]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Function.comp_apply, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  simp only [P!_oddShiftFst, P!_oddShiftSnd]
  ring

/-!

### C.9. Kernel of the inclusion into charges

-/

lemma P!_zero (f : Fin n → ℚ) (h : P! f = 0) : ∀ i, f i = 0 := by
  intro i
  rw [← P!_oddShiftFst f]
  rw [h]
  rfl

/-!

### C.10. The inclusion of the second plane into LinSols

-/

/-- A point in the span of the second part of the basis. -/
def P!' (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).LinSols := ∑ i, f i • basis! i

lemma P!'_val (f : Fin n → ℚ) : (P!' f).val = P! f := by
  simp only [P!', P!]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  rfl

/-!

### C.11. The basis vectors are linearly independent

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

## D. The mixed cubic ACC from points in both planes

-/

lemma P_P_P!_accCube (g : Fin n → ℚ) (j : Fin n) :
    accCubeTriLinSymm (P g) (P g) (basis!AsCharges j)
    = (P g (oddShiftFst j))^2 - (g j)^2 := by
  simp only [accCubeTriLinSymm, PureU1Charges_numberCharges, TriLinearSymm.mk₃_toFun_apply_apply]
  rw [sum_oddShift, basis!_on_oddShiftZero]
  simp only [mul_zero, Function.comp_apply, zero_add]
  rw [Finset.sum_eq_single j, basis!_on_oddShiftFst_self, basis!_on_oddShiftSnd_self]
  · rw [← oddSnd_eq_oddShiftSnd, P_oddSnd]
    ring
  · intro k _ hkj
    erw [basis!_on_oddShiftFst_other hkj.symm, basis!_on_oddShiftSnd_other hkj.symm]
    simp only [mul_zero, add_zero]
  · simp

/-!

## E. The combined basis

-/

/-!

### E.1. The combined basis as `LinSols`

-/

/-- The whole basis as `LinSols`. -/
def basisa : Fin n ⊕ Fin n → (PureU1 (2 * n + 1)).LinSols := fun i =>
  match i with
  | .inl i => basis i
  | .inr i => basis! i

/-!

### E.2. The inclusion of the span of the combined basis into charges

-/

/-- A point in the span of the basis as a charge. -/
def Pa (f : Fin n → ℚ) (g : Fin n → ℚ) : (PureU1 (2 * n + 1)).Charges := P f + P! g

/-!

### E.3. Components of the inclusion

-/

lemma Pa_oddShiftShiftZero (f g : Fin n.succ → ℚ) : Pa f g oddShiftShiftZero = f 0 := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [oddShiftShiftZero_eq_oddFst_zero]
  rw [oddShiftShiftZero_eq_oddShiftZero]
  rw [P_oddFst, P!_oddShiftZero]
  exact Rat.add_zero (f 0)

lemma Pa_oddShiftShiftFst (f g : Fin n.succ → ℚ) (j : Fin n) :
    Pa f g (oddShiftShiftFst j) = f j.succ + g j.castSucc := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [oddShiftShiftFst_eq_oddFst_succ]
  rw [oddShiftShiftFst_eq_oddShiftFst_castSucc]
  rw [P_oddFst, P!_oddShiftFst]

lemma Pa_oddShiftShiftMid (f g : Fin n.succ → ℚ) : Pa f g oddShiftShiftMid = g (Fin.last n) := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [oddShiftShiftMid_eq_oddMid]
  rw [oddShiftShiftMid_eq_oddShiftFst_last]
  rw [P_oddMid, P!_oddShiftFst]
  exact Rat.zero_add (g (Fin.last n))

lemma Pa_oddShiftShiftSnd (f g : Fin n.succ → ℚ) (j : Fin n.succ) :
    Pa f g (oddShiftShiftSnd j) = - f j - g j := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [oddShiftShiftSnd_eq_oddSnd]
  rw [oddShiftShiftSnd_eq_oddShiftSnd]
  rw [P_oddSnd, P!_oddShiftSnd]
  ring

/-!

### E.4. Kernel of the inclusion into charges

-/

lemma Pa_zero (f g : Fin n.succ → ℚ) (h : Pa f g = 0) :
    ∀ i, f i = 0 := by
  have h₃ := Pa_oddShiftShiftZero f g
  rw [h] at h₃
  change 0 = _ at h₃
  intro i
  have hinduc (iv : ℕ) (hiv : iv < n.succ) : f ⟨iv, hiv⟩ = 0 := by
    induction iv
    exact h₃.symm
    rename_i iv hi
    have hivi : iv < n.succ := lt_of_succ_lt hiv
    have hi2 := hi hivi
    have h1 := Pa_oddShiftShiftSnd f g ⟨iv, hivi⟩
    rw [h, hi2] at h1
    change 0 = _ at h1
    simp only [neg_zero, succ_eq_add_one, zero_sub, zero_eq_neg] at h1
    have h2 := Pa_oddShiftShiftFst f g ⟨iv, succ_lt_succ_iff.mp hiv⟩
    simp only [succ_eq_add_one, h, Fin.succ_mk, Fin.castSucc_mk, h1, add_zero] at h2
    exact h2.symm
  exact hinduc i.val i.prop

lemma Pa_zero! (f g : Fin n.succ → ℚ) (h : Pa f g = 0) :
    ∀ i, g i = 0 := by
  have hf := Pa_zero f g h
  rw [Pa, P] at h
  simp only [succ_eq_add_one, hf, zero_smul, sum_const_zero, zero_add] at h
  exact P!_zero g h

/-!

### E.5. The inclusion of the span of the combined basis into LinSols

-/

/-- A point in the span of the whole basis. -/
def Pa' (f : (Fin n) ⊕ (Fin n) → ℚ) : (PureU1 (2 * n + 1)).LinSols :=
    ∑ i, f i • basisa i

lemma Pa'_P'_P!' (f : (Fin n) ⊕ (Fin n) → ℚ) :
    Pa' f = P' (f ∘ Sum.inl) + P!' (f ∘ Sum.inr) := by
  exact Fintype.sum_sum_type _

/-!

### E.6. The combined basis vectors are linearly independent

-/

theorem basisa_linear_independent : LinearIndependent ℚ (@basisa n.succ) := by
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
  simp_all only [succ_eq_add_one, Function.comp_apply]
  cases i
  · simp_all
  · simp_all

/-!

### E.7. Injectivity of the inclusion into linear solutions

-/

lemma Pa'_eq (f f' : (Fin n.succ) ⊕ (Fin n.succ) → ℚ) : Pa' f = Pa' f' ↔ f = f' := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · funext i
    rw [Pa', Pa'] at h
    have h1 : ∑ i : Fin n.succ ⊕ Fin n.succ, (f i + (- f' i)) • basisa i = 0 := by
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

lemma Pa'_elim_eq_iff (g g' : Fin n.succ → ℚ) (f f' : Fin n.succ → ℚ) :
    Pa' (Sum.elim g f) = Pa' (Sum.elim g' f') ↔ Pa g f = Pa g' f' := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [Pa'_eq, Sum.elim_eq_iff] at h
    rw [h.left, h.right]
  · apply ACCSystemLinear.LinSols.ext
    rw [Pa'_P'_P!', Pa'_P'_P!']
    simp only [succ_eq_add_one, ACCSystemLinear.linSolsAddCommMonoid_add_val, P'_val, P!'_val]
    exact h

lemma Pa_eq (g g' : Fin n.succ → ℚ) (f f' : Fin n.succ → ℚ) :
    Pa g f = Pa g' f' ↔ g = g' ∧ f = f' := by
  rw [← Pa'_elim_eq_iff]
  rw [← Sum.elim_eq_iff]
  exact Pa'_eq _ _

/-!

### E.8. Cardinality of the basis

-/

lemma basisa_card : Fintype.card ((Fin n.succ) ⊕ (Fin n.succ)) =
    Module.finrank ℚ (PureU1 (2 * n.succ + 1)).LinSols := by
  erw [BasisLinear.finrank_AnomalyFreeLinear]
  simp only [Fintype.card_sum, Fintype.card_fin]
  exact Eq.symm (Nat.two_mul n.succ)

/-!

### E.9. The basis vectors as a basis

-/

/-- The basis formed out of our basisa vectors. -/
noncomputable def basisaAsBasis :
    Basis (Fin n.succ ⊕ Fin n.succ) ℚ (PureU1 (2 * n.succ + 1)).LinSols :=
  basisOfLinearIndependentOfCardEqFinrank (@basisa_linear_independent n) basisa_card

/-!

## F. Every Lienar solution is the sum of a point from each plane

-/

lemma span_basis (S : (PureU1 (2 * n.succ + 1)).LinSols) :
    ∃ (g f : Fin n.succ → ℚ), S.val = P g + P! f := by
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

lemma span_basis_swap! {S : (PureU1 (2 * n.succ + 1)).LinSols} (j : Fin n.succ)
    (hS : ((FamilyPermutations (2 * n.succ + 1)).linSolRep
    (Equiv.swap (oddShiftFst j) (oddShiftSnd j))) S = S') (g f : Fin n.succ → ℚ)
    (hS1 : S.val = P g + P! f) : ∃ (g' f' : Fin n.succ → ℚ),
    S'.val = P g' + P! f' ∧ P! f' = P! f +
    (S.val (oddShiftSnd j) - S.val (oddShiftFst j)) • basis!AsCharges j ∧ g' = g := by
  let X := P! f + (S.val (oddShiftSnd j) - S.val (oddShiftFst j)) • basis!AsCharges j
  have hf : P! f ∈ Submodule.span ℚ (Set.range basis!AsCharges) := by
    rw [(Submodule.mem_span_range_iff_exists_fun ℚ)]
    use f
    rfl
  have hP : (S.val (oddShiftSnd j) - S.val (oddShiftFst j)) • basis!AsCharges j ∈
      Submodule.span ℚ (Set.range basis!AsCharges) := by
    apply Submodule.smul_mem
    apply SetLike.mem_of_subset
    apply Submodule.subset_span
    simp_all only [Set.mem_range, exists_apply_eq_apply]
  have hX : X ∈ Submodule.span ℚ (Set.range (basis!AsCharges)) := by
    apply Submodule.add_mem
    exact hf
    exact hP
  have hXsum := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hX
  obtain ⟨f', hf'⟩ := hXsum
  use g
  use f'
  change P! f' = _ at hf'
  erw [hf']
  simp only [and_self, and_true, X]
  rw [← add_assoc, ← hS1]
  apply swap!_as_add at hS
  exact hS

end VectorLikeOddPlane

end PureU1
