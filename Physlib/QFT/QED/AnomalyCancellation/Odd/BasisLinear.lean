/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.BasisLinear
public import Physlib.QFT.QED.AnomalyCancellation.VectorLike
/-!
# Splitting the linear solutions in the odd case into two ACC-satisfying planes

## i. Overview

We split the linear solutions of `PureU1 (2 * n + 1)` into two planes,
where every point in either plane satisfies both the linear and cubic anomaly cancellation
conditions.

## ii. Key results

- `Unshifted.planeLinSols` : The inclusion of the unshifted plane into linear solutions
- `Unshifted.planeCharges_accCube` : The statement that charges from the unshifted plane
  satisfy the cubic ACC
- `Shifted.planeLinSols` : The inclusion of the shifted plane.
- `Shifted.planeCharges_accCube` : The statement that charges from the shifted plane
  satisfy the cubic ACC
- `span_basis` : Every linear solution is the sum of a point from each plane.

## iii. Table of contents

- A. Splitting the charges up into groups
  - A.1. The symmetric split: Spltting the charges up via `(n + 1) + 1`
  - A.2. The shifted split: Spltting the charges up via `1 + n + n`
  - A.3. The shifte shifted split: Spltting the charges up via `((1+n)+1) + n.succ`
  - A.4. Relating the splittings together
- B. The unshifted plane
  - B.1. The basis vectors of the unshifted plane as charges
  - B.2. Components of the basis vectors as charges
  - B.3. The basis vectors satisfy the linear ACCs
  - B.4. The basis vectors as `LinSols`
  - B.5. The inclusion of the unshifted plane into charges
  - B.6. Components of the unshifted plane
  - B.7. Points on the unshifted plane satisfies the ACCs
  - B.8. Kernel of the inclusion into charges
  - B.9. The basis vectors are linearly independent
- C. The shifted plane
  - C.1. The basis vectors of the shifted plane as charges
  - C.2. Components of the basis vectors as charges
  - C.3. The basis vectors satisfy the linear ACCs
  - C.4. The basis vectors as `LinSols`
  - C.5. Permutations equal adding basis vectors
  - C.6. The inclusion of the shifted plane into charges
  - C.7. Components of the shifted plane
  - C.8. Points on the shifted plane satisfies the ACCs
  - C.9. Kernel of the inclusion into charges
  - C.10. The inclusion of the shifted plane into LinSols
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

* https://arxiv.org/pdf/1912.04804.pdf. [ref: arxiv_1912_04804]
-/

@[expose] public section

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
  have h1 : ∑ i, S i = ∑ i : Fin (n + 1 + n), S (Fin.cast (split_odd n) i) :=
    (Equiv.sum_comp (finCongr (split_odd n)) S).symm
  rw [h1, Fin.sum_univ_add, Fin.sum_univ_add]
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
  have h1 : ∑ i, S i = ∑ i : Fin ((1+n)+n), S (Fin.cast (odd_shift_eq n) i) :=
    (Equiv.sum_comp (finCongr (odd_shift_eq n)) S).symm
  rw [h1, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton, Function.comp_apply]
  rw [add_assoc, Finset.sum_add_distrib]
  rfl

/-!

### A.3. The shifted shifted split: Spltting the charges up via `((1+n)+1) + n.succ`

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
  simp only [Fin.ext_iff, succ_eq_add_one, oddShiftShiftFst, Fin.val_cast, Fin.val_castAdd,
    Fin.val_natAdd, oddFst, Fin.val_succ]
  omega

lemma oddShiftShiftFst_eq_oddShiftFst_castSucc (j : Fin n) :
    oddShiftShiftFst j = oddShiftFst j.castSucc := by
  rfl

lemma oddShiftShiftMid_eq_oddMid : @oddShiftShiftMid n = oddMid := by
  simp only [Fin.ext_iff, succ_eq_add_one, oddShiftShiftMid, Fin.isValue, Fin.val_cast,
    Fin.val_castAdd, Fin.val_natAdd, Fin.val_eq_zero, add_zero, oddMid]
  omega

lemma oddShiftShiftMid_eq_oddShiftFst_last : oddShiftShiftMid = oddShiftFst (Fin.last n) := by
  rfl

lemma oddShiftShiftSnd_eq_oddSnd (j : Fin n.succ) : oddShiftShiftSnd j = oddSnd j := by
  simp only [Fin.ext_iff, succ_eq_add_one, oddShiftShiftSnd, Fin.val_cast, Fin.val_natAdd, oddSnd,
    add_left_inj]
  omega

lemma oddShiftShiftSnd_eq_oddShiftSnd (j : Fin n.succ) : oddShiftShiftSnd j = oddShiftSnd j := by
  rw [Fin.ext_iff]
  rfl

lemma oddSnd_eq_oddShiftSnd (j : Fin n) : oddSnd j = oddShiftSnd j := by
  simp only [Fin.ext_iff, oddSnd, Fin.val_cast, Fin.val_natAdd, oddShiftSnd, add_left_inj]
  omega

lemma oddShiftZero_eq_oddFst : oddShiftZero = oddFst (0 : Fin n.succ) := by
  simp [Fin.ext_iff, oddShiftZero, oddFst]

lemma oddShiftFst_castSucc_eq_oddFst_succ (j : Fin n) :
    oddShiftFst j.castSucc = oddFst j.succ := by
  simp only [Fin.ext_iff, oddShiftFst, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, oddFst,
    Fin.val_succ, Fin.val_castSucc]
  omega

lemma oddShiftFst_last_eq_oddMid : oddShiftFst (Fin.last n) = oddMid := by
  simp only [Fin.ext_iff, oddShiftFst, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, oddMid,
    Fin.val_last]
  omega

lemma oddShiftSnd_eq_oddSnd (j : Fin n) : oddShiftSnd j = oddSnd j := by
  simp only [Fin.ext_iff, oddShiftSnd, Fin.val_cast, Fin.val_natAdd, oddSnd, add_left_inj]
  omega

end theDeltas

/-!

## B. The unshifted plane

-/

namespace Unshifted

/-!

### B.1. The basis vectors of the unshifted plane as charges

-/

set_option backward.isDefEq.respectTransparency false in
/-- The unshifted part of the basis as charge assignments. -/
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

set_option backward.isDefEq.respectTransparency false in
lemma basis_on_oddFst_self (j : Fin n) : basisAsCharges j (oddFst j) = 1 := by
  simp [basisAsCharges]

set_option backward.isDefEq.respectTransparency false in
lemma basis_on_oddFst_other {k j : Fin n} (h : k ≠ j) :
    basisAsCharges k (oddFst j) = 0 := by
  have hk : (k : ℕ) ≠ (j : ℕ) := fun he => h (Fin.ext he)
  simp only [basisAsCharges, oddFst, oddSnd, Fin.ext_iff, Fin.val_cast, Fin.val_castAdd,
    Fin.val_natAdd]
  split
  · omega
  · split
    · omega
    · rfl

set_option backward.isDefEq.respectTransparency false in
lemma basis_on_other {k : Fin n} {j : Fin (2 * n + 1)} (h1 : j ≠ oddFst k) (h2 : j ≠ oddSnd k) :
    basisAsCharges k j = 0 := by
  simp only [basisAsCharges, h1, h2, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
lemma basis_oddSnd_eq_minus_oddFst (j i : Fin n) :
    basisAsCharges j (oddSnd i) = - basisAsCharges j (oddFst i) := by
  simp only [basisAsCharges, oddSnd, oddFst, Fin.ext_iff, Fin.val_cast, Fin.val_castAdd,
    Fin.val_natAdd]
  split_ifs <;> first | omega | simp

lemma basis_on_oddSnd_self (j : Fin n) : basisAsCharges j (oddSnd j) = - 1 := by
  rw [basis_oddSnd_eq_minus_oddFst, basis_on_oddFst_self]

lemma basis_on_oddSnd_other {k j : Fin n} (h : k ≠ j) : basisAsCharges k (oddSnd j) = 0 := by
  rw [basis_oddSnd_eq_minus_oddFst, basis_on_oddFst_other h]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma basis_on_oddMid (j : Fin n) : basisAsCharges j oddMid = 0 := by
  simp only [basisAsCharges, oddMid, oddFst, oddSnd, Fin.isValue, Fin.val_cast, Fin.val_castAdd,
    Fin.val_natAdd, Fin.val_eq_zero, add_zero, Fin.ext_iff]
  split
  · omega
  · split
    · omega
    · rfl

/-!

### B.3. The basis vectors satisfy the linear ACCs

-/

set_option backward.isDefEq.respectTransparency false in
lemma basis_linearACC (j : Fin n) : (accGrav (2 * n + 1)) (basisAsCharges j) = 0 := by
  rw [accGrav]
  simp [sum_odd, basis_oddSnd_eq_minus_oddFst, basis_on_oddMid]

/-!

### B.4. The basis vectors as `LinSols`

-/

/-- The unshifted part of the basis as `LinSols`. -/
@[simps!]
def basis (j : Fin n) : (PureU1 (2 * n + 1)).LinSols :=
  ⟨basisAsCharges j, by
    intro i
    match i with
    | ⟨0, _⟩ => exact basis_linearACC j⟩

/-!

### B.5. The inclusion of the unshifted plane into charges

-/

/-- A point in the span of the unshifted part of the basis as a charge. -/
def planeCharges (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).Charges := ∑ i, f i • basisAsCharges i

/-!

### B.6. Components of the unshifted plane

-/

lemma planeCharges_oddFst (f : Fin n → ℚ) (j : Fin n) : planeCharges f (oddFst j) = f j := by
  rw [planeCharges, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Fintype.sum_eq_single j]
  · simp [basis_on_oddFst_self]
  · intro k hkj
    exact mul_eq_zero_of_right (f k) (basis_on_oddFst_other hkj)

lemma planeCharges_oddSnd (f : Fin n → ℚ) (j : Fin n) : planeCharges f (oddSnd j) = - f j := by
  rw [planeCharges, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Fintype.sum_eq_single j]
  · simp [basis_on_oddSnd_self]
  · intro k hkj
    exact mul_eq_zero_of_right (f k) (basis_on_oddSnd_other hkj)

lemma planeCharges_oddMid (f : Fin n → ℚ) : planeCharges f oddMid = 0 := by
  rw [planeCharges, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, basis_on_oddMid]

/-!

### B.7. Points on the unshifted plane satisfies the ACCs

-/

set_option backward.isDefEq.respectTransparency false in
lemma planeCharges_linearACC (f : Fin n → ℚ) : (accGrav (2 * n + 1)) (planeCharges f) = 0 := by
  rw [accGrav]
  simp [sum_odd, planeCharges_oddSnd, planeCharges_oddFst, planeCharges_oddMid]

set_option backward.isDefEq.respectTransparency false in
lemma planeCharges_accCube (f : Fin n → ℚ) : accCube (2 * n +1) (planeCharges f) = 0 := by
  rw [accCube_explicit, sum_odd, planeCharges_oddMid]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Function.comp_apply, zero_add]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [planeCharges_oddFst, planeCharges_oddSnd]
  ring

/-!

### B.8. Kernel of the inclusion into charges

-/

lemma planeCharges_zero (f : Fin n → ℚ) (h : planeCharges f = 0) : ∀ i, f i = 0 :=
  fun i => (planeCharges_oddFst f i).symm.trans (congr_fun h (oddFst i))

/-- A point in the span of the unshifted part of the basis. -/
def planeLinSols (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).LinSols := ∑ i, f i • basis i

set_option backward.isDefEq.respectTransparency false in
lemma planeLinSols_val (f : Fin n → ℚ) : (planeLinSols f).val = planeCharges f := by
  simp only [planeLinSols, planeCharges]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  rfl

/-!

### B.9. The basis vectors are linearly independent

-/

lemma basis_linear_independent : LinearIndependent ℚ (@basis n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change planeLinSols f = 0 at h
  exact planeCharges_zero f (planeLinSols_val f ▸ congrArg ACCSystemLinear.LinSols.val h)

end Unshifted

/-!

## C. The shifted plane

-/

namespace Shifted

/-!

### C.1. The basis vectors of the shifted plane as charges

-/

set_option backward.isDefEq.respectTransparency false in
/-- The shifted part of the basis as charge assignments. -/
def basisAsCharges (j : Fin n) : (PureU1 (2 * n + 1)).Charges :=
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

set_option backward.isDefEq.respectTransparency false in
lemma basis_on_oddShiftFst_self (j : Fin n) : basisAsCharges j (oddShiftFst j) = 1 := by
  simp [basisAsCharges]

set_option backward.isDefEq.respectTransparency false in
lemma basis_on_oddShiftFst_other {k j : Fin n} (h : k ≠ j) :
    basisAsCharges k (oddShiftFst j) = 0 := by
  have hk : (k : ℕ) ≠ (j : ℕ) := fun he => h (Fin.ext he)
  simp only [basisAsCharges, oddShiftFst, oddShiftSnd, Fin.ext_iff, Fin.val_cast, Fin.val_castAdd,
    Fin.val_natAdd]
  split
  · omega
  · split
    · omega
    · rfl

set_option backward.isDefEq.respectTransparency false in
lemma basis_on_other {k : Fin n} {j : Fin (2 * n + 1)}
    (h1 : j ≠ oddShiftFst k) (h2 : j ≠ oddShiftSnd k) :
    basisAsCharges k j = 0 := by
  simp only [basisAsCharges, h1, h2, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
lemma basis_oddShiftSnd_eq_minus_oddShiftFst (j i : Fin n) :
    basisAsCharges j (oddShiftSnd i) = - basisAsCharges j (oddShiftFst i) := by
  simp only [basisAsCharges, oddShiftSnd, oddShiftFst, Fin.ext_iff, Fin.val_cast, Fin.val_castAdd,
    Fin.val_natAdd]
  split_ifs <;> first | omega | simp

lemma basis_on_oddShiftSnd_self (j : Fin n) : basisAsCharges j (oddShiftSnd j) = - 1 := by
  rw [basis_oddShiftSnd_eq_minus_oddShiftFst, basis_on_oddShiftFst_self]

lemma basis_on_oddShiftSnd_other {k j : Fin n} (h : k ≠ j) :
    basisAsCharges k (oddShiftSnd j) = 0 := by
  rw [basis_oddShiftSnd_eq_minus_oddShiftFst, basis_on_oddShiftFst_other h]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma basis_on_oddShiftZero (j : Fin n) : basisAsCharges j oddShiftZero = 0 := by
  simp only [basisAsCharges, oddShiftZero, oddShiftFst, oddShiftSnd, Fin.isValue, Fin.val_cast,
    Fin.val_castAdd, Fin.val_eq_zero, Fin.val_natAdd, Fin.ext_iff]
  split
  · omega
  · split
    · omega
    · rfl

/-!

### C.3. The basis vectors satisfy the linear ACCs

-/

set_option backward.isDefEq.respectTransparency false in
lemma basis_linearACC (j : Fin n) : (accGrav (2 * n + 1)) (basisAsCharges j) = 0 := by
  rw [accGrav]
  simp [sum_oddShift, basis_on_oddShiftZero, basis_oddShiftSnd_eq_minus_oddShiftFst]

/-!

### C.4. The basis vectors as `LinSols`

-/

/-- The shifted part of the basis as `LinSols`. -/
@[simps!]
def basis (j : Fin n) : (PureU1 (2 * n + 1)).LinSols :=
  ⟨basisAsCharges j, by
    intro i
    match i with
    | ⟨0, _⟩ => exact basis_linearACC j⟩

/-!

### C.5. Permutations equal adding basis vectors

-/

set_option backward.isDefEq.respectTransparency false in
/-- Swapping the elements oddShiftFst j and oddShiftSnd j is equivalent to adding a vector
  basisAsCharges j. -/
lemma swap_as_add {S S' : (PureU1 (2 * n + 1)).LinSols} (j : Fin n)
    (hS : ((FamilyPermutations (2 * n + 1)).linSolRep
    (Equiv.swap (oddShiftFst j) (oddShiftSnd j))) S = S') :
    S'.val = S.val + (S.val (oddShiftSnd j) - S.val (oddShiftFst j)) • basisAsCharges j := by
  funext i
  rw [← hS, FamilyPermutations_anomalyFreeLinear_apply]
  by_cases hi : i = oddShiftFst j
  · subst hi
    simp [HSMul.hSMul, basis_on_oddShiftFst_self, Equiv.swap_apply_left]
  · by_cases hi2 : i = oddShiftSnd j
    · subst hi2
      simp [HSMul.hSMul,basis_on_oddShiftSnd_self, Equiv.swap_apply_right]
    · simp only [Equiv.invFun_as_coe, HSMul.hSMul, ACCSystemCharges.chargesAddCommMonoid_add,
      ACCSystemCharges.chargesModule_smul]
      rw [basis_on_other hi hi2]
      aesop

/-!

### C.6. The inclusion of the shifted plane into charges

-/

/-- A point in the span of the shifted part of the basis as a charge. -/
def planeCharges (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).Charges := ∑ i, f i • basisAsCharges i

/-!

### C.7. Components of the shifted plane

-/

lemma planeCharges_oddShiftFst (f : Fin n → ℚ) (j : Fin n) :
    planeCharges f (oddShiftFst j) = f j := by
  rw [planeCharges, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Fintype.sum_eq_single j]
  · simp [basis_on_oddShiftFst_self]
  · intro k hkj
    exact mul_eq_zero_of_right (f k) (basis_on_oddShiftFst_other hkj)

lemma planeCharges_oddShiftSnd (f : Fin n → ℚ) (j : Fin n) :
    planeCharges f (oddShiftSnd j) = - f j := by
  rw [planeCharges, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Fintype.sum_eq_single j]
  · simp [basis_on_oddShiftSnd_self]
  · intro k hkj
    exact mul_eq_zero_of_right (f k) (basis_on_oddShiftSnd_other hkj)

lemma planeCharges_oddShiftZero (f : Fin n → ℚ) : planeCharges f oddShiftZero = 0 := by
  rw [planeCharges, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, basis_on_oddShiftZero]

/-!

### C.8. Points on the shifted plane satisfies the ACCs

-/

set_option backward.isDefEq.respectTransparency false in
lemma planeCharges_linearACC (f : Fin n → ℚ) : (accGrav (2 * n + 1)) (planeCharges f) = 0 := by
  rw [accGrav]
  simp [sum_oddShift, planeCharges_oddShiftSnd, planeCharges_oddShiftFst, planeCharges_oddShiftZero]

set_option backward.isDefEq.respectTransparency false in
lemma planeCharges_accCube (f : Fin n → ℚ) : accCube (2 * n +1) (planeCharges f) = 0 := by
  rw [accCube_explicit, sum_oddShift, planeCharges_oddShiftZero]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Function.comp_apply, zero_add]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [planeCharges_oddShiftFst, planeCharges_oddShiftSnd]
  ring

/-!

### C.9. Kernel of the inclusion into charges

-/

lemma planeCharges_zero (f : Fin n → ℚ) (h : planeCharges f = 0) : ∀ i, f i = 0 :=
  fun i => (planeCharges_oddShiftFst f i).symm.trans (congr_fun h (oddShiftFst i))

/-!

### C.10. The inclusion of the shifted plane into LinSols

-/

/-- A point in the span of the shifted part of the basis. -/
def planeLinSols (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).LinSols := ∑ i, f i • basis i

set_option backward.isDefEq.respectTransparency false in
lemma planeLinSols_val (f : Fin n → ℚ) : (planeLinSols f).val = planeCharges f := by
  simp only [planeLinSols, planeCharges]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  rfl

/-!

### C.11. The basis vectors are linearly independent

-/

lemma basis_linear_independent : LinearIndependent ℚ (@basis n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change planeLinSols f = 0 at h
  exact planeCharges_zero f (planeLinSols_val f ▸ congrArg ACCSystemLinear.LinSols.val h)

end Shifted

/-!

## D. The mixed cubic ACC from points in both planes

-/

set_option backward.isDefEq.respectTransparency false in
lemma P_P_P!_accCube (g : Fin n → ℚ) (j : Fin n) :
    accCubeTriLinSymm (Unshifted.planeCharges g) (Unshifted.planeCharges g)
      (Shifted.basisAsCharges j)
    = (Unshifted.planeCharges g (oddShiftFst j))^2 - (g j)^2 := by
  simp only [accCubeTriLinSymm, TriLinearSymm.mk₃_toFun_apply_apply]
  erw [sum_oddShift, Shifted.basis_on_oddShiftZero]
  simp only [mul_zero, Function.comp_apply, zero_add]
  rw [Fintype.sum_eq_single j, Shifted.basis_on_oddShiftFst_self, Shifted.basis_on_oddShiftSnd_self]
  · rw [← oddSnd_eq_oddShiftSnd, Unshifted.planeCharges_oddSnd]
    ring
  · intro k hkj
    erw [Shifted.basis_on_oddShiftFst_other hkj.symm, Shifted.basis_on_oddShiftSnd_other hkj.symm]
    simp only [mul_zero, add_zero]

/-!

## E. The combined Unshifted.basis

-/

/-!

### E.1. The combined Unshifted.basis as `LinSols`

-/

/-- The whole Unshifted.basis as `LinSols`. -/
def basisa : Fin n ⊕ Fin n → (PureU1 (2 * n + 1)).LinSols := fun i =>
  match i with
  | .inl i => Unshifted.basis i
  | .inr i => Shifted.basis i

/-!

### E.2. The inclusion of the span of the combined Unshifted.basis into charges

-/

/-- A point in the span of the Unshifted.basis as a charge. -/
def Pa (f : Fin n → ℚ) (g : Fin n → ℚ) : (PureU1 (2 * n + 1)).Charges :=
  Unshifted.planeCharges f + Shifted.planeCharges g

/-!

### E.3. Components of the inclusion

-/

set_option backward.isDefEq.respectTransparency false in
lemma Pa_oddShiftShiftZero (f g : Fin n.succ → ℚ) : Pa f g oddShiftShiftZero = f 0 := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [oddShiftShiftZero_eq_oddFst_zero]
  rw [oddShiftShiftZero_eq_oddShiftZero]
  rw [Shifted.planeCharges_oddShiftZero, oddShiftZero_eq_oddFst,
    Unshifted.planeCharges_oddFst, add_zero]

set_option backward.isDefEq.respectTransparency false in
lemma Pa_oddShiftShiftFst (f g : Fin n.succ → ℚ) (j : Fin n) :
    Pa f g (oddShiftShiftFst j) = f j.succ + g j.castSucc := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [oddShiftShiftFst_eq_oddFst_succ]
  rw [oddShiftShiftFst_eq_oddShiftFst_castSucc]
  rw [Shifted.planeCharges_oddShiftFst, oddShiftFst_castSucc_eq_oddFst_succ,
    Unshifted.planeCharges_oddFst]

set_option backward.isDefEq.respectTransparency false in
lemma Pa_oddShiftShiftMid (f g : Fin n.succ → ℚ) : Pa f g oddShiftShiftMid = g (Fin.last n) := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [oddShiftShiftMid_eq_oddMid]
  rw [oddShiftShiftMid_eq_oddShiftFst_last]
  rw [Shifted.planeCharges_oddShiftFst, oddShiftFst_last_eq_oddMid,
    Unshifted.planeCharges_oddMid, zero_add]

set_option backward.isDefEq.respectTransparency false in
lemma Pa_oddShiftShiftSnd (f g : Fin n.succ → ℚ) (j : Fin n.succ) :
    Pa f g (oddShiftShiftSnd j) = - f j - g j := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [oddShiftShiftSnd_eq_oddSnd]
  rw [oddShiftShiftSnd_eq_oddShiftSnd]
  rw [Shifted.planeCharges_oddShiftSnd, oddShiftSnd_eq_oddSnd, Unshifted.planeCharges_oddSnd]
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
  rw [Pa, Unshifted.planeCharges] at h
  simp only [succ_eq_add_one, hf, zero_smul, sum_const_zero, zero_add] at h
  exact Shifted.planeCharges_zero g h

/-!

### E.5. The inclusion of the span of the combined Unshifted.basis into LinSols

-/

/-- A point in the span of the whole Unshifted.basis. -/
def Pa' (f : (Fin n) ⊕ (Fin n) → ℚ) : (PureU1 (2 * n + 1)).LinSols :=
    ∑ i, f i • basisa i

lemma Pa'_P'_P!' (f : (Fin n) ⊕ (Fin n) → ℚ) :
    Pa' f = Unshifted.planeLinSols (f ∘ Sum.inl) + Shifted.planeLinSols (f ∘ Sum.inr) := by
  exact Fintype.sum_sum_type _

/-!

### E.6. The combined Unshifted.basis vectors are linearly independent

-/

lemma basisa_linear_independent : LinearIndependent ℚ (@basisa n.succ) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change Pa' f = 0 at h
  have h1 : (Pa' f).val = 0 := congrArg ACCSystemLinear.LinSols.val h
  rw [Pa'_P'_P!'] at h1
  change (Unshifted.planeLinSols (f ∘ Sum.inl)).val +
      (Shifted.planeLinSols (f ∘ Sum.inr)).val = 0 at h1
  rw [Shifted.planeLinSols_val, Unshifted.planeLinSols_val] at h1
  change Pa (f ∘ Sum.inl) (f ∘ Sum.inr) = 0 at h1
  have hf := Pa_zero (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  have hg := Pa_zero! (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  intro i
  simp_all only [succ_eq_add_one, Function.comp_apply]
  cases i <;> simp_all

/-!

### E.7. Injectivity of the inclusion into linear solutions

-/

lemma Pa'_eq (f f' : (Fin n.succ) ⊕ (Fin n.succ) → ℚ) : Pa' f = Pa' f' ↔ f = f' := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · funext i
    rw [Pa', Pa'] at h
    have h1 : ∑ i : Fin n.succ ⊕ Fin n.succ, (f i + (- f' i)) • basisa i = 0 := by
      simp only [add_smul, neg_smul]
      rw [Finset.sum_add_distrib, h, ← Finset.sum_add_distrib]
      simp
    have h2 : ∀ i, (f i + (- f' i)) = 0 :=
      Fintype.linearIndependent_iff.mp (@basisa_linear_independent n) (fun i => f i + -f' i) h1
    linarith [h2 i]
  · rw [h]

lemma Pa'_elim_eq_iff (g g' : Fin n.succ → ℚ) (f f' : Fin n.succ → ℚ) :
    Pa' (Sum.elim g f) = Pa' (Sum.elim g' f') ↔ Pa g f = Pa g' f' := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [Pa'_eq, Sum.elim_eq_iff] at h
    rw [h.left, h.right]
  · apply ACCSystemLinear.LinSols.ext
    rw [Pa'_P'_P!', Pa'_P'_P!']
    simp only [succ_eq_add_one, ACCSystemLinear.linSolsAddCommMonoid_add_val,
      Unshifted.planeLinSols_val, Shifted.planeLinSols_val]
    exact h

lemma Pa_eq (g g' : Fin n.succ → ℚ) (f f' : Fin n.succ → ℚ) :
    Pa g f = Pa g' f' ↔ g = g' ∧ f = f' := by
  rw [← Pa'_elim_eq_iff]
  rw [← Sum.elim_eq_iff]
  exact Pa'_eq _ _

/-!

### E.8. Cardinality of the Unshifted.basis

-/

lemma basisa_card : Fintype.card ((Fin n.succ) ⊕ (Fin n.succ)) =
    Module.finrank ℚ (PureU1 (2 * n.succ + 1)).LinSols := by
  erw [BasisLinear.finrank_AnomalyFreeLinear]
  simp [Fintype.card_sum, Fintype.card_fin, two_mul]

/-!

### E.9. The Unshifted.basis vectors as a Unshifted.basis

-/

/-- The Unshifted.basis formed out of our basisa vectors. -/
noncomputable def basisaAsBasis :
    Basis (Fin n.succ ⊕ Fin n.succ) ℚ (PureU1 (2 * n.succ + 1)).LinSols :=
  basisOfLinearIndependentOfCardEqFinrank (@basisa_linear_independent n) basisa_card

/-!

## F. Every Lienar solution is the sum of a point from each plane

-/

lemma span_basis (S : (PureU1 (2 * n.succ + 1)).LinSols) :
    ∃ (g f : Fin n.succ → ℚ), S.val = Unshifted.planeCharges g + Shifted.planeCharges f := by
  obtain ⟨f, hf⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℚ).mp (Basis.mem_span basisaAsBasis S)
  simp only [succ_eq_add_one, basisaAsBasis, coe_basisOfLinearIndependentOfCardEqFinrank,
    Fintype.sum_sum_type] at hf
  change Unshifted.planeLinSols _ + Shifted.planeLinSols _ = S at hf
  refine ⟨f ∘ Sum.inl, f ∘ Sum.inr, ?_⟩
  rw [← hf]
  simp only [succ_eq_add_one, ACCSystemLinear.linSolsAddCommMonoid_add_val,
    Unshifted.planeLinSols_val, Shifted.planeLinSols_val]
  rfl

/-!

### F.1. Relation under permutations

-/

lemma span_basis_swap! {S : (PureU1 (2 * n.succ + 1)).LinSols} (j : Fin n.succ)
    (hS : ((FamilyPermutations (2 * n.succ + 1)).linSolRep
    (Equiv.swap (oddShiftFst j) (oddShiftSnd j))) S = S') (g f : Fin n.succ → ℚ)
    (hS1 : S.val = Unshifted.planeCharges g + Shifted.planeCharges f) : ∃ (g' f' : Fin n.succ → ℚ),
    S'.val = Unshifted.planeCharges g' + Shifted.planeCharges f' ∧
    Shifted.planeCharges f' = Shifted.planeCharges f +
    (S.val (oddShiftSnd j) - S.val (oddShiftFst j)) • Shifted.basisAsCharges j ∧ g' = g := by
  let X := Shifted.planeCharges f +
    (S.val (oddShiftSnd j) - S.val (oddShiftFst j)) • Shifted.basisAsCharges j
  have hf : Shifted.planeCharges f ∈ Submodule.span ℚ (Set.range Shifted.basisAsCharges) :=
    (Submodule.mem_span_range_iff_exists_fun ℚ).mpr ⟨f, rfl⟩
  have hP : (S.val (oddShiftSnd j) - S.val (oddShiftFst j)) • Shifted.basisAsCharges j ∈
      Submodule.span ℚ (Set.range Shifted.basisAsCharges) :=
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hX : X ∈ Submodule.span ℚ (Set.range (Shifted.basisAsCharges)) :=
    Submodule.add_mem _ hf hP
  obtain ⟨f', hf'⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hX
  use g, f'
  change Shifted.planeCharges f' = _ at hf'
  erw [hf']
  simp only [and_self, and_true, X]
  rw [← add_assoc, ← hS1]
  apply Shifted.swap_as_add at hS
  exact hS

end VectorLikeOddPlane

end PureU1
