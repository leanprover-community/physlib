/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.BasisLinear
public import Physlib.QFT.QED.AnomalyCancellation.VectorLike
/-!

# Splitting the linear solutions in the even case into two ACC-satisfying planes

## i. Overview

We split the linear solutions of `PureU1 (2 * n.succ)` into two planes,
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
  - A.1. The even split: Spltting the charges up via `n.succ + n.succ`
  - A.2. The shifted even split: Spltting the charges up via `1 + (n + n + 1)`
  - A.3. Lemmas relating the two splittings
- B. The unshifted plane
  - B.1. The basis vectors of the unshifted plane as charges
  - B.2. Components of the basis vectors
  - B.3. The basis vectors satisfy the linear ACCs
  - B.4. The basis vectors satisfy the cubic ACC
  - B.5. The basis vectors as linear solutions
  - B.6. The inclusion of the unshifted plane into charges
  - B.7. Components of the inclusion into charges
  - B.8. The inclusion into charges satisfies the linear and cubic ACCs
  - B.9. Kernel of the inclusion into charges
  - B.10. The inclusion of the plane into linear solutions
  - B.11. The basis vectors are linearly independent
  - B.12. Every vector-like even solution is in the span of the basis of the unshifted plane
- C. The shifted plane
  - C.2. Components of the vectors
  - C.3. The vectors satisfy the linear ACCs
  - C.4. The vectors satisfy the cubic ACC
  - C.6. The vectors as linear solutions
  - C.7. The inclusion of the shifted plane into charges
  - C.8. Components of the inclusion into charges
  - C.9. The inclusion into charges satisfies the cubic ACC
  - C.10. Kernel of the inclusion into charges
  - C.11. The inclusion of the shifted plane into the span of the basis
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

* https://arxiv.org/pdf/1912.04804.pdf. [ref: arxiv_1912_04804]
-/

@[expose] public section

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
  · exact h1 ⟨i, hi⟩
  · have h3 : evenSnd ⟨i - n.succ, by omega⟩ = i := by
      simp only [succ_eq_add_one, evenSnd, Fin.ext_iff, Fin.val_cast, Fin.val_natAdd]
      omega
    exact h3 ▸ h2 _

lemma sum_even (S : Fin (2 * n.succ) → ℚ) :
    ∑ i, S i = ∑ i : Fin n.succ, ((S ∘ evenFst) i + (S ∘ evenSnd) i) := by
  rw [← Equiv.sum_comp (Fin.castOrderIso (split_equal n.succ)).toEquiv S, Fin.sum_univ_add,
    Finset.sum_add_distrib]
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
  rw [h1, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add, Finset.sum_add_distrib]
  simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton, Function.comp_apply,
    evenShiftZero, evenShiftLast, evenShiftFst, evenShiftSnd]
  abel

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
  omega

/-!

## B. The unshifted plane

-/

namespace Unshifted

/-!

### B.1. The basis vectors of the unshifted plane as charges

-/

set_option backward.isDefEq.respectTransparency false in
/-- The unshifted part of the basis as charges. -/
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

set_option backward.isDefEq.respectTransparency false in
lemma basis_on_evenFst_self (j : Fin n.succ) : basisAsCharges j (evenFst j) = 1 := by
  simp [basisAsCharges]

set_option backward.isDefEq.respectTransparency false in
lemma basis_on_evenFst_other {k j : Fin n.succ} (h : k ≠ j) :
    basisAsCharges k (evenFst j) = 0 := by
  simp only [basisAsCharges, succ_eq_add_one, evenFst, evenSnd]
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

set_option backward.isDefEq.respectTransparency false in
lemma basis_on_other {k : Fin n.succ} {j : Fin (2 * n.succ)} (h1 : j ≠ evenFst k)
    (h2 : j ≠ evenSnd k) : basisAsCharges k j = 0 := by
  simp only [basisAsCharges, ite_eq_right h1, ite_eq_right h2]

set_option backward.isDefEq.respectTransparency false in
lemma basis_evenSnd_eq_neg_evenFst (j i : Fin n.succ) :
    basisAsCharges j (evenSnd i) = - basisAsCharges j (evenFst i) := by
  simp only [basisAsCharges, succ_eq_add_one, evenSnd, evenFst]
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

set_option backward.isDefEq.respectTransparency false in
lemma basis_linearACC (j : Fin n.succ) : (accGrav (2 * n.succ)) (basisAsCharges j) = 0 := by
  simp [accGrav, sum_even, basis_evenSnd_eq_neg_evenFst]
/-!

### B.4. The basis vectors satisfy the cubic ACC

-/
set_option backward.isDefEq.respectTransparency false in
lemma basis_accCube (j : Fin n.succ) :
    accCube (2 * n.succ) (basisAsCharges j) = 0 := by
  rw [accCube_explicit, sum_even]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [succ_eq_add_one, Function.comp_apply, basis_evenSnd_eq_neg_evenFst]
  ring

/-!

### B.5. The basis vectors as linear solutions

-/

/-- The unshifted part of the basis as `LinSols`. -/
@[simps!]
def basis (j : Fin n.succ) : (PureU1 (2 * n.succ)).LinSols :=
  ⟨basisAsCharges j, by
    intro i
    match i with
    | ⟨0, _⟩ => exact basis_linearACC j⟩

/-!

### B.6. The inclusion of the unshifted plane into charges

-/

/-- A point in the span of the unshifted part of the basis as a charge. -/
def planeCharges (f : Fin n.succ → ℚ) : (PureU1 (2 * n.succ)).Charges := ∑ i, f i • basisAsCharges i

/-!

### B.7. Components of the inclusion into charges

-/

lemma planeCharges_evenFst (f : Fin n.succ → ℚ) (j : Fin n.succ) :
    planeCharges f (evenFst j) = f j := by
  rw [planeCharges, sum_of_charges]
  simp only [succ_eq_add_one, HSMul.hSMul, SMul.smul]
  rw [Fintype.sum_eq_single j]
  · simp [basis_on_evenFst_self]
  · exact fun k hkj => mul_eq_zero_of_right (f k) (basis_on_evenFst_other hkj)

lemma planeCharges_evenSnd (f : Fin n.succ → ℚ) (j : Fin n.succ) :
    planeCharges f (evenSnd j) = - f j := by
  rw [planeCharges, sum_of_charges]
  simp only [succ_eq_add_one, HSMul.hSMul, SMul.smul]
  rw [Fintype.sum_eq_single j]
  · simp [basis_on_evenSnd_self]
  · exact fun k hkj => mul_eq_zero_of_right (f k) (basis_on_evenSnd_other hkj)

set_option backward.isDefEq.respectTransparency false in
lemma planeCharges_evenSnd_evenFst (f : Fin n.succ → ℚ) :
    planeCharges f ∘ evenSnd = - planeCharges f ∘ evenFst := by
  funext j
  simp [planeCharges_evenFst, planeCharges_evenSnd]

/-!

### B.8. The inclusion into charges satisfies the linear and cubic ACCs

-/

set_option backward.isDefEq.respectTransparency false in
lemma planeCharges_linearACC (f : Fin n.succ → ℚ) :
    (accGrav (2 * n.succ)) (planeCharges f) = 0 := by
  simp [accGrav, sum_even, planeCharges_evenSnd, planeCharges_evenFst]

set_option backward.isDefEq.respectTransparency false in
lemma planeCharges_accCube (f : Fin n.succ → ℚ) : accCube (2 * n.succ) (planeCharges f) = 0 := by
  rw [accCube_explicit, sum_even]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [succ_eq_add_one, Function.comp_apply, planeCharges_evenFst, planeCharges_evenSnd]
  ring

/-!

### B.9. Kernel of the inclusion into charges

-/

lemma planeCharges_zero (f : Fin n.succ → ℚ) (h : planeCharges f = 0) : ∀ i, f i = 0 := by
  exact fun i => (planeCharges_evenFst f i).symm.trans (congr_fun h (evenFst i))

/-!

### B.10. The inclusion of the plane into linear solutions

-/

/-- A point in the span of the unshifted part of the basis. -/
def planeLinSols (f : Fin n.succ → ℚ) : (PureU1 (2 * n.succ)).LinSols := ∑ i, f i • basis i

set_option backward.isDefEq.respectTransparency false in
lemma planeLinSols_val (f : Fin n.succ → ℚ) : (planeLinSols f).val = planeCharges f := by
  simp only [succ_eq_add_one, planeLinSols, planeCharges]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  rfl

/-!

### B.11. The basis vectors are linearly independent

-/

theorem basis_linear_independent : LinearIndependent ℚ (@basis n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change planeLinSols f = 0 at h
  exact planeCharges_zero f ((planeLinSols_val f).symm.trans (congrArg _ h))

/-!

### B.12. Every vector-like even solution is in the span of the basis of the unshifted plane

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
  erw [planeLinSols_val]
  apply ext_even
  · intro i
    rw [planeCharges_evenFst]
    rfl
  · intro i
    rw [planeCharges_evenSnd]
    have ht := hS i
    change sort S.val (evenFst i) = - sort S.val (evenSnd i) at ht
    have h : sort S.val (evenSnd i) = - sort S.val (evenFst i) := by
      rw [ht]
      ring
    rw [h]
    rfl



end Unshifted

/-!

## C. The shifted plane

-/

namespace Shifted

set_option backward.isDefEq.respectTransparency false in
/-- The shifted part of the basis as charges. -/
def basisAsCharges (j : Fin n) : (PureU1 (2 * n.succ)).Charges :=
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

set_option backward.isDefEq.respectTransparency false in
lemma basis_on_evenShiftFst_self (j : Fin n) : basisAsCharges j (evenShiftFst j) = 1 := by
  simp [basisAsCharges]

set_option backward.isDefEq.respectTransparency false in
lemma basis_on_other {k : Fin n} {j : Fin (2 * n.succ)} (h1 : j ≠ evenShiftFst k)
    (h2 : j ≠ evenShiftSnd k) : basisAsCharges k j = 0 := by
  simp only [basisAsCharges, ite_eq_right h1, ite_eq_right h2]

lemma basis_on_evenShiftFst_other {k j : Fin n} (h : k ≠ j) :
    basisAsCharges k (evenShiftFst j) = 0 := by
  rw [ne_eq, Fin.ext_iff] at h
  refine basis_on_other ?_ ?_ <;>
    simp only [ne_eq, Fin.ext_iff, evenShiftFst, evenShiftSnd, Fin.val_cast, Fin.val_castAdd,
      Fin.val_natAdd] <;>
    omega

set_option backward.isDefEq.respectTransparency false in
lemma basis_evenShiftSnd_eq_neg_evenShiftFst (j i : Fin n) :
    basisAsCharges j (evenShiftSnd i) = - basisAsCharges j (evenShiftFst i) := by
  simp only [basisAsCharges, succ_eq_add_one, evenShiftSnd, evenShiftFst]
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

lemma basis_on_evenShiftSnd_self (j : Fin n) : basisAsCharges j (evenShiftSnd j) = - 1 := by
  rw [basis_evenShiftSnd_eq_neg_evenShiftFst, basis_on_evenShiftFst_self]

lemma basis_on_evenShiftSnd_other {k j : Fin n} (h : k ≠ j) :
    basisAsCharges k (evenShiftSnd j) = 0 := by
  rw [basis_evenShiftSnd_eq_neg_evenShiftFst, basis_on_evenShiftFst_other h]
  rfl

lemma basis_on_evenShiftZero (j : Fin n) : basisAsCharges j evenShiftZero = 0 := by
  refine basis_on_other ?_ ?_ <;>
    simp only [ne_eq, Fin.ext_iff, evenShiftZero, evenShiftFst, evenShiftSnd, Fin.val_cast,
      Fin.val_castAdd, Fin.val_natAdd, Fin.val_eq_zero] <;>
    omega

lemma basis_on_evenShiftLast (j : Fin n) : basisAsCharges j evenShiftLast = 0 := by
  refine basis_on_other ?_ ?_ <;>
    simp only [ne_eq, Fin.ext_iff, evenShiftLast, evenShiftFst, evenShiftSnd, Fin.val_cast,
      Fin.val_castAdd, Fin.val_natAdd, Fin.val_eq_zero, add_zero] <;>
    omega

/-!

### C.3. The vectors satisfy the linear ACCs

-/

set_option backward.isDefEq.respectTransparency false in
lemma basis_linearACC (j : Fin n) : (accGrav (2 * n.succ)) (basisAsCharges j) = 0 := by
  simp [accGrav, sum_evenShift, basis_on_evenShiftZero, basis_on_evenShiftLast,
    basis_evenShiftSnd_eq_neg_evenShiftFst]

/-!

### C.4. The vectors satisfy the cubic ACC

-/

set_option backward.isDefEq.respectTransparency false in
lemma basis_accCube (j : Fin n) :
    accCube (2 * n.succ) (basisAsCharges j) = 0 := by
  rw [accCube_explicit, sum_evenShift]
  rw [basis_on_evenShiftLast, basis_on_evenShiftZero]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Function.comp_apply,
    zero_add]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [basis_evenShiftSnd_eq_neg_evenShiftFst]
  ring

/-!

### C.6. The vectors as linear solutions

-/

/-- The shifted part of the basis as `LinSols`. -/
@[simps!]
def basis (j : Fin n) : (PureU1 (2 * n.succ)).LinSols :=
  ⟨basisAsCharges j, by
    intro i
    match i with
    | ⟨0, _⟩ => exact basis_linearACC j⟩

/-!

### C.7. The inclusion of the shifted plane into charges

-/

/-- A point in the span of the shifted part of the basis as a charge. -/
def planeCharges (f : Fin n → ℚ) : (PureU1 (2 * n.succ)).Charges := ∑ i, f i • basisAsCharges i

/-!

### C.8. Components of the inclusion into charges

-/

lemma planeCharges_evenShiftFst (f : Fin n → ℚ) (j : Fin n) :
    planeCharges f (evenShiftFst j) = f j := by
  rw [planeCharges, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Fintype.sum_eq_single j]
  · simp [basis_on_evenShiftFst_self]
  · exact fun k hkj => mul_eq_zero_of_right (f k) (basis_on_evenShiftFst_other hkj)

lemma planeCharges_evenShiftSnd (f : Fin n → ℚ) (j : Fin n) :
    planeCharges f (evenShiftSnd j) = - f j := by
  rw [planeCharges, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Fintype.sum_eq_single j]
  · simp [basis_on_evenShiftSnd_self]
  · exact fun k hkj => mul_eq_zero_of_right (f k) (basis_on_evenShiftSnd_other hkj)

set_option backward.isDefEq.respectTransparency false in
lemma planeCharges_evenShiftZero (f : Fin n → ℚ) : planeCharges f (evenShiftZero) = 0 := by
  simp [planeCharges, sum_of_charges, HSMul.hSMul, SMul.smul, basis_on_evenShiftZero]

set_option backward.isDefEq.respectTransparency false in
lemma planeCharges_evenShiftLast (f : Fin n → ℚ) : planeCharges f evenShiftLast = 0 := by
  simp [planeCharges, sum_of_charges, HSMul.hSMul, SMul.smul, basis_on_evenShiftLast]

/-!

### C.9. The inclusion into charges satisfies the cubic ACC

-/

set_option backward.isDefEq.respectTransparency false in
lemma planeCharges_accCube (f : Fin n → ℚ) : accCube (2 * n.succ) (planeCharges f) = 0 := by
  rw [accCube_explicit, sum_evenShift, planeCharges_evenShiftZero, planeCharges_evenShiftLast]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Function.comp_apply,
    zero_add]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [planeCharges_evenShiftFst, planeCharges_evenShiftSnd]
  ring

/-!

### C.10. Kernel of the inclusion into charges

-/

lemma planeCharges_zero (f : Fin n → ℚ) (h : planeCharges f = 0) : ∀ i, f i = 0 := by
  exact fun i => (planeCharges_evenShiftFst f i).symm.trans (congr_fun h (evenShiftFst i))

/-!

### C.11. The inclusion of the shifted plane into the span of the basis

-/

lemma planeCharges_in_span (f : Fin n → ℚ) :
    planeCharges f ∈ Submodule.span ℚ (Set.range basisAsCharges) := by
  exact (Submodule.mem_span_range_iff_exists_fun ℚ).mpr ⟨f, rfl⟩

/-!

### C.12. The inclusion of the plane into linear solutions

-/

/-- A point in the span of the shifted part of the basis. -/
def planeLinSols (f : Fin n → ℚ) : (PureU1 (2 * n.succ)).LinSols := ∑ i, f i • basis i

set_option backward.isDefEq.respectTransparency false in
lemma planeLinSols_val (f : Fin n → ℚ) : (planeLinSols f).val = planeCharges f := by
  simp only [succ_eq_add_one, planeLinSols, planeCharges]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  rfl

/-!

### C.13. The basis vectors are linearly independent

-/

theorem basis_linear_independent : LinearIndependent ℚ (@basis n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change planeLinSols f = 0 at h
  exact planeCharges_zero f ((planeLinSols_val f).symm.trans (congrArg _ h))

/-!

### C.14. Properties of the basis vectors relating to the span

-/

lemma smul_basisAsCharges_in_span (S : (PureU1 (2 * n.succ)).LinSols) (j : Fin n) :
    (S.val (evenShiftSnd j) - S.val (evenShiftFst j)) • basisAsCharges j ∈
    Submodule.span ℚ (Set.range basisAsCharges) := by
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-!

### C.15. Permutations as additions of basis vectors

-/

set_option backward.isDefEq.respectTransparency false in
/-- Swapping the elements evenShiftFst j and evenShiftSnd j is equivalent to
  adding a vector basisAsCharges j. -/
lemma swap_as_add {S S' : (PureU1 (2 * n.succ)).LinSols} (j : Fin n)
    (hS : ((FamilyPermutations (2 * n.succ)).linSolRep
    (Equiv.swap (evenShiftFst j) (evenShiftSnd j))) S = S') :
    S'.val = S.val + (S.val (evenShiftSnd j) - S.val (evenShiftFst j)) • basisAsCharges j := by
  funext i
  rw [← hS, FamilyPermutations_anomalyFreeLinear_apply]
  by_cases hi : i = evenShiftFst j
  · subst hi
    simp [HSMul.hSMul, basis_on_evenShiftFst_self, Equiv.swap_apply_left]
  · by_cases hi2 : i = evenShiftSnd j
    · simp [HSMul.hSMul, hi2, basis_on_evenShiftSnd_self, Equiv.swap_apply_right]
    · simp only [succ_eq_add_one, Equiv.invFun_as_coe, HSMul.hSMul,
      ACCSystemCharges.chargesAddCommMonoid_add, ACCSystemCharges.chargesModule_smul]
      rw [basis_on_other hi hi2]
      aesop


end Shifted

/-!

## D. Mixed cubic ACCs involving points from both planes

-/

set_option backward.isDefEq.respectTransparency false in
lemma unshifted_unshifted_shifted_accCube (g : Fin n.succ → ℚ) (j : Fin n) :
    accCubeTriLinSymm (Unshifted.planeCharges g) (Unshifted.planeCharges g)
      (Shifted.basisAsCharges j)
    = g (j.succ) ^ 2 - g (j.castSucc) ^ 2 := by
  simp only [succ_eq_add_one, accCubeTriLinSymm,
    TriLinearSymm.mk₃_toFun_apply_apply]
  erw [sum_evenShift, Shifted.basis_on_evenShiftZero, Shifted.basis_on_evenShiftLast]
  simp only [mul_zero, add_zero, Function.comp_apply, zero_add]
  rw [Fintype.sum_eq_single j, Shifted.basis_on_evenShiftFst_self,
    Shifted.basis_on_evenShiftSnd_self]
  · simp only [evenShiftFst_eq_evenFst_succ, mul_one, evenShiftSnd_eq_evenSnd_castSucc, mul_neg]
    rw [Unshifted.planeCharges_evenFst, Unshifted.planeCharges_evenSnd]
    ring
  · intro k hkj
    erw [Shifted.basis_on_evenShiftFst_other hkj.symm, Shifted.basis_on_evenShiftSnd_other hkj.symm]
    simp only [mul_zero, add_zero]

set_option backward.isDefEq.respectTransparency false in
lemma shifted_shifted_unshifted_accCube (g : Fin n → ℚ) (j : Fin n.succ) :
    accCubeTriLinSymm (Shifted.planeCharges g) (Shifted.planeCharges g) (Unshifted.basisAsCharges j)
    = (Shifted.planeCharges g (evenFst j))^2 - (Shifted.planeCharges g (evenSnd j))^2 := by
  simp only [succ_eq_add_one, accCubeTriLinSymm,
    TriLinearSymm.mk₃_toFun_apply_apply]
  erw [sum_even]
  simp only [Function.comp_apply]
  rw [Fintype.sum_eq_single j, Unshifted.basis_on_evenFst_self, Unshifted.basis_on_evenSnd_self]
  · simp only [mul_one, mul_neg]
    ring
  · intro k hkj
    erw [Unshifted.basis_on_evenFst_other hkj.symm, Unshifted.basis_on_evenSnd_other hkj.symm]
    simp only [mul_zero, add_zero]

/-!

## E. The combined basis

-/

/-!

### E.1. As a map into linear solutions

-/
/-- The whole basis as `LinSols`. -/
def basisa : (Fin n.succ) ⊕ (Fin n) → (PureU1 (2 * n.succ)).LinSols := fun i =>
  match i with
  | .inl i => Unshifted.basis i
  | .inr i => Shifted.basis i

/-!

### E.2. Inclusion of the span of the basis into charges

-/

/-- A point in the span of the basis as a charge. -/
def Pa (f : Fin n.succ → ℚ) (g : Fin n → ℚ) : (PureU1 (2 * n.succ)).Charges :=
  Unshifted.planeCharges f + Shifted.planeCharges g

/-!

### E.3. Components of the inclusion into charges

-/

set_option backward.isDefEq.respectTransparency false in
lemma Pa_evenShiftFst (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (j : Fin n) :
    Pa f g (evenShiftFst j) = f j.succ + g j := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [Shifted.planeCharges_evenShiftFst, evenShiftFst_eq_evenFst_succ,
    Unshifted.planeCharges_evenFst]

set_option backward.isDefEq.respectTransparency false in
lemma Pa_evenShiftSnd (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (j : Fin n) :
    Pa f g (evenShiftSnd j) = - f j.castSucc - g j := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [Shifted.planeCharges_evenShiftSnd, evenShiftSnd_eq_evenSnd_castSucc,
    Unshifted.planeCharges_evenSnd]
  ring

set_option backward.isDefEq.respectTransparency false in
lemma Pa_evenShitZero (f : Fin n.succ → ℚ) (g : Fin n → ℚ) : Pa f g (evenShiftZero) = f 0 := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [Shifted.planeCharges_evenShiftZero, evenShiftZero_eq_evenFst_zero,
    Unshifted.planeCharges_evenFst, add_zero]

set_option backward.isDefEq.respectTransparency false in
lemma Pa_evenShiftLast (f : Fin n.succ → ℚ) (g : Fin n → ℚ) :
    Pa f g (evenShiftLast) = - f (Fin.last n) := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [Shifted.planeCharges_evenShiftLast, evenShiftLast_eq_evenSnd_last,
    Unshifted.planeCharges_evenSnd, add_zero]

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
  rw [Pa, Unshifted.planeCharges] at h
  simp only [succ_eq_add_one, hf, zero_smul, sum_const_zero, zero_add] at h
  exact Shifted.planeCharges_zero g h

/-!

### E.5. The inclusion of the span of the basis into linear solutions

-/
/-- A point in the span of the whole basis. -/
def Pa' (f : (Fin n.succ) ⊕ (Fin n) → ℚ) : (PureU1 (2 * n.succ)).LinSols :=
    ∑ i, f i • basisa i

lemma Pa'_P'_P!' (f : (Fin n.succ) ⊕ (Fin n) → ℚ) :
    Pa' f = Unshifted.planeLinSols (f ∘ Sum.inl) + Shifted.planeLinSols (f ∘ Sum.inr) := by
  exact Fintype.sum_sum_type _

/-!

### E.6. The combined basis vectors are linearly independent

-/

theorem basisa_linear_independent : LinearIndependent ℚ (@basisa n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change Pa' f = 0 at h
  have h1 : (Pa' f).val = 0 := congrArg _ h
  rw [Pa'_P'_P!'] at h1
  simp only [ACCSystemLinear.linSolsAddCommMonoid_add_val, Unshifted.planeLinSols_val,
    Shifted.planeLinSols_val] at h1
  have hf := Pa_zero (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  have hg := Pa_zero! (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  rintro (i | i)
  · exact hf i
  · exact hg i
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
    have h2 := Fintype.linearIndependent_iff.mp basisa_linear_independent _ h1
    linarith [h2 i]
  · rw [h]

lemma Pa'_elim_eq_iff (g g' : Fin n.succ → ℚ) (f f' : Fin n → ℚ) :
    Pa' (Sum.elim g f) = Pa' (Sum.elim g' f') ↔ Pa g f = Pa g' f' := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [Pa'_eq, Sum.elim_eq_iff] at h
    rw [h.left, h.right]
  · apply ACCSystemLinear.LinSols.ext
    rw [Pa'_P'_P!', Pa'_P'_P!']
    simp only [succ_eq_add_one, ACCSystemLinear.linSolsAddCommMonoid_add_val,
      Unshifted.planeLinSols_val, Shifted.planeLinSols_val]
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
    ∃ (g : Fin n.succ → ℚ) (f : Fin n → ℚ),
      S.val = Unshifted.planeCharges g + Shifted.planeCharges f := by
  have h := (Submodule.mem_span_range_iff_exists_fun ℚ).mp (Basis.mem_span basisaAsBasis S)
  obtain ⟨f, hf⟩ := h
  simp only [succ_eq_add_one, basisaAsBasis, coe_basisOfLinearIndependentOfCardEqFinrank,
    Fintype.sum_sum_type] at hf
  change Unshifted.planeLinSols _ + Shifted.planeLinSols _ = S at hf
  use f ∘ Sum.inl
  use f ∘ Sum.inr
  rw [← hf]
  simp only [succ_eq_add_one, ACCSystemLinear.linSolsAddCommMonoid_add_val,
    Unshifted.planeLinSols_val, Shifted.planeLinSols_val]
  rfl

/-!

### F.1. Relation under permutations

-/
lemma span_basis_swap! {S : (PureU1 (2 * n.succ)).LinSols} (j : Fin n)
    (hS : ((FamilyPermutations (2 * n.succ)).linSolRep
    (Equiv.swap (evenShiftFst j) (evenShiftSnd j))) S = S') (g : Fin n.succ → ℚ) (f : Fin n → ℚ)
    (h : S.val = Unshifted.planeCharges g + Shifted.planeCharges f) :
    ∃ (g' : Fin n.succ → ℚ) (f' : Fin n → ℚ),
      S'.val = Unshifted.planeCharges g' + Shifted.planeCharges f' ∧
      Shifted.planeCharges f' = Shifted.planeCharges f +
      (S.val (evenShiftSnd j) - S.val (evenShiftFst j)) • Shifted.basisAsCharges j ∧ g' = g := by
  let X := Shifted.planeCharges f +
    (S.val (evenShiftSnd j) - S.val (evenShiftFst j)) • Shifted.basisAsCharges j
  have hX : X ∈ Submodule.span ℚ (Set.range (Shifted.basisAsCharges)) := by
    apply Submodule.add_mem
    exact (Shifted.planeCharges_in_span f)
    exact (Shifted.smul_basisAsCharges_in_span S j)
  have hXsum := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hX
  obtain ⟨f', hf'⟩ := hXsum
  use g
  use f'
  change Shifted.planeCharges f' = _ at hf'
  erw [hf']
  simp only [and_self, and_true, X]
  rw [← add_assoc, ← h]
  apply Shifted.swap_as_add at hS
  exact hS

end VectorLikeEvenPlane

end PureU1
