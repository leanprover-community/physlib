/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.OfFieldLabel
import Mathlib.Tactic.Abel
/-!

# Charges associated with a potential term

## i. Overview

In this module we give the multiset of charges associated with a given type of potential term,
given a charge spectrum.

We will define two versions of this, one based on the underlying fields on the
potentials, and the charges that they carry, and one more explicit version which
is faster to compute with. The former is `ofPotentialTerm`, and the latter is
`ofPotentialTerm'`.

We will show that these two multisets have the same elements.

## ii. Key results

- `ofPotentialTerm` : The multiset of charges associated with a potential term,
  defined in terms of the fields making up that potential term, given a charge spectrum.
- `ofPotentialTerm'` : The multiset of charges associated with a potential term,
  defined explicitly, given a charge spectrum.

## iii. Table of contents

- A. Charges of a potential term from field labels
  - A.1. Monotonicity of `ofPotentialTerm`
  - A.2. Charges of potential terms for the empty charge spectrum
- B. Explicit construction of charges of a potential term
  - B.1. Explicit multisets for `ofPotentialTerm'`
  - B.2. `ofPotentialTerm'` on the empty charge spectrum
- C. Relation between two constructions of charges of potential terms
  - C.1. Showing that `ofPotentialTerm` is a subset of `ofPotentialTerm'`
  - C.2. Showing that `ofPotentialTerm'` is a subset of `ofPotentialTerm`
  - C.3. Equivalence of elements of `ofPotentialTerm` and `ofPotentialTerm'`
  - C.4. Induced monotonicity of `ofPotentialTerm'`

## iv. References

There are no known references for this material.

-/

namespace SuperSymmetry
namespace SU5

namespace ChargeSpectrum
open PotentialTerm

variable {𝓩 : Type} [AddCommGroup 𝓩]

/-!

## A. Charges of a potential term from field labels

We first define `ofPotentialTerm`, and prover properties of it.
This is slow to compute in practice.

-/

/-- Given a charges `x : Charges` associated to the representations, and a potential
  term `T`, the charges associated with instances of that potential term. -/
def ofPotentialTerm (x : ChargeSpectrum 𝓩) (T : PotentialTerm) : Multiset 𝓩 :=
  let add : Multiset 𝓩 → Multiset 𝓩 → Multiset 𝓩 := fun a b => (a ×ˢ b).map
      fun (x, y) => x + y
  (T.toFieldLabel.map fun F => (ofFieldLabel x F).val).foldl add {0}

/-!

### A.1. Monotonicity of `ofPotentialTerm`

We show that `ofPotentialTerm` is monotone in its charge spectrum argument.
That is if `x ⊆ y` then `ofPotentialTerm x T ⊆ ofPotentialTerm y T`.

-/
lemma ofPotentialTerm_mono {x y : ChargeSpectrum 𝓩} (h : x ⊆ y) (T : PotentialTerm) :
    x.ofPotentialTerm T ⊆ y.ofPotentialTerm T := by
  have h1 {S1 S2 T1 T2 : Multiset 𝓩} (h1 : S1 ⊆ S2) (h2 : T1 ⊆ T2) :
      (S1 ×ˢ T1) ⊆ S2 ×ˢ T2 :=
    Multiset.subset_iff.mpr (fun x => by simpa only [Multiset.mem_product, and_imp] using
      fun h1' h2' => ⟨h1 h1', h2 h2'⟩)
  rw [subset_def] at h
  cases T
  all_goals
    simp [ofPotentialTerm, PotentialTerm.toFieldLabel]
    repeat'
      apply Multiset.map_subset_map <| Multiset.subset_iff.mpr <|
        h1 _ (Finset.subset_def.mp (ofFieldLabel_mono h _))
    simp

/-!

### A.2. Charges of potential terms for the empty charge spectrum

For the empty charge spectrum, the charges associated with any potential term is empty.

-/

@[simp]
lemma ofPotentialTerm_empty (T : PotentialTerm) :
    ofPotentialTerm (∅ : ChargeSpectrum 𝓩) T = ∅ := by
  cases T
  all_goals
    rfl

/-!

## B. Explicit construction of charges of a potential term

We now turn to a more explicit construction of the charges associated with a potential term.
This is faster to compute with, but less obviously connected to the underlying
fields.

-/

/-- Given a charges `x : ChargeSpectrum` associated to the representations, and a potential
  term `T`, the charges associated with instances of that potential term.

  This is a more explicit form of `PotentialTerm`, which has the benefit that
  it is quick with `decide`, but it is not defined based on more fundamental
  concepts, like `ofPotentialTerm` is. -/
def ofPotentialTerm' (y : ChargeSpectrum 𝓩) (T : PotentialTerm) : Multiset 𝓩 :=
  let qHd := y.qHd
  let qHu := y.qHu
  let Q5 := y.Q5
  let Q10 := y.Q10
  match T with
  | μ =>
    match qHd, qHu with
    | none, _ => ∅
    | _, none => ∅
    | some qHd, some qHu => {qHd - qHu}
  | β =>
    match qHu with
    | none => ∅
    | some qHu => Q5.val.map (fun x => - qHu + x)
  | Λ => (Q5.product <| Q5.product <| Q10).val.map (fun x => x.1 + x.2.1 + x.2.2)
  | W1 => (Q5.product <| Q10.product <| Q10.product <| Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2.1 + x.2.2.2)
  | W2 =>
    match qHd with
    | none => ∅
    | some qHd =>
      (Q10.product <| Q10.product <| Q10).val.map (fun x => qHd + x.1 + x.2.1 + x.2.2)
  | W3 =>
    match qHu with
    | none => ∅
    | some qHu => (Q5.product <| Q5).val.map (fun x => -qHu - qHu + x.1 + x.2)
  | W4 =>
    match qHd, qHu with
    | none, _ => ∅
    | _, none => ∅
    | some qHd, some qHu => Q5.val.map (fun x => qHd - qHu - qHu + x)
  | K1 => (Q5.product <| Q10.product <| Q10).val.map
    (fun x => - x.1 + x.2.1 + x.2.2)
  | K2 =>
    match qHd, qHu with
    | none, _ => ∅
    | _, none => ∅
    | some qHd, some qHu => Q10.val.map (fun x => qHd + qHu + x)
  | topYukawa =>
    match qHu with
    | none => ∅
    | some qHu => (Q10.product <| Q10).val.map (fun x => - qHu + x.1 + x.2)
  | bottomYukawa =>
    match qHd with
    | none => ∅
    | some qHd => (Q5.product <| Q10).val.map (fun x => qHd + x.1 + x.2)

/-!

### B.1. Explicit multisets for `ofPotentialTerm'`

For each potential term, we give an explicit form of the multiset `ofPotentialTerm'`.

-/
lemma ofPotentialTerm'_μ_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' μ =
    (x.qHd.toFinset.product <| x.qHu.toFinset).val.map (fun x => x.1 - x.2) := by
  match x with
  | ⟨none, qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨some qHd, none, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨some qHd, some qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_β_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' β =
    (x.qHu.toFinset.product <| x.Q5).val.map (fun x => - x.1 + x.2) := by
  match x with
  | ⟨qHd, none, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨qHd, some qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_W2_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' W2 = (x.qHd.toFinset.product <|
      x.Q10.product <| x.Q10.product <| x.Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2.1 + x.2.2.2) := by
  match x with
  | ⟨none, qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨some qHd, qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_W3_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' W3 = (x.qHu.toFinset.product <| x.Q5.product <| x.Q5).val.map
    (fun x => -x.1 - x.1 + x.2.1 + x.2.2) := by
  match x with
  | ⟨qHd, none, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨qHd, some qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_W4_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' W4 = (x.qHd.toFinset.product <|
      x.qHu.toFinset.product <| x.Q5).val.map
    (fun x => x.1 - x.2.1 - x.2.1 + x.2.2) := by
  match x with
  | ⟨none, qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨some qHd, none, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨some qHd, some qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_K2_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' K2 = (x.qHd.toFinset.product <|
      x.qHu.toFinset.product <| x.Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2) := by
  match x with
  | ⟨none, qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨some qHd, none, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨some qHd, some qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_topYukawa_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' topYukawa = (x.qHu.toFinset.product <|
      x.Q10.product <| x.Q10).val.map
    (fun x => -x.1 + x.2.1 + x.2.2) := by
  match x with
  | ⟨qHd, none, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨qHd, some qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_bottomYukawa_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' bottomYukawa = (x.1.toFinset.product <|
      x.Q5.product <| x.Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2) := by
  match x with
  | ⟨none, qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨some qHd, qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']

/-!

### B.2. `ofPotentialTerm'` on the empty charge spectrum

We show that for the empty charge spectrum, the charges associated with any potential term is empty,
as defined through `ofPotentialTerm'`.

-/

@[simp]
lemma ofPotentialTerm'_empty (T : PotentialTerm) :
    ofPotentialTerm' (∅ : ChargeSpectrum 𝓩) T = ∅ := by
  cases T
  all_goals
    simp [ofPotentialTerm']
/-!

## C. Relation between two constructions of charges of potential terms

We now give the relation between `ofPotentialTerm` and `ofPotentialTerm'`.
We show that they have the same elements, by showing that they are subsets of each other.

The prove of some of these results are rather long since they involve explicit
case analysis for each potential term, due to the nature of the definition
of `ofPotentialTerm'`.

-/

/-!

### C.1. Showing that `ofPotentialTerm` is a subset of `ofPotentialTerm'`

We first show that `ofPotentialTerm` is a subset of `ofPotentialTerm'`.

-/

lemma ofPotentialTerm_subset_ofPotentialTerm' {x : ChargeSpectrum 𝓩} (T : PotentialTerm) :
    x.ofPotentialTerm T ⊆ x.ofPotentialTerm' T := by
  refine Multiset.subset_iff.mpr (fun n h => ?_)
  simp [ofPotentialTerm] at h
  cases T
  all_goals
    simp [PotentialTerm.toFieldLabel, -existsAndEq] at h
    obtain ⟨f1, f2, ⟨⟨f3, f4, ⟨h3, f4_mem⟩, rfl⟩, f2_mem⟩, f1_add_f2_eq_zero⟩ := h
  case' μ | β => obtain ⟨rfl⟩ := h3
  case' Λ | W1 | W2 | W3 | W4 | K1 | K2 | topYukawa | bottomYukawa =>
    obtain ⟨f5, f6, ⟨h4, f6_mem⟩, rfl⟩ := h3
  case' Λ | K1 | K2 | topYukawa | bottomYukawa => obtain ⟨rfl⟩ := h4
  case' W1 | W2 | W3 | W4 => obtain ⟨f7, f8, ⟨rfl, f8_mem⟩, rfl⟩ := h4
  all_goals
    try simp [ofPotentialTerm'_W2_finset, ofPotentialTerm'_W3_finset,
      ofPotentialTerm'_β_finset, ofPotentialTerm'_μ_finset,
      ofPotentialTerm'_W4_finset, ofPotentialTerm'_K2_finset,
      ofPotentialTerm'_topYukawa_finset, ofPotentialTerm'_bottomYukawa_finset]
    try simp [ofPotentialTerm', -existsAndEq]
    simp_all [ofFieldLabel, -existsAndEq]
  case' W1 => use f2, f4, f6, f8
  case' W2 => use f2, f4, f6, f8
  case' W3 => use (-f2), f6, f8
  case' W4 => use f6, (-f4), f8
  case' K1 => use (-f2), f4, f6
  case' K2 => use f4, f6, f2
  case' Λ => use f4, f6, f2
  case' topYukawa => use (-f2), f4, f6
  case' bottomYukawa => use f2, f4, f6
  case' β => use (-f4), f2
  all_goals simp_all
  all_goals
    rw [← f1_add_f2_eq_zero]
    abel

/-!

### C.2. Showing that `ofPotentialTerm'` is a subset of `ofPotentialTerm`

We now show the other direction of the subset relation, that
`ofPotentialTerm'` is a subset of `ofPotentialTerm`.

-/

lemma ofPotentialTerm'_subset_ofPotentialTerm [DecidableEq 𝓩]
    {x : ChargeSpectrum 𝓩} (T : PotentialTerm) :
    x.ofPotentialTerm' T ⊆ x.ofPotentialTerm T := by
  refine Multiset.subset_iff.mpr (fun n h => ?_)
  cases T
  all_goals
    try simp [ofPotentialTerm'_W2_finset, ofPotentialTerm'_W3_finset,
      ofPotentialTerm'_β_finset, ofPotentialTerm'_μ_finset,
      ofPotentialTerm'_W4_finset, ofPotentialTerm'_K2_finset,
      ofPotentialTerm'_topYukawa_finset, ofPotentialTerm'_bottomYukawa_finset] at h
    try simp [ofPotentialTerm', -existsAndEq] at h
  case' μ | β =>
    obtain ⟨q1, q2, ⟨q1_mem, q2_mem⟩, q_sum⟩ := h
  case' Λ | W3 | W4 | K1 | K2 | topYukawa | bottomYukawa =>
    obtain ⟨q1, q2, q3, ⟨q1_mem, q2_mem, q3_mem⟩, q_sum⟩ := h
  case' W1 | W2 =>
    obtain ⟨q1, q2, q3, q4, ⟨q1_mem, q2_mem, q3_mem, q4_mem⟩, q_sum⟩ := h
  case' μ => refine ofPotentialTerm_mono (x := ⟨q1, q2, ∅, ∅⟩) ?μSub _ ?μP
  case' β => refine ofPotentialTerm_mono (x := ⟨none, q1, {q2}, ∅⟩) ?βSub _ ?βP
  case' Λ =>
    refine ofPotentialTerm_mono (x := ⟨none, none, {q1, q2}, {q3}⟩) ?ΛSub _ ?ΛP
  case' W1 =>
    refine ofPotentialTerm_mono (x := ⟨none, none, {q1}, {q2, q3, q4}⟩) ?W1Sub _ ?W1P
  case' W2 =>
    refine ofPotentialTerm_mono (x := ⟨q1, none, ∅, {q2, q3, q4}⟩) ?W2Sub _ ?W2P
  case' W3 => refine ofPotentialTerm_mono (x := ⟨none, q1, {q2, q3}, ∅⟩) ?W3Sub _ ?W3P
  case' W4 => refine ofPotentialTerm_mono (x := ⟨q1, q2, {q3}, ∅⟩) ?W4Sub _ ?W4P
  case' K1 =>
    refine ofPotentialTerm_mono (x := ⟨none, none, {q1}, {q2, q3}⟩)
      ?K1Sub _ ?K1P
  case' K2 => refine ofPotentialTerm_mono (x := ⟨q1, q2, ∅, {q3}⟩) ?K2Sub _ ?K2P
  case' topYukawa =>
    refine ofPotentialTerm_mono (x := ⟨none, q1, ∅, {q2, q3}⟩)
      ?topYukawaSub _ ?topYukawaP
  case' bottomYukawa =>
    refine ofPotentialTerm_mono (x := ⟨q1, none, {q2}, {q3}⟩)
      ?bottomYukawaSub _ ?bottomYukawaP
  case' μSub | βSub | ΛSub | W1Sub | W2Sub | W3Sub | W4Sub | K1Sub | K2Sub |
      topYukawaSub | bottomYukawaSub =>
    rw [subset_def]
    simp_all [Finset.insert_subset, -existsAndEq]
  all_goals
    simp [ofPotentialTerm, PotentialTerm.toFieldLabel, ofFieldLabel]
  case ΛP =>
    use q1, q2
    simp [← q_sum]
  case W3P | K1P | topYukawaP =>
    use q2, q3
    simp [← q_sum]
    abel
  case W1P | W2P =>
    use q2, q3, q4
    simp [← q_sum]
    abel
  all_goals
    rw [← q_sum]
    try abel

/-!

### C.3. Equivalence of elements of `ofPotentialTerm` and `ofPotentialTerm'`

We now show that a charge is in `ofPotentialTerm` if and only if it is in
`ofPotentialTerm'`. I.e. their underlying finite sets are equal.
We do not say anything about the multiplicity of elements within the multisets,
which is not important for us.

-/
lemma mem_ofPotentialTerm_iff_mem_ofPotentialTerm [DecidableEq 𝓩]
    {T : PotentialTerm} {n : 𝓩} {y : ChargeSpectrum 𝓩} :
    n ∈ y.ofPotentialTerm T ↔ n ∈ y.ofPotentialTerm' T := by
  constructor
  · exact fun h => ofPotentialTerm_subset_ofPotentialTerm' T h
  · exact fun h => ofPotentialTerm'_subset_ofPotentialTerm T h

/-!

### C.4. Induced monotonicity of `ofPotentialTerm'`

Due to the equivalence of elements of `ofPotentialTerm` and `ofPotentialTerm'`,
we can now also show that `ofPotentialTerm'` is monotone in its charge spectrum argument.

-/

lemma ofPotentialTerm'_mono [DecidableEq 𝓩] {x y : ChargeSpectrum 𝓩}
    (h : x ⊆ y) (T : PotentialTerm) :
    x.ofPotentialTerm' T ⊆ y.ofPotentialTerm' T := by
  intro i
  rw [← mem_ofPotentialTerm_iff_mem_ofPotentialTerm, ← mem_ofPotentialTerm_iff_mem_ofPotentialTerm]
  exact fun a => ofPotentialTerm_mono h T a

end ChargeSpectrum

end SU5
end SuperSymmetry
