/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.OfPotentialTerm
public import Mathlib.Tactic.FinCases
/-!

# Charges allowing terms

## i. Overview

To each charge spectrum `x : ChargeSpectrum 𝓩` we say it
allows the potential term `T : PotentialTerm`, if one of the charges associated with that
potential term is zero.

What this means, is that there is a choice of charges from the charge spectrum `x` that
can be assigned to the fields in the potential term `T` such that the total charge is zero,
and therefore that the term is present in the potential. The presence of
absence of certain terms is of phenomenological importance.

This concept is captured by the proposition `AllowsTerm`.

In addition to this, for each potential term `T`, we define a function `allowsTermForm`
which takes three elements of `𝓩`, `a`, `b`, and `c` and returns a charge spectrum
which allows the term `T`. We will show in `allowsTerm_iff_subset_allowsTermForm`
that any charge spectrum that allows a term `T` has a subset which can be expressed as
`allowsTermForm a b c T` for some `a`, `b`, and `c`.

We also define the propositions `AllowsTermQ5 x q5 T` and `AllowsTermQ10 x q10 T`
which correspond to the condition that adding a charge `q5` to the `Q5` charges of
the charge spectrum `x`, or adding a charge `q10` to the `Q10` charges of the
charge spectrum `x`, leads to a zero charge in the charges of potential term `T`.

## ii. Key results

- `AllowsTerm` : The proposition that a charge spectrum allows a potential term.
- `allowsTermForm` : A function which for each potential term `T` and three charges
  `a`, `b`, and `c` returns a charge spectrum which allows the term `T`,
  and such that any charge spectrum allowing `T` has a subset of this form.
- `AllowsTermQ5` : The proposition that adding a charge `q5` to the `Q5` charges
  of a charge spectrum `x` allows the potential term `T` due to the addition of that charge.
- `AllowsTermQ10` : The proposition that adding a charge `q10` to the `Q10` charges
  of a charge spectrum `x` allows the potential term `T` due to the addition of that charge.

## iii. Table of contents

- A. Charge spectrums allowing potential terms
  - A.1. Decidability of `AllowsTerm`
  - A.2. Monotonicity of `AllowsTerm`
- B. Forms of charges which allow potential terms
  - B.1. `allowsTermForm` allows the potential term
  - B.2. Subset relations for `allowsTermForm`
  - B.3. Card of `allowsTermForm`
  - B.4. If `AllowsTerm` then subset equal to `allowsTermForm a b c T`
  - B.5. `AllowsTerm` if and only if subset equal to `allowsTermForm a b c T`
  - B.6. Cardinality of subset allowing potential term
- C. Allowing a potential term by insertion of a `Q5` charge
  - C.1. Decidability of `AllowsTermQ5`
  - C.2. AllowsTermQ5 or AllowsTerm from AllowsTerm with inserted of `Q5` charge
  - C.3. AllowsTerm with inserted of `Q5` charge from AllowsTermQ5
  - C.4. AllowsTerm with inserted of `Q5` charge iff AllowsTermQ5 or AllowsTerm
- D. Allowing a potential term by insertion of a `Q10` charge
  - D.1. Decidability of `AllowsTermQ5`
  - D.2. AllowsTermQ10 or AllowsTerm from AllowsTerm with inserted of `Q10` charge
  - D.3. AllowsTerm with inserted of `Q10` charge from AllowsTermQ5
  - D.4. AllowsTerm with inserted of `Q10` charge iff AllowsTermQ10 or AllowsTerm

## iv. References

There are no known references for the results in this file.

-/

@[expose] public section

namespace SuperSymmetry
namespace SU5

namespace ChargeSpectrum

variable {𝓩 : Type} [AddCommGroup 𝓩]

/-!

## A. Charge spectrums allowing potential terms

We first define the proposition `AllowsTerm`, which for a charge spectrum `x : ChargeSpectrum 𝓩`
and a potential term `T : PotentialTerm`, is true if the zero charge is in the set of
charges associated with that potential term.

That is, if there is some choice of representations present in the theory which will allow that
potential term via symmetry.

-/

/-- The charges of representations `x : Charges` allow a potential term `T : PotentialTerm`
if the zero charge is in the set of charges associated with that potential term. -/
def AllowsTerm (x : ChargeSpectrum 𝓩) (T : PotentialTerm) : Prop := 0 ∈ ofPotentialTerm x T

/-!

### A.1. Decidability of `AllowsTerm`

We define the decidability of `AllowsTerm` through `ofPotentialTerm'` rather than
`ofPotentialTerm` due to the speed of the former compared to the latter.

-/

lemma allowsTerm_iff_zero_mem_ofPotentialTerm' [DecidableEq 𝓩]
    {x : ChargeSpectrum 𝓩} {T : PotentialTerm} :
    x.AllowsTerm T ↔ 0 ∈ x.ofPotentialTerm' T := by
  rw [AllowsTerm]
  exact mem_ofPotentialTerm_iff_mem_ofPotentialTerm

instance [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) (T : PotentialTerm) : Decidable (x.AllowsTerm T) :=
  decidable_of_iff (0 ∈ x.ofPotentialTerm' T) allowsTerm_iff_zero_mem_ofPotentialTerm'.symm

/-!

### A.2. Monotonicity of `AllowsTerm`

The proposition `AllowsTerm` is monotone in its charge spectrum argument.
That is if a charge spectrum `y` is a subset of a charge spectrum `x`,
and `y` allows a potential term `T`, then `x` also allows that potential term `T`.

-/

lemma allowsTerm_mono {T : PotentialTerm} {y x : ChargeSpectrum 𝓩}
    (h : y ⊆ x) (hy : y.AllowsTerm T) : x.AllowsTerm T := ofPotentialTerm_mono h T hy

/-!

## B. Forms of charges which allow potential terms

We now define the function `allowsTermForm` which for each potential term `T`
and three charges `a`, `b`, and `c` returns a charge spectrum which allows the term `T`.

These charges are in a minimal form, in the sense that any charge spectrum allowing `T`
has a subset of this form.

-/

variable [DecidableEq 𝓩]

/-- A element of `Charges` from three integers `a b c : ℤ` for a given potential term `T`.
  Defined such that `allowsTermForm a b c T` always allows the potential term `T`,
  and if any over charge `x` allows `T` then it is due to a subset of the form
  `allowsTermForm a b c T`. -/
def allowsTermForm (a b c : 𝓩) : (T : PotentialTerm) → ChargeSpectrum 𝓩
  | .μ => ⟨some a, some a, ∅, ∅⟩
  | .β => ⟨none, some a, {a}, ∅⟩
  | .Λ => ⟨none, none, {a, b}, {- a - b}⟩
  | .W1 => ⟨none, none, {- a - b - c}, {a, b, c}⟩
  | .W2 => ⟨some (- a - b - c), none, ∅, {a, b, c}⟩
  | .W3 => ⟨none, some (- a), {b, - b - 2 • a}, ∅⟩
  | .W4 => ⟨some (- c - 2 • b), some (- b), {c}, ∅⟩
  | .K1 => ⟨none, none, {-a}, {b, - a - b}⟩
  | .K2 => ⟨some a, some b, ∅, {- a - b}⟩
  | .topYukawa => ⟨none, some (-a), ∅, {b, - a - b}⟩
  | .bottomYukawa => ⟨some a, none, {b}, {- a - b}⟩

/-!

### B.1. `allowsTermForm` allows the potential term

Any charge spectrum of the form `allowsTermForm a b c T` allows the potential term `T`.

-/

/-- The charge spectrum `allowsTermForm a b c T` allows the potential term `T`. -/
lemma allowsTermForm_allowsTerm {a b c : 𝓩} {T : PotentialTerm} :
    (allowsTermForm a b c T).AllowsTerm T := by
  simp [AllowsTerm, ofPotentialTerm, allowsTermForm]
  cases T
  all_goals
    simp [PotentialTerm.toFieldLabel, ofFieldLabel]
  case Λ =>
    use a, b
    simp
  case W3 =>
    use b, -b - 2 • a
    simp only [true_or, or_true, and_self, true_and]
    abel
  case K1 =>
    use b, - a - b
    simp
  case topYukawa =>
    use b, - a - b
    simp
  case W1 =>
    use a, b, c
    simp only [true_or, or_true, and_self, true_and]
    abel
  case W2 =>
    use a, b, c
    simp only [true_or, or_true, and_self, true_and]
    abel
  all_goals abel

lemma allowsTerm_of_eq_allowsTermForm {T : PotentialTerm}
    (x : ChargeSpectrum 𝓩) (h : ∃ a b c, x = allowsTermForm a b c T) :
    x.AllowsTerm T := by
  obtain ⟨a, b, c, rfl⟩ := h
  exact allowsTermForm_allowsTerm

/-!

### B.2. Subset relations for `allowsTermForm`

For any potential term `T` except for `W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ` or `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd`,
a charge spectrum `allowsTermForm a b c T` is a subset of another charge spectrum
`allowsTermForm a' b' c' T` if they are equal.

The reason this does not work for `W1` an `W2` is due to the presence of three
charges in the 10d representation.

-/

open PotentialTerm in
lemma allowsTermForm_eq_of_subset {a b c a' b' c' : 𝓩} {T : PotentialTerm}
    (h : allowsTermForm a b c T ⊆ allowsTermForm a' b' c' T) (hT : T ≠ W1 ∧ T ≠ W2) :
    allowsTermForm a b c T = allowsTermForm a' b' c' T := by
  cases T
  case' W1 | W2 => simp at hT
  all_goals
    rw [subset_def] at h
    simp [allowsTermForm] at h ⊢
  case' μ =>
    subst h
    rfl
  case' β =>
    subst h
    rfl
  case' K2 =>
    obtain ⟨rfl, rfl, h2⟩ := h
    simp
  case' W4 =>
    obtain ⟨h2, rfl, rfl⟩ := h
    simp
  case' bottomYukawa =>
    obtain ⟨rfl, rfl, h2⟩ := h
    simp
  case' Λ => obtain ⟨h2, h1⟩ := h
  case' K1 => obtain ⟨rfl, h2⟩ := h
  case' topYukawa => obtain ⟨rfl, h2⟩ := h
  case' W3 => obtain ⟨rfl, h2⟩ := h
  case' topYukawa | W3 | K1 | Λ =>
    rw [Finset.insert_subset_iff] at h2
    simp at h2
    obtain ⟨rfl | rfl, h1 | h2⟩ := h2
    all_goals simp_all [Finset.pair_comm]

/-!

### B.3. Card of `allowsTermForm`

The cardinality of the charge spectrum `allowsTermForm a b c T` is always
less than or equal to the degree of the potential term `T`.

-/

lemma allowsTermForm_card_le_degree {a b c : 𝓩} {T : PotentialTerm} :
    (allowsTermForm a b c T).card ≤ T.degree := by
  cases T
  all_goals
    simp [allowsTermForm, PotentialTerm.toFieldLabel, card, PotentialTerm.degree]
  case' Λ =>
    have h1 : Finset.card {a, b} ≤ 2 := Finset.card_le_two
    omega
  case' W3 =>
    have h1 : Finset.card {b, -b - 2 • a} ≤ 2 := Finset.card_le_two
    omega
  case' K1 =>
    have h1 : Finset.card {b, -a - b} ≤ 2 := Finset.card_le_two
    omega
  case' topYukawa =>
    have h1 : Finset.card {b, -a - b} ≤ 2 := Finset.card_le_two
    omega
  all_goals
    have h1 : Finset.card {a, b, c} ≤ 3 := Finset.card_le_three
    omega

/-!

### B.4. If `AllowsTerm` then subset equal to `allowsTermForm a b c T`

We now show one of the more important properties of `allowsTermForm`.
Namely that if a charge spectrum `x`
allows a potential term `T`, then there exists charges `a`, `b`, and `c` such that
`allowsTermForm a b c T ⊆ x`.

The proof of this result is rather long, relying on case-by-case analysis of each
of the potential terms of interest.

-/

lemma allowsTermForm_subset_allowsTerm_of_allowsTerm {T : PotentialTerm} {x : ChargeSpectrum 𝓩}
    (h : x.AllowsTerm T) :
    ∃ a b c, allowsTermForm a b c T ⊆ x ∧ (allowsTermForm a b c T).AllowsTerm T := by
  simp [AllowsTerm, ofPotentialTerm] at h
  cases T
  all_goals
    simp [PotentialTerm.toFieldLabel, -existsAndEq] at h
    obtain ⟨f1, f2, ⟨⟨f3, f4, ⟨h3, f4_mem⟩, rfl⟩, f2_mem⟩, f1_add_f2_eq_zero⟩ := h
  case' μ | β => obtain ⟨rfl⟩ := h3
  case' Λ | W1 | W2 | W3 | W4 | K1 | K2 | topYukawa | bottomYukawa =>
    obtain ⟨f5, f6, ⟨h4, f6_mem⟩, rfl⟩ := h3
  case' Λ | K1 | K2 | topYukawa | bottomYukawa => obtain ⟨rfl⟩ := h4
  case' W1 | W2 | W3 | W4 => obtain ⟨f7, f8, ⟨rfl, f8_mem⟩, rfl⟩ := h4
  -- The cases which are present
  case' μ => use f4, (f2), 0
  case' β => use (- f4), f2, 0
  case' Λ => use f4, f6, f2
  case' W1 => use f4, f6, f8
  case' W2 => use f4, f6, f8
  case' W3 => use (f2), f6, f8
  case' W4 => use f6, (f2), f8
  case' K1 => use f2, f4, f6
  case' K2 => use f4, f6, f2
  case' topYukawa => use (f2), f4, f6
  case' bottomYukawa => use f2, f4, f6
  all_goals
    rw [subset_def]
    simp_all [ofFieldLabel, Finset.insert_subset_iff, allowsTermForm]
  all_goals
    simp [AllowsTerm, ofPotentialTerm, PotentialTerm.toFieldLabel, ofFieldLabel]
  -- Replacements of equalities
  case' W1 | W2 =>
    have hf2 : f2 = -f4 - f6 - f8 := by
      rw [← sub_zero f2, ← f1_add_f2_eq_zero]
      abel
    subst hf2
    simp_all
  case β =>
    have hf2 : f4 = - f2 := by
      rw [← sub_zero f2, ← f1_add_f2_eq_zero]
      abel
    subst hf2
    simp_all
  case K2 =>
    have hf2 : f2 = - f4 - f6 := by
      rw [← sub_zero f2, ← f1_add_f2_eq_zero]
      abel
    subst hf2
    simp_all
  case' Λ =>
    have hf2 : f2 = -f4 - f6 := by
      rw [← sub_zero f2, ← f1_add_f2_eq_zero]
      abel
    subst hf2
    simp_all
  case' W3 =>
    subst f4_mem
    have hf8 : f8 = - f6 - 2 • f4 := by
      rw [← sub_zero f8, ← f1_add_f2_eq_zero]
      abel
    subst hf8
    simp_all
  case' bottomYukawa =>
    have hf6 : f6 = - f2 - f4 := by
      rw [← sub_zero f2, ← f1_add_f2_eq_zero]
      abel
    subst hf6
    simp_all
  -- AllowsTerm
  case W3 =>
    use (- f6 - 2 • f4), f6
    simpa using f1_add_f2_eq_zero
  case W1 | W2 =>
    use f4, f6, f8
    simp only [true_or, or_true, and_self, true_and]
    abel
  case K1 =>
    have hf6 : f6 = - f2 - f4 := by
      rw [← sub_zero f2, ← f1_add_f2_eq_zero]
      abel
    subst hf6
    simp_all
    use (-f2 - f4), f4
    simp
  case' topYukawa =>
    have hf2 : f2 = - f4 - f6 := by
      rw [← sub_zero f2, ← f1_add_f2_eq_zero]
      abel
    subst hf2
    simp_all
  case topYukawa | Λ =>
    use f6, f4
    simp only [or_true, true_or, and_self, true_and]
    abel
  case W4 =>
    apply And.intro
    · rw [← sub_zero f8, ← f1_add_f2_eq_zero]
      abel
    · abel
  case μ =>
    rw [← sub_zero f2, ← f1_add_f2_eq_zero]
    abel

/-!

### B.5. `AllowsTerm` if and only if subset equal to `allowsTermForm a b c T`

We now lift the previous result to show that a charge spectrum `x`
allows a potential term `T` if and only if there exists charges `a`, `b`, and `c` such that
`allowsTermForm a b c T ⊆ x`.

Given what has already been shown, this result is now trivial.

-/
lemma allowsTerm_iff_subset_allowsTermForm {T : PotentialTerm} {x : ChargeSpectrum 𝓩} :
    x.AllowsTerm T ↔ ∃ a b c, allowsTermForm a b c T ⊆ x := by
  constructor
  · intro h
    obtain ⟨a, b, c, h1, h2⟩ := allowsTermForm_subset_allowsTerm_of_allowsTerm h
    use a, b, c
  · intro h
    obtain ⟨a, b, c, h1⟩ := h
    apply allowsTerm_mono h1 allowsTermForm_allowsTerm

/-!

### B.6. Cardinality of subset allowing potential term

We show that if a charge spectrum `x` allows a potential term `T`,
then there exists a subset of `x` which allows `T` and whose cardinality is less than or equal
to the degree of `T`.

This follows from the fact that `allowsTermForm a b c T` always has cardinality
less than or equal to the degree of `T`.

-/

lemma subset_card_le_degree_allowsTerm_of_allowsTerm {T : PotentialTerm} {x : ChargeSpectrum 𝓩}
    (h : x.AllowsTerm T) : ∃ y ∈ x.powerset, y.card ≤ T.degree ∧ y.AllowsTerm T := by
  obtain ⟨a, b, c, h1, h2⟩ := allowsTermForm_subset_allowsTerm_of_allowsTerm h
  use allowsTermForm a b c T
  simp_all
  exact allowsTermForm_card_le_degree

/-!

## C. Allowing a potential term by insertion of a `Q5` charge

We now study what happens when we add a charge `q5` to the `Q5` charges of a charge spectrum `x`.
We define the proposition `AllowsTermQ5 x q5 T` which is true if adding the charge `q5`
to the `Q5` charges of `x` allows the potential term `T` due to the addition of that charge.

We prove a number of properties of this proposition, including its relation
to `AllowsTerm` and its decidability.

-/

/-- The proposition for which says, given a charge `x` adding a charge `q5` permits the
  existence of a potential term `T` due to the addition of that charge. -/
def AllowsTermQ5 [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) (q5 : 𝓩) (T : PotentialTerm) : Prop :=
  match T with
  | .μ => false
  | .β =>
    match x with
    | ⟨_, some qHu, _, _⟩ => q5 = qHu
    | _ => false
  | .Λ => (0 : 𝓩) ∈ ((insert q5 x.Q5).product x.Q10).val.map (fun (q1, q2) => (q1 + q5 + q2))
  | .W4 =>
    match x with
    | ⟨some qHd, some qHu, _, _⟩ => q5 + qHd - qHu - qHu = 0
    | _ => false
  | .K1 => (0 : 𝓩) ∈ (x.Q10.product x.Q10).val.map (fun (y, z) => -q5 + y + z)
  | .W1 => (0 : 𝓩) ∈ (x.Q10.product (x.Q10.product x.Q10)).val.map
    (fun (q1, q2, q3) => q5 + q1 + q2 + q3)
  | .W2 => false
  | .bottomYukawa =>
    match x with
    | ⟨none, _, _, _⟩ => false
    | ⟨some qHd, _, _, _⟩ => (0 : 𝓩) ∈ x.Q10.val.map (fun y => y + q5 + qHd)
  | .topYukawa => false
  | .K2 => false
  | .W3 =>
    match x with
    | ⟨_, some qHu, _, _⟩ =>
      (0 : 𝓩) ∈ (insert q5 x.Q5).val.map (fun y => y + q5 - qHu - qHu)
    | _ => false

/-!

### C.1. Decidability of `AllowsTermQ5`

We show that if the type `𝓩` has decidable equality, then the proposition
`AllowsTermQ5 x q5 T` is decidable for any charge spectrum `x`, charge `q5`, and
potential term `T`.

-/
instance [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) (q5 : 𝓩) (T : PotentialTerm) :
    Decidable (AllowsTermQ5 x q5 T) :=
  match T with
  | .μ => isFalse fun h => by simp [AllowsTermQ5] at h
  | .β =>
    match x with
    | ⟨_, some qHu, _, _⟩ => decidable_of_iff (q5 = qHu) (by simp [AllowsTermQ5])
    | ⟨_, none, _, _⟩ => isFalse fun h => by simp [AllowsTermQ5] at h
  | .Λ =>
    decidable_of_iff ((0 : 𝓩) ∈ ((insert q5 x.Q5).product x.Q10).val.map
      (fun (q1, q2) => (q1 + q5 + q2))) (by simp [AllowsTermQ5])
  | .W4 =>
    match x with
    | ⟨some qHd, some qHu, _, _⟩ => decidable_of_iff (q5 + qHd - qHu - qHu = 0)
      (by simp [AllowsTermQ5])
    | ⟨some qHd, none, _, _⟩ => isFalse fun h => by simp [AllowsTermQ5] at h
    | ⟨none, _, _, _⟩ => isFalse fun h => by simp [AllowsTermQ5] at h
  | .K1 =>
    decidable_of_iff ((0 : 𝓩) ∈ (x.Q10.product x.Q10).val.map (fun (y, z) => -q5 + y + z))
      (by simp [AllowsTermQ5])
  | .W1 =>
    decidable_of_iff ((0 : 𝓩) ∈ (x.Q10.product (x.Q10.product x.Q10)).val.map
    (fun (q1, q2, q3) => q5 + q1 + q2 + q3)) (by rfl)
  | .W2 => isFalse fun h => by simp [AllowsTermQ5] at h
  | .bottomYukawa =>
    match x with
    | ⟨none, _, _, _⟩ => isFalse fun h => by simp [AllowsTermQ5] at h
    | ⟨some qHd, _, _, Q10⟩ => decidable_of_iff ((0 : 𝓩) ∈ Q10.val.map (fun y => y + q5 + qHd))
      (by simp [AllowsTermQ5])
  | .topYukawa => isFalse fun h => by simp [AllowsTermQ5] at h
  | .K2 => isFalse fun h => by simp [AllowsTermQ5] at h
  | .W3 =>
    match x with
    | ⟨_, some qHu, Q5, _⟩ => decidable_of_iff
      ((0 : 𝓩) ∈ (insert q5 Q5).val.map (fun y => y + q5 - qHu - qHu))
      (by simp [AllowsTermQ5])
    | ⟨_, none, _, _⟩ => isFalse fun h => by simp [AllowsTermQ5] at h

/-!

### C.2. AllowsTermQ5 or AllowsTerm from AllowsTerm with inserted of `Q5` charge

We show that if a charge spectrum `x` with an inserted charge `q5`
allows a potential term `T`, then either the charge spectrum `x`
allows that potential term `T` *due to* the addition of that charge,
or the charge spectrum `x` already allows that potential term `T`.

-/

lemma allowsTermQ5_or_allowsTerm_of_allowsTerm_insertQ5 {qHd qHu : Option 𝓩}
    {Q5 Q10: Finset 𝓩} {q5 : 𝓩} (T : PotentialTerm)
    (h : AllowsTerm ⟨qHd, qHu, insert q5 Q5, Q10⟩ T) :
    AllowsTermQ5 ⟨qHd, qHu, Q5, Q10⟩ q5 T ∨
    AllowsTerm ⟨qHd, qHu, Q5, Q10⟩ T := by
  rcases T
  all_goals
    simp [allowsTerm_iff_zero_mem_ofPotentialTerm', ofPotentialTerm', AllowsTermQ5] at h ⊢
  · exact h
  · match qHu with
    | some qHu =>
      simp at h
      simp only [Multiset.mem_map, Finset.mem_val]
      convert h using 1
      rw [neg_add_eq_zero, eq_comm]
    | none => simp at h
  · obtain ⟨a1, a2, a3, ⟨h1, h2, h3⟩, hsum⟩ := h
    rcases h1 with h1 | h1
    · subst h1
      left
      rcases h2 with h2 | h2
      · use a2, a3
        simp_all
      · use a2, a3
        simp_all
        rw [← hsum]
        abel
    · rcases h2 with h2 | h2
      · left
        use a1, a3
        simp_all
      · right
        use a1, a2, a3
  · obtain ⟨a1, a2, a3, a4, ⟨h1, h2, h3, h4⟩, hsum⟩ := h
    rcases h1 with h1 | h1
    · left
      use a2, a3, a4
      simp_all
    · right
      use a1, a2, a3, a4
  · simp_all
  · match qHu with
    | some qHu =>
      simp at h
      obtain ⟨a1, a2, ⟨h1, h2⟩, hsum⟩ := h
      rcases h1 with h1 | h1
      · subst h1
        left
        rcases h2 with h2 | h2
        · left
          subst h2
          rw [← hsum]
          abel
        · right
          use a2
          simp_all
          rw [← hsum]
          abel
      · rcases h2 with h2 | h2
        · left
          right
          use a1
          simp_all
          rw [← hsum]
          abel
        · right
          rw [@Multiset.mem_map]
          simp only [Multiset.mem_product, Finset.mem_val, Prod.exists]
          use a1, a2
    | none => simp at h
  · match qHd, qHu with
    | some qHd, some qHu =>
      simp_all
      convert h using 1
      constructor
      all_goals
      · intro h
        rw [← h]
        abel
    | none, _ => simp at h
    | some x, none => simp at h
  · obtain ⟨a1, a2, a3, ⟨h1, h2, h3⟩, hsum⟩ := h
    rcases h1 with h1 | h1
    · left
      use a2, a3
      simp_all
    · right
      use a1, a2, a3
  · simp_all
  · simp_all
  · match qHd with
    | none => simp at h
    | some qHd =>
      simp_all
      obtain ⟨a1, a2, ⟨h1, h2⟩, hsum⟩ := h
      rcases h1 with h1 | h1
      · subst h1
        left
        use a2
        simp_all
        rw [← hsum]
        abel
      · right
        use a1, a2

/-!

### C.3. AllowsTerm with inserted of `Q5` charge from AllowsTermQ5

We show that if a charge spectrum `x` allows a potential term `T`
*due to* the addition of a charge `q5`, then the charge spectrum `x` with that charge inserted
allows that potential term `T`.

-/
lemma allowsTerm_insertQ5_of_allowsTermQ5 {qHd qHu : Option 𝓩}
    {Q5 Q10: Finset 𝓩} {q5 : 𝓩} (T : PotentialTerm)
    (h : AllowsTermQ5 ⟨qHd, qHu, Q5, Q10⟩ q5 T) :
    AllowsTerm ⟨qHd, qHu, insert q5 Q5, Q10⟩ T := by
  rcases T
  all_goals
    simp [AllowsTermQ5] at h
  all_goals
    simp [allowsTerm_iff_zero_mem_ofPotentialTerm', ofPotentialTerm']
  · match qHu with
    | some qHu =>
      simp at h
      subst h
      simp
    | none => simp at h
  · obtain ⟨q1, q2, ⟨h1, h2⟩, hsum⟩ := h
    use q1, q5, q2
    simp_all
  · obtain ⟨q1, q2, q3, h3, hsum⟩ := h
    use q5, q1, q2, q3
    simp_all
  · match qHu with
    | some qHu =>
      simp at h
      simp only [Multiset.mem_map, Multiset.mem_product, Multiset.mem_ndinsert, Finset.mem_val,
        Prod.exists]
      by_cases h' : q5 + q5 - qHu - qHu = 0
      · use q5, q5
        simp only [true_or, and_self, true_and]
        rw [← h']
        abel
      · simp_all
        obtain ⟨q1, hsum⟩ := h
        use q1, q5
        simp_all
        rw [← hsum.2]
        abel
    | none => simp at h
  · match qHd, qHu with
    | some qHd, some qHu =>
      simp_all
      left
      rw [← h]
      abel
    | none, _ => simp at h
    | some x, none => simp at h
  · obtain ⟨q1, q2, ⟨h1, h2⟩, hsum⟩ := h
    use q5, q1, q2
    simp_all
  · match qHd with
    | none => simp at h
    | some qHd =>
      simp at h
      obtain ⟨q1, h1, hsum⟩ := h
      simp only [Multiset.mem_map, Multiset.mem_product, Multiset.mem_ndinsert, Finset.mem_val,
        Prod.exists]
      use q5, q1
      simp_all
      rw [← hsum]
      abel

/-!

### C.4. AllowsTerm with inserted of `Q5` charge iff AllowsTermQ5 or AllowsTerm

We show that the charge spectrum `x` with that charge inserted
allows that potential term `T` if and only if either the charge spectrum `x`
allows that potential term `T` *due to* the addition of that charge,
or the charge spectrum `x` already allows that potential term `T`.

-/

lemma allowsTerm_insertQ5_iff_allowsTermQ5 {qHd qHu : Option 𝓩}
    {Q5 Q10: Finset 𝓩} {q5 : 𝓩} (T : PotentialTerm) :
    AllowsTerm ⟨qHd, qHu, insert q5 Q5, Q10⟩ T ↔
    AllowsTermQ5 ⟨qHd, qHu, Q5, Q10⟩ q5 T ∨
    AllowsTerm ⟨qHd, qHu, Q5, Q10⟩ T := by
  constructor
  · exact allowsTermQ5_or_allowsTerm_of_allowsTerm_insertQ5 T
  · intro h
    rcases h with h | h
    · exact allowsTerm_insertQ5_of_allowsTermQ5 T h
    · apply allowsTerm_mono _ h
      simp [subset_def]

/-!

## D. Allowing a potential term by insertion of a `Q10` charge

We now replicate the previous section, but for the insertion of a `Q10` charge, rather
than a `Q5` charge.

We study what happens when we add a charge `q10` to the `Q10` charges of a charge spectrum `x`.
We define the proposition `AllowsTermQ10 x q10 T` which is true if adding the charge `q10`
to the `Q10` charges of `x` allows the potential term `T` due to the addition of that charge.

We prove a number of properties of this proposition, including its relation
to `AllowsTerm` and its decidability.

-/

/-- The proposition for which says, given a charge `x` adding a charge `q5` permits the
  existence of a potential term `T` due to the addition of that charge. -/
def AllowsTermQ10 [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) (q10 : 𝓩) (T : PotentialTerm) : Prop :=
  match T with
  | .μ => false
  | .β => false
  | .Λ => (0 : 𝓩) ∈ (x.Q5.product x.Q5).val.map (fun (y, z) => y + z + q10)
  | .W4 => false
  | .K1 => (0 : 𝓩) ∈ (x.Q5.product (insert q10 x.Q10)).val.map (fun (q5, q2) => -q5 + q2+ q10)
  | .W1 => (0 : 𝓩) ∈ (x.Q5.product ((insert q10 x.Q10).product (insert q10 x.Q10))).val.map
    (fun (q5, q2, q3) => q5 + q2 + q3 + q10)
  | .W2 =>
    match x with
    | ⟨some qHd, _, _, _⟩ => (0 : 𝓩) ∈
      (((insert q10 x.Q10).product (insert q10 x.Q10))).val.map
      (fun (q2, q3) => qHd + q2 + q3 + q10)
    | _ => false
  | .bottomYukawa =>
    match x with
    | ⟨none, _, _, _⟩ => false
    | ⟨some qHd, _, _, _⟩ => (0 : 𝓩) ∈ x.Q5.val.map (fun y => q10 + y + qHd)
  | .topYukawa =>
    match x with
    | ⟨_, some qHu, _, _⟩ => (0 : 𝓩) ∈ (insert q10 x.Q10).val.map (fun y => q10 + y - qHu)
    | _ => false
  | .K2 =>
    match x with
    | ⟨some qHd, some qHu, _, _⟩ => qHd + qHu + q10 = 0
    | _ => false
  | .W3 => false

/-!

### D.1. Decidability of `AllowsTermQ5`

We show that if the type `𝓩` has decidable equality, then the proposition
`AllowsTermQ10 x q10 T` is decidable for any charge spectrum `x`, charge `q10`, and
potential term `T`.

-/

instance [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) (q10 : 𝓩) (T : PotentialTerm) :
    Decidable (AllowsTermQ10 x q10 T) :=
  match T with
  | .μ => isFalse fun h => by simp [AllowsTermQ10] at h
  | .β => isFalse fun h => by simp [AllowsTermQ10] at h
  | .Λ =>
    decidable_of_iff ((0 : 𝓩) ∈ (x.Q5.product x.Q5).val.map (fun (y, z) => y + z + q10))
      (by simp [AllowsTermQ10])
  | .W4 => isFalse fun h => by simp [AllowsTermQ10] at h
  | .K1 =>
    decidable_of_iff ((0 : 𝓩) ∈
      (x.Q5.product (insert q10 x.Q10)).val.map (fun (q5, q2) => -q5 + q2 + q10))
      (by simp [AllowsTermQ10])
  | .W1 =>
    decidable_of_iff ((0 : 𝓩) ∈
    (x.Q5.product ((insert q10 x.Q10).product (insert q10 x.Q10))).val.map
    (fun (q5, q2, q3) => q5 + q2 + q3 + q10)) (by rfl)
  | .W2 =>
    match x with
    | ⟨some qHd, _, _, Q10⟩ => decidable_of_iff ((0 : 𝓩) ∈
      (((insert q10 Q10).product (insert q10 Q10))).val.map
      (fun (q2, q3) => qHd + q2 + q3 + q10)) (by simp [AllowsTermQ10])
    | ⟨none, _, _, _⟩ => isFalse fun h => by simp [AllowsTermQ10] at h
  | .bottomYukawa =>
    match x with
    | ⟨none, _, _, _⟩ => isFalse fun h => by simp [AllowsTermQ10] at h
    | ⟨some qHd, _, Q5, _⟩ => decidable_of_iff ((0 : 𝓩) ∈ Q5.val.map (fun y => q10 + y + qHd))
      (by simp [AllowsTermQ10])
  | .topYukawa =>
    match x with
    | ⟨_, some qHu, _, Q10⟩ => decidable_of_iff
      ((0 : 𝓩) ∈ (insert q10 Q10).val.map (fun y => q10 + y - qHu))
      (by simp [AllowsTermQ10])
    | ⟨_, none, _, _⟩ => isFalse fun h => by simp [AllowsTermQ10] at h
  | .K2 =>
    match x with
    | ⟨some qHd, some qHu, _, _⟩ => decidable_of_iff (qHd + qHu + q10 = 0) (by simp [AllowsTermQ10])
    | ⟨some qHd, none, _, _⟩ => isFalse fun h => by simp [AllowsTermQ10] at h
    | ⟨none, _, _, _⟩ => isFalse fun h => by simp [AllowsTermQ10] at h
  | .W3 => isFalse fun h => by simp [AllowsTermQ10] at h

/-!

### D.2. AllowsTermQ10 or AllowsTerm from AllowsTerm with inserted of `Q10` charge

We show that if a charge spectrum `x` with an inserted charge `q10`
allows a potential term `T`, then either the charge spectrum `x`
allows that potential term `T` *due to* the addition of that charge,
or the charge spectrum `x` already allows that potential term `T`.

-/

lemma allowsTermQ10_or_allowsTerm_of_allowsTerm_insertQ10 {qHd qHu : Option 𝓩}
    {Q5 Q10: Finset 𝓩} {q10 : 𝓩} (T : PotentialTerm)
    (h : AllowsTerm ⟨qHd, qHu, Q5, insert q10 Q10⟩ T) :
    AllowsTermQ10 ⟨qHd, qHu, Q5, Q10⟩ q10 T ∨
    AllowsTerm ⟨qHd, qHu, Q5, Q10⟩ T := by
  rcases T
  all_goals
    simp [allowsTerm_iff_zero_mem_ofPotentialTerm', ofPotentialTerm', AllowsTermQ10] at h ⊢
  · simp_all
  · simp_all
  · obtain ⟨a1, a2, a3, ⟨h1, h2, h3⟩, hsum⟩ := h
    rcases h3 with h3 | h3
    · subst h3
      left
      use a1, a2
    · right
      use a1, a2, a3
  · obtain ⟨a1, a2, a3, a4, ⟨h1, h2, h3, h4⟩, hsum⟩ := h
    rcases h2 with h2 | h2
    · subst h2
      left
      use a1, a3, a4
      simp_all
      rw [← hsum]
      abel
    rcases h3 with h3 | h3
    · subst h3
      left
      use a1, a2, a4
      simp_all
      rw [← hsum]
      abel
    rcases h4 with h4 | h4
    · subst h4
      left
      use a1, a2, a3
      simp_all
    right
    use a1, a2, a3, a4
  · match qHd with
    | none => simp at h
    | some qHd =>
    simp_all
    obtain ⟨a1, a2, a3, ⟨h1, h2, h3⟩, hsum⟩ := h
    rcases h1 with h1 | h1
    · subst h1
      left
      use a2, a3
      simp_all
      rw [← hsum]
      abel
    rcases h2 with h2 | h2
    · subst h2
      left
      use a1, a3
      simp_all
      rw [← hsum]
      abel
    rcases h3 with h3 | h3
    · subst h3
      left
      use a1, a2
      simp_all
    right
    use a1, a2, a3
  · match qHu with
    | none => simp at h
    | some qHu => simp_all
  · match qHd, qHu with
    | none, _ => simp at h
    | some x, none => simp at h
    | some qHd, some qHu => simp_all
  · obtain ⟨a1, a2, a3, ⟨h1, h2, h3⟩, hsum⟩ := h
    rcases h2 with h2 | h2
    · left
      use a1, a3
      simp_all
      rw [← hsum]
      abel
    rcases h3 with h3 | h3
    · left
      use a1, a2
      simp_all
    right
    use a1, a2, a3
  · match qHd, qHu with
    | none, _ => simp at h
    | some x, none => simp at h
    | some qHd, some qHu => simp_all
  · match qHu with
    | none => simp at h
    | some qHu =>
    simp at h
    obtain ⟨a1, a2, ⟨h1, h2⟩, hsum⟩ := h
    rcases h1 with h1 | h1
    · subst h1
      left
      rcases h2 with h2 | h2
      · subst h2
        left
        rw [← hsum]
        abel
      · right
        use a2
        simp_all
        rw [← hsum]
        abel
    rcases h2 with h2 | h2
    · subst h2
      left; right
      use a1
      simp_all
      rw [← hsum]
      abel
    · right
      simp only [Multiset.mem_map, Multiset.mem_product, Finset.mem_val, Prod.exists]
      use a1, a2
  · match qHd with
    | none => simp at h
    | some qHd =>
    simp_all
    obtain ⟨a1, a2, ⟨h1, h2⟩, hsum⟩ := h
    rcases h2 with h2 | h2
    · subst h2
      left
      use a1
      simp_all
      rw [← hsum]
      abel
    right
    use a1, a2

/-!

### D.3. AllowsTerm with inserted of `Q10` charge from AllowsTermQ5

We show that if a charge spectrum `x` allows a potential term `T`
*due to* the addition of a charge `q10`, then the charge spectrum `x` with that charge inserted
allows that potential term `T`.

-/

lemma allowsTerm_insertQ10_of_allowsTermQ10 {qHd qHu : Option 𝓩}
    {Q5 Q10: Finset 𝓩} {q10 : 𝓩} (T : PotentialTerm)
    (h : AllowsTermQ10 ⟨qHd, qHu, Q5, Q10⟩ q10 T) :
    AllowsTerm ⟨qHd, qHu, Q5, insert q10 Q10⟩ T := by
  rcases T
  all_goals
    simp [AllowsTermQ10] at h
  all_goals
    simp [allowsTerm_iff_zero_mem_ofPotentialTerm', ofPotentialTerm']
  · obtain ⟨a1, a2, ⟨h1, h2⟩, hsum⟩ := h
    use a1, a2, q10
    simp_all
  · obtain ⟨a1, a2, a3, ⟨h1, h2, h3⟩, hsum⟩ := h
    use a1, a2, a3, q10
    simp_all
  · match qHd with
    | none => simp at h
    | some qHd =>
      simp at h ⊢
      obtain ⟨a1, a2, ⟨h1, h2⟩, hsum⟩ := h
      use a1, a2, q10
      simp_all
  · obtain ⟨a1, a2, ⟨h1, h2⟩, hsum⟩ := h
    use a1, a2, q10
    simp_all
  · match qHd, qHu with
    | none, _ => simp at h
    | some x, none => simp at h
    | some qHd, some qHu => simp_all
  · match qHu with
    | none => simp at h
    | some qHu =>
      simp at h ⊢
      rcases h with h | h
      · use q10, q10
        rw [← h]
        simp only [true_or, and_self, true_and]
        abel
      · obtain ⟨a1, h1, hsum⟩ := h
        use a1, q10
        simp_all
        rw [← hsum]
        abel
  · match qHd with
    | none => simp at h
    | some qHd =>
      simp at h ⊢
      obtain ⟨a1, h1, hsum⟩ := h
      use a1, q10
      simp_all
      rw [← hsum]
      abel
/-!

### D.4. AllowsTerm with inserted of `Q10` charge iff AllowsTermQ10 or AllowsTerm

We show that the charge spectrum `x` with that charge inserted
allows that potential term `T` if and only if either the charge spectrum `x`
allows that potential term `T` *due to* the addition of that charge,
or the charge spectrum `x` already allows that potential term `T`.

-/

lemma allowsTerm_insertQ10_iff_allowsTermQ10 {qHd qHu : Option 𝓩}
    {Q5 Q10: Finset 𝓩} {q10 : 𝓩} (T : PotentialTerm) :
    AllowsTerm ⟨qHd, qHu, Q5, insert q10 Q10⟩ T ↔
    AllowsTermQ10 ⟨qHd, qHu, Q5, Q10⟩ q10 T ∨
    AllowsTerm ⟨qHd, qHu, Q5, Q10⟩ T := by
  constructor
  · exact allowsTermQ10_or_allowsTerm_of_allowsTerm_insertQ10 T
  · intro h
    rcases h with h | h
    · exact allowsTerm_insertQ10_of_allowsTermQ10 T h
    · apply allowsTerm_mono _ h
      simp [subset_def]

end ChargeSpectrum

end SU5
end SuperSymmetry
