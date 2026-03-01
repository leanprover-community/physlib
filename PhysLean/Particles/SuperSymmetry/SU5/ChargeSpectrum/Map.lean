/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.Yukawa
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.Completions
/-!

# Mapping charge spectra values

## i. Overview

In this module we define a function `map` which takes an additive monoid homomorphism
`f : 𝓩 →+ 𝓩1` and a charge spectra `x : ChargeSpectrum 𝓩`, and returns the charge
`x.map f : ChargeSpectrum 𝓩1` obtained by mapping the elements of `x` by `f`.

There are various properties which are preserved under this mapping:
- Anomaly cancellation.
- The presence of a specific term in the potential.
- Being complete.

There are some properties which are reflected under this mapping:
- Not being pheno-constrained.
- Not regenerating dangerous Yukawa terms at a given level.

We define the preimage of this mapping within a subset `ofFinset S5 S10` of `Charges 𝓩` in
a computationally efficient way.

## ii. Key results

- `map` : The mapping of charge spectra under an additive monoid homomorphism.
- `map_allowsTerm` : If a charge spectrum allows a potential term, then so does its mapping.
- `map_isPhenoConstrained` : If a charge spectrum is pheno-constrained, then so is its mapping.
- `map_isComplete_iff` : A charge spectrum is complete if and only if its mapping is complete.
- `map_yukawaGeneratesDangerousAtLevel` : A charge spectrum regenerates dangerous Yukawa terms
  at a given level then so does its mapping.
- `preimageOfFinset` : The preimage of a charge spectrum in `ofFinset S5 S10`
  under a mapping.
- `preimageOfFinsetCard` : The cardinality of the preimage of a charge spectrum
  in `ofFinset S5 S10` under a mapping.

## iii. Table of contents

- A. The mapping of charge spectra
  - A.1. Mapping the empty charge spectrum gives the empty charge spectrum
  - A.2. Mapping of charge spectra obeys composing maps
  - A.3. Mapping of charge spectra obeys the identity
  - A.4. The charges of a field label commute with mapping of charge spectra
  - A.5. Mappings of charge spectra preserve the subset relation
  - A.6. Mappings of charge spectra and charges of potential terms
  - A.7. Mapping charge spectra of `allowsTermForm
  - A.8. Mapping preserves whether a charge spectrum allows a potential term
  - A.9. Mapping preserves if a charge spectrum is pheno-constrained
  - A.10. Mapping preserves completeness of charge spectra
  - A.11. Mapping commutes with charges of Yukawa terms
  - A.12. Mapping of charge spectra and regenerating dangerous Yukawa terms
- B. Preimage of a charge spectrum under a mapping
  - B.1. `preimageOfFinset` gives the actual preimage
  - B.2. Efficient definition for the cardinality of the preimage
  - B.3. Definition for the cardinality equals cardinality of the preimage

## iv. References

There are no known references for the material in this module.

-/

namespace SuperSymmetry

namespace SU5
namespace ChargeSpectrum

variable {𝓩 𝓩1 𝓩2 : Type} [AddCommGroup 𝓩] [AddCommGroup 𝓩1] [DecidableEq 𝓩1]
  [AddCommGroup 𝓩2] [DecidableEq 𝓩2]

/-!

## A. The mapping of charge spectra

-/

/-- Given an additive monoid homomorphisms `f : 𝓩 →+ 𝓩1`, for a charge
  `x : Charges 𝓩`, `x.map f` is the charge of `Charges 𝓩1` obtained by mapping the elements
  of `x` by `f`. -/
def map (f : 𝓩 →+ 𝓩1) (x : ChargeSpectrum 𝓩) : ChargeSpectrum 𝓩1 where
  qHd := f <$> x.qHd
  qHu := f <$> x.qHu
  Q5 := x.Q5.image f
  Q10 := x.Q10.image f

/-

### A.1. Mapping the empty charge spectrum gives the empty charge spectrum

-/

@[simp]
lemma map_empty (f : 𝓩 →+ 𝓩1) : map f (∅ : ChargeSpectrum 𝓩) = ∅ := by
  simp only [map, empty_qHd, Option.map_eq_map, Option.map_none, empty_qHu, empty_Q5,
    Finset.image_empty, empty_Q10]
  rfl

/-!

### A.2. Mapping of charge spectra obeys composing maps

-/

lemma map_map (f : 𝓩 →+ 𝓩1) (g : 𝓩1 →+ 𝓩2) (x : ChargeSpectrum 𝓩) :
    map g (map f x) = map (g.comp f) x := by
  simp [map, Option.map_map, Finset.image_image]

/-!

### A.3. Mapping of charge spectra obeys the identity

-/

@[simp]
lemma map_id [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) : map (AddMonoidHom.id 𝓩) x = x := by
  simp [map, Finset.image_id]

/-!

### A.4. The charges of a field label commute with mapping of charge spectra

-/

lemma map_ofFieldLabel (f : 𝓩 →+ 𝓩1) (x : ChargeSpectrum 𝓩) (F : FieldLabel) :
    ofFieldLabel (map f x) F = (ofFieldLabel x F).image f := by
  simp [ofFieldLabel, map]
  match x with
  | ⟨qHd, qHu, Q5, Q10⟩ =>
  fin_cases F
  all_goals simp
  case «0» | «1» =>
    match qHu with
    | some a => simp
    | none => simp
  case «2» | «3» =>
    match qHd with
    | some a => simp
    | none => simp
  · trans (Finset.image (⇑f) Q5).image Neg.neg
    · ext a
      simp
    · rw [Finset.image_image]
      symm
      trans Finset.image (⇑f ∘ Neg.neg) (Q5)
      · ext a
        simp
      congr 1
      funext a
      simp
/-!

### A.5. Mappings of charge spectra preserve the subset relation

-/

lemma map_subset {f : 𝓩 →+ 𝓩1} {x y : ChargeSpectrum 𝓩} (h : x ⊆ y) :
    map f x ⊆ map f y := by
  simp [map, subset_def] at *
  obtain ⟨hHd, hHu, hQ5, hQ10⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · match x, y with
    | ⟨a, _, _, _⟩, ⟨b, _, _, _⟩ =>
      cases a
      all_goals cases b
      all_goals simp
      all_goals simp at hHd
      subst hHd
      rfl
  · match x, y with
    | ⟨_, a, _, _⟩, ⟨_, b, _, _⟩ =>
      cases a
      all_goals cases b
      all_goals simp
      all_goals simp at hHu
      subst hHu
      rfl
  · exact Finset.image_subset_image hQ5
  · exact Finset.image_subset_image hQ10

/-!

### A.6. Mappings of charge spectra and charges of potential terms

-/

lemma map_ofPotentialTerm_toFinset [DecidableEq 𝓩]
    (f : 𝓩 →+ 𝓩1) (x : ChargeSpectrum 𝓩) (T : PotentialTerm) :
    (ofPotentialTerm (map f x) T).toFinset = (ofPotentialTerm x T).toFinset.image f := by
  ext i
  simp [Multiset.mem_toFinset]
  rw [mem_ofPotentialTerm_iff_mem_ofPotentialTerm]
  conv_rhs =>
    enter [1, a]
    rw [mem_ofPotentialTerm_iff_mem_ofPotentialTerm]
  constructor
  · intro h
    cases T
    all_goals
      try simp [ofPotentialTerm'_W2_finset, ofPotentialTerm'_W3_finset,
      ofPotentialTerm'_β_finset, ofPotentialTerm'_μ_finset,
      ofPotentialTerm'_W4_finset, ofPotentialTerm'_K2_finset,
      ofPotentialTerm'_topYukawa_finset, ofPotentialTerm'_bottomYukawa_finset] at h
      try simp [ofPotentialTerm'] at h
    case' μ | β =>
      obtain ⟨q1, q2, ⟨q1_mem, q2_mem⟩, q_sum⟩ := h
      simp [map] at q1_mem q2_mem
      obtain ⟨q1, q1_mem, rfl⟩ := q1_mem
      obtain ⟨q2, q2_mem, rfl⟩ := q2_mem
    case' μ => use q1 - q2
    case' β => use -q1 + q2
    case' Λ | W3 | W4 | K1 | K2 | topYukawa | bottomYukawa =>
      obtain ⟨q1, q2, q3, ⟨q1_mem, q2_mem, q3_mem⟩, q_sum⟩ := h
      simp [map] at q1_mem q2_mem q3_mem
      obtain ⟨q1, q1_mem, rfl⟩ := q1_mem
      obtain ⟨q2, q2_mem, rfl⟩ := q2_mem
      obtain ⟨q3, q3_mem, rfl⟩ := q3_mem
    case' Λ | K2 | bottomYukawa => use q1 + q2 + q3
    case' W3 => use - q1 - q1 + q2 + q3
    case' W4 => use q1 - q2 - q2 + q3
    case' K1 | topYukawa => use - q1 + q2 + q3
    case' W1 | W2 =>
      obtain ⟨q1, q2, q3, q4, ⟨q1_mem, q2_mem, q3_mem, q4_mem⟩, q_sum⟩ := h
      simp [map] at q1_mem q2_mem q3_mem q4_mem
      obtain ⟨q1, q1_mem, rfl⟩ := q1_mem
      obtain ⟨q2, q2_mem, rfl⟩ := q2_mem
      obtain ⟨q3, q3_mem, rfl⟩ := q3_mem
      obtain ⟨q4, q4_mem, rfl⟩ := q4_mem
      use q1 + q2 + q3 + q4
    all_goals
      subst i
      try simp [ofPotentialTerm'_W2_finset, ofPotentialTerm'_W3_finset,
      ofPotentialTerm'_β_finset, ofPotentialTerm'_μ_finset,
      ofPotentialTerm'_W4_finset, ofPotentialTerm'_K2_finset,
      ofPotentialTerm'_topYukawa_finset, ofPotentialTerm'_bottomYukawa_finset]
      try simp [ofPotentialTerm']
      use q1, q2
    · use q3, q4
    · use q3, q4
    all_goals use q3
  · intro h
    obtain ⟨a, h, rfl⟩ := h
    cases T
    all_goals
      try simp [ofPotentialTerm'_W2_finset, ofPotentialTerm'_W3_finset,
      ofPotentialTerm'_β_finset, ofPotentialTerm'_μ_finset,
      ofPotentialTerm'_W4_finset, ofPotentialTerm'_K2_finset,
      ofPotentialTerm'_topYukawa_finset, ofPotentialTerm'_bottomYukawa_finset] at h
      try simp [ofPotentialTerm'] at h
      try simp [ofPotentialTerm'_W2_finset, ofPotentialTerm'_W3_finset,
      ofPotentialTerm'_β_finset, ofPotentialTerm'_μ_finset,
      ofPotentialTerm'_W4_finset, ofPotentialTerm'_K2_finset,
      ofPotentialTerm'_topYukawa_finset, ofPotentialTerm'_bottomYukawa_finset]
      try simp [ofPotentialTerm']
    case' μ | β =>
      obtain ⟨q1, q2, ⟨q1_mem, q2_mem⟩, q_sum⟩ := h
      use f q1, f q2
    case' Λ | W3 | W4 | K1 | K2 | topYukawa | bottomYukawa =>
      obtain ⟨q1, q2, q3, ⟨q1_mem, q2_mem, q3_mem⟩, q_sum⟩ := h
      use f q1, f q2, f q3
    case' W1 | W2 =>
      obtain ⟨q1, q2, q3, q4, ⟨q1_mem, q2_mem, q3_mem, q4_mem⟩, q_sum⟩ := h
      use f q1, f q2, f q3, f q4
    all_goals
      simp only [map]
      subst a
      simp_all
    case W1 => refine ⟨⟨q1, q1_mem, rfl⟩, ⟨q2, q2_mem, rfl⟩, ⟨q3, q3_mem, rfl⟩, ⟨q4, q4_mem, rfl⟩⟩
    case W2 => refine ⟨⟨q2, q2_mem, rfl⟩, ⟨q3, q3_mem, rfl⟩, ⟨q4, q4_mem, rfl⟩⟩
    case Λ | K1 => refine ⟨⟨q1, q1_mem, rfl⟩, ⟨q2, q2_mem, rfl⟩, ⟨q3, q3_mem, rfl⟩⟩
    case W3 | topYukawa | bottomYukawa => refine ⟨⟨q2, q2_mem, rfl⟩, ⟨q3, q3_mem, rfl⟩⟩
    case W4 | K2 => refine ⟨q3, q3_mem, rfl⟩
    case β => refine ⟨q2, q2_mem, rfl⟩

lemma mem_map_ofPotentialTerm_iff [DecidableEq 𝓩]
    (f : 𝓩 →+ 𝓩1) (x : ChargeSpectrum 𝓩) (T : PotentialTerm) :
    i ∈ (ofPotentialTerm (map f x) T) ↔ i ∈ (ofPotentialTerm x T).map f := by
  trans i ∈ (ofPotentialTerm (map f x) T).toFinset
  · simp
  rw [map_ofPotentialTerm_toFinset]
  simp

lemma mem_map_ofPotentialTerm'_iff[DecidableEq 𝓩]
    (f : 𝓩 →+ 𝓩1) (x : ChargeSpectrum 𝓩) (T : PotentialTerm) :
    i ∈ (ofPotentialTerm' (map f x) T) ↔ i ∈ (ofPotentialTerm' x T).map f := by
  rw [← mem_ofPotentialTerm_iff_mem_ofPotentialTerm]
  rw [mem_map_ofPotentialTerm_iff]
  simp only [Multiset.mem_map]
  constructor
  · intro ⟨a, h, h1⟩
    refine ⟨a, ?_, h1⟩
    exact mem_ofPotentialTerm_iff_mem_ofPotentialTerm.mp h
  · intro ⟨a, h, h1⟩
    refine ⟨a, ?_, h1⟩
    exact mem_ofPotentialTerm_iff_mem_ofPotentialTerm.mpr h

lemma map_ofPotentialTerm'_toFinset [DecidableEq 𝓩]
    (f : 𝓩 →+ 𝓩1) (x : ChargeSpectrum 𝓩) (T : PotentialTerm) :
    (ofPotentialTerm' (map f x) T).toFinset = (ofPotentialTerm' x T).toFinset.image f := by
  ext i
  simp only [Multiset.mem_toFinset, Finset.mem_image]
  rw [mem_map_ofPotentialTerm'_iff]
  simp

/-!

### A.7. Mapping charge spectra of `allowsTermForm

-/
variable [DecidableEq 𝓩]

lemma allowsTermForm_map {T} {f : 𝓩 →+ 𝓩1} {a b c : 𝓩} :
    (allowsTermForm a b c T).map f = allowsTermForm (f a) (f b) (f c) T := by
  cases T
  all_goals simp [allowsTermForm, map]

/-!

### A.8. Mapping preserves whether a charge spectrum allows a potential term

-/

lemma map_allowsTerm {f : 𝓩 →+ 𝓩1} {x : ChargeSpectrum 𝓩} {T : PotentialTerm}
    (h : x.AllowsTerm T) : (map f x).AllowsTerm T := by
  rw [allowsTerm_iff_subset_allowsTermForm] at ⊢ h
  obtain ⟨a, b, c, h1⟩ := h
  use f a, f b, f c
  rw [← allowsTermForm_map]
  exact map_subset h1

/-!

### A.9. Mapping preserves if a charge spectrum is pheno-constrained

-/

lemma map_isPhenoConstrained (f : 𝓩 →+ 𝓩1) {x : ChargeSpectrum 𝓩}
    (h : x.IsPhenoConstrained) : (map f x).IsPhenoConstrained := by
  simp [IsPhenoConstrained] at ⊢ h
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inl (map_allowsTerm h)
  · exact Or.inr (Or.inl (map_allowsTerm h))
  · exact Or.inr (Or.inr (Or.inl (map_allowsTerm h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (map_allowsTerm h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (map_allowsTerm h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (map_allowsTerm h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (map_allowsTerm h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((map_allowsTerm h))))))))

lemma not_isPhenoConstrained_of_map {f : 𝓩 →+ 𝓩1} {x : ChargeSpectrum 𝓩}
    (h : ¬ (map f x).IsPhenoConstrained) : ¬ x.IsPhenoConstrained :=
  fun hn => h (map_isPhenoConstrained f hn)

/-!

### A.10. Mapping preserves completeness of charge spectra

-/

omit [DecidableEq 𝓩] in
lemma map_isComplete_iff {f : 𝓩 →+ 𝓩1} {x : ChargeSpectrum 𝓩} :
    (map f x).IsComplete ↔ x.IsComplete := by
  simp [IsComplete, map]

/-!

### A.11. Mapping commutes with charges of Yukawa terms

-/

lemma map_ofYukawaTerms_toFinset {f : 𝓩 →+ 𝓩1} {x : ChargeSpectrum 𝓩} :
    (map f x).ofYukawaTerms.toFinset = x.ofYukawaTerms.toFinset.image f := by
  simp [ofYukawaTerms]
  ext i
  rw [Finset.image_union]
  simp only [Finset.mem_union, Multiset.mem_toFinset]
  rw [mem_map_ofPotentialTerm'_iff, mem_map_ofPotentialTerm'_iff]
  simp [Multiset.mem_map]

lemma mem_map_ofYukawaTerms_iff {f : 𝓩 →+ 𝓩1} {x : ChargeSpectrum 𝓩} {i} :
    i ∈ (map f x).ofYukawaTerms ↔ i ∈ x.ofYukawaTerms.map f := by
  trans i ∈ (map f x).ofYukawaTerms.toFinset
  · simp
  rw [map_ofYukawaTerms_toFinset]
  simp

/-!

### A.12. Mapping of charge spectra and regenerating dangerous Yukawa terms

-/

lemma map_ofYukawaTermsNSum_toFinset {f : 𝓩 →+ 𝓩1} {x : ChargeSpectrum 𝓩} {n : ℕ}:
    ((map f x).ofYukawaTermsNSum n).toFinset = (x.ofYukawaTermsNSum n).toFinset.image f:= by
  induction n with
  | zero => simp [ofYukawaTermsNSum]
  | succ n ih =>
    simp [ofYukawaTermsNSum]
    rw [Finset.image_union]
    congr 1
    ext i
    simp only [Multiset.mem_toFinset, Multiset.mem_bind, Multiset.mem_map, Finset.mem_image,
      exists_exists_and_exists_and_eq_and, map_add]
    constructor
    · intro h
      obtain ⟨a, a_mem, b, b_mem, h⟩ := h
      have a_mem' : a ∈ ((map f x).ofYukawaTermsNSum n).toFinset := by simpa using a_mem
      rw [ih] at a_mem'
      rw [mem_map_ofYukawaTerms_iff] at b_mem
      simp at a_mem' b_mem
      obtain ⟨a, a_mem', rfl⟩ := a_mem'
      obtain ⟨b, b_mem', rfl⟩ := b_mem
      exact ⟨a, a_mem', b, b_mem', h⟩
    · intro h
      obtain ⟨a, a_mem, b, b_mem, h⟩ := h
      use f a
      apply And.intro
      · rw [← Multiset.mem_toFinset, ih]
        simp only [Finset.mem_image, Multiset.mem_toFinset]
        use a
      use f b
      apply And.intro
      · rw [mem_map_ofYukawaTerms_iff]
        simp only [Multiset.mem_map]
        use b
      exact h

lemma mem_map_ofYukawaTermsNSum_iff {f : 𝓩 →+ 𝓩1} {x : ChargeSpectrum 𝓩} {n i} :
    i ∈ (map f x).ofYukawaTermsNSum n ↔ i ∈ (x.ofYukawaTermsNSum n).map f := by
  trans i ∈ ((map f x).ofYukawaTermsNSum n).toFinset
  · simp
  rw [map_ofYukawaTermsNSum_toFinset]
  simp

lemma map_phenoConstrainingChargesSP_toFinset {f : 𝓩 →+ 𝓩1} {x : ChargeSpectrum 𝓩} :
    (map f x).phenoConstrainingChargesSP.toFinset =
    x.phenoConstrainingChargesSP.toFinset.image f := by
  simp [phenoConstrainingChargesSP, map_ofPotentialTerm'_toFinset, Finset.image_union]

lemma map_yukawaGeneratesDangerousAtLevel (f : 𝓩 →+ 𝓩1) {x : ChargeSpectrum 𝓩} (n : ℕ)
    (h : x.YukawaGeneratesDangerousAtLevel n) : (map f x).YukawaGeneratesDangerousAtLevel n := by
  rw [yukawaGeneratesDangerousAtLevel_iff_toFinset]
  rw [map_phenoConstrainingChargesSP_toFinset, map_ofYukawaTermsNSum_toFinset]
  rw [← Finset.nonempty_iff_ne_empty, ← Finset.not_disjoint_iff_nonempty_inter]
  apply Disjoint.of_image_finset.mt
  rw [Finset.not_disjoint_iff_nonempty_inter, Finset.nonempty_iff_ne_empty]
  exact (yukawaGeneratesDangerousAtLevel_iff_toFinset _ _).mp h

lemma not_yukawaGeneratesDangerousAtLevel_of_map {f : 𝓩 →+ 𝓩1} {x : ChargeSpectrum 𝓩}
    (n : ℕ) (h : ¬ (map f x).YukawaGeneratesDangerousAtLevel n) :
    ¬ x.YukawaGeneratesDangerousAtLevel n :=
  fun hn => h (map_yukawaGeneratesDangerousAtLevel f n hn)

/-!

## B. Preimage of a charge spectrum under a mapping

We give a computationally efficient way of calculating the preimage of a charge
`s : Charges 𝓩1` in a subset `ofFinset S5 S10`, and then show it is
equal to the actual preimage.

-/

/-- The preimage of a charge `Charges 𝓩1` in `ofFinset S5 S10 ⊆ Charges 𝓩` under
  mapping charges through `f : 𝓩 →+ 𝓩1`. -/
def preimageOfFinset (S5 S10 : Finset 𝓩) (f : 𝓩 →+ 𝓩1)
    (x : ChargeSpectrum 𝓩1) : Finset (ChargeSpectrum 𝓩) :=
  let SHd := (S5.map ⟨Option.some, Option.some_injective 𝓩⟩ ∪ {none} : Finset (Option 𝓩)).filter
    fun y => f <$> y = x.qHd
  let SHu := (S5.map ⟨Option.some, Option.some_injective 𝓩⟩ ∪ {none} : Finset (Option 𝓩)).filter
    fun y => f <$> y = x.qHu
  let SQ5' := S5.filter fun y => f y ∈ x.Q5
  let SQ5 : Finset (Finset 𝓩) := SQ5'.powerset.filter fun y => y.image f = x.Q5
  let SQ10' := S10.filter fun y => f y ∈ x.Q10
  let SQ10 : Finset (Finset 𝓩) := SQ10'.powerset.filter fun y => y.image f = x.Q10
  (SHd.product <| SHu.product <| SQ5.product SQ10).map toProd.symm.toEmbedding

/-!

### B.1. `preimageOfFinset` gives the actual preimage

-/
lemma preimageOfFinset_eq (S5 S10 : Finset 𝓩) (f : 𝓩 →+ 𝓩1) (x : ChargeSpectrum 𝓩1) :
    preimageOfFinset S5 S10 f x = {y : ChargeSpectrum 𝓩 | y.map f = x ∧ y ∈ ofFinset S5 S10} := by
  ext y
  simp [preimageOfFinset, toProd]
  match y, x with
  | ⟨yHd, yHu, y5, y10⟩, ⟨xHd, xHu, x5, x10⟩ =>
  simp [map]
  constructor
  · intro ⟨⟨h1, rfl⟩, ⟨h2, rfl⟩, ⟨h3, rfl⟩, ⟨h4, rfl⟩⟩
    simp only [true_and]
    rw [mem_ofFinset_iff]
    simp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · match yHd with
      | some a => simpa using h1
      | none => simp
    · match yHu with
      | some a => simpa using h2
      | none => simp
    · exact h3.trans <| Finset.filter_subset (fun y => f y ∈ Finset.image (⇑f) y5) S5
    · apply h4.trans <| Finset.filter_subset (fun y => f y ∈ Finset.image (⇑f) y10) S10
  · intro ⟨⟨rfl, rfl, rfl, rfl⟩, h2⟩
    simp only [and_true, Finset.mem_image]
    rw [mem_ofFinset_iff] at h2
    simp at h2
    refine ⟨?_, ?_, ?_, ?_⟩
    · match yHd with
      | some a =>
        simp at h2
        simpa using h2.1
      | none => simp
    · match yHu with
      | some a =>
        simp at h2
        simpa using h2.2.1
      | none => simp
    · refine Finset.subset_iff.mpr ?_
      intro x hx
      simp only [Finset.mem_filter]
      refine ⟨h2.2.2.1 hx, ?_⟩
      use x
    · refine Finset.subset_iff.mpr ?_
      intro x hx
      simp only [Finset.mem_filter]
      refine ⟨h2.2.2.2 hx, ?_⟩
      use x

/-!

### B.2. Efficient definition for the cardinality of the preimage

-/
/-- The cardinality of the
  preimage of a charge `Charges 𝓩1` in `ofFinset S5 S10 ⊆ Charges 𝓩` under
  mapping charges through `f : 𝓩 →+ 𝓩1`. -/
def preimageOfFinsetCard (S5 S10 : Finset 𝓩) (f : 𝓩 →+ 𝓩1) (x : ChargeSpectrum 𝓩1) : ℕ :=
  let SHd := (S5.map ⟨Option.some, Option.some_injective 𝓩⟩ ∪ {none} : Finset (Option 𝓩)).filter
    fun y => f <$> y = x.qHd
  let SHu := (S5.map ⟨Option.some, Option.some_injective 𝓩⟩ ∪ {none} : Finset (Option 𝓩)).filter
    fun y => f <$> y = x.qHu
  let SQ5' := S5.filter fun y => f y ∈ x.Q5
  let SQ5 : Finset (Finset 𝓩) := SQ5'.powerset.filter fun y => y.image f = x.Q5
  let SQ10' := S10.filter fun y => f y ∈ x.Q10
  let SQ10 : Finset (Finset 𝓩) := SQ10'.powerset.filter fun y => y.image f = x.Q10
  SHd.card * SHu.card * SQ5.card * SQ10.card

/-!

### B.3. Definition for the cardinality equals cardinality of the preimage

-/

lemma preimageOfFinset_card_eq (S5 S10 : Finset 𝓩) (f : 𝓩 →+ 𝓩1) (x : ChargeSpectrum 𝓩1) :
    preimageOfFinsetCard S5 S10 f x =
    (preimageOfFinset S5 S10 f x).card := by
  rw [preimageOfFinset, Finset.card_map]
  simp only [Option.map_eq_map, Finset.product_eq_sprod]
  repeat rw [Finset.card_product]
  simp [preimageOfFinsetCard, mul_assoc]

end ChargeSpectrum
end SU5

end SuperSymmetry
