/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.PhenoConstrained
/-!

# Yukawa charges

## i. Overview

In this module we look at the charges associated with the Yukawa terms
in the super potential, and when they can regenerate
phenomenologically constrained super-potential terms at different levels.

We do not not consider the regeneration of terms in the Kähler potential within
this module.

## ii. Key results

- `ofYukawaTerms`: the multiset of charges associated with the Yukawa terms
- `ofYukawaTermsNSum`: the multiset of charges associated with up-to `n` copies of the Yukawa terms
  or equivalently the charges of singlet insertions needed to regenerate Yukawa terms.
- `YukawaGeneratesDangerousAtLevel`: the proposition that a charge spectrum regenerates a
  phenomenologically constrained term in the super-potential
  with up-to `n` insertions of singlets needed to regenerate
  the Yukawa terms.

## iii. Table of contents

- A. Charges of the Yukawa terms
  - A.1. Monotonicity of charges of the Yukawa terms
  - A.2. upto n-copies of charges of the Yukawa terms (aka charges of singlet insertions)
  - A.3. Monotonicity of set of charges of upto n-copies of the Yukawa terms
- B. Regeneration of phenomenologically constrained terms via upto n Yukawa singlet insertions
  - B.1. Decidability of `YukawaGeneratesDangerousAtLevel`
  - B.2. Simplifications of condition for regenerating dangerous terms
  - B.3. Empty charge spectrum does not regenerate dangerous terms
  - B.4. Monotonicity of regeneration of dangerous terms in charge spectra
  - B.5. Monotonicity of regeneration of dangerous terms in level

## iv. References

There are no known references for this module.

-/

@[expose] public section
namespace SuperSymmetry
namespace SU5

namespace ChargeSpectrum
open PotentialTerm

variable {𝓩 : Type} [AddCommGroup 𝓩]

/-!

## A. Charges of the Yukawa terms

-/

/-- The collection of charges associated with Yukawa terms.
  Correspondingly, the (negative) of the charges of the singlets needed to regenerate all
  Yukawa terms in the potential. -/
def ofYukawaTerms (x : ChargeSpectrum 𝓩) : Multiset 𝓩 :=
  x.ofPotentialTerm' topYukawa + x.ofPotentialTerm' bottomYukawa

/-!

### A.1. Monotonicity of charges of the Yukawa terms

-/

lemma ofYukawaTerms_subset_of_subset [DecidableEq 𝓩] {x y : ChargeSpectrum 𝓩} (h : x ⊆ y) :
    x.ofYukawaTerms ⊆ y.ofYukawaTerms := by
  simp only [ofYukawaTerms]
  refine Multiset.subset_iff.mpr ?_
  intro z
  simp only [Multiset.mem_add]
  intro hr
  rcases hr with hr | hr
  · left
    apply ofPotentialTerm'_mono h
    exact hr
  · right
    apply ofPotentialTerm'_mono h
    exact hr

/-!

### A.2. upto n-copies of charges of the Yukawa terms (aka charges of singlet insertions)

-/

/-- The charges of those terms which can be regenerated with up-to `n`
  insertions of singlets needed to regenerate the Yukawa terms.
  Equivalently, the sum of up-to `n` integers each corresponding to a charge of the
  Yukawa terms. -/
def ofYukawaTermsNSum (x : ChargeSpectrum 𝓩) : ℕ → Multiset 𝓩
  | 0 => {0}
  | n + 1 => x.ofYukawaTermsNSum n + (x.ofYukawaTermsNSum n).bind fun sSum =>
    (x.ofYukawaTerms.map fun s => sSum + s)

/-!

### A.3. Monotonicity of set of charges of upto n-copies of the Yukawa terms

-/

lemma ofYukawaTermsNSum_subset_of_subset [DecidableEq 𝓩] {x y : ChargeSpectrum 𝓩}
    (h : x ⊆ y) (n : ℕ) :
    x.ofYukawaTermsNSum n ⊆ y.ofYukawaTermsNSum n := by
  induction n with
  | zero => simp [ofYukawaTermsNSum]
  | succ n ih =>
    simp [ofYukawaTermsNSum]
    refine Multiset.subset_iff.mpr ?_
    intro z
    simp only [Multiset.mem_add, Multiset.mem_bind, Multiset.mem_map]
    intro hr
    rcases hr with hr | ⟨z1, hz1, z2, hz2, hsum⟩
    · left
      exact ih hr
    right
    use z1
    constructor
    · exact ih hz1
    use z2
    simp_all only [and_true]
    apply ofYukawaTerms_subset_of_subset h
    exact hz2

/-!

## B. Regeneration of phenomenologically constrained terms via upto n Yukawa singlet insertions

-/

variable [DecidableEq 𝓩]

/-- For charges `x : Charges`, the proposition which states that the singlets
  needed to regenerate the Yukawa couplings regenerate a dangerous coupling
  (in the superpotential) with up-to `n` insertions of the scalars.

  Note: If defined as (x.ofYukawaTermsNSum n).toFinset ∩ x.phenoConstrainingChargesSP.toFinset ≠ ∅
  the execution time is greatly increased. -/
def YukawaGeneratesDangerousAtLevel (x : ChargeSpectrum 𝓩) (n : ℕ) : Prop :=
  (x.ofYukawaTermsNSum n) ∩ x.phenoConstrainingChargesSP ≠ ∅

/-!

### B.1. Decidability of `YukawaGeneratesDangerousAtLevel`

-/

instance (x : ChargeSpectrum 𝓩) (n : ℕ) : Decidable (YukawaGeneratesDangerousAtLevel x n) :=
  inferInstanceAs (Decidable ((x.ofYukawaTermsNSum n)
    ∩ x.phenoConstrainingChargesSP ≠ ∅))

/-!

### B.2. Simplifications of condition for regenerating dangerous terms

-/

lemma YukawaGeneratesDangerousAtLevel_iff_inter {x : ChargeSpectrum 𝓩} {n : ℕ} :
    YukawaGeneratesDangerousAtLevel x n ↔
    (x.ofYukawaTermsNSum n) ∩ x.phenoConstrainingChargesSP ≠ ∅ := by rfl

lemma yukawaGeneratesDangerousAtLevel_iff_toFinset (x : ChargeSpectrum 𝓩) (n : ℕ) :
    x.YukawaGeneratesDangerousAtLevel n ↔
    (x.ofYukawaTermsNSum n).toFinset ∩ x.phenoConstrainingChargesSP.toFinset ≠ ∅ := by
  simp [YukawaGeneratesDangerousAtLevel]
  constructor
  · intro h hn
    apply h
    ext i
    simp only [Multiset.count_inter, Multiset.notMem_zero, not_false_eq_true,
      Multiset.count_eq_zero_of_notMem, Nat.min_eq_zero_iff, Multiset.count_eq_zero]
    by_contra h0
    simp at h0
    have h1 : i ∈ (x.ofYukawaTermsNSum n).toFinset ∩ x.phenoConstrainingChargesSP.toFinset := by
      simpa using h0
    simp_all
  · intro h hn
    apply h
    ext i
    simp only [Finset.mem_inter, Multiset.mem_toFinset, Finset.notMem_empty, iff_false, not_and]
    intro h1 h2
    have h3 : i ∈ (x.ofYukawaTermsNSum n) ∩ x.phenoConstrainingChargesSP := by
      simpa using ⟨h1, h2⟩
    simp_all

/-!

### B.3. Empty charge spectrum does not regenerate dangerous terms

-/

@[simp]
lemma not_yukawaGeneratesDangerousAtLevel_of_empty (n : ℕ) :
    ¬ YukawaGeneratesDangerousAtLevel (∅ : ChargeSpectrum 𝓩) n := by
  simp [YukawaGeneratesDangerousAtLevel]

/-!

### B.4. Monotonicity of regeneration of dangerous terms in charge spectra

If `x` regenerates a dangerous term with up-to `n` insertions of Yukawa singlets,
and `x ⊆ y`, then `y` also regenerates a dangerous term with up-to `n` insertions.

-/

lemma yukawaGeneratesDangerousAtLevel_of_subset {x y : ChargeSpectrum 𝓩} {n : ℕ} (h : x ⊆ y)
    (hx : x.YukawaGeneratesDangerousAtLevel n) :
    y.YukawaGeneratesDangerousAtLevel n := by
  simp [yukawaGeneratesDangerousAtLevel_iff_toFinset] at *
  have h1 : (x.ofYukawaTermsNSum n).toFinset ∩ x.phenoConstrainingChargesSP.toFinset
      ⊆ (y.ofYukawaTermsNSum n).toFinset ∩ y.phenoConstrainingChargesSP.toFinset := by
    trans (x.ofYukawaTermsNSum n).toFinset ∩ y.phenoConstrainingChargesSP.toFinset
    · apply Finset.inter_subset_inter_left
      simp only [Multiset.toFinset_subset]
      exact phenoConstrainingChargesSP_mono h
    · apply Finset.inter_subset_inter_right
      simp only [Multiset.toFinset_subset]
      exact ofYukawaTermsNSum_subset_of_subset h n
  by_contra hn
  rw [hn] at h1
  simp at h1
  rw [h1] at hx
  simp at hx

/-!

### B.5. Monotonicity of regeneration of dangerous terms in level

If `x` regenerates a dangerous term with up-to `n` insertions of Yukawa singlets,
then `x` also regenerates a dangerous term with up-to `n + 1` insertions.

-/

lemma yukawaGeneratesDangerousAtLevel_succ {x : ChargeSpectrum 𝓩} {n : ℕ}
    (hx : x.YukawaGeneratesDangerousAtLevel n) :
    x.YukawaGeneratesDangerousAtLevel (n + 1) := by
  simp [yukawaGeneratesDangerousAtLevel_iff_toFinset] at *
  simp [ofYukawaTermsNSum]
  rw [Finset.union_inter_distrib_right]
  rw [Finset.union_eq_empty]
  rw [not_and_or]
  left
  exact hx

lemma yukawaGeneratesDangerousAtLevel_add_of_left {x : ChargeSpectrum 𝓩} {n k : ℕ}
    (hx : x.YukawaGeneratesDangerousAtLevel n) :
    x.YukawaGeneratesDangerousAtLevel (n + k) := by
  induction k with
  | zero => exact hx
  | succ k ih => exact yukawaGeneratesDangerousAtLevel_succ ih

lemma yukawaGeneratesDangerousAtLevel_of_le {x : ChargeSpectrum 𝓩} {n m : ℕ}
    (h : n ≤ m) (hx : x.YukawaGeneratesDangerousAtLevel n) :
    x.YukawaGeneratesDangerousAtLevel m := by
  generalize hk : m - n = k at *
  have h1 : n + k = m := by omega
  subst h1
  exact yukawaGeneratesDangerousAtLevel_add_of_left hx

end ChargeSpectrum

end SU5
end SuperSymmetry
