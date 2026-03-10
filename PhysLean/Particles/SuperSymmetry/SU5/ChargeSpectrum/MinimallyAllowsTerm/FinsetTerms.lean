/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.PhenoConstrained
public import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.MinimallyAllowsTerm.Basic
/-!

# Minimally allows a set of terms

## i. Overview

In this module we consider those charge spectra which minimally allow a
finite set of potential terms.
That is, they those charge spectra which allow each term in the set, but no proper subset of the
charge spectra allows each term in that set.

We have special focus on those charge spectra which minimally allow a top and bottom Yukawa term.

## ii. Key results

- `MinimallyAllowsFinsetTerms`: the proposition that a charge spectrum
  minimally allows a given finite set of potential terms.
- `minTopBottom`: a finite set of charge spectra which contains every
  charge spectrum which minimally allows a top and bottom Yukawa term, given
  finite sets of possible `5`-bar and `10` charges.

## iii. Table of contents

- A. Charge spectra which minimally allow a finite set of potential terms
  - A.1. `MinimallyAllowsFinsetTerms`: Prop of minimally allowing a finset of potential terms
  - A.2. The prop `MinimallyAllowsFinsetTerms` is decidable
  - A.3. Every element of `MinimallyAllowsFinsetTerms` allows each term in the finset
  - A.4. `MinimallyAllowsFinsetTerms` for the singleton set is equivalent to `MinimallyAllowsTerm`
- B. Minimally allowing the top and bottom Yukawa
  - B.1. Finset of charge spectra containing those which minimally allow top and bottom Yukawa
  - B.2. Every element of `minTopBottom` allows a top Yukawa
  - B.3. Every element of `minTopBottom` allows a bottom Yukawa
  - B.4. Every charge spectrum minimally allowing a top and bottom Yukawa in `minTopBottom`

## iv. References

There are no references for this module.

-/

@[expose] public section

namespace SuperSymmetry
namespace SU5

namespace ChargeSpectrum

variable {𝓩 : Type} [AddCommGroup 𝓩] [DecidableEq 𝓩]
open SuperSymmetry.SU5
open PotentialTerm
/-!

## A. Charge spectra which minimally allow a finite set of potential terms

We start by defining the proposition that a charge spectrum minimally allows a
finite set of potential terms, and prove some basic properties there of.

-/

/-!

### A.1. `MinimallyAllowsFinsetTerms`: Prop of minimally allowing a finset of potential terms

-/
/-- A collection of charge spectra is said to minimally allow
  a finite set of potential terms `Ts` if it allows
  all terms in `Ts` and no strict subset of it allows all terms in `Ts`. -/
def MinimallyAllowsFinsetTerms (x : ChargeSpectrum 𝓩) (Ts : Finset PotentialTerm) : Prop :=
  ∀ y ∈ x.powerset, y = x ↔ ∀ T ∈ Ts, y.AllowsTerm T

/-!

### A.2. The prop `MinimallyAllowsFinsetTerms` is decidable

-/

instance (x : ChargeSpectrum 𝓩) (Ts : Finset PotentialTerm) :
    Decidable (x.MinimallyAllowsFinsetTerms Ts) :=
  inferInstanceAs (Decidable (∀ y ∈ powerset x, y = x ↔ ∀ T ∈ Ts, y.AllowsTerm T))

/-!

### A.3. Every element of `MinimallyAllowsFinsetTerms` allows each term in the finset

-/

variable {Ts : Finset PotentialTerm} {x : ChargeSpectrum 𝓩}

lemma allowsTerm_of_minimallyAllowsFinsetTerms {T : PotentialTerm}
    (h : x.MinimallyAllowsFinsetTerms Ts) (hT : T ∈ Ts) : x.AllowsTerm T :=
  (h x (self_mem_powerset x)).mp rfl T hT

/-!

### A.4. `MinimallyAllowsFinsetTerms` for the singleton set is equivalent to `MinimallyAllowsTerm`

-/

@[simp]
lemma minimallyAllowsFinsetTerms_singleton {T : PotentialTerm} :
    x.MinimallyAllowsFinsetTerms {T} ↔ x.MinimallyAllowsTerm T := by
  simp [MinimallyAllowsFinsetTerms, MinimallyAllowsTerm]

/-!

## B. Minimally allowing the top and bottom Yukawa

We now consider the special case of those charge spectra which minimally allow
a top and bottom Yukawa term.

We construct a finite set of such charge spectra given finite sets of
possible `5`-bar and `10` charges which contains every charge
spectrum which minimally allows a top and bottom Yukawa term.

-/

/-!

### B.1. Finset of charge spectra containing those which minimally allow top and bottom Yukawa

Here we define `minTopBottom` in a way which is computationally efficient.

-/

/-- The set of charges of the form `(qHd, qHu, {q5}, {-qHd-q5, q10, qHu - q10})`
  This includes every charge which minimally allows for the top and bottom Yukawas. -/
def minTopBottom (S5 S10 : Finset 𝓩) : Multiset (ChargeSpectrum 𝓩) := Multiset.dedup <|
  (S5.val ×ˢ S5.val ×ˢ S5.val ×ˢ S10.val).map
    (fun x => ⟨x.1, x.2.1, {x.2.2.1}, {- x.1 - x.2.2.1, x.2.2.2, x.2.1 - x.2.2.2}⟩)

/-!

### B.2. Every element of `minTopBottom` allows a top Yukawa

-/

lemma allowsTerm_topYukawa_of_mem_minTopBottom {S5 S10 : Finset 𝓩}
    {x : ChargeSpectrum 𝓩} (h : x ∈ minTopBottom S5 S10) :
    x.AllowsTerm topYukawa := by
  simp only [minTopBottom, Multiset.mem_dedup, Multiset.mem_map, Multiset.mem_product,
    Finset.mem_val, Prod.exists] at h
  obtain ⟨qHd, qHu, q5, q10, ⟨hHd, hHu, h5, h10⟩, rfl⟩ := h
  rw [allowsTerm_iff_subset_allowsTermForm]
  simp [allowsTermForm]
  use -qHu, q10
  rw [subset_def]
  simp

/-!

### B.3. Every element of `minTopBottom` allows a bottom Yukawa

-/

lemma allowsTerm_bottomYukawa_of_mem_minTopBottom {S5 S10 : Finset 𝓩}
    {x : ChargeSpectrum 𝓩} (h : x ∈ minTopBottom S5 S10) :
    x.AllowsTerm bottomYukawa := by
  simp [minTopBottom] at h
  obtain ⟨qHd, qHu, q5, q10, ⟨hHd, hHu, h5, h10⟩, rfl⟩ := h
  rw [allowsTerm_iff_subset_allowsTermForm]
  simp [allowsTermForm]
  use qHd, q5
  rw [subset_def]
  simp

/-!

### B.4. Every charge spectrum minimally allowing a top and bottom Yukawa in `minTopBottom`

-/

lemma mem_minTopBottom_of_minimallyAllowsFinsetTerms
    {x : ChargeSpectrum 𝓩} {S5 S10 : Finset 𝓩}
    (h : x.MinimallyAllowsFinsetTerms {topYukawa, bottomYukawa})
    (hx : x ∈ ofFinset S5 S10) :
    x ∈ minTopBottom S5 S10 := by
  simp [minTopBottom]
  have hTop : x.AllowsTerm topYukawa := allowsTerm_of_minimallyAllowsFinsetTerms h (by simp)
  have hBottom : x.AllowsTerm bottomYukawa := allowsTerm_of_minimallyAllowsFinsetTerms h (by simp)
  match x with
  | ⟨none, qHu, Q5, Q10⟩ =>
    rw [allowsTerm_iff_subset_allowsTermForm] at hBottom
    simp [allowsTermForm, subset_def] at hBottom
  | ⟨qHd, none, Q5, Q10⟩ =>
    rw [allowsTerm_iff_subset_allowsTermForm] at hTop
    simp [allowsTermForm, subset_def] at hTop
  | ⟨some qHd, some qHu, Q5, Q10⟩ =>
  rw [allowsTerm_iff_subset_allowsTermForm] at hTop hBottom
  simp [allowsTermForm, subset_def] at hTop hBottom
  obtain ⟨n, hn, q10, h10⟩ := hTop
  obtain ⟨q5, h5⟩ := hBottom
  use qHd, qHu, q5, q10
  rw [mem_ofFinset_iff] at hx
  simp at hx
  refine ⟨⟨hx.1, hx.2.1, hx.2.2.1 h5.1, hx.2.2.2 (h10 (Finset.mem_insert_self _ _))⟩, ?_⟩
  refine (h _ ?_).mpr ?_
  · simp [subset_def]
    refine ⟨h5.1, ?_⟩
    refine Finset.insert_subset h5.2 ?_
    refine Finset.insert_subset (h10 ?_) ?_
    · simp
    · refine Finset.singleton_subset_iff.mpr (h10 ?_)
      simp [hn]
  · intro T hT
    fin_cases hT
    · rw [allowsTerm_iff_subset_allowsTermForm]
      simp [allowsTermForm, subset_def]
      use -qHu
      simp only [neg_neg, true_and]
      use q10
      simp
    · rw [allowsTerm_iff_subset_allowsTermForm]
      simp [allowsTermForm, subset_def]

end ChargeSpectrum

end SU5
end SuperSymmetry
