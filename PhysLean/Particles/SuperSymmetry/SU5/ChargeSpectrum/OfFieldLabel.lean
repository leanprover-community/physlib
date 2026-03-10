/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.Basic
/-!

# Charges associated with a field label

## i. Overview

Recall that a `FieldLabel` is one of the seven possible superfields in the SU(5) GUT,
corresponding to the fields present and their conjugates.

Given a charge spectrum `x : ChargeSpectrum 𝓩`, we are interested in the finite set of
charges carried by representations associated with a given `FieldLabel`.

Results in this module will be used to find the charges associated with
terms in the potential.

## ii. Key results

- `ofFieldLabel` : Given a charge spectrum `x : ChargeSpectrum 𝓩`,
  `ofFieldLabel x F` is the finite set of charges associated with representations
  corresponding to the field label `F`.

## iii. Table of contents

- A. Charges associated with a field label
  - A.1. The field labels for the empty charge spectrum
  - A.2. Monotonicity of `ofFieldLabel`
  - A.3. Membership of conjugate charges
  - A.4. Extensionality of charge spectra via `ofFieldLabel`

## iv. References

There are no known references for the results in this file.

-/

@[expose] public section

namespace SuperSymmetry
namespace SU5

namespace ChargeSpectrum
open SuperSymmetry.SU5

variable {𝓩 : Type} [InvolutiveNeg 𝓩]

/-!

## A. Charges associated with a field label

We first define `ofFieldLabel`, which given a charge spectrum `x : ChargeSpectrum 𝓩` and
a `FieldLabel`, returns the finite set of charges associated with representations
corresponding to that `FieldLabel`.

-/
/-- Given an `x : Charges`, the charges associated with a given `FieldLabel`. -/
def ofFieldLabel (x : ChargeSpectrum 𝓩) : FieldLabel → Finset 𝓩
  | .fiveBarHd => x.qHd.toFinset
  | .fiveBarHu => x.qHu.toFinset
  | .fiveBarMatter => x.Q5
  | .tenMatter => x.Q10
  | .fiveHd => x.qHd.toFinset.map ⟨Neg.neg, neg_injective⟩
  | .fiveHu => x.qHu.toFinset.map ⟨Neg.neg, neg_injective⟩
  | .fiveMatter => x.Q5.map ⟨Neg.neg, neg_injective⟩

/-!

### A.1. The field labels for the empty charge spectrum

We show that the charges associated with any field label for the empty charge spectrum is empty.
This follows directly from the definition.

-/

/-- `ofFieldLabel ∅ F` is empty for any field label `F`. -/
@[simp]
lemma ofFieldLabel_empty (F : FieldLabel) :
    ofFieldLabel (∅ : ChargeSpectrum 𝓩) F = ∅ := by
  cases F
  all_goals
    rfl

/-!

### A.2. Monotonicity of `ofFieldLabel`

We show that the function `ofFieldLabel` is monotone in the charge spectrum, with relation to
the subset relation. That is for a fixed field label `F`, if `x ⊆ y` are charge spectra,
then `ofFieldLabel x F ⊆ ofFieldLabel y F`.

-/

/-- The function `ofFieldLabel` is monotone in the charge spectrum. -/
lemma ofFieldLabel_mono {x y : ChargeSpectrum 𝓩} (h : x ⊆ y) (F : FieldLabel) :
    x.ofFieldLabel F ⊆ y.ofFieldLabel F := by
  rw [subset_def] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases F
  all_goals simp_all [ofFieldLabel]

/-!

### A.3. Membership of conjugate charges

We show that a charge is a member of the finite sets associated with a field label if and only if
its negative is a member of the finite set associated with the conjugate field label.

-/

@[simp]
lemma mem_ofFieldLabel_fiveHd (x : 𝓩) (y : ChargeSpectrum 𝓩) :
    x ∈ y.ofFieldLabel FieldLabel.fiveHd ↔ -x ∈ y.ofFieldLabel .fiveBarHd := by
  simp [ofFieldLabel]
  aesop

@[simp]
lemma mem_ofFieldLabel_fiveHu (x : 𝓩) (y : ChargeSpectrum 𝓩) :
    x ∈ y.ofFieldLabel FieldLabel.fiveHu ↔ -x ∈ y.ofFieldLabel .fiveBarHu := by
  simp [ofFieldLabel]
  aesop

@[simp]
lemma mem_ofFieldLabel_fiveMatter (x : 𝓩) (y : ChargeSpectrum 𝓩) :
    x ∈ y.ofFieldLabel FieldLabel.fiveMatter ↔ -x ∈ y.ofFieldLabel .fiveBarMatter := by
  simp [ofFieldLabel]
  aesop

/-!

### A.4. Extensionality of charge spectra via `ofFieldLabel`

We show that two charge spectra are equal if they are equal on all field labels.

This extensionality lemma is actually overkill in most cases, as there are a lot more
direct ways to show that two charge spectra are equal.

-/

/-- Two charges are equal if they are equal on all field labels. -/
lemma ext_ofFieldLabel {x y : ChargeSpectrum 𝓩} (h : ∀ F, x.ofFieldLabel F = y.ofFieldLabel F) :
    x = y := by
  match x, y with
  | ⟨x1, x2, x3, x4⟩, ⟨y1, y2, y3, y4⟩ =>
  have h1 := h FieldLabel.fiveBarHd
  have h2 := h FieldLabel.fiveBarHu
  have h3 := h FieldLabel.fiveBarMatter
  have h4 := h FieldLabel.tenMatter
  clear h
  simp_all [ofFieldLabel]
  rw [← Option.toFinset_inj] at h1 h2
  simp_all

end ChargeSpectrum

end SU5
end SuperSymmetry
