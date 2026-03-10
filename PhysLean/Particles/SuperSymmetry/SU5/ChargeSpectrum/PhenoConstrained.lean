/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.AllowsTerm
public import Mathlib.Tactic.Polyrith
/-!

# Pheno constrained charge spectra

## i. Overview

We define a predicate `IsPhenoConstrained` on `ChargeSpectrum 𝓩` which is true if the charge
spectrum allows any super-potential or Kähler potential term leading to proton decay or
R-parity violation.

We prove basic properties of this predicate including monotonicity.

We define some variations of this result.

## ii. Key results

- `IsPhenoConstrained`: The predicate defining a pheno-constrained charge spectrum
  as one allowing any term leading to proton decay or R-parity violation.
- `phenoConstrainingChargesSP`: The multiset of charges of terms in the super-potential
  leading to a pheno-constrained charge spectrum.
- `IsPhenoConstrainedQ5`: The predicate defining when a charge spectrum becomes
  pheno-constrained after adding a single charge to the `Q5` set.
- `IsPhenoConstrainedQ10`: The predicate defining when a charge spectrum becomes
  pheno-constrained after adding a single charge to the `Q10` set.

## iii. Table of contents

- A. Phenomenological constrained charge spectra
  - A.1. Decidability of `IsPhenoConstrained`
  - A.2. The empty charge spectrum is not pheno-constrained
  - A.3. Monotonicity of being pheno-constrained
- B. Charges of pheno-constraining terms in the super potential
  - B.1. The empty charge spectrum has an empty set of pheno-constraining term charges
  - B.2. The charges of pheno-constraining terms in the SP is monotone
- C. Phenomenologically constrained charge spectra after adding a single Q5 charge
  - C.2. Reducing the condition `IsPhenoConstrainedQ5`
  - C.3. Decidability of `IsPhenoConstrainedQ5`
  - C.4. Charge spectra with added `Q5` charge is pheno-constrained iff
- D. Phenomenologically constrained charge spectra after adding a single Q10 charge
  - D.2. Reducing the condition `IsPhenoConstrainedQ10`
  - D.3. Decidability of `IsPhenoConstrainedQ10`
  - D.4. Charge spectra with added `Q10` charge is pheno-constrained iff

## iv. References

There are no known references for the material in this file.

-/

@[expose] public section
namespace SuperSymmetry

namespace SU5

namespace ChargeSpectrum
open SuperSymmetry.SU5
open PotentialTerm

variable {𝓩 : Type} [AddCommGroup 𝓩]

/-!

## A. Phenomenological constrained charge spectra

-/

/-- A charge is pheno-constrained if it leads to the presence of any term causing proton decay
  ` {W1, Λ, W2, K1}` or R-parity violation `{β, Λ, W2, W4, K1, K2}`. -/
def IsPhenoConstrained (x : ChargeSpectrum 𝓩) : Prop :=
  x.AllowsTerm μ ∨ x.AllowsTerm β ∨ x.AllowsTerm Λ ∨ x.AllowsTerm W2 ∨ x.AllowsTerm W4 ∨
  x.AllowsTerm K1 ∨ x.AllowsTerm K2 ∨ x.AllowsTerm W1

/-!

### A.1. Decidability of `IsPhenoConstrained`

-/

instance decidableIsPhenoConstrained [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) :
    Decidable x.IsPhenoConstrained :=
  inferInstanceAs (Decidable (x.AllowsTerm μ ∨ x.AllowsTerm β ∨ x.AllowsTerm Λ ∨ x.AllowsTerm W2
    ∨ x.AllowsTerm W4 ∨ x.AllowsTerm K1 ∨ x.AllowsTerm K2 ∨ x.AllowsTerm W1))

/-!

### A.2. The empty charge spectrum is not pheno-constrained

The empty charge spectrum does not allow any terms, and so is not pheno-constrained.

-/

@[simp]
lemma not_isPhenoConstrained_empty :
    ¬ IsPhenoConstrained (∅ : ChargeSpectrum 𝓩) := by
  simp [IsPhenoConstrained, AllowsTerm, ofPotentialTerm_empty]

/-!

### A.3. Monotonicity of being pheno-constrained

If a charge spectrum `x` is pheno-constrained, then any charge spectrum `y` containing `x`
is also pheno-constrained.

-/

lemma isPhenoConstrained_mono {x y : ChargeSpectrum 𝓩} (h : x ⊆ y)
    (hx : x.IsPhenoConstrained) : y.IsPhenoConstrained := by
  simp [IsPhenoConstrained] at *
  rcases hx with hr | hr | hr | hr | hr | hr | hr | hr
  all_goals
    have h' := allowsTerm_mono h hr
    simp_all

/-!

## B. Charges of pheno-constraining terms in the super potential

-/

/-- The collection of charges of super-potential terms leading to a pheno-constrained model. -/
def phenoConstrainingChargesSP (x : ChargeSpectrum 𝓩) : Multiset 𝓩 :=
  x.ofPotentialTerm' μ + x.ofPotentialTerm' β + x.ofPotentialTerm' Λ +
  x.ofPotentialTerm' W2 + x.ofPotentialTerm' W4 + x.ofPotentialTerm' W1

/-!

### B.1. The empty charge spectrum has an empty set of pheno-constraining term charges

-/

@[simp]
lemma phenoConstrainingChargesSP_empty :
    phenoConstrainingChargesSP (∅ : ChargeSpectrum 𝓩) = ∅ := by
  simp [phenoConstrainingChargesSP]

/-!

### B.2. The charges of pheno-constraining terms in the SP is monotone

-/
lemma phenoConstrainingChargesSP_mono [DecidableEq 𝓩] {x y : ChargeSpectrum 𝓩} (h : x ⊆ y) :
    x.phenoConstrainingChargesSP ⊆ y.phenoConstrainingChargesSP := by
  simp only [phenoConstrainingChargesSP]
  refine Multiset.subset_iff.mpr ?_
  intro z
  simp [or_assoc]
  intro hr
  rcases hr with hr | hr | hr | hr | hr | hr
  all_goals
    have h' := ofPotentialTerm'_mono h _ hr
    simp_all

/-!

## C. Phenomenologically constrained charge spectra after adding a single Q5 charge

We now define `IsPhenoConstrainedQ5` which gives the condition that a charge spectrum becomes
pheno-constrained after adding a single charge to the `Q5` set.

-/

/-- The proposition which is true if the addition of a charge `q5` to a set of charge `x` leads
  `x` to being phenomenologically constrained. -/
def IsPhenoConstrainedQ5 [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) (q5 : 𝓩) : Prop :=
  x.AllowsTermQ5 q5 μ ∨ x.AllowsTermQ5 q5 β ∨ x.AllowsTermQ5 q5 Λ ∨ x.AllowsTermQ5 q5 W2 ∨
  x.AllowsTermQ5 q5 W4 ∨
  x.AllowsTermQ5 q5 K1 ∨ x.AllowsTermQ5 q5 K2 ∨ x.AllowsTermQ5 q5 W1

/-!

### C.2. Reducing the condition `IsPhenoConstrainedQ5`

-/

lemma isPhenoConstrainedQ5_iff [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) (q5 : 𝓩) :
    x.IsPhenoConstrainedQ5 q5 ↔
    x.AllowsTermQ5 q5 β ∨ x.AllowsTermQ5 q5 Λ ∨ x.AllowsTermQ5 q5 W4 ∨
    x.AllowsTermQ5 q5 K1 ∨ x.AllowsTermQ5 q5 W1 := by
  simp [IsPhenoConstrainedQ5, AllowsTermQ5]

/-!

### C.3. Decidability of `IsPhenoConstrainedQ5`

-/

instance decidableIsPhenoConstrainedQ5 [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) (q5 : 𝓩) :
    Decidable (x.IsPhenoConstrainedQ5 q5) :=
  decidable_of_iff _ (isPhenoConstrainedQ5_iff x q5).symm

/-!

### C.4. Charge spectra with added `Q5` charge is pheno-constrained iff

-/

lemma isPhenoConstrained_insertQ5_iff_isPhenoConstrainedQ5 [DecidableEq 𝓩] {qHd qHu : Option 𝓩}
    {Q5 Q10: Finset 𝓩} {q5 : 𝓩} :
    IsPhenoConstrained ⟨qHd, qHu, insert q5 Q5, Q10⟩↔
    IsPhenoConstrainedQ5 ⟨qHd, qHu, Q5, Q10⟩ q5 ∨
    IsPhenoConstrained ⟨qHd, qHu, Q5, Q10⟩:= by
  constructor
  · intro hr
    rcases hr with hr | hr | hr | hr | hr | hr | hr | hr
    all_goals
      rw [allowsTerm_insertQ5_iff_allowsTermQ5] at hr
      rcases hr with hr | hr
      all_goals
        simp_all [IsPhenoConstrainedQ5, IsPhenoConstrained]
  · intro hr
    rcases hr with hr | hr
    · simp [IsPhenoConstrainedQ5] at hr
      rcases hr with hr | hr | hr | hr | hr | hr | hr | hr
      all_goals
        have hr' := allowsTerm_insertQ5_of_allowsTermQ5 _ hr
        simp_all [IsPhenoConstrained]
    · apply isPhenoConstrained_mono _ hr
      simp [subset_def]

/-!

## D. Phenomenologically constrained charge spectra after adding a single Q10 charge

We now define `IsPhenoConstrainedQ10` which gives the condition that a charge spectrum becomes
pheno-constrained after adding a single charge to the `Q10` set.

-/

/-- The proposition which is true if the addition of a charge `q10` to a set of charges `x` leads
  `x` to being phenomenologically constrained. -/
def IsPhenoConstrainedQ10 [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) (q10 : 𝓩) : Prop :=
  x.AllowsTermQ10 q10 μ ∨ x.AllowsTermQ10 q10 β ∨ x.AllowsTermQ10 q10 Λ ∨ x.AllowsTermQ10 q10 W2 ∨
  x.AllowsTermQ10 q10 W4 ∨
  x.AllowsTermQ10 q10 K1 ∨ x.AllowsTermQ10 q10 K2 ∨ x.AllowsTermQ10 q10 W1

/-!

### D.2. Reducing the condition `IsPhenoConstrainedQ10`

-/

lemma isPhenoConstrainedQ10_iff [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) (q10 : 𝓩) :
    x.IsPhenoConstrainedQ10 q10 ↔ x.AllowsTermQ10 q10 Λ ∨ x.AllowsTermQ10 q10 W2 ∨
    x.AllowsTermQ10 q10 K1 ∨ x.AllowsTermQ10 q10 K2 ∨ x.AllowsTermQ10 q10 W1 := by
  simp [IsPhenoConstrainedQ10, AllowsTermQ10]

/-!

### D.3. Decidability of `IsPhenoConstrainedQ10`

-/

instance decidableIsPhenoConstrainedQ10 [DecidableEq 𝓩] (x : ChargeSpectrum 𝓩) (q10 : 𝓩) :
    Decidable (x.IsPhenoConstrainedQ10 q10) :=
  decidable_of_iff _ (isPhenoConstrainedQ10_iff x q10).symm

/-!

### D.4. Charge spectra with added `Q10` charge is pheno-constrained iff

-/

lemma isPhenoConstrained_insertQ10_iff_isPhenoConstrainedQ10 [DecidableEq 𝓩] {qHd qHu : Option 𝓩}
    {Q5 Q10: Finset 𝓩} {q10 : 𝓩} :
    IsPhenoConstrained ⟨qHd, qHu, Q5, insert q10 Q10⟩ ↔
    IsPhenoConstrainedQ10 ⟨qHd, qHu, Q5, Q10⟩ q10 ∨
    IsPhenoConstrained ⟨qHd, qHu, Q5, Q10⟩ := by
  constructor
  · intro hr
    rcases hr with hr | hr | hr | hr | hr | hr | hr | hr
    all_goals
      rw [allowsTerm_insertQ10_iff_allowsTermQ10] at hr
      rcases hr with hr | hr
      all_goals
        simp_all [IsPhenoConstrainedQ10, IsPhenoConstrained]
  · intro hr
    rcases hr with hr | hr
    · simp [IsPhenoConstrainedQ10] at hr
      rcases hr with hr | hr | hr | hr | hr | hr | hr | hr
      all_goals
        have hr' := allowsTerm_insertQ10_of_allowsTermQ10 _ hr
        simp_all [IsPhenoConstrained]
    · apply isPhenoConstrained_mono _ hr
      simp [subset_def]

end ChargeSpectrum

end SU5

end SuperSymmetry
