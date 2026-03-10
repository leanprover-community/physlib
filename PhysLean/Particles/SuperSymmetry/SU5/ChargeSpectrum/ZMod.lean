/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

meta import Mathlib.Data.ZMod.Defs
meta import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.Yukawa
meta import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.Completions
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.ZMod.Defs
public import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.Yukawa
public import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.Completions
public import PhysLean.Meta.Linters.Sorry
/-!

# Charge spectra with values in `ZMod n`

## i. Overview

The way that we have defined `ChargeSpectrum` means we can consider values
of charges which are not only elements of `ℤ`, but also elements of other types.

In this file we will consider `ChargeSpectrum` which have values in `ZMod n` for various
natural numbers `n`, as well as charge spectra with values in `ZMod n × ZMod m`.

In this file we focus on 4-insertions of singlets to be phenomenologically viable.
In other files we usually just consider one.

## ii. Key results

- `ZModCharges n` : The finite set of `ZMod n` valued charges which are complete,
  not pheno-constrained and don't regenerate dangerous couplings
  with the Yukawa term up-to 4-inserstions of singlets.
- `ZModZModCharges m n` : The finite set of `ZMod n × ZMod m` valued charges which are complete,
  not pheno-constrained and don't regenerate dangerous couplings
  with the Yukawa term up-to 4-inserstions of singlets.

## iii. Table of contents

- A. The finite set of viable `ZMod n` charge spectra
  - A.1. General construction
  - A.2. Finite set of viable `ZMod 1` charge spectra is empty
  - A.3. Finite set of viable `ZMod 2` charge spectra is empty
  - A.4. Finite set of viable `ZMod 3` charge spectra is empty
  - A.5. Finite set of viable `ZMod 4` has four elements
  - A.6. Finite set of viable `ZMod 5` charge spectra is empty (pseudo result)
  - A.7. Finite set of viable `ZMod 6` charge spectra is non-empty (pseudo result)
- B. The finite set of viable `ZMod n × ZMod m` charge spectra
  - B.1. General construction

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

namespace SuperSymmetry

namespace SU5
namespace ChargeSpectrum

/-!

## A. The finite set of viable `ZMod n` charge spectra

-/

/-!

### A.1. General construction

-/

/-- The finite set of `ZMod n` valued charges which are complete,
  not pheno-constrained and don't regenerate dangerous couplings
  with the Yukawa term up-to 4-inserstions of singlets. -/
def ZModCharges (n : ℕ) [NeZero n] : Finset (ChargeSpectrum (ZMod n)) :=
  let S : Finset (ChargeSpectrum (ZMod n)) := ofFinset Finset.univ Finset.univ
  S.filter (fun x => IsComplete x ∧ ¬ x.IsPhenoConstrained ∧ ¬ x.YukawaGeneratesDangerousAtLevel 4)

/-!

### A.2. Finite set of viable `ZMod 1` charge spectra is empty

-/

/-- This lemma corresponds to the statement that there are no choices of `ℤ₁` representations
  which give a phenomenologically viable theory. -/
lemma ZModCharges_one_eq : ZModCharges 1 = ∅:= by decide

/-!

### A.3. Finite set of viable `ZMod 2` charge spectra is empty

-/

set_option maxRecDepth 2000 in
/-- This lemma corresponds to the statement that there are no choices of `ℤ₂` representations
  which give a phenomenologically viable theory. -/
lemma ZModCharges_two_eq : ZModCharges 2 = ∅ := by decide

/-!

### A.4. Finite set of viable `ZMod 3` charge spectra is empty

-/

/-- This lemma corresponds to the statement that there are no choices of `ℤ₃` representations
  which give a phenomenologically viable theory. -/
@[pseudo]
lemma ZModCharges_three_eq : ZModCharges 3 = ∅ := by native_decide

/-!

### A.5. Finite set of viable `ZMod 4` has four elements

-/

@[pseudo]
lemma ZModCharges_four_eq : ZModCharges 4 = {⟨some 0, some 2, {1}, {3}⟩,
    ⟨some 0, some 2, {3}, {1}⟩, ⟨some 1, some 2, {0}, {3}⟩, ⟨some 3, some 2, {0}, {1}⟩} := by
  native_decide

/-!

### A.6. Finite set of viable `ZMod 5` charge spectra is empty (pseudo result)

-/

/-- This lemma corresponds to the statement that there are no choices of `ℤ₅` representations
  which give a phenomenologically viable theory. -/
@[pseudo]
lemma ZModCharges_five_eq : ZModCharges 5 = ∅ := by native_decide

/-!

### A.7. Finite set of viable `ZMod 6` charge spectra is non-empty (pseudo result)

-/

@[pseudo]
lemma ZModCharges_six_eq : ZModCharges 6 = {⟨some 0, some 2, {5}, {1}⟩,
    ⟨some 0, some 4, {1}, {5}⟩, ⟨some 1, some 0, {2}, {3}⟩, ⟨some 1, some 2, {4}, {1}⟩,
    ⟨some 1, some 4, {0}, {5}⟩, ⟨some 1, some 4, {3}, {2}⟩, ⟨some 2, some 0, {1}, {3}⟩,
    ⟨some 2, some 4, {5}, {5}⟩, ⟨some 3, some 2, {5}, {4}⟩, ⟨some 3, some 4, {1}, {2}⟩,
    ⟨some 4, some 0, {5}, {3}⟩, ⟨some 4, some 2, {1}, {1}⟩, ⟨some 5, some 0, {4}, {3}⟩,
    ⟨some 5, some 2, {0}, {1}⟩, ⟨some 5, some 2, {3}, {4}⟩, ⟨some 5, some 4, {2}, {5}⟩} := by
  native_decide

/-!

## B. The finite set of viable `ZMod n × ZMod m` charge spectra

-/

/-!

### B.1. General construction

-/

/-- The finite set of `ZMod n × ZMod m` valued charges which are complete,
  not pheno-constrained and don't regenerate dangerous couplings
  with the Yukawa term up-to 4-inserstions of singlets. -/
def ZModZModCharges (n m : ℕ) [NeZero n] [NeZero m] : Finset (ChargeSpectrum (ZMod n × ZMod m)) :=
  let S : Finset (ChargeSpectrum (ZMod n × ZMod m)) := ofFinset (Finset.univ) Finset.univ
  S.filter (fun x => IsComplete x ∧
  ¬ x.IsPhenoConstrained ∧ ¬ x.YukawaGeneratesDangerousAtLevel 4)

end ChargeSpectrum
end SU5

end SuperSymmetry
