/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Classical.Basic
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.OrderUnit
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality

/-!
# Commutative C⋆-algebras are classical

The observables of a commutative C⋆-algebra form a classical system, via its characters.

## i. Overview

A commutative C⋆-algebra is the algebra of continuous functions on its characters, the pure
states. An observable is nonnegative exactly when every character assigns it a nonnegative value,
and one observable lies below another exactly when every character says so. Minima can then be
taken character by character, which gives the Riesz decomposition of the observables. So the
self-adjoint part of a commutative C⋆-algebra is a classical system.

## ii. Key results

- `CommCStarAlgebra.character` : a character as a star-algebra homomorphism.
- `CommCStarAlgebra.nonneg_iff_forall_character` : characters detect positivity.
- `CommCStarAlgebra.hasRieszDecomposition` : the observables have the Riesz decomposition.
- `CommCStarAlgebra.isClassical` : the observables form a classical system.

## iii. Table of contents

- A. Characters
- B. Order through characters
- C. Classicality

## iv. References

* None.

-/

@[expose] public section


namespace CommCStarAlgebra
open ProbabilisticTheory
open scoped ComplexOrder

variable {A : Type*} [CommCStarAlgebra A]

/-! ## A. Characters -/

/-- A character of a commutative C⋆-algebra, as a star-algebra homomorphism to `ℂ`. -/
noncomputable def character (χ : WeakDual.characterSpace ℂ A) : A →⋆ₐ[ℂ] ℂ :=
  (ContinuousMap.evalStarAlgHom ℂ ℂ χ).comp (gelfandStarTransform A).toStarAlgHom

@[simp]
lemma character_apply (χ : WeakDual.characterSpace ℂ A) (a : A) : character χ a = χ a := rfl

/-- Characters separate the elements of a commutative C⋆-algebra. -/
lemma ext_character {a b : A} (h : ∀ χ : WeakDual.characterSpace ℂ A, χ a = χ b) : a = b :=
  (gelfandStarTransform A).injective (ContinuousMap.ext h)

/-- A character takes real values on self-adjoint elements. -/
lemma character_eq_re {a : A} (ha : IsSelfAdjoint a) (χ : WeakDual.characterSpace ℂ A) :
    χ a = ((χ a).re : ℂ) := by
  have h : star (χ a) = χ a := by
    rw [← character_apply, ← map_star, ha.star_eq]
  exact (Complex.conj_eq_iff_re.1 h).symm

/-- The pointwise minimum of two self-adjoint elements, taken character by character. -/
noncomputable def inf (a b : A) : A :=
  (gelfandStarTransform A).symm
    ⟨fun χ => ((min (χ a).re (χ b).re : ℝ) : ℂ), by
      have ha : Continuous fun χ : WeakDual.characterSpace ℂ A => χ a :=
        (WeakDual.gelfandTransform ℂ A a).continuous
      have hb : Continuous fun χ : WeakDual.characterSpace ℂ A => χ b :=
        (WeakDual.gelfandTransform ℂ A b).continuous
      exact Complex.continuous_ofReal.comp
        ((Complex.continuous_re.comp ha).min (Complex.continuous_re.comp hb))⟩

@[simp]
lemma character_inf (a b : A) (χ : WeakDual.characterSpace ℂ A) :
    χ (inf a b) = ((min (χ a).re (χ b).re : ℝ) : ℂ) := by
  change gelfandStarTransform A (inf a b) χ = _
  rw [inf, StarAlgEquiv.apply_symm_apply]
  rfl

lemma isSelfAdjoint_inf (a b : A) : IsSelfAdjoint (inf a b) :=
  ext_character fun χ => by
    rw [← character_apply, map_star, character_apply, character_inf, Complex.star_def,
      Complex.conj_ofReal]

/-! ## B. Order through characters -/

variable [PartialOrder A] [StarOrderedRing A]

/-- **Characters detect positivity.** -/
lemma nonneg_iff_forall_character {a : A} :
    0 ≤ a ↔ ∀ χ : WeakDual.characterSpace ℂ A, 0 ≤ χ a := by
  rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℂ) a]
  simp only [WeakDual.CharacterSpace.mem_spectrum_iff_exists, forall_exists_index,
    forall_apply_eq_imp_iff]

/-- Characters detect the order between self-adjoint elements. -/
lemma le_iff_forall_character {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    a ≤ b ↔ ∀ χ : WeakDual.characterSpace ℂ A, (χ a).re ≤ (χ b).re := by
  rw [← sub_nonneg, nonneg_iff_forall_character]
  refine forall_congr' fun χ => ?_
  rw [map_sub, character_eq_re ha χ, character_eq_re hb χ, ← Complex.ofReal_sub,
    Complex.zero_le_real, sub_nonneg]
  simp only [Complex.ofReal_re]

/-! ## C. Classicality -/

/-- **Riesz decomposition.** A nonnegative observable below a sum of two nonnegative observables
splits, character by character, into two pieces below the summands. -/
lemma hasRieszDecomposition : HasRieszDecomposition (selfAdjoint A) := by
  intro f₁ f₂ g hf₁ hf₂ hg
  have sa := fun x : selfAdjoint A => x.2
  let g₁ : selfAdjoint A := ⟨inf g f₁, isSelfAdjoint_inf _ _⟩
  have le := fun (x y : selfAdjoint A) => le_iff_forall_character (A := A) (sa x) (sa y)
  have h0 := fun x : selfAdjoint A => le 0 x
  simp only [ZeroMemClass.coe_zero, map_zero, Complex.zero_re] at h0
  refine ⟨g₁, ⟨(h0 _).2 fun χ => ?_, (le _ _).2 fun χ => ?_⟩,
    ⟨(h0 _).2 fun χ => ?_, (le _ _).2 fun χ => ?_⟩⟩
  · simpa [g₁] using ⟨(h0 g).1 hg.1 χ, (h0 f₁).1 hf₁ χ⟩
  · simp [g₁]
  · simp [g₁]
  · have := (le g (f₁ + f₂)).1 hg.2 χ
    simp only [AddMemClass.coe_add, map_add, Complex.add_re] at this
    simp only [g₁, AddSubgroupClass.coe_sub, map_sub, Complex.sub_re, character_inf,
      Complex.ofReal_re]
    rcases min_cases (χ g).re (χ f₁).re with h | h <;> linarith [(h0 f₂).1 hf₂ χ]

/-- **The observables of a commutative C⋆-algebra form a classical system.** -/
lemma isClassical : IsClassical (selfAdjoint A) :=
  hasRieszDecomposition.hasLatticeDualCone

end CommCStarAlgebra

