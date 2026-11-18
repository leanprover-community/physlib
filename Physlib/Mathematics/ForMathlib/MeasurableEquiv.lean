/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# The group of measurable automorphisms

Measurable bijections of a measurable space with measurable inverse form a group.

## i. Overview

Composition of measurable automorphisms is again a measurable automorphism, the identity is the
unit and the inverse map is the group inverse. The product `φ * ψ` applies `ψ` first, as for
permutations.

## ii. Key results

- `MeasurableEquiv.instGroup` : the group of measurable automorphisms.

## iii. Table of contents

- A. Group structure

## iv. References

-/

@[expose] public section

namespace MeasurableEquiv

variable {α : Type*} [MeasurableSpace α]

/-! ## A. Group structure -/

/-- Measurable automorphisms form a group under composition. -/
instance instGroup : Group (α ≃ᵐ α) where
  mul φ ψ := ψ.trans φ
  one := refl α
  inv := symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel φ := ext φ.symm_comp_self

@[simp]
lemma mul_apply (φ ψ : α ≃ᵐ α) (x : α) : (φ * ψ) x = φ (ψ x) := rfl

@[simp]
lemma one_apply (x : α) : (1 : α ≃ᵐ α) x = x := rfl

@[simp]
lemma inv_def (φ : α ≃ᵐ α) : φ⁻¹ = φ.symm := rfl

end MeasurableEquiv
