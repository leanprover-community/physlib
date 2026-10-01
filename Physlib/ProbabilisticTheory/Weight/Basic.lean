/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.OrderUnit.Cone

/-!
# Weights

## i. Overview

A state assigns each positive observable a nonnegative expectation value, normalized so the
certain outcome reads exactly `1`. A *weight* generalizes this by dropping the normalization and
letting the values be extended nonnegative reals, possibly `+∞`. This matters especially in
infinite dimensions: the trace on `B(H)` is only finite on the trace-class operators and genuinely
diverges to `+∞` elsewhere. A state is then the special case that happens to be finite everywhere
and normalized.

## ii. Key results

- `Weight.mono` : weights are monotone on the positive cone.
- `Weight.IsFinite.isSemifinite` : a finite weight is automatically semifinite.
- `Weight.IsFinite.normalize_isState` : rescaling a finite weight that's nonzero at the order unit
  turns it into a state.

## iii. Table of contents

- A. Weights
- B. States as weights

## iv. References

- G. Ludwig, *Foundations of Quantum Mechanics I*, Springer, 1983.
  <https://link.springer.com/book/10.1007/978-3-642-86751-4>

-/

@[expose] public section

open scoped ENNReal NNReal

/-!

## A. Weights

-/

/-- An extended nonnegative linear functional on the positive cone. -/
abbrev Weight (E : Type*) [OrderedVectorSpace E] := PosCone E →ₗ[ℝ≥0] ℝ≥0∞

namespace Weight

section OrderedVectorSpace

variable {E : Type*} [OrderedVectorSpace E]

@[ext]
lemma ext {w₁ w₂ : Weight E} (h : ∀ A, w₁ A = w₂ A) : w₁ = w₂ :=
  LinearMap.ext h

/-- Only the zero positive element has weight zero. -/
def IsFaithful (w : Weight E) : Prop := ∀ A : PosCone E, w A = 0 → A = 0

/-- A weight has no infinite values. -/
def IsFinite (w : Weight E) : Prop := ∀ A : PosCone E, w A ≠ ⊤

/-- A weight is the supremum of its finite values below each positive element. -/
def IsSemifinite (w : Weight E) : Prop := ∀ A : PosCone E,
  w A = ⨆ B : {B : PosCone E // B ≤ A ∧ w B ≠ ⊤}, w B

/-- Weights are monotone on the positive cone. -/
lemma mono (w : Weight E) : Monotone (w : PosCone E → ℝ≥0∞) := by
  intro A B hAB
  have hC : (0 : E) ≤ (B : E) - (A : E) := sub_nonneg.mpr hAB
  have hAC : A + (⟨(B : E) - (A : E), hC⟩ : PosCone E) = B :=
    Subtype.ext (show (A : E) + ((B : E) - (A : E)) = B from by abel)
  rw [← hAC, map_add]
  exact le_self_add

/-- A finite weight is semifinite. -/
lemma IsFinite.isSemifinite {w : Weight E} (hw : w.IsFinite) : w.IsSemifinite := fun A =>
  le_antisymm (le_iSup_of_le ⟨A, le_rfl, hw A⟩ le_rfl) (iSup_le fun B => w.mono B.2.1)

/-- A finite weight's real value is additive. -/
lemma IsFinite.toReal_map_add {w : Weight E} (hw : w.IsFinite) (A B : PosCone E) :
    (w (A + B)).toReal = (w A).toReal + (w B).toReal := by
  rw [w.map_add, ENNReal.toReal_add (hw A) (hw B)]

/-- A weight's real value scales linearly under nonnegative real scaling. -/
lemma toReal_map_nnreal_smul (w : Weight E) (k : ℝ≥0) (A : PosCone E) :
    (w (k • A)).toReal = k * (w A).toReal := by
  rw [w.map_smul, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]

/-- A weight is normal when it preserves least upper bounds of increasing sequences in the
positive cone. -/
def IsNormal (w : Weight E) : Prop := ∀ (f : ℕ → PosCone E) (A : PosCone E),
  Monotone f → IsLUB (Set.range f) A → IsLUB (Set.range (w ∘ f)) (w A)

end OrderedVectorSpace

/-!

## B. States as weights

-/

section OrderUnitSpace

variable {E : Type*} [OrderUnitSpace E]

/-- A weight that's finite everywhere and gives the certain outcome weight exactly `1`. -/
structure IsState (w : Weight E) : Prop where
  /-- A state is finite everywhere. -/
  finite : w.IsFinite
  /-- A state gives the certain outcome weight exactly `1`. -/
  normalized : w 1 = 1

/-- Rescale a weight by the inverse of its value at the order unit. -/
noncomputable def normalize (w : Weight E) : Weight E where
  toFun A := (w 1)⁻¹ * w A
  map_add' A B := by rw [map_add, mul_add]
  map_smul' c A := by
    simp only [map_smul, ENNReal.smul_def, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] lemma normalize_apply (w : Weight E) (A : PosCone E) :
    normalize w A = (w 1)⁻¹ * w A := rfl

/-- Normalizing a finite weight that's nonzero at the order unit keeps it finite. -/
lemma IsFinite.normalize_isFinite {w : Weight E} (hw : w.IsFinite) (h : w 1 ≠ 0) :
    (normalize w).IsFinite := fun A =>
  ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr h) (hw A)

/-- Normalizing a finite weight that's nonzero at the order unit makes it a state: the order unit
is scaled to weight exactly `1`. -/
lemma IsFinite.normalize_isState {w : Weight E} (hw : w.IsFinite) (h : w 1 ≠ 0) :
    (normalize w).IsState where
  finite := hw.normalize_isFinite h
  normalized := ENNReal.inv_mul_cancel h (hw 1)

end OrderUnitSpace

end Weight
