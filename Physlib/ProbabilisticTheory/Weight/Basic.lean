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

- `Weight.monotone` : weights are monotone on the positive cone.
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

open ProbabilisticTheory

open scoped ENNReal NNReal

/-!

## A. Weights

-/

/-- An extended nonnegative linear functional on the positive cone. -/
abbrev Weight (P : ProbabilisticTheory) := PosCone P →ₗ[ℝ≥0] ℝ≥0∞

namespace Weight

variable {P : ProbabilisticTheory}

/-- Only the zero positive element has weight zero. -/
def IsFaithful (w : Weight P) : Prop := ∀ A : PosCone P, w A = 0 → A = 0

/-- A weight has no infinite values. -/
def IsFinite (w : Weight P) : Prop := ∀ A : PosCone P, w A ≠ ⊤

/-- A weight is the supremum of its finite values below each positive element. -/
def IsSemifinite (w : Weight P) : Prop := ∀ A : PosCone P,
  w A = ⨆ B : {B : PosCone P // B ≤ A ∧ w B ≠ ⊤}, w B

/-- Weights are monotone on the positive cone. -/
lemma monotone (w : Weight P) : Monotone w := by
  intro A B hAB
  have hAC : A + ⟨(B : P.Observables) - (A : P.Observables), sub_nonneg.mpr hAB⟩ = B := by
    ext; rw [Submodule.coe_add, add_sub_cancel]
  rw [← hAC, map_add]
  exact le_self_add

/-- A finite weight is semifinite. -/
lemma IsFinite.isSemifinite {w : Weight P} (hw : w.IsFinite) : w.IsSemifinite := fun A =>
  le_antisymm (le_iSup_of_le ⟨A, le_rfl, hw A⟩ le_rfl) (iSup_le fun B => w.monotone B.2.1)

/-- A finite weight's real value is additive. -/
lemma IsFinite.toReal_map_add {w : Weight P} (hw : w.IsFinite) (A B : PosCone P) :
    (w (A + B)).toReal = (w A).toReal + (w B).toReal := by
  rw [w.map_add, ENNReal.toReal_add (hw A) (hw B)]

/-- A weight's real value scales linearly under nonnegative real scaling. -/
lemma toReal_map_nnreal_smul (w : Weight P) (k : ℝ≥0) (A : PosCone P) :
    (w (k • A)).toReal = k * (w A).toReal := by
  simp [ENNReal.smul_def]

/-- A weight is normal when it preserves least upper bounds of increasing sequences in the
positive cone. -/
def IsNormal (w : Weight P) : Prop := ∀ (f : ℕ → PosCone P) (A : PosCone P),
  Monotone f → IsLUB (Set.range f) A → IsLUB (Set.range (w ∘ f)) (w A)

/-!

## B. States as weights

-/

/-- A weight that's finite everywhere and gives the certain outcome weight exactly `1`. -/
structure IsState (w : Weight P) : Prop where
  /-- A state is finite everywhere. -/
  finite : w.IsFinite
  /-- A state gives the certain outcome weight exactly `1`. -/
  normalized : w 1 = 1

/-- Rescale a weight by the inverse of its value at the order unit. -/
noncomputable def normalize (w : Weight P) : Weight P where
  toFun A := (w 1)⁻¹ * w A
  map_add' A B := by rw [map_add, mul_add]
  map_smul' c A := by simp

@[simp] lemma normalize_apply (w : Weight P) (A : PosCone P) :
    normalize w A = (w 1)⁻¹ * w A := rfl

/-- Normalizing a finite weight that's nonzero at the order unit keeps it finite. -/
lemma IsFinite.normalize_isFinite {w : Weight P} (hw : w.IsFinite) (h : w 1 ≠ 0) :
    (normalize w).IsFinite :=
  fun A => ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr h) (hw A)

/-- Normalizing a finite weight that's nonzero at the order unit makes it a state: the order unit
is scaled to weight exactly `1`. -/
lemma IsFinite.normalize_isState {w : Weight P} (hw : w.IsFinite) (h : w 1 ≠ 0) :
    (normalize w).IsState where
  finite := hw.normalize_isFinite h
  normalized := ENNReal.inv_mul_cancel h (hw 1)

end Weight
