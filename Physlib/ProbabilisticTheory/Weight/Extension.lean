/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Weight.Basic

/-!
# Extending finite weights

## i. Overview

An `ℝ≥0`-linear map on the positive cone extends uniquely to an `ℝ`-linear map on the whole space
as soon as every element is a difference `P - Q` of positive elements: send `P - Q` to
`f P - f Q`. In an order-unit space every element is such a difference, so a finite weight extends
to a positive linear functional.

## ii. Key results

- `PosCone.extend` : the `ℝ`-linear extension of an `ℝ≥0`-linear map on the positive cone.
- `Weight.IsFinite.toLinearMap` : the `ℝ`-linear map extending a finite weight to all of `E`.

## iii. Table of contents

- A. Extension from the positive cone
- B. Extending finite weights

## iv. References

-/

@[expose] public section

open ProbabilisticTheory

open scoped NNReal

/-!

## A. Extension from the positive cone

-/

namespace PosCone

variable {E : Type*} [OrderUnitSpace E] (f : PosCone E →ₗ[ℝ≥0] ℝ)

@[simp]
lemma coe_nnreal_smul (t : ℝ≥0) (P : PosCone E) : ((t • P : PosCone E) : E) = (t : ℝ) • (P : E) :=
  rfl

/-- `P - Q ↦ f P - f Q` does not depend on how an element is written as a difference. -/
lemma map_sub_eq_map_sub {P Q P' Q' : PosCone E} (h : (P : E) - Q = P' - Q') :
    f P - f Q = f P' - f Q' := by
  rw [sub_eq_sub_iff_add_eq_add] at *
  rw [← Submodule.coe_add, ← Submodule.coe_add, Subtype.val_inj] at h
  simpa using congrArg f h

/-- In an order unit space, every element is a difference of positive elements. -/
lemma exists_sub (A : E) : ∃ P Q : PosCone E, (P : E) - Q = A := by
  obtain ⟨P, Q, hP, hQ, rfl⟩ := OrderUnitSpace.exists_eq_sub_nonneg A
  exact ⟨⟨P, hP⟩, ⟨Q, hQ⟩, rfl⟩

/-- The value of the extension, computed from a chosen decomposition `A = P - Q`. -/
noncomputable def extendFun (A : E) : ℝ :=
  f (exists_sub A).choose - f (exists_sub A).choose_spec.choose

lemma extendFun_eq {A : E} {P Q : PosCone E} (h : (P : E) - Q = A) :
    extendFun f A = f P - f Q :=
  map_sub_eq_map_sub f ((exists_sub A).choose_spec.choose_spec.trans h.symm)

/-- The `ℝ`-linear extension of an `ℝ≥0`-linear map on an order unit space's positive cone. -/
noncomputable def extend : E →ₗ[ℝ] ℝ where
  toFun := extendFun f
  map_add' A B := by
    obtain ⟨P, Q, rfl⟩ := exists_sub A
    obtain ⟨P', Q', rfl⟩ := exists_sub B
    rw [extendFun_eq f rfl, extendFun_eq f rfl,
      extendFun_eq f (P := P + P') (Q := Q + Q') (by simp only [Submodule.coe_add]; abel),
      map_add, map_add]
    ring
  map_smul' t A := by
    obtain ⟨P, Q, rfl⟩ := exists_sub A
    rw [extendFun_eq f rfl, RingHom.id_apply, smul_eq_mul]
    rcases le_total 0 t with ht | ht
    · lift t to ℝ≥0 using ht
      rw [extendFun_eq f (P := t • P) (Q := t • Q) (by simp [smul_sub]), map_smul, map_smul]
      simp [NNReal.smul_def, mul_sub]
    · lift -t to ℝ≥0 using neg_nonneg.mpr ht with s hs
      rw [extendFun_eq f (P := s • Q) (Q := s • P) (by simp only [coe_nnreal_smul, hs]; module),
        map_smul, map_smul, NNReal.smul_def, NNReal.smul_def, smul_eq_mul, smul_eq_mul, hs]
      ring

@[simp]
lemma extend_apply {P Q : PosCone E} : extend f ((P : E) - Q) = f P - f Q :=
  extendFun_eq f rfl

@[simp]
lemma extend_coe (P : PosCone E) : extend f (P : E) = f P := by
  simpa using extend_apply f (P := P) (Q := 0)

end PosCone

/-!

## B. Extending finite weights

-/

namespace Weight

section OrderedVectorSpace

variable {E : Type*} [OrderedVectorSpace E] {w : Weight E}

/-- A finite weight, read as a real-valued `ℝ≥0`-linear map on the positive cone. -/
noncomputable def IsFinite.toReal (hw : w.IsFinite) : PosCone E →ₗ[ℝ≥0] ℝ where
  toFun A := (w A).toReal
  map_add' := hw.toReal_map_add
  map_smul' := w.toReal_map_nnreal_smul

@[simp]
lemma IsFinite.toReal_apply (hw : w.IsFinite) (A : PosCone E) : hw.toReal A = (w A).toReal := rfl

end OrderedVectorSpace

section OrderUnitSpace

variable {E : Type*} [OrderUnitSpace E] {w : Weight E}

/-- The `ℝ`-linear map extending a finite weight. -/
noncomputable def IsFinite.toLinearMap (hw : w.IsFinite) : E →ₗ[ℝ] ℝ :=
  PosCone.extend hw.toReal

@[simp]
lemma IsFinite.toLinearMap_coe (hw : w.IsFinite) (A : PosCone E) :
    hw.toLinearMap (A : E) = (w A).toReal := by
  simp [toLinearMap]

end OrderUnitSpace

end Weight
