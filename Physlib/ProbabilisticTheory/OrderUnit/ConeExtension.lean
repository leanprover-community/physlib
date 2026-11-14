/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.OrderUnit.Cone

/-!
# Linear extension from positive observables

Values on positive observables determine a real-linear functional on all observables.

## i. Overview

Every observable is a difference of two positive observables. Sending a difference `p - q`
to `f p - f q` defines a real-linear map independent of the chosen decomposition.

## ii. Key results

- `PosCone.extend` : extend a real-valued map from positive observables.
- `PosCone.extend_coe` : agreement on the positive cone.
- `PosCone.extend_unique` : uniqueness among real-linear functionals with those values.

## iii. Table of contents

- A. Independence of the positive decomposition
- B. Linearity of the extension
- C. Agreement and uniqueness

## iv. References

-/

@[expose] public section

open ProbabilisticTheory
open scoped NNReal

/-! ## A. Independence of the positive decomposition -/

namespace ProbabilisticTheory.PosCone

variable {P : ProbabilisticTheory} (f : PosCone P →ₗ[ℝ≥0] ℝ)

/-- `p - q ↦ f p - f q` does not depend on how an element is written as a difference. -/
lemma map_sub_eq_map_sub {p q p' q' : PosCone P} (h : (p : P.Observables) - q = p' - q') :
    f p - f q = f p' - f q' := by
  rw [sub_eq_sub_iff_add_eq_add] at *
  rw [← Submodule.coe_add, ← Submodule.coe_add, Subtype.val_inj] at h
  simpa using congrArg f h

/-- In an order unit space, every element is a difference of positive elements. -/
lemma exists_sub (A : P.Observables) : ∃ p q : PosCone P, (p : P.Observables) - q = A := by
  obtain ⟨p, q, hP, hQ, rfl⟩ := ProbabilisticTheory.exists_eq_sub_nonneg A
  exact ⟨⟨p, hP⟩, ⟨q, hQ⟩, rfl⟩

/-- The value of the extension, computed from a chosen decomposition `A = p - q`. -/
noncomputable def extendFun (A : P.Observables) : ℝ :=
  f (exists_sub A).choose - f (exists_sub A).choose_spec.choose

lemma extendFun_eq {A : P.Observables} {p q : PosCone P} (h : (p : P.Observables) - q = A) :
    extendFun f A = f p - f q :=
  map_sub_eq_map_sub f ((exists_sub A).choose_spec.choose_spec.trans h.symm)

/-! ## B. Linearity of the extension -/

lemma extendFun_add (A B : P.Observables) :
    extendFun f (A + B) = extendFun f A + extendFun f B := by
  obtain ⟨p, q, rfl⟩ := exists_sub A
  obtain ⟨p', q', rfl⟩ := exists_sub B
  rw [extendFun_eq f rfl, extendFun_eq f rfl,
    extendFun_eq f (p := p + p') (q := q + q') (by simp only [Submodule.coe_add]; abel),
    map_add, map_add]
  ring

lemma extendFun_neg (A : P.Observables) : extendFun f (-A) = -extendFun f A := by
  obtain ⟨p, q, rfl⟩ := exists_sub A
  rw [extendFun_eq f rfl, extendFun_eq f (p := q) (q := p) (by abel)]
  ring

lemma extendFun_nnreal_smul (t : ℝ≥0) (A : P.Observables) :
    extendFun f ((t : ℝ) • A) = (t : ℝ) • extendFun f A := by
  obtain ⟨p, q, rfl⟩ := exists_sub A
  rw [extendFun_eq f rfl,
    extendFun_eq f (p := t • p) (q := t • q) (by simp [smul_sub]), map_smul, map_smul]
  simp [NNReal.smul_def, mul_sub]

lemma extendFun_smul (t : ℝ) (A : P.Observables) :
    extendFun f (t • A) = t • extendFun f A := by
  rcases le_total 0 t with ht | ht
  · exact extendFun_nnreal_smul f ⟨t, ht⟩ A
  · have h := extendFun_nnreal_smul f ⟨-t, neg_nonneg.mpr ht⟩ A
    change extendFun f ((-t) • A) = (-t) • extendFun f A at h
    simpa only [neg_smul, extendFun_neg, neg_inj] using h

/-- Extend values on positive observables by `f (p - q) = f p - f q`. -/
noncomputable def extend : P.Observables →ₗ[ℝ] ℝ where
  toFun := extendFun f
  map_add' := extendFun_add f
  map_smul' := extendFun_smul f

/-! ## C. Agreement and uniqueness -/

@[simp]
lemma extend_apply {p q : PosCone P} : extend f ((p : P.Observables) - q) = f p - f q :=
  extendFun_eq f rfl

@[simp]
lemma extend_coe (p : PosCone P) : extend f (p : P.Observables) = f p := by
  simpa using extend_apply f (p := p) (q := 0)

/-- Agreement on positive observables determines the real-linear extension. -/
lemma extend_unique (g : P.Observables →ₗ[ℝ] ℝ)
    (h : ∀ p : PosCone P, g (p : P.Observables) = f p) : g = extend f := by
  ext A
  obtain ⟨p, q, rfl⟩ := exists_sub A
  rw [map_sub, h p, h q, extend_apply]

end ProbabilisticTheory.PosCone
