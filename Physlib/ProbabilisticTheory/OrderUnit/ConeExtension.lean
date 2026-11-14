/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.OrderUnit.Cone

/-!
# Linear extension from positive observables

An additive homogeneous map on positive observables extends to their real span.

## i. Overview

Every observable is a difference of two positive observables. Sending a difference `p - q`
to `f p - f q` defines a real-linear map independent of the chosen decomposition.

## ii. Key results

- `PosCone.extend` : extend a real-valued map from positive observables.
- `PosCone.extend_coe` : agreement on the positive cone.

## iii. Table of contents

- A. Extension from the positive cone

## iv. References

-/

@[expose] public section

open ProbabilisticTheory
open scoped NNReal

/-! ## A. Extension from the positive cone -/

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

/-- The `ℝ`-linear extension of an `ℝ≥0`-linear map on an order unit space's positive cone. -/
noncomputable def extend : P.Observables →ₗ[ℝ] ℝ where
  toFun := extendFun f
  map_add' A B := by
    obtain ⟨p, q, rfl⟩ := exists_sub A
    obtain ⟨p', q', rfl⟩ := exists_sub B
    rw [extendFun_eq f rfl, extendFun_eq f rfl,
      extendFun_eq f (p := p + p') (q := q + q') (by simp only [Submodule.coe_add]; abel),
      map_add, map_add]
    ring
  map_smul' t A := by
    obtain ⟨p, q, rfl⟩ := exists_sub A
    rw [extendFun_eq f rfl, RingHom.id_apply, smul_eq_mul]
    rcases le_total 0 t with ht | ht
    · lift t to ℝ≥0 using ht
      rw [extendFun_eq f (p := t • p) (q := t • q) (by simp [smul_sub]), map_smul, map_smul]
      simp [NNReal.smul_def, mul_sub]
    · lift -t to ℝ≥0 using neg_nonneg.mpr ht with s hs
      rw [extendFun_eq f (p := s • q) (q := s • p) (by simp only [coe_nnreal_smul, hs]; module),
        map_smul, map_smul, NNReal.smul_def, NNReal.smul_def, smul_eq_mul, smul_eq_mul, hs]
      ring

@[simp]
lemma extend_apply {p q : PosCone P} : extend f ((p : P.Observables) - q) = f p - f q :=
  extendFun_eq f rfl

@[simp]
lemma extend_coe (p : PosCone P) : extend f (p : P.Observables) = f p := by
  simpa using extend_apply f (p := p) (q := 0)

end ProbabilisticTheory.PosCone
