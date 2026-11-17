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

- A. The extension
- B. Agreement and uniqueness

## iv. References

-/

@[expose] public section

open ProbabilisticTheory
open scoped NNReal

/-! ## A. The extension -/

namespace ProbabilisticTheory.PosCone

variable {P : ProbabilisticTheory} (f : PosCone P →ₗ[ℝ≥0] ℝ)

/-- In an order unit space, every element is a difference of positive elements. -/
lemma exists_sub (A : P.Observables) : ∃ p q : PosCone P, (p : P.Observables) - q = A := by
  obtain ⟨p, q, hP, hQ, rfl⟩ := ProbabilisticTheory.exists_eq_sub_nonneg A
  exact ⟨⟨p, hP⟩, ⟨q, hQ⟩, rfl⟩

/-- `p - q ↦ f p - f q` does not depend on how an element is written as a difference. -/
lemma map_sub_eq_map_sub {p q p' q' : PosCone P} (h : (p : P.Observables) - q = p' - q') :
    f p - f q = f p' - f q' := by
  rw [sub_eq_sub_iff_add_eq_add] at *
  rw [← Submodule.coe_add, ← Submodule.coe_add, Subtype.val_inj] at h
  simpa using congrArg f h

/-- Extend values on positive observables by `f (p - q) = f p - f q`. -/
noncomputable def extend : P.Observables →ₗ[ℝ] ℝ where
  toFun A := f (exists_sub A).choose - f (exists_sub A).choose_spec.choose
  map_add' A B := by
    obtain ⟨p, q, hA⟩ := exists_sub A
    obtain ⟨p', q', hB⟩ := exists_sub B
    rw [map_sub_eq_map_sub f ((exists_sub A).choose_spec.choose_spec.trans hA.symm),
      map_sub_eq_map_sub f ((exists_sub B).choose_spec.choose_spec.trans hB.symm),
      map_sub_eq_map_sub f (p' := p + p') (q' := q + q')
        ((exists_sub (A + B)).choose_spec.choose_spec.trans
          (by rw [← hA, ← hB]; simp only [Submodule.coe_add]; abel)),
      map_add, map_add]
    ring
  map_smul' t A := by
    obtain ⟨p, q, hA⟩ := exists_sub A
    rw [map_sub_eq_map_sub f ((exists_sub A).choose_spec.choose_spec.trans hA.symm)]
    rcases le_total 0 t with ht | ht
    · lift t to ℝ≥0 using ht
      rw [map_sub_eq_map_sub f (p' := t • p) (q' := t • q)
        ((exists_sub _).choose_spec.choose_spec.trans (by rw [← hA]; simp [smul_sub])),
        map_smul, map_smul]
      simp [NNReal.smul_def, mul_sub]
    · lift -t to ℝ≥0 using neg_nonneg.mpr ht with s hs
      rw [map_sub_eq_map_sub f (p' := s • q) (q' := s • p)
        ((exists_sub _).choose_spec.choose_spec.trans
          (by rw [← hA, ← neg_neg t, ← hs]; simp [smul_sub]; abel)),
        map_smul, map_smul, show t = -(s : ℝ) by linarith]
      simp only [NNReal.smul_def, smul_eq_mul, RingHom.id_apply]
      ring

/-! ## B. Agreement and uniqueness -/

/-- The extension sends a difference `p - q` of positive observables to `f p - f q`. -/
@[simp]
lemma extend_apply {p q : PosCone P} : extend f ((p : P.Observables) - q) = f p - f q :=
  map_sub_eq_map_sub f ((exists_sub _).choose_spec.choose_spec)

/-- The extension agrees with `f` on positive observables. -/
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
