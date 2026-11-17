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

/-- `f p - f q` depends only on the difference `p - q`. -/
lemma map_sub_eq_map_sub {A : P.Observables} {p q p' q' : PosCone P}
    (h : (p : P.Observables) - q = A) (h' : (p' : P.Observables) - q' = A) :
    f p - f q = f p' - f q' := by
  rw [← h', sub_eq_sub_iff_add_eq_add, ← Submodule.coe_add, ← Submodule.coe_add,
    Subtype.val_inj] at h
  rw [sub_eq_sub_iff_add_eq_add, ← map_add, ← map_add, h]

/-- Extend values on positive observables by `f (p - q) = f p - f q`. -/
noncomputable def extend : P.Observables →ₗ[ℝ] ℝ where
  toFun A := f (exists_sub A).choose - f (exists_sub A).choose_spec.choose
  map_add' A B := by
    obtain ⟨p, q, hA⟩ := exists_sub A
    obtain ⟨p', q', hB⟩ := exists_sub B
    rw [map_sub_eq_map_sub f (exists_sub A).choose_spec.choose_spec hA,
      map_sub_eq_map_sub f (exists_sub B).choose_spec.choose_spec hB,
      map_sub_eq_map_sub f (exists_sub (A + B)).choose_spec.choose_spec (p' := p + p')
        (q' := q + q') (by rw [← hA, ← hB, Submodule.coe_add, Submodule.coe_add]; abel)]
    simp only [map_add]
    ring
  map_smul' t A := by
    obtain ⟨p, q, hA⟩ := exists_sub A
    have ht : (t.toNNReal : ℝ) - (-t).toNNReal = t := max_zero_sub_max_neg_zero_eq_self t
    rw [map_sub_eq_map_sub f (exists_sub A).choose_spec.choose_spec hA,
      map_sub_eq_map_sub f (exists_sub (t • A)).choose_spec.choose_spec
        (p' := t.toNNReal • p + (-t).toNNReal • q) (q' := t.toNNReal • q + (-t).toNNReal • p)
        (by conv_rhs => rw [← hA, ← ht]
            simp only [Submodule.coe_add, coe_nnreal_smul]; module)]
    simp only [map_add, map_smul, NNReal.smul_def, smul_eq_mul, RingHom.id_apply]
    linear_combination (f p - f q) * ht

/-! ## B. Agreement and uniqueness -/

/-- The extension sends a difference `p - q` of positive observables to `f p - f q`. -/
@[simp]
lemma extend_apply {p q : PosCone P} : extend f ((p : P.Observables) - q) = f p - f q :=
  map_sub_eq_map_sub f (exists_sub _).choose_spec.choose_spec rfl

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
