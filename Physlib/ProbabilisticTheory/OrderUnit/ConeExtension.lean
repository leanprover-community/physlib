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

Every observable is a difference `p - q` of two positive observables. A map `f` that is additive
and nonnegatively homogeneous on positive observables extends to all observables by sending
`p - q` to `f p - f q`. The value does not depend on the chosen decomposition. The extension is
real-linear and it is the only real-linear map that agrees with `f` on positive observables.

## ii. Key results

- `PosCone.extend` : extend a real-valued map from positive observables.
- `PosCone.extend_sub` : the extension sends every difference `p - q` to `f p - f q`.
- `PosCone.extendₗ` : the extension as a real-linear map.
- `PosCone.extendₗ_unique` : uniqueness among real-linear maps with those values.

## iii. Table of contents

- A. The extension
- B. Linearity
- C. Agreement and uniqueness

## iv. References

-/

@[expose] public section

open ProbabilisticTheory
open scoped NNReal

/-! ## A. The extension -/

namespace ProbabilisticTheory.PosCone

variable {P : ProbabilisticTheory} (f : PosCone P →ₗ[ℝ≥0] ℝ)

/-- Extend values on positive observables by `f (p - q) = f p - f q`, for a chosen decomposition
of each observable into positive parts. -/
noncomputable def extend (A : P.Observables) : ℝ :=
  f (exists_sub A).choose - f (exists_sub A).choose_spec.choose

/-- The extension gives `f p - f q` for every decomposition `A = p - q`. -/
lemma extend_sub {A : P.Observables} {p q : PosCone P} (h : (p : P.Observables) - q = A) :
    extend f A = f p - f q := by
  have h' := (exists_sub A).choose_spec.choose_spec.trans h.symm
  rw [sub_eq_sub_iff_add_eq_add, ← Submodule.coe_add, ← Submodule.coe_add,
    Subtype.val_inj] at h'
  rw [extend, sub_eq_sub_iff_add_eq_add, ← map_add, ← map_add, h']

/-! ## B. Linearity -/

/-- The extension is additive. -/
lemma extend_add (A B : P.Observables) : extend f (A + B) = extend f A + extend f B := by
  obtain ⟨p, q, rfl⟩ := exists_sub A
  obtain ⟨p', q', rfl⟩ := exists_sub B
  rw [extend_sub f rfl, extend_sub f rfl, extend_sub f (p := p + p') (q := q + q')
    (by simp only [Submodule.coe_add]; abel), map_add, map_add]
  ring

/-- The extension is homogeneous for every real scalar. -/
lemma extend_smul (t : ℝ) (A : P.Observables) : extend f (t • A) = t * extend f A := by
  obtain ⟨p, q, rfl⟩ := exists_sub A
  have ht : (t.toNNReal : ℝ) - (-t).toNNReal = t := max_zero_sub_max_neg_zero_eq_self t
  have hA : ((t.toNNReal • p + (-t).toNNReal • q : PosCone P) : P.Observables) -
      (t.toNNReal • q + (-t).toNNReal • p : PosCone P) = t • ((p : P.Observables) - q) := by
    conv_rhs => rw [← ht]
    simp only [Submodule.coe_add, coe_nnreal_smul]; module
  rw [extend_sub f rfl, extend_sub f hA]
  simp only [map_add, map_smul, NNReal.smul_def, smul_eq_mul]
  linear_combination (f p - f q) * ht

/-- The extension as a real-linear map. -/
noncomputable def extendₗ : P.Observables →ₗ[ℝ] ℝ where
  toFun := extend f
  map_add' := extend_add f
  map_smul' := extend_smul f

/-! ## C. Agreement and uniqueness -/

/-- The linear extension evaluates as the extension. -/
@[simp]
lemma extendₗ_apply (A : P.Observables) : extendₗ f A = extend f A := rfl

/-- The extension agrees with `f` on positive observables. -/
@[simp]
lemma extend_coe (p : PosCone P) : extend f (p : P.Observables) = f p := by
  simpa using extend_sub f (p := p) (q := 0) (sub_zero _)

/-- Agreement on positive observables determines the real-linear extension. -/
lemma extendₗ_unique (g : P.Observables →ₗ[ℝ] ℝ)
    (h : ∀ p : PosCone P, g (p : P.Observables) = f p) : g = extendₗ f := by
  ext A
  obtain ⟨p, q, rfl⟩ := exists_sub A
  rw [map_sub, h p, h q, extendₗ_apply, extend_sub f rfl]

end ProbabilisticTheory.PosCone
