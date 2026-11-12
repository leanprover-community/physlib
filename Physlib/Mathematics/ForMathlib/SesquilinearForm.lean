/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Star

/-!

# Positive-definite sesquilinear forms

A sesquilinear form is positive-definite when it is symmetric and strictly positive on nonzero
vectors.

## i. Overview

Mathlib has positive-semidefinite sesquilinear forms (`LinearMap.IsPosSemidef`) and
positive-definite matrices (`Matrix.PosDef`), but no positive-definite sesquilinear forms.
`LinearMap.IsPosDef` fills this gap with the shape of `LinearMap.IsPosSemidef`: a structure
extending `LinearMap.IsSymm`. For a form `M →ₗ⋆[R] M →ₗ[R] R` symmetry is Hermiticity,
`star (B x y) = B y x`. A positive-definite form is positive-semidefinite and nondegenerate, and
in a basis it is positive-definite exactly when its matrix is. Symmetry and positive-definiteness
transfer along a surjective linear map that turns one form into the conjugate of the
other, as for the inverse of a Hermitian metric.

## ii. Key results

- `LinearMap.IsPosDef` : a sesquilinear form is symmetric and `0 < B x x` for `x ≠ 0`.
- `LinearMap.IsPosDef.isPosSemidef` : a positive-definite form is positive-semidefinite.
- `LinearMap.IsPosDef.nondegenerate` : a positive-definite form is nondegenerate.
- `LinearMap.IsSymm.of_comp_star` and `LinearMap.IsPosDef.of_comp_star` : a form `B'` with
  `B' (A x) (A y) = star (B y x)` for a surjective `A` is symmetric or
  positive-definite when `B` is.
- `LinearMap.isPosDef_iff_posDef_toMatrix` : a form is positive-definite exactly when its matrix in
  a basis is.

## iii. Table of contents

- A. Positive-definite sesquilinear forms
  - A.1. The definition
  - A.2. Consequences over a preorder
  - A.3. Transport along a linear map
  - A.4. The matrix of a positive-definite form

## iv. References

- `LinearMap.IsPosSemidef` and `LinearMap.IsSymm`, in
  `Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean`;
- `Matrix.PosDef`, in `Mathlib/LinearAlgebra/Matrix/PosDef.lean`.

-/

@[expose] public section

open Module Matrix
open scoped Matrix

/-!

## A. Positive-definite sesquilinear forms

### A.1. The definition

-/

namespace LinearMap

section IsPosDef

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] {I₁ : R →+* R}

/-- A sesquilinear form `B` is **positive-definite** if it is symmetric and `0 < B x x` for every
nonzero `x`. -/
structure IsPosDef [LT R] (B : M →ₛₗ[I₁] M →ₗ[R] R) : Prop extends isSymm : B.IsSymm where
  /-- `B` is strictly positive on nonzero vectors. -/
  pos : ∀ x, x ≠ 0 → 0 < B x x

lemma isPosDef_def [LT R] {B : M →ₛₗ[I₁] M →ₗ[R] R} :
    B.IsPosDef ↔ B.IsSymm ∧ ∀ x, x ≠ 0 → 0 < B x x :=
  ⟨fun h ↦ ⟨h.isSymm, h.pos⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

/-!

### A.2. Consequences over a preorder

-/

variable [Preorder R] {B : M →ₛₗ[I₁] M →ₗ[R] R}

/-- A positive-definite form is positive-semidefinite. -/
lemma IsPosDef.isPosSemidef (hB : B.IsPosDef) : B.IsPosSemidef where
  isSymm := hB.isSymm
  isNonneg := ⟨fun x ↦ (eq_or_ne x 0).elim (fun h ↦ by simp [h]) fun hx ↦ (hB.pos x hx).le⟩

/-- A positive-definite form is nondegenerate: a nonzero `x` is not orthogonal to itself. -/
lemma IsPosDef.nondegenerate (hB : B.IsPosDef) : B.Nondegenerate :=
  ⟨fun x hx ↦ by_contra fun h ↦ (hB.pos x h).ne' (hx x),
    fun y hy ↦ by_contra fun h ↦ (hB.pos y h).ne' (hy y)⟩

end IsPosDef

/-!

### A.3. Transport along a linear map

-/

section comp

variable {R M N : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] {B : M →ₗ⋆[R] M →ₗ[R] R} {B' : N →ₗ⋆[R] N →ₗ[R] R}
  {A : M →ₗ[R] N}

/-- If `B' (A x) (A y) = star (B y x)` for a surjective `A`, then `B'` is symmetric when `B` is. -/
lemma IsSymm.of_comp_star (hA : Function.Surjective A) (hB : B.IsSymm)
    (h : ∀ x y, B' (A x) (A y) = star (B y x)) : B'.IsSymm := by
  refine ⟨fun u w => ?_⟩
  obtain ⟨x, rfl⟩ := hA u
  obtain ⟨y, rfl⟩ := hA w
  rw [h, h, starRingEnd_apply, star_star]
  exact (hB.eq x y).symm

/-- If `B' (A x) (A y) = star (B y x)` for a surjective `A`, then `B'` is positive-definite when `B`
is. -/
lemma IsPosDef.of_comp_star [LT R] (hA : Function.Surjective A) (hB : B.IsPosDef)
    (h : ∀ x y, B' (A x) (A y) = star (B y x)) : B'.IsPosDef := by
  refine ⟨hB.isSymm.of_comp_star hA h, fun u hu => ?_⟩
  obtain ⟨x, rfl⟩ := hA u
  rw [h, ← starRingEnd_apply, hB.isSymm.eq x x]
  exact hB.pos x fun hx => hu (by rw [hx, map_zero])

end comp

/-!

### A.4. The matrix of a positive-definite form

-/

section toMatrix

variable {R M n : Type*} [CommRing R] [StarRing R] [PartialOrder R] [AddCommMonoid M]
  [Module R M] [Fintype n] [DecidableEq n] {B : M →ₗ⋆[R] M →ₗ[R] R}

/-- A sesquilinear form is positive-definite exactly when its matrix in a basis is. -/
lemma isPosDef_iff_posDef_toMatrix (b : Basis n R M) : B.IsPosDef ↔ (toMatrix₂ b b B).PosDef := by
  rw [isPosDef_def, Matrix.posDef_iff_dotProduct_mulVec]
  refine and_congr (B.isSymm_iff_isHermitian_toMatrix b) ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · rw [star_dotProduct_toMatrix₂_mulVec]
    exact h _ (b.equivFun.symm.map_ne_zero_iff.mpr hx)
  · rw [apply_eq_star_dotProduct_toMatrix₂_mulVec b]
    exact h (b.equivFun.map_ne_zero_iff.mpr hx)

end toMatrix

end LinearMap
