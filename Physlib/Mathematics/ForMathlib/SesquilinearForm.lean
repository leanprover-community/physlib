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
in a basis it is positive-definite exactly when its matrix is.

## ii. Key results

- `LinearMap.IsPosDef` : a sesquilinear form is symmetric and `0 < B x x` for `x ≠ 0`.
- `LinearMap.IsPosDef.isPosSemidef` : a positive-definite form is positive-semidefinite.
- `LinearMap.IsPosDef.nondegenerate` : a positive-definite form is nondegenerate.
- `LinearMap.isPosDef_iff_posDef_toMatrix` : a form is positive-definite exactly when its matrix in
  a basis is.
- `LinearMap.IsAlt.schouten` : the Schouten identity for an alternating form in two dimensions.

## iii. Table of contents

- A. Positive-definite sesquilinear forms
  - A.1. The definition
  - A.2. Consequences over a preorder
  - A.3. The matrix of a positive-definite form
- B. Alternating forms in two dimensions

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

### A.3. The matrix of a positive-definite form

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

/-!

## B. Alternating forms in two dimensions

-/

namespace LinearMap.IsAlt

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
  [DecidableEq ι] {B : LinearMap.BilinForm R M}

/-- The Schouten identity, `B(u, v) w + B(v, w) u + B(w, u) v = 0`, for an alternating bilinear
form on a module with a basis of two vectors. -/
lemma schouten (hB : LinearMap.IsAlt B) (b : Basis ι R M) (h2 : Fintype.card ι = 2) (u v w : M) :
    B u v • w + B v w • u + B w u • v = 0 := by
  obtain ⟨i, j, hij, huniv⟩ := Finset.card_eq_two.mp (h2 : Finset.univ.card = 2)
  -- Each vector is `x^i e_i + x^j e_j`, and `B` vanishes on `e_i, e_i` and on `e_j, e_j`.
  have hexp (x : M) : x = b.repr x i • b i + b.repr x j • b j := by
    conv_lhs => rw [← b.sum_repr x, huniv, Finset.sum_pair hij]
  rw [hexp u, hexp v, hexp w]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.IsAlt.self_eq_zero hB, (LinearMap.IsAlt.neg hB (b i) (b j)).symm]
  module

end LinearMap.IsAlt
