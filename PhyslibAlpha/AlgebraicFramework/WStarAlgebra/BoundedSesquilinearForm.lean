/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Riesz realization of a bounded sesquilinear form

Trimmed port of the `BoundedSesquilinearForm` structure from `unbounded-alpha-public`'s
`QuantumMechanics/Unbounded/Operators/SpectralTheory/BoundedSesquilinear.lean` — only the pieces
`WStarAlgebra/TracePairingSurjectivity.lean` actually needs (`form`, `bound`, `operator`,
`operator_inner`), dropping that file's weak-operator-topology bridge (`ofWOT`) and other
self-adjointness helpers, which belong to spectral-measure infrastructure this repo's
`AlgebraicFramework` scope does not include.

The convention is the one used by `InnerProductSpace.continuousLinearMapOfBilin`: `form x y` is
conjugate-linear in `x` and linear in `y`, and the represented operator satisfies
`⟪y, operator x⟫ = conj (form x y)`.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A bounded sesquilinear form in the orientation expected by Mathlib's Riesz representation
theorem. -/
structure BoundedSesquilinearForm (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The underlying sesquilinear form. -/
  form : H →ₛₗ[starRingEnd ℂ] H →ₗ[ℂ] ℂ
  /-- The form is bounded by some constant `C`. -/
  bound : ∃ C : ℝ, ∀ x y, ‖form x y‖ ≤ C * ‖x‖ * ‖y‖

namespace BoundedSesquilinearForm

variable (B : BoundedSesquilinearForm H)

/-- A norm bound witnessing `B.bound`. -/
noncomputable def boundConstant : ℝ := Classical.choose B.bound

@[nolint unusedArguments]
lemma boundConstant_spec : ∀ x y, ‖B.form x y‖ ≤ B.boundConstant * ‖x‖ * ‖y‖ :=
  Classical.choose_spec B.bound

/-- The continuous version of a bounded sesquilinear form. -/
noncomputable def continuous : H →L⋆[ℂ] H →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂ B.form B.boundConstant B.boundConstant_spec

@[simp]
lemma continuous_apply (x y : H) : B.continuous x y = B.form x y :=
  LinearMap.mkContinuous₂_apply B.form B.boundConstant_spec x y

/-- The unique bounded operator represented by `B`. -/
noncomputable def operator : H →L[ℂ] H :=
  InnerProductSpace.continuousLinearMapOfBilin B.continuous

lemma operator_inner (x y : H) :
    ⟪y, B.operator x⟫_ℂ = starRingEnd ℂ (B.form x y) := by
  have h := InnerProductSpace.continuousLinearMapOfBilin_apply B.continuous x y
  change ⟪B.operator x, y⟫_ℂ = B.form x y at h
  rw [← inner_conj_symm, h]

end BoundedSesquilinearForm
