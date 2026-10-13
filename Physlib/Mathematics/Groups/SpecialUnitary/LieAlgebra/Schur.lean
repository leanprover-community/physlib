/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Physlib.Mathematics.Groups.SpecialUnitary.LieAlgebra.Adjoint
/-!

# Schur's lemma for the adjoint representation of `SU(n)`

Every endomorphism commuting with the complex adjoint representation of `SU(n)` is a scalar.

## i. Overview

We show that an endomorphism `T` of the complexification of `su(n)` commuting with the adjoint
action of `SU(n)` is a multiple of the identity (A). For `2 ≤ n` this is Mathlib's Schur's lemma
for an irreducible finite-dimensional representation over an algebraically closed field, applied
to the complex adjoint representation, whose irreducibility is `isIrreducible_adjointℂ`. For
`n ≤ 1` there is nothing to prove, since the complexification vanishes.

As a consequence, every `SU(n)`-invariant bilinear form on the complexification is a multiple of
the contraction `adjointℂContr` (B).

## ii. Key results

- `SULieAlgebra.end_eq_smul_id_of_commute_adjointℂ` : Schur's lemma for the complex adjoint
  representation.
- `SULieAlgebra.intertwiningMap_eq_smul_adjointℂContr` : every intertwiner `adj ⊗ adj → ℂ` is a
  multiple of the complex contraction.

## iii. Table of contents

- A. Schur's lemma
- B. Invariant bilinear forms

## iv. References

* None.

-/

@[expose] public section

open Matrix TensorProduct

namespace SULieAlgebra

/-!

## A. Schur's lemma

-/

/-- An endomorphism of the complexification commuting with the adjoint action is a scalar: the
  complex adjoint representation satisfies Schur's lemma. -/
lemma end_eq_smul_id_of_commute_adjointℂ {n : ℕ} {T : Module.End ℂ (Complexification n)}
    (hT : ∀ g, T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T) : ∃ μ : ℂ, T = μ • LinearMap.id := by
  rcases lt_or_ge n 2 with hn | hn
  · -- for `n ≤ 1` a traceless matrix of size `n` vanishes, so the complexification is zero
    have h0 : ∀ A : Complexification n, A = 0 := by
      interval_cases n
      · exact fun A => toMatrixℂ_injective (Subsingleton.elim _ _)
      · refine fun A => toMatrixℂ_injective (Matrix.ext fun x y => ?_)
        have h := trace_toMatrixℂ A
        rw [Matrix.trace_fin_one] at h
        simpa [Subsingleton.elim x 0, Subsingleton.elim y 0] using h
    exact ⟨0, LinearMap.ext fun A => (h0 (T A)).trans (by simp)⟩
  · -- for `2 ≤ n` the complex adjoint representation is irreducible
    have := isIrreducible_adjointℂ hn
    -- `T` is an intertwiner of `adjointℂ` with itself, hence in the image of `algebraMap ℂ`
    obtain ⟨μ, hμ⟩ :=
      (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
        (ρ := adjointℂ (n := n))).2 ⟨T, hT⟩
    exact ⟨μ, LinearMap.ext fun A => by simpa using (DFunLike.congr_fun hμ A).symm⟩

/-!

## B. Invariant bilinear forms

-/

/-- Every bilinear form on the complexification is the contraction against an endomorphism,
  the contraction being nondegenerate. -/
lemma exists_eq_adjointℂContr_tmul {n : ℕ}
    (B : Complexification n ⊗[ℂ] Complexification n →ₗ[ℂ] ℂ) :
    ∃ T : Module.End ℂ (Complexification n), ∀ A C, B (A ⊗ₜ C) = adjointℂContr (T A ⊗ₜ C) :=
  ⟨(LinearMap.BilinForm.toDual _ adjointℂContr_nondegenerate).symm.toLinearMap ∘ₗ curry B,
    fun A C => (LinearMap.BilinForm.apply_toDual_symm_apply
      (hB := adjointℂContr_nondegenerate) (curry B A) C).symm⟩

/-- The endomorphism representing an invariant bilinear form commutes with the adjoint
  action. -/
lemma adjointℂ_comp_eq_of_adjointℂContr_tmul {n : ℕ}
    (B : ((adjointℂ (n := n)).tprod adjointℂ).IntertwiningMap
      (Representation.trivial ℂ (specialUnitaryGroup (Fin n) ℂ) ℂ))
    {T : Module.End ℂ (Complexification n)} (hT : ∀ A C, B (A ⊗ₜ C) = adjointℂContr (T A ⊗ₜ C))
    (g : specialUnitaryGroup (Fin n) ℂ) :
    T ∘ₗ adjointℂ g = adjointℂ g ∘ₗ T := by
  have hB (A C : Complexification n) : B (adjointℂ g A ⊗ₜ adjointℂ g C) = B (A ⊗ₜ C) := by
    simpa only [Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.trivial_apply] using Representation.IntertwiningMap.isIntertwining _ _ B g
        (A ⊗ₜ C)
  refine LinearMap.ext fun A => sub_eq_zero.1 (adjointℂContr_separating_left _ fun C => ?_)
  rw [sub_tmul, map_sub, sub_eq_zero, LinearMap.comp_apply, LinearMap.comp_apply, ← hT,
    ← Representation.self_inv_apply adjointℂ g C, hB, hT, adjointℂContr_adjointℂ]

/-- Every intertwiner `adj ⊗ adj → ℂ` is a multiple of the contraction: up to scale, the
  contraction is the unique `SU(n)`-invariant bilinear form on the complexification. -/
lemma intertwiningMap_eq_smul_adjointℂContr {n : ℕ}
    (B : ((adjointℂ (n := n)).tprod adjointℂ).IntertwiningMap
      (Representation.trivial ℂ (specialUnitaryGroup (Fin n) ℂ) ℂ)) :
    ∃ z : ℂ, B = z • adjointℂContr := by
  obtain ⟨T, hT⟩ := exists_eq_adjointℂContr_tmul B.toLinearMap
  obtain ⟨μ, hμ⟩ :=
    end_eq_smul_id_of_commute_adjointℂ (adjointℂ_comp_eq_of_adjointℂContr_tmul B hT)
  refine ⟨μ, Representation.IntertwiningMap.ext (TensorProduct.ext' fun A C => ?_)⟩
  rw [hT, hμ, LinearMap.smul_apply, LinearMap.id_apply, ← smul_tmul', map_smul]
  rfl

end SULieAlgebra
