/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.Groups.SpecialUnitary.LieAlgebra.GellMann.Basic
/-!

# The adjoint action in the Gell-Mann basis

The matrix of the adjoint action of `SU(n)` on `su(n)` in the generalized Gell-Mann basis.

## i. Overview

The adjoint action `x ↦ g x g†` of `g ∈ SU(n)` on `su(n)` is, in the Gell-Mann basis, a real
matrix `R(g)` with entries `re tr (λ_i g λ_j g†) / 2`. As `g ↦ R(g)` is a monoid homomorphism and
the adjoint action preserves the contraction, `R(g)` is orthogonal (A). It acts on the Gell-Mann
matrices as `g λ_j g† = ∑ i, R_ij(g) λ_i`, and on the coordinates in the Gell-Mann basis by matrix
multiplication (B).

## ii. Key results

- `SULieAlgebra.adjointGellMannBasis` : the matrix of the adjoint action in the Gell-Mann basis.
- `SULieAlgebra.adjointGellMannBasis_transpose_mul_self` : that matrix is orthogonal.
- `SULieAlgebra.adjoint_gellMannMatrices` : the adjoint action on the Gell-Mann matrices.

## iii. Table of contents

- A. The matrix of the adjoint action
- B. The adjoint action on Gell-Mann matrices and coordinates

## iv. References

* https://mathworld.wolfram.com/GeneralizedGell-MannMatrix.html

-/

@[expose] public section

namespace SULieAlgebra

open Matrix

/-!

## A. The matrix of the adjoint action

-/

/-- The matrix of the adjoint action of `g` in the Gell-Mann basis, a real matrix, as a monoid
  homomorphism from `SU(n)`. -/
noncomputable def adjointGellMannBasis {n : ℕ} :
    specialUnitaryGroup (Fin n) ℂ →* Matrix (GellMannIndex n) (GellMannIndex n) ℝ :=
  (MonoidHom.ofClass (LinearMap.toMatrixAlgEquiv gellMannBasis)).comp adjoint

/-- The entries of the matrix of the adjoint action, `re tr (λ_i g λ_j g†) / 2`. -/
lemma adjointGellMannBasis_apply {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ)
    (i j : GellMannIndex n) : adjointGellMannBasis g i j =
      ((gellMannMatrices i).1 * (g.1 * (gellMannMatrices j).1 * star g.1)).trace.re / 2 := by
  rw [adjointGellMannBasis, MonoidHom.comp_apply, MonoidHom.coe_ofClass,
    LinearMap.toMatrixAlgEquiv_apply, gellMannBasis_repr_apply, adjointContr_tmul,
    gellMannBasis_apply, adjoint_val]

/-- The matrix of the adjoint action of `g⁻¹` is the transpose of that of `g`, the adjoint action
  preserving the contraction. -/
lemma adjointGellMannBasis_inv {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) :
    adjointGellMannBasis g⁻¹ = (adjointGellMannBasis g)ᵀ := by
  ext i j
  rw [transpose_apply, adjointGellMannBasis, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MonoidHom.coe_ofClass, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrixAlgEquiv_apply,
    gellMannBasis_repr_apply, gellMannBasis_repr_apply, gellMannBasis_apply, gellMannBasis_apply,
    ← adjointContr_adjoint g, Representation.self_inv_apply, adjointContr_symm]

/-- The matrix of the adjoint action is orthogonal. -/
lemma adjointGellMannBasis_transpose_mul_self {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) :
    (adjointGellMannBasis g)ᵀ * adjointGellMannBasis g = 1 := by
  rw [← adjointGellMannBasis_inv, ← map_mul, inv_mul_cancel, map_one]

/-- The matrix of the complex adjoint action in the complex Gell-Mann basis is the real matrix of
  the adjoint action. -/
lemma toMatrix_adjointℂ_gellMannBasisℂ {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) :
    LinearMap.toMatrix gellMannBasisℂ gellMannBasisℂ (adjointℂ g) =
      (adjointGellMannBasis g).map (algebraMap ℝ ℂ) :=
  LinearMap.toMatrix_baseChange ℂ (adjoint g) gellMannBasis gellMannBasis

/-!

## B. The adjoint action on Gell-Mann matrices and coordinates

-/

/-- The adjoint action on a Gell-Mann matrix is a combination of Gell-Mann matrices with
  coefficients the entries of the matrix of the adjoint action,
  `g λ_j g† = ∑ i, R_ij(g) λ_i`. -/
lemma adjoint_gellMannMatrices {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (j : GellMannIndex n) :
    adjoint g (gellMannMatrices j) = ∑ i, adjointGellMannBasis g i j • gellMannMatrices i := by
  conv_lhs => rw [← gellMannBasis.sum_repr (adjoint g (gellMannMatrices j))]
  simp only [adjointGellMannBasis, MonoidHom.comp_apply, MonoidHom.coe_ofClass,
    LinearMap.toMatrixAlgEquiv_apply, gellMannBasis_apply]

/-- The adjoint action on the coordinates in the Gell-Mann basis is multiplication by the matrix of
  the adjoint action, `A^i ↦ R_ij(g) A^j`. -/
lemma gellMannBasis_repr_adjoint {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ)
    (x : SULieAlgebra n ℂ) :
    gellMannBasis.repr (adjoint g x) = adjointGellMannBasis g *ᵥ gellMannBasis.repr x :=
  (LinearMap.toMatrix_mulVec_repr gellMannBasis gellMannBasis (adjoint g) x).symm

end SULieAlgebra
