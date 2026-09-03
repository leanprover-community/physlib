/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Compact.Intertwiner.Basic
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.Schur
public import Mathlib.Analysis.InnerProductSpace.Trace
import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Irreducible

/-!
# Schur orthogonality for irreducible compact-group representations

This file proves the first Schur orthogonality relation for matrix coefficients of a
finite-dimensional irreducible unitary representation of a compact group. Haar-averaging a
rank-one operator produces a self-intertwiner. Schur's lemma makes that intertwiner scalar, and
preservation of the trace determines the scalar to be the reciprocal of the dimension.

The coordinate-free result is accompanied by its orthonormal-basis form. The latter fixes both the
order of the Kronecker deltas and the placement of complex conjugation in Mathlib's convention that
the inner product is conjugate-linear in its first argument.

The second relation, for a pair of representations, is proved in
`TauCeti/RepresentationTheory/Compact/Intertwiner/Basic.lean` from the vanishing of the intertwiners
between them; the last section here packages it with the hypothesis Schur's lemma actually
discharges, namely that the two irreducibles are inequivalent.

## Main statements

* `TauCeti.ContRepresentation.averageOperator_eq_finrank_inv_mul_trace_smul_id`: the average of a
  self-map is its normalized trace times the identity.
* `TauCeti.ContRepresentation.schur_orthogonality_self`: the coordinate-free first Schur
  orthogonality relation.
* `TauCeti.ContRepresentation.schur_orthogonality_basis`: the corresponding Kronecker-delta
  formula in an orthonormal basis.
* `TauCeti.ContRepresentation.schur_orthogonality`: the second Schur orthogonality relation, for
  a pair of inequivalent irreducible unitary representations.

This supplies the three formulas pinned by the orthogonality items of Layer 4 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md);
that item's remaining request, checking the convention against `fourierBasis` on `AddCircle`, waits
on the `AddCircle` material and is not done here. The roadmap sketches the basis identity as the
primitive one; here the coordinate-free statement is the primitive and the basis identity is read
off from it, which is the shorter route and fixes the same convention.
The mathematical argument follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open MeasureTheory
open scoped InnerProductSpace
open scoped MonoidAlgebra

namespace TauCeti

namespace ContRepresentation

section Average

variable {𝕜 G V : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]

local instance instCompleteSpaceSchurAverage : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-! ### The scalar selected by Haar averaging -/

/-- On an irreducible finite-dimensional representation, the Haar average of a self-map is its
normalized trace times the identity. -/
theorem averageOperator_eq_finrank_inv_mul_trace_smul_id
    (hirr : Representation.IsIrreducible π.toRepresentation) (T : V →L[𝕜] V) :
    averageOperator π hπ π hπ T =
      ((Module.finrank 𝕜 V : 𝕜)⁻¹ * LinearMap.trace 𝕜 V (T : V →ₗ[𝕜] V)) •
        ContinuousLinearMap.id 𝕜 V := by
  have hdim : (Module.finrank 𝕜 V : 𝕜) ≠ 0 :=
    Representation.IsIrreducible.natCast_finrank_ne_zero hirr
  have h := π.eq_finrank_inv_mul_trace_smul_id_of_irreducible hdim hirr
    (averageIntertwiner π hπ π hπ T)
  rwa [toContinuousLinearMap_averageIntertwiner, trace_averageOperator] at h

end Average

section Orthogonality

variable {𝕜 G V : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]

local instance instCompleteSpaceSchurOrthogonality : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-! ### The first Schur orthogonality relation -/

/-- **Schur orthogonality for one irreducible representation, in coordinate-free form.**

For a unitary irreducible representation of dimension `d`, the `L²` inner product of the matrix
coefficients determined by `(v₁, w₁)` and `(v₂, w₂)` is
`d⁻¹ * conj ⟪v₁, v₂⟫ * ⟪w₁, w₂⟫`. The conjugation on the first vector factor is forced by Mathlib's
inner-product convention. -/
theorem schur_orthogonality_self (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) (v₁ w₁ v₂ w₂ : V) :
    ⟪matrixCoeffLp π hπ v₁ w₁, matrixCoeffLp π hπ v₂ w₂⟫_𝕜 =
      (Module.finrank 𝕜 V : 𝕜)⁻¹ *
        ((starRingEnd 𝕜) ⟪v₁, v₂⟫_𝕜 * ⟪w₁, w₂⟫_𝕜) := by
  rw [inner_matrixCoeffLp_eq_inner_averageOperator π hπ π hπ hunitary,
    averageOperator_eq_finrank_inv_mul_trace_smul_id π hπ hirr,
    smul_apply, ContinuousLinearMap.id_apply, InnerProductSpace.trace_rankOne, inner_smul_right]
  rw [← inner_conj_symm v₂ v₁]
  ring

/-- **Schur orthogonality in an orthonormal basis.** If
`πᵢⱼ(g) = ⟪π(g)eⱼ, eᵢ⟫`, then
`⟪πᵢⱼ, πₖₗ⟫_{L²} = d⁻¹ δⱼₗ δᵢₖ`.

This is the convention check for `schur_orthogonality_self`: Kronecker deltas are real, so the
coordinate-free conjugation becomes invisible here, while the order of all four indices remains
explicit. -/
theorem schur_orthogonality_basis (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation)
    {d : ℕ} (e : OrthonormalBasis (Fin d) 𝕜 V) (i j k l : Fin d) :
    ⟪matrixCoeffLp π hπ (e j) (e i), matrixCoeffLp π hπ (e l) (e k)⟫_𝕜 =
      (d : 𝕜)⁻¹ *
        ((if j = l then (1 : 𝕜) else 0) * (if i = k then (1 : 𝕜) else 0)) := by
  rw [schur_orthogonality_self π hπ hunitary hirr]
  rw [Module.finrank_eq_card_basis e.toBasis, Fintype.card_fin]
  simp only [orthonormal_iff_ite.mp e.orthonormal]
  split_ifs <;> simp_all

end Orthogonality

section Inequivalent

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]
  [CompleteSpace W]

/-- **The second Schur orthogonality relation.** Matrix coefficients of inequivalent
finite-dimensional irreducible representations of a compact group are `L²`-orthogonal, provided the
second one is unitary.

This is `TauCeti.ContRepresentation.schur_orthogonality_distinct` with its hypothesis discharged:
the vanishing half of Schur's lemma turns inequivalence into the vanishing of every continuous
intertwiner `π → ρ`. Algebraic closedness is not needed, since only the vanishing half of Schur's
lemma is used. -/
theorem schur_orthogonality (π : ContRepresentation 𝕜 G V)
    (hπ : Continuous π) (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ) (hunitary : IsUnitary ρ)
    (hirrπ : Representation.IsIrreducible π.toRepresentation)
    (hirrρ : Representation.IsIrreducible ρ.toRepresentation)
    (hne : IsEmpty (_root_.ContRepresentation.Equiv π ρ)) (v w : V) (v' w' : W) :
    ⟪matrixCoeffLp π hπ v w, matrixCoeffLp ρ hρ v' w'⟫_𝕜 = 0 :=
  schur_orthogonality_distinct π hπ ρ hρ hunitary
    (fun f ↦ by simp [eq_zero_of_isEmpty_equiv hirrπ hirrρ hne f]) v w v' w'

end Inequivalent

end ContRepresentation

end TauCeti
