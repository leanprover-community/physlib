/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Analysis.InnerProductSpace.TensorProduct
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.MatrixCoefficient

/-!
# The tensor product of continuous representations

The tensor product of two continuous representations of the same monoid acts by
`g ↦ (π g) ⊗ (ρ g)`, that is, by Mathlib's `TensorProduct.mapL`. This file builds it and proves the
three facts its use requires: the operator-valued action stays continuous, unitarity is preserved,
and the matrix coefficients **multiply**,
`(π ⊗ ρ)_{v ⊗ v', w ⊗ w'} = π_{v,w} · ρ_{v',w'}`.

The last identity is the reason the construction is here: it is what makes the span of the matrix
coefficients of all finite-dimensional representations of `G` closed under multiplication, hence a
subalgebra of `C(G, 𝕜)` rather than only a subspace.

Mathlib's inner product on `V ⊗[𝕜] W` (`TensorProduct.instInnerProductSpace`) is the one for which
`⟪v ⊗ₜ v', w ⊗ₜ w'⟫ = ⟪v, w⟫ * ⟪v', w'⟫`, so no choice is being made here; the same file supplies
`TensorProduct.mapL` with its multiplicativity `TensorProduct.mapL_mul` and its norm bound.

## Main definitions

* `TauCeti.ContRepresentation.tprod`: the tensor product `π ⊗ ρ` of two continuous
  representations.

## Main statements

* `TauCeti.ContRepresentation.continuous_tprod` and
  `TauCeti.ContRepresentation.IsUnitary.tprod`: the tensor product of continuous representations is
  continuous, and of unitary ones is unitary.
* `TauCeti.ContRepresentation.matrixCoeff_tprod`: matrix coefficients of a tensor product at pure
  tensors are products of matrix coefficients.

The construction supplies the "products of matrix coefficients of `π, ρ` are matrix coefficients of
`π ⊗ ρ`" item of Layer 3 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md).
The mathematical development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open scoped InnerProductSpace TensorProduct

namespace TauCeti

namespace ContRepresentation

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

/-- **The tensor product of two continuous representations**, acting by `g ↦ (π g) ⊗ (ρ g)`. -/
noncomputable def tprod (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W) :
    ContRepresentation 𝕜 G (V ⊗[𝕜] W) :=
  .ofMonoidHom
    { toFun g := TensorProduct.mapL (π g) (ρ g)
      map_one' := by simp [ContinuousLinearMap.one_def]
      map_mul' g h := by rw [map_mul, map_mul, TensorProduct.mapL_mul] }

variable (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W)

omit [TopologicalSpace G] in
/-- The action operators of a tensor product of representations. -/
@[simp]
theorem tprod_apply (g : G) : (tprod π ρ) g = TensorProduct.mapL (π g) (ρ g) :=
  (rfl)

/-- The tensor product of two continuous representations has a continuous operator-valued action:
`mapL` is the composition of two contractions of the separate actions. -/
theorem continuous_tprod (hπ : Continuous π) (hρ : Continuous ρ) :
    Continuous (tprod π ρ) :=
  (lipschitzWith_one_rTensor.continuous.comp hπ).clm_comp
    (lipschitzWith_one_lTensor.continuous.comp hρ)

omit [TopologicalSpace G] in
/-- The tensor product of two unitary representations is unitary: the tensor product of two linear
isometries is a linear isometry. -/
theorem IsUnitary.tprod {π : ContRepresentation 𝕜 G V} {ρ : ContRepresentation 𝕜 G W}
    (hπ : IsUnitary π) (hρ : IsUnitary ρ) : IsUnitary (tprod π ρ) :=
  (isUnitary_iff_norm_map _).mpr fun g x ↦ by
    simpa using TensorProduct.norm_map
      (((π g) : V →ₗ[𝕜] V).isometryOfInner (hπ.inner_map_map g))
      (((ρ g) : W →ₗ[𝕜] W).isometryOfInner (hρ.inner_map_map g)) x

/-- **Matrix coefficients multiply under tensor product.** The matrix coefficient of `π ⊗ ρ` at a
pair of pure tensors is the product of the matrix coefficients of `π` and of `ρ`. -/
@[simp]
theorem matrixCoeff_tprod (hπ : Continuous π) (hρ : Continuous ρ) (v w : V) (v' w' : W) :
    matrixCoeff (tprod π ρ) (continuous_tprod π ρ hπ hρ) (v ⊗ₜ[𝕜] v') (w ⊗ₜ[𝕜] w') =
      matrixCoeff π hπ v w * matrixCoeff ρ hρ v' w' := by
  ext g
  simp

end ContRepresentation

end TauCeti
