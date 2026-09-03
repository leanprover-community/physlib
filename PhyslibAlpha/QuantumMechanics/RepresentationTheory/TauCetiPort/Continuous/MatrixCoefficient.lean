/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.Unitary.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Matrix coefficients of continuous representations

This file defines the matrix coefficient
`g ↦ ⟪π g v, w⟫` of a representation whose operator-valued action is continuous, and develops its
algebra: sesquilinearity in the defining vectors, the matrix-multiplication identity at a product
of group elements, the behaviour under left and right translation of the group argument, the
involution coming from inversion, and the uniform bound for unitary representations.

Mathlib's `ContRepresentation` bundles continuous linear action operators but does not require
continuity of the map from the acting topological monoid to those operators. The continuity
hypothesis is therefore explicit in `matrixCoeff` and its API; since it is a `Prop` argument, two
matrix coefficients built from different continuity proofs are equal by proof irrelevance.

## Main definitions

* `TauCeti.ContRepresentation.matrixCoeff`: the matrix coefficient `g ↦ ⟪π g v, w⟫` as an element
  of `C(G, 𝕜)`.
* `TauCeti.ContRepresentation.matrixCoeffₛₗ`: the matrix coefficients of a fixed representation
  bundled as a sesquilinear map `V →ₗ⋆[𝕜] V →ₗ[𝕜] C(G, 𝕜)`, in Mathlib's `innerₛₗ` convention.

## Main statements

* `TauCeti.ContRepresentation.matrixCoeff_apply_mul_eq_sum`: in an orthonormal basis, matrix
  coefficients multiply like matrices, `π_{ik}(g * h) = ∑ j, π_{ij}(g) · π_{jk}(h)`.
* `TauCeti.ContRepresentation.matrixCoeff_comp_mulRight` and
  `TauCeti.ContRepresentation.matrixCoeff_comp_mulLeft`: right and left translates of a matrix
  coefficient of `π` are again matrix coefficients of `π`. This is the `G × G`-action that
  structures the span of the matrix coefficients.
* `TauCeti.ContRepresentation.star_matrixCoeff`: the conjugate of a matrix coefficient of a
  unitary representation is a matrix coefficient composed with inversion.
* `TauCeti.ContRepresentation.matrixCoeff_trivial`: the matrix coefficients of the trivial
  representation are constant.
* `TauCeti.ContRepresentation.norm_matrixCoeff_le`: the uniform bound `‖v‖ * ‖w‖` for a unitary
  representation.

The algebra of matrix coefficients is the Layer 3 milestone of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap); it is what makes the
span of the matrix coefficients of a fixed representation a translation-stable subspace of `C(G)`,
stable under conjugation followed by inversion of the argument, and it feeds the Schur
orthogonality relations of Layer 4. Conjugation alone leaves that span in general: it produces a
matrix coefficient of the contragredient representation, which is not built here. The mathematical
development follows Daniel Bump, *Lie Groups*, second edition, Chapters 2–4.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

namespace ContRepresentation

section Coefficients

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- The matrix coefficient `g ↦ ⟪π g v, w⟫` of a representation with continuous
operator-valued action. -/
noncomputable def matrixCoeff (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v w : V) : C(G, 𝕜) where
  toFun g := ⟪π g v, w⟫_𝕜
  continuous_toFun := by fun_prop

/-- Evaluation of a matrix coefficient. -/
@[simp]
theorem matrixCoeff_apply (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) (v w : V) (g : G) :
    matrixCoeff π hπ v w g = ⟪π g v, w⟫_𝕜 :=
  (rfl)

/-- A matrix coefficient at the identity is the inner product of its defining vectors. -/
theorem matrixCoeff_apply_one (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) (v w : V) :
    matrixCoeff π hπ v w 1 = ⟪v, w⟫_𝕜 := by
  simp

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-! ### Sesquilinearity in the defining vectors

Following Mathlib's inner-product convention, a matrix coefficient is conjugate-linear in its first
vector and linear in its second. -/

@[simp]
theorem matrixCoeff_zero_left (w : V) : matrixCoeff π hπ 0 w = 0 := by
  ext g
  simp

@[simp]
theorem matrixCoeff_zero_right (v : V) : matrixCoeff π hπ v 0 = 0 := by
  ext g
  simp

@[simp]
theorem matrixCoeff_add_left (v₁ v₂ w : V) :
    matrixCoeff π hπ (v₁ + v₂) w = matrixCoeff π hπ v₁ w + matrixCoeff π hπ v₂ w := by
  ext g
  simp [inner_add_left]

@[simp]
theorem matrixCoeff_add_right (v w₁ w₂ : V) :
    matrixCoeff π hπ v (w₁ + w₂) = matrixCoeff π hπ v w₁ + matrixCoeff π hπ v w₂ := by
  ext g
  simp [inner_add_right]

@[simp]
theorem matrixCoeff_smul_left (c : 𝕜) (v w : V) :
    matrixCoeff π hπ (c • v) w = (starRingEnd 𝕜) c • matrixCoeff π hπ v w := by
  ext g
  simp [inner_smul_left]

@[simp]
theorem matrixCoeff_smul_right (v : V) (c : 𝕜) (w : V) :
    matrixCoeff π hπ v (c • w) = c • matrixCoeff π hπ v w := by
  ext g
  simp [inner_smul_right]

/-- The matrix coefficients of a fixed representation, bundled as a sesquilinear map: conjugate
linear in the first vector, linear in the second, exactly as Mathlib's `innerₛₗ`.

Bundling records the sesquilinearity in the form the span of the matrix coefficients is built from,
and supplies the remaining additive identities (`map_neg`, `map_sub`, `map_sum`) through the
`LinearMap` API. -/
noncomputable def matrixCoeffₛₗ : V →ₗ⋆[𝕜] V →ₗ[𝕜] C(G, 𝕜) where
  toFun v :=
    { toFun := matrixCoeff π hπ v
      map_add' := matrixCoeff_add_right π hπ v
      map_smul' := matrixCoeff_smul_right π hπ v }
  map_add' v₁ v₂ := LinearMap.ext fun w ↦ matrixCoeff_add_left π hπ v₁ v₂ w
  map_smul' c v := LinearMap.ext fun w ↦ matrixCoeff_smul_left π hπ c v w

@[simp]
theorem matrixCoeffₛₗ_apply_apply (v w : V) :
    matrixCoeffₛₗ π hπ v w = matrixCoeff π hπ v w :=
  (rfl)

/-! ### Translating the group argument -/

/-- Translating the argument of a matrix coefficient on the right moves the action onto the first
vector. The pointwise statement needs no continuity of the multiplication of `G`. -/
theorem matrixCoeff_apply_mul_right (v w : V) (g g₀ : G) :
    matrixCoeff π hπ v w (g * g₀) = matrixCoeff π hπ (π g₀ v) w g := by
  simp [map_mul]

/-- Matrix coefficients multiply like matrices: expanding the intermediate vector `π h v` in an
orthonormal basis writes the coefficient at a product as a sum of products of coefficients. In the
basis notation `π_{ij}(g) = ⟪π g eⱼ, eᵢ⟫` this is `π_{ik}(g * h) = ∑ j, π_{ij}(g) · π_{jk}(h)`. -/
theorem matrixCoeff_apply_mul_eq_sum {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι 𝕜 V)
    (v w : V) (g h : G) :
    matrixCoeff π hπ v w (g * h) =
      ∑ i, matrixCoeff π hπ (e i) w g * matrixCoeff π hπ v (e i) h := by
  have hmul : π (g * h) v = π g (π h v) := by simp [map_mul]
  calc
    matrixCoeff π hπ v w (g * h) = ⟪π g (∑ i, ⟪e i, π h v⟫_𝕜 • e i), w⟫_𝕜 := by
      rw [matrixCoeff_apply, hmul, e.sum_repr']
    _ = ∑ i, (starRingEnd 𝕜) ⟪e i, π h v⟫_𝕜 * ⟪π g (e i), w⟫_𝕜 := by
      simp [map_sum, sum_inner, inner_smul_left]
    _ = ∑ i, matrixCoeff π hπ (e i) w g * matrixCoeff π hπ v (e i) h := by
      simp [inner_conj_symm, mul_comm]

/-! ### The trivial representation, and restriction along a homomorphism -/

/-- A matrix coefficient of the trivial representation is the constant function at the inner
product of its defining vectors; the trivial action is constant, so `continuous_const` is its
continuity witness. Which constants arise depends on `V`: they are the values of the inner product,
so all of `𝕜` when some `⟪v, w⟫ ≠ 0`, and only `0` when `V` is trivial. -/
@[simp]
theorem matrixCoeff_trivial (v w : V) :
    matrixCoeff (ContRepresentation.trivial 𝕜 G V) continuous_const v w =
      ContinuousMap.const G ⟪v, w⟫_𝕜 := by
  ext g
  simp
  rfl

/-- A matrix coefficient of an invariant submodule is the matrix coefficient of the ambient
representation at the underlying vectors, so passing to a subrepresentation creates no new
matrix coefficients; `continuous_subrepresentation hπ` is the continuity witness of the restricted
action. -/
@[simp]
theorem matrixCoeff_subrepresentation {W : Submodule 𝕜 V} (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) (v w : W) :
    matrixCoeff (subrepresentation π W hW) (continuous_subrepresentation hπ) v w =
      matrixCoeff π hπ (v : V) (w : V) := by
  ext g
  simp [Submodule.coe_inner]

/-- Restricting a representation along a continuous homomorphism precomposes its matrix
coefficients; the restricted action is `π ∘ φ`, so `hπ.comp hφ` is its continuity witness. -/
@[simp]
theorem matrixCoeff_restrict {H : Type*} [Monoid H] [TopologicalSpace H] (φ : H →* G)
    (hφ : Continuous φ) (v w : V) :
    matrixCoeff (π.restrict φ) (hπ.comp hφ) v w = (matrixCoeff π hπ v w).comp ⟨φ, hφ⟩ := by
  ext h
  simp

end Coefficients

section TranslationRight

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- The right translate of a matrix coefficient of `π` is again a matrix coefficient of `π`: the
translation is absorbed into the first vector. -/
@[simp]
theorem matrixCoeff_comp_mulRight (v w : V) (g₀ : G) :
    (matrixCoeff π hπ v w).comp (ContinuousMap.mulRight g₀) = matrixCoeff π hπ (π g₀ v) w :=
  ContinuousMap.ext fun g ↦ matrixCoeff_apply_mul_right π hπ v w g g₀

end TranslationRight

section Group

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
variable {π : ContRepresentation 𝕜 G V}

/-- Translating the argument of a matrix coefficient of a unitary representation on the left moves
the action of the inverse onto the second vector. -/
theorem matrixCoeff_apply_mul_left (hπ : Continuous π) (hunitary : IsUnitary π) (v w : V)
    (g₀ g : G) :
    matrixCoeff π hπ v w (g₀ * g) = matrixCoeff π hπ v (π g₀⁻¹ w) g := by
  have hmul : π (g₀ * g) v = π g₀ (π g v) := by simp [map_mul]
  rw [matrixCoeff_apply, matrixCoeff_apply, hmul, hunitary.inner_map_left]

/-- Evaluating a matrix coefficient of a unitary representation at an inverse conjugates it and
swaps its defining vectors. This is the involution that the span of the matrix coefficients carries;
see `star_matrixCoeff` for the packaged form. -/
theorem matrixCoeff_apply_inv (hπ : Continuous π) (hunitary : IsUnitary π) (v w : V) (g : G) :
    matrixCoeff π hπ v w g⁻¹ = (starRingEnd 𝕜) (matrixCoeff π hπ w v g) := by
  rw [matrixCoeff_apply, matrixCoeff_apply, hunitary.inner_map_left, inv_inv, inner_conj_symm]

/-- The left translate of a matrix coefficient of a unitary representation is again a matrix
coefficient: the translation is absorbed into the second vector. -/
@[simp]
theorem matrixCoeff_comp_mulLeft [SeparatelyContinuousMul G] (hπ : Continuous π)
    (hunitary : IsUnitary π) (v w : V) (g₀ : G) :
    (matrixCoeff π hπ v w).comp (ContinuousMap.mulLeft g₀) = matrixCoeff π hπ v (π g₀⁻¹ w) :=
  ContinuousMap.ext fun g ↦ matrixCoeff_apply_mul_left hπ hunitary v w g₀ g

/-- The conjugate of a matrix coefficient of a unitary representation is the matrix coefficient
with its vectors swapped, precomposed with inversion. So the span of the matrix coefficients of a
unitary representation is stable under the star operation of `C(G, 𝕜)` followed by inversion of the
argument. -/
@[simp]
theorem star_matrixCoeff [ContinuousInv G] (hπ : Continuous π) (hunitary : IsUnitary π) (v w : V) :
    star (matrixCoeff π hπ v w) =
      (matrixCoeff π hπ w v).comp ⟨Inv.inv, continuous_inv⟩ :=
  ContinuousMap.ext fun g ↦ (matrixCoeff_apply_inv hπ hunitary w v g).symm

end Group

section CompactDomain

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G] [CompactSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- The uniform norm of a matrix coefficient of a unitary representation is at most the product
of the norms of its defining vectors. -/
theorem norm_matrixCoeff_le (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (hunitary : IsUnitary π) (v w : V) :
    ‖matrixCoeff π hπ v w‖ ≤ ‖v‖ * ‖w‖ := by
  rw [ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact fun g ↦ hunitary.norm_inner_map_le g v w

end CompactDomain

end ContRepresentation

end TauCeti
