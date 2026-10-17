/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.GNS
public import PhyslibAlpha.ProbabilisticTheory.Representation.VectorMeasure

/-!

# Symmetries of an invariant state are unitarily implemented

A ⋆-automorphism preserving a state is implemented by a unitary operator on the GNS space that fixes
the cyclic vector.

## i. Overview

Let `ω` be a state on a unital C⋆-algebra `A` and `σ` a ⋆-automorphism of `A` with `ω ∘ σ = ω`.
Then `[a] ↦ [σ a]` preserves the GNS inner product `⟨a, b⟩ = ω(a⋆ b)`, so it extends to an
isometry of the GNS space `H_ω`, with inverse the extension of `σ⁻¹`. This unitary operator `U_σ`
fixes the cyclic vector and intertwines the GNS representation: `U_σ π_ω(a) = π_ω(σ a) U_σ`.
For a group of such automorphisms, for instance the translations of a lattice and a
translation-invariant state, this gives a unitary representation of the group on `H_ω`.

## ii. Key results

- `UnitalPositiveLinearMap.gnsUnitary` : the unitary operator implementing a symmetry.
- `UnitalPositiveLinearMap.gnsUnitary_cyclicVector` : it fixes the cyclic vector.
- `UnitalPositiveLinearMap.gnsUnitary_comp_gnsRep` : it intertwines the GNS representation.
- `UnitalPositiveLinearMap.gnsUnitaryRep` : the unitary representation of a group of symmetries.

## iii. Table of contents

- A. The isometry on the pre-Hilbert space
- B. The unitary operator
- C. Representations of groups of symmetries

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace UnitalPositiveLinearMap

variable (ω : 𝓢[ℂ, A]) (σ : A ≃⋆ₐ[ℂ] A)

/-! ## A. The isometry on the pre-Hilbert space -/

/-- The map `[a] ↦ [σ a]` on the pre-Hilbert space of a state. -/
def preGNSAut : ω.toPositiveLinearMap.PreGNS →ₗ[ℂ] ω.toPositiveLinearMap.PreGNS :=
  ω.toPositiveLinearMap.toPreGNS.toLinearMap ∘ₗ σ.toAlgEquiv.toLinearMap ∘ₗ
    ω.toPositiveLinearMap.ofPreGNS.toLinearMap

variable {ω σ}

omit [StarOrderedRing A] in
lemma ofPreGNS_preGNSAut (x : ω.toPositiveLinearMap.PreGNS) :
    ω.toPositiveLinearMap.ofPreGNS (preGNSAut ω σ x) = σ (ω.toPositiveLinearMap.ofPreGNS x) := rfl

/-- A symmetry preserving the state preserves the GNS inner product. -/
lemma inner_preGNSAut (hσ : ∀ a, ω (σ a) = ω a) (x y : ω.toPositiveLinearMap.PreGNS) :
    ⟪preGNSAut ω σ x, preGNSAut ω σ y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.preGNS_inner_def,
    ofPreGNS_preGNSAut, ofPreGNS_preGNSAut, ← map_star, ← map_mul]
  exact hσ _

lemma norm_preGNSAut (hσ : ∀ a, ω (σ a) = ω a) (x : ω.toPositiveLinearMap.PreGNS) :
    ‖preGNSAut ω σ x‖ = ‖x‖ := by
  have h := inner_preGNSAut hσ x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖preGNSAut ω σ x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h
  nlinarith [norm_nonneg (preGNSAut ω σ x), norm_nonneg x]

/-- The symmetry as a bounded operator on the pre-Hilbert space. -/
def preGNSAutCLM (hσ : ∀ a, ω (σ a) = ω a) :
    ω.toPositiveLinearMap.PreGNS →L[ℂ] ω.toPositiveLinearMap.PreGNS :=
  (preGNSAut ω σ).mkContinuous 1 fun x => by rw [one_mul, norm_preGNSAut hσ]

/-! ## B. The unitary operator -/

/-- The unitary operator on the GNS space implementing a symmetry that preserves the state. -/
def gnsAut (hσ : ∀ a, ω (σ a) = ω a) : ω.GNS →L[ℂ] ω.GNS :=
  (preGNSAutCLM hσ).completion

lemma gnsAut_coe (hσ : ∀ a, ω (σ a) = ω a) (x : ω.toPositiveLinearMap.PreGNS) :
    gnsAut hσ (x : ω.GNS) = ((preGNSAut ω σ x : ω.toPositiveLinearMap.PreGNS) : ω.GNS) := by
  simp [gnsAut, preGNSAutCLM]

/-- The implementing operator preserves the inner product of the GNS space. -/
lemma inner_gnsAut (hσ : ∀ a, ω (σ a) = ω a) (x y : ω.GNS) :
    ⟪gnsAut hσ x, gnsAut hσ y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp =>
    exact isClosed_eq ((continuous_inner.comp ((gnsAut hσ).continuous.prodMap
      (gnsAut hσ).continuous)).comp continuous_id) continuous_inner
  | ih x y => rw [gnsAut_coe, gnsAut_coe, Completion.inner_coe, Completion.inner_coe,
      inner_preGNSAut hσ]

/-! ## C. Representations of groups of symmetries -/

section Group

variable {G : Type*} [AddCommGroup G]
variable {α : Multiplicative G →* (A ≃⋆ₐ[ℂ] A)} (hα : ∀ g a, ω (α g a) = ω a)

include hα

lemma gnsAut_mul (g h : Multiplicative G) :
    gnsAut (hα (g * h)) = gnsAut (hα g) * gnsAut (hα h) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (gnsAut (hα (g * h))).continuous (gnsAut (hα g) * gnsAut (hα h)).continuous
  | ih x =>
    rw [mul_apply_eq_comp, gnsAut_coe, gnsAut_coe, gnsAut_coe]
    congr 1
    show ω.toPositiveLinearMap.toPreGNS ((α (g * h)) (ω.toPositiveLinearMap.ofPreGNS x)) =
      ω.toPositiveLinearMap.toPreGNS ((α g) ((α h) (ω.toPositiveLinearMap.ofPreGNS x)))
    rw [map_mul]
    rfl

lemma gnsAut_one : gnsAut (hα 1) = 1 := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (gnsAut (hα 1)).continuous continuous_id
  | ih x =>
    rw [gnsAut_coe]
    simp only [one_apply_eq_self]
    congr 1
    show ω.toPositiveLinearMap.toPreGNS ((α 1) (ω.toPositiveLinearMap.ofPreGNS x)) = x
    rw [map_one]
    rfl

lemma star_gnsAut_mul_gnsAut (g : Multiplicative G) :
    star (gnsAut (hα g)) * gnsAut (hα g) = 1 := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
  exact (ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self _).mp
    (fun x y => inner_gnsAut (hα g) x y)

lemma star_gnsAut (g : Multiplicative G) : star (gnsAut (hα g)) = gnsAut (hα g⁻¹) := by
  have h1 : gnsAut (hα g) * gnsAut (hα g⁻¹) = 1 := by
    rw [← gnsAut_mul hα _ _, mul_inv_cancel, gnsAut_one hα]
  calc star (gnsAut (hα g)) = star (gnsAut (hα g)) * (gnsAut (hα g) * gnsAut (hα g⁻¹)) := by
        rw [h1, mul_one]
    _ = gnsAut (hα g⁻¹) := by rw [← mul_assoc, star_gnsAut_mul_gnsAut hα, one_mul]

/-- **Translations of an invariant state are unitarily implemented**: the unitary operator on the
GNS space implementing the symmetry `α g`. -/
def gnsUnitary (g : Multiplicative G) : unitary (ω.GNS →L[ℂ] ω.GNS) :=
  ⟨gnsAut (hα g), by
    rw [Unitary.mem_iff]
    refine ⟨star_gnsAut_mul_gnsAut hα g, ?_⟩
    rw [star_gnsAut hα g, ← gnsAut_mul hα _ _, mul_inv_cancel, gnsAut_one hα]⟩

/-- **The unitary representation of a symmetry group on the GNS space of an invariant state.** -/
def gnsUnitaryRep : Multiplicative G →* unitary (ω.GNS →L[ℂ] ω.GNS) where
  toFun := gnsUnitary hα
  map_one' := Subtype.ext (gnsAut_one hα)
  map_mul' g h := Subtype.ext (gnsAut_mul hα g h)

/-- The implementing unitary fixes the cyclic vector. -/
lemma gnsUnitary_cyclicVector (g : Multiplicative G) :
    ((gnsUnitary hα g : unitary (ω.GNS →L[ℂ] ω.GNS)) : ω.GNS →L[ℂ] ω.GNS) ω.gnsCyclicVector =
      ω.gnsCyclicVector := by
  show gnsAut (hα g) ω.gnsCyclicVector = ω.gnsCyclicVector
  rw [gnsCyclicVector, gnsAut_coe]
  congr 1
  show ω.toPositiveLinearMap.toPreGNS ((α g) 1) = _
  rw [map_one]

/-- The implementing unitary carries `π(a) Ω` to `π(α_g a) Ω`. -/
lemma gnsUnitary_gnsRep_cyclicVector (g : Multiplicative G) (a : A) :
    ((gnsUnitary hα g : unitary (ω.GNS →L[ℂ] ω.GNS)) : ω.GNS →L[ℂ] ω.GNS)
        (ω.gnsRep a ω.gnsCyclicVector) = ω.gnsRep (α g a) ω.gnsCyclicVector := by
  rw [gnsRep_gnsCyclicVector, gnsRep_gnsCyclicVector]
  show gnsAut (hα g) _ = _
  rw [gnsAut_coe]
  rfl

/-- The implementing unitaries intertwine the GNS representation with the symmetry:
`U_g π(a) = π(α_g a) U_g`. -/
lemma gnsUnitary_comp_gnsRep (g : Multiplicative G) (a : A) :
    ((gnsUnitary hα g : unitary (ω.GNS →L[ℂ] ω.GNS)) : ω.GNS →L[ℂ] ω.GNS) * ω.gnsRep a =
      ω.gnsRep (α g a) * ((gnsUnitary hα g : unitary (ω.GNS →L[ℂ] ω.GNS)) : ω.GNS →L[ℂ] ω.GNS) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (((gnsUnitary hα g : unitary (ω.GNS →L[ℂ] ω.GNS)) :
        ω.GNS →L[ℂ] ω.GNS) * ω.gnsRep a).continuous
      (ω.gnsRep (α g a) * ((gnsUnitary hα g : unitary (ω.GNS →L[ℂ] ω.GNS)) :
        ω.GNS →L[ℂ] ω.GNS)).continuous
  | ih x =>
    show gnsAut (hα g) (ω.toPositiveLinearMap.gnsStarAlgHom a (x : ω.GNS)) =
      ω.toPositiveLinearMap.gnsStarAlgHom (α g a) (gnsAut (hα g) (x : ω.GNS))
    rw [PositiveLinearMap.gnsStarAlgHom_apply, PositiveLinearMap.gnsStarAlgHom_apply]
    show gnsAut (hα g) (ω.toPositiveLinearMap.gnsNonUnitalStarAlgHom a (x : ω.GNS)) =
      ω.toPositiveLinearMap.gnsNonUnitalStarAlgHom (α g a) (gnsAut (hα g) (x : ω.GNS))
    rw [gnsAut_coe, PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe,
      PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe, gnsAut_coe]
    congr 1
    show ω.toPositiveLinearMap.toPreGNS ((α g) (a * ω.toPositiveLinearMap.ofPreGNS x)) =
      ω.toPositiveLinearMap.toPreGNS ((α g a) * (α g) (ω.toPositiveLinearMap.ofPreGNS x))
    rw [map_mul]

/-- The matrix coefficients of the GNS vectors `π(a) Ω` are the correlation functions of the
state: `⟪π(a) Ω, U_g π(a) Ω⟫ = ω(a⋆ α_g(a))`. -/
lemma inner_gnsRep_cyclicVector_gnsUnitary (g : Multiplicative G) (a : A) :
    ⟪ω.gnsRep a ω.gnsCyclicVector,
      ((gnsUnitary hα g : unitary (ω.GNS →L[ℂ] ω.GNS)) : ω.GNS →L[ℂ] ω.GNS)
        (ω.gnsRep a ω.gnsCyclicVector)⟫_ℂ = ω (star a * α g a) := by
  rw [gnsUnitary_gnsRep_cyclicVector hα g a]
  have h : ⟪ω.gnsRep a ω.gnsCyclicVector, ω.gnsRep (α g a) ω.gnsCyclicVector⟫_ℂ =
      ⟪ω.gnsCyclicVector, ω.gnsRep (star a) (ω.gnsRep (α g a) ω.gnsCyclicVector)⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_left (ω.gnsRep (star a)),
      ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    simp
  rw [h, ← mul_apply_eq_comp, ← map_mul, inner_gnsCyclicVector_gnsRep_gnsCyclicVector]

end Group

end UnitalPositiveLinearMap

end ProbabilisticTheory

end
