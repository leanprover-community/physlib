/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.RepresentationTheory.Continuous.Basic
public import PhyslibAlpha.Mathematics.TauCeti.RepresentationTheory.Continuous.Subrepresentation

/-!
# Unitary continuous representations

This file defines when a continuous representation preserves a real or complex inner product.

## i. Overview

This file defines when a continuous representation preserves a real or complex inner product. It
characterizes unitarity through norm preservation, isometries, and Mathlib's `unitary` submonoid of
continuous linear operators, and records the basic inner-product identities, the coefficient bound,
and that unitarity passes to restrictions.

The operator characterizations reuse Mathlib's adjoint and unitary-operator theory.

The mathematical development follows Daniel Bump, *Lie Groups*, second edition, Chapters 2–4.

## ii. Key results

This file proves the statement described in the overview.

## iii. Table of contents

- A. Development

## iv. References

* Standard material; the statements and proofs are original to this formalization.
-/

public section

/-! ## A. Development -/

open scoped InnerProductSpace

namespace ContRepresentation

variable {R G V : Type*} [Ring R] [Group G] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V]

/-- Applying a continuous group representation at an element and then at its inverse cancels.

This restates `Representation.self_inv_apply` for the continuous action coercion, which `simp` does
not otherwise reach; it is an implementation detail of the inverse-transfer proofs below. -/
private lemma self_inv_apply (π : ContRepresentation R G V) (g : G) (v : V) :
    π g (π g⁻¹ v) = v :=
  Representation.self_inv_apply π.toRepresentation g v

section Monoid

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- A continuous representation is unitary when every action operator preserves the inner
product. -/
def IsUnitary (π : ContRepresentation 𝕜 G V) : Prop :=
  ∀ g v w, ⟪π g v, π g w⟫_𝕜 = ⟪v, w⟫_𝕜

/-- A representation is unitary exactly when every action map preserves norms. -/
lemma isUnitary_iff_norm_map (π : ContRepresentation 𝕜 G V) :
    IsUnitary π ↔ ∀ g v, ‖π g v‖ = ‖v‖ := by
  constructor
  · intro hπ g
    exact (LinearMap.norm_map_iff_inner_map_map (π g)).mpr (hπ g)
  · intro hπ g
    exact (LinearMap.norm_map_iff_inner_map_map (π g)).mp (hπ g)

/-- A representation is unitary exactly when every action map is an isometry. -/
lemma isUnitary_iff_isometry (π : ContRepresentation 𝕜 G V) :
    IsUnitary π ↔ ∀ g, Isometry (π g) := by
  rw [isUnitary_iff_norm_map]
  exact forall_congr' fun g ↦ (AddMonoidHomClass.isometry_iff_norm (π g)).symm

namespace IsUnitary

variable {π : ContRepresentation 𝕜 G V}

/-- A unitary representation preserves the inner product. -/
@[simp]
lemma inner_map_map (hπ : IsUnitary π) (g : G) (v w : V) :
    ⟪π g v, π g w⟫_𝕜 = ⟪v, w⟫_𝕜 :=
  hπ g v w

/-- Every action map of a unitary representation preserves norms. -/
@[simp]
lemma norm_map (hπ : IsUnitary π) (g : G) (v : V) :
    ‖π g v‖ = ‖v‖ :=
  (isUnitary_iff_norm_map π).mp hπ g v

/-- Every action operator of a unitary representation has operator norm at most `1`. -/
lemma norm_le_one (hπ : IsUnitary π) (g : G) : ‖π g‖ ≤ 1 :=
  (π g).opNorm_le_bound zero_le_one fun v ↦ by simp [hπ.norm_map]

/-- The action operators of a unitary representation are uniformly bounded, in the form taken
by the integrated-form API. -/
lemma exists_norm_le (hπ : IsUnitary π) : ∃ C, ∀ g, ‖π g‖ ≤ C :=
  ⟨1, hπ.norm_le_one⟩

/-- Every action map of a unitary representation is an isometry. -/
lemma isometry (hπ : IsUnitary π) (g : G) : Isometry (π g) :=
  (isUnitary_iff_isometry π).mp hπ g

/-- Every action map of a unitary representation is injective. -/
lemma injective (hπ : IsUnitary π) (g : G) : Function.Injective (π g) :=
  (hπ.isometry g).injective

/-- Restriction along a monoid homomorphism preserves unitarity. -/
lemma restrict {H : Type*} [Monoid H] (hπ : IsUnitary π) (φ : H →* G) :
    IsUnitary (π.restrict φ) :=
  fun h ↦ hπ (φ h)

/-- The restriction of a unitary representation to an invariant submodule is unitary. -/
lemma subrepresentation (hπ : IsUnitary π) {W : Submodule 𝕜 V}
    (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) : IsUnitary (subrepresentation π W hW) :=
  (isUnitary_iff_norm_map _).mpr fun g v => by
    rw [← Submodule.norm_coe, ← Submodule.norm_coe (s := W) v, coe_subrepresentation_apply,
      hπ.norm_map]

/-- A matrix coefficient of a unitary representation is bounded by the product of the vector
norms. -/
lemma norm_inner_map_le (hπ : IsUnitary π) (g : G) (v w : V) :
    ‖⟪π g v, w⟫_𝕜‖ ≤ ‖v‖ * ‖w‖ := by
  calc
    ‖⟪π g v, w⟫_𝕜‖ ≤ ‖π g v‖ * ‖w‖ := norm_inner_le_norm _ _
    _ = ‖v‖ * ‖w‖ := by rw [hπ.norm_map]

section

variable [CompleteSpace V]

/-- The adjoint of a unitary action operator is a left inverse. -/
lemma adjoint_comp_self (hπ : IsUnitary π) (g : G) :
    (ContinuousLinearMap.adjoint (π g)).comp (π g) = 1 :=
  (π g).inner_map_map_iff_adjoint_comp_self.mp (hπ g)

end

end IsUnitary

/-- The trivial continuous representation is unitary. -/
lemma isUnitary_trivial :
    IsUnitary (ContRepresentation.trivial 𝕜 G V) := by
  intro _ v w
  simp

end Monoid

section Group

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V] [CompleteSpace V]
variable {π : ContRepresentation 𝕜 G V}

/-- For a group representation, inner-product preservation is equivalent to every action operator
belonging to Mathlib's unitary submonoid. -/
lemma isUnitary_iff_mem_unitary (π : ContRepresentation 𝕜 G V) :
    IsUnitary π ↔ ∀ g, π g ∈ unitary (V →L[𝕜] V) := by
  constructor
  · intro hπ g
    apply ((Group.isUnit g).map π.toMonoidHom).mem_unitary_of_star_mul_self
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact (π g).inner_map_map_iff_adjoint_comp_self.mp (hπ g)
  · intro hπ g v w
    exact (π g).inner_map_map_of_mem_unitary (hπ g) v w

namespace IsUnitary

/-- Every action operator of a unitary group representation belongs to Mathlib's `unitary`
submonoid. -/
lemma mem_unitary (hπ : IsUnitary π) (g : G) :
    π g ∈ unitary (V →L[𝕜] V) :=
  (isUnitary_iff_mem_unitary π).mp hπ g

/-- The adjoint of a unitary action operator is a right inverse. -/
lemma self_comp_adjoint (hπ : IsUnitary π) (g : G) :
    (π g).comp (ContinuousLinearMap.adjoint (π g)) = 1 := by
  rw [← ContinuousLinearMap.mul_def]
  simpa only [ContinuousLinearMap.star_eq_adjoint] using
    Unitary.mul_star_self_of_mem (hπ.mem_unitary g)

omit [CompleteSpace V] in
/-- Moving a unitary action from the first inner-product argument to the second replaces the group
element by its inverse. -/
lemma inner_map_left (hπ : IsUnitary π) (g : G) (v w : V) :
    ⟪π g v, w⟫_𝕜 = ⟪v, π g⁻¹ w⟫_𝕜 := by
  simpa only [ContRepresentation.self_inv_apply] using hπ.inner_map_map g v (π g⁻¹ w)

omit [CompleteSpace V] in
/-- Moving a unitary action from the second inner-product argument to the first replaces the group
element by its inverse. -/
lemma inner_map_right (hπ : IsUnitary π) (g : G) (v w : V) :
    ⟪v, π g w⟫_𝕜 = ⟪π g⁻¹ v, w⟫_𝕜 := by
  simpa only [ContRepresentation.self_inv_apply] using hπ.inner_map_map g (π g⁻¹ v) w

/-- The adjoint of a unitary action operator is the action of the inverse group element. -/
@[simp]
lemma adjoint_eq_inv (hπ : IsUnitary π) (g : G) :
    ContinuousLinearMap.adjoint (π g) = π g⁻¹ := by
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  simpa using hπ.inner_map_left g⁻¹ v w

end IsUnitary

end Group

end ContRepresentation
