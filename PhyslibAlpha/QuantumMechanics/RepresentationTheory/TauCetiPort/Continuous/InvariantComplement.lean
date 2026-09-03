/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RepresentationTheory.Submodule
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.Unitary.Basic
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Subrepresentation

/-!
# Invariant complements of unitary continuous representations

For a unitary representation of a *group* the orthogonal complement of an invariant subspace is
again invariant, so an invariant subspace admitting an orthogonal projection has an invariant
complement. This is the averaging-free half of complete reducibility: it needs no measure, only
that every action operator preserves the inner product.

Invariance of a submodule is Mathlib's `Representation.invtSubmodule`, the sublattice of submodules
invariant under every action operator, and semisimplicity is Mathlib's
`Representation.IsSemisimpleRepresentation`, the statement that the lattice of subrepresentations is
complemented.

## Main definitions

* `TauCeti.ContRepresentation.IsUnitary.orthogonalSubrepresentation`: the orthogonal complement of
  a subrepresentation of a unitary representation, as a subrepresentation.
* `TauCeti.ContRepresentation.IsUnitary.starProjectionIntertwiner`: the orthogonal projection onto
  an invariant subspace, as a continuous intertwining map.

## Main results

* `TauCeti.ContRepresentation.IsUnitary.orthogonal_mem_invtSubmodule`: for a unitary representation
  of a group, the orthogonal complement of an invariant submodule is invariant. The element form is
  `TauCeti.ContRepresentation.IsUnitary.apply_mem_orthogonal`.
* `TauCeti.ContRepresentation.IsUnitary.isCompl_orthogonalSubrepresentation`: a subrepresentation
  admitting an orthogonal projection is complemented by its orthogonal complement.
* `TauCeti.ContRepresentation.IsUnitary.sup_orthogonalSubrepresentation_inf`: a subrepresentation
  together with its orthogonal complement inside a larger one recovers the larger one.
* `TauCeti.ContRepresentation.IsUnitary.starProjection_apply_comm`: the orthogonal projection onto
  an invariant subspace commutes with the action.
* `TauCeti.ContRepresentation.IsUnitary.isSemisimpleRepresentation` and
  `TauCeti.ContRepresentation.IsUnitary.isSemisimpleModule_asModule`: complete reducibility of a
  finite-dimensional unitary continuous representation, in the subrepresentation-lattice form and
  as semisimplicity of the group-algebra module.

## Implementation notes

The hypothesis that `G` is a group is essential and is not a convenience: the unilateral shift is a
unitary representation of the monoid `ℕ` on `ℓ²` for which the orthogonal complement of an
invariant subspace need not be invariant. What the proof uses is that the action of `g⁻¹` carries
the invariant subspace back into itself.

Nothing here assumes `V` complete. Mathlib's `ContinuousLinearMap.orthogonal_mem_invtSubmodule`
draws the same conclusion for a single operator `T`, from invariance under `T.adjoint`, but
`ContinuousLinearMap.adjoint` is available only on a complete space, so that route would force
`[CompleteSpace V]` on every statement below. Instead `IsUnitary.inner_map_right` moves the action
across the inner product by inverting the group element, which needs no completeness. Mathlib keeps
a completeness-free counterpart of the same result for symmetric operators, namely
`LinearMap.IsSymmetric.orthogonalComplement_mem_invtSubmodule`.

Complementation of a single subrepresentation asks only for an orthogonal projection onto it. The
semisimplicity statement, which asks it of *every* subrepresentation, is stated in finite
dimensions, where every subspace is complete and hence has one. It is false for a general
infinite-dimensional unitary representation, whose invariant subspaces decompose it as a Hilbert
direct sum but not as an algebraic one.

## References

This file builds the invariant-complement milestone of Layer 2 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/roadmap/representation-theory/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
whose `Suggested.lean` names it `orthogonal_invariant`. The mathematical development follows Daniel
Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

namespace ContRepresentation

/-! ### The orthogonal complement of an invariant subspace -/

section Unitary

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  {π : ContRepresentation 𝕜 G V}

namespace IsUnitary

variable {W : Submodule 𝕜 V}

/-- For a unitary representation of a group, the action carries the orthogonal complement of an
invariant subspace into itself. -/
theorem apply_mem_orthogonal (hπ : IsUnitary π) (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) (g : G) {v : V}
    (hv : v ∈ Wᗮ) : π g v ∈ Wᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [hπ.inner_map_right]
  exact hv _ (hW g⁻¹ u hu)

/-- **Invariant complements.** For a unitary representation of a group, the orthogonal complement
of an invariant submodule is again invariant. -/
theorem orthogonal_mem_invtSubmodule (hπ : IsUnitary π)
    (hW : W ∈ π.toRepresentation.invtSubmodule) : Wᗮ ∈ π.toRepresentation.invtSubmodule := by
  rw [Representation.mem_invtSubmodule] at hW ⊢
  exact fun g _ hv => hπ.apply_mem_orthogonal (fun g' _ hu => hW g' hu) g hv

/-- The orthogonal complement of a subrepresentation of a unitary representation, as a
subrepresentation. -/
def orthogonalSubrepresentation (hπ : IsUnitary π) (σ : Subrepresentation π.toRepresentation) :
    Subrepresentation π.toRepresentation where
  toSubmodule := σ.toSubmoduleᗮ
  apply_mem_toSubmodule g _ hv :=
    hπ.apply_mem_orthogonal (fun g' _ hu => σ.apply_mem_toSubmodule g' hu) g hv

@[simp]
theorem toSubmodule_orthogonalSubrepresentation (hπ : IsUnitary π)
    (σ : Subrepresentation π.toRepresentation) :
    (hπ.orthogonalSubrepresentation σ).toSubmodule = σ.toSubmoduleᗮ :=
  (rfl)

section Projection

variable [W.HasOrthogonalProjection]

/-- The orthogonal projection onto an invariant subspace of a unitary representation commutes with
the action. -/
theorem starProjection_apply_comm (hπ : IsUnitary π) (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) (g : G)
    (v : V) : W.starProjection (π g v) = π g (W.starProjection v) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal' (z := π g (v - W.starProjection v))
    (hW g _ (W.starProjection_apply_mem v))
    (hπ.apply_mem_orthogonal hW g (W.sub_starProjection_mem_orthogonal v)) ?_
  rw [← map_add, add_sub_cancel]

/-- The orthogonal projection onto an invariant subspace of a unitary representation, as a
continuous intertwining map. -/
noncomputable def starProjectionIntertwiner (hπ : IsUnitary π)
    (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) : ContIntertwiningMap π π where
  __ := W.starProjection
  isIntertwining' g := by
    ext v
    exact hπ.starProjection_apply_comm hW g v

@[simp]
theorem toContinuousLinearMap_starProjectionIntertwiner (hπ : IsUnitary π)
    (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) :
    (hπ.starProjectionIntertwiner hW).toContinuousLinearMap = W.starProjection :=
  (rfl)

@[simp]
theorem starProjectionIntertwiner_apply (hπ : IsUnitary π) (hW : ∀ g, ∀ v ∈ W, π g v ∈ W) (v : V) :
    hπ.starProjectionIntertwiner hW v = W.starProjection v :=
  (rfl)

end Projection

/-- A subrepresentation of a unitary representation is complemented by its orthogonal complement,
as soon as it admits an orthogonal projection. -/
theorem isCompl_orthogonalSubrepresentation (hπ : IsUnitary π)
    (σ : Subrepresentation π.toRepresentation) [σ.toSubmodule.HasOrthogonalProjection] :
    IsCompl σ (hπ.orthogonalSubrepresentation σ) := by
  have h : IsCompl σ.toSubmodule σ.toSubmoduleᗮ := σ.toSubmodule.isCompl_orthogonal
  constructor
  · rw [disjoint_iff]
    exact Subrepresentation.toSubmodule_injective h.inf_eq_bot
  · rw [codisjoint_iff]
    exact Subrepresentation.toSubmodule_injective h.sup_eq_top

/-- A subrepresentation, together with its orthogonal complement taken inside a larger
subrepresentation, recovers that larger subrepresentation. This is
`Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection` read in the lattice of
subrepresentations, which is legitimate because unitarity makes the orthogonal complement
invariant. -/
theorem sup_orthogonalSubrepresentation_inf (hπ : IsUnitary π)
    {σ τ : Subrepresentation π.toRepresentation} (h : σ ≤ τ)
    [σ.toSubmodule.HasOrthogonalProjection] :
    σ ⊔ hπ.orthogonalSubrepresentation σ ⊓ τ = τ := by
  refine Subrepresentation.toSubmodule_injective ?_
  rw [Subrepresentation.toSubmodule_sup, Subrepresentation.toSubmodule_inf,
    toSubmodule_orthogonalSubrepresentation]
  exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
    (Subrepresentation.toSubmodule_le_toSubmodule.mpr h)

/-! ### Complete reducibility in finite dimensions -/

section FiniteDimensional

variable [FiniteDimensional 𝕜 V]

/-- **Complete reducibility.** A finite-dimensional unitary continuous representation of a group is
semisimple: every subrepresentation has a complement. -/
theorem isSemisimpleRepresentation (hπ : IsUnitary π) :
    Representation.IsSemisimpleRepresentation π.toRepresentation :=
  ⟨fun σ => ⟨_, hπ.isCompl_orthogonalSubrepresentation σ⟩⟩

/-- **Complete reducibility, algebraic form.** The group-algebra module of a finite-dimensional
unitary continuous representation of a group is semisimple. -/
theorem isSemisimpleModule_asModule (hπ : IsUnitary π) :
    IsSemisimpleModule (MonoidAlgebra 𝕜 G) π.toRepresentation.asModule :=
  (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule
    π.toRepresentation).mp hπ.isSemisimpleRepresentation

end FiniteDimensional

end IsUnitary

end Unitary

end ContRepresentation

end TauCeti
