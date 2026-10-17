/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Spans of orthonormal subfamilies

For a finite-index orthonormal basis and a set of indices, `spanIndices` is the subspace spanned by
the corresponding basis vectors.

## i. Overview

For a finite-index orthonormal basis and a set of indices, `spanIndices` is the
subspace spanned by the corresponding basis vectors.

## ii. Key results

* `OrthonormalBasis.spanIndices_eq_span`: the explicit span characterization.
* `OrthonormalBasis.spanIndices_mono`: monotonicity under index-set inclusion.
* `OrthonormalBasis.mem_spanIndices_of_mem`: selected basis vectors belong to the span.
* `OrthonormalBasis.mem_spanIndices_iff`: membership means coordinates vanish
  outside the selected indices.
* `OrthonormalBasis.finrank_spanIndices`: the dimension of a selected finite span.
* `OrthonormalBasis.finrank_spanIndices_set`: dimension as set cardinality.
* `OrthonormalBasis.orthogonal_spanIndices`: orthogonal complement by index complement.

## iii. Table of contents

- A. Development

## iv. References

Source: Adapted from `ForTauCeti/Analysis/InnerProductSpace/BasisSpan.lean` in the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc.; Apache-2.0). The selected-span construction originates in the
Courant--Fischer development.
-/

public section

/-! ## A. Development -/

namespace OrthonormalBasis

open Module (finrank)
open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι]

/-- The subspace spanned by the orthonormal basis vectors `b i` for indices
`i ∈ s`. -/
noncomputable def spanIndices (b : OrthonormalBasis ι 𝕜 E) (s : Set ι) :
    Submodule 𝕜 E :=
  Submodule.span 𝕜 (b '' s)

/-- The selected subspace is the span of its basis vectors.
Use this identity to apply `Submodule.span`'s induction or universal property. -/
lemma spanIndices_eq_span (b : OrthonormalBasis ι 𝕜 E) (s : Set ι) :
    b.spanIndices s = Submodule.span 𝕜 (b '' s) := (rfl)

/-- Selecting more indices spans more. -/
lemma spanIndices_mono (b : OrthonormalBasis ι 𝕜 E) {s t : Set ι} (h : s ⊆ t) :
    b.spanIndices s ≤ b.spanIndices t := by
  rw [b.spanIndices_eq_span s, b.spanIndices_eq_span t]
  exact Submodule.span_mono (Set.image_mono h)

/-- A selected basis vector lies in the span of its index set. -/
lemma mem_spanIndices_of_mem (b : OrthonormalBasis ι 𝕜 E) {s : Set ι} {i : ι}
    (hi : i ∈ s) : b i ∈ b.spanIndices s := by
  rw [b.spanIndices_eq_span]
  exact Submodule.subset_span ⟨i, hi, rfl⟩

/-- A vector in the span of a selected subfamily has zero coordinate at any
index outside the selection. -/
lemma repr_eq_zero_of_mem_spanIndices (b : OrthonormalBasis ι 𝕜 E)
    {s : Set ι} {x : E} (hx : x ∈ b.spanIndices s) {i : ι} (hi : i ∉ s) :
    b.repr x i = 0 := by
  rw [b.spanIndices_eq_span] at hx
  rw [b.repr_apply_apply]
  -- `⟪b i, ·⟫` vanishes on the spanning set, hence on the whole span.
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨j, hj, rfl⟩
    refine b.inner_eq_zero ?_
    rintro rfl
    exact hi hj
  · rw [inner_zero_right]
  · intro y z _ _ hy hz
    rw [inner_add_right, hy, hz, add_zero]
  · intro a y _ hy
    rw [inner_smul_right, hy, mul_zero]

/-- Membership in the span of a selected subfamily is exactly the vanishing of
the coordinates outside the selection. -/
@[simp]
lemma mem_spanIndices_iff (b : OrthonormalBasis ι 𝕜 E)
    {s : Set ι} {x : E} :
    x ∈ b.spanIndices s ↔ ∀ i ∉ s, b.repr x i = 0 := by
  classical
  refine ⟨fun hx i hi => b.repr_eq_zero_of_mem_spanIndices hx hi, fun h => ?_⟩
  rw [← b.sum_repr x]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : i ∈ s
  · exact Submodule.smul_mem _ _ (b.mem_spanIndices_of_mem hi)
  · rw [h i hi, zero_smul]
    exact Submodule.zero_mem _

/-- The span of a selected subfamily has dimension the number of selected
indices. -/
lemma finrank_spanIndices (b : OrthonormalBasis ι 𝕜 E) (s : Finset ι) :
    finrank 𝕜 (b.spanIndices ↑s) = s.card := by
  have h : finrank 𝕜 (Submodule.span 𝕜
      (Set.range fun i : ↥(↑s : Set ι) => b ↑i)) = Fintype.card ↥(↑s : Set ι) :=
    finrank_span_eq_card
      (b.orthonormal.linearIndependent.comp _ Subtype.val_injective)
  rw [b.spanIndices_eq_span, Set.image_eq_range, h]
  simp

/-- The span of a selected set of basis vectors has dimension equal to the
number of selected indices. -/
lemma finrank_spanIndices_set (b : OrthonormalBasis ι 𝕜 E) (s : Set ι) :
    finrank 𝕜 (b.spanIndices s) = s.ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  rw [← b.finrank_spanIndices s.toFinset, Set.coe_toFinset]

/-- The orthogonal complement of the span of a selected subfamily is the span
of the complementary subfamily. -/
lemma orthogonal_spanIndices (b : OrthonormalBasis ι 𝕜 E) (s : Set ι) :
    (b.spanIndices s)ᗮ = b.spanIndices sᶜ := by
  classical
  have : FiniteDimensional 𝕜 E := Module.Finite.of_basis b.toBasis
  have hEcard : finrank 𝕜 E = Fintype.card ι := by
    rw [Module.finrank_eq_card_basis b.toBasis]
  refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
  · -- the complementary span is orthogonal to the selected span.
    rw [b.spanIndices_eq_span (sᶜ)]
    apply Submodule.span_le.mpr
    rintro y ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal]
    intro u hu
    rw [← inner_conj_symm, ← b.repr_apply_apply,
      b.repr_eq_zero_of_mem_spanIndices hu hj, map_zero]
  · -- dimensions match: `card ι − #s` on both sides.
    have h1 : finrank 𝕜 (b.spanIndices s)
        + finrank 𝕜 ((b.spanIndices s)ᗮ : Submodule 𝕜 E) = Fintype.card ι := by
      rw [Submodule.finrank_add_finrank_orthogonal, hEcard]
    have h2 := b.finrank_spanIndices_set s
    have h3 := b.finrank_spanIndices_set sᶜ
    have h4 : s.toFinset.card + (sᶜ).toFinset.card = Fintype.card ι := by
      rw [Set.toFinset_compl, Finset.card_compl]
      have := Finset.card_le_univ s.toFinset
      omega
    simp only [Set.ncard_eq_toFinset_card'] at h2 h3
    omega

end OrthonormalBasis

end
