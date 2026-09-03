/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.StarSubalgebra
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Compact.ApproximateIdentity
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Compact.EigenspaceRepresentation

/-!
# The representative ring is dense in `C(G)`: the analytic core of Peter-Weyl

The **representative ring** `𝓡(G)` of `TauCeti/RepresentationTheory/Continuous/Representative.lean`
is the span, inside `C(G, 𝕜)`, of the matrix coefficients of the finite-dimensional continuous
representations of `G`. This file proves that on a compact group it is **uniformly dense** in
`C(G, 𝕜)`; no separation axiom is needed for density, only for the point-separation corollaries
below, which read closedness of points off `isClosed_singleton` and so ask for `[T1Space G]`. That
density is the analytic core of the Peter-Weyl theorem: it is what makes the matrix coefficients
span a dense subspace of `L²(G)`, and hence what a Hilbert basis of `L²(G)` can be assembled from.

Two halves already available meet here, and neither of them presupposes any separation property of
`𝓡(G)`.

* Every convolution `k * f` by a *symmetric* kernel lies in the uniform closure of `𝓡(G)`
  (`TauCeti.convolutionCLM_mem_closure_representativeSubmodule`). This is the spectral half: the
  eigenspaces of the compact self-adjoint operator `convolutionOperator k` span a dense subspace of
  `L²(G)`, each of them is finite-dimensional and translation invariant, hence carries a
  finite-dimensional continuous representation, and the continuous representative of an eigenvector
  is one of its matrix coefficients.
* Convolution against a mollifying kernel supported near the identity moves a continuous function
  by an arbitrarily small amount in the uniform norm
  (`TauCeti.exists_isMollifier_norm_convolutionCLM_toLp_sub_le`), and a mollifying kernel is
  symmetric (`TauCeti.IsMollifier.inv_apply_eq_conj`). This is the approximate-identity half.

Putting them together, a continuous function is a uniform limit of functions in the closure of
`𝓡(G)`, so it lies in that closure: `TauCeti.dense_representativeSubmodule`.

**Point separation is a corollary, never an input.** Once density is known, and provided the points
of `G` are closed, `𝓡(G)` separates the points of `G` because `C(G, 𝕜)` does: the values `0` and `1`
of a Urysohn function at two distinct points cannot both be approximated to within `1/2` by a
function taking equal values there. Closed points are exactly what this last step needs, and
nothing before it, which is why only the results below carry `[T1Space G]`. Since a span separates
two points only if one of its generators does, this upgrades to the statement that the
*finite-dimensional continuous representations themselves* separate the points of a compact
Hausdorff group (`TauCeti.exists_contRepresentation_apply_ne`): distinct group elements act
differently in some finite-dimensional continuous representation.

Finally the density is transported to `L²(G)`. The continuous functions are dense in `L²` of a
finite measure on a compact space (`ContinuousMap.toLp_denseRange`) and `𝓡(G)` is uniformly dense
in them, so the images of the matrix coefficients span a dense subspace of `L²(G)`, whose
orthogonal complement is therefore trivial. That vanishing complement is the hypothesis of
`HilbertBasis.mkOfOrthogonalEqBot`, so it is the form in which Layer 5 consumes this file.

## Implementation notes

The uniform density and the point separation drawn from it are purely topological statements, so
they take no measurable structure on `G`: the Haar measure their proofs run through is built on the
Borel σ-algebra installed inside those proofs. Only the `L²` statements name a measure, and they
alone carry `[MeasurableSpace G] [BorelSpace G]`.

The separation hypothesis on the point-separation results is spelled `[T1Space G]`, the closedness
of points that the Urysohn step consumes, rather than `[T2Space G]`. On a topological group the two
are the same condition: such a group is regular (`IsTopologicalGroup.regularSpace`), so `T1Space G`
already delivers `T3Space G`. These are therefore the usual compact Hausdorff statements, with the
separation axiom stated at the strength the proof actually uses.

## Main statements

* `TauCeti.dense_representativeSubmodule`: **the Peter-Weyl density theorem.** The representative
  ring is uniformly dense in `C(G, 𝕜)`.
* `TauCeti.representativeStarSubalgebra_dense`: the same, read on the representative
  `*`-subalgebra: its topological closure is everything.
* `TauCeti.representativeStarSubalgebra_separatesPoints`: **point separation, as a corollary.**
* `TauCeti.exists_contRepresentation_apply_ne`: **a compact Hausdorff group has enough
  finite-dimensional representations.** Two distinct elements act differently in some
  finite-dimensional continuous representation.
* `TauCeti.dense_image_toLp_representativeSubmodule` and
  `TauCeti.orthogonal_map_toLp_representativeSubmodule_eq_bot`: the representative ring is dense in
  `L²(G)`, equivalently its orthogonal complement there vanishes.

## References

This is `representativeStarSubalgebra_dense` and its corollary
`representativeStarSubalgebra_separatesPoints` from Layer 5 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
whose non-circular route to Peter-Weyl asks precisely that density be proved from the convolution
operators and an approximate identity, with point separation drawn from it afterwards.

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC (2016), §5.2.
* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 2.
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter III.
-/

public section

open MeasureTheory Set
open scoped InnerProductSpace

namespace TauCeti

open _root_.TauCeti.ContRepresentation

section CompactGroup

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

/-! ### Uniform density -/

variable (𝕜 G) in
/-- **The Peter-Weyl density theorem.** The representative ring `𝓡(G)` of a compact group is
uniformly dense in `C(G, 𝕜)`. Hausdorffness is not needed: the mollifiers the proof runs on are
built without it. -/
theorem dense_representativeSubmodule : Dense (representativeSubmodule 𝕜 G : Set C(G, 𝕜)) := by
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  intro f
  rw [← closure_closure (s := (representativeSubmodule 𝕜 G : Set C(G, 𝕜)))]
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  obtain ⟨k, hk, hle⟩ :=
    exists_isMollifier_norm_convolutionCLM_toLp_sub_le 𝕜 f (half_pos hε) Filter.univ_mem
  refine ⟨convolutionCLM k (ContinuousMap.toLp 2 (haarProb G) 𝕜 f),
    convolutionCLM_mem_closure_representativeSubmodule k hk.inv_apply_eq_conj _, ?_⟩
  rw [dist_comm, dist_eq_norm]
  exact hle.trans_lt (half_lt_self hε)

variable (𝕜 G) in
/-- The representative ring is dense, read as an equality of submodules: its topological closure is
the whole of `C(G, 𝕜)`. -/
theorem representativeSubmodule_topologicalClosure_eq_top :
    (representativeSubmodule 𝕜 G).topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.1 (dense_representativeSubmodule 𝕜 G)

variable (𝕜 G) in
/-- **The representative `*`-subalgebra is dense in `C(G, 𝕜)`.** The span carrying the algebra
structure is the same set as `TauCeti.representativeSubmodule`, so this is
`TauCeti.dense_representativeSubmodule` again; stating it on the `*`-subalgebra is what makes it
available to the Stone-Weierstrass vocabulary. -/
theorem representativeStarSubalgebra_dense :
    (representativeStarSubalgebra 𝕜 G).topologicalClosure = ⊤ := by
  have hcoe : (representativeStarSubalgebra 𝕜 G : Set C(G, 𝕜))
      = (representativeSubmodule 𝕜 G : Set C(G, 𝕜)) :=
    Set.ext fun _ => mem_representativeStarSubalgebra_iff
  refine SetLike.ext' ?_
  rw [StarSubalgebra.topologicalClosure_coe, StarSubalgebra.coe_top, hcoe]
  exact (dense_representativeSubmodule 𝕜 G).closure_eq

/-! ### Point separation -/

/-- **The representative ring separates the points of a compact Hausdorff group.**

Point separation is a *corollary* of `TauCeti.dense_representativeSubmodule`, and the roadmap's
non-circular route to Peter-Weyl depends on its never being assumed beforehand. -/
theorem exists_mem_representativeSubmodule_apply_ne [T1Space G] (x y : G) (hxy : x ≠ y) :
    ∃ f ∈ representativeSubmodule 𝕜 G, f x ≠ f y := by
  obtain ⟨u, hux, huy, -⟩ := exists_continuous_zero_one_of_isClosed (X := G)
    isClosed_singleton isClosed_singleton (Set.disjoint_singleton.2 hxy)
  obtain ⟨F, hFx, hFy⟩ : ∃ F : C(G, 𝕜), F x = 0 ∧ F y = 1 :=
    ⟨⟨fun g => ((u g : ℝ) : 𝕜), RCLike.continuous_ofReal.comp u.continuous⟩,
      by simpa using hux rfl, by simpa using huy rfl⟩
  obtain ⟨g, hg, hdist⟩ :=
    Metric.mem_closure_iff.1 (dense_representativeSubmodule 𝕜 G F) (1 / 2) (by norm_num)
  refine ⟨g, hg, fun hcon => ?_⟩
  rw [dist_eq_norm] at hdist
  have hxlt : ‖F x - g x‖ < 1 / 2 :=
    calc ‖F x - g x‖ = ‖(F - g) x‖ := by rw [ContinuousMap.sub_apply]
      _ ≤ ‖F - g‖ := (F - g).norm_coe_le_norm x
      _ < 1 / 2 := hdist
  have hylt : ‖F y - g y‖ < 1 / 2 :=
    calc ‖F y - g y‖ = ‖(F - g) y‖ := by rw [ContinuousMap.sub_apply]
      _ ≤ ‖F - g‖ := (F - g).norm_coe_le_norm y
      _ < 1 / 2 := hdist
  have hlt : ‖F x - F y‖ < 1 :=
    calc ‖F x - F y‖ = ‖(F x - g x) - (F y - g y)‖ := by rw [hcon]; congr 1; ring
      _ ≤ ‖F x - g x‖ + ‖F y - g y‖ := norm_sub_le _ _
      _ < 1 := by linarith
  rw [hFx, hFy] at hlt
  simp at hlt

/-- Point separation, read on the representative `*`-subalgebra: this is the roadmap's
`representativeStarSubalgebra_separatesPoints`. -/
theorem representativeStarSubalgebra_separatesPoints [T1Space G] (x y : G) (hxy : x ≠ y) :
    ∃ f ∈ representativeStarSubalgebra 𝕜 G, f x ≠ f y := by
  obtain ⟨f, hf, hne⟩ := exists_mem_representativeSubmodule_apply_ne (𝕜 := 𝕜) x y hxy
  exact ⟨f, mem_representativeStarSubalgebra_iff.2 hf, hne⟩

/-- **A single representative function already separates two distinct points**, and not merely a
linear combination of representative functions. -/
theorem exists_isRepresentative_apply_ne [T1Space G] (x y : G) (hxy : x ≠ y) :
    ∃ f : C(G, 𝕜), IsRepresentative f ∧ f x ≠ f y := by
  by_contra hcon
  have hall : Set.EqOn (ContinuousMap.evalCLM 𝕜 x).toLinearMap
      (ContinuousMap.evalCLM 𝕜 y).toLinearMap {f : C(G, 𝕜) | IsRepresentative f} := by
    intro f hf
    by_contra h
    exact hcon ⟨f, hf, h⟩
  obtain ⟨g, hg, hgxy⟩ := exists_mem_representativeSubmodule_apply_ne (𝕜 := 𝕜) x y hxy
  exact hgxy (LinearMap.eqOn_span hall (representativeSubmodule_eq_span 𝕜 G ▸ hg))

/-- **A compact Hausdorff group has enough finite-dimensional representations.** Two distinct
elements of `G` act differently in some finite-dimensional continuous representation.

This is the group-theoretic content of Peter-Weyl density: the finite-dimensional continuous
representations of a compact Hausdorff group are jointly faithful. -/
theorem exists_contRepresentation_apply_ne [T1Space G] (x y : G) (hxy : x ≠ y) :
    ∃ (n : ℕ) (π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin n))),
      Continuous π ∧ π x ≠ π y := by
  obtain ⟨f, hf, hne⟩ := exists_isRepresentative_apply_ne (𝕜 := 𝕜) x y hxy
  obtain ⟨n, π, hπ, v, w, rfl⟩ := isRepresentative_iff.1 hf
  refine ⟨n, π, hπ, fun hcon => hne ?_⟩
  rw [matrixCoeff_apply, matrixCoeff_apply, hcon]

/-! ### Density in `L²(G)` -/

section LTwo

variable [MeasurableSpace G] [BorelSpace G]

variable (𝕜 G) in
/-- **The representative ring is dense in `L²(G)`.** -/
theorem dense_image_toLp_representativeSubmodule :
    Dense (ContinuousMap.toLp 2 (haarProb G) 𝕜 '' (representativeSubmodule 𝕜 G : Set C(G, 𝕜))) :=
  (ContinuousMap.toLp_denseRange (E := 𝕜) (p := 2) (haarProb G) 𝕜 (by simp)).dense_image
    (ContinuousMap.toLp 2 (haarProb G) 𝕜).continuous (dense_representativeSubmodule 𝕜 G)

variable (𝕜 G) in
/-- The image of the representative ring in `L²(G)` has topological closure everything. -/
theorem map_toLp_representativeSubmodule_topologicalClosure_eq_top :
    ((representativeSubmodule 𝕜 G).map
      (ContinuousMap.toLp 2 (haarProb G) 𝕜 :
        C(G, 𝕜) →L[𝕜] Lp 𝕜 2 (haarProb G)).toLinearMap).topologicalClosure = ⊤ := by
  refine Submodule.dense_iff_topologicalClosure_eq_top.1 ?_
  rw [Submodule.map_coe]
  exact dense_image_toLp_representativeSubmodule 𝕜 G

variable (𝕜 G) in
/-- **The matrix coefficients have trivial orthogonal complement in `L²(G)`.** This is the form in
which the density is consumed by `HilbertBasis.mkOfOrthogonalEqBot`, which turns an orthonormal
system with vanishing orthogonal complement into a Hilbert basis; Schur orthogonality supplies the
orthonormality, and this supplies the completeness. -/
theorem orthogonal_map_toLp_representativeSubmodule_eq_bot :
    ((representativeSubmodule 𝕜 G).map
      (ContinuousMap.toLp 2 (haarProb G) 𝕜 :
        C(G, 𝕜) →L[𝕜] Lp 𝕜 2 (haarProb G)).toLinearMap)ᗮ = ⊥ :=
  Submodule.topologicalClosure_eq_top_iff.1
    (map_toLp_representativeSubmodule_topologicalClosure_eq_top 𝕜 G)

end LTwo

end CompactGroup

end TauCeti
