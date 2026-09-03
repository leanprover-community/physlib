/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Analysis.InnerProductSpace.Parseval
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Compact.Orthonormal
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Compact.RepresentativeDensity
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.Conjugate
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.OrthogonalDecomposition
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.Unitary.Equivalence

/-!
# The Peter-Weyl theorem: the matrix coefficients are a Hilbert basis of `L²(G)`

Let `G` be a compact group. Schur orthogonality
(`TauCeti/RepresentationTheory/Compact/Orthonormal.lean`) says that the normalized matrix
coefficients `√(dim V_i) · (π i)_{ab}` of a family of pairwise inequivalent finite-dimensional
irreducible unitary continuous representations form an *orthonormal system* in `L²(G)`. This file
proves that when the family is moreover **exhaustive** the system is *complete*, so it is a
**Hilbert basis** of `L²(G)`: the Peter-Weyl theorem. Hausdorffness is nowhere needed, here or
in the unconditional standard basis at the end: what the density argument runs on are the
mollifiers of `Compact/ApproximateIdentity.lean`, which are built without it.

## "One representative per equivalence class" is data

The index of the basis is not free. It hides a choice of model spaces, of unitary irreducible
representations on them, and of orthonormal bases; a theorem that merely asserts the existence of
such a family says nothing about which functions the basis consists of. Both are pinned here.

* `TauCeti.IrrepModel` is one chosen model: a natural number `dim`, a continuous unitary
  irreducible representation on the standard Hilbert space `EuclideanSpace 𝕜 (Fin dim)`, whose
  orthonormal basis is therefore `EuclideanSpace.basisFun`, not a further choice.
* `TauCeti.IsIrrepSkeleton models` says the family `models` is a skeleton of the unitary dual:
  pairwise inequivalent, and exhaustive in the sense that every continuous unitary irreducible
  representation on a standard model space is carried onto some `models i` by a linear isometry
  equivalence. Exhaustion is asked for in unitary form, which is no restriction: between
  irreducible unitary representations Schur's lemma makes every intertwining isomorphism a scalar
  multiple of an isometry (`TauCeti.ContRepresentation.exists_linearIsometryEquiv_congr_eq`).
* `TauCeti.peterWeylBasis` is a `HilbertBasis`, defined outright rather than existentially, and
  `TauCeti.coe_peterWeylBasis` identifies its elements as the normalized matrix coefficients
  `TauCeti.peterWeylFamily`. The element-level content is therefore available on the nose.

Nothing here is conditional on a skeleton being available: one is built at the end of the file.
Because a model's carrier is a standard space `EuclideanSpace 𝕜 (Fin n)`, unitary equivalence is
an equivalence relation on the *type* `TauCeti.IrrepModel 𝕜 G`, and choosing a representative in
each class gives `TauCeti.IrrepClass.model`, a skeleton by
`TauCeti.isIrrepSkeleton_model`. Feeding it to `TauCeti.peterWeylBasis` gives
`TauCeti.stdPeterWeylBasis`, a Hilbert basis of `L²(G)` for every compact `G` with no
hypothesis left over. Pairwise inequivalence of the representatives is the point where the
rescaling above is used.

## The completeness argument

Orthonormality is quoted from Schur. Completeness is what is proved here, and it factors through
the span `TauCeti.modelSubmodule` of the matrix coefficients of the models inside `C(G, 𝕜)`.

1. *Irreducible representations.* A continuous unitary irreducible representation on any
   finite-dimensional inner product space is carried to a standard model by
   `stdOrthonormalBasis`, hence onto some `models i` by exhaustion, and matrix coefficients are
   unchanged along an isometry (`TauCeti.ContRepresentation.matrixCoeff_congr`).
2. *Unitary representations.* An arbitrary continuous unitary representation splits as an
   orthogonal direct sum of irreducible subrepresentations
   (`TauCeti.ContRepresentation.IsUnitary.exists_orthogonal_irreducible_decomposition`), and for
   a vector `v` in one block the functional `⟪·, w⟫` only sees the orthogonal projection of `w`
   onto that block, so every matrix coefficient reduces to matrix coefficients of the blocks.
3. *Density.* The analytic core of Peter-Weyl
   (`TauCeti/RepresentationTheory/Compact/RepresentativeDensity.lean`) approximates a continuous
   function by convolutions, and expands each convolution along the eigenspaces of the
   convolution operator. Those eigenspace representations are unitary
   (`TauCeti.isUnitary_convolutionEigenspaceRepresentation`), so step 2 applies to them and the
   *models'* coefficients are already uniformly dense: no unitarization of an arbitrary
   representation is needed anywhere.
4. *Passage to `L²`.* Continuous functions are dense in `L²` of a finite measure on a compact
   space, so the span of the models' coefficients is dense in `L²(G)` and its orthogonal
   complement vanishes, which is the hypothesis of `HilbertBasis.mkOfOrthogonalEqBot`.

## Main definitions

* `TauCeti.IrrepModel`, `TauCeti.IsIrrepSkeleton`: the chosen data and the exhaustion property.
* `TauCeti.modelSubmodule`: the span of the models' matrix coefficients in `C(G, 𝕜)`.
* `TauCeti.peterWeylFamily`: the normalized matrix coefficients, indexed by
  `Σ i, Fin (models i).dim × Fin (models i).dim`.
* `TauCeti.peterWeylBasis`: **the Peter-Weyl Hilbert basis of `L²(G)`.**
* `TauCeti.peterWeylCoeff`: the Fourier coefficient against a normalized matrix coefficient.
* `TauCeti.IrrepClass`, `TauCeti.IrrepClass.model`: the models up to unitary equivalence, and the
  representative chosen in each class.
* `TauCeti.stdPeterWeylBasis`: the Peter-Weyl basis of `L²(G)` on the chosen representatives, with
  no skeleton assumed.

## Main statements

* `TauCeti.IsIrrepSkeleton.matrixCoeff_mem`: every matrix coefficient of a finite-dimensional
  unitary continuous representation is a linear combination of the models' matrix coefficients.
* `TauCeti.IsIrrepSkeleton.dense_modelSubmodule`: those coefficients are uniformly dense in
  `C(G, 𝕜)`.
* `TauCeti.IsIrrepSkeleton.orthogonal_span_peterWeylFamily_eq_bot`: the completeness of the
  orthonormal system.
* `TauCeti.coe_peterWeylBasis`, `TauCeti.coe_stdPeterWeylBasis`: the basis is the normalized
  matrix coefficients.
* `TauCeti.peterWeylFamily_eq_toLp`: each family element is the `L²` class of its normalized
  continuous matrix coefficient.
* `TauCeti.coeFn_peterWeylFamily`: the almost-everywhere representative of a normalized matrix
  coefficient.
* `TauCeti.peterWeylBasis_repr_apply`, `TauCeti.stdPeterWeylBasis_repr_apply`: the abstract basis
  coordinates are the explicit Haar-integral Fourier coefficients.
* `TauCeti.hasSum_peterWeyl_expansion`: reconstruction of an `L²` function from its Peter-Weyl
  coefficients.
* `TauCeti.tsum_conj_peterWeylCoeff_mul_peterWeylCoeff`,
  `TauCeti.tsum_norm_sq_peterWeylCoeff`: polarized and norm-square Parseval identities.
* `TauCeti.isIrrepSkeleton_model`: the chosen representatives are a skeleton, so the hypothesis of
  `TauCeti.peterWeylBasis` is satisfiable and the theorem is not conditional.

## References

This is the summit `peterWeylBasis` of Layer 5 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
including its `IrrepModel` and `IsIrrepSkeleton` packaging and the requirement that the
element-level content of the basis be stated rather than left inside an existential.

* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 2.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC (2016), §5.2.
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter III.
-/

public section

open MeasureTheory Set
open scoped InnerProductSpace

namespace TauCeti

/-! ### Chosen models of the irreducible representations -/

/-- **A chosen model of a finite-dimensional irreducible unitary continuous representation.** The
carrier is the standard Hilbert space `EuclideanSpace 𝕜 (Fin dim)`, so the model comes with a
canonical orthonormal basis and no further choice is hidden in it. -/
structure IrrepModel (𝕜 G : Type*) [RCLike 𝕜] [Group G] [TopologicalSpace G] where
  /-- The dimension of the model, which is also the size of its index type. -/
  dim : ℕ
  /-- The representation carried by the model. -/
  rep : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin dim))
  /-- The model's action is continuous. -/
  continuous_rep : Continuous rep
  /-- The model's action is by unitary operators. -/
  isUnitary : ContRepresentation.IsUnitary rep
  /-- The model is irreducible. -/
  isIrreducible : Representation.IsIrreducible rep.toRepresentation

namespace IrrepModel

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G]

/-- The canonical orthonormal basis of the carrier of a model. -/
noncomputable def basis (m : IrrepModel 𝕜 G) :
    OrthonormalBasis (Fin m.dim) 𝕜 (EuclideanSpace 𝕜 (Fin m.dim)) :=
  EuclideanSpace.basisFun (Fin m.dim) 𝕜

end IrrepModel

section Skeleton

variable {𝕜 G ι : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- The set of all matrix coefficients of the members of a family of models. -/
def modelCoeffs (models : ι → IrrepModel 𝕜 G) : Set C(G, 𝕜) :=
  {f | ∃ i v w, f = ContRepresentation.matrixCoeff (models i).rep (models i).continuous_rep v w}

/-- The span, inside `C(G, 𝕜)`, of the matrix coefficients of a family of models. Peter-Weyl is
the statement that for a skeleton of the unitary dual this is dense. -/
noncomputable def modelSubmodule (models : ι → IrrepModel 𝕜 G) : Submodule 𝕜 C(G, 𝕜) :=
  Submodule.span 𝕜 (modelCoeffs models)

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- A matrix coefficient of a model lies in the span of the models' matrix coefficients. -/
theorem matrixCoeff_mem_modelSubmodule (models : ι → IrrepModel 𝕜 G) (i : ι)
    (v w : EuclideanSpace 𝕜 (Fin (models i).dim)) :
    ContRepresentation.matrixCoeff (models i).rep (models i).continuous_rep v w ∈
      modelSubmodule models :=
  Submodule.subset_span ⟨i, v, w, rfl⟩

/-- **A skeleton of the unitary dual of `G`.** The family `models` is pairwise inequivalent and
exhausts the finite-dimensional irreducible unitary continuous representations: every one of them
on a standard model space is carried onto some `models i` by a linear isometry equivalence.

Exhaustion in *unitary* form is no restriction. Between finite-dimensional irreducible unitary
representations Schur's lemma makes any intertwining isomorphism a scalar multiple of a unitary
one (`TauCeti.ContRepresentation.exists_linearIsometryEquiv_congr_eq`), so a family exhaustive up
to isomorphism is exhaustive up to unitary isomorphism. -/
structure IsIrrepSkeleton (models : ι → IrrepModel 𝕜 G) : Prop where
  /-- Distinct members of the family are inequivalent. -/
  pairwise_isEmpty_equiv :
    Pairwise fun i j ↦ IsEmpty (_root_.ContRepresentation.Equiv (models i).rep (models j).rep)
  /-- Every continuous unitary irreducible representation on a standard model space is carried
  onto a member of the family by a linear isometry equivalence. -/
  exists_congr_eq (n : ℕ) (π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin n)))
    (hπ : Continuous π) (hu : ContRepresentation.IsUnitary π)
    (hirr : π.toRepresentation.IsIrreducible) :
    ∃ (i : ι) (e : EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin (models i).dim)),
      ContRepresentation.congr e.toContinuousLinearEquiv π = (models i).rep

namespace IsIrrepSkeleton

variable {models : ι → IrrepModel 𝕜 G}

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- **The matrix coefficients of an irreducible representation are accounted for.** A
finite-dimensional irreducible unitary continuous representation is carried to a standard model by
`stdOrthonormalBasis`, and from there onto a member of the skeleton; matrix coefficients survive
both isometries. -/
theorem matrixCoeff_mem_of_isIrreducible (h : IsIrrepSkeleton models) {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    {π : ContRepresentation 𝕜 G V} (hπ : Continuous π) (hu : ContRepresentation.IsUnitary π)
    (hirr : π.toRepresentation.IsIrreducible) (v w : V) :
    ContRepresentation.matrixCoeff π hπ v w ∈ modelSubmodule models := by
  set e := (stdOrthonormalBasis 𝕜 V).repr
  obtain ⟨i, e', hi⟩ := h.exists_congr_eq _ (ContRepresentation.congr e.toContinuousLinearEquiv π)
    (ContRepresentation.continuous_congr _ hπ) (hu.congr e)
    (ContRepresentation.isIrreducible_congr _ hirr)
  refine Submodule.subset_span ⟨i, e' (e v), e' (e w), ?_⟩
  ext g
  have hg : (models i).rep g = ContRepresentation.congr e'.toContinuousLinearEquiv
      (ContRepresentation.congr e.toContinuousLinearEquiv π) g := by rw [hi]
  rw [ContRepresentation.matrixCoeff_apply, ContRepresentation.matrixCoeff_apply, hg]
  simp

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- **A matrix coefficient of a vector in an irreducible invariant subspace is accounted for.**
If `W` is a finite-dimensional subspace invariant under `π`, on which `π` restricts to a unitary
irreducible representation, then for `x ∈ W` and any `w` the matrix coefficient of `π` at `x`, `w`
lies in the span of the skeleton's coefficients. -/
theorem matrixCoeff_mem_of_mem_of_isIrreducible (h : IsIrrepSkeleton models) {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    {π : ContRepresentation 𝕜 G V} (hπ : Continuous π)
    {W : Submodule 𝕜 V} [FiniteDimensional 𝕜 W] (hU : ∀ g, ∀ y ∈ W, π g y ∈ W)
    (hu : ContRepresentation.IsUnitary (ContRepresentation.subrepresentation π W hU))
    {x : V} (hx : x ∈ W)
    (hirr : (ContRepresentation.subrepresentation π W hU).toRepresentation.IsIrreducible)
    (w : V) :
    ContRepresentation.matrixCoeff π hπ x w ∈ modelSubmodule models := by
  -- Only the component of `w` in the subspace is seen.
  have hproj : ContRepresentation.matrixCoeff π hπ x w
      = ContRepresentation.matrixCoeff π hπ x (W.starProjection w) := by
    ext g
    rw [ContRepresentation.matrixCoeff_apply, ContRepresentation.matrixCoeff_apply]
    calc ⟪π g x, w⟫_𝕜 = ⟪W.starProjection (π g x), w⟫_𝕜 := by
          rw [Submodule.starProjection_eq_self_iff.2 (hU g x hx)]
      _ = ⟪π g x, W.starProjection w⟫_𝕜 :=
          Submodule.inner_starProjection_left_eq_right _ _ _
  have hblock := h.matrixCoeff_mem_of_isIrreducible
    (π := ContRepresentation.subrepresentation π W hU)
    (ContRepresentation.continuous_subrepresentation hπ) hu hirr
    ⟨x, hx⟩ ⟨W.starProjection w, W.starProjection_apply_mem w⟩
  have heq := ContRepresentation.matrixCoeff_subrepresentation (π := π) (hπ := hπ) hU
    (⟨x, hx⟩ : W) ⟨W.starProjection w, W.starProjection_apply_mem w⟩
  rw [hproj, ← heq]
  exact hblock

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- **The matrix coefficients of a unitary representation are accounted for.** Complete
reducibility splits the representation into irreducible blocks orthogonally, and the inner product
against a fixed vector only sees that vector's component in the block, so every matrix coefficient
of the whole is a sum of matrix coefficients of the blocks. -/
theorem matrixCoeff_mem (h : IsIrrepSkeleton models) {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V] {π : ContRepresentation 𝕜 G V}
    (hπ : Continuous π) (hu : ContRepresentation.IsUnitary π) (v w : V) :
    ContRepresentation.matrixCoeff π hπ v w ∈ modelSubmodule models := by
  obtain ⟨n, U, hirr, -, hint, -⟩ := hu.exists_orthogonal_irreducible_decomposition
  -- The vectors all of whose matrix coefficients are accounted for form a submodule.
  set S : Submodule 𝕜 V :=
    { carrier := {v | ∀ w, ContRepresentation.matrixCoeff π hπ v w ∈ modelSubmodule models}
      add_mem' := fun ha hb w ↦ by
        rw [ContRepresentation.matrixCoeff_add_left]
        exact add_mem (ha w) (hb w)
      zero_mem' := fun w ↦ by
        rw [ContRepresentation.matrixCoeff_zero_left]
        exact zero_mem _
      smul_mem' := fun c _ ha w ↦ by
        rw [ContRepresentation.matrixCoeff_smul_left]
        exact Submodule.smul_mem _ _ (ha w) }
  have hle : ∀ i, (U i).toSubmodule ≤ S := by
    intro i x hx w
    have hU : ∀ g, ∀ y ∈ (U i).toSubmodule, π g y ∈ (U i).toSubmodule :=
      fun g y hy ↦ (U i).apply_mem_toSubmodule g hy
    have hirr' : (ContRepresentation.subrepresentation π (U i).toSubmodule
        hU).toRepresentation.IsIrreducible := by
      rw [ContRepresentation.toRepresentation_subrepresentation]
      exact hirr i
    exact h.matrixCoeff_mem_of_mem_of_isIrreducible hπ hU (hu.subrepresentation hU) hx hirr' w
  have htop : (⊤ : Submodule 𝕜 V) ≤ S := hint.submodule_iSup_eq_top ▸ iSup_le hle
  exact htop Submodule.mem_top w

/-! ### Density -/

/-- Convolving a finite sum of eigenvectors of a convolution operator lands in the span of the
models' matrix coefficients: each nonzero eigenspace carries a *unitary* finite-dimensional
continuous representation, so `TauCeti.IsIrrepSkeleton.matrixCoeff_mem` applies to it. -/
theorem convolutionCLM_mem_modelSubmodule (h : IsIrrepSkeleton models) (k : C(G, 𝕜))
    {f : Lp 𝕜 2 (haarProb G)}
    (hf : f ∈ ⨆ μ : 𝕜, Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :
    convolutionCLM k f ∈ modelSubmodule models := by
  refine Submodule.iSup_induction
    (motive := fun x ↦ convolutionCLM k x ∈ modelSubmodule models) _ hf (fun μ x hx ↦ ?_)
    (by rw [map_zero]; exact zero_mem _) fun x y hx hy ↦ ?_
  · rcases eq_or_ne μ 0 with rfl | hμ
    · rw [convolutionCLM_eq_zero_of_mem_eigenspace_zero k hx]
      exact zero_mem _
    have := finiteDimensional_eigenspace_convolutionOperator k hμ
    obtain ⟨y, hy⟩ := exists_smul_convolutionCLM_eq_star_matrixCoeff k hμ
    have hsmul : convolutionCLM k x = μ • (μ⁻¹ • convolutionCLM k x) := by
      rw [smul_smul, mul_inv_cancel₀ hμ, one_smul]
    rw [hsmul, hy x hx]
    refine Submodule.smul_mem _ _ ?_
    -- the conjugate of a matrix coefficient is a matrix coefficient of the conjugate
    -- representation, which is again unitary
    rw [ContRepresentation.star_matrixCoeff_eq_matrixCoeff_conjugate
      (stdOrthonormalBasis 𝕜 (Module.End.eigenspace
        (convolutionOperator (G := G) k).toLinearMap μ))]
    exact h.matrixCoeff_mem _
      (ContRepresentation.IsUnitary.conjugate _
        (isUnitary_convolutionEigenspaceRepresentation k μ)) _ _
  · rw [map_add]
    exact add_mem hx hy

/-- Every convolution by a symmetric kernel lies in the uniform closure of the span of the models'
matrix coefficients. -/
theorem convolutionCLM_mem_closure_modelSubmodule (h : IsIrrepSkeleton models) (k : C(G, 𝕜))
    (hk : ∀ g : G, k g⁻¹ = (starRingEnd 𝕜) (k g)) (f : Lp 𝕜 2 (haarProb G)) :
    convolutionCLM k f ∈ closure (modelSubmodule models : Set C(G, 𝕜)) := by
  set S := ⨆ μ : 𝕜, Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ
  have htop : S.topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.2
      (orthogonalComplement_iSup_eigenspaces_convolutionOperator_eq_bot k hk)
  have hf : f ∈ closure (S : Set (Lp 𝕜 2 (haarProb G))) := by
    rw [← Submodule.topologicalClosure_coe, htop]
    exact Submodule.mem_top
  refine closure_mono ?_
    (image_closure_subset_closure_image (convolutionCLM (G := G) k).continuous ⟨f, hf, rfl⟩)
  rintro - ⟨y, hy, rfl⟩
  exact h.convolutionCLM_mem_modelSubmodule k hy

/-- **The models' matrix coefficients are uniformly dense in `C(G, 𝕜)`.** This is the Peter-Weyl
density theorem sharpened from "all finite-dimensional representations" to "the chosen
irreducible ones": convolving by an approximate identity moves a continuous function arbitrarily
little, and every convolution is already a uniform limit of the models' coefficients. -/
theorem dense_modelSubmodule (h : IsIrrepSkeleton models) :
    Dense (modelSubmodule models : Set C(G, 𝕜)) := by
  intro F
  rw [← closure_closure (s := (modelSubmodule models : Set C(G, 𝕜)))]
  refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
  obtain ⟨k, hk, hle⟩ :=
    exists_isMollifier_norm_convolutionCLM_toLp_sub_le 𝕜 F (half_pos hε) Filter.univ_mem
  refine ⟨convolutionCLM k (ContinuousMap.toLp 2 (haarProb G) 𝕜 F),
    h.convolutionCLM_mem_closure_modelSubmodule k hk.inv_apply_eq_conj _, ?_⟩
  rw [dist_comm, dist_eq_norm]
  exact hle.trans_lt (half_lt_self hε)

/-- The models' matrix coefficients are dense in `L²(G)`. -/
theorem dense_image_toLp_modelSubmodule (h : IsIrrepSkeleton models) :
    Dense (ContinuousMap.toLp 2 (haarProb G) 𝕜 '' (modelSubmodule models : Set C(G, 𝕜))) :=
  (ContinuousMap.toLp_denseRange (E := 𝕜) (p := 2) (haarProb G) 𝕜 (by simp)).dense_image
    (ContinuousMap.toLp 2 (haarProb G) 𝕜).continuous h.dense_modelSubmodule

end IsIrrepSkeleton

/-! ### The Peter-Weyl basis -/

/-- **The normalized matrix coefficients of a family of models**, indexed by
`Σ i, Fin (models i).dim × Fin (models i).dim`. The scalar `√(dim)` is what Schur orthogonality
normalizes away. -/
noncomputable def peterWeylFamily (models : ι → IrrepModel 𝕜 G)
    (x : Σ i, Fin (models i).dim × Fin (models i).dim) : Lp 𝕜 2 (haarProb G) :=
  (Real.sqrt (models x.1).dim : 𝕜) •
    ContRepresentation.matrixCoeffLp (models x.1).rep (models x.1).continuous_rep
      ((models x.1).basis x.2.1) ((models x.1).basis x.2.2)

/-- The elements of the Peter-Weyl family, on the nose. -/
@[simp]
theorem peterWeylFamily_apply (models : ι → IrrepModel 𝕜 G)
    (x : Σ i, Fin (models i).dim × Fin (models i).dim) :
    peterWeylFamily models x =
      (Real.sqrt (models x.1).dim : 𝕜) •
        ContRepresentation.matrixCoeffLp (models x.1).rep (models x.1).continuous_rep
          ((models x.1).basis x.2.1) ((models x.1).basis x.2.2) :=
  (rfl)

/-- A Peter-Weyl family element is the `L²` class of its normalized continuous matrix
coefficient. -/
theorem peterWeylFamily_eq_toLp (models : ι → IrrepModel 𝕜 G)
    (x : Σ i, Fin (models i).dim × Fin (models i).dim) :
    peterWeylFamily models x =
      ContinuousMap.toLp 2 (haarProb G) 𝕜
        ((Real.sqrt (models x.1).dim : 𝕜) •
          ContRepresentation.matrixCoeff (models x.1).rep (models x.1).continuous_rep
            ((models x.1).basis x.2.1) ((models x.1).basis x.2.2)) := by
  rw [peterWeylFamily_apply, ContRepresentation.matrixCoeffLp_def, map_smul]

/-- A normalized Peter-Weyl matrix coefficient in `L²` is represented almost everywhere by its
defining continuous function. -/
theorem coeFn_peterWeylFamily (models : ι → IrrepModel 𝕜 G)
    (x : Σ i, Fin (models i).dim × Fin (models i).dim) :
    peterWeylFamily models x =ᵐ[haarProb G] fun g ↦
      (Real.sqrt (models x.1).dim : 𝕜) *
        ⟪(models x.1).rep g ((models x.1).basis x.2.1), (models x.1).basis x.2.2⟫_𝕜 := by
  filter_upwards [Lp.coeFn_smul (Real.sqrt (models x.1).dim : 𝕜)
    (ContRepresentation.matrixCoeffLp (models x.1).rep (models x.1).continuous_rep
      ((models x.1).basis x.2.1) ((models x.1).basis x.2.2)),
    ContRepresentation.coeFn_matrixCoeffLp (models x.1).rep (models x.1).continuous_rep
      ((models x.1).basis x.2.1) ((models x.1).basis x.2.2)] with g hsmul hcoeff
  rw [peterWeylFamily_apply, hsmul, Pi.smul_apply, hcoeff, smul_eq_mul]

/-- Every `L²` matrix coefficient of a model lies in the span of the normalized ones: expand both
defining vectors in the canonical orthonormal basis and use sesquilinearity. -/
theorem matrixCoeffLp_mem_span_peterWeylFamily (models : ι → IrrepModel 𝕜 G) (i : ι)
    (v w : EuclideanSpace 𝕜 (Fin (models i).dim)) :
    ContRepresentation.matrixCoeffLp (models i).rep (models i).continuous_rep v w ∈
      Submodule.span 𝕜 (Set.range (peterWeylFamily models)) := by
  classical
  set P := Submodule.span 𝕜 (Set.range (peterWeylFamily models))
  -- the coefficients at two basis vectors, before normalization
  have hbase : ∀ a b : Fin (models i).dim,
      ContRepresentation.matrixCoeffLp (models i).rep (models i).continuous_rep
        ((models i).basis a) ((models i).basis b) ∈ P := by
    intro a b
    have hd : (0 : ℝ) < (models i).dim := by exact_mod_cast Fin.pos a
    have hne : (Real.sqrt (models i).dim : 𝕜) ≠ 0 := by
      simpa using (Real.sqrt_pos.2 hd).ne'
    have hmem : peterWeylFamily models ⟨i, a, b⟩ ∈ P := Submodule.subset_span ⟨⟨i, a, b⟩, rfl⟩
    have := Submodule.smul_mem P ((Real.sqrt (models i).dim : 𝕜))⁻¹ hmem
    rwa [peterWeylFamily, smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have hspan : Submodule.span 𝕜 (Set.range ⇑(models i).basis) = ⊤ := by
    rw [← OrthonormalBasis.coe_toBasis]
    exact (models i).basis.toBasis.span_eq
  -- Each slot of the bundled sesquilinear coefficient map is (semi)linear, so membership in `P`
  -- spreads from the basis over the whole span; `hspan` says that span is everything.
  have hright : ∀ (a : Fin (models i).dim) (u : EuclideanSpace 𝕜 (Fin (models i).dim)),
      ContRepresentation.matrixCoeffLp (models i).rep (models i).continuous_rep
        ((models i).basis a) u ∈ P := fun a u => by
    have himg := (Submodule.image_span_subset
      (ContRepresentation.matrixCoeffLpₛₗ (models i).rep (models i).continuous_rep
        ((models i).basis a)) (Set.range ⇑(models i).basis) P).2
      (by rintro _ ⟨b, rfl⟩; simpa using hbase a b)
    simpa using himg ⟨u, hspan ▸ Submodule.mem_top, rfl⟩
  have himg := (Submodule.image_span_subset
    ((ContRepresentation.matrixCoeffLpₛₗ (models i).rep (models i).continuous_rep).flip w)
    (Set.range ⇑(models i).basis) P).2 (by rintro _ ⟨a, rfl⟩; simpa using hright a w)
  simpa using himg ⟨v, hspan ▸ Submodule.mem_top, rfl⟩

namespace IsIrrepSkeleton

variable {models : ι → IrrepModel 𝕜 G}

/-- **The normalized matrix coefficients of a skeleton are orthonormal.** This is Schur
orthogonality; only pairwise inequivalence of the family is used. -/
theorem orthonormal_peterWeylFamily [IsAlgClosed 𝕜] (h : IsIrrepSkeleton models) :
    Orthonormal 𝕜 (peterWeylFamily models) :=
  ContRepresentation.orthonormal_matrixCoeffLp (fun i ↦ (models i).rep)
    (fun i ↦ (models i).continuous_rep) (fun i ↦ (models i).isUnitary)
    (fun i ↦ (models i).isIrreducible) h.pairwise_isEmpty_equiv (fun i ↦ (models i).basis)

/-- **The normalized matrix coefficients of a skeleton are complete.** Their span is dense in
`L²(G)`, so its orthogonal complement vanishes. This is the completeness half of Peter-Weyl, in
the form `HilbertBasis.mkOfOrthogonalEqBot` consumes. -/
theorem orthogonal_span_peterWeylFamily_eq_bot (h : IsIrrepSkeleton models) :
    (Submodule.span 𝕜 (Set.range (peterWeylFamily models)))ᗮ = ⊥ := by
  set P := Submodule.span 𝕜 (Set.range (peterWeylFamily models))
  have hsub : ContinuousMap.toLp 2 (haarProb G) 𝕜 '' (modelSubmodule models : Set C(G, 𝕜)) ⊆
      (P : Set (Lp 𝕜 2 (haarProb G))) := by
    rintro - ⟨F, hF, rfl⟩
    rw [SetLike.mem_coe]
    induction hF using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, v, w, rfl⟩ := hx
        simpa [ContRepresentation.matrixCoeffLp_def] using
          matrixCoeffLp_mem_span_peterWeylFamily models i v w
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem P c hx
  refine Submodule.topologicalClosure_eq_top_iff.1
    (Submodule.dense_iff_topologicalClosure_eq_top.1 (h.dense_image_toLp_modelSubmodule.mono hsub))

end IsIrrepSkeleton

/-- **The Peter-Weyl theorem.** For a skeleton of the unitary dual of a compact group,
the normalized matrix coefficients `√(dim V_i) · (models i)_{ab}` are a Hilbert basis of `L²(G)`,
indexed by `Σ i, Fin (models i).dim × Fin (models i).dim`.

Algebraic closedness of the scalars is Schur's lemma, and enters through the orthonormality half. -/
noncomputable def peterWeylBasis [IsAlgClosed 𝕜] {models : ι → IrrepModel 𝕜 G}
    (h : IsIrrepSkeleton models) :
    HilbertBasis (Σ i, Fin (models i).dim × Fin (models i).dim) 𝕜 (Lp 𝕜 2 (haarProb G)) :=
  HilbertBasis.mkOfOrthogonalEqBot h.orthonormal_peterWeylFamily
    h.orthogonal_span_peterWeylFamily_eq_bot

/-- **The Peter-Weyl basis is the normalized matrix coefficients.** Its elements are the `L²`
classes represented by the continuous functions
`g ↦ √(dim V_i) · ⟪(models i).rep g e_a, e_b⟫`. -/
@[simp]
theorem coe_peterWeylBasis [IsAlgClosed 𝕜] {models : ι → IrrepModel 𝕜 G}
    (h : IsIrrepSkeleton models) : ⇑(peterWeylBasis h) = peterWeylFamily models :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- The Peter-Weyl Fourier coefficient of `f` at the normalized matrix coefficient indexed by
`x`, written as a Haar integral. -/
noncomputable def peterWeylCoeff (models : ι → IrrepModel 𝕜 G)
    (f : Lp 𝕜 2 (haarProb G))
    (x : Σ i, Fin (models i).dim × Fin (models i).dim) : 𝕜 :=
  ∫ g : G, (starRingEnd 𝕜)
      ((Real.sqrt (models x.1).dim : 𝕜) *
        ContRepresentation.matrixCoeff (models x.1).rep (models x.1).continuous_rep
          ((models x.1).basis x.2.1) ((models x.1).basis x.2.2) g) * f g ∂haarProb G

/-- The Peter-Weyl coefficient is the Haar integral against the conjugate of the normalized
continuous matrix coefficient. -/
theorem peterWeylCoeff_def (models : ι → IrrepModel 𝕜 G) (f : Lp 𝕜 2 (haarProb G))
    (x : Σ i, Fin (models i).dim × Fin (models i).dim) :
    peterWeylCoeff models f x =
      ∫ g : G, (starRingEnd 𝕜)
        ((Real.sqrt (models x.1).dim : 𝕜) *
          ContRepresentation.matrixCoeff (models x.1).rep (models x.1).continuous_rep
            ((models x.1).basis x.2.1) ((models x.1).basis x.2.2) g) * f g ∂haarProb G := by
  rw [peterWeylCoeff]

/-- A Peter-Weyl coefficient is the `L²` inner product against the corresponding normalized
matrix coefficient. This characterization does not require the models to form a skeleton. -/
theorem peterWeylCoeff_eq_inner (models : ι → IrrepModel 𝕜 G) (f : Lp 𝕜 2 (haarProb G))
    (x : Σ i, Fin (models i).dim × Fin (models i).dim) :
    peterWeylCoeff models f x = inner 𝕜 (peterWeylFamily models x) f := by
  rw [peterWeylCoeff_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_peterWeylFamily models x] with g hg
  rw [hg, ContRepresentation.matrixCoeff_apply, RCLike.inner_apply]
  exact mul_comm _ _

/-- The abstract coordinate in the Peter-Weyl Hilbert basis is the explicit Haar-integral
Fourier coefficient. -/
@[simp]
theorem peterWeylBasis_repr_apply [IsAlgClosed 𝕜] {models : ι → IrrepModel 𝕜 G}
    (h : IsIrrepSkeleton models) (f : Lp 𝕜 2 (haarProb G))
    (x : Σ i, Fin (models i).dim × Fin (models i).dim) :
    (peterWeylBasis h).repr f x = peterWeylCoeff models f x := by
  rw [(peterWeylBasis h).repr_apply_apply, coe_peterWeylBasis,
    ← peterWeylCoeff_eq_inner]

/-- **The Peter-Weyl expansion.** Every `L²` function is the sum of its Fourier coefficients
times the corresponding normalized matrix coefficients. -/
theorem hasSum_peterWeyl_expansion [IsAlgClosed 𝕜] {models : ι → IrrepModel 𝕜 G}
    (h : IsIrrepSkeleton models) (f : Lp 𝕜 2 (haarProb G)) :
    HasSum (fun x ↦ peterWeylCoeff models f x • peterWeylFamily models x) f := by
  simpa only [peterWeylBasis_repr_apply, coe_peterWeylBasis, Function.comp_apply] using
    (peterWeylBasis h).hasSum_repr f

/-- **Polarized Parseval for the Peter-Weyl basis.** The coordinate pairing of two `L²`
functions sums to their inner product. -/
theorem hasSum_conj_peterWeylCoeff_mul_peterWeylCoeff [IsAlgClosed 𝕜]
    {models : ι → IrrepModel 𝕜 G} (h : IsIrrepSkeleton models)
    (f g : Lp 𝕜 2 (haarProb G)) :
    HasSum (fun x ↦ (starRingEnd 𝕜) (peterWeylCoeff models f x) *
      peterWeylCoeff models g x) (inner 𝕜 f g) := by
  have hfirst (x : Σ i, Fin (models i).dim × Fin (models i).dim) :
      inner 𝕜 f (peterWeylBasis h x) =
        (starRingEnd 𝕜) (peterWeylCoeff models f x) := by
    rw [← inner_conj_symm, ← (peterWeylBasis h).repr_apply_apply,
      peterWeylBasis_repr_apply, starRingEnd_apply]
  simpa only [hfirst, ← (peterWeylBasis h).repr_apply_apply,
    peterWeylBasis_repr_apply] using (peterWeylBasis h).hasSum_inner_mul_inner f g

/-- **Polarized Parseval for the Peter-Weyl basis** (`tsum` form). -/
theorem tsum_conj_peterWeylCoeff_mul_peterWeylCoeff [IsAlgClosed 𝕜]
    {models : ι → IrrepModel 𝕜 G} (h : IsIrrepSkeleton models)
    (f g : Lp 𝕜 2 (haarProb G)) :
    ∑' x, (starRingEnd 𝕜) (peterWeylCoeff models f x) * peterWeylCoeff models g x =
      inner 𝕜 f g :=
  (hasSum_conj_peterWeylCoeff_mul_peterWeylCoeff h f g).tsum_eq

/-- The products of the conjugated Peter-Weyl coefficients of `f` with those of `g` are
summable. -/
theorem summable_conj_peterWeylCoeff_mul_peterWeylCoeff [IsAlgClosed 𝕜]
    {models : ι → IrrepModel 𝕜 G} (h : IsIrrepSkeleton models)
    (f g : Lp 𝕜 2 (haarProb G)) :
    Summable fun x ↦ (starRingEnd 𝕜) (peterWeylCoeff models f x) *
      peterWeylCoeff models g x :=
  (hasSum_conj_peterWeylCoeff_mul_peterWeylCoeff h f g).summable

/-- **Norm-square Parseval for the Peter-Weyl basis.** The squared norms of the Fourier
coefficients of `f` sum to `‖f‖²`, as a convergent series. -/
theorem hasSum_norm_sq_peterWeylCoeff [IsAlgClosed 𝕜]
    {models : ι → IrrepModel 𝕜 G} (h : IsIrrepSkeleton models)
    (f : Lp 𝕜 2 (haarProb G)) :
    HasSum (fun x ↦ ‖peterWeylCoeff models f x‖ ^ 2) (‖f‖ ^ 2) := by
  simpa only [← (peterWeylBasis h).repr_apply_apply, peterWeylBasis_repr_apply] using
    (peterWeylBasis h).hasSum_norm_sq_inner f

/-- **Norm-square Parseval for the Peter-Weyl basis** (`tsum` form). -/
theorem tsum_norm_sq_peterWeylCoeff [IsAlgClosed 𝕜]
    {models : ι → IrrepModel 𝕜 G} (h : IsIrrepSkeleton models)
    (f : Lp 𝕜 2 (haarProb G)) :
    ∑' x, ‖peterWeylCoeff models f x‖ ^ 2 = ‖f‖ ^ 2 :=
  (hasSum_norm_sq_peterWeylCoeff h f).tsum_eq

/-- The squared Peter-Weyl Fourier coefficients of an `L²` function are summable. -/
theorem summable_norm_sq_peterWeylCoeff [IsAlgClosed 𝕜]
    {models : ι → IrrepModel 𝕜 G} (h : IsIrrepSkeleton models)
    (f : Lp 𝕜 2 (haarProb G)) :
    Summable fun x ↦ ‖peterWeylCoeff models f x‖ ^ 2 :=
  (hasSum_norm_sq_peterWeylCoeff h f).summable

end Skeleton

/-! ### A skeleton exists -/

section Existence

variable (𝕜 G : Type*) [RCLike 𝕜] [Group G] [TopologicalSpace G]

/-- **Unitary equivalence of models.** Two models are equivalent when some linear isometry
equivalence of their carriers transports one representation onto the other; by
`TauCeti.ContRepresentation.congr_refl` and `TauCeti.ContRepresentation.congr_congr` this is an
equivalence relation.

Asking the carriers to be the standard spaces is what makes this a relation on a *type*, so that
one representative per class may be chosen; on "all irreducible unitary representations on all
inner product spaces" there is no such type to quotient. -/
instance IrrepModel.instSetoid : Setoid (IrrepModel 𝕜 G) where
  r m m' := ∃ e : EuclideanSpace 𝕜 (Fin m.dim) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin m'.dim),
    ContRepresentation.congr e.toContinuousLinearEquiv m.rep = m'.rep
  iseqv :=
    { refl m := by
        refine ⟨LinearIsometryEquiv.refl 𝕜 _, ?_⟩
        rw [LinearIsometryEquiv.toContinuousLinearEquiv_refl, ContRepresentation.congr_refl]
      symm := by
        rintro m m' ⟨e, he⟩
        refine ⟨e.symm, ?_⟩
        rw [LinearIsometryEquiv.toContinuousLinearEquiv_symm, ← he]
        simp
      trans := by
        rintro m m' m'' ⟨e, he⟩ ⟨f, hf⟩
        refine ⟨e.trans f, ?_⟩
        rw [LinearIsometryEquiv.toContinuousLinearEquiv_trans, ← ContRepresentation.congr_congr,
          he, hf] }

/-- **The unitary dual of `G` in its standard models**: the models of finite-dimensional
irreducible unitary continuous representations, up to unitary equivalence. This is the index of
the Peter-Weyl basis. -/
def IrrepClass : Type _ := Quotient (IrrepModel.instSetoid 𝕜 G)

variable {𝕜 G}

/-- **The model chosen in a class.** Choice enters exactly here, and only to pick a representative
of an equivalence class; everything the representative carries -- the carrier, the orthonormal
basis, the representation -- is pinned by `TauCeti.IrrepModel`. -/
noncomputable def IrrepClass.model (i : IrrepClass 𝕜 G) : IrrepModel 𝕜 G := Quotient.out i

variable (𝕜 G)

/-- **A skeleton of the unitary dual exists**: the chosen representatives of the unitary
equivalence classes form one.

Pairwise inequivalence is the substance. Distinct classes are inequivalent *unitarily* by
construction, and `TauCeti.ContRepresentation.exists_linearIsometryEquiv_congr_eq` upgrades that
to inequivalence outright, since between irreducible unitary representations every intertwining
isomorphism can be rescaled to an isometry. Exhaustion is then the tautology that every model
lies in its own class. -/
theorem isIrrepSkeleton_model [IsAlgClosed 𝕜] :
    IsIrrepSkeleton (IrrepClass.model (𝕜 := 𝕜) (G := G)) where
  pairwise_isEmpty_equiv i j hne :=
    ⟨fun φ ↦ hne <| Quotient.out_equiv_out.1 <|
      ContRepresentation.exists_linearIsometryEquiv_congr_eq (Quotient.out i).isUnitary
        (Quotient.out j).isUnitary (Quotient.out i).isIrreducible φ⟩
  exists_congr_eq n π hπ hu hirr := by
    refine ⟨Quotient.mk _ ⟨n, π, hπ, hu, hirr⟩, ?_⟩
    exact Setoid.symm (Quotient.mk_out (s := IrrepModel.instSetoid 𝕜 G) ⟨n, π, hπ, hu, hirr⟩)

end Existence

section StandardBasis

variable (𝕜 G : Type*) [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- **The Peter-Weyl theorem, unconditionally.** The normalized matrix coefficients of the models
chosen in the unitary equivalence classes are a Hilbert basis of `L²(G)`, indexed by
`Σ i, Fin (IrrepClass.model i).dim × Fin (IrrepClass.model i).dim`. No skeleton is assumed:
`isIrrepSkeleton_model` supplies one.

`TauCeti.coe_stdPeterWeylBasis` identifies the elements of this basis with
`TauCeti.peterWeylFamily IrrepClass.model`. -/
noncomputable def stdPeterWeylBasis :
    HilbertBasis (Σ i : IrrepClass 𝕜 G,
      Fin (IrrepClass.model i).dim × Fin (IrrepClass.model i).dim) 𝕜 (Lp 𝕜 2 (haarProb G)) :=
  peterWeylBasis (isIrrepSkeleton_model 𝕜 G)

/-- **The unconditional Peter-Weyl basis is the normalized matrix coefficients of the chosen
representatives.** As for `TauCeti.coe_peterWeylBasis`, its elements are the `L²` classes
represented by the functions
`g ↦ √(dim V_i) · ⟪(IrrepClass.model i).rep g e_a, e_b⟫`. -/
@[simp]
theorem coe_stdPeterWeylBasis :
    ⇑(stdPeterWeylBasis 𝕜 G) = peterWeylFamily (IrrepClass.model (𝕜 := 𝕜) (G := G)) :=
  coe_peterWeylBasis _

/-- A coordinate in the unconditional Peter-Weyl basis is its explicit Fourier coefficient. -/
@[simp]
theorem stdPeterWeylBasis_repr_apply (f : Lp 𝕜 2 (haarProb G))
    (x : Σ i : IrrepClass 𝕜 G,
      Fin (IrrepClass.model i).dim × Fin (IrrepClass.model i).dim) :
    (stdPeterWeylBasis 𝕜 G).repr f x =
      peterWeylCoeff (IrrepClass.model (𝕜 := 𝕜) (G := G)) f x := by
  simpa only [stdPeterWeylBasis] using
    peterWeylBasis_repr_apply (isIrrepSkeleton_model 𝕜 G) f x

end StandardBasis

end TauCeti
