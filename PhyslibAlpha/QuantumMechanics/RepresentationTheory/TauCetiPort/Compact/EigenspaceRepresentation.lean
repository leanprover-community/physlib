/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Compact.Convolution
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Compact.RegularRepresentation
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Continuous.Representative
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The finite-dimensional representations carried by convolution eigenspaces

A compact group `G` acts on `L²(G)` by right translation, `(π g f) x = f (x * g)`
(`TauCeti.rightRegularLp`). This action is isometric and strongly continuous, but nothing makes
`g ↦ π g` continuous for the operator norm, so `L²(G)` itself does not come with the continuity
hypothesis that Mathlib's `ContRepresentation` is usually paired with. Restricted to an
eigenspace of a convolution operator at a nonzero eigenvalue it does: that eigenspace is
finite-dimensional, right-translation invariant, and made of continuous functions, all of which
`TauCeti.RepresentationTheory.Compact.Convolution` supplies.

This file assembles those three facts into the representation itself, and reads off the
consequence the Peter-Weyl theorem needs: the continuous representative `μ⁻¹ • (k * f)` of an
eigenvector `f` is the conjugate of a **matrix coefficient** of that representation, hence a
representative function, so it lies in the representative ring `𝓡(G)`. Since the eigenspaces of a
symmetric kernel span a dense subspace of `L²(G)` and convolution is bounded from `L²(G)` into the
uniform norm, *every* function of the form `k * f` lies in the uniform closure of `𝓡(G)`.

This is where the finite-dimensional representations of a compact group come from. Nothing here
presupposes that `G` has any: the representation is manufactured out of the spectral theory of a
compact self-adjoint operator, and no point-separation property is used, so the argument does not
quietly assume the theorem it serves.

## Main definitions

* `TauCeti.convolutionEigenspaceRepresentation`: the restriction of the right regular
  representation to an eigenspace of a convolution operator.

## Main statements

* `TauCeti.convolutionCLM_rightRegularLp`: convolution intertwines right translation on `L²(G)`
  with right translation of continuous functions.
* `TauCeti.continuous_convolutionEigenspaceRepresentation`: at a nonzero eigenvalue the eigenspace
  representation is continuous, so it is a genuine finite-dimensional continuous representation
  of `G`.
* `TauCeti.exists_smul_convolutionCLM_eq_star_matrixCoeff`: the continuous representative of an
  eigenvector at a nonzero eigenvalue is the conjugate of a matrix coefficient of that
  representation, at a vector independent of the eigenvector.
* `TauCeti.isRepresentative_smul_convolutionCLM_of_mem_eigenspace`: consequently it is a
  representative function.
* `TauCeti.convolutionCLM_mem_representativeSubmodule_of_mem_iSup_eigenspace`: convolving a finite
  sum of eigenvectors gives an element of the representative ring `𝓡(G)`.
* `TauCeti.convolutionCLM_mem_closure_representativeSubmodule`: for a symmetric kernel, `k * f`
  lies in the uniform closure of `𝓡(G)` for *every* `f ∈ L²(G)`.

## Implementation notes

Continuity of `g ↦ π g` on the eigenspace is checked pointwise, which is enough because the
eigenspace is finite-dimensional (`continuous_clm_apply`); pointwise it is the strong continuity
`TauCeti.continuous_rightRegularLp_apply` of the right regular representation, so no separate
argument about continuous representatives is needed.

The matrix coefficient is produced from the linear functional `h ↦ μ⁻¹ • (k * h) 1`, evaluation of
the continuous representative at the identity. Its Riesz vector `y` satisfies
`⟪y, π g f⟫ = μ⁻¹ • (k * f) g`, and Mathlib's inner product is conjugate linear in its first
argument, so what appears directly is the *conjugate* of the matrix coefficient
`g ↦ ⟪π g f, y⟫`. The representative functions are closed under conjugation
(`TauCeti.IsRepresentative.star`), so nothing is lost.

## References

This is the `nonzero_eigenspace_finite_dim_continuous_rep` step of Layer 5 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
which asks for each nonzero eigenspace to be finite-dimensional and translation invariant, "so it
carries a continuous finite-dimensional representation whose functions lie in `𝓡(G)`". Combined
with an approximate identity it gives the uniform density of `𝓡(G)` in `C(G)`, the analytic core
of the Peter-Weyl theorem.

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC (2016), §5.2.
* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapters 3-4.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti

section CompactGroup

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-! ### Convolution against the right regular representation -/

/-- **Convolution intertwines right translation on `L²(G)` with right translation of continuous
functions.** This is `TauCeti.convolutionCLM_compMeasurePreserving_mul_right` phrased in terms of
`TauCeti.rightRegularLp`. -/
theorem convolutionCLM_rightRegularLp (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) (g : G) :
    convolutionCLM k (rightRegularLp 𝕜 G g f)
      = (convolutionCLM k f).comp (.mulRight g) := by
  rw [rightRegularLp_apply]
  exact ContinuousMap.ext fun x => convolutionCLM_compMeasurePreserving_mul_right k f g x

/-- **The eigenspaces of a convolution operator are invariant under the right regular
representation.** This is
`TauCeti.compMeasurePreserving_mul_right_mem_eigenspace_convolutionOperator` phrased in terms of
`TauCeti.rightRegularLp`. -/
theorem rightRegularLp_mem_eigenspace_convolutionOperator (k : C(G, 𝕜)) (μ : 𝕜) (g : G)
    {f : Lp 𝕜 2 (haarProb G)}
    (hf : f ∈ Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :
    rightRegularLp 𝕜 G g f ∈
      Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ := by
  rw [rightRegularLp_apply]
  exact compMeasurePreserving_mul_right_mem_eigenspace_convolutionOperator k μ g hf

/-! ### The representation on an eigenspace of a convolution operator -/

/-- **The representation of `G` on an eigenspace of a convolution operator**: the right regular
representation restricted to the eigenspace, which is right-translation invariant because
convolution commutes with right translation. -/
noncomputable def convolutionEigenspaceRepresentation (k : C(G, 𝕜)) (μ : 𝕜) :
    ContRepresentation 𝕜 G
      (Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :=
  ContRepresentation.subrepresentation (rightRegularLp 𝕜 G) _
    fun g _ hf => rightRegularLp_mem_eigenspace_convolutionOperator k μ g hf

@[simp]
theorem coe_convolutionEigenspaceRepresentation_apply (k : C(G, 𝕜)) (μ : 𝕜) (g : G)
    (f : Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :
    ((convolutionEigenspaceRepresentation k μ g f : _) : Lp 𝕜 2 (haarProb G))
      = rightRegularLp 𝕜 G g (f : Lp 𝕜 2 (haarProb G)) :=
  ContRepresentation.coe_subrepresentation_apply g f

/-- **The eigenspace representation is unitary**, being a restriction of the unitary right regular
representation. -/
theorem isUnitary_convolutionEigenspaceRepresentation (k : C(G, 𝕜)) (μ : 𝕜) :
    ContRepresentation.IsUnitary (convolutionEigenspaceRepresentation k μ) :=
  (isUnitary_rightRegularLp 𝕜 G).subrepresentation _

/-- **The eigenspace representation at a nonzero eigenvalue is continuous.** The eigenspace is
finite-dimensional, so continuity for the operator norm may be checked one vector at a time; on a
vector it is the strong continuity of the right regular representation.

Together with `TauCeti.finiteDimensional_eigenspace_convolutionOperator` this is the statement
that a nonzero eigenspace of a convolution operator carries a finite-dimensional continuous
representation of `G`. -/
theorem continuous_convolutionEigenspaceRepresentation (k : C(G, 𝕜)) {μ : 𝕜} (hμ : μ ≠ 0) :
    Continuous (convolutionEigenspaceRepresentation k μ) := by
  have := finiteDimensional_eigenspace_convolutionOperator k hμ
  rw [continuous_clm_apply]
  intro f
  rw [Topology.IsInducing.subtypeVal.continuous_iff]
  simpa only [Function.comp_def, coe_convolutionEigenspaceRepresentation_apply] using
    continuous_rightRegularLp_apply (f : Lp 𝕜 2 (haarProb G))

/-! ### The eigenvectors are representative functions -/

/-- **The continuous representative of an eigenvector is a matrix coefficient of the eigenspace
representation.** For a nonzero eigenvalue `μ`, one vector `y` of the eigenspace serves for every
eigenvector at once: it is the Riesz vector of the functional "evaluate the continuous
representative at the identity", and `μ⁻¹ • (k * f)` is the conjugate of the matrix coefficient at
`(f, y)`.

Naming the representation, rather than only the conclusion that the function is representative,
is what records that the finite-dimensional representations produced by the density argument are
*unitary* (`TauCeti.isUnitary_convolutionEigenspaceRepresentation`), so that a statement proved
for unitary representations can be fed back into it. -/
theorem exists_smul_convolutionCLM_eq_star_matrixCoeff (k : C(G, 𝕜)) {μ : 𝕜} (hμ : μ ≠ 0) :
    ∃ y : Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ,
      ∀ f (hf : f ∈ Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ),
        μ⁻¹ • convolutionCLM k f
          = star (ContRepresentation.matrixCoeff (convolutionEigenspaceRepresentation k μ)
              (continuous_convolutionEigenspaceRepresentation k hμ) ⟨f, hf⟩ y) := by
  have := finiteDimensional_eigenspace_convolutionOperator k hμ
  have hπ := continuous_convolutionEigenspaceRepresentation k hμ
  obtain ⟨y, hy⟩ :
      ∃ y : Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ,
        ∀ h : Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ,
          ⟪y, h⟫_𝕜 = μ⁻¹ * convolutionCLM k (h : Lp 𝕜 2 (haarProb G)) 1 := by
    refine ⟨(InnerProductSpace.toDual 𝕜 _).symm
      (μ⁻¹ • ((ContinuousMap.evalCLM (R := 𝕜) (M := 𝕜) (1 : G)).comp
        ((convolutionCLM k).comp
          (Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ).subtypeL))),
      fun h => ?_⟩
    rw [InnerProductSpace.toDual_symm_apply]
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      Submodule.coe_subtypeL, Submodule.subtype_apply, ContinuousMap.evalCLM_apply, smul_eq_mul]
  refine ⟨y, fun f hf => ?_⟩
  ext g
  have hg : ⟪y, convolutionEigenspaceRepresentation k μ g ⟨f, hf⟩⟫_𝕜
      = μ⁻¹ * convolutionCLM k f g := by
    rw [hy, coe_convolutionEigenspaceRepresentation_apply, convolutionCLM_rightRegularLp]
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulRight, one_mul]
  rw [ContinuousMap.star_apply, ContinuousMap.smul_apply, smul_eq_mul,
    ContRepresentation.matrixCoeff_apply, RCLike.star_def, inner_conj_symm, hg]

/-- **The continuous representative of an eigenvector is a representative function.** For a nonzero
eigenvalue `μ`, the continuous function `μ⁻¹ • (k * f)` representing an eigenvector `f` is the
conjugate of a matrix coefficient of `TauCeti.convolutionEigenspaceRepresentation`. At `μ = 0` the
function is `0`, which is representative for trivial reasons.

This is the point of the whole construction: at a nonzero eigenvalue the continuous representative
of an eigenvector is not merely continuous, it is a matrix coefficient of a finite-dimensional
continuous representation. At `μ = 0` the statement carries no information about `f` beyond
`TauCeti.convolutionCLM_eq_zero_of_mem_eigenspace_zero`, which is what makes it `0`. -/
theorem isRepresentative_smul_convolutionCLM_of_mem_eigenspace (k : C(G, 𝕜)) {μ : 𝕜}
    {f : Lp 𝕜 2 (haarProb G)}
    (hf : f ∈ Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :
    IsRepresentative (μ⁻¹ • convolutionCLM k f) := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · rw [inv_zero, zero_smul]
    exact isRepresentative_zero 𝕜 G
  have := finiteDimensional_eigenspace_convolutionOperator k hμ
  obtain ⟨y, hy⟩ := exists_smul_convolutionCLM_eq_star_matrixCoeff k hμ
  rw [hy f hf]
  exact (isRepresentative_matrixCoeff _ _ _ _).star

/-- **Convolving a finite sum of eigenvectors lies in the representative ring `𝓡(G)`.** Each
nonzero eigenvalue contributes a matrix coefficient, and the zero eigenspace contributes
nothing. -/
theorem convolutionCLM_mem_representativeSubmodule_of_mem_iSup_eigenspace (k : C(G, 𝕜))
    {f : Lp 𝕜 2 (haarProb G)}
    (hf : f ∈ ⨆ μ : 𝕜, Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :
    convolutionCLM k f ∈ representativeSubmodule 𝕜 G := by
  refine Submodule.iSup_induction (motive := fun x => convolutionCLM k x ∈
    representativeSubmodule 𝕜 G) _ hf (fun μ x hx => ?_) (by rw [map_zero]; exact zero_mem _)
    fun x y hx hy => ?_
  · rcases eq_or_ne μ 0 with rfl | hμ
    · rw [convolutionCLM_eq_zero_of_mem_eigenspace_zero k hx]
      exact zero_mem _
    · have hsmul : convolutionCLM k x = μ • (μ⁻¹ • convolutionCLM k x) := by
        rw [smul_smul, mul_inv_cancel₀ hμ, one_smul]
      rw [hsmul]
      exact Submodule.smul_mem _ _ (mem_representativeSubmodule_of_isRepresentative
        (isRepresentative_smul_convolutionCLM_of_mem_eigenspace k hx))
  · rw [map_add]
    exact add_mem hx hy

/-- **Every convolution by a symmetric kernel lies in the uniform closure of the representative
ring.** The eigenspaces of a symmetric convolution operator span a dense subspace of `L²(G)`, each
of them convolves into `𝓡(G)`, and convolution is continuous from `L²(G)` into the uniform norm of
`C(G)`.

With an approximate identity, which lets a continuous function be uniformly approximated by such
convolutions, this gives the uniform density of `𝓡(G)` in `C(G)`, the analytic core of the
Peter-Weyl theorem. -/
theorem convolutionCLM_mem_closure_representativeSubmodule (k : C(G, 𝕜))
    (hk : ∀ g : G, k g⁻¹ = (starRingEnd 𝕜) (k g)) (f : Lp 𝕜 2 (haarProb G)) :
    convolutionCLM k f ∈ closure (representativeSubmodule 𝕜 G : Set C(G, 𝕜)) := by
  set S := ⨆ μ : 𝕜, Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ
  have htop : S.topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.2
      (orthogonalComplement_iSup_eigenspaces_convolutionOperator_eq_bot k hk)
  have hf : f ∈ closure (S : Set (Lp 𝕜 2 (haarProb G))) := by
    rw [← Submodule.topologicalClosure_coe, htop]
    exact Submodule.mem_top
  refine closure_mono ?_
    (image_closure_subset_closure_image (convolutionCLM (G := G) k).continuous ⟨f, hf, rfl⟩)
  rintro - ⟨h, hh, rfl⟩
  exact convolutionCLM_mem_representativeSubmodule_of_mem_iSup_eigenspace k hh

end CompactGroup

end TauCeti
