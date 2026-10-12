/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Reproducing
import Mathlib.Analysis.Normed.Operator.Extend
import PhyslibAlpha.Mathematics.TauCeti.Analysis.InnerProductSpace.LinearCombination

/-!
# Kolmogorov decomposition of a positive-definite kernel

This file constructs the canonical Hilbert-space realization of a scalar-valued positive-definite
kernel.

## i. Overview

This file constructs the canonical Hilbert-space realization of a scalar-valued
positive-definite kernel.  A kernel `K : α → α → 𝕜` is first regarded as the operator-valued
kernel whose `(a, b)` entry is multiplication by `K a b` on the one-dimensional Hilbert space
`𝕜`.  Mathlib's `RKHS.OfKernel` construction then gives a Hilbert space and kernel vectors
`Φ a` satisfying

`⟪Φ a, Φ b⟫_𝕜 = K a b`.

The span of the kernel vectors is dense, so this is the minimal Kolmogorov decomposition rather
than an arbitrary realization.  Its universal property gives a unique linear isometry into any
other realization, and a linear isometric equivalence when that realization is also minimal.

The completion and reproducing-kernel construction are Mathlib's `RKHS.OfKernel`; this file
supplies the scalar-kernel bridge and its characteristic API.

## ii. Key results

* `TauCeti.positiveDefiniteKernelOperator`: regard a scalar kernel as an operator-valued kernel.
* `TauCeti.posSemidef_positiveDefiniteKernelOperator`: positivity of that
  operator kernel.
* `Matrix.PosSemidef.KolmogorovSpace`: the canonical Hilbert space.
* `Matrix.PosSemidef.kolmogorovFeature`: its canonical feature map.
* `Matrix.PosSemidef.inner_kolmogorovFeature`: the Kolmogorov identity.
* `Matrix.PosSemidef.kolmogorovFeature_dense`: minimality of the decomposition.
* `Matrix.PosSemidef.kolmogorovIsometry`: the universal comparison isometry.
* `Matrix.PosSemidef.kolmogorovEquiv`: equivalence with any other minimal
  realization.

## iii. Table of contents

- A. Development

## iv. References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups*,
  Springer GTM 100 (1984), Chapter 3.
-/

public section

/-! ## A. Development -/

open ComplexConjugate ContinuousLinearMap InnerProductSpace
open scoped ComplexOrder

namespace TauCeti

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {α : Type v}

/-- A scalar kernel regarded as an operator-valued kernel on the one-dimensional Hilbert space
`𝕜`: the entry at `(a, b)` is left multiplication by `K a b`. -/
noncomputable def positiveDefiniteKernelOperator (K : α → α → 𝕜) :
    Matrix α α (𝕜 →L[𝕜] 𝕜) :=
  Matrix.of fun a b => ContinuousLinearMap.mul 𝕜 𝕜 (K a b)

@[simp]
lemma positiveDefiniteKernelOperator_apply (K : α → α → 𝕜) (a b : α) (z : 𝕜) :
    positiveDefiniteKernelOperator K a b z = K a b * z := by
  rfl

variable {𝕜 : Type u} [RCLike 𝕜]
variable {α : Type v}
variable {K : α → α → 𝕜}

/-- The operator-valued kernel obtained from a scalar positive-definite kernel is positive
semidefinite.  This is the bridge needed by Mathlib's `RKHS.OfKernel` construction. -/
lemma posSemidef_positiveDefiniteKernelOperator (hK : Matrix.PosSemidef K) :
    (positiveDefiniteKernelOperator K).PosSemidef := by
  have hsymm (a b : α) : conj (K a b) = K b a := by
    simpa only [starRingEnd_apply] using hK.isHermitian.apply b a
  apply (RKHS.posSemidef_tfae (K := positiveDefiniteKernelOperator K)).out 3 1 |>.mp
  refine ⟨?_, ?_⟩
  · apply Matrix.ext
    intro a b
    rw [Matrix.conjTranspose_apply]
    symm
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
    intro x y
    rw [positiveDefiniteKernelOperator_apply, positiveDefiniteKernelOperator_apply]
    rw [RCLike.inner_apply', RCLike.inner_apply', map_mul, hsymm]
    ring
  · intro f
    have hnonneg := hK.2 f
    have hre := (RCLike.nonneg_iff.mp hnonneg).1
    have hinner (a b : α) (x y : 𝕜) :
        ⟪positiveDefiniteKernelOperator K b a x, y⟫_𝕜 = star x * K a b * y := by
      rw [positiveDefiniteKernelOperator_apply, RCLike.inner_apply', map_mul,
        hsymm, RCLike.star_def]
      ring
    have hquadratic :
        RCLike.re (f.sum fun a x => f.sum fun b y =>
          ⟪positiveDefiniteKernelOperator K b a x, y⟫_𝕜) =
          RCLike.re (f.sum fun a x => f.sum fun b y => star x * K a b * y) := by
      simp only [hinner]
    rw [hquadratic]
    simpa only [Matrix.of_apply] using hre

end TauCeti

namespace Matrix.PosSemidef

open TauCeti

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {α : Type v}
variable {K : α → α → 𝕜}

/-- The canonical Hilbert space in the Kolmogorov decomposition of `K`.

This is an abbreviation because Mathlib's `RKHS.OfKernel` currently has to be an abbreviation in
order for its normed-group and inner-product instances to reduce. -/
noncomputable abbrev KolmogorovSpace (hK : Matrix.PosSemidef K) :=
  letI : Fact (positiveDefiniteKernelOperator K).PosSemidef :=
    ⟨posSemidef_positiveDefiniteKernelOperator hK⟩
  RKHS.OfKernel (positiveDefiniteKernelOperator K)

/-- The canonical feature map into the Kolmogorov space.  It sends `a` to the reproducing-kernel
vector at `a`, evaluated on the scalar `1`. -/
noncomputable def kolmogorovFeature (hK : Matrix.PosSemidef K) (a : α) :
    KolmogorovSpace hK := by
  letI : Fact (positiveDefiniteKernelOperator K).PosSemidef :=
    ⟨posSemidef_positiveDefiniteKernelOperator hK⟩
  exact RKHS.kerFun (KolmogorovSpace hK) a 1

/-- **Kolmogorov identity.** Inner products of the canonical feature vectors recover the
original kernel. -/
@[simp]
lemma inner_kolmogorovFeature (hK : Matrix.PosSemidef K) (a b : α) :
    ⟪kolmogorovFeature hK a, kolmogorovFeature hK b⟫_𝕜 = K a b := by
  have hsymm (x y : α) : conj (K x y) = K y x := by
    simpa only [starRingEnd_apply] using hK.isHermitian.apply y x
  let : Fact (positiveDefiniteKernelOperator K).PosSemidef :=
    ⟨posSemidef_positiveDefiniteKernelOperator hK⟩
  rw [kolmogorovFeature, kolmogorovFeature,
    ← RKHS.kernel_inner (KolmogorovSpace hK) b a (1 : 𝕜) 1,
    RKHS.OfKernel.kernel_ofKernel]
  simp [hsymm]

/-- The squared norm of a canonical feature vector is the real part of the corresponding
diagonal kernel value. -/
@[simp]
lemma norm_kolmogorovFeature_sq (hK : Matrix.PosSemidef K) (a : α) :
    ‖kolmogorovFeature hK a‖ ^ 2 = RCLike.re (K a a) := by
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), inner_kolmogorovFeature hK]

/-- The squared distance between two canonical feature vectors, expressed entirely in terms of
the original kernel. -/
@[simp]
lemma norm_kolmogorovFeature_sub_sq (hK : Matrix.PosSemidef K) (a b : α) :
    ‖kolmogorovFeature hK a - kolmogorovFeature hK b‖ ^ 2 =
      RCLike.re (K a a) - 2 * RCLike.re (K a b) + RCLike.re (K b b) := by
  rw [norm_sub_sq (𝕜 := 𝕜), norm_kolmogorovFeature_sq hK, norm_kolmogorovFeature_sq hK,
    inner_kolmogorovFeature hK]

/-- The canonical feature vectors have dense linear span in the Kolmogorov space.  Thus the
construction is minimal: it contains no orthogonal summand invisible to the kernel. -/
lemma kolmogorovFeature_dense (hK : Matrix.PosSemidef K) :
    (Submodule.span 𝕜 (Set.range (kolmogorovFeature hK))).topologicalClosure = ⊤ := by
  let : Fact (positiveDefiniteKernelOperator K).PosSemidef :=
    ⟨posSemidef_positiveDefiniteKernelOperator hK⟩
  have hspan :
      Submodule.span 𝕜
          {y | ∃ (a : α) (z : 𝕜), RKHS.kerFun (KolmogorovSpace hK) a z = y} =
        Submodule.span 𝕜 (Set.range (kolmogorovFeature hK)) := by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro y ⟨a, z, rfl⟩
      have hfeature :
          RKHS.kerFun (KolmogorovSpace hK) a z =
            z • RKHS.kerFun (KolmogorovSpace hK) a 1 := by
        rw [← map_smul]
        simp
      rw [hfeature]
      exact (Submodule.span 𝕜 (Set.range (kolmogorovFeature hK))).smul_mem z
        (Submodule.subset_span ⟨a, by rw [kolmogorovFeature]⟩)
    · refine Submodule.span_le.2 ?_
      rintro y ⟨a, rfl⟩
      exact Submodule.subset_span ⟨a, 1, by rw [kolmogorovFeature]⟩
  have hdense := RKHS.kerFun_dense (H := KolmogorovSpace hK)
  rw [hspan] at hdense
  exact hdense

private lemma denseRange_featureCombination (hK : Matrix.PosSemidef K) :
    DenseRange (Finsupp.linearCombination 𝕜 (kolmogorovFeature hK)) := by
  have hdense : Dense ((Finsupp.linearCombination 𝕜 (kolmogorovFeature hK)).range :
      Set (KolmogorovSpace hK)) := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.2
    rw [Finsupp.range_linearCombination]
    exact kolmogorovFeature_dense hK
  exact hdense

/-- The unique linear isometry from the canonical Kolmogorov space into any Hilbert-space
realization of `K`.  It sends each canonical feature vector to the corresponding vector in the
given realization. -/
noncomputable def kolmogorovIsometry {E : Type w} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (hK : Matrix.PosSemidef K) (φ : α → E)
    (hφ : ∀ a b, ⟪φ a, φ b⟫_𝕜 = K a b) : KolmogorovSpace hK →ₗᵢ[𝕜] E := by
  let canonical := Finsupp.linearCombination 𝕜 (kolmogorovFeature hK)
  let target := Finsupp.linearCombination 𝕜 φ
  have hdense : DenseRange canonical := denseRange_featureCombination hK
  have hnorm : ∀ f, ‖target f‖ = ‖canonical f‖ := fun f =>
    f.norm_linearCombination_eq_of_inner_eq fun a b =>
      (hφ a b).trans (inner_kolmogorovFeature hK a b).symm
  have hbound : ∃ C, ∀ f, ‖target f‖ ≤ C * ‖canonical f‖ :=
    ⟨1, fun f => by simp [hnorm f]⟩
  exact LinearIsometry.mk (target.extendOfNorm canonical).toLinearMap fun x => by
    refine hdense.induction_on x (isClosed_eq (target.extendOfNorm canonical).continuous.norm
      continuous_norm) ?_
    intro f
    exact calc
      ‖target.extendOfNorm canonical (canonical f)‖ = ‖target f‖ :=
        congrArg norm (LinearMap.extendOfNorm_eq hdense hbound f)
      _ = ‖canonical f‖ := hnorm f

/-- The universal comparison isometry sends canonical feature vectors to the vectors of the
given realization. -/
@[simp]
lemma kolmogorovIsometry_apply {E : Type w} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (hK : Matrix.PosSemidef K) (φ : α → E)
    (hφ : ∀ a b, ⟪φ a, φ b⟫_𝕜 = K a b) (a : α) :
    kolmogorovIsometry hK φ hφ (kolmogorovFeature hK a) = φ a := by
  rw [kolmogorovIsometry]
  have happ := LinearMap.extendOfNorm_eq
    (f := Finsupp.linearCombination 𝕜 φ)
    (e := Finsupp.linearCombination 𝕜 (kolmogorovFeature hK))
    (denseRange_featureCombination hK)
    ⟨1, fun f => by
      simpa only [one_mul] using (f.norm_linearCombination_eq_of_inner_eq
        fun a b => (hφ a b).trans (inner_kolmogorovFeature hK a b).symm).le⟩
    (Finsupp.single a 1)
  simpa only [LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe,
    Finsupp.linearCombination_single, one_smul] using happ

/-- A linear isometry out of the canonical Kolmogorov space is uniquely determined by its values
on the canonical feature vectors. -/
lemma kolmogorovIsometry_unique {E : Type w} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (hK : Matrix.PosSemidef K) (φ : α → E)
    (hφ : ∀ a b, ⟪φ a, φ b⟫_𝕜 = K a b) (T : KolmogorovSpace hK →ₗᵢ[𝕜] E)
    (hT : ∀ a, T (kolmogorovFeature hK a) = φ a) : T = kolmogorovIsometry hK φ hφ := by
  have hdense : Dense (Submodule.span 𝕜 (Set.range (kolmogorovFeature hK)) :
      Set (KolmogorovSpace hK)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2 (kolmogorovFeature_dense hK)
  refine LinearIsometry.toContinuousLinearMap_injective (ContinuousLinearMap.ext_on hdense ?_)
  rintro _ ⟨a, rfl⟩
  simp [hT a]

/-- If the vectors in a realization of `K` have dense linear span, the universal comparison
isometry is surjective. -/
lemma kolmogorovIsometry_surjective {E : Type w} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (hK : Matrix.PosSemidef K) (φ : α → E)
    (hφ : ∀ a b, ⟪φ a, φ b⟫_𝕜 = K a b)
    (hφdense : (Submodule.span 𝕜 (Set.range φ)).topologicalClosure = ⊤) :
    Function.Surjective (kolmogorovIsometry hK φ hφ) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hφdense]
  apply Submodule.topologicalClosure_minimal
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨kolmogorovFeature hK a, kolmogorovIsometry_apply hK φ hφ a⟩
  · exact (kolmogorovIsometry hK φ hφ).isometry.isClosedEmbedding.isClosed_range

/-- The canonical Kolmogorov space is linearly isometric to every other minimal realization of
the same kernel. -/
noncomputable def kolmogorovEquiv {E : Type w} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (hK : Matrix.PosSemidef K) (φ : α → E)
    (hφ : ∀ a b, ⟪φ a, φ b⟫_𝕜 = K a b)
    (hφdense : (Submodule.span 𝕜 (Set.range φ)).topologicalClosure = ⊤) :
    KolmogorovSpace hK ≃ₗᵢ[𝕜] E :=
  LinearIsometryEquiv.ofSurjective (kolmogorovIsometry hK φ hφ)
    (kolmogorovIsometry_surjective hK φ hφ hφdense)

/-- The equivalence with another minimal realization sends canonical feature vectors to the
vectors of that realization. -/
@[simp]
lemma kolmogorovEquiv_apply {E : Type w} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (hK : Matrix.PosSemidef K) (φ : α → E)
    (hφ : ∀ a b, ⟪φ a, φ b⟫_𝕜 = K a b)
    (hφdense : (Submodule.span 𝕜 (Set.range φ)).topologicalClosure = ⊤) (a : α) :
    kolmogorovEquiv hK φ hφ hφdense (kolmogorovFeature hK a) = φ a := by
  rw [kolmogorovEquiv, LinearIsometryEquiv.coe_ofSurjective]
  exact kolmogorovIsometry_apply hK φ hφ a

end Matrix.PosSemidef

end
