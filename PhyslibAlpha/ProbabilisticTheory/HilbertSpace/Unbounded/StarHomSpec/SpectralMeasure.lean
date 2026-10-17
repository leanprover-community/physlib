/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.StarHomSpec.SesquilinearForm
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.UnitaryInfra.SpectralMeasure
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Algebra.Star.Unitary

/-!

# The spectral measure of a representation of continuous functions

The projection-valued measure of a unital ⋆-homomorphism from the continuous functions on a compact
Hausdorff space to the bounded operators of a Hilbert space.

## i. Overview

The sesquilinear form of the indicator of a Borel set `S` is represented by an operator `E(S)`.
These operators are projections, countably additive in the weak operator topology, and commute with
every operator commuting with the range of the ⋆-homomorphism. They form the spectral measure of the
⋆-homomorphism, whose integral of a continuous function `f` is `Φ f`. This is the construction of
`UnitaryInfra.SpectralMeasure` with the continuous functional calculus of a normal operator
replaced by an arbitrary ⋆-homomorphism, so that it applies to commuting families.

## ii. Key results

- `starHomSpectralOperator` : the operator `E(S)`.
- `starHomSpectralOperator_isStarProjection` : each `E(S)` is an orthogonal projection.
- `starHomSpectralMeasure` : the spectral measure of a ⋆-homomorphism.
- `starHomSpectralMeasure_reconstruction` : integrating a real continuous `f` gives `Φ f`.
- `starHomSpectralMeasure_commute` : `E` commutes with operators commuting with the range of `Φ`.

## iii. Table of contents

- A. Order properties of the spectral operators
- B. Weak countable additivity
- C. The spectral operators are projections
- D. The spectral measure
- E. Commutation with the commutant

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open MeasureTheory Set Topology
open scoped ComplexOrder CStarAlgebra InnerProductSpace

namespace QuantumMechanics

section StarHomScalar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [CompactSpace X] (Φ : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- The Riesz-represented operator at the measurable set `S`. -/
noncomputable def starHomSpectralOperatorAux (S : Set (X)) (hS : MeasurableSet S) :
    H →L[ℂ] H :=
  InnerProductSpace.continuousLinearMapOfBilin (starHomSesquilinearForm Φ S hS)

lemma starHomSpectralOperatorAux_inner (S : Set (X)) (hS : MeasurableSet S) (x y : H) :
    ⟪y, starHomSpectralOperatorAux Φ S hS x⟫_ℂ =
      polarizedStarHomScalarMeasure Φ x y S := by
  have h := InnerProductSpace.continuousLinearMapOfBilin_apply (starHomSesquilinearForm Φ S hS) x y
  rw [starHomSesquilinearForm_apply] at h
  change ⟪starHomSpectralOperatorAux Φ S hS x, y⟫_ℂ = _ at h
  rw [← inner_conj_symm, h, Complex.conj_conj]

open scoped Classical in
/-- The Riesz-represented operator on every set, `0` off the measurable sets so that this
directly matches `MeasureTheory.VectorMeasure`'s `not_measurable'` convention. -/
noncomputable def starHomSpectralOperator (S : Set (X)) : H →L[ℂ] H :=
  if hS : MeasurableSet S then starHomSpectralOperatorAux Φ S hS else 0

lemma starHomSpectralOperator_inner (S : Set (X)) (x y : H) :
    ⟪y, starHomSpectralOperator Φ S x⟫_ℂ = polarizedStarHomScalarMeasure Φ x y S := by
  unfold starHomSpectralOperator
  split_ifs with hS
  · exact starHomSpectralOperatorAux_inner Φ S hS x y
  · simp [(polarizedStarHomScalarMeasure Φ x y).not_measurable hS]

lemma starHomSpectralOperator_apply_eq_zero_of_not_measurableSet {S : Set (X)}
    (hS : ¬MeasurableSet S) : starHomSpectralOperator Φ S = 0 := by
  unfold starHomSpectralOperator
  rw [dite_eq_right hS]

/-- The `Complex.I`-inversion companion of `starHomScalarMeasure_real_I_smul`: rewrites a Riesz
measure at `v` as the Riesz measure at `(-I) • v`.  This is the algebraic engine behind
Hermitian symmetry of the polarized measure below. -/
lemma starHomScalarMeasure_real_eq_negI_smul (v : H) (S : Set (X)) :
    (starHomScalarMeasure Φ v).real S = (starHomScalarMeasure Φ ((-Complex.I) • v)).real S := by
  have hv : Complex.I • ((-Complex.I) • v) = v := by
    rw [smul_smul, show Complex.I * (-Complex.I) = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg],
      one_smul]
  conv_lhs => rw [← hv]
  exact starHomScalarMeasure_real_I_smul Φ ((-Complex.I) • v) S

/-- Hermitian symmetry of the polarized measure: `B(y,x,S) = conj (B(x,y,S))`, matching the
convention that `B` is exactly `⟪y, starHomRealOperator Φ f x⟫` in the limit and inner products
are conjugate-symmetric.  This is the input `starHomSpectralOperator_isSelfAdjoint` needs. -/
lemma polarizedStarHomScalarMeasure_conj_symm (x y : H) (S : Set (X)) :
    polarizedStarHomScalarMeasure Φ y x S =
      starRingEnd ℂ (polarizedStarHomScalarMeasure Φ x y S) := by
  by_cases hS : MeasurableSet S
  · rw [polarizedStarHomScalarMeasure_apply Φ hS, polarizedStarHomScalarMeasure_apply Φ hS]
    have hcomm : (starHomScalarMeasure Φ (y + x)).real S =
        (starHomScalarMeasure Φ (x + y)).real S := by rw [add_comm y x]
    have hnegcomm : (starHomScalarMeasure Φ (y - x)).real S =
        (starHomScalarMeasure Φ (x - y)).real S := by
      rw [show y - x = -(x - y) by abel, starHomScalarMeasure_real_neg]
    have hnegI : (-Complex.I) • (Complex.I • x) = x := by
      rw [smul_smul, show (-Complex.I) * Complex.I = 1 by
        rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul]
    have hA : (starHomScalarMeasure Φ (y + Complex.I • x)).real S =
        (starHomScalarMeasure Φ (x - Complex.I • y)).real S := by
      have heq : (-Complex.I) • (y + Complex.I • x) = x - Complex.I • y := by
        rw [smul_add, hnegI]; module
      rw [starHomScalarMeasure_real_eq_negI_smul Φ (y + Complex.I • x) S, heq]
    have hB : (starHomScalarMeasure Φ (y - Complex.I • x)).real S =
        (starHomScalarMeasure Φ (x + Complex.I • y)).real S := by
      have heq : (-Complex.I) • (y - Complex.I • x) = -(x + Complex.I • y) := by
        rw [smul_sub, hnegI]; module
      rw [starHomScalarMeasure_real_eq_negI_smul Φ (y - Complex.I • x) S, heq,
        starHomScalarMeasure_real_neg]
    rw [hcomm, hnegcomm, hA, hB]
    simp only [map_add, map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I]
    ring
  · simp [(polarizedStarHomScalarMeasure Φ y x).not_measurable hS,
      (polarizedStarHomScalarMeasure Φ x y).not_measurable hS]

/-- `starHomSpectralOperator Φ S` is self-adjoint, for every `S` (measurable or not — the
non-measurable case is trivial since the operator is `0`).  This follows from
`polarizedStarHomScalarMeasure_conj_symm` via `LinearMap.IsSymmetric`. -/
lemma starHomSpectralOperator_isSelfAdjoint (S : Set (X)) :
    IsSelfAdjoint (starHomSpectralOperator Φ S) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  show ⟪starHomSpectralOperator Φ S x, y⟫_ℂ = ⟪x, starHomSpectralOperator Φ S y⟫_ℂ
  rw [← inner_conj_symm (starHomSpectralOperator Φ S x) y, starHomSpectralOperator_inner,
    starHomSpectralOperator_inner Φ S y x, polarizedStarHomScalarMeasure_conj_symm,
      Complex.conj_conj]

/-- The polarized measure of the whole spectrum is `⟪y, x⟫`. -/
lemma polarizedStarHomScalarMeasure_univ (x y : H) :
    polarizedStarHomScalarMeasure Φ x y Set.univ = ⟪y, x⟫_ℂ := by
  have hsq : ∀ v : H, ⟪v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hpol := inner_map_polarization_continuous (1 : H →L[ℂ] H) x y
  simp only [one_apply_eq_self, hsq] at hpol
  rw [polarizedStarHomScalarMeasure_apply Φ MeasurableSet.univ]
  simp only [starHomScalarMeasure_real_univ]
  rw [hpol]
  push_cast
  ring

lemma starHomSpectralOperator_univ_apply (x : H) :
    starHomSpectralOperator Φ Set.univ x = x := by
  apply ext_inner_left ℂ
  intro v
  rw [starHomSpectralOperator_inner]
  exact polarizedStarHomScalarMeasure_univ Φ x v

lemma starHomSpectralOperator_univ : starHomSpectralOperator Φ Set.univ = 1 := by
  ext x
  rw [starHomSpectralOperator_univ_apply Φ x, one_apply_eq_self]

/-- On the diagonal, `⟪x, E(S) x⟫` is the diagonal measure of `S`. -/
lemma starHomSpectralOperator_inner_self {S : Set (X)} (hS : MeasurableSet S) (x : H) :
    ⟪x, starHomSpectralOperator Φ S x⟫_ℂ = ((starHomScalarMeasure Φ x).real S : ℂ) := by
  rw [starHomSpectralOperator_inner, polarizedStarHomScalarMeasure_apply Φ hS]
  have hzero : (starHomScalarMeasure Φ (0 : H)).real S = 0 := by
    have h := starHomScalarMeasure_real_parallelogram Φ (0 : H) 0 S
    simp only [add_zero, sub_self] at h
    linarith
  have hxx : x - x = (0 : H) := sub_self x
  have hdouble :
      (starHomScalarMeasure Φ (x + x)).real S = 4 * (starHomScalarMeasure Φ x).real S := by
    have h := starHomScalarMeasure_real_parallelogram Φ x x S
    rw [hxx, hzero] at h
    linarith
  have hIeq : Complex.I • (x - Complex.I • x) = x + Complex.I • x := by
    rw [smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul, sub_neg_eq_add, add_comm]
  have himag : (starHomScalarMeasure Φ (x + Complex.I • x)).real S =
      (starHomScalarMeasure Φ (x - Complex.I • x)).real S := by
    have h := starHomScalarMeasure_real_I_smul Φ (x - Complex.I • x) S
    rwa [hIeq] at h
  rw [hxx, hzero, hdouble, himag, sub_self]
  push_cast
  ring

/-- `reApplyInnerSelf` version of `starHomSpectralOperator_inner_self`, in the exact shape
`ContinuousLinearMap.IsPositive` consumes. -/
lemma starHomSpectralOperator_reApplyInnerSelf {S : Set (X)} (hS : MeasurableSet S)
    (x : H) :
    (starHomSpectralOperator Φ S).reApplyInnerSelf x = (starHomScalarMeasure Φ x).real S := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, ← RCLike.conj_re, inner_conj_symm,
    starHomSpectralOperator_inner_self Φ hS x]
  simp

/-! ## A. Order properties of the spectral operators -/

/-- `starHomSpectralOperator Φ S` is a positive operator, for measurable `S`. -/
lemma starHomSpectralOperator_isPositive {S : Set (X)} (hS : MeasurableSet S) :
    ContinuousLinearMap.IsPositive (starHomSpectralOperator Φ S) := by
  rw [ContinuousLinearMap.isPositive_def']
  refine ⟨starHomSpectralOperator_isSelfAdjoint Φ S, fun x => ?_⟩
  rw [starHomSpectralOperator_reApplyInnerSelf Φ hS x]
  exact starHomScalarMeasure_real_nonneg Φ x S

lemma starHomSpectralOperator_nonneg {S : Set (X)} (hS : MeasurableSet S) :
    0 ≤ starHomSpectralOperator Φ S :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr (starHomSpectralOperator_isPositive Φ hS)

/-- `starHomSpectralOperator Φ S` is monotone in `S`, for measurable sets, in the Loewner order on
`H →L[ℂ] H`. -/
lemma starHomSpectralOperator_mono {S T : Set (X)} (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hST : S ⊆ T) :
    starHomSpectralOperator Φ S ≤ starHomSpectralOperator Φ T := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_def']
  refine ⟨(starHomSpectralOperator_isSelfAdjoint Φ T).sub
    (starHomSpectralOperator_isSelfAdjoint Φ S), fun x => ?_⟩
  show 0 ≤ (starHomSpectralOperator Φ T - starHomSpectralOperator Φ S).reApplyInnerSelf x
  have hTx := starHomSpectralOperator_reApplyInnerSelf Φ hT x
  have hSx := starHomSpectralOperator_reApplyInnerSelf Φ hS x
  have hre : (starHomSpectralOperator Φ T - starHomSpectralOperator Φ S).reApplyInnerSelf x =
      (starHomSpectralOperator Φ T).reApplyInnerSelf x -
        (starHomSpectralOperator Φ S).reApplyInnerSelf x := by
    simp only [ContinuousLinearMap.reApplyInnerSelf_apply, sub_apply,
      inner_sub_left]
    rfl
  rw [hre, hTx, hSx, sub_nonneg]
  exact MeasureTheory.measureReal_mono hST

lemma starHomSpectralOperator_le_one {S : Set (X)} (hS : MeasurableSet S) :
    starHomSpectralOperator Φ S ≤ 1 := by
  rw [← starHomSpectralOperator_univ Φ]
  exact starHomSpectralOperator_mono Φ hS MeasurableSet.univ (Set.subset_univ S)

lemma starHomSpectralOperator_empty : starHomSpectralOperator Φ ∅ = 0 := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [starHomSpectralOperator_inner, zero_apply, inner_zero_right,
    (polarizedStarHomScalarMeasure Φ x y).empty]

/-- Finite additivity of `starHomSpectralOperator` on disjoint measurable sets. -/
lemma starHomSpectralOperator_add_of_disjoint {S T : Set (X)} (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hdisj : Disjoint S T) :
    starHomSpectralOperator Φ (S ∪ T) =
      starHomSpectralOperator Φ S + starHomSpectralOperator Φ T := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [starHomSpectralOperator_inner, add_apply, inner_add_right,
    starHomSpectralOperator_inner, starHomSpectralOperator_inner,
    (polarizedStarHomScalarMeasure Φ x y).of_union hdisj hS hT]

/-! ## B. Weak countable additivity -/

/-- The operator at `S`, valued in the weak-operator-topology type. -/
noncomputable def starHomSpectralMeasureFun (S : Set (X)) : H →WOT[ℂ] H :=
  ContinuousLinearMapWOT.ofCLM (starHomSpectralOperator Φ S)

@[simp]
lemma starHomSpectralMeasureFun_inner (S : Set (X)) (x y : H) :
    ⟪y, starHomSpectralMeasureFun Φ S x⟫_ℂ = polarizedStarHomScalarMeasure Φ x y S := by
  simp only [starHomSpectralMeasureFun, ContinuousLinearMapWOT.ofCLM_apply]
  exact starHomSpectralOperator_inner Φ S x y

/-- The operators `E(S)`, as a vector measure in the weak operator topology. -/
noncomputable def starHomSpectralVectorMeasure :
    VectorMeasure (X) (H →WOT[ℂ] H) where
  measureOf' := starHomSpectralMeasureFun Φ
  empty' := by
    apply ContinuousLinearMapWOT.ext_inner
    intro x y
    rw [starHomSpectralMeasureFun_inner]
    simp
  not_measurable' S hS := by
    show starHomSpectralMeasureFun Φ S = 0
    unfold starHomSpectralMeasureFun
    rw [starHomSpectralOperator_apply_eq_zero_of_not_measurableSet Φ hS]
    simp
  m_iUnion' f hf hdisj := by
    apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
    intro x y
    have heq : ∀ s : Finset ℕ,
        ⟪y, (∑ i ∈ s, starHomSpectralMeasureFun Φ (f i)) x⟫_ℂ =
          ∑ i ∈ s, ⟪y, starHomSpectralMeasureFun Φ (f i) x⟫_ℂ :=
      fun s => map_sum (QuantumMechanics.WOTSpectralMeasure.innerEvaluation x y) _ s
    simp_rw [heq, starHomSpectralMeasureFun_inner]
    exact (polarizedStarHomScalarMeasure Φ x y).m_iUnion hf hdisj

@[simp]
lemma starHomSpectralVectorMeasure_apply (S : Set (X)) :
    starHomSpectralVectorMeasure Φ S = starHomSpectralMeasureFun Φ S := rfl

/-! ## C. The spectral operators are projections

For a compact set `K` and an open `V ⊇ K`, a Urysohn function `f` gives `E(K) ≤ f(U) ≤ E(V)`. With
the estimate `‖A x‖² ≤ re ⟪x, A x⟫` for `0 ≤ A ≤ 1` and outer regularity this shows `E(K)² = E(K)`.
Inner regularity extends it to measurable sets, and multiplicativity on intersections follows from
additivity.
-/





lemma starHomSpectralOperatorAux_nonneg {S : Set (X)} (hS : MeasurableSet S) :
    0 ≤ starHomSpectralOperatorAux Φ S hS := by
  simpa [starHomSpectralOperator, hS] using starHomSpectralOperator_nonneg Φ hS

lemma starHomSpectralOperatorAux_le_one {S : Set (X)} (hS : MeasurableSet S) :
    starHomSpectralOperatorAux Φ S hS ≤ 1 := by
  simpa [starHomSpectralOperator, hS] using starHomSpectralOperator_le_one Φ hS

lemma starHomSpectralOperatorAux_mono {S T : Set (X)} (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hST : S ⊆ T) :
    starHomSpectralOperatorAux Φ S hS ≤ starHomSpectralOperatorAux Φ T hT := by
  simpa [starHomSpectralOperator, hS, hT] using starHomSpectralOperator_mono Φ hS hT hST

lemma starHomRealOperator_reApplyInnerSelf
    (f : CompactlySupportedContinuousMap (X) ℝ) (x : H) :
    (starHomRealOperator Φ f).reApplyInnerSelf x =
      ∫ z, f z ∂starHomScalarMeasure Φ x := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]
  exact (starHomScalarMeasure_integral Φ x f).symm

lemma starHomSpectralOperator_le_cfcRealOperator_of_compact_subset_open
    {K V : Set (X)} (hK : IsCompact K) (_hV : IsOpen V) (_hKV : K ⊆ V)
    (f : CompactlySupportedContinuousMap (X) ℝ)
    (hfK : Set.EqOn f 1 K) (_hfV : tsupport f ⊆ V) (hf : ∀ z, f z ∈ Set.Icc 0 1) :
    starHomSpectralOperator Φ K ≤ starHomRealOperator Φ f := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_def']
  refine ⟨(starHomRealOperator_isSelfAdjoint Φ f).sub
    (starHomSpectralOperator_isSelfAdjoint Φ K), fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, sub_apply,
    inner_sub_left, map_sub, inner_re_symm, ← starHomScalarMeasure_integral Φ x f]
  rw [inner_re_symm (starHomSpectralOperator Φ K x) x,
    starHomSpectralOperator_inner_self Φ hK.measurableSet x]
  simpa using sub_nonneg.mpr (measureReal_compact_le_integral_of_eqOn_one
    (starHomScalarMeasure Φ x) hK f hfK fun z => (hf z).1)

lemma starHomRealOperator_le_cfcSpectralOperator_of_support_subse
    {V : Set (X)} (hV : IsOpen V)
    (f : CompactlySupportedContinuousMap (X) ℝ)
    (hfV : tsupport f ⊆ V) (hf : ∀ z, f z ∈ Set.Icc 0 1) :
    starHomRealOperator Φ f ≤ starHomSpectralOperator Φ V := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_def']
  refine ⟨(starHomSpectralOperator_isSelfAdjoint Φ V).sub
    (starHomRealOperator_isSelfAdjoint Φ f), fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, sub_apply,
    inner_sub_left, map_sub, inner_re_symm,
    starHomSpectralOperator_inner_self Φ hV.measurableSet x]
  rw [inner_re_symm (starHomRealOperator Φ f x) x,
    ← starHomScalarMeasure_integral Φ x f]
  simpa using sub_nonneg.mpr (integral_le_measureReal_of_support_subset
    (starHomScalarMeasure Φ x) hV f hfV hf)

omit [T2Space X] [BorelSpace X] [CompactSpace X] [MeasurableSpace X] in
lemma starHomRealOperator_mul_self
    (f : CompactlySupportedContinuousMap (X) ℝ) :
    starHomRealOperator Φ (f * f) = starHomRealOperator Φ f * starHomRealOperator Φ f := by
  have hmul : realToComplex (f * f) =
      realToComplex f * realToComplex f := by
    ext z
    simp
  unfold starHomRealOperator
  rw [hmul, map_mul]

omit [T2Space X] [BorelSpace X] [CompactSpace X] [MeasurableSpace X] in
lemma starHomRealOperator_sub_mul_self
    (f : CompactlySupportedContinuousMap (X) ℝ) :
    starHomRealOperator Φ (f - f * f) =
      starHomRealOperator Φ f - starHomRealOperator Φ f * starHomRealOperator Φ f := by
  have hmul : realToComplex (f * f) =
      realToComplex f * realToComplex f := by
    ext z
    simp
  have hsub : realToComplex (f - f * f) =
      realToComplex f - realToComplex (f * f) := by
    ext z
    simp
  unfold starHomRealOperator
  rw [hsub, hmul, map_sub, map_mul]

lemma starHomSpectralOperator_isIdempotent_of_isCompact
    {K : Set (X)} (hK : IsCompact K) :
    IsIdempotentElem (starHomSpectralOperator Φ K) := by
  let A : H →L[ℂ] H := starHomSpectralOperator Φ K
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact starHomSpectralOperator_nonneg Φ hK.measurableSet
  have hA1 : A ≤ 1 := by
    dsimp [A]
    exact starHomSpectralOperator_le_one Φ hK.measurableSet
  have hF1 (f : CompactlySupportedContinuousMap (X) ℝ)
      (hf : ∀ z, f z ∈ Set.Icc 0 1) :
      starHomRealOperator Φ f ≤ 1 := by
    calc
      starHomRealOperator Φ f ≤ starHomSpectralOperator Φ Set.univ :=
        starHomRealOperator_le_cfcSpectralOperator_of_support_subse
          Φ isOpen_univ f (Set.subset_univ _) hf
      _ = 1 := starHomSpectralOperator_univ Φ
  have hD_order (V : Set (X)) (hV : IsOpen V)
      (hKV : K ⊆ V)
      (f : CompactlySupportedContinuousMap (X) ℝ)
      (hfK : Set.EqOn f 1 K) (hfV : tsupport f ⊆ V) (hf : ∀ z, f z ∈ Set.Icc 0 1) :
      0 ≤ starHomRealOperator Φ f - A ∧
        starHomRealOperator Φ f - A ≤ 1 := by
    have hAF : A ≤ starHomRealOperator Φ f := by
      dsimp [A]
      exact starHomSpectralOperator_le_cfcRealOperator_of_compact_subset_open
        Φ hK hV hKV f hfK hfV hf
    have hF0 : 0 ≤ starHomRealOperator Φ f :=
      ContinuousLinearMap.nonneg_iff_isPositive.mpr
        (starHomRealOperator_nonneg Φ f (fun z => (hf z).1))
    have hFone := hF1 f hf
    constructor
    · exact sub_nonneg.mpr hAF
    · calc
        starHomRealOperator Φ f - A ≤ starHomRealOperator Φ f - 0 :=
          sub_le_sub_left hA0 _
        _ ≤ 1 := by simpa using hFone
  have hcompact : ∀ (x : H),
      (starHomSpectralOperator Φ K) (starHomSpectralOperator Φ K x) =
        starHomSpectralOperator Φ K x := by
    intro x
    apply eq_of_sub_eq_zero
    rw [← norm_eq_zero]
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (norm_nonneg _)
    let μx := starHomScalarMeasure Φ x
    let μAx := starHomScalarMeasure Φ (A x)
    let ν := μx + μAx
    let δ : ℝ := (ε / 4) ^ 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨V, hKV, hV, hνV⟩ :=
      hK.measurableSet.exists_isOpen_sdiff_lt (μ := ν)
        (measure_ne_top ν K) (ENNReal.ofReal_pos.mpr hδ).ne'
    let ug : C(X, ℝ) :=
      Classical.choose (exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV)
    have hug := Classical.choose_spec
      (exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV)
    let f0 : CompactlySupportedContinuousMap (X) ℝ :=
      ⟨ug, hasCompactSupport_def.mpr hug.2.1⟩
    have hf0K : Set.EqOn f0 1 K := by simpa [f0, ug] using hug.1
    have hf0V : tsupport f0 ⊆ V := by simpa [f0, ug] using hug.2.2.1
    have hf0 : ∀ z, f0 z ∈ Set.Icc 0 1 := by simpa [f0, ug] using hug.2.2.2
    let F := starHomRealOperator Φ f0
    let D := F - A
    have hD0 : 0 ≤ D := by
      dsimp [D, F]
      exact (hD_order V hV hKV f0 hf0K hf0V hf0).1
    have hD1 : D ≤ 1 := by
      dsimp [D, F]
      exact (hD_order V hV hKV f0 hf0K hf0V hf0).2
    have hD_est (z : H) (hz : z = x ∨ z = A x) :
        ‖D z‖ ^ 2 ≤ (starHomScalarMeasure Φ z).real (V \ K) := by
      have hpc := norm_sq_le_inner_of_isPositive_of_le_one hD0 hD1 z
      have hupper : (∫ y, f0 y ∂starHomScalarMeasure Φ z) ≤
          (starHomScalarMeasure Φ z).real V := by
        exact integral_le_measureReal_of_support_subset
          (starHomScalarMeasure Φ z) hV f0 hf0V hf0
      have hsplit : (starHomScalarMeasure Φ z).real K +
          (starHomScalarMeasure Φ z).real (V \ K) =
          (starHomScalarMeasure Φ z).real V := by
        rw [measureReal_add_sdiff hK.measurableSet (measure_ne_top _ _)
          (measure_ne_top _ _), union_eq_right.mpr hKV]
      have hinner : RCLike.re ⟪z, D z⟫_ℂ =
          (∫ y, f0 y ∂starHomScalarMeasure Φ z) -
            (starHomScalarMeasure Φ z).real K := by
        dsimp [D, F]
        rw [sub_apply, inner_sub_right]
        change (⟪z, (starHomRealOperator Φ f0) z⟫_ℂ - ⟪z, A z⟫_ℂ).re = _
        change RCLike.re ⟪z, (starHomRealOperator Φ f0) z⟫_ℂ -
          RCLike.re ⟪z, A z⟫_ℂ = _
        rw [← starHomScalarMeasure_integral Φ z f0,
          starHomSpectralOperator_inner_self Φ hK.measurableSet z]
        norm_num
      calc
        ‖D z‖ ^ 2 ≤ RCLike.re ⟪z, D z⟫_ℂ := hpc
        _ = (∫ y, f0 y ∂starHomScalarMeasure Φ z) -
            (starHomScalarMeasure Φ z).real K := hinner
        _ ≤ (starHomScalarMeasure Φ z).real (V \ K) := by linarith
    have hD_lt (z : H) (hz : z = x ∨ z = A x) : ‖D z‖ < ε / 4 := by
      have hνlt : ν.real (V \ K) < δ :=
        measureReal_lt_of_measure_lt_of_pos ν hδ hνV.2
      have hzν : (starHomScalarMeasure Φ z).real (V \ K) ≤ ν.real (V \ K) := by
        rcases hz with rfl | rfl
        · rw [measureReal_def, measureReal_def]
          exact ENNReal.toReal_mono (measure_ne_top ν (V \ K))
            ((MeasureTheory.Measure.le_add_right le_rfl) (V \ K))
        · rw [measureReal_def, measureReal_def]
          exact ENNReal.toReal_mono (measure_ne_top ν (V \ K))
            ((MeasureTheory.Measure.le_add_left le_rfl) (V \ K))
      have hs := (hD_est z hz).trans_lt (hzν.trans_lt hνlt)
      dsimp [δ] at hs
      nlinarith [norm_nonneg (D z)]
    let q : CompactlySupportedContinuousMap (X) ℝ := f0 - f0 * f0
    have hq (z : X) : q z ∈ Set.Icc 0 1 := by
      dsimp [q]
      have hz := hf0 z
      constructor <;> nlinarith [hz.1, hz.2]
    have hq_ind (z : X) : q z ≤ (V \ K).indicator 1 z := by
      by_cases hz : z ∈ V \ K
      · simp [hz, (hq z).2]
      · have hz' : z ∉ V ∨ z ∈ K := by
          by_cases hzV : z ∈ V
          · right
            by_contra hzK
            exact hz ⟨hzV, hzK⟩
          · exact Or.inl hzV
        rcases hz' with hzV | hzK
        · have hzsupport : z ∉ tsupport f0 := fun hz' => hzV (hf0V hz')
          have hfz : f0 z = 0 := image_eq_zero_of_notMem_tsupport hzsupport
          simp [q, hfz, hzV]
        · have hfz : f0 z = 1 := hf0K hzK
          dsimp [q]
          simp [hfz, hzK]
    let Q := starHomRealOperator Φ q
    have hQ0 : 0 ≤ Q := by
      dsimp [Q]
      exact ContinuousLinearMap.nonneg_iff_isPositive.mpr
        (starHomRealOperator_nonneg Φ q (fun z => (hq z).1))
    have hQ1 : Q ≤ 1 := by
      dsimp [Q]
      exact hF1 q hq
    have hQ_est : ‖Q x‖ ^ 2 ≤ μx.real (V \ K) := by
      have hpc := norm_sq_le_inner_of_isPositive_of_le_one hQ0 hQ1 x
      have hinner : RCLike.re ⟪x, Q x⟫_ℂ = ∫ z, q z ∂μx := by
        dsimp [Q, μx]
        exact (starHomScalarMeasure_integral Φ x q).symm
      calc
        ‖Q x‖ ^ 2 ≤ RCLike.re ⟪x, Q x⟫_ℂ := hpc
        _ = ∫ z, q z ∂μx := hinner
        _ ≤ μx.real (V \ K) := integral_le_measureReal_of_le_indicator μx
          (hV.sdiff hK.isClosed).measurableSet q (fun z => (hq z).1) hq_ind
    have hQ_lt : ‖Q x‖ < ε / 4 := by
      have hνlt : ν.real (V \ K) < δ :=
        measureReal_lt_of_measure_lt_of_pos ν hδ hνV.2
      have hμν : μx.real (V \ K) ≤ ν.real (V \ K) := by
        rw [measureReal_def, measureReal_def]
        exact ENNReal.toReal_mono (measure_ne_top ν (V \ K))
          ((MeasureTheory.Measure.le_add_right le_rfl) (V \ K))
      have hs := hQ_est.trans_lt (hμν.trans_lt hνlt)
      dsimp [δ] at hs
      nlinarith [norm_nonneg (Q x)]
    have hFop : ‖F‖ ≤ 1 := by
      exact (CStarAlgebra.norm_le_one_iff_of_nonneg F
        (ContinuousLinearMap.nonneg_iff_isPositive.mpr
          (starHomRealOperator_nonneg Φ f0 (fun z => (hf0 z).1)))).2
        (hF1 f0 hf0)
    have hexpand : A * A - A =
        (A - F) * A + F * (A - F) + (F * F - F) + (F - A) := by
      noncomm_ring
    have hbound : ‖(A * A - A) x‖ ≤ ε := by
      rw [hexpand]
      change ‖(A - F) (A x) + F ((A - F) x) +
        (F (F x) - F x) + (F x - A x)‖ ≤ ε
      calc
        ‖(A - F) (A x) + F ((A - F) x) + (F (F x) - F x) + (F x - A x)‖ ≤
            ‖(A - F) (A x)‖ + ‖F ((A - F) x)‖ +
              ‖F (F x) - F x‖ + ‖F x - A x‖ := by
                calc
                  _ ≤ ‖(A - F) (A x) + F ((A - F) x) + (F (F x) - F x)‖ +
                      ‖F x - A x‖ := norm_add_le _ _
                  _ ≤ (‖(A - F) (A x) + F ((A - F) x)‖ +
                      ‖F (F x) - F x‖) + ‖F x - A x‖ := by
                    gcongr
                    exact norm_add_le _ _
                  _ ≤ ((‖(A - F) (A x)‖ + ‖F ((A - F) x)‖) +
                      ‖F (F x) - F x‖) + ‖F x - A x‖ := by
                    gcongr
                    exact norm_add_le _ _
        _ ≤ ε / 4 + ε / 4 + ε / 4 + ε / 4 := by
          have h1 : ‖(A - F) (A x)‖ < ε / 4 := by
            have h' := hD_lt (A x) (Or.inr rfl)
            change ‖F (A x) - A (A x)‖ < ε / 4 at h'
            change ‖A (A x) - F (A x)‖ < ε / 4
            rw [show A (A x) - F (A x) = -(F (A x) - A (A x)) by abel, norm_neg]
            exact h'
          have h2 : ‖F ((A - F) x)‖ ≤ ‖(A - F) x‖ := by
            calc
              ‖F ((A - F) x)‖ ≤ ‖F‖ * ‖(A - F) x‖ := F.le_opNorm _
              _ ≤ ‖(A - F) x‖ := by
                nlinarith [hFop, norm_nonneg ((A - F) x)]
          have h2' : ‖F ((A - F) x)‖ < ε / 4 :=
            h2.trans_lt (by
              have h' := hD_lt x (Or.inl rfl)
              change ‖F x - A x‖ < ε / 4 at h'
              change ‖A x - F x‖ < ε / 4
              rw [show A x - F x = -(F x - A x) by abel, norm_neg]
              exact h')
          have hQeq : Q = F - F * F := by
            dsimp [Q, F]
            exact starHomRealOperator_sub_mul_self Φ f0
          have h3 : ‖F (F x) - F x‖ < ε / 4 := by
            have heq : F (F x) - F x = -Q x := by
              calc
                F (F x) - F x = -(F - F * F) x := by
                  simp [ContinuousLinearMap.mul_def, sub_eq_add_neg]
                _ = -Q x := by rw [hQeq]
            rw [heq]
            simpa [norm_neg] using hQ_lt
          have h4 : ‖F x - A x‖ < ε / 4 := by
            have h' := hD_lt x (Or.inl rfl)
            change ‖F x - A x‖ < ε / 4 at h'
            exact h'
          linarith only [h1, h2', h3, h4]
        _ ≤ ε := by
          ring_nf
          exact le_rfl
    simpa using hbound
  apply ContinuousLinearMap.ext
  intro x
  exact hcompact x

/-- **`E(S)` is idempotent.** For compact `S` this follows from a Urysohn function between `S` and
an open neighbourhood, using `0 ≤ A ≤ 1 ⟹ ‖A x‖² ≤ re ⟪x, A x⟫`; inner regularity extends it to
measurable `S`. -/
lemma starHomSpectralOperatorAux_isIdempotentElem (S : Set (X)) (hS : MeasurableSet S) :
    starHomSpectralOperatorAux Φ S hS * starHomSpectralOperatorAux Φ S hS =
      starHomSpectralOperatorAux Φ S hS := by
  let A : H →L[ℂ] H := starHomSpectralOperator Φ S
  have hA0 : 0 ≤ A := starHomSpectralOperator_nonneg Φ hS
  have hA1 : A ≤ 1 := starHomSpectralOperator_le_one Φ hS
  have hA_id : A * A = A := by
    apply ContinuousLinearMap.ext
    intro x
    apply eq_of_sub_eq_zero
    rw [← norm_eq_zero]
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (norm_nonneg _)
    let μx := starHomScalarMeasure Φ x
    let μAx := starHomScalarMeasure Φ (A x)
    let ν := μx + μAx
    let δ : ℝ := (ε / 4) ^ 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨K, hKS, hK, hνK⟩ := hS.exists_isCompact_sdiff_lt
      (measure_ne_top ν S) (ENNReal.ofReal_pos.mpr hδ).ne'
    let P : H →L[ℂ] H := starHomSpectralOperator Φ K
    have hP0 : 0 ≤ P := starHomSpectralOperator_nonneg Φ hK.measurableSet
    have hP1 : P ≤ 1 := starHomSpectralOperator_le_one Φ hK.measurableSet
    have hP_id : P * P = P := starHomSpectralOperator_isIdempotent_of_isCompact Φ hK
    have hPA : P ≤ A := by
      dsimp [P, A]
      exact starHomSpectralOperator_mono Φ hK.measurableSet hS hKS
    let D : H →L[ℂ] H := A - P
    have hD0 : 0 ≤ D := by
      dsimp [D]
      exact sub_nonneg.mpr hPA
    have hD1 : D ≤ 1 := by
      dsimp [D]
      calc
        A - P ≤ A - 0 := sub_le_sub_left hP0 _
        _ ≤ 1 := by simpa using hA1
    have hD_est (z : H) (hz : z = x ∨ z = A x) :
        ‖D z‖ ^ 2 ≤ (starHomScalarMeasure Φ z).real (S \ K) := by
      have hpc := norm_sq_le_inner_of_isPositive_of_le_one hD0 hD1 z
      have hsplit : (starHomScalarMeasure Φ z).real K +
          (starHomScalarMeasure Φ z).real (S \ K) =
          (starHomScalarMeasure Φ z).real S := by
        rw [measureReal_add_sdiff hK.measurableSet (measure_ne_top _ _)
          (measure_ne_top _ _), union_eq_right.mpr hKS]
      have hinner : RCLike.re ⟪z, D z⟫_ℂ =
          (starHomScalarMeasure Φ z).real S -
            (starHomScalarMeasure Φ z).real K := by
        dsimp [D]
        rw [sub_apply, inner_sub_right]
        change (⟪z, A z⟫_ℂ - ⟪z, P z⟫_ℂ).re = _
        change RCLike.re ⟪z, A z⟫_ℂ - RCLike.re ⟪z, P z⟫_ℂ = _
        rw [starHomSpectralOperator_inner_self Φ hS z,
          starHomSpectralOperator_inner_self Φ hK.measurableSet z]
        norm_num
      calc
        ‖D z‖ ^ 2 ≤ RCLike.re ⟪z, D z⟫_ℂ := hpc
        _ = (starHomScalarMeasure Φ z).real S -
            (starHomScalarMeasure Φ z).real K := hinner
        _ ≤ (starHomScalarMeasure Φ z).real (S \ K) := by linarith [hsplit]
    have hD_lt (z : H) (hz : z = x ∨ z = A x) : ‖D z‖ < ε / 4 := by
      have hνlt : ν.real (S \ K) < δ :=
        measureReal_lt_of_measure_lt_of_pos ν hδ hνK
      have hzν : (starHomScalarMeasure Φ z).real (S \ K) ≤ ν.real (S \ K) := by
        rcases hz with rfl | rfl
        · rw [measureReal_def, measureReal_def]
          exact ENNReal.toReal_mono (measure_ne_top ν (S \ K))
            ((MeasureTheory.Measure.le_add_right le_rfl) (S \ K))
        · rw [measureReal_def, measureReal_def]
          exact ENNReal.toReal_mono (measure_ne_top ν (S \ K))
            ((MeasureTheory.Measure.le_add_left le_rfl) (S \ K))
      have hs := (hD_est z hz).trans_lt (hzν.trans_lt hνlt)
      dsimp [δ] at hs
      nlinarith [norm_nonneg (D z)]
    have hPop : ‖P‖ ≤ 1 := by
      exact (CStarAlgebra.norm_le_one_iff_of_nonneg P
        (ContinuousLinearMap.nonneg_iff_isPositive.mpr
          (starHomSpectralOperator_isPositive Φ hK.measurableSet))).2 hP1
    have hexpand : A * A - A = (A - P) * A + P * (A - P) - (A - P) := by
      calc
        A * A - A = A * A - A + (P - P * P) := by rw [hP_id]; simp
        _ = (A - P) * A + P * (A - P) - (A - P) := by noncomm_ring
    have hbound : ‖(A * A - A) x‖ ≤ ε := by
      rw [hexpand]
      change ‖(A - P) (A x) + P ((A - P) x) - (A - P) x‖ ≤ ε
      calc
        ‖(A - P) (A x) + P ((A - P) x) - (A - P) x‖ ≤
            ‖(A - P) (A x)‖ + ‖P ((A - P) x)‖ + ‖(A - P) x‖ := by
          calc
            _ ≤ ‖(A - P) (A x) + P ((A - P) x)‖ + ‖(A - P) x‖ := norm_sub_le _ _
            _ ≤ (‖(A - P) (A x)‖ + ‖P ((A - P) x)‖) + ‖(A - P) x‖ := by
              gcongr
              exact norm_add_le _ _
        _ ≤ ε / 4 + ε / 4 + ε / 4 := by
          have h1 : ‖(A - P) (A x)‖ < ε / 4 := by
            have h' := hD_lt (A x) (Or.inr rfl)
            change ‖(A - P) (A x)‖ < ε / 4 at h'
            exact h'
          have h2 : ‖P ((A - P) x)‖ ≤ ‖(A - P) x‖ := by
            calc
              ‖P ((A - P) x)‖ ≤ ‖P‖ * ‖(A - P) x‖ := P.le_opNorm _
              _ ≤ ‖(A - P) x‖ := by
                nlinarith [hPop, norm_nonneg ((A - P) x)]
          have h2' : ‖P ((A - P) x)‖ < ε / 4 :=
            h2.trans_lt (by
              have h' := hD_lt x (Or.inl rfl)
              change ‖(A - P) x‖ < ε / 4 at h'
              exact h')
          have h3 : ‖(A - P) x‖ < ε / 4 := by
            have h' := hD_lt x (Or.inl rfl)
            change ‖(A - P) x‖ < ε / 4 at h'
            exact h'
          linarith only [h1, h2', h3]
        _ ≤ ε := by
          ring_nf
          nlinarith [hε]
    simpa [sub_apply] using hbound
  simpa [A, starHomSpectralOperator, hS] using hA_id

/-! The idempotency proof above is the reusable order/regularity construction.  It first proves
the compact case with an Urysohn cutoff and outer regularity, then approximates an arbitrary
measurable set from inside by compact sets.  The only analytic estimate is the positive
contraction inequality `0 ≤ A ≤ 1 ⟹ ‖A x‖² ≤ re ⟪x, A x⟫`; no weak/strong operator topology
argument or multiplication of operator limits is involved. -/

/-- Idempotency of `starHomSpectralOperator` on every set — `0` (hence trivially idempotent) off the
measurable sets, and the order/regularity theorem above on measurable sets. -/
lemma starHomSpectralOperator_isIdempotentElem (S : Set (X)) :
    IsIdempotentElem (starHomSpectralOperator Φ S) := by
  unfold starHomSpectralOperator IsIdempotentElem
  split_ifs with hS
  · exact starHomSpectralOperatorAux_isIdempotentElem Φ S hS
  · simp

/-- `starHomSpectralOperator Φ S` is a star-projection, for every `S`; both self-adjointness and
idempotency are proved. -/
lemma starHomSpectralOperator_isStarProjection (S : Set (X)) :
    IsStarProjection (starHomSpectralOperator Φ S) :=
  ⟨starHomSpectralOperator_isIdempotentElem Φ S, starHomSpectralOperator_isSelfAdjoint Φ S⟩

/-! ## D. The spectral measure -/

/-- **The weak-operator spectral measure of a bounded normal operator.**  Assembled from the
Riesz-represented, weakly σ-additive family `starHomSpectralOperator` (Steps B–C, fully proved) and
the star-projection property (Step D), including the order/regularity proof of idempotency. -/
noncomputable def starHomSpectralMeasure : QuantumMechanics.WOTSpectralMeasure (X) H where
  toVectorMeasure := starHomSpectralVectorMeasure Φ
  isStarProjection' S := by
    show IsStarProjection (starHomSpectralMeasureFun Φ S)
    unfold starHomSpectralMeasureFun
    refine ⟨?_, ?_⟩
    · show ContinuousLinearMapWOT.ofCLM (starHomSpectralOperator Φ S) *
        ContinuousLinearMapWOT.ofCLM (starHomSpectralOperator Φ S) =
        ContinuousLinearMapWOT.ofCLM (starHomSpectralOperator Φ S)
      rw [← ContinuousLinearMapWOT.ofCLM_mul]
      exact congrArg ContinuousLinearMapWOT.ofCLM (starHomSpectralOperator_isIdempotentElem Φ S)
    · apply ContinuousLinearMapWOT.toCLM_injective
      change star (starHomSpectralOperator Φ S) = starHomSpectralOperator Φ S
      exact starHomSpectralOperator_isSelfAdjoint Φ S
  univ' := by
    show starHomSpectralMeasureFun Φ Set.univ = 1
    unfold starHomSpectralMeasureFun
    rw [starHomSpectralOperator_univ, ContinuousLinearMapWOT.ofCLM_one]

@[simp]
lemma starHomSpectralMeasure_apply (S : Set (X)) :
    starHomSpectralMeasure Φ S = starHomSpectralMeasureFun Φ S := rfl

/-- The scalar
  measure attached to `starHomSpectralMeasure` is exactly the polarized Riesz measure it
was built from.   -/
lemma starHomSpectralMeasure_scalarMeasure (x y : H) :
    (starHomSpectralMeasure Φ).scalarMeasure x y = polarizedStarHomScalarMeasure Φ x y := by
  apply MeasureTheory.VectorMeasure.ext
  intro S _
  rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply, starHomSpectralMeasure_apply]
  exact starHomSpectralMeasureFun_inner Φ S x y

/-- **The spectral measure reconstructs the functional calculus**: integrating a continuous function
`f` gives `f(U)`. -/
lemma starHomSpectralMeasure_reconstruction
    (f : CompactlySupportedContinuousMap (X) ℝ) (x y : H) :
    (starHomSpectralMeasure Φ).complexWeakIntegral (fun z => (f z : ℂ)) x y =
      ⟪y, starHomRealOperator Φ f x⟫_ℂ := by
  unfold QuantumMechanics.WOTSpectralMeasure.complexWeakIntegral
  rw [starHomSpectralMeasure_scalarMeasure]
  exact polarizedStarHomScalarMeasure_complexIntegral_eq_inner Φ f x y

/-! ## E. Commutation with the commutant

omit [MeasurableSpace X] in
An operator commuting with the range of `Φ` commutes with `Φ f` for continuous `f`, and by
uniqueness in the Riesz–Markov–Kakutani theorem with every spectral projection of `Φ`.   -/

omit [T2Space X] [BorelSpace X] [CompactSpace X] [MeasurableSpace X] in
/-- An operator commuting with the range of `Φ` commutes with `Φ` at every real test function. -/
lemma starHomRealOperator_commute {T : H →L[ℂ] H} (hT : ∀ f : C(X, ℂ), Commute (Φ f) T)
    (f : CompactlySupportedContinuousMap (X) ℝ) :
    Commute (starHomRealOperator Φ f) T :=
  hT (realToComplex f)

/-- If `T` is an isometry (`star T * T = 1`) commuting with `U` and `star U`, the vector-state
Riesz measure at `T v` agrees with the one at `v`: an isometric intertwiner of `U` leaves the
diagonal spectral measure unchanged. -/
lemma starHomScalarMeasure_eq_of_commute_isometry
    {T : H →L[ℂ] H} (hT : ∀ f : C(X, ℂ), Commute (Φ f) T)
    (hTiso : star T * T = 1) (v : H) :
    starHomScalarMeasure Φ (T v) = starHomScalarMeasure Φ v := by
  apply MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [starHomScalarMeasure_integral, starHomScalarMeasure_integral]
  have hcomm : starHomRealOperator Φ f * T = T * starHomRealOperator Φ f :=
    starHomRealOperator_commute Φ hT f
  have hcommv : starHomRealOperator Φ f (T v) = T (starHomRealOperator Φ f v) := by
    have h := congrArg (fun A : H →L[ℂ] H => A v) hcomm
    simpa using h
  rw [hcommv]
  have hTT : ⟪T v, T (starHomRealOperator Φ f v)⟫_ℂ = ⟪v, starHomRealOperator Φ f v⟫_ℂ := by
    have h := ContinuousLinearMap.adjoint_inner_right T v (T (starHomRealOperator Φ f v))
    rw [← h, ← ContinuousLinearMap.star_eq_adjoint]
    have hw : star T (T (starHomRealOperator Φ f v)) = starHomRealOperator Φ f v := by
      have := congrArg (fun A : H →L[ℂ] H => A (starHomRealOperator Φ f v)) hTiso
      simpa using this
    rw [hw]
  rw [hTT]

/-- If `T` is unitary and commutes with `U` and `star U`, the polarized Riesz measure intertwines:
testing at `(T x, y)` matches testing at `(x, star T y)`.  This is the sesquilinear form of the
commutation identity,
  and is exactly what `starHomSpectralOperator_inner` needs to see commutation of
each spectral projection with `T`. -/
lemma polarizedStarHomScalarMeasure_eq_of_commute_unitary
    {T : H →L[ℂ] H} (hT : ∀ f : C(X, ℂ), Commute (Φ f) T)
    (hTunit : T ∈ unitary (H →L[ℂ] H)) (x y : H) :
    polarizedStarHomScalarMeasure Φ (T x) y =
      polarizedStarHomScalarMeasure Φ x (star T y) := by
  have hTT : star T * T = (1 : H →L[ℂ] H) := Unitary.star_mul_self_of_mem hTunit
  have hTT' : T * star T = (1 : H →L[ℂ] H) := Unitary.mul_star_self_of_mem hTunit
  set w : H := star T y with hw_def
  have hTw : T w = y := by
    have h := congrArg (fun A : H →L[ℂ] H => A y) hTT'
    simpa [hw_def] using h
  have hTxw : T x + y = T (x + w) := by rw [map_add, hTw]
  have hTxw' : T x - y = T (x - w) := by rw [map_sub, hTw]
  have hTxIw : T x + Complex.I • y = T (x + Complex.I • w) := by
    rw [map_add, map_smul, hTw]
  have hTxIw' : T x - Complex.I • y = T (x - Complex.I • w) := by
    rw [map_sub, map_smul, hTw]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  rw [polarizedStarHomScalarMeasure_apply Φ hS, polarizedStarHomScalarMeasure_apply Φ hS,
    hTxw, hTxw', hTxIw, hTxIw',
    starHomScalarMeasure_eq_of_commute_isometry Φ hT hTT (x + w),
    starHomScalarMeasure_eq_of_commute_isometry Φ hT hTT (x - w),
    starHomScalarMeasure_eq_of_commute_isometry Φ hT hTT (x + Complex.I • w),
    starHomScalarMeasure_eq_of_commute_isometry Φ hT hTT (x - Complex.I • w)]

/-- Every spectral operator `starHomSpectralOperator Φ S` commutes with any unitary intertwiner of
`U` (i.e. any unitary commuting with both `U` and `star U`).  Holds for *every* `S`, measurable or
not, since `starHomSpectralOperator_inner` itself needs no measurability hypothesis. -/
lemma starHomSpectralOperator_commute_of_commute_unitary
    {T : H →L[ℂ] H} (hT : ∀ f : C(X, ℂ), Commute (Φ f) T)
    (hTunit : T ∈ unitary (H →L[ℂ] H)) (S : Set (X)) :
    starHomSpectralOperator Φ S * T = T * starHomSpectralOperator Φ S := by
  ext v
  apply ext_inner_left ℂ
  intro y
  show ⟪y, (starHomSpectralOperator Φ S * T) v⟫_ℂ = ⟪y, (T * starHomSpectralOperator Φ S) v⟫_ℂ
  rw [show (starHomSpectralOperator Φ S * T) v = starHomSpectralOperator Φ S (T v) from rfl,
    show (T * starHomSpectralOperator Φ S) v = T (starHomSpectralOperator Φ S v) from rfl,
    starHomSpectralOperator_inner Φ S (T v) y,
    polarizedStarHomScalarMeasure_eq_of_commute_unitary Φ hT hTunit v y,
    ← starHomSpectralOperator_inner Φ S v (star T y),
    ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left T (starHomSpectralOperator Φ S v) y

/-- The weak-operator spectral measure `starHomSpectralMeasure Φ` commutes with any unitary
intertwiner of `U`, at every set (measurable or not). -/
lemma starHomSpectralMeasure_commute_of_commute_unitary
    {T : H →L[ℂ] H} (hT : ∀ f : C(X, ℂ), Commute (Φ f) T)
    (hTunit : T ∈ unitary (H →L[ℂ] H)) (S : Set (X)) :
    starHomSpectralMeasure Φ S * ContinuousLinearMapWOT.ofCLM T =
      ContinuousLinearMapWOT.ofCLM T * starHomSpectralMeasure Φ S := by
  rw [starHomSpectralMeasure_apply]
  show ContinuousLinearMapWOT.ofCLM (starHomSpectralOperator Φ S) *
      ContinuousLinearMapWOT.ofCLM T =
    ContinuousLinearMapWOT.ofCLM T * ContinuousLinearMapWOT.ofCLM (starHomSpectralOperator Φ S)
  rw [← ContinuousLinearMapWOT.ofCLM_mul, ← ContinuousLinearMapWOT.ofCLM_mul]
  exact congrArg ContinuousLinearMapWOT.ofCLM
    (starHomSpectralOperator_commute_of_commute_unitary Φ hT hTunit S)

end StarHomScalar

end QuantumMechanics

end ProbabilisticTheory

end
