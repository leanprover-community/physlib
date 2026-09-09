/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Basic
public import Mathlib.MeasureTheory.Measure.Complex

/-!

# Scalar and diagonal measures of a weak spectral measure

Testing `μS : WOTSpectralMeasure α H` against a pair of vectors `x, y : H` gives a complex
*scalar* measure `S ↦ ⟪y, μS S x⟫`, and testing against a single vector `x` on the diagonal
gives a positive, finite `Measure α`, `x`'s *diagonal* measure `S ↦ ‖μS S x‖² = re ⟪x, μS S x⟫`.
These are the measure-theoretic inputs to the bounded spectral integral built in
`BoundedIntegral.lean`; they are recorded here first, on their own, because the extensionality
principle `ext_of_scalarMeasure_eq` below — a weak spectral measure is determined by all of its
scalar matrix-coefficient measures — is the basic uniqueness tool used throughout the rest of
this development.

## Main definitions

- `scalarMeasure`, `scalarMeasure_apply` : `μS.scalarMeasure x y S = ⟪y, μS S x⟫`.
- `ext_of_scalarMeasure_eq` : a weak spectral measure is determined by its scalar measures.
- `diagonalMeasure`, `diagonalMeasure_apply_eq_norm_sq` : the vector-state spectral measure
  `μₓ S = ‖μS S x‖²`, and its basic identities (`univ`, `map`, finiteness, homogeneity, the
  parallelogram law).

-/

@[expose] public section

noncomputable section

open scoped Topology InnerProductSpace Function
open ContinuousLinearMap ContinuousLinearMapWOT MeasureTheory Set

namespace QuantumMechanics

namespace WOTSpectralMeasure

variable {α : Type*} [MeasurableSpace α]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μS : WOTSpectralMeasure α H)

/-! ## A. The scalar (matrix-coefficient) measure and extensionality -/

/-- Evaluation of a WOT operator between two test vectors. -/
def innerEvaluation (x y : H) : (H →WOT[ℂ] H) →+ ℂ where
  toFun A := ⟪y, A x⟫_ℂ
  map_zero' := by simp
  map_add' A B := by
    change ⟪y, (A + B) x⟫_ℂ = _
    rw [ContinuousLinearMapWOT.add_apply, inner_add_right]

lemma continuous_innerEvaluation (x y : H) :
    Continuous (innerEvaluation (H := H) x y) := by
  change Continuous (fun A : H →WOT[ℂ] H ↦ ⟪y, A x⟫_ℂ)
  fun_prop

/-- The complex scalar measure obtained by testing a WOT spectral measure against `x` and `y`.
This is the measure used to state the unbounded reconstruction law weakly. -/
def scalarMeasure (x y : H) : ComplexMeasure α :=
  μS.toVectorMeasure.mapRange (innerEvaluation (H := H) x y)
    (continuous_innerEvaluation x y)

@[simp]
lemma scalarMeasure_apply (x y : H) (S : Set α) :
    μS.scalarMeasure x y S = ⟪y, μS S x⟫_ℂ := by
  simp [scalarMeasure, innerEvaluation]

lemma scalarMeasure_map {β : Type*} [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) (x y : H) :
    (μS.map f hf).scalarMeasure x y = (μS.scalarMeasure x y).map f := by
  apply VectorMeasure.ext
  intro S hS
  rw [scalarMeasure_apply]
  rw [μS.map_apply f hf hS]
  rw [MeasureTheory.VectorMeasure.map_apply _ hf hS]
  rw [scalarMeasure_apply]

/-- A weak spectral measure is determined by all of its scalar matrix-coefficient measures.
This is the extensionality principle used when comparing two spectral constructions obtained by
different bounded or unbounded routes. -/
theorem ext_of_scalarMeasure_eq {μS νS : WOTSpectralMeasure α H}
    (h : ∀ x y : H, μS.scalarMeasure x y = νS.scalarMeasure x y) : μS = νS := by
  rw [WOTSpectralMeasure.mk.injEq]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  apply ContinuousLinearMapWOT.ext_inner
  intro x y
  change μS.scalarMeasure x y S = νS.scalarMeasure x y S
  rw [h x y]

/-! ## B. Positivity on the diagonal

A weak PVM gives a positive scalar measure on every vector state. This is the measure-theoretic
input for the bounded and unbounded spectral integrals; it is deliberately proved here, before any
operator-valued integral is introduced. -/

lemma re_inner_nonneg (S : Set α) (x : H) :
    0 ≤ (⟪x, μS S x⟫_ℂ).re := by
  let p : H →L[ℂ] H := (ContinuousLinearMapWOT.toCLM (μS S))
  have hp := μS.isStarProjection S
  have hmul : p * p = p := by
    exact congrArg ContinuousLinearMapWOT.toCLM hp.isIdempotentElem
  have hstar : ContinuousLinearMap.adjoint p = p := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact congrArg ContinuousLinearMapWOT.toCLM hp.isSelfAdjoint
  have hinner : ⟪x, p x⟫_ℂ = ⟪p x, p x⟫_ℂ := by
    calc
      ⟪x, p x⟫_ℂ = ⟪x, p (p x)⟫_ℂ := by
        congr 1
        exact (congrArg (fun q : H →L[ℂ] H => q x) hmul).symm
      _ = ⟪x, ContinuousLinearMap.adjoint p (p x)⟫_ℂ := by rw [hstar]
      _ = ⟪p x, p x⟫_ℂ := ContinuousLinearMap.adjoint_inner_right p x (p x)
  change 0 ≤ (⟪x, p x⟫_ℂ).re
  rw [hinner]
  exact inner_self_nonneg (𝕜 := ℂ) (x := p x)

lemma re_inner_eq_norm_sq (S : Set α) (x : H) :
    (⟪x, μS S x⟫_ℂ).re = ‖μS S x‖ ^ 2 := by
  let p : H →L[ℂ] H := (ContinuousLinearMapWOT.toCLM (μS S))
  have hp := μS.isStarProjection S
  have hmul : p * p = p := by
    exact congrArg ContinuousLinearMapWOT.toCLM hp.isIdempotentElem
  have hstar : ContinuousLinearMap.adjoint p = p := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact congrArg ContinuousLinearMapWOT.toCLM hp.isSelfAdjoint
  have hinner : ⟪x, p x⟫_ℂ = ⟪p x, p x⟫_ℂ := by
    calc
      ⟪x, p x⟫_ℂ = ⟪x, p (p x)⟫_ℂ := by
        congr 1
        exact (congrArg (fun q : H →L[ℂ] H => q x) hmul).symm
      _ = ⟪x, ContinuousLinearMap.adjoint p (p x)⟫_ℂ := by rw [hstar]
      _ = ⟪p x, p x⟫_ℂ := ContinuousLinearMap.adjoint_inner_right p x (p x)
  change (⟪x, p x⟫_ℂ).re = ‖p x‖ ^ 2
  rw [hinner]
  have hi : (⟪p x, p x⟫_ℂ).re = ‖p x‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (p x)
  exact hi

lemma inner_eq_inner_projection (S : Set α) (x : H) :
    ⟪x, μS S x⟫_ℂ = ⟪μS S x, μS S x⟫_ℂ := by
  let p : H →L[ℂ] H := (ContinuousLinearMapWOT.toCLM (μS S))
  have hp := μS.isStarProjection S
  have hmul : p * p = p := by
    exact congrArg ContinuousLinearMapWOT.toCLM hp.isIdempotentElem
  have hstar : ContinuousLinearMap.adjoint p = p := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact congrArg ContinuousLinearMapWOT.toCLM hp.isSelfAdjoint
  change ⟪x, p x⟫_ℂ = ⟪p x, p x⟫_ℂ
  calc
    ⟪x, p x⟫_ℂ = ⟪x, p (p x)⟫_ℂ := by
      congr 1
      exact (congrArg (fun q : H →L[ℂ] H => q x) hmul).symm
    _ = ⟪x, ContinuousLinearMap.adjoint p (p x)⟫_ℂ := by rw [hstar]
    _ = ⟪p x, p x⟫_ℂ := ContinuousLinearMap.adjoint_inner_right p x (p x)

lemma inner_eq_zero_of_disjoint {A B : Set α} (h : Disjoint A B)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (x : H) :
    ⟪μS A x, μS B x⟫_ℂ = 0 := by
  let pA : H →L[ℂ] H := (ContinuousLinearMapWOT.toCLM (μS A))
  let pB : H →L[ℂ] H := (ContinuousLinearMapWOT.toCLM (μS B))
  have hcomp : pA * pB = 0 := by
    exact congrArg ContinuousLinearMapWOT.toCLM (μS.comp_of_disjoint h hA hB)
  have hstar : ContinuousLinearMap.adjoint pA = pA := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact congrArg ContinuousLinearMapWOT.toCLM (μS.isStarProjection A).isSelfAdjoint
  change ⟪pA x, pB x⟫_ℂ = 0
  calc
    ⟪pA x, pB x⟫_ℂ = ⟪x, ContinuousLinearMap.adjoint pA (pB x)⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right pA x (pB x)).symm
    _ = ⟪x, pA (pB x)⟫_ℂ := by rw [hstar]
    _ = ⟪x, (pA * pB) x⟫_ℂ := by rfl
    _ = 0 := by rw [hcomp]; simp

lemma diagonal_tsum {f : ℕ → Set α} (hf : ∀ i, MeasurableSet (f i))
    (hdisj : Pairwise (Disjoint on f)) (x : H) :
    ENNReal.ofReal (⟪x, μS (⋃ i, f i) x⟫_ℂ).re =
      ∑' i, ENNReal.ofReal (⟪x, μS (f i) x⟫_ℂ).re := by
  have hs := μS.hasSum_inner hf hdisj x x
  have hre : HasSum (fun i ↦ (⟪x, μS (f i) x⟫_ℂ).re)
      (⟪x, μS (⋃ i, f i) x⟫_ℂ).re :=
    hs.map Complex.reCLM.toAddMonoidHom Complex.reCLM.continuous
  have hnonneg : ∀ i, 0 ≤ (⟪x, μS (f i) x⟫_ℂ).re :=
    fun i ↦ μS.re_inner_nonneg (f i) x
  calc
    ENNReal.ofReal (⟪x, μS (⋃ i, f i) x⟫_ℂ).re =
        ENNReal.ofReal (∑' i, (⟪x, μS (f i) x⟫_ℂ).re) :=
      congrArg ENNReal.ofReal hre.tsum_eq.symm
    _ = ∑' i, ENNReal.ofReal (⟪x, μS (f i) x⟫_ℂ).re :=
      ENNReal.ofReal_tsum_of_nonneg hnonneg hre.summable

/-! ## C. The diagonal (vector-state) measure -/

/-- The positive scalar measure obtained by testing a weak PVM on a vector.

Its value on a measurable set is `ofReal (re ⟪x,E(S)x⟫)`. The projection identity below shows
that this is the usual vector-state spectral measure. -/
noncomputable def diagonalMeasure (x : H) : Measure α := by
  let m : ∀ S : Set α, MeasurableSet S → ENNReal :=
    fun S _ => ENNReal.ofReal (⟪x, μS S x⟫_ℂ).re
  have hm_empty : m ∅ MeasurableSet.empty = 0 := by simp [m]
  have hm_iUnion : ∀ ⦃f : ℕ → Set α⦄ (hf : ∀ i, MeasurableSet (f i)),
      Pairwise (Disjoint on f) →
        m (⋃ i, f i) (MeasurableSet.iUnion hf) = ∑' i, m (f i) (hf i) := by
    intro f hf hdisj
    simpa [m] using μS.diagonal_tsum hf hdisj x
  exact Measure.ofMeasurable m hm_empty hm_iUnion

lemma diagonalMeasure_apply (x : H) (S : Set α) (hS : MeasurableSet S) :
    μS.diagonalMeasure x S = ENNReal.ofReal (⟪x, μS S x⟫_ℂ).re := by
  simp only [diagonalMeasure, Measure.ofMeasurable_apply _ hS]

lemma diagonalMeasure_apply_eq_norm_sq (x : H) (S : Set α) (hS : MeasurableSet S) :
    μS.diagonalMeasure x S = ENNReal.ofReal (‖μS S x‖ ^ 2) := by
  rw [μS.diagonalMeasure_apply x S hS, μS.re_inner_eq_norm_sq S x]

lemma diagonalMeasure_univ (x : H) :
    μS.diagonalMeasure x Set.univ = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [μS.diagonalMeasure_apply x Set.univ MeasurableSet.univ, μS.univ]
  change ENNReal.ofReal (⟪x, x⟫_ℂ).re = _
  have hi : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  rw [hi]

lemma diagonalMeasure_map {β : Type*} [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) (x : H) :
    (μS.map f hf).diagonalMeasure x = Measure.map f (μS.diagonalMeasure x) := by
  apply Measure.ext
  intro S hS
  rw [(μS.map f hf).diagonalMeasure_apply x S hS,
    Measure.map_apply hf hS,
    μS.diagonalMeasure_apply x (f ⁻¹' S) (hS.preimage hf)]
  have hmap : μS.map f hf S = μS (f ⁻¹' S) := μS.map_apply f hf hS
  rw [hmap]

instance diagonalMeasure_isFinite (x : H) : IsFiniteMeasure (μS.diagonalMeasure x) where
  measure_univ_lt_top := by
    rw [μS.diagonalMeasure_univ]
    exact ENNReal.ofReal_lt_top

lemma diagonalMeasure_neg (x : H) :
    μS.diagonalMeasure (-x) = μS.diagonalMeasure x := by
  apply Measure.ext
  intro S hS
  rw [μS.diagonalMeasure_apply _ _ hS, μS.diagonalMeasure_apply _ _ hS]
  simp [inner_neg_left, inner_neg_right]

lemma diagonalMeasure_I_smul (x : H) :
    μS.diagonalMeasure (Complex.I • x) = μS.diagonalMeasure x := by
  apply Measure.ext
  intro S hS
  rw [μS.diagonalMeasure_apply _ _ hS, μS.diagonalMeasure_apply _ _ hS]
  simp [inner_smul_left, inner_smul_right]

lemma diagonalMeasure_smul (c : ℂ) (x : H) :
    μS.diagonalMeasure (c • x) = ENNReal.ofReal (‖c‖ ^ 2) • μS.diagonalMeasure x := by
  apply Measure.ext
  intro S hS
  rw [Measure.smul_apply, μS.diagonalMeasure_apply _ _ hS,
    μS.diagonalMeasure_apply _ _ hS]
  have hinner :
      (⟪c • x, μS S (c • x)⟫_ℂ).re =
        ‖c‖ ^ 2 * (⟪x, μS S x⟫_ℂ).re := by
    simp only [map_smul, inner_smul_left, inner_smul_right]
    simp [Complex.mul_re, Complex.mul_im]
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hinner]
  change ENNReal.ofReal (‖c‖ ^ 2 * (⟪x, μS S x⟫_ℂ).re) =
    ENNReal.ofReal (‖c‖ ^ 2) * ENNReal.ofReal (⟪x, μS S x⟫_ℂ).re
  rw [ENNReal.ofReal_mul (sq_nonneg ‖c‖)]

lemma diagonalMeasure_parallelogram (x y : H) :
    μS.diagonalMeasure (x + y) + μS.diagonalMeasure (x - y) =
      (μS.diagonalMeasure x + μS.diagonalMeasure x) +
        (μS.diagonalMeasure y + μS.diagonalMeasure y) := by
  apply Measure.ext
  intro S hS
  rw [Measure.add_apply, Measure.add_apply, Measure.add_apply, Measure.add_apply,
    μS.diagonalMeasure_apply (x + y) S hS, μS.diagonalMeasure_apply (x - y) S hS,
    μS.diagonalMeasure_apply x S hS, μS.diagonalMeasure_apply y S hS]
  have h₁ : 0 ≤ (⟪x + y, μS S (x + y)⟫_ℂ).re := μS.re_inner_nonneg S (x + y)
  have h₂ : 0 ≤ (⟪x - y, μS S (x - y)⟫_ℂ).re := μS.re_inner_nonneg S (x - y)
  have h₃ : 0 ≤ (⟪x, μS S x⟫_ℂ).re := μS.re_inner_nonneg S x
  have h₄ : 0 ≤ (⟪y, μS S y⟫_ℂ).re := μS.re_inner_nonneg S y
  rw [← ENNReal.ofReal_add h₁ h₂]
  have hreal :
      (⟪x + y, μS S (x + y)⟫_ℂ).re +
          (⟪x - y, μS S (x - y)⟫_ℂ).re =
        2 * (⟪x, μS S x⟫_ℂ).re + 2 * (⟪y, μS S y⟫_ℂ).re := by
    simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
      inner_sub_right, Complex.add_re, Complex.sub_re]
    ring
  rw [hreal]
  calc
    ENNReal.ofReal (2 * (⟪x, μS S x⟫_ℂ).re + 2 * (⟪y, μS S y⟫_ℂ).re) =
        ENNReal.ofReal (2 * (⟪x, μS S x⟫_ℂ).re) +
          ENNReal.ofReal (2 * (⟪y, μS S y⟫_ℂ).re) :=
      ENNReal.ofReal_add
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h₃)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h₄)
    _ = ENNReal.ofReal (⟪x, μS S x⟫_ℂ).re +
          ENNReal.ofReal (⟪x, μS S x⟫_ℂ).re +
          (ENNReal.ofReal (⟪y, μS S y⟫_ℂ).re +
            ENNReal.ofReal (⟪y, μS S y⟫_ℂ).re) := by
      rw [show 2 * (⟪x, μS S x⟫_ℂ).re =
          (⟪x, μS S x⟫_ℂ).re + (⟪x, μS S x⟫_ℂ).re by ring]
      rw [show 2 * (⟪y, μS S y⟫_ℂ).re =
          (⟪y, μS S y⟫_ℂ).re + (⟪y, μS S y⟫_ℂ).re by ring]
      rw [ENNReal.ofReal_add h₃ h₃, ENNReal.ofReal_add h₄ h₄]

end WOTSpectralMeasure

end QuantumMechanics

end
