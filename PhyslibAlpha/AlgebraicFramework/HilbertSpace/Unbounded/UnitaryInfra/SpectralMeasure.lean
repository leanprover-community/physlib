/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.UnitaryInfra.SesquilinearForm
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Algebra.Star.Unitary

/-!
# Infrastructure for the bounded-unitary spectral theorem: the spectral measure

Continues `UnitaryInfra/SesquilinearForm.lean`: turns `cfcSesquilinearForm` into
projection-valued operators `cfcSpectralOperator`, proves they are idempotent star-projections
that add over disjoint sets, and assembles the final `cfcSpectralMeasure` — the weak-operator
spectral measure of a bounded normal operator — together with its reconstruction theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology
open scoped ComplexOrder CStarAlgebra InnerProductSpace

namespace QuantumMechanics

section CFCScalar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : H →L[ℂ] H) (hU : IsStarNormal U)

/-- The Riesz-represented operator at the measurable set `S`. -/
noncomputable def cfcSpectralOperatorAux (S : Set (spectrum ℂ U)) (hS : MeasurableSet S) :
    H →L[ℂ] H :=
  InnerProductSpace.continuousLinearMapOfBilin (cfcSesquilinearForm U hU S hS)

lemma cfcSpectralOperatorAux_inner (S : Set (spectrum ℂ U)) (hS : MeasurableSet S) (x y : H) :
    ⟪y, cfcSpectralOperatorAux U hU S hS x⟫_ℂ =
      polarizedCfcScalarMeasure (hU := hU) U x y S := by
  have h := InnerProductSpace.continuousLinearMapOfBilin_apply (cfcSesquilinearForm U hU S hS) x y
  rw [cfcSesquilinearForm_apply] at h
  change ⟪cfcSpectralOperatorAux U hU S hS x, y⟫_ℂ = _ at h
  rw [← inner_conj_symm, h, Complex.conj_conj]

open scoped Classical in
/-- The Riesz-represented operator on every set, `0` off the measurable sets so that this
directly matches `MeasureTheory.VectorMeasure`'s `not_measurable'` convention. -/
noncomputable def cfcSpectralOperator (S : Set (spectrum ℂ U)) : H →L[ℂ] H :=
  if hS : MeasurableSet S then cfcSpectralOperatorAux U hU S hS else 0

lemma cfcSpectralOperator_inner (S : Set (spectrum ℂ U)) (x y : H) :
    ⟪y, cfcSpectralOperator U hU S x⟫_ℂ = polarizedCfcScalarMeasure (hU := hU) U x y S := by
  unfold cfcSpectralOperator
  split_ifs with hS
  · exact cfcSpectralOperatorAux_inner U hU S hS x y
  · simp [(polarizedCfcScalarMeasure (hU := hU) U x y).not_measurable hS]

lemma cfcSpectralOperator_apply_eq_zero_of_not_measurableSet {S : Set (spectrum ℂ U)}
    (hS : ¬MeasurableSet S) : cfcSpectralOperator U hU S = 0 := by
  unfold cfcSpectralOperator
  rw [dif_neg hS]

set_option maxHeartbeats 1000000 in
/-- The `Complex.I`-inversion companion of `cfcScalarMeasure_real_I_smul`: rewrites a Riesz
measure at `v` as the Riesz measure at `(-I) • v`.  This is the algebraic engine behind
Hermitian symmetry of the polarized measure below. -/
theorem cfcScalarMeasure_real_eq_negI_smul (v : H) (S : Set (spectrum ℂ U)) :
    (cfcScalarMeasure U hU v).real S = (cfcScalarMeasure U hU ((-Complex.I) • v)).real S := by
  have hv : Complex.I • ((-Complex.I) • v) = v := by
    rw [smul_smul, show Complex.I * (-Complex.I) = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg],
      one_smul]
  conv_lhs => rw [← hv]
  exact cfcScalarMeasure_real_I_smul U hU ((-Complex.I) • v) S

set_option maxHeartbeats 1000000 in
/-- Hermitian symmetry of the polarized measure: `B(y,x,S) = conj (B(x,y,S))`, matching the
convention that `B` is exactly `⟪y, cfcRealOperator U hU f x⟫` in the limit and inner products
are conjugate-symmetric.  This is the input `cfcSpectralOperator_isSelfAdjoint` needs. -/
lemma polarizedCfcScalarMeasure_conj_symm (x y : H) (S : Set (spectrum ℂ U)) :
    polarizedCfcScalarMeasure (hU := hU) U y x S =
      starRingEnd ℂ (polarizedCfcScalarMeasure (hU := hU) U x y S) := by
  by_cases hS : MeasurableSet S
  · rw [polarizedCfcScalarMeasure_apply U hU hS, polarizedCfcScalarMeasure_apply U hU hS]
    have hcomm : (cfcScalarMeasure U hU (y + x)).real S =
        (cfcScalarMeasure U hU (x + y)).real S := by rw [add_comm y x]
    have hnegcomm : (cfcScalarMeasure U hU (y - x)).real S =
        (cfcScalarMeasure U hU (x - y)).real S := by
      rw [show y - x = -(x - y) by abel, cfcScalarMeasure_real_neg]
    have hnegI : (-Complex.I) • (Complex.I • x) = x := by
      rw [smul_smul, show (-Complex.I) * Complex.I = 1 by
        rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul]
    have hA : (cfcScalarMeasure U hU (y + Complex.I • x)).real S =
        (cfcScalarMeasure U hU (x - Complex.I • y)).real S := by
      have heq : (-Complex.I) • (y + Complex.I • x) = x - Complex.I • y := by
        rw [smul_add, hnegI]; module
      rw [cfcScalarMeasure_real_eq_negI_smul U hU (y + Complex.I • x) S, heq]
    have hB : (cfcScalarMeasure U hU (y - Complex.I • x)).real S =
        (cfcScalarMeasure U hU (x + Complex.I • y)).real S := by
      have heq : (-Complex.I) • (y - Complex.I • x) = -(x + Complex.I • y) := by
        rw [smul_sub, hnegI]; module
      rw [cfcScalarMeasure_real_eq_negI_smul U hU (y - Complex.I • x) S, heq,
        cfcScalarMeasure_real_neg]
    rw [hcomm, hnegcomm, hA, hB]
    simp only [map_add, map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I]
    ring
  · simp [(polarizedCfcScalarMeasure (hU := hU) U y x).not_measurable hS,
      (polarizedCfcScalarMeasure (hU := hU) U x y).not_measurable hS]

/-- `cfcSpectralOperator U hU S` is self-adjoint, for every `S` (measurable or not — the
non-measurable case is trivial since the operator is `0`).  This follows from
`polarizedCfcScalarMeasure_conj_symm` via `LinearMap.IsSymmetric`. -/
lemma cfcSpectralOperator_isSelfAdjoint (S : Set (spectrum ℂ U)) :
    IsSelfAdjoint (cfcSpectralOperator U hU S) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  show ⟪cfcSpectralOperator U hU S x, y⟫_ℂ = ⟪x, cfcSpectralOperator U hU S y⟫_ℂ
  rw [← inner_conj_symm (cfcSpectralOperator U hU S x) y, cfcSpectralOperator_inner,
    cfcSpectralOperator_inner U hU S y x, polarizedCfcScalarMeasure_conj_symm, Complex.conj_conj]

/-- `polarizedCfcScalarMeasure U hU x y` reproduces `⟪y, x⟫` at `S = univ` — the vector-state
counterpart of `cfcHom hU 1 = 1`, and the exact fact `cfcSpectralOperator_univ` needs.  (Moved
ahead of Step E's original position: it has no dependency on the idempotency gap and the
Step 0–4 order/positivity infrastructure below needs `cfcSpectralOperator_univ` early.) -/
lemma polarizedCfcScalarMeasure_univ (x y : H) :
    polarizedCfcScalarMeasure (hU := hU) U x y Set.univ = ⟪y, x⟫_ℂ := by
  have hsq : ∀ v : H, ⟪v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hpol := inner_map_polarization_continuous (1 : H →L[ℂ] H) x y
  simp only [one_apply_eq_self, hsq] at hpol
  rw [polarizedCfcScalarMeasure_apply U hU MeasurableSet.univ]
  simp only [cfcScalarMeasure_real_univ]
  rw [hpol]
  push_cast
  ring

lemma cfcSpectralOperator_univ_apply (x : H) :
    cfcSpectralOperator U hU Set.univ x = x := by
  apply ext_inner_left ℂ
  intro v
  rw [cfcSpectralOperator_inner]
  exact polarizedCfcScalarMeasure_univ U hU x v

lemma cfcSpectralOperator_univ : cfcSpectralOperator U hU Set.univ = 1 := by
  ext x
  rw [cfcSpectralOperator_univ_apply U hU x, one_apply_eq_self]

/-- **The diagonal quadratic form.** Evaluating the reconstruction identity
`cfcSpectralOperator_inner` on the diagonal `y = x` collapses the four-term polarization to the
single vector-state Riesz measure `(cfcScalarMeasure U hU x).real S`: a polarization identity
applied to its own diagonal always recovers the original quadratic form.  The mechanical work is
in showing `μ_{x-x} = μ_0 = 0` (from the parallelogram law at `a = b = 0`), `μ_{x+x} = 4 μ_x`
(parallelogram law at `a = b = x`), and `μ_{x+I•x} = μ_{x-I•x}` (from `Complex.I`-invariance,
`cfcScalarMeasure_real_I_smul`, applied to `x - I • x`). -/
lemma cfcSpectralOperator_inner_self {S : Set (spectrum ℂ U)} (hS : MeasurableSet S) (x : H) :
    ⟪x, cfcSpectralOperator U hU S x⟫_ℂ = ((cfcScalarMeasure U hU x).real S : ℂ) := by
  rw [cfcSpectralOperator_inner, polarizedCfcScalarMeasure_apply U hU hS]
  have hzero : (cfcScalarMeasure U hU (0 : H)).real S = 0 := by
    have h := cfcScalarMeasure_real_parallelogram U hU (0 : H) 0 S
    simp only [add_zero, sub_self] at h
    linarith
  have hxx : x - x = (0 : H) := sub_self x
  have hdouble : (cfcScalarMeasure U hU (x + x)).real S = 4 * (cfcScalarMeasure U hU x).real S := by
    have h := cfcScalarMeasure_real_parallelogram U hU x x S
    rw [hxx, hzero] at h
    linarith
  have hIeq : Complex.I • (x - Complex.I • x) = x + Complex.I • x := by
    rw [smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul, sub_neg_eq_add, add_comm]
  have himag : (cfcScalarMeasure U hU (x + Complex.I • x)).real S =
      (cfcScalarMeasure U hU (x - Complex.I • x)).real S := by
    have h := cfcScalarMeasure_real_I_smul U hU (x - Complex.I • x) S
    rwa [hIeq] at h
  rw [hxx, hzero, hdouble, himag, sub_self]
  push_cast
  ring

/-- `reApplyInnerSelf` version of `cfcSpectralOperator_inner_self`, in the exact shape
`ContinuousLinearMap.IsPositive` consumes. -/
lemma cfcSpectralOperator_reApplyInnerSelf {S : Set (spectrum ℂ U)} (hS : MeasurableSet S)
    (x : H) :
    (cfcSpectralOperator U hU S).reApplyInnerSelf x = (cfcScalarMeasure U hU x).real S := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, ← RCLike.conj_re, inner_conj_symm,
    cfcSpectralOperator_inner_self U hU hS x]
  simp

/-! ## Step 1: elementary order API for `cfcSpectralOperator` -/

/-- `cfcSpectralOperator U hU S` is a positive operator, for measurable `S`. -/
lemma cfcSpectralOperator_isPositive {S : Set (spectrum ℂ U)} (hS : MeasurableSet S) :
    ContinuousLinearMap.IsPositive (cfcSpectralOperator U hU S) := by
  rw [ContinuousLinearMap.isPositive_def']
  refine ⟨cfcSpectralOperator_isSelfAdjoint U hU S, fun x => ?_⟩
  rw [cfcSpectralOperator_reApplyInnerSelf U hU hS x]
  exact cfcScalarMeasure_real_nonneg U hU x S

lemma cfcSpectralOperator_nonneg {S : Set (spectrum ℂ U)} (hS : MeasurableSet S) :
    0 ≤ cfcSpectralOperator U hU S :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (cfcSpectralOperator_isPositive U hU hS)

/-- `cfcSpectralOperator U hU S` is monotone in `S`, for measurable sets, in the Loewner order on
`H →L[ℂ] H`. -/
lemma cfcSpectralOperator_mono {S T : Set (spectrum ℂ U)} (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hST : S ⊆ T) :
    cfcSpectralOperator U hU S ≤ cfcSpectralOperator U hU T := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_def']
  refine ⟨(cfcSpectralOperator_isSelfAdjoint U hU T).sub
    (cfcSpectralOperator_isSelfAdjoint U hU S), fun x => ?_⟩
  show 0 ≤ (cfcSpectralOperator U hU T - cfcSpectralOperator U hU S).reApplyInnerSelf x
  have hTx := cfcSpectralOperator_reApplyInnerSelf U hU hT x
  have hSx := cfcSpectralOperator_reApplyInnerSelf U hU hS x
  have hre : (cfcSpectralOperator U hU T - cfcSpectralOperator U hU S).reApplyInnerSelf x =
      (cfcSpectralOperator U hU T).reApplyInnerSelf x -
        (cfcSpectralOperator U hU S).reApplyInnerSelf x := by
    simp only [ContinuousLinearMap.reApplyInnerSelf_apply, sub_apply,
      inner_sub_left]
    rfl
  rw [hre, hTx, hSx, sub_nonneg]
  exact MeasureTheory.measureReal_mono hST

lemma cfcSpectralOperator_le_one {S : Set (spectrum ℂ U)} (hS : MeasurableSet S) :
    cfcSpectralOperator U hU S ≤ 1 := by
  rw [← cfcSpectralOperator_univ U hU]
  exact cfcSpectralOperator_mono U hU hS MeasurableSet.univ (Set.subset_univ S)

lemma cfcSpectralOperator_empty : cfcSpectralOperator U hU ∅ = 0 := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [cfcSpectralOperator_inner, zero_apply, inner_zero_right,
    (polarizedCfcScalarMeasure (hU := hU) U x y).empty]

/-- Finite additivity of `cfcSpectralOperator` on disjoint measurable sets. -/
lemma cfcSpectralOperator_add_of_disjoint {S T : Set (spectrum ℂ U)} (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hdisj : Disjoint S T) :
    cfcSpectralOperator U hU (S ∪ T) = cfcSpectralOperator U hU S + cfcSpectralOperator U hU T := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [cfcSpectralOperator_inner, add_apply, inner_add_right,
    cfcSpectralOperator_inner, cfcSpectralOperator_inner,
    (polarizedCfcScalarMeasure (hU := hU) U x y).of_union hdisj hS hT]

/-! ## Step C: weak σ-additivity -/

/-- The operator at `S`, valued in the weak-operator-topology type. -/
noncomputable def cfcSpectralMeasureFun (S : Set (spectrum ℂ U)) : H →WOT[ℂ] H :=
  ContinuousLinearMapWOT.ofCLM (cfcSpectralOperator U hU S)

@[simp]
lemma cfcSpectralMeasureFun_inner (S : Set (spectrum ℂ U)) (x y : H) :
    ⟪y, cfcSpectralMeasureFun U hU S x⟫_ℂ = polarizedCfcScalarMeasure (hU := hU) U x y S := by
  simp only [cfcSpectralMeasureFun, ContinuousLinearMapWOT.ofCLM_apply]
  exact cfcSpectralOperator_inner U hU S x y

/-- The Riesz-represented family of operators assembled into a genuine
`MeasureTheory.VectorMeasure`, valued in the weak-operator-topology type `H →WOT[ℂ] H`.  Weak
σ-additivity is transported directly from each `polarizedCfcScalarMeasure U hU x y`'s genuine
`ComplexMeasure` σ-additivity, through
    `ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto`
(the defining property of the weak operator topology) and the additivity of the evaluation
functional `⟪y, · x⟫` over finite sums. -/
noncomputable def cfcSpectralVectorMeasure :
    VectorMeasure (spectrum ℂ U) (H →WOT[ℂ] H) where
  measureOf' := cfcSpectralMeasureFun U hU
  empty' := by
    apply ContinuousLinearMapWOT.ext_inner
    intro x y
    rw [cfcSpectralMeasureFun_inner]
    simp
  not_measurable' S hS := by
    show cfcSpectralMeasureFun U hU S = 0
    unfold cfcSpectralMeasureFun
    rw [cfcSpectralOperator_apply_eq_zero_of_not_measurableSet U hU hS]
    simp
  m_iUnion' f hf hdisj := by
    apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
    intro x y
    have heq : ∀ s : Finset ℕ,
        ⟪y, (∑ i ∈ s, cfcSpectralMeasureFun U hU (f i)) x⟫_ℂ =
          ∑ i ∈ s, ⟪y, cfcSpectralMeasureFun U hU (f i) x⟫_ℂ :=
      fun s => map_sum (QuantumMechanics.WOTSpectralMeasure.innerEvaluation x y) _ s
    simp_rw [heq, cfcSpectralMeasureFun_inner]
    exact (polarizedCfcScalarMeasure (hU := hU) U x y).m_iUnion hf hdisj

@[simp]
lemma cfcSpectralVectorMeasure_apply (S : Set (spectrum ℂ U)) :
    cfcSpectralVectorMeasure U hU S = cfcSpectralMeasureFun U hU S := rfl

/-! ## Step D: `E(S)` is a star-projection

The idempotency proof follows the order/regularity route.  We do not approximate indicator
functions by a sequence and then multiply weak limits.  Instead, the scalar-measure quadratic
form first gives positivity, monotonicity, and the contraction bound for `E(S)`.  For a compact
`K`, a Urysohn function supported in an open `V ⊇ K` gives an order sandwich
`E(K) ≤ f(U) ≤ E(V)`.  The positive-contraction estimate above converts the resulting quadratic
form bounds into vector-norm bounds.  Outer regularity of the finite measure
`μ_x + μ_{E(K)x}` then proves compact-set idempotence by an epsilon argument.  Inner regularity
of `μ_x + μ_{E(S)x}` extends this to arbitrary measurable `S`.  Set multiplicativity is derived
afterwards from finite additivity and orthogonality of projections on disjoint sets.
-/

set_option maxHeartbeats 1000000

section OrderRegularityHelpers

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [CompactSpace X]

omit [CompactSpace X] in
/-- A continuous compactly supported function which is one on a compact set dominates that
compact set's measure in the scalar integral.  This is the lower half of the Urysohn sandwich. -/
@[nolint unusedArguments]
lemma measureReal_compact_le_integral_of_eqOn_one
    (μ : Measure X) [IsFiniteMeasure μ] {K : Set X} (hK : IsCompact K)
    (f : CompactlySupportedContinuousMap X ℝ) (hfK : Set.EqOn f 1 K)
    (hf0 : ∀ x, 0 ≤ f x) :
    μ.real K ≤ ∫ x, f x ∂μ := by
  calc
    μ.real K = ∫ x, K.indicator 1 x ∂μ :=
      MeasureTheory.integral_indicator_one hK.measurableSet |>.symm
    _ ≤ ∫ x, f x ∂μ := by
      refine MeasureTheory.integral_mono ?_ f.integrable ?_
      · exact (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
      · intro x
        by_cases hx : x ∈ K
        · simp [hx, hfK hx]
        · simp [hx, hf0 x]

omit [T2Space X] [CompactSpace X] in
/-- A nonnegative `[0,1]`-valued continuous compactly supported function supported in an open set
is dominated in integral by the indicator of that open set.  This is the upper half of the Urysohn
sandwich. -/
@[nolint unusedArguments]
lemma integral_le_measureReal_of_support_subset
    (μ : Measure X) [IsFiniteMeasure μ] {V : Set X} (hV : IsOpen V)
    (f : CompactlySupportedContinuousMap X ℝ) (hfV : tsupport f ⊆ V)
    (hf : ∀ x, f x ∈ Set.Icc 0 1) :
    (∫ x, f x ∂μ) ≤ μ.real V := by
  calc
    (∫ x, f x ∂μ) ≤ ∫ x, V.indicator 1 x ∂μ := by
      refine MeasureTheory.integral_mono f.integrable ?_ ?_
      · exact IntegrableOn.integrable_indicator integrableOn_const hV.measurableSet
      · intro x
        by_cases hx : x ∈ tsupport f
        · simp [hfV hx, (hf x).2]
        · simp [image_eq_zero_of_notMem_tsupport hx, Set.indicator_nonneg]
    _ = μ.real V := by
      rw [MeasureTheory.integral_indicator_one hV.measurableSet]

omit [T2Space X] [CompactSpace X] in
@[nolint unusedArguments]
lemma integral_le_measureReal_of_le_indicator
    (μ : Measure X) [IsFiniteMeasure μ] {D : Set X} (hD : MeasurableSet D)
    (f : CompactlySupportedContinuousMap X ℝ) (_hf : ∀ x, 0 ≤ f x)
    (hfd : ∀ x, f x ≤ D.indicator 1 x) :
    (∫ x, f x ∂μ) ≤ μ.real D := by
  calc
    (∫ x, f x ∂μ) ≤ ∫ x, D.indicator 1 x ∂μ := by
      refine MeasureTheory.integral_mono f.integrable ?_ hfd
      exact IntegrableOn.integrable_indicator integrableOn_const hD
    _ = μ.real D := by
      rw [MeasureTheory.integral_indicator_one hD]

end OrderRegularityHelpers

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]

omit [TopologicalSpace X] [T2Space X] in
@[nolint unusedArguments]
lemma measureReal_lt_of_measure_lt_of_pos
    (μ : Measure X) [IsFiniteMeasure μ] {S : Set X} {ε : ℝ} (hε : 0 < ε)
    (hμε : μ S < ENNReal.ofReal ε) : μ.real S < ε := by
  rw [measureReal_def]
  have h := (ENNReal.toReal_lt_toReal (measure_ne_top μ S) ENNReal.ofReal_ne_top).2 hμε
  simpa [ENNReal.toReal_ofReal hε.le] using h

lemma cfcSpectralOperatorAux_nonneg {S : Set (spectrum ℂ U)} (hS : MeasurableSet S) :
    0 ≤ cfcSpectralOperatorAux U hU S hS := by
  simpa [cfcSpectralOperator, hS] using cfcSpectralOperator_nonneg U hU hS

lemma cfcSpectralOperatorAux_le_one {S : Set (spectrum ℂ U)} (hS : MeasurableSet S) :
    cfcSpectralOperatorAux U hU S hS ≤ 1 := by
  simpa [cfcSpectralOperator, hS] using cfcSpectralOperator_le_one U hU hS

lemma cfcSpectralOperatorAux_mono {S T : Set (spectrum ℂ U)} (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hST : S ⊆ T) :
    cfcSpectralOperatorAux U hU S hS ≤ cfcSpectralOperatorAux U hU T hT := by
  simpa [cfcSpectralOperator, hS, hT] using cfcSpectralOperator_mono U hU hS hT hST

lemma cfcRealOperator_reApplyInnerSelf
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ) (x : H) :
    (cfcRealOperator U hU f).reApplyInnerSelf x =
      ∫ z, f z ∂cfcScalarMeasure U hU x := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]
  exact (cfcScalarMeasure_integral U hU x f).symm

@[nolint unusedArguments]
lemma cfcSpectralOperator_le_cfcRealOperator_of_compact_subset_open
    {K V : Set (spectrum ℂ U)} (hK : IsCompact K) (_hV : IsOpen V) (_hKV : K ⊆ V)
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ)
    (hfK : Set.EqOn f 1 K) (_hfV : tsupport f ⊆ V) (hf : ∀ z, f z ∈ Set.Icc 0 1) :
    cfcSpectralOperator U hU K ≤ cfcRealOperator U hU f := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_def']
  refine ⟨(cfcRealOperator_isSelfAdjoint U hU f).sub
    (cfcSpectralOperator_isSelfAdjoint U hU K), fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, sub_apply,
    inner_sub_left, map_sub, inner_re_symm, ← cfcScalarMeasure_integral U hU x f]
  rw [inner_re_symm (cfcSpectralOperator U hU K x) x,
    cfcSpectralOperator_inner_self U hU hK.measurableSet x]
  simpa using sub_nonneg.mpr (measureReal_compact_le_integral_of_eqOn_one
    (cfcScalarMeasure U hU x) hK f hfK fun z => (hf z).1)

lemma cfcRealOperator_le_cfcSpectralOperator_of_support_subset
    {V : Set (spectrum ℂ U)} (hV : IsOpen V)
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ)
    (hfV : tsupport f ⊆ V) (hf : ∀ z, f z ∈ Set.Icc 0 1) :
    cfcRealOperator U hU f ≤ cfcSpectralOperator U hU V := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_def']
  refine ⟨(cfcSpectralOperator_isSelfAdjoint U hU V).sub
    (cfcRealOperator_isSelfAdjoint U hU f), fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, sub_apply,
    inner_sub_left, map_sub, inner_re_symm,
    cfcSpectralOperator_inner_self U hU hV.measurableSet x]
  rw [inner_re_symm (cfcRealOperator U hU f x) x,
    ← cfcScalarMeasure_integral U hU x f]
  simpa using sub_nonneg.mpr (integral_le_measureReal_of_support_subset
    (cfcScalarMeasure U hU x) hV f hfV hf)

lemma cfcRealOperator_mul_self
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ) :
    cfcRealOperator U hU (f * f) = cfcRealOperator U hU f * cfcRealOperator U hU f := by
  have hmul : realToComplexContinuousMap U (f * f) =
      realToComplexContinuousMap U f * realToComplexContinuousMap U f := by
    ext z
    simp [realToComplexContinuousMap_apply]
  unfold cfcRealOperator
  rw [hmul, map_mul]

lemma cfcRealOperator_sub_mul_self
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ) :
    cfcRealOperator U hU (f - f * f) =
      cfcRealOperator U hU f - cfcRealOperator U hU f * cfcRealOperator U hU f := by
  have hmul : realToComplexContinuousMap U (f * f) =
      realToComplexContinuousMap U f * realToComplexContinuousMap U f := by
    ext z
    simp [realToComplexContinuousMap_apply]
  have hsub : realToComplexContinuousMap U (f - f * f) =
      realToComplexContinuousMap U f - realToComplexContinuousMap U (f * f) := by
    ext z
    simp [realToComplexContinuousMap_apply]
  unfold cfcRealOperator
  rw [hsub, hmul, map_sub, map_mul]

lemma cfcSpectralOperator_isIdempotent_of_isCompact
    {K : Set (spectrum ℂ U)} (hK : IsCompact K) :
    IsIdempotentElem (cfcSpectralOperator U hU K) := by
  let A : H →L[ℂ] H := cfcSpectralOperator U hU K
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact cfcSpectralOperator_nonneg U hU hK.measurableSet
  have hA1 : A ≤ 1 := by
    dsimp [A]
    exact cfcSpectralOperator_le_one U hU hK.measurableSet
  have hF1 (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ)
      (hf : ∀ z, f z ∈ Set.Icc 0 1) :
      cfcRealOperator U hU f ≤ 1 := by
    calc
      cfcRealOperator U hU f ≤ cfcSpectralOperator U hU Set.univ :=
        cfcRealOperator_le_cfcSpectralOperator_of_support_subset
          U hU isOpen_univ f (Set.subset_univ _) hf
      _ = 1 := cfcSpectralOperator_univ U hU
  have hD_order (V : Set (spectrum ℂ U)) (hV : IsOpen V)
      (hKV : K ⊆ V)
      (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ)
      (hfK : Set.EqOn f 1 K) (hfV : tsupport f ⊆ V) (hf : ∀ z, f z ∈ Set.Icc 0 1) :
      0 ≤ cfcRealOperator U hU f - A ∧
        cfcRealOperator U hU f - A ≤ 1 := by
    have hAF : A ≤ cfcRealOperator U hU f := by
      dsimp [A]
      exact cfcSpectralOperator_le_cfcRealOperator_of_compact_subset_open
        U hU hK hV hKV f hfK hfV hf
    have hF0 : 0 ≤ cfcRealOperator U hU f :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
        (cfcRealOperator_nonneg U hU f (fun z => (hf z).1))
    have hFone := hF1 f hf
    constructor
    · exact sub_nonneg.mpr hAF
    · calc
        cfcRealOperator U hU f - A ≤ cfcRealOperator U hU f - 0 :=
          sub_le_sub_left hA0 _
        _ ≤ 1 := by simpa using hFone
  have hcompact : ∀ (x : H),
      (cfcSpectralOperator U hU K) (cfcSpectralOperator U hU K x) =
        cfcSpectralOperator U hU K x := by
    intro x
    apply eq_of_sub_eq_zero
    rw [← norm_eq_zero]
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (norm_nonneg _)
    let μx := cfcScalarMeasure U hU x
    let μAx := cfcScalarMeasure U hU (A x)
    let ν := μx + μAx
    let δ : ℝ := (ε / 4) ^ 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨V, hKV, hV, hνV⟩ :=
      hK.measurableSet.exists_isOpen_sdiff_lt (μ := ν)
        (measure_ne_top ν K) (ENNReal.ofReal_pos.mpr hδ).ne'
    let ug : C(spectrum ℂ U, ℝ) :=
      Classical.choose (exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV)
    have hug := Classical.choose_spec
      (exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV)
    let f0 : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ :=
      ⟨ug, hasCompactSupport_def.mpr hug.2.1⟩
    have hf0K : Set.EqOn f0 1 K := by simpa [f0, ug] using hug.1
    have hf0V : tsupport f0 ⊆ V := by simpa [f0, ug] using hug.2.2.1
    have hf0 : ∀ z, f0 z ∈ Set.Icc 0 1 := by simpa [f0, ug] using hug.2.2.2
    let F := cfcRealOperator U hU f0
    let D := F - A
    have hD0 : 0 ≤ D := by
      dsimp [D, F]
      exact (hD_order V hV hKV f0 hf0K hf0V hf0).1
    have hD1 : D ≤ 1 := by
      dsimp [D, F]
      exact (hD_order V hV hKV f0 hf0K hf0V hf0).2
    have hD_est (z : H) (hz : z = x ∨ z = A x) :
        ‖D z‖ ^ 2 ≤ (cfcScalarMeasure U hU z).real (V \ K) := by
      have hpc := norm_sq_le_inner_of_isPositive_of_le_one hD0 hD1 z
      have hupper : (∫ y, f0 y ∂cfcScalarMeasure U hU z) ≤
          (cfcScalarMeasure U hU z).real V := by
        exact integral_le_measureReal_of_support_subset
          (cfcScalarMeasure U hU z) hV f0 hf0V hf0
      have hsplit : (cfcScalarMeasure U hU z).real K +
          (cfcScalarMeasure U hU z).real (V \ K) =
          (cfcScalarMeasure U hU z).real V := by
        rw [measureReal_add_sdiff hK.measurableSet (measure_ne_top _ _)
          (measure_ne_top _ _), union_eq_right.mpr hKV]
      have hinner : RCLike.re ⟪z, D z⟫_ℂ =
          (∫ y, f0 y ∂cfcScalarMeasure U hU z) -
            (cfcScalarMeasure U hU z).real K := by
        dsimp [D, F]
        rw [sub_apply, inner_sub_right]
        change (⟪z, (cfcRealOperator U hU f0) z⟫_ℂ - ⟪z, A z⟫_ℂ).re = _
        change RCLike.re ⟪z, (cfcRealOperator U hU f0) z⟫_ℂ -
          RCLike.re ⟪z, A z⟫_ℂ = _
        rw [← cfcScalarMeasure_integral U hU z f0,
          cfcSpectralOperator_inner_self U hU hK.measurableSet z]
        norm_num
      calc
        ‖D z‖ ^ 2 ≤ RCLike.re ⟪z, D z⟫_ℂ := hpc
        _ = (∫ y, f0 y ∂cfcScalarMeasure U hU z) -
            (cfcScalarMeasure U hU z).real K := hinner
        _ ≤ (cfcScalarMeasure U hU z).real (V \ K) := by linarith
    have hD_lt (z : H) (hz : z = x ∨ z = A x) : ‖D z‖ < ε / 4 := by
      have hνlt : ν.real (V \ K) < δ :=
        measureReal_lt_of_measure_lt_of_pos ν hδ hνV.2
      have hzν : (cfcScalarMeasure U hU z).real (V \ K) ≤ ν.real (V \ K) := by
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
    let q : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ := f0 - f0 * f0
    have hq (z : spectrum ℂ U) : q z ∈ Set.Icc 0 1 := by
      dsimp [q]
      have hz := hf0 z
      constructor <;> nlinarith [hz.1, hz.2]
    have hq_ind (z : spectrum ℂ U) : q z ≤ (V \ K).indicator 1 z := by
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
    let Q := cfcRealOperator U hU q
    have hQ0 : 0 ≤ Q := by
      dsimp [Q]
      exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
        (cfcRealOperator_nonneg U hU q (fun z => (hq z).1))
    have hQ1 : Q ≤ 1 := by
      dsimp [Q]
      exact hF1 q hq
    have hQ_est : ‖Q x‖ ^ 2 ≤ μx.real (V \ K) := by
      have hpc := norm_sq_le_inner_of_isPositive_of_le_one hQ0 hQ1 x
      have hinner : RCLike.re ⟪x, Q x⟫_ℂ = ∫ z, q z ∂μx := by
        dsimp [Q, μx]
        exact (cfcScalarMeasure_integral U hU x q).symm
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
        ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
          (cfcRealOperator_nonneg U hU f0 (fun z => (hf0 z).1)))).2
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
            exact cfcRealOperator_sub_mul_self U hU f0
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

/-- **Idempotency of `cfcSpectralOperator` at a measurable set.**  The proof is deliberately
order-theoretic: first establish the compact-set case using a Urysohn function and outer
regularity, then extend to arbitrary measurable sets using inner regularity.  The estimates are
obtained from `0 ≤ A ≤ 1 ⟹ ‖A x‖² ≤ re ⟪x, A x⟫`; no weak/strong operator topology or
multiplication of limits is needed. -/
lemma cfcSpectralOperatorAux_isIdempotentElem (S : Set (spectrum ℂ U)) (hS : MeasurableSet S) :
    cfcSpectralOperatorAux U hU S hS * cfcSpectralOperatorAux U hU S hS =
      cfcSpectralOperatorAux U hU S hS := by
  let A : H →L[ℂ] H := cfcSpectralOperator U hU S
  have hA0 : 0 ≤ A := cfcSpectralOperator_nonneg U hU hS
  have hA1 : A ≤ 1 := cfcSpectralOperator_le_one U hU hS
  have hA_id : A * A = A := by
    apply ContinuousLinearMap.ext
    intro x
    apply eq_of_sub_eq_zero
    rw [← norm_eq_zero]
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (norm_nonneg _)
    let μx := cfcScalarMeasure U hU x
    let μAx := cfcScalarMeasure U hU (A x)
    let ν := μx + μAx
    let δ : ℝ := (ε / 4) ^ 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨K, hKS, hK, hνK⟩ := hS.exists_isCompact_sdiff_lt
      (measure_ne_top ν S) (ENNReal.ofReal_pos.mpr hδ).ne'
    let P : H →L[ℂ] H := cfcSpectralOperator U hU K
    have hP0 : 0 ≤ P := cfcSpectralOperator_nonneg U hU hK.measurableSet
    have hP1 : P ≤ 1 := cfcSpectralOperator_le_one U hU hK.measurableSet
    have hP_id : P * P = P := cfcSpectralOperator_isIdempotent_of_isCompact U hU hK
    have hPA : P ≤ A := by
      dsimp [P, A]
      exact cfcSpectralOperator_mono U hU hK.measurableSet hS hKS
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
        ‖D z‖ ^ 2 ≤ (cfcScalarMeasure U hU z).real (S \ K) := by
      have hpc := norm_sq_le_inner_of_isPositive_of_le_one hD0 hD1 z
      have hsplit : (cfcScalarMeasure U hU z).real K +
          (cfcScalarMeasure U hU z).real (S \ K) =
          (cfcScalarMeasure U hU z).real S := by
        rw [measureReal_add_sdiff hK.measurableSet (measure_ne_top _ _)
          (measure_ne_top _ _), union_eq_right.mpr hKS]
      have hinner : RCLike.re ⟪z, D z⟫_ℂ =
          (cfcScalarMeasure U hU z).real S -
            (cfcScalarMeasure U hU z).real K := by
        dsimp [D]
        rw [sub_apply, inner_sub_right]
        change (⟪z, A z⟫_ℂ - ⟪z, P z⟫_ℂ).re = _
        change RCLike.re ⟪z, A z⟫_ℂ - RCLike.re ⟪z, P z⟫_ℂ = _
        rw [cfcSpectralOperator_inner_self U hU hS z,
          cfcSpectralOperator_inner_self U hU hK.measurableSet z]
        norm_num
      calc
        ‖D z‖ ^ 2 ≤ RCLike.re ⟪z, D z⟫_ℂ := hpc
        _ = (cfcScalarMeasure U hU z).real S -
            (cfcScalarMeasure U hU z).real K := hinner
        _ ≤ (cfcScalarMeasure U hU z).real (S \ K) := by linarith [hsplit]
    have hD_lt (z : H) (hz : z = x ∨ z = A x) : ‖D z‖ < ε / 4 := by
      have hνlt : ν.real (S \ K) < δ :=
        measureReal_lt_of_measure_lt_of_pos ν hδ hνK
      have hzν : (cfcScalarMeasure U hU z).real (S \ K) ≤ ν.real (S \ K) := by
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
        ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
          (cfcSpectralOperator_isPositive U hU hK.measurableSet))).2 hP1
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
  simpa [A, cfcSpectralOperator, hS] using hA_id

/-! The idempotency proof above is the reusable order/regularity construction.  It first proves
the compact case with an Urysohn cutoff and outer regularity, then approximates an arbitrary
measurable set from inside by compact sets.  The only analytic estimate is the positive
contraction inequality `0 ≤ A ≤ 1 ⟹ ‖A x‖² ≤ re ⟪x, A x⟫`; no weak/strong operator topology
argument or multiplication of operator limits is involved. -/

/-- Idempotency of `cfcSpectralOperator` on every set — `0` (hence trivially idempotent) off the
measurable sets, and the order/regularity theorem above on measurable sets. -/
lemma cfcSpectralOperator_isIdempotentElem (S : Set (spectrum ℂ U)) :
    IsIdempotentElem (cfcSpectralOperator U hU S) := by
  unfold cfcSpectralOperator IsIdempotentElem
  split_ifs with hS
  · exact cfcSpectralOperatorAux_isIdempotentElem U hU S hS
  · simp

/-- `cfcSpectralOperator U hU S` is a star-projection, for every `S`; both self-adjointness and
idempotency are proved. -/
lemma cfcSpectralOperator_isStarProjection (S : Set (spectrum ℂ U)) :
    IsStarProjection (cfcSpectralOperator U hU S) :=
  ⟨cfcSpectralOperator_isIdempotentElem U hU S, cfcSpectralOperator_isSelfAdjoint U hU S⟩

/-! ## Step E: final assembly -/

/-- **The weak-operator spectral measure of a bounded normal operator.**  Assembled from the
Riesz-represented, weakly σ-additive family `cfcSpectralOperator` (Steps B–C, fully proved) and
the star-projection property (Step D), including the order/regularity proof of idempotency. -/
noncomputable def cfcSpectralMeasure : QuantumMechanics.WOTSpectralMeasure (spectrum ℂ U) H where
  toVectorMeasure := cfcSpectralVectorMeasure U hU
  isStarProjection' S := by
    show IsStarProjection (cfcSpectralMeasureFun U hU S)
    unfold cfcSpectralMeasureFun
    refine ⟨?_, ?_⟩
    · show ContinuousLinearMapWOT.ofCLM (cfcSpectralOperator U hU S) *
        ContinuousLinearMapWOT.ofCLM (cfcSpectralOperator U hU S) =
        ContinuousLinearMapWOT.ofCLM (cfcSpectralOperator U hU S)
      rw [← ContinuousLinearMapWOT.ofCLM_mul]
      exact congrArg ContinuousLinearMapWOT.ofCLM (cfcSpectralOperator_isIdempotentElem U hU S)
    · apply ContinuousLinearMapWOT.toCLM_injective
      change star (cfcSpectralOperator U hU S) = cfcSpectralOperator U hU S
      exact cfcSpectralOperator_isSelfAdjoint U hU S
  univ' := by
    show cfcSpectralMeasureFun U hU Set.univ = 1
    unfold cfcSpectralMeasureFun
    rw [cfcSpectralOperator_univ, ContinuousLinearMapWOT.ofCLM_one]

@[simp]
lemma cfcSpectralMeasure_apply (S : Set (spectrum ℂ U)) :
    cfcSpectralMeasure U hU S = cfcSpectralMeasureFun U hU S := rfl

/-- The scalar measure attached to `cfcSpectralMeasure` is exactly the polarized Riesz measure it
was built from. -/
lemma cfcSpectralMeasure_scalarMeasure (x y : H) :
    (cfcSpectralMeasure U hU).scalarMeasure x y = polarizedCfcScalarMeasure (hU := hU) U x y := by
  apply MeasureTheory.VectorMeasure.ext
  intro S _
  rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply, cfcSpectralMeasure_apply]
  exact cfcSpectralMeasureFun_inner U hU S x y

/-- **Reconstruction**: `cfcSpectralMeasure` genuinely is the spectral measure of `U` in the
weak sense — its weak integral against any continuous test function reproduces the continuous
functional calculus applied to `U`. -/
theorem cfcSpectralMeasure_reconstruction
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ) (x y : H) :
    (cfcSpectralMeasure U hU).complexWeakIntegral (fun z => (f z : ℂ)) x y =
      ⟪y, cfcRealOperator U hU f x⟫_ℂ := by
  unfold QuantumMechanics.WOTSpectralMeasure.complexWeakIntegral
  rw [cfcSpectralMeasure_scalarMeasure]
  exact polarizedCfcScalarMeasure_complexIntegral_eq_inner U hU f x y

/-! ## Step F: commutation with the commutant of `U`

Everything above builds `cfcSpectralMeasure` as the genuine Borel/PVM spectral measure of the
normal operator `U`.  This section shows that every spectral projection commutes with anything
that commutes with `U` (and its adjoint) — the fact needed to run Schur's lemma with genuine
spectral (rather than merely continuous-functional-calculus) projections.  The key input is
Mathlib's `Commute.cfcHom`, which gives commutation with `cfcHom hU g` for every *continuous*
`g`; the commutation is transported to arbitrary measurable sets via the Riesz–Markov measure
uniqueness already used throughout this file
(`MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported`), using that a unitary
intertwiner preserves the defining vector-state functional. -/

/-- An operator commuting with `U` and `star U` commutes with the continuous functional calculus
of `U` at every real test function. -/
lemma commute_cfcRealOperator {T : H →L[ℂ] H} (hTU : Commute U T) (hTU' : Commute (star U) T)
    (f : CompactlySupportedContinuousMap (spectrum ℂ U) ℝ) :
    Commute (cfcRealOperator U hU f) T :=
  hTU.cfcHom hU hTU' (realToComplexContinuousMap U f)

/-- If `T` is an isometry (`star T * T = 1`) commuting with `U` and `star U`, the vector-state
Riesz measure at `T v` agrees with the one at `v`: an isometric intertwiner of `U` leaves the
diagonal spectral measure unchanged. -/
lemma cfcScalarMeasure_eq_of_commute_isometry
    {T : H →L[ℂ] H} (hTU : Commute U T) (hTU' : Commute (star U) T)
    (hTiso : star T * T = 1) (v : H) :
    cfcScalarMeasure U hU (T v) = cfcScalarMeasure U hU v := by
  apply MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [cfcScalarMeasure_integral, cfcScalarMeasure_integral]
  have hcomm : cfcRealOperator U hU f * T = T * cfcRealOperator U hU f :=
    commute_cfcRealOperator U hU hTU hTU' f
  have hcommv : cfcRealOperator U hU f (T v) = T (cfcRealOperator U hU f v) := by
    have h := congrArg (fun A : H →L[ℂ] H => A v) hcomm
    simpa using h
  rw [hcommv]
  have hTT : ⟪T v, T (cfcRealOperator U hU f v)⟫_ℂ = ⟪v, cfcRealOperator U hU f v⟫_ℂ := by
    have h := ContinuousLinearMap.adjoint_inner_right T v (T (cfcRealOperator U hU f v))
    rw [← h, ← ContinuousLinearMap.star_eq_adjoint]
    have hw : star T (T (cfcRealOperator U hU f v)) = cfcRealOperator U hU f v := by
      have := congrArg (fun A : H →L[ℂ] H => A (cfcRealOperator U hU f v)) hTiso
      simpa using this
    rw [hw]
  rw [hTT]

/-- If `T` is unitary and commutes with `U` and `star U`, the polarized Riesz measure intertwines:
testing at `(T x, y)` matches testing at `(x, star T y)`.  This is the sesquilinear form of the
commutation identity, and is exactly what `cfcSpectralOperator_inner` needs to see commutation of
each spectral projection with `T`. -/
lemma polarizedCfcScalarMeasure_eq_of_commute_unitary
    {T : H →L[ℂ] H} (hTU : Commute U T) (hTU' : Commute (star U) T)
    (hTunit : T ∈ unitary (H →L[ℂ] H)) (x y : H) :
    polarizedCfcScalarMeasure (hU := hU) U (T x) y =
      polarizedCfcScalarMeasure (hU := hU) U x (star T y) := by
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
  rw [polarizedCfcScalarMeasure_apply U hU hS, polarizedCfcScalarMeasure_apply U hU hS,
    hTxw, hTxw', hTxIw, hTxIw',
    cfcScalarMeasure_eq_of_commute_isometry U hU hTU hTU' hTT (x + w),
    cfcScalarMeasure_eq_of_commute_isometry U hU hTU hTU' hTT (x - w),
    cfcScalarMeasure_eq_of_commute_isometry U hU hTU hTU' hTT (x + Complex.I • w),
    cfcScalarMeasure_eq_of_commute_isometry U hU hTU hTU' hTT (x - Complex.I • w)]

/-- Every spectral operator `cfcSpectralOperator U hU S` commutes with any unitary intertwiner of
`U` (i.e. any unitary commuting with both `U` and `star U`).  Holds for *every* `S`, measurable or
not, since `cfcSpectralOperator_inner` itself needs no measurability hypothesis. -/
lemma cfcSpectralOperator_commute_of_commute_unitary
    {T : H →L[ℂ] H} (hTU : Commute U T) (hTU' : Commute (star U) T)
    (hTunit : T ∈ unitary (H →L[ℂ] H)) (S : Set (spectrum ℂ U)) :
    cfcSpectralOperator U hU S * T = T * cfcSpectralOperator U hU S := by
  ext v
  apply ext_inner_left ℂ
  intro y
  show ⟪y, (cfcSpectralOperator U hU S * T) v⟫_ℂ = ⟪y, (T * cfcSpectralOperator U hU S) v⟫_ℂ
  rw [show (cfcSpectralOperator U hU S * T) v = cfcSpectralOperator U hU S (T v) from rfl,
    show (T * cfcSpectralOperator U hU S) v = T (cfcSpectralOperator U hU S v) from rfl,
    cfcSpectralOperator_inner U hU S (T v) y,
    polarizedCfcScalarMeasure_eq_of_commute_unitary U hU hTU hTU' hTunit v y,
    ← cfcSpectralOperator_inner U hU S v (star T y),
    ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left T (cfcSpectralOperator U hU S v) y

/-- The weak-operator spectral measure `cfcSpectralMeasure U hU` commutes with any unitary
intertwiner of `U`, at every set (measurable or not). -/
lemma cfcSpectralMeasure_commute_of_commute_unitary
    {T : H →L[ℂ] H} (hTU : Commute U T) (hTU' : Commute (star U) T)
    (hTunit : T ∈ unitary (H →L[ℂ] H)) (S : Set (spectrum ℂ U)) :
    cfcSpectralMeasure U hU S * ContinuousLinearMapWOT.ofCLM T =
      ContinuousLinearMapWOT.ofCLM T * cfcSpectralMeasure U hU S := by
  rw [cfcSpectralMeasure_apply]
  show ContinuousLinearMapWOT.ofCLM (cfcSpectralOperator U hU S) *
      ContinuousLinearMapWOT.ofCLM T =
    ContinuousLinearMapWOT.ofCLM T * ContinuousLinearMapWOT.ofCLM (cfcSpectralOperator U hU S)
  rw [← ContinuousLinearMapWOT.ofCLM_mul, ← ContinuousLinearMapWOT.ofCLM_mul]
  exact congrArg ContinuousLinearMapWOT.ofCLM
    (cfcSpectralOperator_commute_of_commute_unitary U hU hTU hTU' hTunit S)

end CFCScalar

end QuantumMechanics

end
