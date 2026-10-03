/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.MeasureTheory.LiftingAndConditioning
public import PhyslibAlpha.Mathematics.Convex.Choquet.RepresentingMeasure
public import PhyslibAlpha.Mathematics.MeasureTheory.IntegrationFunctional

/-!
# Every point is a mixture of extreme points

Choquet's theorem: each point of a metrizable compact convex set is a mixture of extreme points.

## i. Overview

Let `S` be a compact convex set that is metrizable and whose points are separated by countably many
continuous linear functionals. Every point of `S` is a mixture of extreme points: it has a
representing probability measure that lives on the extreme points. This is Choquet's theorem. For
states it says that every state is a mixture of pure states.

The measure is any maximal representing measure in the Choquet order. Suppose it gave positive
weight to the points that are not extreme. Each of them is the midpoint of two different points.
Moving the weight from the midpoints out to these endpoints would give a strictly higher measure. To
make this precise, the midpoints are grouped by the distance of their endpoints, and each group is a
closed set.

## ii. Key results

- `Choquet.measurableSet_extremePoints` proves that the extreme points form a Borel set.
- `Choquet.maximal_ae_mem_extremePoints` proves that maximal representing measures live on the
  extreme points.
- `Choquet.exists_extreme_representingMeasure` proves Choquet's theorem.

## iii. Table of contents

- A. The extreme points are Borel
- B. Splitting mass between endpoints
- C. The boundary theorem

## iv. References

* None.

-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace Choquet

/-!

## A. The extreme points are Borel

-/

section Metric

variable {V : Type*} [TopologicalSpace V] {S : Set V} [TopologicalSpace.MetrizableSpace S]

set_option warn.classDefReducibility false in
/-- A metric inducing the topology of `S`. -/
noncomputable def choquetMetric : MetricSpace S := TopologicalSpace.metrizableSpaceMetric S

/-- The distance of `choquetMetric`. -/
noncomputable def cdist (x y : S) : ℝ :=
  @Dist.dist S choquetMetric.toPseudoMetricSpace.toDist x y

lemma cdist_pos {x y : S} (h : x ≠ y) : 0 < cdist x y :=
  (@_root_.dist_pos S choquetMetric x y).mpr h

lemma continuous_cdist : Continuous (fun p : S × S => cdist p.1 p.2) :=
  @continuous_dist S choquetMetric.toPseudoMetricSpace

lemma ne_of_one_div_le_cdist {n : ℕ} {x y : S} (h : 1 / (n + 1 : ℝ) ≤ cdist x y) : x ≠ y := by
  rintro rfl
  rw [cdist, @_root_.dist_self S choquetMetric.toPseudoMetricSpace] at h
  linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := n)]

lemma isCompact_decompositionSet [CompactSpace S] (n : ℕ) :
    IsCompact {p : S × S | 1 / (n + 1 : ℝ) ≤ cdist p.1 p.2} :=
  (isClosed_le continuous_const continuous_cdist).isCompact

/-- The pairs of points at distance at least `1 / (n + 1)`. -/
noncomputable abbrev decompositionSpace (n : ℕ) := {p : S × S // 1 / (n + 1 : ℝ) ≤ cdist p.1 p.2}

instance [CompactSpace S] (n : ℕ) : CompactSpace (decompositionSpace (S := S) n) :=
  isCompact_iff_compactSpace.mp (isCompact_decompositionSet n)

lemma continuous_fst_decomposition (n : ℕ) :
    Continuous fun p : decompositionSpace (S := S) n => p.1.1 :=
  continuous_fst.comp continuous_subtype_val

lemma continuous_snd_decomposition (n : ℕ) :
    Continuous fun p : decompositionSpace (S := S) n => p.1.2 :=
  continuous_snd.comp continuous_subtype_val

end Metric

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] {S : Set V} (hS : Convex ℝ S) [CompactSpace S] [T2Space S]
  [MeasurableSpace S] [BorelSpace S] [TopologicalSpace.MetrizableSpace S]

/-- The midpoints of pairs of points at distance at least `1 / (n + 1)`. -/
noncomputable def nontrivialMixSet (n : ℕ) : Set S :=
  mixHalf hS '' {p : S × S | 1 / (n + 1 : ℝ) ≤ cdist p.1 p.2}

omit [MeasurableSpace ↑S] [BorelSpace ↑S] in
lemma isClosed_nontrivialMixSet (n : ℕ) : IsClosed (nontrivialMixSet hS n) :=
  ((isCompact_decompositionSet n).image (continuous_mixHalf hS)).isClosed

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [CompactSpace ↑S] [T2Space ↑S]
  [MeasurableSpace ↑S] [BorelSpace ↑S] in
/-- The non-extreme points are the union of the sets `nontrivialMixSet n`. -/
lemma setOf_notMem_extremePoints_eq :
    {x : S | (x : V) ∉ S.extremePoints ℝ} = ⋃ n, nontrivialMixSet hS n := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · intro hx
    obtain ⟨p, q, hpq, rfl⟩ := exists_mixHalf_eq_of_notMem_extremePoints hS hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (cdist_pos hpq)
    exact ⟨n, (p, q), hn.le, rfl⟩
  · rintro ⟨n, ⟨p, q⟩, hd, rfl⟩
    exact mixHalf_notMem_extremePoints hS (ne_of_one_div_le_cdist hd)

include hS in
/-- The extreme points form a Borel set. -/
lemma measurableSet_extremePoints : MeasurableSet {x : S | (x : V) ∈ S.extremePoints ℝ} := by
  have := (MeasurableSet.iUnion fun n => (isClosed_nontrivialMixSet hS n).measurableSet).compl
  simpa only [← setOf_notMem_extremePoints_eq hS, compl_ofPred, not_not] using this

/-!

## B. Splitting mass between endpoints

-/

/-- The midpoint of a pair in `decompositionSpace (S := S) n`. -/
noncomputable def decompositionMidpoint (n : ℕ) (p : decompositionSpace (S := S) n) : S :=
  mixHalf hS p.1

omit [CompactSpace ↑S] [T2Space ↑S] [MeasurableSpace ↑S] [BorelSpace ↑S] in
lemma continuous_decompositionMidpoint (n : ℕ) : Continuous (decompositionMidpoint hS n) :=
  (continuous_mixHalf hS).comp continuous_subtype_val

/-- The conditional law on `nontrivialMixSet n` is the pushforward of a law on
`decompositionSpace (S := S) n` under the midpoint map. -/
lemma exists_decomposition_lift (mu : ProbabilityMeasure S) (n : ℕ)
    (hpos : (mu : Measure S) (nontrivialMixSet hS n) ≠ 0) :
    ∃ rho : ProbabilityMeasure (decompositionSpace (S := S) n),
      rho.map (decompositionMidpoint hS n) =
        ProbabilityMeasure.condition mu (nontrivialMixSet hS n) hpos :=
  ProbabilityMeasure.exists_map_eq_of_continuous_of_compl_range_null _
    (continuous_decompositionMidpoint hS n) _ <| by
      rw [show range (decompositionMidpoint hS n) = nontrivialMixSet hS n from
        (image_eq_range _ _).symm]
      exact ProbabilityMeasure.condition_compl_apply mu
        (isClosed_nontrivialMixSet hS n).measurableSet hpos

omit [AddCommGroup V] [Module ℝ V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space ↑S] in
lemma integrable_comp_decomposition {n : ℕ}
    (rho : ProbabilityMeasure (decompositionSpace (S := S) n)) (f : C(S, ℝ))
    {g : decompositionSpace (S := S) n → S} (hg : Continuous g) :
    Integrable (fun p => f (g p)) (rho : Measure _) :=
  (f.continuous.comp hg).integrable_of_hasCompactSupport (.of_compactSpace _)

omit [T2Space ↑S] in
lemma integral_eq_integral_decompositionMidpoint {n : ℕ}
    {rho : ProbabilityMeasure (decompositionSpace (S := S) n)} {nu : ProbabilityMeasure S}
    (h : rho.map (decompositionMidpoint hS n) = nu) (f : C(S, ℝ)) :
    ∫ w, f w ∂(nu : Measure S) = ∫ p, f (decompositionMidpoint hS n p) ∂(rho : Measure _) := by
  rw [← h, ProbabilityMeasure.toMeasure_map, integral_map
    (continuous_decompositionMidpoint hS n).measurable.aemeasurable
    f.continuous.aestronglyMeasurable]

/-- The law on `S` putting half the mass of `rho` on first points and half on second points. -/
noncomputable def endpointMeasure (n : ℕ)
    (rho : ProbabilityMeasure (decompositionSpace (S := S) n)) : ProbabilityMeasure S :=
  ProbabilityMeasure.averageMap rho (fun p => p.1.1) (fun p => p.1.2)
    (continuous_fst_decomposition n).measurable.aemeasurable
    (continuous_snd_decomposition n).measurable.aemeasurable

omit [AddCommGroup V] [Module ℝ V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space ↑S] in
lemma integral_endpointMeasure (n : ℕ)
    (rho : ProbabilityMeasure (decompositionSpace (S := S) n)) (f : C(S, ℝ)) :
    ∫ w, f w ∂(endpointMeasure n rho : Measure _) =
      ∫ p : decompositionSpace (S := S) n, (1 / 2 * f p.1.1 + 1 / 2 * f p.1.2)
        ∂(rho : Measure _) := by
  rw [endpointMeasure, ProbabilityMeasure.integral_averageMap _ _
    (integrable_continuousMap (_ : Measure _) f) (integrable_continuousMap (_ : Measure _) f),
    integral_add
      ((integrable_comp_decomposition rho f (continuous_fst_decomposition n)).const_mul _)
      ((integrable_comp_decomposition rho f (continuous_snd_decomposition n)).const_mul _),
    integral_const_mul, integral_const_mul]

omit [T2Space ↑S] in
/-- The conditional law on `nontrivialMixSet n` lies below the endpoint law in the Choquet
order. -/
lemma condition_choquetLE_endpointMeasure (mu : ProbabilityMeasure S) (n : ℕ)
    (hpos : (mu : Measure S) (nontrivialMixSet hS n) ≠ 0)
    (rho : ProbabilityMeasure (decompositionSpace (S := S) n))
    (hrho : rho.map (decompositionMidpoint hS n) =
      ProbabilityMeasure.condition mu (nontrivialMixSet hS n) hpos) :
    ChoquetLE hS (ProbabilityMeasure.condition mu (nontrivialMixSet hS n) hpos)
      (endpointMeasure n rho) := fun f hf => by
  rw [integral_eq_integral_decompositionMidpoint hS hrho f, integral_endpointMeasure]
  refine integral_mono
    (integrable_comp_decomposition rho f (continuous_decompositionMidpoint hS n))
    (((integrable_comp_decomposition rho f (continuous_fst_decomposition n)).const_mul _).add
      ((integrable_comp_decomposition rho f (continuous_snd_decomposition n)).const_mul _))
    fun p => (hf p.1.1 p.1.2 half).trans_eq ?_
  norm_num

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space ↑S]
  [TopologicalSpace.MetrizableSpace ↑S] in
/-- Replacing the mass on `T` by a law above the conditional law on `T` moves up the Choquet
order. -/
lemma choquetLE_replacePart (mu eta : ProbabilityMeasure S) (T : Set S) (hT : MeasurableSet T)
    (hpos : (mu : Measure S) T ≠ 0)
    (hle : ChoquetLE hS (ProbabilityMeasure.condition mu T hpos) eta) :
    ChoquetLE hS mu (ProbabilityMeasure.replacePart mu eta T hT) := fun f hf => by
  rw [ProbabilityMeasure.integral_eq_restrict_compl_add_condition mu hT hpos
      (integrable_continuousMap (mu : Measure _) f),
      ProbabilityMeasure.integral_replacePart mu eta T hT
      (integrable_continuousMap (mu : Measure _) f) (integrable_continuousMap (eta : Measure _) f)]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hle f hf) ENNReal.toReal_nonneg)

omit [AddCommGroup V] [Module ℝ V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space ↑S]
  [TopologicalSpace.MetrizableSpace ↑S] in
/-- Replacing the mass on `T` by a law with strictly larger integral than the conditional law on
`T` strictly raises the integral. -/
lemma integral_lt_replacePart (mu eta : ProbabilityMeasure S) (T : Set S) (hT : MeasurableSet T)
    (hpos : (mu : Measure S) T ≠ 0) (f : C(S, ℝ))
    (hlt : ∫ w, f w ∂(ProbabilityMeasure.condition mu T hpos : Measure S) <
      ∫ w, f w ∂(eta : Measure S)) :
    ∫ w, f w ∂(mu : Measure S) <
      ∫ w, f w ∂(ProbabilityMeasure.replacePart mu eta T hT : Measure S) := by
  rw [ProbabilityMeasure.integral_eq_restrict_compl_add_condition mu hT hpos
      (integrable_continuousMap (mu : Measure _) f),
      ProbabilityMeasure.integral_replacePart mu eta T hT
      (integrable_continuousMap (mu : Measure _) f) (integrable_continuousMap (eta : Measure _) f)]
  exact add_lt_add_of_le_of_lt le_rfl
    (mul_lt_mul_of_pos_left hlt (ENNReal.toReal_pos hpos (measure_ne_top _ _)))

/-- The square of a continuous linear functional, on `S`. -/
noncomputable def squaredEvaluation (ℓ : V →L[ℝ] ℝ) : C(S, ℝ) :=
  ⟨fun x => ℓ x ^ 2, (ℓ.continuous.comp continuous_subtype_val).pow 2⟩

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [CompactSpace ↑S] [T2Space ↑S]
  [MeasurableSpace ↑S] [BorelSpace ↑S] [TopologicalSpace.MetrizableSpace ↑S] in
lemma isConvexFunction_squaredEvaluation (ℓ : V →L[ℝ] ℝ) :
    IsConvexFunction hS (squaredEvaluation ℓ) := fun x y t => by
  change ℓ (mix hS x y t) ^ 2 ≤ (t : ℝ) * ℓ x ^ 2 + (1 - (t : ℝ)) * ℓ y ^ 2
  simp only [coe_mix, map_add, map_smul, smul_eq_mul]
  nlinarith [mul_nonneg (mul_nonneg t.2.1 (sub_nonneg.mpr t.2.2)) (sq_nonneg (ℓ x - ℓ y))]

variable (ℓ : ℕ → V →L[ℝ] ℝ) (hℓ : ∀ x y : S, (∀ i, ℓ i x = ℓ i y) → x = y)
include hℓ

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [CompactSpace ↑S] [T2Space ↑S] [BorelSpace ↑S]
  in
/-- Some functional of the sequence tells the two points of a pair apart with positive
probability. -/
lemma exists_index_positive_separation (n : ℕ)
    (rho : ProbabilityMeasure (decompositionSpace (S := S) n)) :
    ∃ i, (rho : Measure _) {p : decompositionSpace (S := S) n | ℓ i p.1.1 ≠ ℓ i p.1.2} ≠ 0 := by
  by_contra! h
  have hA : ⋃ i, {p : decompositionSpace (S := S) n | ℓ i p.1.1 ≠ ℓ i p.1.2} = univ :=
    eq_univ_of_forall fun p => mem_iUnion.mpr (not_forall.mp fun h' =>
      ne_of_one_div_le_cdist p.2 (hℓ _ _ h'))
  have := measure_iUnion_null h
  rw [hA, measure_univ] at this
  exact one_ne_zero this

omit [T2Space ↑S] in
/-- Splitting the mass of `rho` between endpoints strictly raises the integral of some squared
functional of the sequence. -/
lemma exists_squaredEvaluation_strict (n : ℕ)
    (rho : ProbabilityMeasure (decompositionSpace (S := S) n)) :
    ∃ i, ∫ p, squaredEvaluation (S := S) (ℓ i) (decompositionMidpoint hS n p) ∂(rho : Measure _) <
      ∫ w, squaredEvaluation (S := S) (ℓ i) w ∂(endpointMeasure n rho : Measure _) := by
  obtain ⟨i, hi⟩ := exists_index_positive_separation ℓ hℓ n rho
  refine ⟨i, ?_⟩
  have hgap (p : decompositionSpace (S := S) n) : 1 / 2 * squaredEvaluation (S := S) (ℓ i) p.1.1 +
      1 / 2 * squaredEvaluation (S := S) (ℓ i) p.1.2 =
        squaredEvaluation (S := S) (ℓ i) (decompositionMidpoint hS n p) +
          (ℓ i p.1.1 - ℓ i p.1.2) ^ 2 / 4 := by
    simp only [squaredEvaluation, ContinuousMap.coe_mk, decompositionMidpoint, mixHalf, coe_mix,
      half_coe, map_add, map_smul, smul_eq_mul]
    ring
  have hLR : Integrable (fun p : decompositionSpace (S := S) n =>
      1 / 2 * squaredEvaluation (S := S) (ℓ i) p.1.1 +
        1 / 2 * squaredEvaluation (S := S) (ℓ i) p.1.2) (rho : Measure _) :=
    ((integrable_comp_decomposition rho (squaredEvaluation (S := S) (ℓ i))
    (continuous_fst_decomposition n)).const_mul (1 / 2)).add
    ((integrable_comp_decomposition rho (squaredEvaluation (S := S) (ℓ i))
      (continuous_snd_decomposition n)).const_mul (1 / 2))
  have hM := integrable_comp_decomposition rho (squaredEvaluation (S := S) (ℓ i))
    (continuous_decompositionMidpoint hS n)
  rw [integral_endpointMeasure, ← sub_pos, ← integral_sub hLR hM]
  refine (integral_pos_iff_support_of_nonneg_ae (.of_forall fun p => ?_) (hLR.sub hM)).2
    (pos_iff_ne_zero.2 (mt (measure_mono_null fun p hp => ?_) hi))
  · simp only [Pi.zero_apply, Pi.sub_apply, hgap, add_sub_cancel_left]
    positivity
  · simp only [Function.mem_support, Pi.sub_apply, hgap, add_sub_cancel_left]
    exact div_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hp)) four_ne_zero

/-!

## C. The boundary theorem

-/

/-- A Choquet-maximal measure gives `nontrivialMixSet n` no mass. -/
lemma maximal_nontrivialMixSet_null {x : S} {mu : ProbabilityMeasure S}
    (hmu : IsChoquetMaximalAt hS x mu) (n : ℕ) :
    (mu : Measure S) (nontrivialMixSet hS n) = 0 := by
  have hT := (isClosed_nontrivialMixSet hS n).measurableSet
  by_contra hpos
  obtain ⟨rho, hrho⟩ := exists_decomposition_lift hS mu n hpos
  have hle := choquetLE_replacePart hS mu _ _ hT hpos
    (condition_choquetLE_endpointMeasure hS mu n hpos rho hrho)
  have hrev := hmu.2 _ (ChoquetLE.isRepresentingMeasure hS hmu.1 hle) hle
  obtain ⟨i, hi⟩ := exists_squaredEvaluation_strict hS ℓ hℓ n rho
  exact (hrev _ (isConvexFunction_squaredEvaluation hS (ℓ i))).not_gt <| integral_lt_replacePart
    mu _ _ hT hpos _ ((integral_eq_integral_decompositionMidpoint hS hrho _).trans_lt hi)

/-- A Choquet-maximal measure is concentrated on the extreme points. -/
lemma maximal_ae_mem_extremePoints {x : S} {mu : ProbabilityMeasure S}
    (hmu : IsChoquetMaximalAt hS x mu) :
    ∀ᵐ y : S ∂(mu : Measure S), (y : V) ∈ S.extremePoints ℝ := by
  rw [ae_iff, setOf_notMem_extremePoints_eq hS]
  exact measure_iUnion_null fun n => maximal_nontrivialMixSet_null hS ℓ hℓ hmu n

include hS in
/-- **The Choquet boundary theorem.** Every point has a representing probability measure
concentrated on the extreme points. -/
lemma exists_extreme_representingMeasure (x : S) :
    ∃ mu : ProbabilityMeasure S,
      IsRepresentingMeasure x mu ∧ ∀ᵐ y : S ∂(mu : Measure S), (y : V) ∈ S.extremePoints ℝ :=
  let ⟨mu, hmax⟩ := exists_isChoquetMaximalAt hS x
  ⟨mu, hmax.1, maximal_ae_mem_extremePoints hS ℓ hℓ hmax⟩

end Choquet
