/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Classical.EnsembleRefinement
public import PhyslibAlpha.Mathematics.MeasureTheory.IntegrationFunctional
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Uniqueness of pure decompositions

Choquet–Meyer uniqueness: when ensembles refine, pure decompositions are unique.

## i. Overview

When ensembles refine, every state has at most one pure decomposition. This is the uniqueness half
of the Choquet–Meyer theorem.

A measure on the pure states is fixed by the averages it gives to continuous functions. We test it
on special functions: the largest of finitely many expectation values, `ω ↦ max (ω A₁) … (ω Aₙ)`.
Every pure decomposition of a state `ω` averages this function to the same number, the upper
envelope of `A₁, …, Aₙ` at `ω`. To see this, cut the pure states into small pieces on each of which
one `Aᵢ` is nearly the largest, and glue the pieces with refinement. These test functions and their
differences are dense among all continuous functions, so two pure decompositions of the same state
agree.

## ii. Key results

- `StateSpace.maxApply` is the largest expectation value of a state on finitely many observables.
- `PureState.integral_maxApply_eq` proves that, when ensembles refine, a pure decomposition averages
  the largest value to the upper envelope.
- `EnsemblesRefine.eq_of_toPositive_eq` proves that two measures on the pure states giving the same
  positive functional are equal. This is **Choquet–Meyer uniqueness**.
- `EnsemblesRefine.hasUniquePureDecomposition` proves that, when ensembles refine, a pure
  decomposition is unique.

## iii. Table of contents

- A. The largest value on a finite family
- B. Integrating the largest value
- C. Integrating the largest value when ensembles refine
- D. Density of largest values
- E. Uniqueness
- F. Unique pure decompositions

## iv. References

- G. Choquet and P.-A. Meyer, *Existence et unicité des représentations intégrales dans les
  convexes compacts quelconques*, Ann. Inst. Fourier 13 (1963), 139–154.
- E. M. Alfsen, *Compact Convex Sets and Boundary Integrals*, Springer, 1971, ch. II.3.

-/

@[expose] public section

namespace ProbabilisticTheory

open MeasureTheory PositiveLinearMap PureState Set ArchimedeanOrderUnitSpace
open scoped ENNReal

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

/-!

## A. The largest value on a finite family

-/

section PureEnvelope

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- At a pure state, the upper envelope of a family is at most its largest value on the family. -/
lemma UnitalPositiveLinearMap.IsPure.upperEnvelope_le {e : 𝓢[ℝ, E]} (he : e.IsPure) (s : ι → E)
    {M : ℝ} (hM : ∀ i, e (s i) ≤ M) : upperEnvelope s e.toPositiveLinearMap ≤ M := by
  obtain ⟨ψ, hψ, hU⟩ := exists_sum_eq_upperEnvelope s e.toPositiveLinearMap
  have h1 : ∑ i, ψ i 1 = 1 := by
    rw [← sum_apply, hψ]
    exact map_one e
  rw [← hU]
  calc ∑ i, ψ i (s i) = ∑ i, ψ i 1 * e (s i) :=
        Finset.sum_congr rfl fun i _ => he.apply_eq_of_le (hψ ▸ le_sum ψ (Finset.mem_univ i)) _
    _ ≤ ∑ i, ψ i 1 * M := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hM i) (map_nonneg _ OrderUnitSpace.one_nonneg)
    _ = M := by rw [← Finset.sum_mul, h1, one_mul]

end PureEnvelope

namespace StateSpace

variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]

/-- The largest value of a state on a finite family of observables. -/
noncomputable def maxApply (s : ι → E) : C(stateSpace E, ℝ) :=
  Finset.univ.sup' Finset.univ_nonempty fun i => ⟨fun ω => toState ω (s i), continuous_apply _⟩

lemma maxApply_apply (s : ι → E) (ω : stateSpace E) :
    maxApply s ω = Finset.univ.sup' Finset.univ_nonempty fun i => toState ω (s i) :=
  ContinuousMap.sup'_apply _ _ _

lemma apply_le_maxApply (s : ι → E) (ω : stateSpace E) (i : ι) :
    toState ω (s i) ≤ maxApply s ω := by
  rw [maxApply_apply]
  exact Finset.le_sup' (fun i => toState ω (s i)) (Finset.mem_univ i)

lemma maxApply_le_of_forall {s : ι → E} {ω : stateSpace E} {r : ℝ}
    (h : ∀ i, toState ω (s i) ≤ r) : maxApply s ω ≤ r := by
  rw [maxApply_apply]
  exact Finset.sup'_le _ _ fun i _ => h i

lemma exists_eq_maxApply (s : ι → E) (ω : stateSpace E) : ∃ i, maxApply s ω = toState ω (s i) :=
  let ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun i => toState ω (s i)
  ⟨i, (maxApply_apply s ω).trans hi⟩

lemma maxApply_le {s : ι → E} {b : E} (hb : b ∈ upperBounds (range s)) (ω : stateSpace E) :
    maxApply s ω ≤ toState ω b :=
  maxApply_le_of_forall fun i => OrderHomClass.mono (toState ω) (hb ⟨i, rfl⟩)

lemma abs_maxApply_le (s : ι → E) (ω : stateSpace E) :
    |maxApply s ω| ≤ ∑ i, orderUnitNorm (s i) := by
  obtain ⟨i, hi⟩ := exists_eq_maxApply s ω
  rw [hi]
  exact (UnitalPositiveLinearMap.abs_apply_le_orderUnitNorm _ _).trans
    (Finset.single_le_sum (fun j _ => orderUnitNorm_nonneg (s j)) (Finset.mem_univ i))

lemma maxApply_unit (a : E) (ω : stateSpace E) : maxApply (fun _ : Unit => a) ω = toState ω a :=
  le_antisymm (maxApply_le_of_forall fun _ => le_rfl) (apply_le_maxApply (fun _ : Unit => a) ω ())

lemma maxApply_sumElim (s : ι → E) (t : κ → E) :
    maxApply (Sum.elim s t) = maxApply s ⊔ maxApply t := by
  ext ω
  rw [ContinuousMap.sup_apply]
  refine le_antisymm (maxApply_le_of_forall ?_) (sup_le (maxApply_le_of_forall fun i => ?_)
    (maxApply_le_of_forall fun i => ?_))
  · rintro (i | i)
    exacts [le_sup_of_le_left (apply_le_maxApply s ω i),
      le_sup_of_le_right (apply_le_maxApply t ω i)]
  exacts [apply_le_maxApply (Sum.elim s t) ω (.inl i), apply_le_maxApply (Sum.elim s t) ω (.inr i)]

lemma maxApply_add (s : ι → E) (t : κ → E) :
    maxApply (fun p : ι × κ => s p.1 + t p.2) = maxApply s + maxApply t := by
  ext ω
  rw [ContinuousMap.add_apply]
  refine le_antisymm (maxApply_le_of_forall fun p => ?_) ?_
  · rw [map_add]
    exact add_le_add (apply_le_maxApply s ω p.1) (apply_le_maxApply t ω p.2)
  · obtain ⟨i, hi⟩ := exists_eq_maxApply s ω
    obtain ⟨j, hj⟩ := exists_eq_maxApply t ω
    rw [hi, hj, ← map_add]
    exact apply_le_maxApply (fun p : ι × κ => s p.1 + t p.2) ω (i, j)

end StateSpace

open StateSpace

/-!

## B. Integrating the largest value

-/

namespace PureState

variable {ι : Type*} [Fintype ι] [Nonempty ι] (μ : Measure (PureState E)) [IsFiniteMeasure μ]
  (s : ι → E)

lemma integrable_maxApply : Integrable (fun k : PureState E => maxApply s k.1) μ :=
  .of_bound ((maxApply s).continuous.comp continuous_subtype_val).aestronglyMeasurable _
    (.of_forall fun k => (Real.norm_eq_abs _).trans_le (abs_maxApply_le s k.1))

/-- Integrating the largest value on a family stays below the upper envelope. -/
lemma integral_maxApply_le : ∫ k, maxApply s k.1 ∂μ ≤ upperEnvelope s (toPositive μ) :=
  le_upperEnvelope fun b hb =>
    integral_mono (integrable_maxApply μ s) (PureState.integrable μ b) fun k => maxApply_le hb k.1

lemma toPositive_restrict_univ : toPositive (μ.restrict univ) = toPositive μ :=
  PositiveLinearMap.ext fun _ => setIntegral_univ

lemma toPositive_restrict_inter_add_sdiff (A : Set (PureState E)) {W : Set (PureState E)}
    (hW : MeasurableSet W) :
    toPositive (μ.restrict (A ∩ W)) + toPositive (μ.restrict (A \ W)) =
      toPositive (μ.restrict A) :=
  PositiveLinearMap.ext fun f => integral_inter_add_sdiff hW (PureState.integrable μ f).integrableOn

omit [Nonempty ι] in
/-- A finite family of observables lies below the sum of their norms times the unit. -/
lemma sum_norm_smul_one_mem_upperBounds (s : ι → E) :
    (∑ i, orderUnitNorm (s i)) • (1 : E) ∈ upperBounds (Set.range s) := by
  rintro _ ⟨i, rfl⟩
  exact (le_orderUnitNorm_smul_one (s i)).trans (smul_one_mono (Finset.single_le_sum
    (fun j _ => orderUnitNorm_nonneg (s j)) (Finset.mem_univ i)))

/-- On any piece, the upper envelope exceeds the integral of the largest value by at most twice
the norm of the family times the mass of the piece. -/
lemma upperEnvelope_restrict_le_norm (A : Set (PureState E)) :
    upperEnvelope s (toPositive (μ.restrict A)) ≤
      ∫ k in A, maxApply s k.1 ∂μ + 2 * (∑ i, orderUnitNorm (s i)) * μ.real A := by
  have h₁ := upperEnvelope_le (α := toPositive (μ.restrict A)) (sum_norm_smul_one_mem_upperBounds s)
  rw [map_smul, toPositive_one, measureReal_restrict_apply_univ, smul_eq_mul] at h₁
  have h₂ := norm_integral_le_of_norm_le_const (μ := μ.restrict A)
    (.of_forall fun k => (Real.norm_eq_abs _).trans_le (abs_maxApply_le s k.1))
  rw [measureReal_restrict_apply_univ, Real.norm_eq_abs] at h₂
  linarith [neg_abs_le (∫ k in A, maxApply s k.1 ∂μ)]

/-- Near a pure state, the upper envelope on a piece is within `ε` times its mass of the integral
of the largest value. -/
lemma exists_nhds_upperEnvelope_restrict_le {ε : ℝ} (hε : 0 < ε) (e : PureState E) :
    ∃ W : Set (PureState E), IsOpen W ∧ e ∈ W ∧ ∀ A ⊆ W, MeasurableSet A →
      upperEnvelope s (toPositive (μ.restrict A)) ≤ ∫ k in A, maxApply s k.1 ∂μ + ε * μ.real A := by
  obtain ⟨b, hb, hbe⟩ := exists_mem_upperBounds_lt (α := (toState e.1).toPositiveLinearMap)
    ((e.2.upperEnvelope_le s (apply_le_maxApply s e.1)).trans_lt (lt_add_of_pos_right _ hε))
  refine ⟨{k | toState k.1 b < maxApply s k.1 + ε}, isOpen_lt
    ((continuous_apply b).comp continuous_subtype_val)
    (((maxApply s).continuous.comp continuous_subtype_val).add continuous_const), hbe,
    fun A hAW hA => ?_⟩
  calc upperEnvelope s (toPositive (μ.restrict A)) ≤ ∫ k in A, toState k.1 b ∂μ :=
        upperEnvelope_le hb
    _ ≤ ∫ k in A, (maxApply s k.1 + ε) ∂μ := setIntegral_mono_on
        (PureState.integrable μ b).integrableOn
        ((integrable_maxApply μ s).add (integrable_const ε)).integrableOn hA fun k hk => (hAW hk).le
    _ = _ := by
        rw [integral_add (integrable_maxApply μ s).integrableOn (integrable_const ε),
          setIntegral_const, smul_eq_mul, mul_comm]

omit [Nonempty ι] in
lemma upperEnvelope_restrict_empty_le [Nonempty ι] :
    upperEnvelope s (toPositive (μ.restrict ∅)) ≤ 0 := by
  obtain ⟨b, hb⟩ := upperBounds_nonempty s
  simpa [toPositive_apply] using upperEnvelope_le (α := toPositive (μ.restrict ∅)) hb

/-!

## C. Integrating the largest value when ensembles refine

-/

variable {μ s} (hE : EnsemblesRefine E)
include hE

lemma upperEnvelope_restrict_le_of_inter_sdiff {A W : Set (PureState E)} (hW : MeasurableSet W)
    {r₁ r₂ : ℝ}
    (h₁ : upperEnvelope s (toPositive (μ.restrict (A ∩ W))) ≤
      ∫ k in A ∩ W, maxApply s k.1 ∂μ + r₁)
    (h₂ : upperEnvelope s (toPositive (μ.restrict (A \ W))) ≤
      ∫ k in A \ W, maxApply s k.1 ∂μ + r₂) :
    upperEnvelope s (toPositive (μ.restrict A)) ≤ ∫ k in A, maxApply s k.1 ∂μ + (r₁ + r₂) := by
  rw [← toPositive_restrict_inter_add_sdiff μ A hW,
    ← integral_inter_add_sdiff hW (integrable_maxApply μ s).integrableOn]
  linarith [hE.upperEnvelope_add_le s (toPositive (μ.restrict (A ∩ W)))
    (toPositive (μ.restrict (A \ W)))]

/-- Pieces covered by finitely many good neighbourhoods are good. -/
lemma upperEnvelope_restrict_le_of_subset_biUnion {ε : ℝ} {W : PureState E → Set (PureState E)}
    (hWm : ∀ e, MeasurableSet (W e)) (hW : ∀ e, ∀ A ⊆ W e, MeasurableSet A →
      upperEnvelope s (toPositive (μ.restrict A)) ≤ ∫ k in A, maxApply s k.1 ∂μ + ε * μ.real A)
    (t : Finset (PureState E)) : ∀ A, MeasurableSet A → A ⊆ ⋃ e ∈ t, W e →
      upperEnvelope s (toPositive (μ.restrict A)) ≤ ∫ k in A, maxApply s k.1 ∂μ + ε * μ.real A := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro A _ hA
    obtain rfl : A = ∅ := by simpa using hA
    simpa using upperEnvelope_restrict_empty_le (μ := μ) s
  | insert e t he ih =>
    intro A hA hAt
    have hsub : A \ W e ⊆ ⋃ e ∈ t, W e := fun k hk => by
      have := hAt hk.1
      rw [Finset.set_biUnion_insert, mem_union] at this
      exact this.resolve_left hk.2
    have h := upperEnvelope_restrict_le_of_inter_sdiff hE (hWm e)
      (hW e _ inter_subset_right (hA.inter (hWm e))) (ih _ (hA.diff (hWm e)) hsub)
    rwa [← mul_add, measureReal_inter_add_sdiff₀ (hWm e).nullMeasurableSet] at h

variable (μ s) in
/-- On a compact set of pure states, the upper envelope is within `ε` times its mass of the
integral of the largest value. -/
lemma upperEnvelope_restrict_le_of_isCompact {ε : ℝ} (hε : 0 < ε) {C : Set (PureState E)}
    (hC : IsCompact C) :
    upperEnvelope s (toPositive (μ.restrict C)) ≤ ∫ k in C, maxApply s k.1 ∂μ + ε * μ.real C := by
  choose W hWo hW hWle using fun e => exists_nhds_upperEnvelope_restrict_le μ s hε e
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover W hWo fun k _ => mem_iUnion.2 ⟨k, hW k⟩
  exact upperEnvelope_restrict_le_of_subset_biUnion hE (fun e => (hWo e).measurableSet) hWle t C
    hC.isClosed.measurableSet ht

omit hE in
/-- A finite regular measure gives all but `ε` of its mass to a compact set. -/
lemma exists_isCompact_measureReal_sdiff_lt (μ : Measure (PureState E)) [IsFiniteMeasure μ]
    [μ.Regular] {ε : ℝ} (hε : 0 < ε) : ∃ C, IsCompact C ∧ μ.real (univ \ C) < ε := by
  obtain ⟨C, -, hC, hμC⟩ := MeasurableSet.univ.exists_isCompact_sdiff_lt (μ := μ)
    (measure_ne_top _ _) (ENNReal.ofReal_pos.2 hε).ne'
  exact ⟨C, hC, ENNReal.toReal_lt_of_lt_ofReal hμC⟩

variable (μ s) in
lemma upperEnvelope_le_integral_add [IsProbabilityMeasure μ] [μ.Regular] {ε : ℝ} (hε : 0 < ε) :
    upperEnvelope s (toPositive μ) ≤
      ∫ k, maxApply s k.1 ∂μ + (ε + 2 * (∑ i, orderUnitNorm (s i)) * ε) := by
  obtain ⟨C, hC, hCε⟩ := exists_isCompact_measureReal_sdiff_lt μ hε
  have hCm := hC.isClosed.measurableSet
  have h := upperEnvelope_restrict_le_of_inter_sdiff hE (A := univ) hCm
    (by rw [univ_inter]; exact upperEnvelope_restrict_le_of_isCompact μ s hE hε hC)
    (upperEnvelope_restrict_le_norm μ s _)
  rw [toPositive_restrict_univ, setIntegral_univ] at h
  have hM : 0 ≤ 2 * ∑ i, orderUnitNorm (s i) :=
    mul_nonneg zero_le_two (Finset.sum_nonneg fun i _ => orderUnitNorm_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left (measureReal_le_one (μ := μ) (s := C)) hε.le,
    mul_le_mul_of_nonneg_left hCε.le hM]

variable (μ s) in
/-- **Choquet–Meyer**: when ensembles refine, a regular probability measure on the pure states
integrates the largest value of a finite family to the upper envelope at its barycenter. -/
lemma integral_maxApply_eq [IsProbabilityMeasure μ] [μ.Regular] :
    ∫ k, maxApply s k.1 ∂μ = upperEnvelope s (toPositive μ) := by
  refine le_antisymm (integral_maxApply_le μ s) (le_of_forall_pos_le_add fun η hη => ?_)
  have hM : 0 ≤ ∑ i, orderUnitNorm (s i) := Finset.sum_nonneg fun i _ => orderUnitNorm_nonneg _
  refine (upperEnvelope_le_integral_add μ s hE (div_pos hη (by linarith : (0 : ℝ) < 1 + 2 * _))
    ).trans_eq ?_
  congr 1
  field_simp

end PureState

/-!

## D. Density of largest values

-/

namespace StateSpace

/-- Differences of largest values on finite families of observables. -/
def maxApplyDiffs : Set C(stateSpace E, ℝ) :=
  {g | ∃ (ι κ : Type) (_ : Fintype ι) (_ : Nonempty ι) (_ : Fintype κ) (_ : Nonempty κ)
    (s : ι → E) (t : κ → E), g = maxApply s - maxApply t}

lemma sup_mem_maxApplyDiffs {g h : C(stateSpace E, ℝ)} (hg : g ∈ maxApplyDiffs)
    (hh : h ∈ maxApplyDiffs) : g ⊔ h ∈ maxApplyDiffs := by
  obtain ⟨ι, κ, _, _, _, _, s, t, rfl⟩ := hg
  obtain ⟨ι', κ', _, _, _, _, s', t', rfl⟩ := hh
  refine ⟨(ι × κ') ⊕ (ι' × κ), κ × κ', inferInstance, inferInstance, inferInstance, inferInstance,
    Sum.elim (fun p => s p.1 + t' p.2) (fun p => s' p.1 + t p.2), fun p => t p.1 + t' p.2, ?_⟩
  ext ω
  simp only [maxApply_sumElim, maxApply_add, ContinuousMap.sup_apply, ContinuousMap.sub_apply,
    ContinuousMap.add_apply]
  rw [← max_sub_sub_right]
  congr 1 <;> ring

lemma neg_mem_maxApplyDiffs {g : C(stateSpace E, ℝ)} (hg : g ∈ maxApplyDiffs) :
    -g ∈ maxApplyDiffs := by
  obtain ⟨ι, κ, _, _, _, _, s, t, rfl⟩ := hg
  exact ⟨κ, ι, inferInstance, inferInstance, inferInstance, inferInstance, t, s, neg_sub _ _⟩

lemma inf_mem_maxApplyDiffs {g h : C(stateSpace E, ℝ)} (hg : g ∈ maxApplyDiffs)
    (hh : h ∈ maxApplyDiffs) : g ⊓ h ∈ maxApplyDiffs := by
  simpa [neg_sup] using
    neg_mem_maxApplyDiffs
      (sup_mem_maxApplyDiffs (neg_mem_maxApplyDiffs hg) (neg_mem_maxApplyDiffs hh))

lemma separatesPointsStrongly_maxApplyDiffs :
    (maxApplyDiffs (E := E)).SeparatesPointsStrongly := fun v x y => by
  obtain ⟨a, hx, hy⟩ := exists_apply_eq_apply (x := x) (y := y) (v x) (v y) (congrArg v)
  refine ⟨_, ⟨Unit, Unit, inferInstance, inferInstance, inferInstance, inferInstance,
    fun _ => a, fun _ => 0, rfl⟩, ?_, ?_⟩ <;> simp [maxApply_unit, hx, hy]

/-- **Stone–Weierstrass**: differences of largest values are dense among continuous functions on
the state space. -/
lemma closure_maxApplyDiffs : closure (maxApplyDiffs (E := E)) = univ :=
  ContinuousMap.sublattice_closure_eq_top _
    ⟨0, Unit, Unit, inferInstance, inferInstance, inferInstance, inferInstance, fun _ => 0,
      fun _ => 0, by simp⟩
    (fun _ hg _ hh => inf_mem_maxApplyDiffs hg hh) (fun _ hg _ hh => sup_mem_maxApplyDiffs hg hh)
    separatesPointsStrongly_maxApplyDiffs

end StateSpace

/-!

## E. Uniqueness

-/

namespace PureState

lemma eq_of_map_val_eq {μ ν : Measure (PureState E)}
    (h : μ.map Subtype.val = ν.map Subtype.val) : μ = ν := by
  ext B hB
  obtain ⟨B', hB', rfl⟩ := hB
  rw [← Measure.map_apply measurable_subtype_coe hB', h,
    Measure.map_apply measurable_subtype_coe hB']

variable (hE : EnsemblesRefine E) {μ ν : Measure (PureState E)} [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν] [μ.Regular] [ν.Regular]
include hE

lemma integral_map_val_eq (h : toPositive μ = toPositive ν) (g : C(stateSpace E, ℝ)) :
    ∫ ω, g ω ∂μ.map Subtype.val = ∫ ω, g ω ∂ν.map Subtype.val := by
  have hL : EqOn (integralCLM (μ.map Subtype.val)) (integralCLM (ν.map Subtype.val))
      maxApplyDiffs := by
    rintro _ ⟨ι, κ, _, _, _, _, s, t, rfl⟩
    simp only [integralCLM_apply]
    rw [integral_map continuous_subtype_val.aemeasurable (by fun_prop),
      integral_map continuous_subtype_val.aemeasurable (by fun_prop)]
    simp only [ContinuousMap.sub_apply]
    rw [integral_sub (integrable_maxApply μ s) (integrable_maxApply μ t),
      integral_sub (integrable_maxApply ν s) (integrable_maxApply ν t),
      integral_maxApply_eq μ s hE, integral_maxApply_eq μ t hE, integral_maxApply_eq ν s hE,
      integral_maxApply_eq ν t hE, h]
  exact (hL.closure (integralCLM _).continuous (integralCLM _).continuous)
    (by rw [closure_maxApplyDiffs]; exact mem_univ g)

end PureState

/-- **Choquet–Meyer uniqueness**: when ensembles refine, two regular probability measures on the
pure states with the same barycenter are equal. -/
lemma EnsemblesRefine.eq_of_toPositive_eq (hE : EnsemblesRefine E)
    {μ ν : Measure (PureState E)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [μ.Regular]
    [ν.Regular] (h : toPositive μ = toPositive ν) : μ = ν := by
  have := Measure.Regular.map_of_continuous (μ := μ) continuous_subtype_val
  have := Measure.Regular.map_of_continuous (μ := ν) continuous_subtype_val
  exact PureState.eq_of_map_val_eq (Measure.ext_of_integral_eq_on_compactlySupported fun g =>
    PureState.integral_map_val_eq hE h g.toContinuousMap)

/-!

## F. Unique pure decompositions

-/

/-- **Choquet–Meyer**: when ensembles refine, a state with a decomposition into pure states has
exactly one. -/
lemma EnsemblesRefine.hasUniquePureDecomposition (hE : EnsemblesRefine E) {ω : 𝓢[ℝ, E]}
    (h : ω.HasPureDecomposition) : ω.HasUniquePureDecomposition := by
  obtain ⟨μ, hμr, hμp, hμf⟩ := h
  refine ⟨μ, ⟨hμr, hμp, hμf⟩, fun ν ⟨hνr, hνp, hνf⟩ => ?_⟩
  exact hE.eq_of_toPositive_eq (PositiveLinearMap.ext fun f => (hνf f).trans (hμf f).symm)

end ProbabilisticTheory
