/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Effect.Integral
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Norm
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.Order.Basic
public import Mathlib.Analysis.Normed.Group.Uniform

/-!

# Integrating bounded measurable functions against an effect-valued measure

## i. Overview

`Effect/Integral.lean` defines `EffectValuedMeasure.simpleIntegral`. This file extends it to
bounded measurable `f : Ω → ℝ`, assuming `E` is complete for its order-unit norm.

## ii. Construction

For a bound `M` with `|f x| ≤ M` and scale `n`, `meshPiece f M n` and `meshWeight M n` define a
finite simple approximation with uniform error at most `1/(n+1)`. The comparison lemma for two
simple approximations makes these integrals Cauchy and proves that every uniformly approximating
sequence has the same limit. The resulting integral is independent of the bound, agrees with
`simpleIntegral`, and is linear and positive.

## iii. Key definitions and results

- `EffectValuedMeasure.meshBound`, `MeshIndex`, `meshWeight`, `meshPiece` : the width-`1/(n+1)`
  mesh simple function approximating a bounded measurable `f` with `|f x| ≤ M`, and its uniform
  convergence to `f` (`abs_simpleValue_meshWeight_meshPiece_sub_le`).
- `EffectValuedMeasure.orderUnitNorm_simpleIntegral_sub_le` : the key comparison lemma — two simple
  functions within `ε`, `ε'` of `f` give simple integrals within `ε + ε'` of each other.
- `EffectValuedMeasure.cauchySeq_meshSimpleIntegral`, `EffectValuedMeasure.integral` : the mesh
  sequence is Cauchy, and (under `[CompleteSpace E]`, fixed via `letI`/`local instance` from
  `IsArchimedeanOrderUnit.orderUnitNormedAddCommGroup`) `integral hf hM μ` is its limit.
- `EffectValuedMeasure.tendsto_of_uniformly_approximating` : independence from the approximating
  sequence — any uniformly-approximating simple-function sequence has the same limit.
- `EffectValuedMeasure.integral_indep_of_bound`, `integral_eq_simpleIntegral` : independence from
  the bound `M`, and agreement with `simpleIntegral` on functions that already are simple.
- `EffectValuedMeasure.integral_add`, `integral_smul`, `nonneg_integral` : linearity and
  positivity.

## iv. Table of contents

- A. Mesh approximation
- B. Linear operations on simple values
- C. Comparison of simple integrals
- D. Construction by completeness

-/

@[expose] public section

namespace EffectValuedMeasure

/-! ## A. The mesh approximation of a bounded measurable function -/

section Mesh

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The number of width-`1/(n+1)` mesh cells it takes to reach out to `M` on either side of `0`:
`⌈(n+1)*M⌉₊`. Only depends on `M` and `n`, not on any particular function. -/
noncomputable def meshBound (M : ℝ) (n : ℕ) : ℕ := ⌈(n + 1 : ℝ) * M⌉₊

/-- The mesh cell label set at scale `n` covering `[-M, M]`: integers from `-meshBound M n` to
`meshBound M n`. -/
abbrev MeshIndex (M : ℝ) (n : ℕ) : Type :=
  ↥(Finset.Icc (-(meshBound M n : ℤ)) (meshBound M n : ℤ))

/-- The weight of mesh cell `k` at scale `n`: `k/(n+1)`, the left endpoint of the cell. -/
noncomputable def meshWeight (M : ℝ) (n : ℕ) (k : MeshIndex M n) : ℝ := (k : ℤ) / ((n : ℝ) + 1)

/-- The mesh cell `k` at scale `n`, pulled back along `f`: the points where `f` rounds down to
`k/(n+1)` at that scale, i.e. `⌊(n+1)*f(x)⌋ = k`. -/
noncomputable def meshPiece (f : Ω → ℝ) (M : ℝ) (n : ℕ) (k : MeshIndex M n) : Set Ω :=
  (fun x => ⌊((n : ℝ) + 1) * f x⌋) ⁻¹' {(k : ℤ)}

variable {f : Ω → ℝ} {M : ℝ}

omit [MeasurableSpace Ω] in
@[simp]
lemma mem_meshPiece_iff (n : ℕ) (k : MeshIndex M n) (x : Ω) :
    x ∈ meshPiece f M n k ↔ ⌊((n : ℝ) + 1) * f x⌋ = (k : ℤ) := Iff.rfl

variable (hf : Measurable f) (hM : ∀ x, |f x| ≤ M)

include hf in
lemma measurableSet_meshPiece (n : ℕ) (k : MeshIndex M n) : MeasurableSet (meshPiece f M n k) :=
  (Measurable.floor (measurable_const.mul hf)) (measurableSet_singleton _)

include hM in
/-- The label the mesh assigns to the point `x`, together with the proof that it lies in range:
`⌊(n+1)*f(x)⌋` always lies in `[-meshBound M n, meshBound M n]` once `|f x| ≤ M`. -/
noncomputable def meshIndexOf (n : ℕ) (x : Ω) : MeshIndex M n :=
  ⟨⌊((n : ℝ) + 1) * f x⌋, by
    unfold meshBound
    have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have hle : f x ≤ M := (abs_le.mp (hM x)).2
    have hge : -M ≤ f x := (abs_le.mp (hM x)).1
    have hceil : ((n:ℝ)+1) * M ≤ (⌈((n:ℝ)+1) * M⌉₊ : ℝ) := Nat.le_ceil _
    have hub : ((n:ℝ)+1) * f x ≤ (⌈((n:ℝ)+1) * M⌉₊ : ℝ) := by
      have := mul_le_mul_of_nonneg_left hle hn1.le
      linarith
    have hlb : -(⌈((n:ℝ)+1) * M⌉₊ : ℝ) ≤ ((n:ℝ)+1) * f x := by
      have := mul_le_mul_of_nonneg_left hge hn1.le
      linarith
    rw [Finset.mem_Icc]
    constructor
    · have hmono := Int.floor_mono hlb
      have heq : ⌊(-(⌈((n:ℝ)+1) * M⌉₊ : ℝ))⌋ = -(⌈((n:ℝ)+1) * M⌉₊ : ℤ) := by
        rw [show (-(⌈((n:ℝ)+1) * M⌉₊ : ℝ)) = ((-(⌈((n:ℝ)+1) * M⌉₊ : ℤ) : ℤ) : ℝ) by push_cast; ring]
        exact Int.floor_intCast _
      rwa [heq] at hmono
    · have hmono := Int.floor_mono hub
      rwa [Int.floor_natCast] at hmono⟩

omit [MeasurableSpace Ω] in
include hM in
@[simp]
lemma meshIndexOf_coe (n : ℕ) (x : Ω) :
    ((meshIndexOf hM n x : MeshIndex M n) : ℤ) = ⌊((n : ℝ) + 1) * f x⌋ := rfl

omit [MeasurableSpace Ω] in
include hM in
lemma mem_meshPiece_meshIndexOf (n : ℕ) (x : Ω) : x ∈ meshPiece f M n (meshIndexOf hM n x) := rfl

include hf hM in
/-- The mesh pieces at scale `n` form a finite measurable partition of `Ω`. -/
lemma isPartition_meshPiece (n : ℕ) : IsPartition (meshPiece f M n) where
  measurable k := measurableSet_meshPiece hf n k
  disjoint k l hkl := by
    rw [Set.disjoint_left]
    intro x hxk hxl
    rw [mem_meshPiece_iff] at hxk hxl
    exact hkl (Subtype.ext (hxk.symm.trans hxl))
  cover := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨meshIndexOf hM n x, mem_meshPiece_meshIndexOf hM n x⟩

include hf hM in
/-- The value of the mesh simple function at `x` is the label `f` is assigned, over `(n+1)`. -/
lemma simpleValue_meshWeight_meshPiece (n : ℕ) (x : Ω) :
    simpleValue (meshWeight M n) (meshPiece f M n) x =
      (⌊((n : ℝ) + 1) * f x⌋ : ℝ) / ((n : ℝ) + 1) := by
  rw [simpleValue_apply_of_mem (isPartition_meshPiece hf hM n) (mem_meshPiece_meshIndexOf hM n x)]
  unfold meshWeight
  rw [meshIndexOf_coe hM]

include hf hM in
/-- **Uniform convergence of the mesh approximation.** At scale `n`, the mesh simple function
never differs from `f` by more than the mesh width `1/(n+1)`, at any point. -/
lemma abs_simpleValue_meshWeight_meshPiece_sub_le (n : ℕ) (x : Ω) :
    |simpleValue (meshWeight M n) (meshPiece f M n) x - f x| ≤ 1 / ((n : ℝ) + 1) := by
  rw [simpleValue_meshWeight_meshPiece hf hM]
  have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have h1 : (⌊((n:ℝ)+1) * f x⌋ : ℝ) ≤ ((n:ℝ)+1) * f x := Int.floor_le _
  have h2 : ((n:ℝ)+1) * f x < (⌊((n:ℝ)+1) * f x⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hle : (⌊((n:ℝ)+1) * f x⌋ : ℝ) / ((n:ℝ)+1) ≤ f x := by
    rw [div_le_iff₀ hn1]
    nlinarith [h1]
  have hlt : f x < (⌊((n:ℝ)+1) * f x⌋ : ℝ) / ((n:ℝ)+1) + 1 / ((n:ℝ)+1) := by
    rw [← add_div, lt_div_iff₀ hn1]
    nlinarith [h2]
  rw [abs_le]
  constructor <;> linarith

end Mesh

section SimpleValueLinear

/-! ## B. Linear operations on simple values -/

variable {Ω : Type*} {ι : Type*} [Fintype ι]

/-- `simpleValue` is additive in the weights, pointwise. -/
lemma simpleValue_add (a b : ι → ℝ) (s : ι → Set Ω) (x : Ω) :
    simpleValue (a + b) s x = simpleValue a s x + simpleValue b s x := by
  unfold simpleValue
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : x ∈ s i <;> simp [hi]

/-- `simpleValue` is homogeneous in the weights, pointwise. -/
lemma simpleValue_smul (r : ℝ) (c : ι → ℝ) (s : ι → Set Ω) (x : Ω) :
    simpleValue (r • c) s x = r * simpleValue c s x := by
  unfold simpleValue
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : x ∈ s i <;> simp [hi]

end SimpleValueLinear

/-! ## C. Comparing the simple integrals of two approximations

The key ingredient for both the Cauchy property and the independence of the eventual integral
from the choice of approximating sequence: if two simple functions (over possibly different
partitions) both stay within `ε`, resp. `ε'`, of the same `f` everywhere, their integrals against
`μ` stay within `ε + ε'` of each other, in the order-unit norm. -/

section Comparison

variable {Ω E : Type*} [MeasurableSpace Ω] [AddCommGroup E] [PartialOrder E]
  [IsOrderedAddMonoid E] [Module ℝ E] [PosSMulMono ℝ E] [One E] [IsArchimedeanOrderUnit E]

open IsArchimedeanOrderUnit

/-- The pairwise intersections of two partitions again form a partition, indexed by the product of
their labels. -/
lemma isPartition_inter {ι ι' : Type*} [Fintype ι] [Fintype ι'] {s : ι → Set Ω} {s' : ι' → Set Ω}
    (hs : IsPartition s) (hs' : IsPartition s') :
    IsPartition (fun p : ι × ι' => s p.1 ∩ s' p.2) where
  measurable p := (hs.measurable p.1).inter (hs'.measurable p.2)
  disjoint p q hpq := by
    rcases p with ⟨i, j⟩
    rcases q with ⟨i', j'⟩
    by_cases hii' : i = i'
    · subst hii'
      have hjj' : j ≠ j' := fun h => hpq (by rw [h])
      exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right (hs'.disjoint j j' hjj')
    · exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left (hs.disjoint i i' hii')
  cover := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hxs : x ∈ ⋃ i, s i := by rw [hs.cover]; trivial
    have hxs' : x ∈ ⋃ j, s' j := by rw [hs'.cover]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxs
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxs'
    exact ⟨(i, j), hi, hj⟩

lemma simpleValue_eq_simpleValue_inter_fst {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {c : ι → ℝ} {s : ι → Set Ω} (hs : IsPartition s) {s' : ι' → Set Ω} (hs' : IsPartition s')
    (x : Ω) :
    simpleValue c s x = simpleValue (fun p : ι × ι' => c p.1) (fun p => s p.1 ∩ s' p.2) x := by
  have hxs : x ∈ ⋃ i, s i := by rw [hs.cover]; trivial
  have hxs' : x ∈ ⋃ j, s' j := by rw [hs'.cover]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxs
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxs'
  rw [simpleValue_apply_of_mem hs hi,
    simpleValue_apply_of_mem (isPartition_inter hs hs') (i := (i, j))
      (show x ∈ s i ∩ s' j from ⟨hi, hj⟩)]

lemma simpleValue_eq_simpleValue_inter_snd {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {c' : ι' → ℝ} {s : ι → Set Ω} (hs : IsPartition s) {s' : ι' → Set Ω} (hs' : IsPartition s')
    (x : Ω) :
    simpleValue c' s' x = simpleValue (fun p : ι × ι' => c' p.2) (fun p => s p.1 ∩ s' p.2) x := by
  have hxs : x ∈ ⋃ i, s i := by rw [hs.cover]; trivial
  have hxs' : x ∈ ⋃ j, s' j := by rw [hs'.cover]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxs
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxs'
  rw [simpleValue_apply_of_mem hs' hj,
    simpleValue_apply_of_mem (isPartition_inter hs hs') (i := (i, j))
      (show x ∈ s i ∩ s' j from ⟨hi, hj⟩)]

/-- The pointwise sum of two simple functions, over possibly different partitions, is the simple
function of their common refinement with pointwise-summed weights. Used to build an admissible
approximating sequence for `f + g` out of ones for `f` and `g`. -/
lemma simpleValue_add_inter {ι ι' : Type*} [Fintype ι] [Fintype ι'] {a : ι → ℝ} {s : ι → Set Ω}
    (hs : IsPartition s) {b : ι' → ℝ} {s' : ι' → Set Ω} (hs' : IsPartition s') (x : Ω) :
    simpleValue a s x + simpleValue b s' x =
      simpleValue (fun p : ι × ι' => a p.1 + b p.2) (fun p => s p.1 ∩ s' p.2) x := by
  rw [simpleValue_eq_simpleValue_inter_fst hs hs', simpleValue_eq_simpleValue_inter_snd hs hs',
    ← simpleValue_add]
  congr 1

omit [PosSMulMono ℝ E] in
lemma simpleIntegral_eq_simpleIntegral_inter_fst {ι ι' : Type*} [Fintype ι] [Fintype ι']
    [DecidableEq ι] [DecidableEq ι'] (μ : EffectValuedMeasure Ω E) {c : ι → ℝ} {s : ι → Set Ω}
    (hs : IsPartition s) {s' : ι' → Set Ω} (hs' : IsPartition s') :
    simpleIntegral μ c s hs =
      simpleIntegral μ (fun p : ι × ι' => c p.1) (fun p => s p.1 ∩ s' p.2)
        (isPartition_inter hs hs') :=
  simpleIntegral_eq_of_pointwise_eq μ c s hs _ _ (isPartition_inter hs hs')
    (simpleValue_eq_simpleValue_inter_fst hs hs')

omit [PosSMulMono ℝ E] in
lemma simpleIntegral_eq_simpleIntegral_inter_snd {ι ι' : Type*} [Fintype ι] [Fintype ι']
    [DecidableEq ι] [DecidableEq ι'] (μ : EffectValuedMeasure Ω E) {c' : ι' → ℝ} {s : ι → Set Ω}
    (hs : IsPartition s) {s' : ι' → Set Ω} (hs' : IsPartition s') :
    simpleIntegral μ c' s' hs' =
      simpleIntegral μ (fun p : ι × ι' => c' p.2) (fun p => s p.1 ∩ s' p.2)
        (isPartition_inter hs hs') :=
  simpleIntegral_eq_of_pointwise_eq μ c' s' hs' _ _ (isPartition_inter hs hs')
    (simpleValue_eq_simpleValue_inter_snd hs hs')

omit [PosSMulMono ℝ E] in
/-- The difference of two simple integrals, over possibly different partitions, is itself a simple
integral over their common refinement, with weights the pointwise difference of the two original
weights. This is what lets the difference be bounded termwise. -/
lemma simpleIntegral_sub_simpleIntegral {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    [DecidableEq ι'] (μ : EffectValuedMeasure Ω E) {c : ι → ℝ} {s : ι → Set Ω}
    (hs : IsPartition s) {c' : ι' → ℝ} {s' : ι' → Set Ω} (hs' : IsPartition s') :
    simpleIntegral μ c s hs - simpleIntegral μ c' s' hs' =
      simpleIntegral μ (fun p : ι × ι' => c p.1 - c' p.2) (fun p => s p.1 ∩ s' p.2)
        (isPartition_inter hs hs') := by
  have hd : (fun p : ι × ι' => c p.1 - c' p.2)
      = (fun p : ι × ι' => c p.1) + (-1 : ℝ) • (fun p : ι × ι' => c' p.2) := by
    funext p; simp [sub_eq_add_neg]
  rw [hd, simpleIntegral_add, simpleIntegral_smul,
    ← simpleIntegral_eq_simpleIntegral_inter_fst μ hs hs',
    ← simpleIntegral_eq_simpleIntegral_inter_snd μ hs hs', neg_one_smul, sub_eq_add_neg]

omit [PosSMulMono ℝ E] in
/-- The sum of two simple integrals, over possibly different partitions, is itself a simple
integral over their common refinement, with weights the pointwise sum of the two original
weights. Used to build an admissible approximating sequence for `f + g` out of ones for `f` and
`g`. -/
lemma simpleIntegral_add_simpleIntegral {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    [DecidableEq ι'] (μ : EffectValuedMeasure Ω E) {c : ι → ℝ} {s : ι → Set Ω}
    (hs : IsPartition s) {c' : ι' → ℝ} {s' : ι' → Set Ω} (hs' : IsPartition s') :
    simpleIntegral μ c s hs + simpleIntegral μ c' s' hs' =
      simpleIntegral μ (fun p : ι × ι' => c p.1 + c' p.2) (fun p => s p.1 ∩ s' p.2)
        (isPartition_inter hs hs') := by
  rw [simpleIntegral_eq_simpleIntegral_inter_fst μ hs hs',
    simpleIntegral_eq_simpleIntegral_inter_snd μ hs hs', ← simpleIntegral_add]
  congr 1

omit [PosSMulMono ℝ E] in
/-- The total measure of a partition is the certain outcome. -/
lemma sum_apply_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : EffectValuedMeasure Ω E)
    {s : ι → Set Ω} (hs : IsPartition s) :
    ∑ i, (μ (s i) (hs.measurable i) : E) = 1 := by
  have h := apply_iUnion_of_disjoint μ s hs.measurable hs.disjoint
  rw [apply_congr μ hs.cover (ht := MeasurableSet.univ), map_univ] at h
  exact h.symm

/-- A simple integral whose weights are bounded by `δ`, on every piece the underlying measure sees
(i.e. every nonempty piece), has order-unit norm at most `δ`: every term is sandwiched between
`±δ` times a nonnegative effect, and those effects sum to the certain outcome. -/
lemma orderUnitNorm_simpleIntegral_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : EffectValuedMeasure Ω E) {c : ι → ℝ} {s : ι → Set Ω} (hs : IsPartition s) {δ : ℝ}
    (hδ : 0 ≤ δ) (hc : ∀ i, (s i).Nonempty → |c i| ≤ δ) :
    orderUnitNorm (simpleIntegral μ c s hs) ≤ δ := by
  have hzero : ∀ i, ¬ (s i).Nonempty → (μ (s i) (hs.measurable i) : E) = 0 := by
    intro i hi
    rw [Set.not_nonempty_iff_eq_empty] at hi
    rw [apply_congr μ hi (ht := MeasurableSet.empty)]
    simp
  apply orderUnitNorm_le
  refine ⟨hδ, ?_, ?_⟩
  · have hlow : ∀ i ∈ (Finset.univ : Finset ι),
        (-δ) • (μ (s i) (hs.measurable i) : E) ≤ c i • (μ (s i) (hs.measurable i) : E) := by
      intro i _
      by_cases hi : (s i).Nonempty
      · exact smul_le_smul_of_nonneg_right (abs_le.mp (hc i hi)).1 (μ (s i) (hs.measurable i)).2.1
      · rw [hzero i hi]; simp
    have keyL : ∑ i, ((-δ) • (μ (s i) (hs.measurable i) : E)) = -(δ • (1 : E)) := by
      rw [← Finset.smul_sum, sum_apply_eq_one μ hs, neg_smul]
    calc -(δ • (1 : E)) = ∑ i, ((-δ) • (μ (s i) (hs.measurable i) : E)) := keyL.symm
      _ ≤ ∑ i, (c i • (μ (s i) (hs.measurable i) : E)) := Finset.sum_le_sum hlow
      _ = simpleIntegral μ c s hs := rfl
  · have hup : ∀ i ∈ (Finset.univ : Finset ι),
        c i • (μ (s i) (hs.measurable i) : E) ≤ δ • (μ (s i) (hs.measurable i) : E) := by
      intro i _
      by_cases hi : (s i).Nonempty
      · exact smul_le_smul_of_nonneg_right (abs_le.mp (hc i hi)).2 (μ (s i) (hs.measurable i)).2.1
      · rw [hzero i hi]; simp
    have keyU : ∑ i, (δ • (μ (s i) (hs.measurable i) : E)) = δ • (1 : E) := by
      rw [← Finset.smul_sum, sum_apply_eq_one μ hs]
    calc simpleIntegral μ c s hs = ∑ i, (c i • (μ (s i) (hs.measurable i) : E)) := rfl
      _ ≤ ∑ i, (δ • (μ (s i) (hs.measurable i) : E)) := Finset.sum_le_sum hup
      _ = δ • (1 : E) := keyU

/-- A simple integral is nonnegative as soon as its weights are nonnegative on every piece the
underlying measure sees (i.e. every nonempty piece) — the same "only nonempty pieces matter"
relaxation of `simpleIntegral_nonneg` used above for the norm bound. -/
lemma simpleIntegral_nonneg' {ι : Type*} [Fintype ι] (μ : EffectValuedMeasure Ω E) {c : ι → ℝ}
    {s : ι → Set Ω} (hs : IsPartition s) (hc : ∀ i, (s i).Nonempty → 0 ≤ c i) :
    0 ≤ simpleIntegral μ c s hs := by
  unfold simpleIntegral
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : (s i).Nonempty
  · exact smul_nonneg (hc i hi) (μ (s i) (hs.measurable i)).2.1
  · rw [Set.not_nonempty_iff_eq_empty] at hi
    rw [apply_congr μ hi (ht := MeasurableSet.empty)]
    simp

/-- **The key comparison lemma.** Two simple functions that both stay within `ε`, resp. `ε'`, of
the same bounded function `f` everywhere give integrals against `μ` that are within `ε + ε'` of
each other, in the order-unit norm — regardless of which partitions were used to build them. -/
theorem orderUnitNorm_simpleIntegral_sub_le {ι ι' : Type*} [Fintype ι] [Fintype ι']
    [DecidableEq ι] [DecidableEq ι'] (μ : EffectValuedMeasure Ω E) {f : Ω → ℝ}
    {c : ι → ℝ} {s : ι → Set Ω} (hs : IsPartition s) {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ x, |simpleValue c s x - f x| ≤ ε)
    {c' : ι' → ℝ} {s' : ι' → Set Ω} (hs' : IsPartition s') {ε' : ℝ} (hε' : 0 ≤ ε')
    (hc' : ∀ x, |simpleValue c' s' x - f x| ≤ ε') :
    orderUnitNorm (simpleIntegral μ c s hs - simpleIntegral μ c' s' hs') ≤ ε + ε' := by
  rw [simpleIntegral_sub_simpleIntegral μ hs hs']
  apply orderUnitNorm_simpleIntegral_le μ (isPartition_inter hs hs') (add_nonneg hε hε')
  rintro ⟨i, j⟩ ⟨x, hx⟩
  have hxi : x ∈ s i := hx.1
  have hxj : x ∈ s' j := hx.2
  have hci : c i = simpleValue c s x := (simpleValue_apply_of_mem hs hxi).symm
  have hcj : c' j = simpleValue c' s' x := (simpleValue_apply_of_mem hs' hxj).symm
  have h1 : |simpleValue c s x - f x| ≤ ε := hc x
  have h2 : |simpleValue c' s' x - f x| ≤ ε' := hc' x
  rw [hci, hcj]
  calc |simpleValue c s x - simpleValue c' s' x|
      = |(simpleValue c s x - f x) - (simpleValue c' s' x - f x)| := by ring_nf
    _ ≤ |simpleValue c s x - f x| + |simpleValue c' s' x - f x| := abs_sub _ _
    _ ≤ ε + ε' := add_le_add h1 h2

private lemma orderUnitNorm_smul_le_of_nonneg {c : ℝ} (hc : 0 ≤ c) (x : E) :
    orderUnitNorm (c • x) ≤ c * orderUnitNorm x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  rcases hc.eq_or_lt with hc0 | hc0
  · rw [← hc0]; simpa using hε.le
  · obtain ⟨r, hr, hrlt⟩ := exists_orderUnitBound_lt_orderUnitNorm_add x (div_pos hε hc0)
    have hmem : c * r ∈ orderUnitBounds (c • x) := by
      refine ⟨mul_nonneg hc hr.1, ?_, ?_⟩
      · calc -((c * r) • (1 : E)) = c • (-(r • (1 : E))) := by module
          _ ≤ c • x := smul_le_smul_of_nonneg_left hr.2.1 hc
      · calc c • x ≤ c • (r • (1 : E)) := smul_le_smul_of_nonneg_left hr.2.2 hc
          _ = (c * r) • (1 : E) := by module
    have hc0' : c ≠ 0 := hc0.ne'
    calc orderUnitNorm (c • x) ≤ c * r := orderUnitNorm_le hmem
      _ ≤ c * (orderUnitNorm x + ε / c) := (mul_lt_mul_of_pos_left hrlt hc0).le
      _ = c * orderUnitNorm x + ε := by field_simp

/-- The order-unit norm is `|c|`-Lipschitz under scaling by a fixed real: needed since this level
of generality never assumes `E` is a normed *space* over `ℝ` (only a normed *group*, since no
compatibility between the order-unit norm and the `ℝ`-action is otherwise available), so scalar
multiplication's continuity has to be established by hand from this bound wherever it's used
below. -/
lemma orderUnitNorm_smul_le (c : ℝ) (x : E) : orderUnitNorm (c • x) ≤ |c| * orderUnitNorm x := by
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc]
    exact orderUnitNorm_smul_le_of_nonneg hc x
  · rw [abs_of_nonpos hc, show c • x = -((-c) • x) by rw [neg_smul, neg_neg], orderUnitNorm_neg]
    exact orderUnitNorm_smul_le_of_nonneg (neg_nonneg.mpr hc) x

/-- Any real strictly above the order-unit norm of `y` is itself an order-unit bound of `y`: since
`orderUnitBounds y` is an up-set with infimum `orderUnitNorm y`, anything strictly past that
infimum is already in the set. The positivity argument below needs this to turn a norm estimate
into an actual order bound. -/
lemma le_smul_one_of_orderUnitNorm_lt {y : E} {r : ℝ} (h : orderUnitNorm y < r) :
    y ≤ r • (1 : E) := by
  obtain ⟨r', hr', hr'lt⟩ := exists_lt_of_csInf_lt (orderUnitBounds_nonempty y) h
  calc y ≤ r' • (1 : E) := hr'.2.2
    _ ≤ r • (1 : E) := smul_le_smul_of_nonneg_right hr'lt.le IsOrderUnit.one_nonneg

end Comparison

/-! ## D. The integral, via completeness

`E`'s order-unit norm (`IsArchimedeanOrderUnit.orderUnitNorm`) makes it a normed group via
`IsArchimedeanOrderUnit.orderUnitNormedAddCommGroup`, deliberately not a registered instance at
this level of generality (see `OrderUnit/Norm.lean`); we fix it as a `local instance` for this
section (the term-mode `letI` the file's plan mentions is the tactic-mode spelling of the same
thing; at the section/command level `local instance` is what registers it for the elaborator), and
additionally assume `[CompleteSpace E]` under *that* instance — a genuine extra hypothesis, since
most order-unit spaces are not complete. -/

section Definition

variable {Ω E : Type*} [MeasurableSpace Ω] [AddCommGroup E] [PartialOrder E]
  [IsOrderedAddMonoid E] [Module ℝ E] [PosSMulMono ℝ E] [One E] [IsArchimedeanOrderUnit E]

open IsArchimedeanOrderUnit Filter Topology

/-- The order-unit norm supplies the ambient normed additive-group structure for this section. -/
@[nolint docBlame]
noncomputable local instance instNormedAddCommGroup : NormedAddCommGroup E :=
  IsArchimedeanOrderUnit.orderUnitNormedAddCommGroup

variable [CompleteSpace E]

omit [CompleteSpace E] in
lemma dist_eq_orderUnitNorm (x y : E) : dist x y = orderUnitNorm (x - y) := by
  rw [dist_eq_norm]
  rfl

omit [CompleteSpace E] in
/-- Scalar multiplication by a fixed real is continuous, established by hand from
`orderUnitNorm_smul_le` since no `NormedSpace ℝ E` instance is assumed at this generality. -/
lemma tendsto_const_smul_of_tendsto {a : ℕ → E} {L : E} (c : ℝ)
    (ha : Filter.Tendsto a atTop (𝓝 L)) : Filter.Tendsto (fun n => c • a n) atTop (𝓝 (c • L)) := by
  rw [tendsto_iff_dist_tendsto_zero] at ha ⊢
  have hb : ∀ n, dist (c • a n) (c • L) ≤ |c| * dist (a n) L := by
    intro n
    rw [dist_eq_orderUnitNorm, dist_eq_orderUnitNorm, ← smul_sub]
    exact orderUnitNorm_smul_le c (a n - L)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => dist_nonneg) hb
  simpa using ha.const_mul |c|

variable {f : Ω → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M)

omit [CompleteSpace E] in
include hf hM in
/-- **The mesh approximation is Cauchy.** Refining the mesh from scale `n` to scale `m`, both past
`N`, moves the simple integral by at most `2/(N+1)` in the order-unit norm — the sum of the two
meshes' uniform error bounds, via `orderUnitNorm_simpleIntegral_sub_le`. -/
lemma cauchySeq_meshSimpleIntegral (μ : EffectValuedMeasure Ω E) :
    CauchySeq (fun n : ℕ => simpleIntegral μ (meshWeight M n) (meshPiece f M n)
      (isPartition_meshPiece hf hM n)) := by
  apply cauchySeq_of_le_tendsto_0 (fun N : ℕ => 2 / ((N : ℝ) + 1))
  · intro n m N hNn hNm
    rw [dist_eq_orderUnitNorm]
    have hbound := orderUnitNorm_simpleIntegral_sub_le μ (f := f)
      (isPartition_meshPiece hf hM n) (by positivity : (0:ℝ) ≤ 1 / ((n:ℝ)+1))
      (abs_simpleValue_meshWeight_meshPiece_sub_le hf hM n)
      (isPartition_meshPiece hf hM m) (by positivity : (0:ℝ) ≤ 1 / ((m:ℝ)+1))
      (abs_simpleValue_meshWeight_meshPiece_sub_le hf hM m)
    have hn : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.succ_le_succ hNn
    have hm : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.succ_le_succ hNm
    calc orderUnitNorm (simpleIntegral μ (meshWeight M n) (meshPiece f M n)
            (isPartition_meshPiece hf hM n)
          - simpleIntegral μ (meshWeight M m) (meshPiece f M m) (isPartition_meshPiece hf hM m))
        ≤ 1 / ((n:ℝ)+1) + 1 / ((m:ℝ)+1) := hbound
      _ ≤ 1 / ((N:ℝ)+1) + 1 / ((N:ℝ)+1) := add_le_add hn hm
      _ = 2 / ((N:ℝ)+1) := by ring
  · simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2

include hf hM in
/-- **The integral of a bounded measurable function against `μ`.** The limit of the mesh
approximation's simple integrals, which exists by completeness of `E` since the sequence is
Cauchy. -/
noncomputable def integral (μ : EffectValuedMeasure Ω E) : E :=
  (cauchySeq_tendsto_of_complete (cauchySeq_meshSimpleIntegral hf hM μ)).choose

include hf hM in
/-- The mesh approximation's simple integrals converge to `integral hf hM μ`, by construction. -/
lemma integral_tendsto (μ : EffectValuedMeasure Ω E) :
    Tendsto (fun n : ℕ => simpleIntegral μ (meshWeight M n) (meshPiece f M n)
      (isPartition_meshPiece hf hM n)) atTop (𝓝 (integral hf hM μ)) :=
  (cauchySeq_tendsto_of_complete (cauchySeq_meshSimpleIntegral hf hM μ)).choose_spec

include hf hM in
/-- **Independence of the approximating sequence.** Any sequence of simple-function partitions
whose simple values converge to `f` uniformly (with an explicit `→ 0` error bound) has its simple
integrals against `μ` converge to `integral hf hM μ` — not just the canonical mesh sequence used to
define it. This is what makes `integral` a genuine integral of the function `f`, not of the
particular mesh construction: swap in any other admissible approximation and the same limit comes
out, by the same comparison argument (`orderUnitNorm_simpleIntegral_sub_le`) that drove the Cauchy
property above. -/
theorem tendsto_of_uniformly_approximating (μ : EffectValuedMeasure Ω E) {ι : ℕ → Type*}
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] {c : ∀ n, ι n → ℝ} {s : ∀ n, ι n → Set Ω}
    (hs : ∀ n, IsPartition (s n)) {ε : ℕ → ℝ} (hε0 : ∀ n, 0 ≤ ε n)
    (hεtendsto : Tendsto ε atTop (𝓝 0)) (happrox : ∀ n x, |simpleValue (c n) (s n) x - f x| ≤ ε n) :
    Tendsto (fun n => simpleIntegral μ (c n) (s n) (hs n)) atTop (𝓝 (integral hf hM μ)) := by
  apply Filter.Tendsto.congr_dist (integral_tendsto hf hM μ)
  have hb : ∀ n : ℕ, dist
      (simpleIntegral μ (meshWeight M n) (meshPiece f M n) (isPartition_meshPiece hf hM n))
      (simpleIntegral μ (c n) (s n) (hs n)) ≤ 1 / ((n:ℝ)+1) + ε n := by
    intro n
    rw [dist_eq_orderUnitNorm]
    exact orderUnitNorm_simpleIntegral_sub_le μ (f := f) (isPartition_meshPiece hf hM n)
      (by positivity) (abs_simpleValue_meshWeight_meshPiece_sub_le hf hM n) (hs n) (hε0 n)
      (happrox n)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => dist_nonneg) hb
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).add hεtendsto

include hf hM in
/-- **Independence from the choice of bound.** `integral` doesn't depend on which valid bound `M`
was used to build it: swapping in another bound `M'` only changes the *range* of mesh cells, not
their width, so the `M'`-mesh sequence is itself uniformly approximating for the `M`-built
`integral hf hM μ` too, and `tendsto_nhds_unique` identifies the two limits. -/
theorem integral_indep_of_bound {M' : ℝ} (hM' : ∀ x, |f x| ≤ M') (μ : EffectValuedMeasure Ω E) :
    integral hf hM μ = integral hf hM' μ := by
  have happrox := tendsto_of_uniformly_approximating hf hM μ
    (hs := fun n => isPartition_meshPiece hf hM' n) (ε := fun n => 1 / ((n:ℝ)+1))
    (fun n => by positivity) (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    (abs_simpleValue_meshWeight_meshPiece_sub_le hf hM')
  exact tendsto_nhds_unique happrox (integral_tendsto hf hM' μ)

include hf hM in
/-- **Consistency with the simple case.** When `f` already *is* a simple function against some
partition, `integral` agrees with `simpleIntegral` on it — the general construction extends the
special case rather than computing something else. The constant sequence `(c, s, hs)` is itself
(trivially) uniformly approximating, with error `0`, so `tendsto_of_uniformly_approximating`
applies directly. -/
theorem integral_eq_simpleIntegral {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ι → ℝ}
    {s : ι → Set Ω} (hs : IsPartition s) (hcs : ∀ x, simpleValue c s x = f x)
    (μ : EffectValuedMeasure Ω E) : integral hf hM μ = simpleIntegral μ c s hs := by
  have happrox := tendsto_of_uniformly_approximating hf hM μ (ι := fun _ : ℕ => ι)
    (c := fun _ => c) (s := fun _ => s) (fun _ => hs) (ε := fun _ => (0 : ℝ))
    (fun _ => le_refl 0) tendsto_const_nhds (fun _ x => by rw [hcs x]; simp)
  exact tendsto_nhds_unique happrox tendsto_const_nhds

include hf hM in
/-- **Positivity.** A nonnegative `f` integrates to a nonnegative value: every mesh approximation
of a nonnegative `f` has nonnegative weight on every piece it actually sees (a piece labelled `k`
that meets `f`'s graph forces `k ≥ 0`, since `f ≥ 0` there), so every term of the mesh sequence is
`≥ 0` (`simpleIntegral_nonneg'`); pass that bound to the limit using that
`-integral hf hM μ ≤ ε • 1` for every `ε > 0`, which is exactly what
`IsArchimedeanOrderUnit.le_zero_of_forall_pos_smul_one_le` needs to conclude `-integral ≤ 0`. -/
theorem nonneg_integral (hf0 : ∀ x, 0 ≤ f x) (μ : EffectValuedMeasure Ω E) :
    0 ≤ integral hf hM μ := by
  have hmesh_nonneg : ∀ n, 0 ≤ simpleIntegral μ (meshWeight M n) (meshPiece f M n)
      (isPartition_meshPiece hf hM n) := by
    intro n
    apply simpleIntegral_nonneg' μ (isPartition_meshPiece hf hM n)
    intro k ⟨x, hx⟩
    rw [mem_meshPiece_iff] at hx
    have hxnn : (0:ℝ) ≤ ((n:ℝ)+1) * f x := mul_nonneg (by positivity) (hf0 x)
    have : (0:ℤ) ≤ ⌊((n:ℝ)+1) * f x⌋ := by
      have := Int.floor_mono hxnn
      simpa using this
    unfold meshWeight
    rw [hx] at this
    positivity
  rw [← neg_nonpos]
  apply IsArchimedeanOrderUnit.le_zero_of_forall_pos_smul_one_le
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (integral_tendsto hf hM μ) ε hε
  have hstep : -(integral hf hM μ) ≤ simpleIntegral μ (meshWeight M N) (meshPiece f M N)
      (isPartition_meshPiece hf hM N) - integral hf hM μ := by
    have h0 := hmesh_nonneg N
    calc -(integral hf hM μ) = (0 : E) - integral hf hM μ := (zero_sub _).symm
      _ ≤ simpleIntegral μ (meshWeight M N) (meshPiece f M N) (isPartition_meshPiece hf hM N)
          - integral hf hM μ := sub_le_sub_right h0 _
  have hnorm : orderUnitNorm (simpleIntegral μ (meshWeight M N) (meshPiece f M N)
      (isPartition_meshPiece hf hM N) - integral hf hM μ) < ε := by
    have := hN N le_rfl
    rwa [dist_eq_orderUnitNorm] at this
  calc -(integral hf hM μ) ≤ simpleIntegral μ (meshWeight M N) (meshPiece f M N)
        (isPartition_meshPiece hf hM N) - integral hf hM μ := hstep
    _ ≤ ε • (1 : E) := le_smul_one_of_orderUnitNorm_lt hnorm

include hf hM in
/-- **Additivity.** `integral (f + g) = integral f + integral g`, built by combining the two
canonical mesh sequences into one admissible sequence for `f + g` (pieces the pairwise
intersections, weights the pointwise sums — `simpleValue_add_inter` for the uniform bound,
`simpleIntegral_add_simpleIntegral` for the exact algebraic identity) and matching limits: the
combined sequence tends to `integral hfg hMfg μ` by `tendsto_of_uniformly_approximating`, and its
terms equal `mesh_f + mesh_g` exactly at every stage, so it also tends to
`integral f + integral g` (continuity of `+`, free in any normed group). -/
theorem integral_add {g : Ω → ℝ} (hg : Measurable g) {M' : ℝ} (hM' : ∀ x, |g x| ≤ M')
    {hfg : Measurable (f + g)} {hMfg : ∀ x, |(f + g) x| ≤ M + M'} (μ : EffectValuedMeasure Ω E) :
    integral hfg hMfg μ = integral hf hM μ + integral hg hM' μ := by
  set comb : ∀ n : ℕ, MeshIndex M n × MeshIndex M' n → ℝ :=
    fun n p => meshWeight M n p.1 + meshWeight M' n p.2 with hcomb_def
  set combPiece : ∀ n : ℕ, MeshIndex M n × MeshIndex M' n → Set Ω :=
    fun n p => meshPiece f M n p.1 ∩ meshPiece g M' n p.2 with hcombPiece_def
  have hcombPart : ∀ n, IsPartition (combPiece n) := fun n =>
    isPartition_inter (isPartition_meshPiece hf hM n) (isPartition_meshPiece hg hM' n)
  have key1 : Filter.Tendsto (fun n => simpleIntegral μ (comb n) (combPiece n) (hcombPart n))
      atTop (𝓝 (integral hfg hMfg μ)) := by
    apply tendsto_of_uniformly_approximating hfg hMfg μ hcombPart (ε := fun n => 2 / ((n:ℝ)+1))
      (fun n => by positivity)
    · simpa [div_eq_mul_inv] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    · intro n x
      have hval : simpleValue (meshWeight M n) (meshPiece f M n) x
          + simpleValue (meshWeight M' n) (meshPiece g M' n) x
          = simpleValue (comb n) (combPiece n) x :=
        simpleValue_add_inter (isPartition_meshPiece hf hM n) (isPartition_meshPiece hg hM' n) x
      have h1 := abs_simpleValue_meshWeight_meshPiece_sub_le hf hM n x
      have h2 := abs_simpleValue_meshWeight_meshPiece_sub_le hg hM' n x
      rw [← hval]
      have hregroup : simpleValue (meshWeight M n) (meshPiece f M n) x
            + simpleValue (meshWeight M' n) (meshPiece g M' n) x - (f + g) x
          = (simpleValue (meshWeight M n) (meshPiece f M n) x - f x)
            + (simpleValue (meshWeight M' n) (meshPiece g M' n) x - g x) := by
        simp only [Pi.add_apply]; ring
      rw [hregroup]
      calc |(simpleValue (meshWeight M n) (meshPiece f M n) x - f x)
            + (simpleValue (meshWeight M' n) (meshPiece g M' n) x - g x)|
          ≤ |simpleValue (meshWeight M n) (meshPiece f M n) x - f x|
              + |simpleValue (meshWeight M' n) (meshPiece g M' n) x - g x| := abs_add_le _ _
        _ ≤ 1 / ((n:ℝ)+1) + 1 / ((n:ℝ)+1) := add_le_add h1 h2
        _ = 2 / ((n:ℝ)+1) := by ring
  have key2 : Filter.Tendsto (fun n => simpleIntegral μ (comb n) (combPiece n) (hcombPart n))
      atTop (𝓝 (integral hf hM μ + integral hg hM' μ)) := by
    have heq : ∀ n, simpleIntegral μ (comb n) (combPiece n) (hcombPart n)
        = simpleIntegral μ (meshWeight M n) (meshPiece f M n) (isPartition_meshPiece hf hM n)
          + simpleIntegral μ (meshWeight M' n) (meshPiece g M' n)
              (isPartition_meshPiece hg hM' n) :=
      fun n => (simpleIntegral_add_simpleIntegral μ _ _).symm
    simp_rw [heq]
    exact (integral_tendsto hf hM μ).add (integral_tendsto hg hM' μ)
  exact tendsto_nhds_unique key1 key2

include hf hM in
/-- **Homogeneity.** `integral (c • f) = c • integral f`, built from the canonical mesh sequence
for `f` with weights rescaled by `c` (same partition, so `simpleIntegral_smul` gives the exact
algebraic identity at every stage, no refinement needed); matching limits needs scalar
multiplication's continuity, established from `orderUnitNorm_smul_le` since no `NormedSpace ℝ E`
instance is assumed at this generality. -/
theorem integral_smul (c : ℝ) {hcf : Measurable (c • f)} {hMcf : ∀ x, |(c • f) x| ≤ |c| * M}
    (μ : EffectValuedMeasure Ω E) : integral hcf hMcf μ = c • integral hf hM μ := by
  have key1 : Filter.Tendsto (fun n => c • simpleIntegral μ (meshWeight M n) (meshPiece f M n)
      (isPartition_meshPiece hf hM n)) atTop (𝓝 (integral hcf hMcf μ)) := by
    have heq : ∀ n, c • simpleIntegral μ (meshWeight M n) (meshPiece f M n)
        (isPartition_meshPiece hf hM n)
        = simpleIntegral μ (c • meshWeight M n) (meshPiece f M n) (isPartition_meshPiece hf hM n) :=
      fun n => (simpleIntegral_smul μ c _ _ _).symm
    simp_rw [heq]
    apply tendsto_of_uniformly_approximating hcf hMcf μ
      (hs := fun n => isPartition_meshPiece hf hM n) (ε := fun n => |c| / ((n:ℝ)+1))
      (fun n => by positivity)
    · simpa [div_eq_mul_inv] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul |c|
    · intro n x
      have h1 := abs_simpleValue_meshWeight_meshPiece_sub_le hf hM n x
      rw [simpleValue_smul, show (c • f) x = c * f x by simp]
      calc |c * simpleValue (meshWeight M n) (meshPiece f M n) x - c * f x|
          = |c| * |simpleValue (meshWeight M n) (meshPiece f M n) x - f x| := by
            rw [← mul_sub, abs_mul]
        _ ≤ |c| * (1 / ((n:ℝ)+1)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
        _ = |c| / ((n:ℝ)+1) := by ring
  have key2 : Filter.Tendsto (fun n => c • simpleIntegral μ (meshWeight M n) (meshPiece f M n)
      (isPartition_meshPiece hf hM n)) atTop (𝓝 (c • integral hf hM μ)) :=
    tendsto_const_smul_of_tendsto c (integral_tendsto hf hM μ)
  exact tendsto_nhds_unique key1 key2

end Definition

end EffectValuedMeasure
