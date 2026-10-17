/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Algebra.Order.Module.Defs

/-!
# Bounded measurable functions

The vector lattice of bounded measurable functions, staircase approximation and integrability.

## i. Overview

The bounded measurable functions on a space `Ω` are the observables of a classical system with
outcomes in `Ω`. They form a vector lattice under the pointwise operations. The least upper bound of
a sequence bounded above is its pointwise supremum. Every bounded measurable function is uniformly
approximated from below by a staircase, a finite combination of indicator functions, and it is
integrable against every finite measure.

## ii. Key results

- `BoundedMeasurable Ω` is the space of bounded measurable real functions on `Ω`.
- `BoundedMeasurable.isLUB_range_iff` proves that least upper bounds of sequences are pointwise.
- `BoundedMeasurable.abs_sub_staircase_le` proves that the staircase approximation is uniform.

## iii. Table of contents

- A. The vector space
- B. The lattice order
- C. Least upper bounds of sequences
- D. Indicators and staircases
- E. Integrability

## iv. References

* None.

-/

@[expose] public section

open Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-!

## A. The vector space

-/

variable (Ω) in
/-- The bounded measurable real functions on `Ω`, as a subspace of all real functions. -/
def boundedMeasurableSubmodule : Submodule ℝ (Ω → ℝ) where
  carrier := {f | Measurable f ∧ ∃ C, ∀ x, |f x| ≤ C}
  add_mem' := fun ⟨hf, C, hC⟩ ⟨hg, D, hD⟩ =>
    ⟨hf.add hg, C + D, fun x => (abs_add_le _ _).trans (add_le_add (hC x) (hD x))⟩
  zero_mem' := ⟨measurable_const, 0, fun _ => by simp⟩
  smul_mem' c _ := fun ⟨hf, C, hC⟩ => ⟨hf.const_smul c, |c| * C, fun x => by
    rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)⟩

variable (Ω) in
/-- The bounded measurable real functions on `Ω`. -/
def BoundedMeasurable : Type _ := boundedMeasurableSubmodule Ω

namespace BoundedMeasurable

instance : AddCommGroup (BoundedMeasurable Ω) :=
  inferInstanceAs (AddCommGroup (boundedMeasurableSubmodule Ω))

instance : Module ℝ (BoundedMeasurable Ω) :=
  inferInstanceAs (Module ℝ (boundedMeasurableSubmodule Ω))

instance : FunLike (BoundedMeasurable Ω) Ω ℝ where
  coe f := (f : boundedMeasurableSubmodule Ω).1
  coe_injective _ _ h := Subtype.ext h

@[ext] lemma ext {f g : BoundedMeasurable Ω} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

lemma measurable (f : BoundedMeasurable Ω) : Measurable f := (f : boundedMeasurableSubmodule Ω).2.1

lemma exists_bound (f : BoundedMeasurable Ω) : ∃ C, ∀ x, |f x| ≤ C :=
  (f : boundedMeasurableSubmodule Ω).2.2

/-- A bounded measurable function. -/
def mk (f : Ω → ℝ) (hf : Measurable f) (hb : ∃ C, ∀ x, |f x| ≤ C) : BoundedMeasurable Ω :=
  (⟨f, hf, hb⟩ : boundedMeasurableSubmodule Ω)

@[simp] lemma mk_apply (f : Ω → ℝ) (hf) (hb) (x : Ω) : mk f hf hb x = f x := rfl
@[simp] lemma zero_apply (x : Ω) : (0 : BoundedMeasurable Ω) x = 0 := rfl
@[simp] lemma add_apply (f g : BoundedMeasurable Ω) (x : Ω) : (f + g) x = f x + g x := rfl
@[simp] lemma neg_apply (f : BoundedMeasurable Ω) (x : Ω) : (-f) x = -f x := rfl
@[simp] lemma sub_apply (f g : BoundedMeasurable Ω) (x : Ω) : (f - g) x = f x - g x := rfl
@[simp] lemma smul_apply (c : ℝ) (f : BoundedMeasurable Ω) (x : Ω) : (c • f) x = c * f x := rfl

@[simp] lemma nsmul_apply (n : ℕ) (f : BoundedMeasurable Ω) (x : Ω) : (n • f) x = n * f x := by
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_apply]

lemma sum_apply {ι : Type*} (t : Finset ι) (f : ι → BoundedMeasurable Ω) (x : Ω) :
    (∑ i ∈ t, f i) x = ∑ i ∈ t, f i x :=
  map_sum (⟨⟨fun f : BoundedMeasurable Ω => f x, rfl⟩, fun _ _ => rfl⟩ :
    BoundedMeasurable Ω →+ ℝ) f t

instance : One (BoundedMeasurable Ω) := ⟨mk 1 measurable_const ⟨1, fun _ => by simp⟩⟩

@[simp] lemma one_apply (x : Ω) : (1 : BoundedMeasurable Ω) x = 1 := rfl

/-!

## B. The lattice order

-/

instance : LE (BoundedMeasurable Ω) := ⟨fun f g => ∀ x, f x ≤ g x⟩
instance : LT (BoundedMeasurable Ω) := ⟨fun f g => f ≤ g ∧ ¬ g ≤ f⟩

instance : Max (BoundedMeasurable Ω) := ⟨fun f g => mk (fun x => max (f x) (g x))
  (f.measurable.max g.measurable) <| by
    obtain ⟨C, hC⟩ := f.exists_bound
    obtain ⟨D, hD⟩ := g.exists_bound
    exact ⟨max C D, fun x => (abs_max_le_max_abs_abs).trans (max_le_max (hC x) (hD x))⟩⟩

instance : Min (BoundedMeasurable Ω) := ⟨fun f g => mk (fun x => min (f x) (g x))
  (f.measurable.min g.measurable) <| by
    obtain ⟨C, hC⟩ := f.exists_bound
    obtain ⟨D, hD⟩ := g.exists_bound
    exact ⟨max C D, fun x => (abs_min_le_max_abs_abs).trans (max_le_max (hC x) (hD x))⟩⟩

instance : Lattice (BoundedMeasurable Ω) :=
  DFunLike.coe_injective.lattice _ Iff.rfl lt_iff_le_not_ge (fun _ _ => rfl) fun _ _ => rfl

lemma le_def {f g : BoundedMeasurable Ω} : f ≤ g ↔ ∀ x, f x ≤ g x := Iff.rfl

@[simp] lemma sup_apply (f g : BoundedMeasurable Ω) (x : Ω) : (f ⊔ g) x = max (f x) (g x) := rfl
@[simp] lemma inf_apply (f g : BoundedMeasurable Ω) (x : Ω) : (f ⊓ g) x = min (f x) (g x) := rfl

@[simp] lemma posPart_apply (f : BoundedMeasurable Ω) (x : Ω) : f⁺ x = max (f x) 0 := rfl
@[simp] lemma negPart_apply (f : BoundedMeasurable Ω) (x : Ω) : f⁻ x = max (-f x) 0 := rfl

instance : IsOrderedAddMonoid (BoundedMeasurable Ω) where
  add_le_add_left _ _ h _ := le_def.2 fun x => by simpa using le_def.1 h x

instance : PosSMulMono ℝ (BoundedMeasurable Ω) where
  smul_le_smul_of_nonneg_left c hc _ _ h := le_def.2 fun x => by
    simpa using mul_le_mul_of_nonneg_left (le_def.1 h x) hc

/-!

## C. Least upper bounds of sequences

-/

/-- The pointwise supremum of a sequence bounded above by `g`. -/
noncomputable def iSup' (f : ℕ → BoundedMeasurable Ω) (g : BoundedMeasurable Ω)
    (hfg : ∀ n, f n ≤ g) : BoundedMeasurable Ω :=
  mk (fun x => ⨆ n, f n x) (Measurable.iSup fun n => (f n).measurable) <| by
    obtain ⟨C, hC⟩ := (f 0).exists_bound
    obtain ⟨D, hD⟩ := g.exists_bound
    refine ⟨C + D, fun x => abs_le.2 ⟨?_, ?_⟩⟩
    · show -(C + D) ≤ ⨆ n, f n x
      have h1 : f 0 x ≤ ⨆ n, f n x :=
        le_ciSup (f := fun n => f n x) ⟨g x, forall_mem_range.2 fun n => le_def.1 (hfg n) x⟩ 0
      linarith [neg_abs_le (f 0 x), hC x, abs_nonneg (g x), hD x]
    · show ⨆ n, f n x ≤ C + D
      have h2 : ⨆ n, f n x ≤ g x := ciSup_le fun n => le_def.1 (hfg n) x
      linarith [le_abs_self (g x), hD x, abs_nonneg (f 0 x), hC x]

/-- A sequence has least upper bound `g` exactly when `g` is its pointwise supremum. -/
lemma isLUB_range_iff {f : ℕ → BoundedMeasurable Ω} {g : BoundedMeasurable Ω} :
    IsLUB (range f) g ↔ ∀ x, IsLUB (range fun n => f n x) (g x) := by
  constructor
  · intro h x
    have hfg n : f n ≤ g := h.1 ⟨n, rfl⟩
    refine ⟨forall_mem_range.2 fun n => le_def.1 (hfg n) x, fun b hb => ?_⟩
    have hs : g ≤ iSup' f g hfg := h.2 <| forall_mem_range.2 fun n => le_def.2 fun y =>
      le_ciSup (f := fun m => f m y) ⟨g y, forall_mem_range.2 fun m => le_def.1 (hfg m) y⟩ n
    exact (le_def.1 hs x).trans (ciSup_le fun n => hb ⟨n, rfl⟩)
  · intro h
    exact ⟨forall_mem_range.2 fun n => le_def.2 fun x => (h x).1 ⟨n, rfl⟩, fun b hb =>
      le_def.2 fun x => (h x).2 (forall_mem_range.2 fun n => le_def.1 (hb ⟨n, rfl⟩) x)⟩

/-!

## D. Indicators and staircases

-/

/-- The indicator function of a measurable set. -/
noncomputable def indicator (s : Set Ω) (hs : MeasurableSet s) : BoundedMeasurable Ω :=
  mk (s.indicator 1) (measurable_one.indicator hs) ⟨1, fun x => by
    by_cases hx : x ∈ s <;> simp [hx]⟩

@[simp] lemma indicator_apply (s : Set Ω) (hs : MeasurableSet s) (x : Ω) :
    indicator s hs x = s.indicator 1 x := rfl

lemma indicator_nonneg (s : Set Ω) (hs : MeasurableSet s) : 0 ≤ indicator s hs :=
  le_def.2 fun x => by by_cases hx : x ∈ s <;> simp [hx]

lemma indicator_le_one (s : Set Ω) (hs : MeasurableSet s) : indicator s hs ≤ 1 :=
  le_def.2 fun x => by by_cases hx : x ∈ s <;> simp [hx]

omit [MeasurableSpace Ω] in
/-- The indicators of disjoint sets sum to the indicator of their union. -/
lemma hasSum_indicator_apply {s : ℕ → Set Ω} (hd : Pairwise (Function.onFun Disjoint s)) (x : Ω) :
    HasSum (fun n => (s n).indicator (1 : Ω → ℝ) x) ((⋃ n, s n).indicator 1 x) := by
  by_cases hx : ∃ k, x ∈ s k
  · obtain ⟨k, hk⟩ := hx
    rw [indicator_of_mem (mem_iUnion.2 ⟨k, hk⟩)]
    convert hasSum_single (f := fun n => (s n).indicator (1 : Ω → ℝ) x) k fun n hn =>
      indicator_of_notMem (fun h => (hd hn).le_bot ⟨h, hk⟩) _
    simp [hk]
  · push Not at hx
    rw [indicator_of_notMem (by simpa using hx)]
    simp [hx]

/-- The indicators of disjoint measurable sets have the indicator of their union as least upper
bound of their partial sums. -/
lemma isLUB_sum_indicator {s : ℕ → Set Ω} (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (Function.onFun Disjoint s)) :
    IsLUB (range fun N => ∑ n ∈ Finset.range N, indicator (s n) (hs n))
      (indicator (⋃ n, s n) (.iUnion hs)) :=
  isLUB_range_iff.2 fun x => by
    simpa [sum_apply, Function.comp_def] using isLUB_of_tendsto_atTop
      (Finset.sum_mono_set_of_nonneg (f := fun n => (s n).indicator (1 : Ω → ℝ) x)
        (fun n => Set.indicator_nonneg (fun _ _ => zero_le_one) x) |>.comp Finset.range_mono)
      (hasSum_indicator_apply hd x).tendsto_sum_nat

/-- The staircase `⌊N g⌋ / N` below a nonnegative function `g ≤ K`, as a combination of
indicators of superlevel sets. -/
noncomputable def staircase (g : BoundedMeasurable Ω) (N K : ℕ) : BoundedMeasurable Ω :=
  ∑ k ∈ Finset.Icc 1 (N * K), ((N : ℝ)⁻¹) •
    indicator {x | (k : ℝ) / N ≤ g x} (measurableSet_le measurable_const g.measurable)

lemma staircase_apply {g : BoundedMeasurable Ω} {N K : ℕ} (hN : 0 < N) {x : Ω} (h0 : 0 ≤ g x)
    (hK : g x ≤ K) : staircase g N K x = ⌊N * g x⌋₊ / N := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hy : 0 ≤ (N : ℝ) * g x := by positivity
  have hfl : ⌊(N : ℝ) * g x⌋₊ ≤ N * K := Nat.floor_le_of_le (by push_cast; nlinarith)
  have hk (k : ℕ) : (k : ℝ) / N ≤ g x ↔ k ≤ ⌊(N : ℝ) * g x⌋₊ := by
    rw [div_le_iff₀ hN', mul_comm, Nat.le_floor_iff hy]
  have hset : (Finset.Icc 1 (N * K)).filter (fun k : ℕ => (k : ℝ) / N ≤ g x) =
      Finset.Icc 1 ⌊(N : ℝ) * g x⌋₊ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, hk]
    omega
  simp only [staircase, sum_apply, smul_apply, indicator_apply, Set.indicator_apply,
    Set.mem_ofPred_eq, Pi.one_apply, ← Finset.mul_sum, Finset.sum_boole, hset, Nat.card_Icc,
    Nat.add_sub_cancel]
  rw [inv_mul_eq_div]

/-- The staircase approximates a nonnegative bounded measurable function uniformly. -/
lemma abs_sub_staircase_le {g : BoundedMeasurable Ω} {N K : ℕ} (hN : 0 < N) (h0 : 0 ≤ g)
    (hK : ∀ x, g x ≤ K) (x : Ω) : |(g - staircase g N K) x| ≤ (N : ℝ)⁻¹ := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hy : 0 ≤ (N : ℝ) * g x := mul_nonneg hN'.le (le_def.1 h0 x)
  rw [sub_apply, staircase_apply hN (le_def.1 h0 x) (hK x),
    show g x - (⌊(N : ℝ) * g x⌋₊ : ℝ) / N = ((N : ℝ) * g x - ⌊(N : ℝ) * g x⌋₊) / N by
      field_simp,
    abs_div, abs_of_nonneg (sub_nonneg.2 (Nat.floor_le hy)), abs_of_pos hN', div_le_iff₀ hN',
    inv_mul_cancel₀ hN'.ne']
  linarith [Nat.lt_floor_add_one ((N : ℝ) * g x)]

/-!

## E. Integrability

-/

open MeasureTheory

lemma integrable (f : BoundedMeasurable Ω) (μ : Measure Ω) [IsFiniteMeasure μ] :
    Integrable f μ :=
  let ⟨C, hC⟩ := f.exists_bound
  .of_bound f.measurable.aestronglyMeasurable C (.of_forall hC)

end BoundedMeasurable
