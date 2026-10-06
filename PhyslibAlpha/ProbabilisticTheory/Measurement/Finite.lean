/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Measurement.Basic

/-!
# Measurements with finitely many outcomes

Measurements with finitely many outcomes are the families of effects summing to `1`.

## i. Overview

On a finite discrete outcome space, every observable of the outcome is a combination of the
indicators of single outcomes. A measurement is therefore determined by the effects of its single
outcomes, and these add up to `1`. Conversely, a family of effects adding up to `1` is a
measurement: send the observable `f` to `∑ x, f x • a x`. Normality is automatic, since an
increasing sequence of functions on finitely many points converges uniformly; this uses that the
system is Archimedean.

## ii. Key results

- `BoundedMeasurable.eq_sum_indicator` : an observable of a finite classical system is a combination
  of point indicators.
- `UnitalPositiveLinearMap.isNormal_of_fintype` : a channel from a finite classical system into an
  Archimedean system is normal.
- `Measurement.ofAtoms` : the measurement of a family of effects adding up to `1`.
- `Measurement.eq_ofAtoms` : a measurement with finitely many outcomes is determined by the effects
  of its outcomes.

## iii. Table of contents

- A. Observables of a finite classical system
- B. Normality is automatic
- C. Measurements from their outcome effects

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

open BoundedMeasurable UnitalPositiveLinearMap

variable {Ω E : Type*} [MeasurableSpace Ω] [Fintype Ω] [MeasurableSingletonClass Ω]

/-! ## A. Observables of a finite classical system -/

end ProbabilisticTheory

namespace BoundedMeasurable
open ProbabilisticTheory
open BoundedMeasurable UnitalPositiveLinearMap
variable {Ω E : Type*} [MeasurableSpace Ω] [Fintype Ω] [MeasurableSingletonClass Ω]

/-- An observable of a finite classical system is a combination of point indicators. -/
lemma eq_sum_indicator (f : BoundedMeasurable Ω) :
    f = ∑ x, f x • indicator {x} (measurableSet_singleton x) :=
  BoundedMeasurable.ext fun y => by
    classical
    simp [BoundedMeasurable.sum_apply, Set.indicator_apply]

/-- The point indicators add up to the unit. -/
lemma sum_indicator_singleton :
    ∑ x, indicator {x} (measurableSet_singleton x) = (1 : BoundedMeasurable Ω) := by
  simpa using (eq_sum_indicator (1 : BoundedMeasurable Ω)).symm

end BoundedMeasurable

namespace ProbabilisticTheory

open BoundedMeasurable UnitalPositiveLinearMap
variable {Ω E : Type*} [MeasurableSpace Ω] [Fintype Ω] [MeasurableSingletonClass Ω]

/-! ## B. Normality is automatic -/

namespace UnitalPositiveLinearMap

variable [ArchimedeanOrderUnitSpace E]

omit [MeasurableSingletonClass Ω] in
/-- An increasing sequence of functions on a finite set comes uniformly close to its least upper
bound. -/
lemma exists_le_add_smul_one {f : ℕ → BoundedMeasurable Ω} (hf : Monotone f)
    {g : BoundedMeasurable Ω} (hg : IsLUB (Set.range f) g) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, g ≤ f n + ε • 1 := by
  have h (x : Ω) : ∃ n, g x - ε < f n x := by
    obtain ⟨_, ⟨n, rfl⟩, hn, -⟩ := (isLUB_range_iff.1 hg x).exists_between (sub_lt_self _ hε)
    exact ⟨n, hn⟩
  choose n hn using h
  refine ⟨Finset.univ.sup n, le_def.2 fun x => ?_⟩
  have := le_def.1 (hf (Finset.le_sup (f := n) (Finset.mem_univ x))) x
  simp only [BoundedMeasurable.add_apply, BoundedMeasurable.smul_apply,
    BoundedMeasurable.one_apply, mul_one]
  linarith [hn x]

omit [MeasurableSingletonClass Ω] in
/-- A channel from a finite classical system into an Archimedean system is normal. -/
lemma isNormal_of_fintype (Φ : Channel (BoundedMeasurable Ω) E) : Φ.IsNormal := by
  intro f g hf hg
  refine ⟨Set.forall_mem_range.2 fun n => Φ.monotone' (hg.1 ⟨n, rfl⟩), fun b hb => ?_⟩
  refine sub_nonpos.1 (ArchimedeanOrderUnitSpace.le_zero_of_forall_pos_smul_one_le _
    fun ε hε => ?_)
  obtain ⟨n, hn⟩ := exists_le_add_smul_one hf hg hε
  have h := OrderHomClass.mono Φ hn
  simp only [map_add, map_smul, map_one] at h
  have hb' : Φ (f n) ≤ b := hb ⟨n, rfl⟩
  rw [sub_le_iff_le_add]
  exact h.trans (by rw [add_comm]; gcongr)

end UnitalPositiveLinearMap

/-! ## C. Measurements from their outcome effects -/

namespace Measurement

variable [ArchimedeanOrderUnitSpace E]

omit [MeasurableSingletonClass Ω] in
/-- The channel `f ↦ ∑ x, f x • a x` of a family of effects adding up to `1`. -/
noncomputable def atomsChannel (a : Ω → Effect E) (ha : ∑ x, (a x : E) = 1) :
    Channel (BoundedMeasurable Ω) E :=
  ofLinearMap
    { toFun f := ∑ x, f x • (a x : E)
      map_add' f g := by simp [add_smul, Finset.sum_add_distrib]
      map_smul' c f := by simp [Finset.smul_sum, smul_smul] }
    (fun _ hf => Finset.sum_nonneg fun x _ => smul_nonneg (le_def.1 hf x) (a x).2.1)
    (by simpa using ha)

omit [MeasurableSingletonClass Ω] in
/-- The measurement of a family of effects adding up to `1`: the outcome `x` has effect `a x`. -/
noncomputable def ofAtoms (a : Ω → Effect E) (ha : ∑ x, (a x : E) = 1) : Measurement Ω E where
  toChannel := atomsChannel a ha
  isNormal := isNormal_of_fintype _

omit [MeasurableSingletonClass Ω] in
lemma ofAtoms_toChannel_apply (a : Ω → Effect E) (ha : ∑ x, (a x : E) = 1)
    (f : BoundedMeasurable Ω) : (ofAtoms a ha).toChannel f = ∑ x, f x • (a x : E) := rfl

omit [MeasurableSingletonClass Ω] in
open Classical in
lemma coe_ofAtoms_apply (a : Ω → Effect E) (ha : ∑ x, (a x : E) = 1) (s : Set Ω)
    (hs : MeasurableSet s) : (ofAtoms a ha s hs : E) = ∑ x, if x ∈ s then (a x : E) else 0 := by
  rw [coe_apply, ofAtoms_toChannel_apply]
  exact Finset.sum_congr rfl fun x _ => by by_cases hx : x ∈ s <;> simp [hx]

omit [MeasurableSingletonClass Ω] in
@[simp, nolint simpNF]
lemma coe_ofAtoms_singleton (a : Ω → Effect E) (ha : ∑ x, (a x : E) = 1) (x : Ω)
    (hx : MeasurableSet {x}) : (ofAtoms a ha {x} hx : E) = a x := by
  classical
  rw [coe_ofAtoms_apply]
  simp

/-- The effects of the outcomes of a measurement add up to `1`. -/
lemma sum_singleton (M : Measurement Ω E) :
    ∑ x, (M {x} (measurableSet_singleton x) : E) = 1 := by
  simp only [coe_apply, ← map_sum, BoundedMeasurable.sum_indicator_singleton, map_one]

/-- A measurement with finitely many outcomes is the measurement of its outcome effects. -/
lemma eq_ofAtoms (M : Measurement Ω E) :
    M = ofAtoms (fun x => M {x} (measurableSet_singleton x)) M.sum_singleton :=
  Measurement.ext <| UnitalPositiveLinearMap.ext fun f => by
    conv_lhs => rw [BoundedMeasurable.eq_sum_indicator f]
    simp [ofAtoms_toChannel_apply, map_sum, map_smul]

/-- Two measurements with finitely many outcomes agree when their outcome effects agree. -/
lemma ext_of_singleton {M N : Measurement Ω E}
    (h : ∀ x, M {x} (measurableSet_singleton x) = N {x} (measurableSet_singleton x)) :
    M = N := by
  rw [M.eq_ofAtoms, N.eq_ofAtoms]
  simp only [h]

end Measurement

end ProbabilisticTheory
