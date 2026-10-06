/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Measurement.BornRule
public import PhyslibAlpha.ProbabilisticTheory.Measurement.BoundedIntegral

/-!

# Channels and integrals

Normal channels commute with integration against effect-valued measures.

## i. Overview

A normal channel maps an effect-valued measure to an effect-valued measure, and it commutes with
integration of bounded functions.

## ii. Key results

- `EffectValuedMeasure.map_simpleIntegral` : for simple functions.
- `EffectValuedMeasure.map_integral` : for bounded measurable functions.

## iii. Table of contents

- A. Simple integrals
- B. Bounded integrals

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace EffectValuedMeasure

/-! ## A. Simple integrals -/

section SimpleNaturality

variable {Ω E F : Type*} [MeasurableSpace Ω] [OrderUnitSpace E] [OrderUnitSpace F]

/-- Pushing an effect-valued measure through a normal channel commutes with its simple integral. -/
lemma map_simpleIntegral (μ : EffectValuedMeasure Ω E) (φ : Channel E F) (hφ : φ.IsNormal)
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (s : ι → Set Ω) (hs : IsPartition s) :
    φ (simpleIntegral μ c s hs) = simpleIntegral (μ.map φ hφ) c s hs := by
  simp only [simpleIntegral, map_sum, map_smul, coe_map_apply]

end SimpleNaturality

/-! ## B. Bounded integrals -/

section BoundedNaturality

variable {Ω E F : Type*} [MeasurableSpace Ω] [ArchimedeanOrderUnitSpace E]
  [ArchimedeanOrderUnitSpace F]

open Filter Topology ArchimedeanOrderUnitSpace

@[nolint docBlame]
noncomputable local instance instNormedAddCommGroupE : NormedAddCommGroup E :=
  ArchimedeanOrderUnitSpace.orderUnitNormedAddCommGroup

@[nolint docBlame]
noncomputable local instance instNormedAddCommGroupF : NormedAddCommGroup F :=
  ArchimedeanOrderUnitSpace.orderUnitNormedAddCommGroup

variable [CompleteSpace (WithOrderUnitNorm E)] [CompleteSpace (WithOrderUnitNorm F)]

/-- A normal channel commutes with the bounded effect-valued integral.  The only analytic input is
order-unit contractivity of a unital positive map; normality is used solely to make `μ.map φ hφ`
an effect-valued measure. -/
lemma map_integral {f : Ω → ℝ} {M : ℝ} (hf : Measurable f) (hM : ∀ x, |f x| ≤ M)
    (μ : EffectValuedMeasure Ω E) (φ : Channel E F) (hφ : φ.IsNormal) :
    φ (integral hf hM μ) = integral hf hM (μ.map φ hφ) := by
  let φc : E →L[ℝ] F := φ.toLinearMap.mkContinuous 1 (by
    intro x
    change orderUnitNorm (φ x) ≤ 1 * orderUnitNorm x
    simpa using φ.orderUnitNorm_map_le x)
  have hmap : Tendsto
      (fun n : ℕ => φ (simpleIntegral μ (meshWeight M n) (meshPiece f M n)
        (isPartition_meshPiece hf hM n))) atTop (𝓝 (φ (integral hf hM μ))) := by
    have h := (φc.continuous.tendsto (integral hf hM μ)).comp (integral_tendsto hf hM μ)
    change Tendsto (fun n : ℕ => φc (simpleIntegral μ (meshWeight M n) (meshPiece f M n)
      (isPartition_meshPiece hf hM n))) atTop (𝓝 (φc (integral hf hM μ)))
    exact h.congr fun _ => rfl
  have htarget := integral_tendsto hf hM (μ.map φ hφ)
  apply tendsto_nhds_unique ?_ htarget
  exact hmap.congr fun n => map_simpleIntegral μ φ hφ (meshWeight M n) (meshPiece f M n)
    (isPartition_meshPiece hf hM n)

end BoundedNaturality

end EffectValuedMeasure

end ProbabilisticTheory
