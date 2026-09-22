/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.Measurement.MeasurableOutcome
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Effect.BoundedIntegral

/-!

# Naturality of bounded effect-valued integration

A normal channel carries an effect-valued measure to an effect-valued measure.  This file proves
that the already-defined bounded integral commutes with that operation.  The proof is intentionally
at the order-unit/channel level: scalarization by a normal state is a later specialization, not a
second limit argument.

-/

@[expose] public section

namespace EffectValuedMeasure

section BoundedNaturality

variable {Ω E F : Type*} [MeasurableSpace Ω]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]
  [PosSMulMono ℝ E] [One E] [IsArchimedeanOrderUnit E]
  [AddCommGroup F] [PartialOrder F] [IsOrderedAddMonoid F] [Module ℝ F]
  [PosSMulMono ℝ F] [One F] [IsArchimedeanOrderUnit F]

open Filter Topology IsArchimedeanOrderUnit

@[nolint docBlame]
noncomputable local instance instNormedAddCommGroupE : NormedAddCommGroup E :=
  IsArchimedeanOrderUnit.orderUnitNormedAddCommGroup

@[nolint docBlame]
noncomputable local instance instNormedAddCommGroupF : NormedAddCommGroup F :=
  IsArchimedeanOrderUnit.orderUnitNormedAddCommGroup

variable [CompleteSpace E] [CompleteSpace F]

/-- A normal channel commutes with the bounded effect-valued integral.  The only analytic input is
order-unit contractivity of a unital positive map; normality is used solely to make `μ.map φ hφ`
an effect-valued measure. -/
theorem map_integral {f : Ω → ℝ} {M : ℝ} (hf : Measurable f) (hM : ∀ x, |f x| ≤ M)
    (μ : EffectValuedMeasure Ω E) (φ : E →ₚ₁[ℝ] F) (hφ : φ.IsNormal) :
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
