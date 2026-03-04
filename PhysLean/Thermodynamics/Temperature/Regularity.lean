/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be, Matteo Cipollina, Tan-Phuoc-Hung Le, Joseph Tooby-Smith
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import PhysLean.Thermodynamics.Temperature.Basic

/-!
# Regularity of the inverse temperature map

This file proves continuity and differentiability properties of
`PositiveTemperature.ofβ : ℝ>0 → PositiveTemperature`.

## Main results

* `PositiveTemperature.ofβ_continuous` : `ofβ` is continuous.
* `PositiveTemperature.ofβ_differentiableOn` : the real-valued formula underlying `ofβ` is
  differentiable on `(0, ∞)`.
-/

open NNReal

namespace PositiveTemperature
open Constants

/-! ### Regularity of `ofβ` -/

/-- The function `ofβ` is continuous. -/
lemma ofβ_continuous : Continuous ofβ := by
  have h_ind : Topology.IsInducing (fun (T : PositiveTemperature) => (T : ℝ)) :=
    Topology.IsInducing.subtypeVal.comp
      ((show Topology.IsInducing (fun (T : Temperature) => T.val) from ⟨rfl⟩).comp
        Topology.IsInducing.subtypeVal)
  apply h_ind.continuous_iff.mpr
  simp only [PositiveTemperature.toReal, Temperature.toReal]
  exact continuous_const.div₀ (continuous_const.mul continuous_subtype_val)
    (fun (β : ℝ>0) => mul_ne_zero kB_ne_zero (ne_of_gt β.2))

/-- The real-valued formula underlying `ofβ` is differentiable on `(0, ∞)`.
-/
lemma ofβ_differentiableOn :
    DifferentiableOn ℝ (fun (β : ℝ) => (1 : ℝ) / (kB * β)) (Set.Ioi 0) := by
  apply DifferentiableOn.fun_div
  · fun_prop
  · fun_prop
  · intro x hx
    exact mul_ne_zero kB_ne_zero (Set.mem_Ioi.mp hx).ne'

end PositiveTemperature
