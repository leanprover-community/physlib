/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be, Matteo Cipollina, Tan-Phuoc-Hung Le, Joseph Tooby-Smith
-/
import PhysLean.Thermodynamics.Temperature.Basic

/-!
# Convergence of inverse temperature maps

This file proves that as the inverse temperature `β` tends to infinity,
the temperature `ofβ β` tends to zero.

## Main results

* `PositiveTemperature.eventually_pos_ofβ`: `ofβ` always produces positive temperatures.
* `PositiveTemperature.tendsto_toReal_ofβ_atTop` : The real representation of `ofβ β`
  tends to `0` as `β → ∞`.
* `PositiveTemperature.tendsto_ofβ_atTop` : `ofβ β` tends to `0` from above as `β → ∞`.
-/

open NNReal

namespace PositiveTemperature
open Constants
open Filter Topology

/-- Lemma for `PositiveTemperature`:

The function `ofβ` will eventually produce positive temperatures as `β` tends to infinity in `ℝ>0`.
-/
lemma eventually_pos_ofβ : ∀ᶠ (β : ℝ>0) in atTop, (PositiveTemperature.ofβ β : ℝ) > 0 := by
  filter_upwards [] with β
  exact PositiveTemperature.zero_lt_toReal _

/-- Helper lemma for `PositiveTemperature`:

As `b` tends to infinity in `ℝ>0`, the function value `1 / (a * b)` tends to `0`.
-/
private lemma tendsto_const_inv_mul_atTop (a : ℝ) (h_a_pos : 0 < a) :
    Tendsto (fun (b : ℝ>0) => (1 : ℝ) / (a * (b : ℝ))) atTop (𝓝 (0 : ℝ)) := by
  have h_val_atTop : Tendsto (Subtype.val : ℝ>0 → ℝ) atTop atTop :=
    Filter.tendsto_atTop_atTop_of_monotone (fun a b h => h)
    (fun b => ⟨⟨max b 1, lt_max_of_lt_right one_pos⟩, le_max_left _ _⟩)
  simp_rw [one_div]
  exact (Filter.Tendsto.const_mul_atTop h_a_pos h_val_atTop).inv_tendsto_atTop

/-- Lemma for `PositiveTemperature`:

As the inverse temperature `β` tends to infinity,
the real-valued representation of the temperature `ofβ β` tends to `0`
in the sense of the metric space distance.
-/
lemma tendsto_toReal_ofβ_atTop :
    Tendsto (fun (β : ℝ>0) => (PositiveTemperature.ofβ β : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  exact tendsto_const_inv_mul_atTop kB kB_pos

/-- Lemma for `PositiveTemperature`:

As the inverse temperature `β` tends to infinity,
the real-valued representation of the temperature `ofβ β`
tends to `0` from above (within the interval `(0, ∞)`).
-/
lemma tendsto_ofβ_atTop : Tendsto (fun (β : ℝ>0) => (PositiveTemperature.ofβ β : ℝ))
    atTop (nhdsWithin 0 (Set.Ioi 0)) := by
  have h_tendsto_nhds_zero := tendsto_toReal_ofβ_atTop
  have h_tendsto_principal_Ioi : Tendsto (fun (β : ℝ>0) => (PositiveTemperature.ofβ β : ℝ))
    atTop (𝓟 (Set.Ioi (0 : ℝ))) := tendsto_principal.mpr eventually_pos_ofβ
  have h_tendsto_inf :
      Tendsto (fun (β : ℝ>0) =>
        (PositiveTemperature.ofβ β : ℝ))
        atTop
        ((nhds (0 : ℝ)) ⊓ 𝓟 (Set.Ioi (0 : ℝ))) :=
    tendsto_inf.mpr
      ⟨h_tendsto_nhds_zero, h_tendsto_principal_Ioi⟩
  simpa [nhdsWithin] using h_tendsto_inf

end PositiveTemperature
