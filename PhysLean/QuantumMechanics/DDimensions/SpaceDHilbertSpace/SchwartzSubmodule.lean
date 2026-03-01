/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import PhysLean.QuantumMechanics.DDimensions.SpaceDHilbertSpace.Basic
/-!

# Schwartz submodule of the Hilbert space

-/

namespace QuantumMechanics
namespace SpaceDHilbertSpace

noncomputable section

open MeasureTheory
open InnerProductSpace
open SchwartzMap

/-- The continuous linear map including Schwartz functions into `SpaceDHilbertSpace d`. -/
def schwartzIncl {d : ℕ} : 𝓢(Space d, ℂ) →L[ℂ] SpaceDHilbertSpace d := toLpCLM ℂ (E := Space d) ℂ 2

lemma schwartzIncl_injective {d : ℕ} : Function.Injective (schwartzIncl (d := d)) :=
  injective_toLp (E := Space d) 2

lemma schwartzIncl_coe_ae {d : ℕ} (f : 𝓢(Space d, ℂ)) : f.1 =ᵐ[volume] (schwartzIncl f) :=
  (coeFn_toLp f 2).symm

lemma schwartzIncl_inner {d : ℕ} (f g : 𝓢(Space d, ℂ)) :
    ⟪schwartzIncl f, schwartzIncl g⟫_ℂ = ∫ x : Space d, starRingEnd ℂ (f x) * g x := by
  apply integral_congr_ae
  filter_upwards [schwartzIncl_coe_ae f, schwartzIncl_coe_ae g] with _ hf hg
  rw [← hf, ← hg, RCLike.inner_apply, mul_comm]
  rfl

/-- The submodule of `SpaceDHilbertSpace d` consisting of Schwartz functions. -/
abbrev schwartzSubmodule (d : ℕ) := (schwartzIncl (d := d)).range

lemma schwartzSubmodule_dense {d : ℕ} :
    Dense (schwartzSubmodule d : Set (SpaceDHilbertSpace d)) :=
  denseRange_toLpCLM ENNReal.top_ne_ofNat.symm

end
end SpaceDHilbertSpace
end QuantumMechanics
