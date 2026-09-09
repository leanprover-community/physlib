/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Channel.Basic

/-!

# Normal channels

## i. Overview

A channel is normal when it preserves suprema of directed sets: its value at a directed supremum
is the supremum of its values on the directed set. This is the extra continuity — beyond mere
positivity — needed to push a countably-additive effect-valued measure forward along a channel and
keep it countably additive (`Measurement/MeasurableOutcome.lean`); it plays the same role for
channels that `Weight.IsNormal` plays for weights.

## ii. Key definitions and results

- `UnitalPositiveLinearMap.IsNormal`
- `UnitalPositiveLinearMap.isNormal_id`, `UnitalPositiveLinearMap.IsNormal.comp`

## iii. Table of contents

- A. Normality
- B. Identity and composition

-/

@[expose] public section

variable {E₁ E₂ E₃ : Type*}
  [AddCommGroup E₁] [PartialOrder E₁] [IsOrderedAddMonoid E₁] [Module ℝ E₁] [PosSMulMono ℝ E₁]
  [One E₁]
  [AddCommGroup E₂] [PartialOrder E₂] [IsOrderedAddMonoid E₂] [Module ℝ E₂] [PosSMulMono ℝ E₂]
  [One E₂]
  [AddCommGroup E₃] [PartialOrder E₃] [IsOrderedAddMonoid E₃] [Module ℝ E₃] [PosSMulMono ℝ E₃]
  [One E₃]

namespace UnitalPositiveLinearMap

/-! ## A. Normality -/

/-- A channel is normal when it carries the supremum of every directed set to the supremum of the
image: it does not "jump" at a limit. -/
def IsNormal (φ : E₁ →ₚ₁[ℝ] E₂) : Prop :=
  ∀ (D : Set E₁) (x : E₁), D.Nonempty → DirectedOn (· ≤ ·) D → IsLUB D x → IsLUB (φ '' D) (φ x)

omit [IsOrderedAddMonoid E₁] [PosSMulMono ℝ E₁] in
/-- The identity channel is normal: the image of a directed set under it is itself. -/
lemma isNormal_id : (UnitalPositiveLinearMap.id ℝ E₁).IsNormal := fun D x _ _ hlub => by
  rwa [show (UnitalPositiveLinearMap.id ℝ E₁) '' D = D from Set.image_id D,
    UnitalPositiveLinearMap.id_apply]

/-! ## B. Identity and composition -/

omit [IsOrderedAddMonoid E₁] [PosSMulMono ℝ E₁] [IsOrderedAddMonoid E₂] [PosSMulMono ℝ E₂]
  [IsOrderedAddMonoid E₃] [PosSMulMono ℝ E₃] in
/-- Normality survives composition: normality is exactly the continuity needed to carry a
directed supremum through each stage of the composite. -/
lemma IsNormal.comp {φ : E₁ →ₚ₁[ℝ] E₂} {ψ : E₂ →ₚ₁[ℝ] E₃} (hφ : φ.IsNormal) (hψ : ψ.IsNormal) :
    (ψ.comp φ).IsNormal := fun D x hD hdirected hlub => by
  have hφD : IsLUB (φ '' D) (φ x) := hφ D x hD hdirected hlub
  have hdirectedφD : DirectedOn (· ≤ ·) (φ '' D) :=
    hdirected.mono_comp (fun _ _ hab => φ.monotone' hab)
  have hφDnonempty : (φ '' D).Nonempty := hD.image φ
  have himg := hψ (φ '' D) (φ x) hφDnonempty hdirectedφD hφD
  rw [Set.image_image] at himg
  exact himg

end UnitalPositiveLinearMap
