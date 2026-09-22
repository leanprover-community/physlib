/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Channel.Basic
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Effect.Basic
public import Mathlib.Topology.UnitInterval

/-!

# States

## i. Overview

A state is a normalized positive linear functional: an element of `𝓟[𝕜, A]`, the positive linear
functionals on `A`, that sends the unit to `1`. `𝓢[𝕜, A]` is just `A →ₚ₁[𝕜] 𝕜` — the state space
is a special case of the channel type, with the target system the base field itself.

## ii. Key definitions

- `𝓟[𝕜, A]` is the type of positive linear functionals on an ordered `𝕜`-vector space.
- `𝓢[𝕜, A]` is the state space of an ordered `𝕜`-vector space with unit.
- `UnitalPositiveLinearMap.onEffect` is the probability assigned by a real state to an effect.

## iii. Table of contents

- A. Positive functionals and states
- B. Pulling states back along channels

-/

@[expose] public section

/-! ## A. Positive functionals and states -/

/-- Positive linear functionals on an ordered `𝕜`-vector space. -/
notation " 𝓟[" 𝕜 ", " A "] " => A →ₚ[𝕜] 𝕜

/-- Positive linear functionals on an ordered complex vector space. -/
notation " 𝓟[" A "] " => A →ₚ[ℂ] ℂ

/-- State space of an ordered `𝕜`-vector space with unit. -/
notation " 𝓢[" 𝕜 ", " A "] " => A →ₚ₁[𝕜] 𝕜

/-- State space of an ordered complex vector space with unit. -/
notation " 𝓢[" A "] " => A →ₚ₁[ℂ] ℂ

namespace UnitalPositiveLinearMap

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [One E] [IsOrderUnit E]

/-- The probability a real state assigns to an effect, bundled in the unit interval. -/
def onEffect (ω : 𝓢[ℝ, E]) (e : Effect E) : unitInterval :=
  ⟨ω (e : E), ω.map_nonneg e.2.1,
    (ω.monotone' e.2.2).trans_eq (map_one ω)⟩

omit [IsOrderedAddMonoid E] [IsOrderUnit E] in
@[simp]
lemma coe_onEffect (ω : 𝓢[ℝ, E]) (e : Effect E) :
    (ω.onEffect e : ℝ) = ω (e : E) := rfl

omit [IsOrderUnit E] in
/-- A state sends complementary effects to complementary probabilities. -/
lemma onEffect_complement (ω : 𝓢[ℝ, E]) (e : Effect E) :
    ω.onEffect (Effect.complement e) = unitInterval.symm (ω.onEffect e) := by
  apply Subtype.ext
  simp [onEffect, Effect.complement, unitInterval.symm]

omit [IsOrderUnit E] in
/-- A state is additive on every defined partial sum of effects. -/
lemma onEffect_addOfOrthogonal (ω : 𝓢[ℝ, E]) (e f : Effect E)
    (h : Effect.Orthogonal e f) :
    (ω.onEffect (Effect.addOfOrthogonal e f h) : ℝ) = ω.onEffect e + ω.onEffect f := by
  simp [onEffect]

variable [PosSMulMono ℝ E]

/-- States are determined by their probabilities on effects.  Every positive observable can be
rescaled into the effect interval, and every observable is a difference of two positive ones. -/
lemma ext_of_onEffect_eq {ω φ : 𝓢[ℝ, E]} (h : ∀ e : Effect E, ω.onEffect e = φ.onEffect e) :
    ω = φ := by
  apply UnitalPositiveLinearMap.ext
  intro x
  obtain ⟨xp, xn, hxp, hxn, rfl⟩ := IsOrderUnit.exists_eq_sub_nonneg x
  suffices hpos : ∀ y : E, 0 ≤ y → ω y = φ y by
    rw [map_sub, map_sub, hpos xp hxp, hpos xn hxn]
  intro y hy
  obtain ⟨n, hn⟩ := IsOrderUnit.exists_nsmul_one_le y
  let r : ℝ := n + 1
  have hr : 0 < r := by positivity
  have hyr : y ≤ r • (1 : E) := by
    calc
      y ≤ n • (1 : E) := hn
      _ = (n : ℝ) • (1 : E) := (Nat.cast_smul_eq_nsmul ℝ n (1 : E)).symm
      _ ≤ r • (1 : E) :=
        smul_le_smul_of_nonneg_right (by simp [r]) IsOrderUnit.one_nonneg
  let e : Effect E := ⟨r⁻¹ • y, smul_nonneg (inv_nonneg.mpr hr.le) hy, by
    have hs := smul_le_smul_of_nonneg_left hyr (inv_nonneg.mpr hr.le)
    simpa [smul_smul, hr.ne'] using hs⟩
  have heq := congrArg Subtype.val (h e)
  change ω (r⁻¹ • y) = φ (r⁻¹ • y) at heq
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at heq
  exact mul_left_cancel₀ (inv_ne_zero hr.ne') heq

/-- Two states are equal exactly when all of their effect probabilities agree. -/
lemma eq_iff_onEffect_eq {ω φ : 𝓢[ℝ, E]} :
    ω = φ ↔ ∀ e : Effect E, ω.onEffect e = φ.onEffect e := by
  constructor
  · rintro rfl
    exact fun _ => rfl
  · exact ext_of_onEffect_eq

end UnitalPositiveLinearMap

namespace UnitalPositiveLinearMap

/-! ## B. Pulling states back along channels -/

variable {E₁ E₂ : Type*}
  [AddCommGroup E₁] [PartialOrder E₁] [IsOrderedAddMonoid E₁] [Module ℝ E₁] [One E₁]
  [AddCommGroup E₂] [PartialOrder E₂] [IsOrderedAddMonoid E₂] [Module ℝ E₂] [One E₂]

/-- The Schrödinger-picture action of a Heisenberg channel on states: precomposition. -/
def pullbackState (φ : E₁ →ₚ₁[ℝ] E₂) (ω : 𝓢[ℝ, E₂]) : 𝓢[ℝ, E₁] := ω.comp φ

omit [IsOrderedAddMonoid E₁] [IsOrderedAddMonoid E₂] in
@[simp]
lemma pullbackState_apply (φ : E₁ →ₚ₁[ℝ] E₂) (ω : 𝓢[ℝ, E₂]) (x : E₁) :
    φ.pullbackState ω x = ω (φ x) := rfl

omit [IsOrderedAddMonoid E₁] in
@[simp]
lemma pullbackState_id (ω : 𝓢[ℝ, E₁]) :
    (UnitalPositiveLinearMap.id ℝ E₁).pullbackState ω = ω := by
  ext x
  rfl

variable {E₃ : Type*}
  [AddCommGroup E₃] [PartialOrder E₃] [IsOrderedAddMonoid E₃] [Module ℝ E₃] [One E₃]

omit [IsOrderedAddMonoid E₁] [IsOrderedAddMonoid E₂] [IsOrderedAddMonoid E₃] in
@[simp]
lemma pullbackState_comp (φ : E₁ →ₚ₁[ℝ] E₂) (ψ : E₂ →ₚ₁[ℝ] E₃) (ω : 𝓢[ℝ, E₃]) :
    (ψ.comp φ).pullbackState ω = φ.pullbackState (ψ.pullbackState ω) := by
  ext x
  rfl

end UnitalPositiveLinearMap
