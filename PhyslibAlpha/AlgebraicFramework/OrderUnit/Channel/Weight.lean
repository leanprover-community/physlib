/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Weight.Basic
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Channel.Basic

/-!

# Weight pushforward along a channel

## i. Overview

A channel from system `A` to system `B` is, in the Schrödinger picture, an affine map on states.
Dualizing gives a unital positive linear map on effects in the other direction (the Heisenberg
picture): that map is already `UnitalPositiveLinearMap`, so a channel's adjoint needs no new
structure. What *is* new is pushing a weight forward along that adjoint, and the fact that a
state pushes forward to a state.

Read `φ : E₂ →ₚ₁[ℝ] E₁` here as the adjoint of a channel `A → B` with effect algebras
`E₁ = E_A`, `E₂ = E_B`: it pulls an effect of `B` back to an effect of `A`. Precomposing a weight
on `A` with `φ` gives a weight on `B` — the Schrödinger-picture pushforward — and `Weight.comp_id`,
`Weight.comp_comp` show this assignment respects identities and composition, so pushforward is a
functor from unital positive linear maps to weights, contravariant in `φ`.

## ii. Key definitions and results

- `Weight.comp`, `Weight.IsFinite.comp`, `Weight.IsState.comp`

## iii. Table of contents

- A. Pushforward of weights
- B. Functoriality
- C. Preservation of finite weights and states

-/

@[expose] public section

open scoped ENNReal

variable {E₁ E₂ E₃ : Type*}
  [AddCommGroup E₁] [PartialOrder E₁] [IsOrderedAddMonoid E₁] [Module ℝ E₁] [PosSMulMono ℝ E₁]
  [One E₁]
  [AddCommGroup E₂] [PartialOrder E₂] [IsOrderedAddMonoid E₂] [Module ℝ E₂] [PosSMulMono ℝ E₂]
  [One E₂]
  [AddCommGroup E₃] [PartialOrder E₃] [IsOrderedAddMonoid E₃] [Module ℝ E₃] [PosSMulMono ℝ E₃]
  [One E₃]

namespace Weight

/-! ## A. Pushforward of weights -/

/-- Precompose a weight on `E₁` with the adjoint `φ : E₂ →ₚ₁[ℝ] E₁` of a channel `E₁ → E₂`,
giving a weight on `E₂`: the Schrödinger-picture pushforward of `w` along the channel. -/
noncomputable def comp (w : Weight E₁) (φ : E₂ →ₚ₁[ℝ] E₁) : Weight E₂ where
  toFun y := w ⟨φ (y : E₂), φ.map_nonneg y.2⟩
  map_add' x y := by
    have hxy : (⟨φ ((x + y : PosCone E₂) : E₂), φ.map_nonneg (x + y).2⟩ : PosCone E₁) =
        ⟨φ (x : E₂), φ.map_nonneg x.2⟩ + ⟨φ (y : E₂), φ.map_nonneg y.2⟩ := by
      apply Subtype.ext
      show φ ((x : E₂) + (y : E₂)) = φ (x : E₂) + φ (y : E₂)
      exact _root_.map_add φ _ _
    show w ⟨φ ((x + y : PosCone E₂) : E₂), _⟩ = _
    rw [hxy, w.map_add]
  map_smul' c y := by
    have hy : (⟨φ ((c • y : PosCone E₂) : E₂), φ.map_nonneg (c • y).2⟩ : PosCone E₁) =
        c • (⟨φ (y : E₂), φ.map_nonneg y.2⟩ : PosCone E₁) := by
      apply Subtype.ext
      show φ ((c : ℝ) • (y : E₂)) = (c : ℝ) • φ (y : E₂)
      exact _root_.map_smul φ (c : ℝ) (y : E₂)
    show w ⟨φ ((c • y : PosCone E₂) : E₂), _⟩ = _
    rw [hy, w.map_smul]
    rfl

@[simp]
lemma comp_apply (w : Weight E₁) (φ : E₂ →ₚ₁[ℝ] E₁) (y : PosCone E₂) :
    w.comp φ y = w ⟨φ (y : E₂), φ.map_nonneg y.2⟩ := rfl

/-! ## B. Functoriality -/

@[simp]
lemma comp_id (w : Weight E₁) : w.comp (.id ℝ E₁) = w := by
  ext y
  simp

lemma comp_comp (w : Weight E₁) (φ : E₂ →ₚ₁[ℝ] E₁) (ψ : E₃ →ₚ₁[ℝ] E₂) :
    w.comp (φ.comp ψ) = (w.comp φ).comp ψ := by
  ext y
  simp

/-! ## C. Preservation of finite weights and states -/

/-- Pushing a finite weight forward along a channel's adjoint stays finite: `φ` never sends the
cone anywhere `w` is infinite. -/
lemma IsFinite.comp {w : Weight E₁} (hw : w.IsFinite) (φ : E₂ →ₚ₁[ℝ] E₁) :
    (w.comp φ).IsFinite :=
  fun _ => hw _

variable [IsOrderUnit E₁] [IsOrderUnit E₂]

/-- Pushing a state forward along a channel's adjoint gives a state: finiteness survives
(`IsFinite.comp`) and normalization survives because the adjoint is unital. -/
lemma IsState.comp {w : Weight E₁} (hw : w.IsState) (φ : E₂ →ₚ₁[ℝ] E₁) :
    (w.comp φ).IsState where
  finite := hw.finite.comp φ
  normalized := by
    show w ⟨φ (1 : E₂), φ.map_nonneg IsOrderUnit.one_nonneg⟩ = 1
    have h1 : (⟨φ (1 : E₂), φ.map_nonneg IsOrderUnit.one_nonneg⟩ : PosCone E₁) = Weight.unit := by
      apply Subtype.ext
      show φ (1 : E₂) = 1
      exact map_one φ
    rw [h1, hw.normalized]

end Weight
