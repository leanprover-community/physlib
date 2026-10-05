/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Weight.Basic
public import PhyslibAlpha.ProbabilisticTheory.Channel.Basic

/-!

# Weight pushforward along a channel

Pushing weights and states forward along a channel, functorially in the channel.

## i. Overview

A channel from system `A` to system `B` is, in the Schrödinger picture, an affine map on states.
Dualizing gives a unital positive linear map on effects in the other direction (the Heisenberg
picture): that map is already `UnitalPositiveLinearMap`, so a channel's adjoint needs no new
structure. What *is* new is pushing a weight forward along that adjoint, and the fact that a
state pushes forward to a state.

Read `φ : Channel E₂ E₁` here as the adjoint of a channel `A → B` with effect algebras
`E₁ = E_A`, `E₂ = E_B`: it pulls an effect of `B` back to an effect of `A`. Precomposing a weight
on `A` with `φ` gives a weight on `B` — the Schrödinger-picture pushforward — and `Weight.comp_id`,
`Weight.comp_comp` show this assignment respects identities and composition, so pushforward is a
functor from unital positive linear maps to weights, contravariant in `φ`.

## ii. Key results

- `Weight.comp` : the pushforward of a weight along a channel.
- `Weight.comp_id`, `Weight.comp_comp` : pushforward respects identities and composition.
- `Weight.IsFinite.comp`, `Weight.IsState.comp` : finite weights and states push forward to
  finite weights and states.

## iii. Table of contents

- A. Pushforward of weights
- B. Functoriality
- C. Preservation of finite weights and states

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped ENNReal

variable {E₁ E₂ E₃ : Type*} [OrderUnitSpace E₁] [OrderUnitSpace E₂] [OrderUnitSpace E₃]

namespace Weight

/-! ## A. Pushforward of weights -/

/-- Precompose a weight on `E₁` with the adjoint `φ : Channel E₂ E₁` of a channel `E₁ → E₂`,
giving a weight on `E₂`: the Schrödinger-picture pushforward of `w` along the channel. -/
noncomputable def comp (w : Weight E₁) (φ : Channel E₂ E₁) : Weight E₂ where
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
lemma comp_apply (w : Weight E₁) (φ : Channel E₂ E₁) (y : PosCone E₂) :
    w.comp φ y = w ⟨φ (y : E₂), φ.map_nonneg y.2⟩ := rfl

/-! ## B. Functoriality -/

@[simp]
lemma comp_id (w : Weight E₁) : w.comp (.id ℝ E₁) = w := by
  ext y
  simp

lemma comp_comp (w : Weight E₁) (φ : Channel E₂ E₁) (ψ : Channel E₃ E₂) :
    w.comp (φ.comp ψ) = (w.comp φ).comp ψ := by
  ext y
  simp

/-! ## C. Preservation of finite weights and states -/

/-- Pushing a finite weight forward along a channel's adjoint stays finite: `φ` never sends the
cone anywhere `w` is infinite. -/
lemma IsFinite.comp {w : Weight E₁} (hw : w.IsFinite) (φ : Channel E₂ E₁) :
    (w.comp φ).IsFinite :=
  fun _ => hw _

section OrderUnitSpace

variable {F₁ F₂ : Type*} [OrderUnitSpace F₁] [OrderUnitSpace F₂]

/-- Pushing a state forward along a channel's adjoint gives a state: finiteness survives
(`IsFinite.comp`) and normalization survives because the adjoint is unital. -/
lemma IsState.comp {w : Weight F₁} (hw : w.IsState) (φ : Channel F₂ F₁) :
    (w.comp φ).IsState where
  finite := hw.finite.comp φ
  normalized := by
    show w ⟨φ (1 : F₂), φ.map_nonneg OrderUnitSpace.one_nonneg⟩ = 1
    have h1 :
        (⟨φ (1 : F₂), φ.map_nonneg OrderUnitSpace.one_nonneg⟩ : PosCone F₁) = 1 := by
      apply Subtype.ext
      show φ (1 : F₂) = 1
      exact map_one φ
    rw [h1, hw.normalized]

end OrderUnitSpace

end Weight

end ProbabilisticTheory
