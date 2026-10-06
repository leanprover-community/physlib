/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Order.StrongUnit
public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith

/-!
# Positive functionals

Positive functionals on an ordered vector space, their order, and extension from the cone.

## i. Overview

A positive functional on an ordered real vector space `E` is a linear functional that is
nonnegative on the positive cone. When the order is directed, every element is a difference of
two nonnegative ones, so positive functionals are determined by their values on the cone. They are
then ordered by comparing these values: `ψ ≤ φ` when `φ - ψ` is positive again.

Conversely, a nonnegative function on the cone that is additive and positively homogeneous there
extends uniquely to a positive functional.

## ii. Key results

- `PositiveLinearMap.instPartialOrder` : positive functionals ordered on the positive cone.
- `PositiveLinearMap.subOfLE` : the difference of two positive functionals, one below the other.
- `PositiveLinearMap.eq_zero_of_map_eq_zero` : a positive functional vanishing at an order unit
  vanishes.
- `PositiveLinearMap.ofCone` : a nonnegative, additive, positively homogeneous function on the
  cone as a positive functional.

## iii. Table of contents

- A. Scaling positive functionals
- B. The order on positive functionals
- C. Extending from the cone

## iv. References

* None.

-/

@[expose] public section

open scoped NNReal

namespace PositiveLinearMap

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]

/-! ## A. Scaling positive functionals -/

/-- A positive functional scaled by a nonnegative real. -/
instance : SMul ℝ≥0 (E →ₚ[ℝ] ℝ) :=
  ⟨fun c φ => mk₀ ((c : ℝ) • φ.toLinearMap) fun _ hf => mul_nonneg c.2 (map_nonneg φ hf)⟩

@[simp]
lemma nnsmul_apply (c : ℝ≥0) (φ : E →ₚ[ℝ] ℝ) (f : E) : (c • φ) f = c * φ f :=
  rfl

/-! ## B. The order on positive functionals -/

section Directed

variable [IsDirectedOrder E]

/-- An element above both `f` and `0`. -/
noncomputable def dominator (f : E) : E := (exists_ge_ge f 0).choose

omit [IsOrderedAddMonoid E] [Module ℝ E] in
lemma le_dominator (f : E) : f ≤ dominator f := (exists_ge_ge f 0).choose_spec.1

omit [IsOrderedAddMonoid E] [Module ℝ E] in
lemma dominator_nonneg (f : E) : 0 ≤ dominator f := (exists_ge_ge f 0).choose_spec.2

/-- Positive functionals are ordered by comparing them on the positive cone. -/
instance instPartialOrder : PartialOrder (E →ₚ[ℝ] ℝ) where
  le φ ψ := ∀ f, 0 ≤ f → φ f ≤ ψ f
  le_refl _ _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ f hf := (h₁ f hf).trans (h₂ f hf)
  le_antisymm φ ψ h₁ h₂ := ext fun f => by
    have hb := dominator_nonneg f
    have hbf := sub_nonneg.2 (le_dominator f)
    have e₁ := le_antisymm (h₁ _ hb) (h₂ _ hb)
    have e₂ := le_antisymm (h₁ _ hbf) (h₂ _ hbf)
    rw [map_sub, map_sub] at e₂
    linarith

lemma le_def {φ ψ : E →ₚ[ℝ] ℝ} : φ ≤ ψ ↔ ∀ f, 0 ≤ f → φ f ≤ ψ f := Iff.rfl

lemma zero_le (φ : E →ₚ[ℝ] ℝ) : 0 ≤ φ := fun _ hf => map_nonneg φ hf

lemma le_add_right (φ ψ : E →ₚ[ℝ] ℝ) : φ ≤ φ + ψ := fun f hf => by
  simpa using map_nonneg ψ hf

lemma le_sum {ι : Type*} {t : Finset ι} (ψ : ι → E →ₚ[ℝ] ℝ) {i : ι} (hi : i ∈ t) :
    ψ i ≤ ∑ j ∈ t, ψ j := fun f hf => by
  rw [sum_apply]
  exact Finset.single_le_sum (fun j _ => map_nonneg (ψ j) hf) hi

/-- The difference of two positive functionals, one below the other. -/
def subOfLE (φ ψ : E →ₚ[ℝ] ℝ) (h : ψ ≤ φ) : E →ₚ[ℝ] ℝ :=
  .mk₀ (φ.toLinearMap - ψ.toLinearMap) fun f hf => sub_nonneg.2 (h f hf)

@[simp] lemma subOfLE_apply (φ ψ : E →ₚ[ℝ] ℝ) (h : ψ ≤ φ) (f : E) :
    subOfLE φ ψ h f = φ f - ψ f := rfl

lemma add_subOfLE (φ ψ : E →ₚ[ℝ] ℝ) (h : ψ ≤ φ) : ψ + subOfLE φ ψ h = φ :=
  ext fun f => by simp

lemma eq_zero_of_add_eq_zero {φ ψ : E →ₚ[ℝ] ℝ} (h : φ + ψ = 0) : φ = 0 :=
  le_antisymm (h ▸ le_add_right φ ψ) (zero_le φ)

lemma eq_subOfLE_add_subOfLE {φ σ θ₁ θ₂ α β : E →ₚ[ℝ] ℝ} (h : φ + σ = α + β)
    (e : φ = θ₁ + θ₂) (h₁ : θ₁ ≤ α) (h₂ : θ₂ ≤ β) : σ = subOfLE α θ₁ h₁ + subOfLE β θ₂ h₂ :=
  ext fun f => by
    have := congrArg (· f) h
    simp only [add_apply, e] at this
    simp only [add_apply, subOfLE_apply]
    linarith

end Directed

/-- A positive functional vanishing at an order unit vanishes. -/
lemma eq_zero_of_map_eq_zero {u : E} (hu : IsOrderUnit u) {ψ : E →ₚ[ℝ] ℝ} (h : ψ u = 0) :
    ψ = 0 :=
  ext fun A => by
    obtain ⟨n, hlo, hhi⟩ := hu.exists_two_sided A
    have h₁ : ψ (-(n • u)) ≤ ψ A := ψ.monotone' hlo
    have h₂ : ψ A ≤ ψ (n • u) := ψ.monotone' hhi
    rw [map_neg, map_nsmul, h, smul_zero, neg_zero] at h₁
    rw [map_nsmul, h, smul_zero] at h₂
    exact le_antisymm h₂ h₁

/-! ## C. Extending from the cone -/

section Cone

variable [PosSMulMono ℝ E] [IsDirectedOrder E] (F : E → ℝ) (h0 : ∀ f, 0 ≤ f → 0 ≤ F f)
  (hadd : ∀ f g, 0 ≤ f → 0 ≤ g → F (f + g) = F f + F g)
  (hsmul : ∀ (c : ℝ) f, 0 < c → 0 ≤ f → F (c • f) = c * F f)

/-- The extension of `F` from the cone: `F b - F (b - f)` for any `b` above `f` and `0`. -/
noncomputable def coneExt (f : E) : ℝ := F (dominator f) - F (dominator f - f)

include hadd

omit [IsOrderedAddMonoid E] [Module ℝ E] [IsDirectedOrder E] in
lemma map_zero_of_cone_add : F 0 = 0 := by
  have := hadd 0 0 le_rfl le_rfl
  rw [add_zero] at this
  linarith

omit [Module ℝ E] in
/-- The extension does not depend on the element `b` above `f` and `0`. -/
lemma coneExt_eq {f b : E} (hb : 0 ≤ b) (hbf : f ≤ b) : coneExt F f = F b - F (b - f) := by
  have h₁ := hadd b (dominator f - f) hb (sub_nonneg.2 (le_dominator f))
  have h₂ := hadd (dominator f) (b - f) (dominator_nonneg f) (sub_nonneg.2 hbf)
  rw [show b + (dominator f - f) = dominator f + (b - f) by abel] at h₁
  unfold coneExt
  linarith

omit [Module ℝ E] in
lemma coneExt_of_nonneg {f : E} (hf : 0 ≤ f) : coneExt F f = F f := by
  rw [coneExt_eq F hadd hf le_rfl, sub_self, map_zero_of_cone_add F hadd, sub_zero]

omit [Module ℝ E] in
lemma coneExt_add (f g : E) : coneExt F (f + g) = coneExt F f + coneExt F g := by
  rw [coneExt_eq F hadd (add_nonneg (dominator_nonneg f) (dominator_nonneg g))
    (add_le_add (le_dominator f) (le_dominator g))]
  have h₁ := hadd _ _ (dominator_nonneg f) (dominator_nonneg g)
  have h₂ := hadd _ _ (sub_nonneg.2 (le_dominator f)) (sub_nonneg.2 (le_dominator g))
  rw [show dominator f - f + (dominator g - g) = dominator f + dominator g - (f + g) by abel]
    at h₂
  unfold coneExt
  linarith

omit [Module ℝ E] in
lemma coneExt_neg (f : E) : coneExt F (-f) = -coneExt F f := by
  rw [coneExt_eq F hadd (sub_nonneg.2 (le_dominator f))
    (by rw [neg_le_sub_iff_le_add]; exact le_add_of_nonneg_left (dominator_nonneg f)),
    sub_neg_eq_add, sub_add_cancel]
  unfold coneExt
  ring

include hsmul

lemma coneExt_smul_of_pos {c : ℝ} (hc : 0 < c) (f : E) : coneExt F (c • f) = c * coneExt F f := by
  rw [coneExt_eq F hadd (smul_nonneg hc.le (dominator_nonneg f))
    (smul_le_smul_of_nonneg_left (le_dominator f) hc.le), ← smul_sub,
    hsmul c _ hc (dominator_nonneg f), hsmul c _ hc (sub_nonneg.2 (le_dominator f))]
  unfold coneExt
  ring

lemma coneExt_smul (c : ℝ) (f : E) : coneExt F (c • f) = c * coneExt F f := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have := coneExt_smul_of_pos F hadd hsmul (neg_pos.2 hc) f
    rw [neg_smul, coneExt_neg F hadd] at this
    linarith
  · rw [zero_smul, zero_mul, coneExt_of_nonneg F hadd le_rfl, map_zero_of_cone_add F hadd]
  · exact coneExt_smul_of_pos F hadd hsmul hc f

omit hadd hsmul in
include hadd hsmul in
/-- A nonnegative, additive and positively homogeneous function on the positive cone extends to a
positive functional. -/
noncomputable def ofCone : E →ₚ[ℝ] ℝ :=
  mk₀ ⟨⟨coneExt F, coneExt_add F hadd⟩, coneExt_smul F hadd hsmul⟩ fun f hf => by
    change 0 ≤ coneExt F f
    rw [coneExt_of_nonneg F hadd hf]
    exact h0 f hf

include h0 in
lemma ofCone_apply {f : E} (hf : 0 ≤ f) : ofCone F h0 hadd hsmul f = F f :=
  coneExt_of_nonneg F hadd hf

end Cone

end PositiveLinearMap
