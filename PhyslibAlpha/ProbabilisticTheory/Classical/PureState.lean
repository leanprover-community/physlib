/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.OrderUnit.Lattice
public import PhyslibAlpha.ProbabilisticTheory.State.StateSpace
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Ordered

/-!
# Pure states

## i. Overview

A pure state is a state of maximal knowledge. It cannot be prepared by mixing two different states.
In quantum mechanics the pure states are the vector states. In classical mechanics they are the
points of phase space.

Mixing shows up in the order of positive functionals. A weighted state below a pure state is a
fraction of that same pure state. Two different pure states have nothing in common: only zero lies
below weighted copies of both.

The pure states form a space, `PureState E`, on which all other states are decomposed. They see
every observable: by the Krein–Milman theorem, an observable with nonnegative expectation value in
every pure state is nonnegative.

## ii. Key results

- `UnitalPositiveLinearMap.IsPure.apply_eq_of_le` proves that a positive functional below a pure
  state is a multiple of it.
- `UnitalPositiveLinearMap.eq_zero_of_le_weighted` proves that only zero lies below weighted copies
  of two different pure states.
- `PureState E` is the space of pure states.
- `PureState.nonneg_of_forall_pure` proves that an observable nonnegative in every pure state is
  nonnegative.
- `PureState.evalPure_le_iff` proves that observables are ordered by their values on pure states.

## iii. Table of contents

- A. Functionals below a pure state
- B. The space of pure states

-/

@[expose] public section

namespace ProbabilisticTheory

open StateSpace

open ArchimedeanOrderUnitSpace Set
open scoped NNReal

/-!

## A. Functionals below a pure state

-/

namespace UnitalPositiveLinearMap

section Archimedean

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

/-- The state `φ / φ 1` of a positive functional with `φ 1 > 0`. -/
noncomputable def normalize (φ : E →ₚ[ℝ] ℝ) (h : 0 < φ 1) : 𝓢[ℝ, E] :=
  ofLinearMap ((φ 1)⁻¹ • φ.toLinearMap)
    (fun _ hf => mul_nonneg (inv_nonneg.2 h.le) (map_nonneg φ hf))
    (show (φ 1)⁻¹ * φ 1 = 1 from inv_mul_cancel₀ h.ne')

@[simp] lemma normalize_apply (φ : E →ₚ[ℝ] ℝ) (h : 0 < φ 1) (f : E) :
    normalize φ h f = (φ 1)⁻¹ * φ f := rfl

@[simp] lemma toPositiveLinearMap_apply (ω : 𝓢[ℝ, E]) (f : E) :
    ω.toPositiveLinearMap f = ω f := rfl

/-- A positive functional below a pure state `ω` with `0 < φ 1 < 1` is `φ 1` times `ω`. -/
lemma IsPure.apply_eq_of_le_of_pos {ω : 𝓢[ℝ, E]} (hω : ω.IsPure) {φ : E →ₚ[ℝ] ℝ}
    (hφ : φ ≤ ω.toPositiveLinearMap) (h0 : 0 < φ 1) (h1 : φ 1 < 1) (f : E) :
    φ f = φ 1 * ω f := by
  have hψ : 0 < PositiveLinearMap.subOfLE ω.toPositiveLinearMap φ hφ 1 := by simp [h1]
  have hmix : mix (normalize φ h0) (normalize _ hψ) ⟨φ 1, h0.le, h1.le⟩ = ω := ext fun g => by
    simp only [mix_apply, normalize_apply, PositiveLinearMap.subOfLE_apply, map_one,
      toPositiveLinearMap_apply]
    field_simp [(sub_pos.2 h1).ne']
    ring
  have := congrArg (· f) (hω.eq_of_mix _ (fun h => h0.ne' (congrArg Subtype.val h))
    (fun h => h1.ne (congrArg Subtype.val h)) hmix).1
  simp only [normalize_apply] at this
  field_simp at this
  linarith

/-- A pure state dominates only multiples of itself. -/
lemma IsPure.apply_eq_of_le {ω : 𝓢[ℝ, E]} (hω : ω.IsPure) {φ : E →ₚ[ℝ] ℝ}
    (hφ : φ ≤ ω.toPositiveLinearMap) (f : E) : φ f = φ 1 * ω f := by
  have h1 : φ 1 ≤ 1 := (hφ 1 OrderUnitSpace.one_nonneg).trans_eq (map_one ω)
  rcases (map_nonneg φ OrderUnitSpace.one_nonneg).eq_or_lt with h0 | h0
  · rw [← h0, zero_mul]
    exact apply_eq_zero_of_apply_one_eq_zero h0.symm f
  rcases h1.eq_or_lt with h1 | h1
  · have := apply_eq_zero_of_apply_one_eq_zero
      (p := PositiveLinearMap.subOfLE ω.toPositiveLinearMap φ hφ) (by simp [h1]) f
    rw [PositiveLinearMap.subOfLE_apply, toPositiveLinearMap_apply] at this
    rw [h1, one_mul]
    linarith
  · exact hω.apply_eq_of_le_of_pos hφ h0 h1 f

/-- The state `ω` with weight `c`, as a positive functional. -/
def weighted (ω : 𝓢[ℝ, E]) (c : ℝ≥0) : E →ₚ[ℝ] ℝ :=
  .mk₀ ((c : ℝ) • ω.toLinearMap) fun _ hf => mul_nonneg c.2 (map_nonneg ω hf)

@[simp] lemma weighted_apply (ω : 𝓢[ℝ, E]) (c : ℝ≥0) (f : E) : ω.weighted c f = c * ω f := rfl

/-- A positive functional below a weighted pure state is a multiple of that state. -/
lemma IsPure.apply_eq_of_le_weighted {ω : 𝓢[ℝ, E]} (hω : ω.IsPure) {γ : E →ₚ[ℝ] ℝ} {c : ℝ≥0}
    (h : γ ≤ ω.weighted c) (f : E) : γ f = γ 1 * ω f := by
  rcases eq_or_ne c 0 with rfl | hc
  · have h0 : γ 1 = 0 := le_antisymm (by simpa using h 1 OrderUnitSpace.one_nonneg)
      (map_nonneg γ OrderUnitSpace.one_nonneg)
    rw [h0, zero_mul, apply_eq_zero_of_apply_one_eq_zero h0]
  have hc' : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  let φ : E →ₚ[ℝ] ℝ := .mk₀ ((c : ℝ)⁻¹ • γ.toLinearMap) fun _ hf =>
    mul_nonneg (inv_nonneg.2 hc'.le) (map_nonneg γ hf)
  have hφ : φ ≤ ω.toPositiveLinearMap := fun g hg => by
    change (c : ℝ)⁻¹ * γ g ≤ ω g
    rw [inv_mul_le_iff₀ hc']
    simpa using h g hg
  have := hω.apply_eq_of_le hφ f
  change (c : ℝ)⁻¹ * γ f = (c : ℝ)⁻¹ * γ 1 * ω f at this
  rw [mul_assoc] at this
  exact mul_left_cancel₀ (inv_ne_zero hc'.ne') this

/-- A positive functional below weighted copies of two distinct pure states vanishes. -/
lemma eq_zero_of_le_weighted {ω₁ ω₂ : 𝓢[ℝ, E]} (h₁ : ω₁.IsPure) (h₂ : ω₂.IsPure) (hne : ω₁ ≠ ω₂)
    {γ : E →ₚ[ℝ] ℝ} {c₁ c₂ : ℝ≥0} (hγ₁ : γ ≤ ω₁.weighted c₁) (hγ₂ : γ ≤ ω₂.weighted c₂) :
    γ = 0 := by
  by_cases h0 : γ 1 = 0
  · exact PositiveLinearMap.ext fun f => apply_eq_zero_of_apply_one_eq_zero h0 f
  · exact absurd (ext fun f => mul_left_cancel₀ h0 ((h₁.apply_eq_of_le_weighted hγ₁ f).symm.trans
      (h₂.apply_eq_of_le_weighted hγ₂ f))) hne

end Archimedean

end UnitalPositiveLinearMap

/-- Two distinct states take any two prescribed values on a common observable. -/
lemma StateSpace.exists_apply_eq_apply {E : Type*} [ArchimedeanOrderUnitSpace E]
    {x y : stateSpace E} (p q : ℝ) (h : x = y → p = q) :
    ∃ a : E, toState x a = p ∧ toState y a = q := by
  by_cases hxy : x = y
  · subst hxy
    exact ⟨p • 1, by simp, by simp [h rfl]⟩
  obtain ⟨g, hg⟩ : ∃ g : E, toState x g ≠ toState y g := by
    by_contra! h
    exact hxy (StateSpace.equivState.injective (UnitalPositiveLinearMap.ext h))
  refine ⟨((p - q) / (toState x g - toState y g)) • g +
    (p - (p - q) / (toState x g - toState y g) * toState x g) • 1, by simp, ?_⟩
  simp only [map_add, map_smul, map_one, smul_eq_mul, mul_one]
  field_simp [sub_ne_zero.2 hg]
  ring

/-!

## B. The space of pure states

-/

section Archimedean

variable (E : Type*) [ArchimedeanOrderUnitSpace E]

/-- The pure states, with the weak-star topology. -/
abbrev PureState : Type _ := {ω : stateSpace E // (toState ω).IsPure}

namespace PureState

variable {E}

/-- An observable as the continuous function of its values on the pure states. -/
noncomputable def evalPure : E →ₗ[ℝ] C(PureState E, ℝ) where
  toFun f := ⟨fun ω => toState ω.1 f,
    (StateSpace.continuous_apply f).comp continuous_subtype_val⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp] lemma evalPure_apply (f : E) (ω : PureState E) : evalPure f ω = toState ω.1 f := rfl

@[simp] lemma evalPure_one : evalPure (1 : E) = 1 := by ext; simp

/-- **Krein–Milman**: an observable nonnegative in every pure state is nonnegative. -/
lemma nonneg_of_forall_pure {f : E} (h : ∀ ω : PureState E, 0 ≤ toState ω.1 f) : 0 ≤ f := by
  have : LocallyConvexSpace ℝ (WeakDual ℝ E) := WeakBilin.locallyConvexSpace
  refine (UnitalPositiveLinearMap.nonneg_iff_forall_state_nonneg f).2 fun φ => ?_
  have hsub : stateSpace E ⊆ {F : WeakDual ℝ E | 0 ≤ F f} := by
    rw [← closure_convexHull_extremePoints isCompact_stateSpace
      convex_stateSpace]
    refine closure_minimal (convexHull_min (fun F hF => ?_)
      (convex_halfSpace_ge ⟨fun _ _ => rfl, fun _ _ => rfl⟩ 0))
      (isClosed_le continuous_const (WeakDual.eval_continuous f))
    exact h ⟨⟨F, extremePoints_subset hF⟩, (StateSpace.isPure_iff_mem_extremePoints _).2 hF⟩
  exact hsub (StateSpace.ofState φ).2

/-- Pure states determine the order. -/
lemma evalPure_le_iff {f g : E} : evalPure f ≤ evalPure g ↔ f ≤ g :=
  ⟨fun h => sub_nonneg.1 (nonneg_of_forall_pure fun ω => by simpa [map_sub] using h ω),
    fun h ω => OrderHomClass.mono (toState ω.1) h⟩

end PureState

end Archimedean

end ProbabilisticTheory
