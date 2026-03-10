/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Relativity.LorentzGroup.Proper
public import PhysLean.Relativity.LorentzGroup.ToVector
public import PhysLean.Relativity.Tensors.RealTensor.Velocity.Basic
/-!
# The Orthochronous Lorentz Group

We define the give a series of lemmas related to the orthochronous property of lorentz
matrices.

-/

@[expose] public section
TODO "6VZLO" "Prove topological properties of the Orthochronous Lorentz Group."

noncomputable section

open Matrix
open Complex
open ComplexConjugate

namespace LorentzGroup

variable {d : ℕ}
variable (Λ : LorentzGroup d)
open Lorentz.Vector

/-- A Lorentz transformation is `orthochronous` if its `0 0` element is non-negative. -/
def IsOrthochronous : Prop := 0 ≤ Λ.1 (Sum.inl 0) (Sum.inl 0)

/-- A Lorentz transformation is `orthochronous` if and only if its first column is
  future pointing. -/
lemma isOrthochronous_iff_toVector_timeComponet_nonneg :
    IsOrthochronous Λ ↔ 0 ≤ (toVector Λ).timeComponent := by
  simp [IsOrthochronous, timeComponent]

/-- A Lorentz transformation is orthochronous if and only if its transpose is orthochronous. -/
lemma isOrthochronous_iff_transpose :
    IsOrthochronous Λ ↔ IsOrthochronous (transpose Λ) := by rfl

@[simp]
lemma isOrthochronous_inv_iff {Λ : LorentzGroup d} :
    IsOrthochronous Λ⁻¹ ↔ IsOrthochronous Λ := by
  simp [IsOrthochronous, inv_eq_dual, minkowskiMatrix.dual_apply, minkowskiMatrix.inl_0_inl_0]

/-- A Lorentz transformation is orthochronous if and only if its `0 0` element is greater
  or equal to one. -/
lemma isOrthochronous_iff_ge_one :
    IsOrthochronous Λ ↔ 1 ≤ Λ.1 (Sum.inl 0) (Sum.inl 0) := by
  have h1 := one_le_abs_timeComponent Λ
  rw [le_abs'] at h1
  simp [IsOrthochronous]
  constructor
  · intro h
    rcases h1 with h1 | h1
    · linarith
    · linarith
  · intro h
    linarith

/-- The `Lorentz.Velocity` from `Lorentz.toVector` of a orthochronous lorentz
  transformation. -/
def orthochronoustoVelocity {Λ : LorentzGroup d} (h : IsOrthochronous Λ) :
    Lorentz.Velocity d := ⟨toVector Λ, by
      rw [isOrthochronous_iff_ge_one] at h
      simp [Lorentz.Velocity.mem_iff]
      linarith⟩

/-- A Lorentz transformation is not orthochronous if and only if its `0 0` element is less than
  or equal to minus one. -/
lemma not_isOrthochronous_iff_le_neg_one :
    ¬ IsOrthochronous Λ ↔ Λ.1 (Sum.inl 0) (Sum.inl 0) ≤ -1 := by
  have h1 := one_le_abs_timeComponent Λ
  rw [le_abs'] at h1
  simp [IsOrthochronous]
  constructor
  · intro h
    rcases h1 with h1 | h1
    · linarith
    · linarith
  · intro h
    linarith

lemma isOrthochronous_iff_not_neg :
    IsOrthochronous Λ ↔ ¬ IsOrthochronous (- Λ) := by
  rw [not_isOrthochronous_iff_le_neg_one, isOrthochronous_iff_ge_one]
  simp

lemma neg_isOrthochronous_iff_not {Λ : LorentzGroup d} :
    IsOrthochronous (- Λ) ↔ ¬ IsOrthochronous Λ := by
  conv_rhs => rw [isOrthochronous_iff_not_neg]
  simp

/-- A Lorentz transformation is not orthochronous if and only if its `0 0` element is
  non-positive. -/
lemma not_isOrthochronous_iff_le_zero : ¬ IsOrthochronous Λ ↔ Λ.1 (Sum.inl 0) (Sum.inl 0) ≤ 0 := by
  have h1 := one_le_abs_timeComponent Λ
  rw [le_abs'] at h1
  simp [IsOrthochronous]
  constructor
  · intro h
    rcases h1 with h1 | h1
    · linarith
    · linarith
  · intro h
    rcases h1 with h1 | h1
    · linarith
    · linarith

lemma not_isOrthochronous_iff_toVector_timeComponet_nonpos :
    ¬ IsOrthochronous Λ ↔ (toVector Λ).timeComponent ≤ 0:= by
  rw [not_isOrthochronous_iff_le_zero]
  simp

/-- The identity Lorentz transformation is orthochronous. -/
lemma id_isOrthochronous : @IsOrthochronous d 1 := by
  simp [IsOrthochronous]

/-- The continuous map taking a Lorentz transformation to its `0 0` element. -/
def timeCompCont : C(LorentzGroup d, ℝ) := ⟨fun Λ => Λ.1 (Sum.inl 0) (Sum.inl 0),
    Continuous.matrix_elem (continuous_iff_le_induced.mpr fun _ a => a) (Sum.inl 0) (Sum.inl 0)⟩

/-- An auxiliary function used in the definition of `orthchroMapReal`.
  This function takes all elements of `ℝ` less than `-1` to `-1`,
  all elements of `R` greater than `1` to `1` and preserves all other elements. -/
def stepFunction : ℝ → ℝ := fun t =>
  if t ≤ -1 then -1 else
    if 1 ≤ t then 1 else t

/-- The `stepFunction` is continuous. -/
lemma stepFunction_continuous : Continuous stepFunction := by
  apply Continuous.if ?_ continuous_const (Continuous.if ?_ continuous_const continuous_id)
    <;> intro a ha
  · rw [@Set.Iic_def, @frontier_Iic, @Set.mem_singleton_iff] at ha
    rw [ha]
    simp only [le_neg_self_iff, id_eq]
    have h1 : ¬ (1 : ℝ) ≤ 0 := by simp
    exact Eq.symm (if_neg h1)
  · rw [Set.Ici_def, @frontier_Ici, @Set.mem_singleton_iff] at ha
    exact id (Eq.symm ha)

/-- The continuous map from `lorentzGroup` to `ℝ` wh
taking Orthochronous elements to `1` and non-orthochronous to `-1`. -/
def orthchroMapReal : C(LorentzGroup d, ℝ) := ContinuousMap.comp
  ⟨stepFunction, stepFunction_continuous⟩ timeCompCont

/-- A Lorentz transformation which is orthochronous maps under `orthchroMapReal` to `1`. -/
lemma orthchroMapReal_on_IsOrthochronous {Λ : LorentzGroup d} (h : IsOrthochronous Λ) :
    orthchroMapReal Λ = 1 := by
  rw [isOrthochronous_iff_ge_one] at h
  change stepFunction (Λ.1 _ _) = 1
  rw [stepFunction, if_pos h, if_neg]
  linarith

/-- A Lorentz transformation which is not-orthochronous maps under `orthchroMapReal` to `- 1`. -/
lemma orthchroMapReal_on_not_IsOrthochronous {Λ : LorentzGroup d} (h : ¬ IsOrthochronous Λ) :
    orthchroMapReal Λ = - 1 := by
  rw [not_isOrthochronous_iff_le_neg_one] at h
  change stepFunction _ = - 1
  rw [stepFunction, if_pos]
  exact h

/-- Every Lorentz transformation maps under `orthchroMapReal` to either `1` or `-1`. -/
lemma orthchroMapReal_minus_one_or_one (Λ : LorentzGroup d) :
    orthchroMapReal Λ = -1 ∨ orthchroMapReal Λ = 1 := by
  by_cases h : IsOrthochronous Λ
  · exact Or.inr $ orthchroMapReal_on_IsOrthochronous h
  · exact Or.inl $ orthchroMapReal_on_not_IsOrthochronous h

local notation "ℤ₂" => Multiplicative (ZMod 2)

/-- A continuous map from `lorentzGroup` to `ℤ₂` whose kernel are the Orthochronous elements. -/
def orthchroMap : C(LorentzGroup d, ℤ₂) :=
  ContinuousMap.comp coeForℤ₂ {
    toFun := fun Λ => ⟨orthchroMapReal Λ, orthchroMapReal_minus_one_or_one Λ⟩,
    continuous_toFun := Continuous.subtype_mk (ContinuousMap.continuous orthchroMapReal) _}

/-- A Lorentz transformation which is orthochronous maps under `orthchroMap` to `1`
  in `ℤ₂` (the identity element). -/
lemma orthchroMap_IsOrthochronous {Λ : LorentzGroup d} (h : IsOrthochronous Λ) :
    orthchroMap Λ = 1 := by
  simp [orthchroMap, orthchroMapReal_on_IsOrthochronous h]

/-- A Lorentz transformation which is not-orthochronous maps under `orthchroMap` to
  the non-identity element of `ℤ₂`. -/
lemma orthchroMap_not_IsOrthochronous {Λ : LorentzGroup d} (h : ¬ IsOrthochronous Λ) :
    orthchroMap Λ = Additive.toMul (1 : ZMod 2) := by
  simp only [orthchroMap, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    orthchroMapReal_on_not_IsOrthochronous h, coeForℤ₂_apply, Subtype.mk.injEq, Nat.reduceAdd]
  rw [if_neg]
  · rfl
  · linarith

/-- The product of two orthochronous Lorentz transformations is orthochronous. -/
lemma isOrthochronous_mul {Λ Λ' : LorentzGroup d} (h : IsOrthochronous Λ)
    (h' : IsOrthochronous Λ') : IsOrthochronous (Λ * Λ') := by
  rw [isOrthochronous_iff_toVector_timeComponet_nonneg]
  rw [toVector_mul, smul_timeComponent_eq_toVector_minkowskiProduct]
  change _ ≤ ⟪orthochronoustoVelocity (isOrthochronous_inv_iff.mpr h),
    (orthochronoustoVelocity h').1⟫ₘ
  exact Lorentz.Velocity.zero_le_minkowskiProduct
    (orthochronoustoVelocity (isOrthochronous_inv_iff.mpr h)) (orthochronoustoVelocity h')

lemma isOrthochronous_mul_iff {Λ Λ' : LorentzGroup d} :
    IsOrthochronous (Λ * Λ') ↔ (IsOrthochronous Λ = IsOrthochronous Λ') := by
  by_cases h : IsOrthochronous Λ <;> by_cases h' : IsOrthochronous Λ'
    <;> simp [h, h']
  · rw [isOrthochronous_iff_toVector_timeComponet_nonneg]
    rw [toVector_mul, smul_timeComponent_eq_toVector_minkowskiProduct]
    trans ⟪orthochronoustoVelocity (isOrthochronous_inv_iff.mpr h),
      (orthochronoustoVelocity h').1⟫ₘ
    · exact Lorentz.Velocity.zero_le_minkowskiProduct
        (orthochronoustoVelocity (isOrthochronous_inv_iff.mpr h)) (orthochronoustoVelocity h')
    · rfl
  · rw [not_isOrthochronous_iff_toVector_timeComponet_nonpos]
    rw [toVector_mul, smul_timeComponent_eq_toVector_minkowskiProduct]
    trans - ⟪orthochronoustoVelocity (isOrthochronous_inv_iff.mpr h),
      (orthochronoustoVelocity (neg_isOrthochronous_iff_not.mpr h')).1⟫ₘ
    · simp [orthochronoustoVelocity, toVector_neg]
    · simp
      exact Lorentz.Velocity.zero_le_minkowskiProduct _ _
  · rw [not_isOrthochronous_iff_toVector_timeComponet_nonpos]
    rw [toVector_mul, smul_timeComponent_eq_toVector_minkowskiProduct]
    trans - ⟪orthochronoustoVelocity
      (isOrthochronous_inv_iff.mpr (neg_isOrthochronous_iff_not.mpr h)),
      (orthochronoustoVelocity h').1⟫ₘ
    · simp only [orthochronoustoVelocity, inv_neg, toVector_neg]
      simp
    · simp
      exact Lorentz.Velocity.zero_le_minkowskiProduct _ _
  · rw [isOrthochronous_iff_toVector_timeComponet_nonneg]
    rw [toVector_mul, smul_timeComponent_eq_toVector_minkowskiProduct]
    trans ⟪orthochronoustoVelocity
      (isOrthochronous_inv_iff.mpr (neg_isOrthochronous_iff_not.mpr h)),
      (orthochronoustoVelocity (neg_isOrthochronous_iff_not.mpr h')).1⟫ₘ
    · exact Lorentz.Velocity.zero_le_minkowskiProduct _ _
    · simp [orthochronoustoVelocity, toVector_neg, LorentzGroup.inv_neg]

/-- The homomorphism from `LorentzGroup` to `ℤ₂`. -/
def orthchroRep : LorentzGroup d →* ℤ₂ where
  toFun := orthchroMap
  map_one' := orthchroMap_IsOrthochronous (by simp [IsOrthochronous])
  map_mul' Λ Λ' := by
    by_cases h : IsOrthochronous Λ
      <;> by_cases h' : IsOrthochronous Λ'
    · rw [orthchroMap_IsOrthochronous h, orthchroMap_IsOrthochronous h',
        orthchroMap_IsOrthochronous]
      · rfl
      · rw [isOrthochronous_mul_iff]
        simp_all
    · rw [orthchroMap_IsOrthochronous h, orthchroMap_not_IsOrthochronous h',
        orthchroMap_not_IsOrthochronous]
      · rfl
      · rw [isOrthochronous_mul_iff]
        simp_all
    · rw [orthchroMap_not_IsOrthochronous h, orthchroMap_IsOrthochronous h',
        orthchroMap_not_IsOrthochronous]
      · rfl
      · rw [isOrthochronous_mul_iff]
        simp_all
    · rw [orthchroMap_not_IsOrthochronous h, orthchroMap_not_IsOrthochronous h',
        orthchroMap_IsOrthochronous]
      · rfl
      · rw [isOrthochronous_mul_iff]
        simp_all

/-- The orthochronous Lorentz transformations form the kernel of the homomorphism from
  `LorentzGroup` to `ℤ₂`. -/
lemma IsOrthochronous.iff_in_orthchroRep_ker : IsOrthochronous Λ ↔ Λ ∈ orthchroRep.ker := by
  constructor
  · exact orthchroMap_IsOrthochronous
  · intro h
    contrapose! h
    apply orthchroMap_not_IsOrthochronous at h
    change orthchroRep Λ = _ at h
    rw [MonoidHom.mem_ker, h]
    trivial

/-- The homomorphism from `LorentzGroup` to `ℤ₂` assigns the same value to any Lorentz
  transformation and its inverse. -/
lemma orthchroRep_inv_eq_self (Λ : LorentzGroup d) : orthchroRep Λ = orthchroRep Λ⁻¹ := by
  by_cases h_orth : IsOrthochronous Λ
  · have hΛ_1 : orthchroRep Λ = (1 : ℤ₂) := by exact orthchroMap_IsOrthochronous h_orth
    rw [map_inv orthchroRep Λ, hΛ_1]
    rfl
  · have hΛ_0 : orthchroRep Λ = (1 : ZMod 2) := by exact orthchroMap_not_IsOrthochronous h_orth
    rw [map_inv orthchroRep Λ, hΛ_0]
    rfl

/-- Two Lorentz transformations are both orthochronous or both not orthochronous if they are mapped
to the same element via the homomorphism from `LorentzGroup` to `ℤ₂`. -/
lemma isOrthochronous_iff_of_orthchroMap_eq {Λ Λ' : LorentzGroup d}
    (h : orthchroMap Λ = orthchroMap Λ') : IsOrthochronous Λ ↔ IsOrthochronous Λ' := by
  rw [IsOrthochronous.iff_in_orthchroRep_ker, IsOrthochronous.iff_in_orthchroRep_ker]
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  change orthchroMap Λ = 1 ↔ orthchroMap Λ' = 1
  rw [h]

/-- Two Lorentz transformations which are in the same connected component are either both
orthochronous or both not orthochronous. -/
lemma isOrthochronous_on_connected_component {Λ Λ' : LorentzGroup d}
    (h : Λ' ∈ connectedComponent Λ) : IsOrthochronous Λ ↔ IsOrthochronous Λ' := by
  obtain ⟨s, hs, hΛ'⟩ := h
  let f : ContinuousMap s ℤ₂ := ContinuousMap.restrict s orthchroMap
  haveI : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs.1
  have h_eq : orthchroMap Λ = orthchroMap Λ' := by
    apply IsPreconnected.subsingleton (isPreconnected_range f.continuous_toFun)
    · exact Set.mem_range_self (⟨Λ, hs.2⟩ : {x : LorentzGroup d | x ∈ s})
    · exact Set.mem_range_self (⟨Λ', hΛ'⟩ : {x : LorentzGroup d | x ∈ s})
  exact isOrthochronous_iff_of_orthchroMap_eq h_eq

end LorentzGroup

end
