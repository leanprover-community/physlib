/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.Basic
/-!

# Symmetric operators

## i. Overview

A symmetric operator `T` on an inner product space is one for which `⟪T x, y⟫ = ⟪x, T y⟫`
for all `x` and `y` in its domain. When `H` is complete (a Hilbert space) this is a weaker notio
than `T` being self-adjoint: it amounts to `T ≤ T†` rather than `T = T†`.

This module is dedicated to defining the `IsSymmetric` property and collecting its basic properties.
For aspects of the spectral theory of symmetric operators
see `Physlib.QuantumMechanics.Operators.SpectralTheory.Symmetric`.

## ii. Key results

- `IsSymmetric` : An operator `T` is symmetric if `⟪T x, y⟫ = ⟪x, T y⟫` for all `x` and `y` in its
  domain.
- `isSymmetric_iff_inner_map_self_real` : An operator `T` is symmetric *if and only if* `⟪T x, x⟫`
  is real for all `x` in its domain.
- `isSymmetric_iff_le_adjoint` : An operator `T` is symmetric *if and only if* `T ≤ T†`.
- `add_adjoint_isSymmetric` : For *any* densely-defined operator `T`, `T + T†` is symmetric.

## iii. Table of contents

- A. Definition of symmetric operator
- B. Criteria for symmetric operators
- C. Properties
- D. Unbounded operator from symmetric endomorphism

## iv. References

-/

@[expose] public section

namespace LinearPMap

open Complex
open scoped ComplexConjugate InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {T T₂ : H →ₗ.[ℂ] H}

/-!
## A. Definition of symmetric operator
-/

/-- An operator `T` is symmetric if `⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ` for all `x y : T.domain`. -/
def IsSymmetric (T : H →ₗ.[ℂ] H) : Prop := T.IsFormalAdjoint T

lemma isSymmetric_def : T.IsSymmetric ↔ T.IsFormalAdjoint T := Iff.rfl

/-!
## B. Criteria for symmetric operators
-/

-- The analogue of `LinearMap.isSymmetric_iff_inner_map_self_real` for LinearPMap.
lemma isSymmetric_iff_inner_map_self_real :
    T.IsSymmetric ↔ ∀ x : T.domain, conj ⟪T x, x⟫_ℂ = ⟪T x, x⟫_ℂ := by
  refine ⟨fun h_symm x ↦ by simp [h_symm x x], fun h_re x y ↦ ?_⟩
  nth_rw 2 [← inner_conj_symm, inner_map_polarization]
  simp only [map_div₀, _root_.map_sub, _root_.map_add, map_mul, neg_mul, conj_ofNat, conj_I, h_re]
  rw [inner_map_polarization']
  simp [sub_eq_add_neg]

/-- A densely-defined operator on a Hilbert space is symmetric *if and only if*
it has its adjoint as an extension. -/
lemma isSymmetric_iff_le_adjoint [CompleteSpace H] (h : T.HasDenseDomain) :
    T.IsSymmetric ↔ T ≤ T† := by
  refine ⟨fun h_symm ↦ h_symm.le_adjoint h, fun h_le x y ↦ ?_⟩
  have h_eq : T x = T† ⟨x, h_le.1 x.2⟩ := @h_le.2 x ⟨x, h_le.1 x.2⟩ rfl
  exact h_eq ▸ adjoint_isFormalAdjoint h _ _

/-- For a densely-defined operator `T` on a Hilbert space, `T + T†` is symmetric. -/
lemma add_adjoint_isSymmetric [CompleteSpace H] (h : T.HasDenseDomain) : (T + T†).IsSymmetric := by
  intro x y
  have h₁ := adjoint_isFormalAdjoint h ⟨x, x.2.2⟩ ⟨y, y.2.1⟩
  have h₂ := congrArg conj (adjoint_isFormalAdjoint h ⟨y, y.2.2⟩ ⟨x, x.2.1⟩)
  simp only [inner_conj_symm] at h₂
  simp only [add_apply, inner_add_left, inner_add_right, h₁, h₂]
  exact add_comm _ _

/-!
## C. Properties
-/

namespace IsSymmetric

variable (h : T.IsSymmetric)

include h

/-- A densely-defined symmetric operator on a Hilbert space is closable. -/
lemma isClosable [CompleteSpace H] (h' : T.HasDenseDomain) : T.IsClosable :=
  isClosable_iff_exists_closed_extension.mpr ⟨T†, adjoint_isClosed h', h.le_adjoint h'⟩

/-- A symmetric operator on a Hilbert space is unbounded (densely defined and closed)
*if and only if* it is densely defined. -/
lemma isUnbounded_iff_hasDenseDomain [CompleteSpace H] : T.IsUnbounded ↔ T.HasDenseDomain :=
  and_iff_left_of_imp h.isClosable

/-- The adjoint of a densely-defined symmetric operator is an extension of its closure. -/
lemma closure_le_adjoint [CompleteSpace H] (h' : T.HasDenseDomain) : T.closure ≤ T† := by
  have h_adj : T†.IsClosed := adjoint_isClosed h'
  exact h_adj.closure_eq ▸ h_adj.isClosable.closure_mono (h.le_adjoint h')

@[aesop safe apply]
protected lemma pow (n : ℕ) : (T ^ n).IsSymmetric := by
  induction n with
  | zero => exact fun _ _ ↦ rfl
  | succ n ih =>
    intro x y
    let y' : (T * T ^ n).domain := ⟨y, pow_succ' T n ▸ y.2⟩
    let Tx : (T ^ n).domain := ⟨T ⟨x, x.2.2⟩, mem_domain_of_mem_compRestricted_domain x⟩
    let Tny : T.domain := ⟨(T ^ n) ⟨y', y'.2.2⟩, mem_domain_of_mem_compRestricted_domain y'⟩
    have h_eq : T Tny = (T ^ (n + 1)) y := by
      change (T * T ^ n) y' = (T ^ (n + 1)) y
      congr 1
      · exact (pow_succ' T n).symm
      · exact (Subtype.heq_iff_coe_eq <| by simp [pow_succ']).mpr rfl
    exact (ih Tx ⟨y', y'.2.2⟩).trans (h_eq ▸ h ⟨x, x.2.2⟩ Tny)

@[aesop safe apply]
protected lemma neg : (-T).IsSymmetric := fun x y ↦ by simp [h x y]

@[aesop safe apply]
protected lemma add (h₂ : T₂.IsSymmetric) : (T + T₂).IsSymmetric := by
  intro x y
  simp [h ⟨x, x.2.1⟩ ⟨y, y.2.1⟩, h₂ ⟨x, x.2.2⟩ ⟨y, y.2.2⟩, add_apply, inner_add_left,
    inner_add_right]

@[aesop safe apply]
protected lemma sub (h₂ : T₂.IsSymmetric) : (T - T₂).IsSymmetric :=
  sub_eq_add_neg T T₂ ▸ h.add h₂.neg

@[aesop safe apply]
protected lemma smul {c : ℂ} (hc : conj c = c) : (c • T).IsSymmetric :=
  fun x y ↦ by simp only [smul_apply, inner_smul_left, inner_smul_right, hc, h x y]

@[aesop safe apply]
protected lemma real_smul (r : ℝ) : (r • T).IsSymmetric := h.smul (conj_ofReal r)

omit h in
@[aesop safe apply]
protected lemma sum {α : Type*} [Fintype α] {S : α → H →ₗ.[ℂ] H} (h : ∀ a, (S a).IsSymmetric) :
    (sum S).IsSymmetric := by
  intro x y
  simp [sum_apply, sum_inner, inner_sum, h _ ⟨x, sum_domain_le S _ x.2⟩ ⟨y, sum_domain_le S _ y.2⟩]

protected lemma of_le (h_le : T₂ ≤ T) : T₂.IsSymmetric := by
  intro x y
  have hx : T₂ x = T ⟨x, h_le.1 x.2⟩ := @h_le.2 x ⟨x, h_le.1 x.2⟩ rfl
  have hy : T₂ y = T ⟨y, h_le.1 y.2⟩ := @h_le.2 y ⟨y, h_le.1 y.2⟩ rfl
  exact hx ▸ hy ▸ h ⟨x, h_le.1 x.2⟩ ⟨y, h_le.1 y.2⟩

/-- The closure of a symmetric densely-defined operator is symmetric: `T††` is a symmetric
closed extension of `T`, so it extends `T.closure`, whose symmetry then descends. -/
lemma closure [CompleteSpace H] (h' : T.HasDenseDomain) : T.closure.IsSymmetric := by
  have hle : T ≤ T† := (isSymmetric_def.mp h).le_adjoint h'
  have hadj_dense : T†.HasDenseDomain := h'.mono hle.1
  have hT_le : T ≤ T†† := (adjoint_isFormalAdjoint h').le_adjoint hadj_dense
  have hc : (T††).IsClosed := adjoint_isClosed hadj_dense
  have h1 : (T††).IsSymmetric :=
    (isSymmetric_iff_le_adjoint (h'.mono hT_le.1)).mpr
      (adjoint_antitone (Or.inl (h'.mono hT_le.1)) (adjoint_antitone (Or.inl h') hle))
  exact h1.of_le (hc.closure_eq ▸ hc.isClosable.closure_mono hT_le)

end IsSymmetric

/-!
## D. Unbounded operator from symmetric endomorphism
-/

/-- A LinearPMap constructed from a symmetric LinearMap with dense domain
  is an unbounded operator. -/
lemma isUnbounded_of_dense_of_isSymmetric [CompleteSpace H] {E : Submodule ℂ H}
    (hE : Dense (E : Set H)) {f : E →ₗ[ℂ] H} (h : ∀ x y : E, ⟪f x, ↑y⟫_ℂ = ⟪↑x, f y⟫_ℂ) :
    (mk E f).IsUnbounded :=
  ⟨hE, IsSymmetric.isClosable h hE⟩

/-- Variant of `isUnbounded_of_dense_of_isSymmetric` for an endomorphism
satisfying `LinearMap.IsSymmetric`. -/
lemma isUnbounded_of_dense_of_isSymmetric' [CompleteSpace H]
    {E : Submodule ℂ H} (hE : Dense (E : Set H)) {f : E →ₗ[ℂ] E} (h : f.IsSymmetric) :
    (mk E (E.subtype ∘ₗ f)).IsUnbounded :=
  ⟨hE, IsSymmetric.isClosable h hE⟩

end LinearPMap
