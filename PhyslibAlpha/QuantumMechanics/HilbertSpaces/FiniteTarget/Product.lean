/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.Basic
/-!

# Operators on one coordinate of a product of finite targets

## i. Overview

A system whose configurations are pairs `(a, b)` has the Hilbert space `𝓗[α × β]`. An operator
`A` on `𝓗[α]` acts on the first coordinate alone, `(A Ψ) (a, b) = ∑ a', ⟨a|A|a'⟩ Ψ (a', b)`,
and leaves the second in place; an operator on `𝓗[β]` acts on the second coordinate in the same
way. Operators on different coordinates commute, acting twice on one coordinate composes the
operators, and hermitian operators stay hermitian.

## ii. Key results

- `onFst`, `onSnd` : an operator acting on one coordinate of `𝓗[α × β]`.
- `onFst_comp`, `onSnd_comp` : acting twice on the same coordinate.
- `onFst_comp_onSnd` : operators on different coordinates commute.
- `onFst_isSymmetric`, `onSnd_isSymmetric` : hermitian operators stay hermitian.

## iii. Table of contents

- A. Amplitudes
- B. Operators on one coordinate
- C. Composition
- D. Hermiticity

-/

@[expose] public section

namespace QuantumMechanics

namespace FiniteHilbertSpace

open InnerProductSpace

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-!

## A. Amplitudes

-/

/-- The amplitude `⟨a|A|a'⟩` of an operator is the `a` component of `A |a'⟩`. -/
lemma val_apply_basisFun (A : 𝓗[α] →ₗ[ℂ] 𝓗[α]) (a a' : α) :
    (A (basisFun α a')).val a = ⟪basisFun α a, A (basisFun α a')⟫_ℂ := by
  rw [inner_eq_val, basisFun_apply a, EuclideanSpace.inner_single_left, map_one, one_mul]

/-- An operator in components: `(A ψ) a = ∑ a', ⟨a|A|a'⟩ ψ a'`. -/
lemma val_apply (A : 𝓗[α] →ₗ[ℂ] 𝓗[α]) (ψ : 𝓗[α]) (a : α) :
    (A ψ).val a = ∑ a', (A (basisFun α a')).val a * ψ.val a' := by
  conv_lhs => rw [← (basisFun α).sum_repr ψ]
  simp only [map_sum, map_smul]
  change (linearEquivEuclidean (∑ a', _)) a = _
  rw [map_sum]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, map_smul, OrthonormalBasis.repr_apply_apply,
    inner_eq_val, basisFun_apply, EuclideanSpace.inner_single_left, map_one, one_mul]
  exact Finset.sum_congr rfl fun a' _ => by rw [mul_comm]; rfl

/-!

## B. Operators on one coordinate

-/

/-- The operator `A` acting on the first coordinate: `(A Ψ) (a, b) = ∑ a', ⟨a|A|a'⟩ Ψ (a', b)`. -/
noncomputable def onFst (A : 𝓗[α] →ₗ[ℂ] 𝓗[α]) : 𝓗[α × β] →ₗ[ℂ] 𝓗[α × β] where
  toFun Ψ := ⟨WithLp.toLp 2 fun p => ∑ a, (A (basisFun α a)).val p.1 * Ψ.val (a, p.2)⟩
  map_add' Ψ Φ := by
    ext p
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c Ψ := by
    ext p
    simp [Finset.mul_sum, mul_left_comm]

/-- The operator `B` acting on the second coordinate: `(B Ψ) (a, b) = ∑ b', ⟨b|B|b'⟩ Ψ (a, b')`. -/
noncomputable def onSnd (B : 𝓗[β] →ₗ[ℂ] 𝓗[β]) : 𝓗[α × β] →ₗ[ℂ] 𝓗[α × β] where
  toFun Ψ := ⟨WithLp.toLp 2 fun p => ∑ b, (B (basisFun β b)).val p.2 * Ψ.val (p.1, b)⟩
  map_add' Ψ Φ := by
    ext p
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c Ψ := by
    ext p
    simp [Finset.mul_sum, mul_left_comm]

lemma onFst_val (A : 𝓗[α] →ₗ[ℂ] 𝓗[α]) (Ψ : 𝓗[α × β]) (p : α × β) :
    (onFst A Ψ).val p = ∑ a, (A (basisFun α a)).val p.1 * Ψ.val (a, p.2) := rfl

lemma onSnd_val (B : 𝓗[β] →ₗ[ℂ] 𝓗[β]) (Ψ : 𝓗[α × β]) (p : α × β) :
    (onSnd B Ψ).val p = ∑ b, (B (basisFun β b)).val p.2 * Ψ.val (p.1, b) := rfl

/-!

## C. Composition

-/

/-- Acting twice on the first coordinate composes the operators. -/
lemma onFst_comp (A A' : 𝓗[α] →ₗ[ℂ] 𝓗[α]) :
    onFst (β := β) (A ∘ₗ A') = onFst A ∘ₗ onFst A' := by
  ext Ψ p
  simp only [LinearMap.comp_apply, onFst_val]
  simp only [val_apply A (A' _), Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- Acting twice on the second coordinate composes the operators. -/
lemma onSnd_comp (B B' : 𝓗[β] →ₗ[ℂ] 𝓗[β]) :
    onSnd (α := α) (B ∘ₗ B') = onSnd B ∘ₗ onSnd B' := by
  ext Ψ p
  simp only [LinearMap.comp_apply, onSnd_val]
  simp only [val_apply B (B' _), Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- Operators on different coordinates commute. -/
lemma onFst_comp_onSnd (A : 𝓗[α] →ₗ[ℂ] 𝓗[α]) (B : 𝓗[β] →ₗ[ℂ] 𝓗[β]) :
    onFst A ∘ₗ onSnd B = onSnd B ∘ₗ onFst A := by
  ext Ψ p
  simp only [LinearMap.comp_apply, onFst_val, onSnd_val, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-!

## D. Hermiticity

-/

/-- The inner product of `𝓗[α × β]` in components. -/
lemma inner_eq_sum (Ψ Φ : 𝓗[α × β]) :
    ⟪Ψ, Φ⟫_ℂ = ∑ p, (starRingEnd ℂ) (Ψ.val p) * Φ.val p := by
  rw [inner_eq_val, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun p _ => by rw [RCLike.inner_apply, mul_comm]

/-- Hermitian amplitudes: `conj ⟨a'|A|a⟩ = ⟨a|A|a'⟩`. -/
lemma conj_val_apply_basisFun {A : 𝓗[α] →ₗ[ℂ] 𝓗[α]} (hA : A.IsSymmetric) (a a' : α) :
    (starRingEnd ℂ) ((A (basisFun α a)).val a') = (A (basisFun α a')).val a := by
  rw [val_apply_basisFun, val_apply_basisFun, inner_conj_symm, hA]

/-- A hermitian operator on the first coordinate is hermitian. -/
lemma onFst_isSymmetric {A : 𝓗[α] →ₗ[ℂ] 𝓗[α]} (hA : A.IsSymmetric) :
    (onFst (β := β) A).IsSymmetric := fun Ψ Φ => by
  simp only [inner_eq_sum, onFst_val, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    Fintype.sum_prod_type]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => by
    rw [conj_val_apply_basisFun hA]
    ring

/-- A hermitian operator on the second coordinate is hermitian. -/
lemma onSnd_isSymmetric {B : 𝓗[β] →ₗ[ℂ] 𝓗[β]} (hB : B.IsSymmetric) :
    (onSnd (α := α) B).IsSymmetric := fun Ψ Φ => by
  simp only [inner_eq_sum, onSnd_val, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by
    rw [conj_val_apply_basisFun hB]
    ring

end FiniteHilbertSpace

end QuantumMechanics
