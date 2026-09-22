/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.HarmonicOscillator.Basic
public import Physlib.QuantumMechanics.Operators.Commutation
/-!

# Ladder operators

## i. Overview

The ladder operators of the `d`-dimensional quantum harmonic oscillator, acting on Schwartz maps:
the lowering (annihilation) operators `aᵢ = (xᵢ/ξᵢ + i ξᵢ pᵢ/ℏ)/√2` and the raising (creation)
operators `aᵢ† = (xᵢ/ξᵢ - i ξᵢ pᵢ/ℏ)/√2`, together with
their commutation relations, which all follow from the canonical commutation relations
`position_commutation_momentum`. The ladder operators are then lifted to unbounded operators on the
Hilbert space with the Schwartz submodule as domain (like `momentumOperator`), `aᵢ†` being the
formal adjoint of `aᵢ`. The number operators `Nᵢ = aᵢ† aᵢ` and the Hamiltonian written through them
are in `NumberOperator.lean`.

## ii. Key results

- `lowering_commutation_raising`: `[aᵢ, aⱼ†] = δᵢⱼ 𝟙`; `lowering_commutation_lowering`,
  `raising_commutation_raising`: `[aᵢ, aⱼ] = 0`, `[aᵢ†, aⱼ†] = 0`.
- `position_eq_lowering_add_raising`, `momentum_eq_raising_sub_lowering`: the position and
  momentum operators in terms of the ladder operators.
- `loweringOperator_isFormalAdjoint_raisingOperator`: `aᵢ†` is the formal adjoint of `aᵢ`.

## iii. Table of contents

- A. Ladder operators
  - A.1. Definitions
  - A.2. Commutation relations
  - A.3. Position and momentum in terms of the ladder operators
  - A.4. The ladder operators as unbounded operators, adjointness

## iv. References

* None.

-/

@[expose] public section

noncomputable section
namespace QuantumMechanics.HarmonicOscillator

open Complex Constants KroneckerDelta Bracket SchwartzMap ContinuousLinearMap SpaceDHilbertSpace
open MeasureTheory SchwartzSubmodule
open scoped InnerProductSpace

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 100] LieAlgebra.ofAssociativeAlgebra

variable {d : ℕ} (Q : HarmonicOscillator d) (i j : Fin d)

/-!

## A. Ladder operators

-/

/-!

### A.1. Definitions

-/

/-- The lowering (annihilation) operator `aᵢ = (xᵢ/ξᵢ + i ξᵢ pᵢ/ℏ)/√2`, as a continuous linear
  map on Schwartz maps. -/
def loweringCLM : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (Real.sqrt 2 : ℂ)⁻¹ • (((Q.ξ i : ℝ) : ℂ)⁻¹ • 𝐱 i + (I * ((Q.ξ i : ℝ) : ℂ) / (ℏ : ℂ)) • 𝐩 i)

/-- The raising (creation) operator `aᵢ† = (xᵢ/ξᵢ - i ξᵢ pᵢ/ℏ)/√2`, as a continuous linear
  map on Schwartz maps. -/
def raisingCLM : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (Real.sqrt 2 : ℂ)⁻¹ • (((Q.ξ i : ℝ) : ℂ)⁻¹ • 𝐱 i - (I * ((Q.ξ i : ℝ) : ℂ) / (ℏ : ℂ)) • 𝐩 i)

lemma loweringCLM_eq : Q.loweringCLM i =
    (Real.sqrt 2 : ℂ)⁻¹ • (((Q.ξ i : ℝ) : ℂ)⁻¹ • 𝐱 i + (I * ((Q.ξ i : ℝ) : ℂ) / (ℏ : ℂ)) • 𝐩 i) :=
  rfl

lemma raisingCLM_eq : Q.raisingCLM i =
    (Real.sqrt 2 : ℂ)⁻¹ • (((Q.ξ i : ℝ) : ℂ)⁻¹ • 𝐱 i - (I * ((Q.ξ i : ℝ) : ℂ) / (ℏ : ℂ)) • 𝐩 i) :=
  rfl

/-- `(√2)² = 2` as complex numbers. -/
lemma sqrt_two_sq_ofReal : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-!

### A.2. Commutation relations

-/

/-- `[aᵢ, aⱼ†] = δᵢⱼ 𝟙`. -/
lemma lowering_commutation_raising :
    ⁅Q.loweringCLM i, Q.raisingCLM j⁆ = δ[i,j] • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  simp only [loweringCLM, raisingCLM, lie_smul, smul_lie, add_lie, lie_sub,
    position_commutation_position, momentum_commutation_momentum, position_commutation_momentum,
    ← lie_skew (𝐩 i) (𝐱 j), smul_zero, zero_add, smul_neg, smul_smul, KroneckerDelta.symm j i]
  rcases eq_or_ne i j with rfl | hne
  · simp only [eq_one_of_same, one_nsmul, add_zero]
    ext ψ x
    simp only [smul_apply, neg_apply, sub_apply, id_apply, smul_eq_mul]
    have hξ := Q.ξ_ofReal_ne_zero i
    have hℏ := ℏ_ofReal_ne_zero
    ring_nf
    rw [I_sq, inv_pow, sqrt_two_sq_ofReal]
    field_simp
  · simp only [eq_zero_of_ne hne, zero_smul, smul_zero, sub_zero, neg_zero, add_zero]

/-- `[aᵢ, aⱼ] = 0`. -/
lemma lowering_commutation_lowering : ⁅Q.loweringCLM i, Q.loweringCLM j⁆ = 0 := by
  simp only [loweringCLM, lie_smul, smul_lie, lie_add, add_lie,
    position_commutation_position, momentum_commutation_momentum, position_commutation_momentum,
    ← lie_skew (𝐩 i) (𝐱 j), smul_zero, zero_add, smul_neg, smul_smul, KroneckerDelta.symm j i]
  rcases eq_or_ne i j with rfl | hne
  · ext ψ x
    simp only [eq_one_of_same, one_smul, add_zero, smul_add, smul_neg, add_apply, neg_apply,
      smul_apply, id_apply, smul_eq_mul, zero_apply]
    have hξ := Q.ξ_ofReal_ne_zero i
    have hℏ := ℏ_ofReal_ne_zero
    field_simp
    ring
  · simp [eq_zero_of_ne hne]

/-- `[aᵢ†, aⱼ†] = 0`. -/
lemma raising_commutation_raising : ⁅Q.raisingCLM i, Q.raisingCLM j⁆ = 0 := by
  simp only [raisingCLM, lie_smul, smul_lie, lie_sub, sub_lie,
    position_commutation_position, momentum_commutation_momentum, position_commutation_momentum,
    ← lie_skew (𝐩 i) (𝐱 j), smul_zero, zero_sub, smul_neg, smul_smul, KroneckerDelta.symm j i]
  rcases eq_or_ne i j with rfl | hne
  · ext ψ x
    simp only [eq_one_of_same, one_smul, neg_neg, sub_zero, smul_apply, sub_apply, id_apply,
      smul_eq_mul, zero_apply, mul_eq_zero, inv_eq_zero, ofReal_eq_zero, Nat.ofNat_nonneg,
      Real.sqrt_eq_zero, OfNat.ofNat_ne_zero, false_or]
    have hξ := Q.ξ_ofReal_ne_zero i
    have hℏ := ℏ_ofReal_ne_zero
    field_simp
    ring
  · simp [eq_zero_of_ne hne]

/-- `[aᵢ†, aⱼ] = -δᵢⱼ 𝟙`. -/
lemma raising_commutation_lowering :
    ⁅Q.raisingCLM i, Q.loweringCLM j⁆ = -(δ[i,j] • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ)) := by
  rw [← lie_skew, lowering_commutation_raising, KroneckerDelta.symm j i]

/-!

### A.3. Position and momentum in terms of the ladder operators

-/

/-- `xᵢ = (ξᵢ/√2) (aᵢ + aᵢ†)`. -/
lemma position_eq_lowering_add_raising :
    𝐱 i = (((Q.ξ i : ℝ) : ℂ) / (Real.sqrt 2 : ℂ)) • (Q.loweringCLM i + Q.raisingCLM i) := by
  ext ψ x
  simp [loweringCLM, raisingCLM]
  have hξ := Q.ξ_ofReal_ne_zero i
  have hℏ := ℏ_ofReal_ne_zero
  ring_nf
  rw [inv_pow, sqrt_two_sq_ofReal]
  field_simp

/-- `pᵢ = (i ℏ/(√2 ξᵢ)) (aᵢ† - aᵢ)`. -/
lemma momentum_eq_raising_sub_lowering :
    𝐩 i = (I * (ℏ : ℂ) / ((Real.sqrt 2 : ℂ) * ((Q.ξ i : ℝ) : ℂ))) •
      (Q.raisingCLM i - Q.loweringCLM i) := by
  ext ψ x
  simp [loweringCLM, raisingCLM]
  have hξ := Q.ξ_ofReal_ne_zero i
  have hℏ := ℏ_ofReal_ne_zero
  ring_nf
  rw [I_pow_three, inv_pow, sqrt_two_sq_ofReal]
  field_simp

/-!

### A.4. The ladder operators as unbounded operators, adjointness

-/

/-- The lowering operator as an unbounded operator with domain the Schwartz submodule. -/
def loweringOperator : Q.HS →ₗ.[ℂ] Q.HS where
  domain := SchwartzSubmodule d
  toFun := (schwartzIncl volume).1 ∘ₗ (Q.loweringCLM i).1 ∘ₗ (schwartzEquiv volume).symm.1

/-- The raising operator as an unbounded operator with domain the Schwartz submodule. -/
def raisingOperator : Q.HS →ₗ.[ℂ] Q.HS where
  domain := SchwartzSubmodule d
  toFun := (schwartzIncl volume).1 ∘ₗ (Q.raisingCLM i).1 ∘ₗ (schwartzEquiv volume).symm.1

lemma loweringOperator_apply (ψ : SchwartzSubmodule d) :
    Q.loweringOperator i ψ =
      schwartzEquiv volume (Q.loweringCLM i ((schwartzEquiv volume).symm ψ)) :=
  rfl

lemma raisingOperator_apply (ψ : SchwartzSubmodule d) :
    Q.raisingOperator i ψ =
      schwartzEquiv volume (Q.raisingCLM i ((schwartzEquiv volume).symm ψ)) :=
  rfl

/-- `⟪aᵢ f, g⟫ = ⟪f, aᵢ† g⟫` for Schwartz maps `f`, `g`. -/
lemma loweringCLM_inner (f g : 𝓢(Space d, ℂ)) :
    ⟪(schwartzEquiv volume (Q.loweringCLM i f) : Q.HS), schwartzEquiv volume g⟫_ℂ
      = ⟪(schwartzEquiv volume f : Q.HS), schwartzEquiv volume (Q.raisingCLM i g)⟫_ℂ := by
  simp only [loweringCLM_eq, raisingCLM_eq, map_add, map_smul, map_sub, smul_apply, add_apply,
    sub_apply, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sub, inner_add_left,
    inner_smul_left, inner_smul_right, inner_sub_right, positionCLM_inner, momentumCLM_inner]
  simp only [map_inv₀, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- `⟪aᵢ† f, g⟫ = ⟪f, aᵢ g⟫` for Schwartz maps `f`, `g`. -/
lemma raisingCLM_inner (f g : 𝓢(Space d, ℂ)) :
    ⟪(schwartzEquiv volume (Q.raisingCLM i f) : Q.HS), schwartzEquiv volume g⟫_ℂ
      = ⟪(schwartzEquiv volume f : Q.HS), schwartzEquiv volume (Q.loweringCLM i g)⟫_ℂ := by
  rw [← inner_conj_symm, ← Q.loweringCLM_inner i, inner_conj_symm]

/-- The raising operator is the formal adjoint of the lowering operator. -/
lemma loweringOperator_isFormalAdjoint_raisingOperator :
    (Q.loweringOperator i).IsFormalAdjoint (Q.raisingOperator i) := by
  intro ψ φ
  obtain ⟨f, rfl⟩ := (schwartzEquiv volume).surjective ψ
  obtain ⟨g, rfl⟩ := (schwartzEquiv volume).surjective φ
  simp only [loweringOperator_apply, raisingOperator_apply, LinearEquiv.symm_apply_apply]
  exact Q.loweringCLM_inner i f g

end QuantumMechanics.HarmonicOscillator

end
