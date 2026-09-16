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
the lowering (annihilation) operators `aᵢ = (xᵢ/ξᵢ + i ξᵢ pᵢ/ℏ)/√2`, the raising (creation)
operators `aᵢ† = (xᵢ/ξᵢ - i ξᵢ pᵢ/ℏ)/√2` and the number operators `Nᵢ = aᵢ† aᵢ`, together with
their commutation relations, which all follow from the canonical commutation relations
`position_commutation_momentum`. The ladder operators are then lifted to unbounded operators on the
Hilbert space with the Schwartz submodule as domain (like `momentumOperator`): `aᵢ†` is the formal
adjoint of `aᵢ` and `Nᵢ` is symmetric. The Hamiltonian `H_N = ∑ᵢ ℏ ωᵢ (Nᵢ + ½)` commutes with
the number operators, lowers and raises energies by `ℏ ωᵢ`, and coincides with the
kinetic-plus-potential Hamiltonian of `Basic.lean` on Schwartz maps: as unbounded operators,
`numberHamiltonian ≤ hamiltonian`. Whether the two define the same quantum system (essential
self-adjointness) is still a TODO item.

## ii. Key results

- `lowering_commutation_raising`: `[aᵢ, aⱼ†] = δᵢⱼ 𝟙`; `lowering_commutation_lowering`,
  `raising_commutation_raising`: `[aᵢ, aⱼ] = 0`, `[aᵢ†, aⱼ†] = 0`.
- `position_eq_lowering_add_raising`, `momentum_eq_raising_sub_lowering`: the position and
  momentum operators in terms of the ladder operators.
- `number_commutation_number`: `[Nᵢ, Nⱼ] = 0`; `number_commutation_lowering`,
  `number_commutation_raising`: `[Nᵢ, aⱼ] = -δᵢⱼ aⱼ`, `[Nᵢ, aⱼ†] = δᵢⱼ aⱼ†`.
- `lowering_comp_raising`: `aᵢ aᵢ† = Nᵢ + 𝟙`.
- `loweringOperator_isFormalAdjoint_raisingOperator`: `aᵢ†` is the formal adjoint of `aᵢ`;
  `numberOperator_isSymmetric`, `numberHamiltonian_isSymmetric`.
- `numberHamiltonianCLM_commutation_lowering`, `numberHamiltonianCLM_commutation_raising`,
  `numberHamiltonianCLM_commutation_number`: `[H_N, aᵢ] = -ℏ ωᵢ aᵢ`, `[H_N, aᵢ†] = ℏ ωᵢ aᵢ†`,
  `[H_N, Nᵢ] = 0`.
- `numberHamiltonianCLM_apply`: `H_N ψ = (1/2m) ∑ᵢ pᵢ (pᵢ ψ) + V ψ` on Schwartz maps;
  `numberHamiltonian_le_hamiltonian`: `numberHamiltonian ≤ hamiltonian` as unbounded operators.

## iii. Table of contents

- A. Ladder operators
  - A.1. Definitions
  - A.2. Commutation relations
  - A.3. Position and momentum in terms of the ladder operators
  - A.4. The ladder operators as unbounded operators, adjointness
- B. Number operators
  - B.1. Definition
  - B.2. Commutation relations
  - B.3. The number operators as unbounded operators, symmetry
- C. Hamiltonian
  - C.1. The Hamiltonian in terms of the number operators
  - C.2. Commutation relations
  - C.3. Relation to the kinetic-plus-potential Hamiltonian

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

/-!

## B. Number operators

-/

/-!

### B.1. Definition

-/

/-- The number operator `Nᵢ = aᵢ† aᵢ`. -/
def numberCLM : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) := Q.raisingCLM i ∘L Q.loweringCLM i

lemma numberCLM_eq : Q.numberCLM i = Q.raisingCLM i ∘L Q.loweringCLM i := rfl

/-!

### B.2. Commutation relations

-/

/-- `[Nᵢ, aⱼ] = -δᵢⱼ aⱼ`. -/
lemma number_commutation_lowering :
    ⁅Q.numberCLM i, Q.loweringCLM j⁆ = -(δ[i,j] • Q.loweringCLM j) := by
  rw [numberCLM_eq, leibniz_lie, lowering_commutation_lowering, raising_commutation_lowering,
    comp_zero, zero_add, neg_comp, smul_comp, id_comp]
  rcases eq_or_ne i j with rfl | hne
  · rfl
  · simp [eq_zero_of_ne hne]

/-- `[Nᵢ, aⱼ†] = δᵢⱼ aⱼ†`. -/
lemma number_commutation_raising :
    ⁅Q.numberCLM i, Q.raisingCLM j⁆ = δ[i,j] • Q.raisingCLM j := by
  rw [numberCLM_eq, leibniz_lie, lowering_commutation_raising, raising_commutation_raising,
    zero_comp, add_zero, comp_smul, comp_id]
  rcases eq_or_ne i j with rfl | hne
  · rfl
  · simp [eq_zero_of_ne hne]

/-- `[Nᵢ, Nⱼ] = 0`. -/
lemma number_commutation_number : ⁅Q.numberCLM i, Q.numberCLM j⁆ = 0 := by
  simp only [numberCLM_eq]
  rw [leibniz_lie, lie_leibniz, lie_leibniz, lowering_commutation_lowering,
    lowering_commutation_raising, raising_commutation_lowering, raising_commutation_raising]
  rcases eq_or_ne i j with rfl | hne
  · simp only [eq_one_of_same, one_nsmul, comp_zero, zero_add, id_comp, comp_id, neg_comp,
      comp_neg, zero_comp, add_zero]
    abel
  · simp [eq_zero_of_ne hne]

/-- `aᵢ aᵢ† = Nᵢ + 𝟙`. -/
lemma lowering_comp_raising :
    Q.loweringCLM i ∘L Q.raisingCLM i =
      Q.numberCLM i + ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  have h := Q.lowering_commutation_raising i i
  rw [eq_one_of_same, one_nsmul, Ring.lie_def, mul_def, mul_def] at h
  rw [numberCLM_eq, add_comm]
  exact sub_eq_iff_eq_add.mp h

/-!

### B.3. The number operators as unbounded operators, symmetry

-/

/-- The number operator as an unbounded operator with domain the Schwartz submodule. -/
def numberOperator : Q.HS →ₗ.[ℂ] Q.HS where
  domain := SchwartzSubmodule d
  toFun := (schwartzIncl volume).1 ∘ₗ (Q.numberCLM i).1 ∘ₗ (schwartzEquiv volume).symm.1

lemma numberOperator_apply (ψ : SchwartzSubmodule d) :
    Q.numberOperator i ψ =
      schwartzEquiv volume (Q.numberCLM i ((schwartzEquiv volume).symm ψ)) :=
  rfl

/-- `⟪Nᵢ f, g⟫ = ⟪f, Nᵢ g⟫` for Schwartz maps `f`, `g`. -/
lemma numberCLM_inner (f g : 𝓢(Space d, ℂ)) :
    ⟪(schwartzEquiv volume (Q.numberCLM i f) : Q.HS), schwartzEquiv volume g⟫_ℂ
      = ⟪(schwartzEquiv volume f : Q.HS), schwartzEquiv volume (Q.numberCLM i g)⟫_ℂ := by
  rw [numberCLM_eq, comp_apply, Q.raisingCLM_inner i, Q.loweringCLM_inner i, comp_apply]

/-- The number operator is symmetric. -/
lemma numberOperator_isSymmetric : (Q.numberOperator i).IsSymmetric := by
  intro ψ φ
  obtain ⟨f, rfl⟩ := (schwartzEquiv volume).surjective ψ
  obtain ⟨g, rfl⟩ := (schwartzEquiv volume).surjective φ
  simp only [numberOperator_apply, LinearEquiv.symm_apply_apply]
  exact Q.numberCLM_inner i f g

TODO "Prove that the number operators are essentially self-adjoint."

/-!

## C. Hamiltonian

-/

/-!

### C.1. The Hamiltonian in terms of the number operators

-/

/-- The Hamiltonian in terms of the number operators, `H_N = ∑ᵢ ℏ ωᵢ (Nᵢ + ½)`, on Schwartz maps. -/
def numberHamiltonianCLM : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  ∑ i, ((ℏ * Q.ω i : ℝ) : ℂ) • (Q.numberCLM i + (2⁻¹ : ℂ) • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ))

lemma numberHamiltonianCLM_eq : Q.numberHamiltonianCLM =
    ∑ i, ((ℏ * Q.ω i : ℝ) : ℂ) •
      (Q.numberCLM i + (2⁻¹ : ℂ) • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ)) :=
  rfl

/-- The Hamiltonian `H_N` as an unbounded operator with domain the Schwartz submodule. -/
def numberHamiltonian : Q.HS →ₗ.[ℂ] Q.HS where
  domain := SchwartzSubmodule d
  toFun := (schwartzIncl volume).1 ∘ₗ (Q.numberHamiltonianCLM).1 ∘ₗ (schwartzEquiv volume).symm.1

lemma numberHamiltonian_apply (ψ : SchwartzSubmodule d) :
    Q.numberHamiltonian ψ =
      schwartzEquiv volume (Q.numberHamiltonianCLM ((schwartzEquiv volume).symm ψ)) :=
  rfl

/-!

### C.2. Commutation relations

-/

/-- `[H_N, aᵢ] = -ℏ ωᵢ aᵢ`. -/
lemma numberHamiltonianCLM_commutation_lowering :
    ⁅Q.numberHamiltonianCLM, Q.loweringCLM i⁆ = -(((ℏ * Q.ω i : ℝ) : ℂ) • Q.loweringCLM i) := by
  simp only [numberHamiltonianCLM_eq, sum_lie, smul_lie, add_lie, number_commutation_lowering,
    id_commutation, smul_zero, add_zero, smul_neg]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [eq_zero_of_ne hb]) (by simp)]
  simp [eq_one_of_same]

/-- `[H_N, aᵢ†] = ℏ ωᵢ aᵢ†`. -/
lemma numberHamiltonianCLM_commutation_raising :
    ⁅Q.numberHamiltonianCLM, Q.raisingCLM i⁆ = ((ℏ * Q.ω i : ℝ) : ℂ) • Q.raisingCLM i := by
  simp only [numberHamiltonianCLM_eq, sum_lie, smul_lie, add_lie, number_commutation_raising,
    id_commutation, smul_zero, add_zero]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [eq_zero_of_ne hb]) (by simp)]
  simp [eq_one_of_same]

/-- `[H_N, Nᵢ] = 0`. -/
lemma numberHamiltonianCLM_commutation_number : ⁅Q.numberHamiltonianCLM, Q.numberCLM i⁆ = 0 := by
  simp [numberHamiltonianCLM_eq, sum_lie, smul_lie, add_lie, number_commutation_number,
    id_commutation]

/-!

### C.3. Relation to the kinetic-plus-potential Hamiltonian

-/

/-- On Schwartz maps, `H_N ψ = (1/2m) ∑ᵢ pᵢ (pᵢ ψ) + V ψ`: the Hamiltonian in terms of the number
  operators is the kinetic-plus-potential Hamiltonian. -/
lemma numberHamiltonianCLM_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    Q.numberHamiltonianCLM ψ x =
      ((2 * Q.m : ℝ) : ℂ)⁻¹ * ∑ i, 𝐩 i (𝐩 i ψ) x + (Q.potentialFunction x : ℂ) * ψ x := by
  simp only [numberHamiltonianCLM_eq, FunLike.coe_sum, Finset.sum_apply, smul_apply, add_apply,
    id_apply, smul_eq_mul]
  rw [potentialFunction_apply, Finset.mul_sum, ofReal_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hccr := position_commutation_momentum_apply i ψ x
  have hξ := Q.ξ_sq_mul_ofReal i
  have hξ0 := Q.ξ_ofReal_ne_zero i
  have hℏ0 := ℏ_ofReal_ne_zero
  have hm0 : ((Q.m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Q.m_ne_zero
  have hω0 : ((Q.ω i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Q.ω_ne_zero i
  simp only [numberCLM_eq, loweringCLM_eq, raisingCLM_eq, comp_apply, map_add, map_smul, smul_apply,
    add_apply, sub_apply, smul_eq_mul, positionCLM_apply]
  push_cast
  field_simp
  linear_combination
    (2 * I * (ℏ : ℂ) * ((Q.m : ℝ) : ℂ) * ((Q.ω i : ℝ) : ℂ) * ((Q.ξ i : ℝ) : ℂ) ^ 2) * hccr
    - ((ℏ : ℂ) * ((Q.ξ i : ℝ) : ℂ) ^ 2 * (𝐩 i (𝐩 i ψ) x
        - (ℏ : ℂ) * ((Q.m : ℝ) : ℂ) * ((Q.ω i : ℝ) : ℂ) * ψ x
        + ((Q.m : ℝ) : ℂ) ^ 2 * ((Q.ω i : ℝ) : ℂ) ^ 2 * ψ x * ((x i : ℝ) : ℂ) ^ 2))
      * sqrt_two_sq_ofReal
    - (2 * (-(𝐩 i (𝐩 i ψ) x * ((Q.ξ i : ℝ) : ℂ) ^ 2)
        + (ℏ : ℂ) * ((Q.m : ℝ) : ℂ) * ((Q.ω i : ℝ) : ℂ) * ψ x * ((x i : ℝ) : ℂ) ^ 2)) * hξ
    + (2 * ((Q.ω i : ℝ) : ℂ) * (ℏ : ℂ) ^ 2 * ψ x * ((Q.ξ i : ℝ) : ℂ) ^ 2 * ((Q.m : ℝ) : ℂ)
        - 2 * ((Q.ω i : ℝ) : ℂ) * ((Q.ξ i : ℝ) : ℂ) ^ 4 * 𝐩 i (𝐩 i ψ) x * ((Q.m : ℝ) : ℂ)) * I_sq

/-- The kinetic operator on a Schwartz map, `(1/2m) ∑ᵢ pᵢ (pᵢ f)`. -/
lemma kineticOperator_apply_schwartz (f : 𝓢(Space d, ℂ))
    (h : (schwartzEquiv volume f : Q.HS) ∈ Q.kineticOperator.domain) :
    Q.kineticOperator ⟨schwartzEquiv volume f, h⟩
      = schwartzEquiv volume (((2 * Q.m)⁻¹ : ℝ) • ∑ i, 𝐩 i (𝐩 i f)) := by
  have h1 : Q.kineticOperator ⟨schwartzEquiv volume f, h⟩ =
      (2 * Q.m)⁻¹ • momentumSqOperator ⟨schwartzEquiv volume f, h⟩ :=
    LinearPMap.smul_apply _ _ _
  rw [h1]
  erw [LinearPMap.sum_apply]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul,
    map_sum, Submodule.coe_smul, Submodule.coe_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  have hr : ∀ x : (𝓟 a).domain, 𝓟 a x ∈ (𝓟 a).domain := momentumOperator_range a
  have key : ∀ H, ((𝓟 a).comp (𝓟 a) hr) ⟨(schwartzEquiv volume f : Q.HS), H⟩
      = schwartzEquiv volume (𝐩 a (𝐩 a f)) := fun H => by
    have H' : (schwartzEquiv volume f : Q.HS) ∈ (𝓟 a).domain := H
    have e3 : (⟨𝓟 a ⟨(schwartzEquiv volume f : Q.HS), H'⟩, hr _⟩ : (𝓟 a).domain)
        = ⟨(schwartzEquiv volume (𝐩 a f) : Q.HS), (schwartzEquiv volume (𝐩 a f)).2⟩ := by
      apply Subtype.ext
      show 𝓟 a (schwartzEquiv volume f) = (schwartzEquiv volume (𝐩 a f) : Q.HS)
      rw [momentumOperator_apply, LinearEquiv.symm_apply_apply]
    show 𝓟 a ⟨𝓟 a ⟨(schwartzEquiv volume f : Q.HS), H'⟩, hr _⟩ = _
    rw [e3]
    show 𝓟 a (schwartzEquiv volume (𝐩 a f)) = _
    rw [momentumOperator_apply, LinearEquiv.symm_apply_apply]
  exact key _

/-- The potential operator on a Schwartz map, almost everywhere `V f`. -/
lemma potentialOperator_apply_schwartz (f : 𝓢(Space d, ℂ))
    (h : (schwartzEquiv volume f : Q.HS) ∈ Q.potentialOperator.domain) :
    ⇑(Q.potentialOperator ⟨schwartzEquiv volume f, h⟩) =ᵐ[volume]
      fun x => (Q.potentialFunction x : ℂ) * f x := by
  have h1 : ⇑(Q.potentialOperator ⟨schwartzEquiv volume f, h⟩) =ᵐ[volume]
      (ofReal ∘ Q.potentialFunction) • ⇑(schwartzEquiv volume f : Q.HS) := mulOperator_apply_ae _
  filter_upwards [h1, schwartzEquiv_coe_ae (μ := volume) f] with x hx1 hx2
  rw [hx1]
  simp [hx2]

/-- As unbounded operators, `H_N` (with the Schwartz submodule as domain) is contained in the
  kinetic-plus-potential Hamiltonian. -/
lemma numberHamiltonian_le_hamiltonian : Q.numberHamiltonian ≤ Q.hamiltonian := by
  refine ⟨?_, ?_⟩
  · show SchwartzSubmodule d ≤ _
    rw [hamiltonain_eq, LinearPMap.add_domain, kineticOperator, LinearPMap.smul_domain,
      momentumSqOperator_domain_eq]
    exact le_inf le_rfl (mulOperator_domain_ge_of_hasTemperateGrowth
      Q.potentialFunction_hasTemperateGrowth volume)
  · intro ψ φ hψφ
    obtain ⟨f, hf⟩ := (schwartzEquiv volume).surjective ψ
    subst hf
    have hk := (φ.2 : (φ : Q.HS) ∈ Q.kineticOperator.domain ⊓ Q.potentialOperator.domain).1
    have hp := (φ.2 : (φ : Q.HS) ∈ Q.kineticOperator.domain ⊓ Q.potentialOperator.domain).2
    have hadd : Q.hamiltonian φ = Q.kineticOperator ⟨φ, hk⟩ + Q.potentialOperator ⟨φ, hp⟩ :=
      LinearPMap.add_apply _ _ φ
    have hk' : (⟨(φ : Q.HS), hk⟩ : Q.kineticOperator.domain) =
        ⟨schwartzEquiv volume f, hψφ ▸ hk⟩ :=
      Subtype.ext hψφ.symm
    have hp' : (⟨(φ : Q.HS), hp⟩ : Q.potentialOperator.domain) =
        ⟨schwartzEquiv volume f, hψφ ▸ hp⟩ :=
      Subtype.ext hψφ.symm
    have hN : Q.numberHamiltonian (schwartzEquiv volume f) =
        schwartzEquiv volume (Q.numberHamiltonianCLM f) := by
      rw [numberHamiltonian_apply, LinearEquiv.symm_apply_apply]
    apply MeasureTheory.Lp.ext
    rw [hadd, hk', hp', Q.kineticOperator_apply_schwartz, hN]
    have h1 := schwartzEquiv_coe_ae (μ := volume) (((2 * Q.m)⁻¹ : ℝ) • ∑ i, 𝐩 i (𝐩 i f))
    have h2 := schwartzEquiv_coe_ae (μ := volume) (Q.numberHamiltonianCLM f)
    have h3 := MeasureTheory.Lp.coeFn_add
      (schwartzEquiv volume (((2 * Q.m)⁻¹ : ℝ) • ∑ i, 𝐩 i (𝐩 i f)) : Q.HS)
      (Q.potentialOperator ⟨schwartzEquiv volume f, hψφ ▸ hp⟩)
    filter_upwards [h1, h2, h3, Q.potentialOperator_apply_schwartz f _] with x hx1 hx2 hx3 hx4
    rw [hx2, hx3, numberHamiltonianCLM_apply, Pi.add_apply, hx1, hx4]
    simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply, Complex.real_smul,
      Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]

/-- `⟪H_N f, g⟫ = ⟪f, H_N g⟫` for Schwartz maps `f`, `g`. -/
lemma numberHamiltonianCLM_inner (f g : 𝓢(Space d, ℂ)) :
    ⟪(schwartzEquiv volume (Q.numberHamiltonianCLM f) : Q.HS), schwartzEquiv volume g⟫_ℂ
      = ⟪(schwartzEquiv volume f : Q.HS), schwartzEquiv volume (Q.numberHamiltonianCLM g)⟫_ℂ := by
  simp only [numberHamiltonianCLM_eq, FunLike.coe_sum, Finset.sum_apply, smul_apply, add_apply,
    id_apply, map_sum, map_smul, map_add, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_add,
    sum_inner, inner_sum, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    Q.numberCLM_inner, Complex.conj_ofReal, map_inv₀, map_ofNat]

/-- The Hamiltonian `H_N` is symmetric. -/
lemma numberHamiltonian_isSymmetric : Q.numberHamiltonian.IsSymmetric := by
  intro ψ φ
  obtain ⟨f, rfl⟩ := (schwartzEquiv volume).surjective ψ
  obtain ⟨g, rfl⟩ := (schwartzEquiv volume).surjective φ
  simp only [numberHamiltonian_apply, LinearEquiv.symm_apply_apply]
  exact Q.numberHamiltonianCLM_inner f g

TODO "Prove that the two Hamiltonians define the same quantum system."

end QuantumMechanics.HarmonicOscillator

end
