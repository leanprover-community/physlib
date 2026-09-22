/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import Physlib.QuantumMechanics.HarmonicOscillator.LadderOperators
/-!

# Number operators

## i. Overview

The number operators `Nᵢ = aᵢ† aᵢ` of the `d`-dimensional quantum harmonic oscillator, built from
the ladder operators of `LadderOperators.lean` and acting on Schwartz maps: their commutation
relations with the ladder operators and with each other, and the Hamiltonian of `Basic.lean`, which
on Schwartz maps acts as `H_N = ∑ᵢ ℏ ωᵢ (Nᵢ + ½)`, commutes with the number operators and lowers
and raises energies by `ℏ ωᵢ`. The number operators are then lifted to unbounded operators on the
Hilbert space with the Schwartz submodule as domain (like `momentumOperator`), where they are
symmetric, as is the Hamiltonian.

## ii. Key results

- `number_commutation_number`: `[Nᵢ, Nⱼ] = 0`; `number_commutation_lowering`,
  `number_commutation_raising`: `[Nᵢ, aⱼ] = -δᵢⱼ aⱼ`, `[Nᵢ, aⱼ†] = δᵢⱼ aⱼ†`.
- `lowering_comp_raising`: `aᵢ aᵢ† = Nᵢ + 𝟙`; `numberCLM_inner`:
  `⟪ Nᵢ f, g⟫ = ⟪ f, Nᵢ g⟫` for Schwartz maps.
- `sum_number_commutation_lowering`, `sum_number_commutation_raising`,
  `sum_number_commutation_number`: with `H_N = ∑ⱼ ℏ ωⱼ (Nⱼ + ½)`, `[H_N, aᵢ] = -ℏ ωᵢ aᵢ`,
  `[H_N, aᵢ†] = ℏ ωᵢ aᵢ†`, `[H_N, Nᵢ] = 0`.
- `sum_number_apply`: `H_N ψ = (1/2m) ∑ᵢ pᵢ (pᵢ ψ) + V ψ` on Schwartz maps;
  `hamiltonian_apply_schwartz`: the Hamiltonian of `Basic.lean` acts on Schwartz maps as `H_N`;
  `hamiltonian_inner_schwartz`: it is symmetric on the Schwartz submodule.
- `numberOperator_isSymmetric`: the number operators are symmetric.

## iii. Table of contents

- A. Number operators
  - A.1. Definition
  - A.2. Commutation relations
  - A.3. Inner products
- B. Hamiltonian
  - B.1. Commutation relations with the ladder and number operators
  - B.2. The Hamiltonian on Schwartz maps
- C. The number operators as unbounded operators
- D. Symmetry

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

## A. Number operators

-/

/-!

### A.1. Definition

-/

/-- The number operator `Nᵢ = aᵢ† aᵢ`. -/
def numberCLM : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) := Q.raisingCLM i ∘L Q.loweringCLM i

lemma numberCLM_eq : Q.numberCLM i = Q.raisingCLM i ∘L Q.loweringCLM i := rfl

/-!

### A.2. Commutation relations

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

### A.3. Inner products

-/

/-- `⟪Nᵢ f, g⟫ = ⟪f, Nᵢ g⟫` for Schwartz maps `f`, `g`. -/
lemma numberCLM_inner (f g : 𝓢(Space d, ℂ)) :
    ⟪(schwartzEquiv volume (Q.numberCLM i f) : Q.HS), schwartzEquiv volume g⟫_ℂ
      = ⟪(schwartzEquiv volume f : Q.HS), schwartzEquiv volume (Q.numberCLM i g)⟫_ℂ := by
  rw [numberCLM_eq, comp_apply, Q.raisingCLM_inner i, Q.loweringCLM_inner i, comp_apply]

/-!

## B. Hamiltonian

On Schwartz maps the Hamiltonian of `Basic.lean` acts as `H_N = ∑ⱼ ℏ ωⱼ (Nⱼ + ½)`
(`hamiltonian_apply_schwartz`); the lemmas below are stated for this sum.

-/

/-!

### B.1. Commutation relations with the ladder and number operators

-/

/-- `[∑ⱼ ℏ ωⱼ (Nⱼ + ½), aᵢ] = -ℏ ωᵢ aᵢ`. -/
lemma sum_number_commutation_lowering :
    ⁅∑ j, ((ℏ * Q.ω j : ℝ) : ℂ) •
        (Q.numberCLM j + (2⁻¹ : ℂ) • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ)),
      Q.loweringCLM i⁆ = -(((ℏ * Q.ω i : ℝ) : ℂ) • Q.loweringCLM i) := by
  simp only [sum_lie, smul_lie, add_lie, number_commutation_lowering, id_commutation, smul_zero,
    add_zero, smul_neg]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [eq_zero_of_ne hb]) (by simp)]
  simp [eq_one_of_same]

/-- `[∑ⱼ ℏ ωⱼ (Nⱼ + ½), aᵢ†] = ℏ ωᵢ aᵢ†`. -/
lemma sum_number_commutation_raising :
    ⁅∑ j, ((ℏ * Q.ω j : ℝ) : ℂ) •
        (Q.numberCLM j + (2⁻¹ : ℂ) • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ)),
      Q.raisingCLM i⁆ = ((ℏ * Q.ω i : ℝ) : ℂ) • Q.raisingCLM i := by
  simp only [sum_lie, smul_lie, add_lie, number_commutation_raising, id_commutation, smul_zero,
    add_zero]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [eq_zero_of_ne hb]) (by simp)]
  simp [eq_one_of_same]

/-- `[∑ⱼ ℏ ωⱼ (Nⱼ + ½), Nᵢ] = 0`. -/
lemma sum_number_commutation_number :
    ⁅∑ j, ((ℏ * Q.ω j : ℝ) : ℂ) •
        (Q.numberCLM j + (2⁻¹ : ℂ) • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ)),
      Q.numberCLM i⁆ = 0 := by
  simp [sum_lie, smul_lie, add_lie, number_commutation_number, id_commutation]

/-!

### B.2. The Hamiltonian on Schwartz maps

-/

/-- On Schwartz maps, `∑ᵢ ℏ ωᵢ (Nᵢ + ½) ψ = (1/2m) ∑ᵢ pᵢ (pᵢ ψ) + V ψ`. -/
lemma sum_number_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    (∑ j, ((ℏ * Q.ω j : ℝ) : ℂ) •
      (Q.numberCLM j + (2⁻¹ : ℂ) • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ))) ψ x =
      ((2 * Q.m : ℝ) : ℂ)⁻¹ * ∑ i, 𝐩 i (𝐩 i ψ) x + (Q.potentialFunction x : ℂ) * ψ x := by
  simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply, add_apply, id_apply, smul_eq_mul]
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

/-- The Schwartz submodule is contained in the domain of the Hamiltonian. -/
lemma schwartzSubmodule_le_hamiltonian_domain : SchwartzSubmodule d ≤ Q.hamiltonian.domain := by
  rw [hamiltonain_eq, LinearPMap.add_domain, kineticOperator, LinearPMap.smul_domain,
    momentumSqOperator_domain_eq]
  exact le_inf le_rfl (mulOperator_domain_ge_of_hasTemperateGrowth
    Q.potentialFunction_hasTemperateGrowth volume)

/-- On a Schwartz map, the Hamiltonian `kineticOperator + potentialOperator` of `Basic.lean` acts as
  `∑ᵢ ℏ ωᵢ (Nᵢ + ½)`. -/
lemma hamiltonian_apply_schwartz (f : 𝓢(Space d, ℂ))
    (h : (schwartzEquiv volume f : Q.HS) ∈ Q.hamiltonian.domain) :
    Q.hamiltonian ⟨schwartzEquiv volume f, h⟩ = schwartzEquiv volume
      ((∑ j, ((ℏ * Q.ω j : ℝ) : ℂ) •
        (Q.numberCLM j + (2⁻¹ : ℂ) • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ))) f) := by
  have hk := (h : (schwartzEquiv volume f : Q.HS) ∈
    Q.kineticOperator.domain ⊓ Q.potentialOperator.domain).1
  have hp := (h : (schwartzEquiv volume f : Q.HS) ∈
    Q.kineticOperator.domain ⊓ Q.potentialOperator.domain).2
  have hadd : Q.hamiltonian ⟨schwartzEquiv volume f, h⟩ =
      Q.kineticOperator ⟨schwartzEquiv volume f, hk⟩ +
        Q.potentialOperator ⟨schwartzEquiv volume f, hp⟩ :=
    LinearPMap.add_apply _ _ _
  apply MeasureTheory.Lp.ext
  rw [hadd, Q.kineticOperator_apply_schwartz]
  have h1 := schwartzEquiv_coe_ae (μ := volume) (((2 * Q.m)⁻¹ : ℝ) • ∑ i, 𝐩 i (𝐩 i f))
  have h2 := schwartzEquiv_coe_ae (μ := volume)
    ((∑ j, ((ℏ * Q.ω j : ℝ) : ℂ) •
      (Q.numberCLM j + (2⁻¹ : ℂ) • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ))) f)
  have h3 := MeasureTheory.Lp.coeFn_add
    (schwartzEquiv volume (((2 * Q.m)⁻¹ : ℝ) • ∑ i, 𝐩 i (𝐩 i f)) : Q.HS)
    (Q.potentialOperator ⟨schwartzEquiv volume f, hp⟩)
  filter_upwards [h1, h2, h3, Q.potentialOperator_apply_schwartz f hp] with x hx1 hx2 hx3 hx4
  rw [hx2, hx3, sum_number_apply, Pi.add_apply, hx1, hx4]
  simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]

/-- `⟪H f, g⟫ = ⟪f, H g⟫` for Schwartz maps `f`, `g`: the Hamiltonian is symmetric on the Schwartz
  submodule. -/
lemma hamiltonian_inner_schwartz (f g : 𝓢(Space d, ℂ))
    (hf : (schwartzEquiv volume f : Q.HS) ∈ Q.hamiltonian.domain)
    (hg : (schwartzEquiv volume g : Q.HS) ∈ Q.hamiltonian.domain) :
    ⟪Q.hamiltonian ⟨schwartzEquiv volume f, hf⟩, (schwartzEquiv volume g : Q.HS)⟫_ℂ
      = ⟪(schwartzEquiv volume f : Q.HS), Q.hamiltonian ⟨schwartzEquiv volume g, hg⟩⟫_ℂ := by
  rw [hamiltonian_apply_schwartz, hamiltonian_apply_schwartz]
  simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply, add_apply, id_apply, map_sum, map_smul,
    map_add, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_add, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, inner_add_left, inner_add_right, Q.numberCLM_inner,
    Complex.conj_ofReal, map_inv₀, map_ofNat]

/-!

## C. The number operators as unbounded operators

-/

/-- The number operator as an unbounded operator with domain the Schwartz submodule. -/
def numberOperator : Q.HS →ₗ.[ℂ] Q.HS where
  domain := SchwartzSubmodule d
  toFun := (schwartzIncl volume).1 ∘ₗ (Q.numberCLM i).1 ∘ₗ (schwartzEquiv volume).symm.1

lemma numberOperator_apply (ψ : SchwartzSubmodule d) :
    Q.numberOperator i ψ =
      schwartzEquiv volume (Q.numberCLM i ((schwartzEquiv volume).symm ψ)) :=
  rfl

/-!

## D. Symmetry

-/

/-- The number operator is symmetric. -/
lemma numberOperator_isSymmetric : (Q.numberOperator i).IsSymmetric := by
  intro ψ φ
  obtain ⟨f, rfl⟩ := (schwartzEquiv volume).surjective ψ
  obtain ⟨g, rfl⟩ := (schwartzEquiv volume).surjective φ
  simp only [numberOperator_apply, LinearEquiv.symm_apply_apply]
  exact Q.numberCLM_inner i f g

TODO "Prove that the number operators are essentially self-adjoint."

end QuantumMechanics.HarmonicOscillator

end
