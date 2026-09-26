/-
Copyright (c) 2026 Zhuoran Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhuoran Li
-/
module

public import Physlib.QuantumMechanics.Operators.AngularMomentum
public import Physlib.Mathematics.LeviCivita.Basic

/-!
# Three-dimensional angular momentum

## i. Overview

The Cartesian components use the right-handed convention
`Lx = L₁₂`, `Ly = L₂₀`, `Lz = L₀₁`, with coordinate indices `0, 1, 2`.
The Schwartz operators are the existing `angularMomentumOperator3D`; the Hilbert-space
operators have the common invariant domain `SchwartzSubmodule 3`.
Their commutation algebra and the raising/lowering operators are proved first on Schwartz maps
and then transported to this Hilbert-space domain. In particular, a zero commutator means zero
on that domain; it is not an equality with the everywhere-defined zero `LinearPMap`.

## ii. Key results

- `angularMomentumDimThreeOperator`: the Hilbert-space Cartesian components.
- `angularMomentumOperatorSqr_eq_sum_dimThree`: `L² = Lx² + Ly² + Lz²` on Schwartz maps.
- `angularMomentumDimThreeOperator_isSymmetric`: symmetry of each Cartesian component.
- `angularMomentumDimThree_commutation`: `[Li, Lj] = iℏ ∑k εijk Lk`.
- `angularMomentumRaisingCLM`, `angularMomentumLoweringCLM`: `Lx ± i Ly` on Schwartz maps.
- `angularMomentumRaisingOperator`, `angularMomentumLoweringOperator`: their Hilbert-space lifts.
- `angularMomentumZOperator_commutation_raising`, `angularMomentumZOperator_commutation_lowering`:
  `[Lz, L±] = ±ℏ L±` on the Schwartz domain.
- `angularMomentumSqOperator_commutation_raising`, `angularMomentumSqOperator_commutation_lowering`:
  `[L², L±] = 0` on that domain.

Open the `AngularMomentum` scope for `𝐋₃ i` on Schwartz maps and `𝓛₃ i` on the Hilbert space,
where `i : Fin 3` and indices `0`, `1`, `2` correspond to `x`, `y`, `z`.
The notation `𝓛²` denotes the Hilbert-space square.
The same scope provides `𝐋⁺`, `𝐋⁻` and `𝓛⁺`, `𝓛⁻` for the ladder operators.

## iii. Table of contents

- A. Cartesian components
  - A.1. Hilbert-space transport
  - A.2. Sum of the three squares
- B. Commutation algebra
- C. Ladder operators
  - C.1. Hilbert-space ladder operators
  - C.2. Hilbert-space commutation relations on the invariant domain

## iv. References

* None.
-/

@[expose] public section

namespace QuantumMechanics
noncomputable section

open Complex Constants SchwartzMap ContinuousLinearMap MeasureTheory
open SpaceDHilbertSpace SchwartzSubmodule
open scoped InnerProductSpace

/-!
## A. Cartesian components
-/

@[inherit_doc QuantumMechanics.angularMomentumOperator3D]
scoped[AngularMomentum] notation "𝐋₃" => QuantumMechanics.angularMomentumOperator3D

/-- The Cartesian Hilbert-space components, ordered as `x, y, z`. -/
def angularMomentumDimThreeOperator (i : Fin 3) :
    SpaceDHilbertSpace 3 →ₗ.[ℂ] SpaceDHilbertSpace 3 where
  domain := SchwartzSubmodule 3
  toFun := (schwartzIncl volume).1 ∘ₗ (angularMomentumOperator3D i).1 ∘ₗ
    (schwartzEquiv volume).symm.1

@[inherit_doc QuantumMechanics.angularMomentumDimThreeOperator]
scoped[AngularMomentum] notation "𝓛₃" => QuantumMechanics.angularMomentumDimThreeOperator

open scoped AngularMomentum

lemma angularMomentumDimThreeCLM_x : 𝐋₃ 0 = 𝐋 1 2 := rfl
lemma angularMomentumDimThreeCLM_y : 𝐋₃ 1 = 𝐋 2 0 := rfl
lemma angularMomentumDimThreeCLM_z : 𝐋₃ 2 = 𝐋 0 1 := rfl

lemma angularMomentumDimThreeOperator_x : 𝓛₃ 0 = angularMomentumOperator 1 2 := rfl
lemma angularMomentumDimThreeOperator_y : 𝓛₃ 1 = angularMomentumOperator 2 0 := rfl
lemma angularMomentumDimThreeOperator_z : 𝓛₃ 2 = angularMomentumOperator 0 1 := rfl

/-!
### A.1. Hilbert-space transport
-/

variable (i : Fin 3)

lemma angularMomentumDimThreeOperator_domain_eq :
    (𝓛₃ i).domain = SchwartzSubmodule 3 := rfl

lemma angularMomentumDimThreeOperator_apply (ψ : SchwartzSubmodule 3) :
    𝓛₃ i ψ = schwartzEquiv volume (𝐋₃ i ((schwartzEquiv volume).symm ψ)) := rfl

lemma angularMomentumDimThreeOperator_apply_ae (ψ : SchwartzSubmodule 3) :
    𝓛₃ i ψ =ᵐ[volume] 𝐋₃ i ((schwartzEquiv volume).symm ψ) := schwartzEquiv_coe_ae _

lemma angularMomentumDimThreeOperator_range (ψ : SchwartzSubmodule 3) :
    𝓛₃ i ψ ∈ SchwartzSubmodule 3 := by
  simp [angularMomentumDimThreeOperator_apply]

/-- Composing two components stays on the common Schwartz domain. -/
lemma angularMomentumDimThreeOperator_apply_apply (j : Fin 3) (ψ : SchwartzSubmodule 3) :
    𝓛₃ i ⟨𝓛₃ j ψ, angularMomentumDimThreeOperator_range j ψ⟩ =
      schwartzEquiv volume (𝐋₃ i (𝐋₃ j ((schwartzEquiv volume).symm ψ))) := by
  change schwartzIncl volume (𝐋₃ i ((schwartzEquiv volume).symm
    (schwartzEquiv volume (𝐋₃ j ((schwartzEquiv volume).symm ψ))))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

lemma angularMomentumDimThreeOperator_hasDenseDomain :
    (𝓛₃ i).HasDenseDomain := SchwartzSubmodule.dense 3 _

lemma angularMomentumDimThreeOperator_isSymmetric :
    (𝓛₃ i).IsSymmetric := by
  fin_cases i <;> exact angularMomentumOperator_isSymmetric _ _

lemma angularMomentumDimThreeOperator_isUnbounded :
    (𝓛₃ i).IsUnbounded :=
  (angularMomentumDimThreeOperator_isSymmetric i).isUnbounded_iff_hasDenseDomain.mpr
    (angularMomentumDimThreeOperator_hasDenseDomain i)

/-!
### A.2. Sum of the three squares
-/

/-- The antisymmetric-index definition agrees with the Cartesian sum of squares. -/
lemma angularMomentumOperatorSqr_eq_sum_dimThree :
    𝐋²[3] = ∑ i : Fin 3, 𝐋₃ i ∘L 𝐋₃ i := by
  simp only [angularMomentumOperatorSqr, Fin.sum_univ_three,
    angularMomentumDimThreeCLM_x, angularMomentumDimThreeCLM_y, angularMomentumDimThreeCLM_z,
    angularMomentumCLM_eq_zero, angularMomentumCLM_antisymm (0 : Fin 3) 2,
    angularMomentumCLM_antisymm (1 : Fin 3) 0, angularMomentumCLM_antisymm (2 : Fin 3) 1,
    comp_zero, neg_comp, comp_neg, neg_neg, add_zero, zero_add]
  module

/-- The same Cartesian sum of squares, evaluated on a Hilbert-space Schwartz vector. -/
lemma angularMomentumSqOperator_apply_eq_sum_dimThree (ψ : SchwartzSubmodule 3) :
    angularMomentumSqOperator ψ = ∑ i : Fin 3, 𝓛₃ i
      ⟨𝓛₃ i ψ, angularMomentumDimThreeOperator_range i ψ⟩ := by
  simp [angularMomentumSqOperator_apply, angularMomentumOperatorSqr_eq_sum_dimThree,
    angularMomentumDimThreeOperator_apply_apply]

/-!
## B. Commutation algebra

The bracket below is the existing commutator of continuous linear maps on Schwartz space.
Hilbert-space statements are evaluated on `SchwartzSubmodule 3`, with explicit membership
proofs for intermediate vectors. They make no claims about domains of closed extensions.
-/

open KroneckerDelta

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 100] LieAlgebra.ofAssociativeAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The Cartesian angular momentum algebra, with the right-handed Levi-Civita symbol. -/
lemma angularMomentumDimThree_commutation (j : Fin 3) :
    ⁅𝐋₃ i, 𝐋₃ j⁆ =
      (I * ℏ) • ∑ k : Fin 3, (leviCivitaSymbol ![i, j, k] : ℂ) • 𝐋₃ k := by
  simp only [leviCivitaSymbol_eq_det, Matrix.det_fin_three]
  fin_cases i <;> fin_cases j <;>
    norm_num [angularMomentumDimThreeCLM_x, angularMomentumDimThreeCLM_y,
      angularMomentumDimThreeCLM_z, angularMomentum_commutation_angularMomentum,
      kroneckerDelta, Fin.sum_univ_three, angularMomentumCLM_eq_zero,
      angularMomentumCLM_antisymm (0 : Fin 3) 2, angularMomentumCLM_antisymm (1 : Fin 3) 0,
      angularMomentumCLM_antisymm (2 : Fin 3) 1]

/-- `[Lx, Ly] = iℏ Lz`. -/
lemma angularMomentumDimThree_commutation_xy : ⁅𝐋₃ 0, 𝐋₃ 1⁆ = (I * ℏ) • 𝐋₃ 2 := by
  simpa [angularMomentumDimThreeCLM_x, angularMomentumDimThreeCLM_y,
    angularMomentumDimThreeCLM_z, kroneckerDelta,
    angularMomentumCLM_antisymm (1 : Fin 3) 0] using
    angularMomentum_commutation_angularMomentum (d := 3) 1 2 2 0

/-- `[Ly, Lz] = iℏ Lx`. -/
lemma angularMomentumDimThree_commutation_yz : ⁅𝐋₃ 1, 𝐋₃ 2⁆ = (I * ℏ) • 𝐋₃ 0 := by
  simpa [angularMomentumDimThreeCLM_x, angularMomentumDimThreeCLM_y,
    angularMomentumDimThreeCLM_z, kroneckerDelta,
    angularMomentumCLM_antisymm (2 : Fin 3) 1] using
    angularMomentum_commutation_angularMomentum (d := 3) 2 0 0 1

/-- `[Lz, Lx] = iℏ Ly`. -/
lemma angularMomentumDimThree_commutation_zx : ⁅𝐋₃ 2, 𝐋₃ 0⁆ = (I * ℏ) • 𝐋₃ 1 := by
  simpa [angularMomentumDimThreeCLM_x, angularMomentumDimThreeCLM_y,
    angularMomentumDimThreeCLM_z, kroneckerDelta,
    angularMomentumCLM_antisymm (0 : Fin 3) 2] using
    angularMomentum_commutation_angularMomentum (d := 3) 0 1 1 2

/-- Angular momentum squared commutes with every Cartesian component on Schwartz maps. -/
lemma angularMomentumSqr_commutation_dimThree : ⁅𝐋²[3], 𝐋₃ i⁆ = 0 := by
  fin_cases i <;> exact angularMomentumSqr_commutation_angularMomentum _ _

/-- The Cartesian commutation algebra on the common Hilbert-space Schwartz domain. -/
lemma angularMomentumDimThreeOperator_commutation (j : Fin 3) (ψ : SchwartzSubmodule 3) :
    𝓛₃ i ⟨𝓛₃ j ψ, angularMomentumDimThreeOperator_range j ψ⟩ -
      𝓛₃ j ⟨𝓛₃ i ψ, angularMomentumDimThreeOperator_range i ψ⟩ =
      (I * ℏ) • ∑ k : Fin 3, (leviCivitaSymbol ![i, j, k] : ℂ) • 𝓛₃ k ψ := by
  rw [angularMomentumDimThreeOperator_apply_apply, angularMomentumDimThreeOperator_apply_apply]
  have h := congrArg
    (fun A : 𝓢(Space 3, ℂ) →L[ℂ] 𝓢(Space 3, ℂ) =>
      schwartzIncl volume (A ((schwartzEquiv volume).symm ψ)))
    (angularMomentumDimThree_commutation i j)
  simpa only [Ring.lie_def, ContinuousLinearMap.mul_def, sub_apply, comp_apply, smul_apply,
    _root_.sum_apply, map_sub, map_smul, map_sum,
    angularMomentumDimThreeOperator_apply, schwartzEquiv_apply_coe] using h

/-- `[L², Li] = 0` on the common invariant Hilbert-space domain. -/
lemma angularMomentumSqOperator_commutation_dimThree (ψ : SchwartzSubmodule 3) :
    angularMomentumSqOperator
        ⟨𝓛₃ i ψ, angularMomentumDimThreeOperator_range i ψ⟩ -
      𝓛₃ i
        ⟨angularMomentumSqOperator ψ, angularMomentumSqOperator_range ψ⟩ = 0 := by
  change schwartzIncl volume (𝐋² ((schwartzEquiv volume).symm
      (schwartzEquiv volume (𝐋₃ i ((schwartzEquiv volume).symm ψ))))) -
    schwartzIncl volume (𝐋₃ i ((schwartzEquiv volume).symm
      (schwartzEquiv volume (𝐋² ((schwartzEquiv volume).symm ψ))))) = 0
  simp only [LinearEquiv.symm_apply_apply]
  have h := congrArg
    (fun A : 𝓢(Space 3, ℂ) →L[ℂ] 𝓢(Space 3, ℂ) =>
      schwartzIncl volume (A ((schwartzEquiv volume).symm ψ)))
    (angularMomentumSqr_commutation_dimThree i)
  simpa only [Ring.lie_def, ContinuousLinearMap.mul_def, sub_apply, comp_apply, zero_apply,
    map_sub, map_zero] using h

/-!
## C. Ladder operators

These operators act on arbitrary Schwartz vectors. No eigenstate or spectral assumptions
are used in their commutation relations.
-/

/-- The angular momentum raising operator `L₊ = Lx + i Ly` on Schwartz maps. -/
def angularMomentumRaisingCLM : 𝓢(Space 3, ℂ) →L[ℂ] 𝓢(Space 3, ℂ) := 𝐋₃ 0 + I • 𝐋₃ 1

/-- The angular momentum lowering operator `L₋ = Lx - i Ly` on Schwartz maps. -/
def angularMomentumLoweringCLM : 𝓢(Space 3, ℂ) →L[ℂ] 𝓢(Space 3, ℂ) := 𝐋₃ 0 - I • 𝐋₃ 1

@[inherit_doc QuantumMechanics.angularMomentumRaisingCLM]
scoped[AngularMomentum] notation "𝐋⁺" => QuantumMechanics.angularMomentumRaisingCLM
@[inherit_doc QuantumMechanics.angularMomentumLoweringCLM]
scoped[AngularMomentum] notation "𝐋⁻" => QuantumMechanics.angularMomentumLoweringCLM

/-- `[Lz, L₊] = ℏ L₊`. -/
lemma angularMomentumZ_commutation_raising : ⁅𝐋₃ 2, 𝐋⁺⁆ = (ℏ : ℂ) • 𝐋⁺ := by
  rw [angularMomentumRaisingCLM, lie_add, lie_smul, angularMomentumDimThree_commutation_zx,
    ← lie_skew (𝐋₃ 2) (𝐋₃ 1), angularMomentumDimThree_commutation_yz]
  simp only [smul_neg, smul_smul, ← mul_assoc, I_mul_I, neg_one_mul]
  module

/-- `[Lz, L₋] = -ℏ L₋`. -/
lemma angularMomentumZ_commutation_lowering : ⁅𝐋₃ 2, 𝐋⁻⁆ = -(ℏ : ℂ) • 𝐋⁻ := by
  rw [angularMomentumLoweringCLM, lie_sub, lie_smul, angularMomentumDimThree_commutation_zx,
    ← lie_skew (𝐋₃ 2) (𝐋₃ 1), angularMomentumDimThree_commutation_yz]
  simp only [smul_neg, smul_smul, ← mul_assoc, I_mul_I, neg_one_mul]
  module

/-- Angular momentum squared commutes with the raising operator. -/
lemma angularMomentumSqr_commutation_raising : ⁅𝐋²[3], 𝐋⁺⁆ = 0 := by
  simp [angularMomentumRaisingCLM, lie_add, lie_smul, angularMomentumSqr_commutation_dimThree]

/-- Angular momentum squared commutes with the lowering operator. -/
lemma angularMomentumSqr_commutation_lowering : ⁅𝐋²[3], 𝐋⁻⁆ = 0 := by
  simp [angularMomentumLoweringCLM, lie_sub, lie_smul, angularMomentumSqr_commutation_dimThree]

/-!
### C.1. Hilbert-space ladder operators
-/

/-- The raising operator on the Hilbert space, with Schwartz domain. -/
def angularMomentumRaisingOperator : SpaceDHilbertSpace 3 →ₗ.[ℂ] SpaceDHilbertSpace 3 where
  domain := SchwartzSubmodule 3
  toFun := (schwartzIncl volume).1 ∘ₗ (𝐋⁺).1 ∘ₗ (schwartzEquiv volume).symm.1

/-- The lowering operator on the Hilbert space, with Schwartz domain. -/
def angularMomentumLoweringOperator : SpaceDHilbertSpace 3 →ₗ.[ℂ] SpaceDHilbertSpace 3 where
  domain := SchwartzSubmodule 3
  toFun := (schwartzIncl volume).1 ∘ₗ (𝐋⁻).1 ∘ₗ (schwartzEquiv volume).symm.1

@[inherit_doc QuantumMechanics.angularMomentumRaisingOperator]
scoped[AngularMomentum] notation "𝓛⁺" => QuantumMechanics.angularMomentumRaisingOperator
@[inherit_doc QuantumMechanics.angularMomentumLoweringOperator]
scoped[AngularMomentum] notation "𝓛⁻" => QuantumMechanics.angularMomentumLoweringOperator

lemma angularMomentumRaisingOperator_domain_eq : (𝓛⁺).domain = SchwartzSubmodule 3 := rfl
lemma angularMomentumLoweringOperator_domain_eq : (𝓛⁻).domain = SchwartzSubmodule 3 := rfl

lemma angularMomentumRaisingOperator_apply (ψ : SchwartzSubmodule 3) :
    𝓛⁺ ψ = schwartzEquiv volume (𝐋⁺ ((schwartzEquiv volume).symm ψ)) := rfl

lemma angularMomentumLoweringOperator_apply (ψ : SchwartzSubmodule 3) :
    𝓛⁻ ψ = schwartzEquiv volume (𝐋⁻ ((schwartzEquiv volume).symm ψ)) := rfl

lemma angularMomentumRaisingOperator_apply_eq (ψ : SchwartzSubmodule 3) :
    𝓛⁺ ψ = 𝓛₃ 0 ψ + I • 𝓛₃ 1 ψ := by
  simp [angularMomentumRaisingOperator_apply, angularMomentumRaisingCLM,
    angularMomentumDimThreeOperator_apply]

lemma angularMomentumLoweringOperator_apply_eq (ψ : SchwartzSubmodule 3) :
    𝓛⁻ ψ = 𝓛₃ 0 ψ - I • 𝓛₃ 1 ψ := by
  simp [angularMomentumLoweringOperator_apply, angularMomentumLoweringCLM,
    angularMomentumDimThreeOperator_apply]

lemma angularMomentumRaisingOperator_apply_ae (ψ : SchwartzSubmodule 3) :
    𝓛⁺ ψ =ᵐ[volume] 𝐋⁺ ((schwartzEquiv volume).symm ψ) := schwartzEquiv_coe_ae _

lemma angularMomentumLoweringOperator_apply_ae (ψ : SchwartzSubmodule 3) :
    𝓛⁻ ψ =ᵐ[volume] 𝐋⁻ ((schwartzEquiv volume).symm ψ) := schwartzEquiv_coe_ae _

lemma angularMomentumRaisingOperator_range (ψ : SchwartzSubmodule 3) :
    𝓛⁺ ψ ∈ SchwartzSubmodule 3 := by
  simp [angularMomentumRaisingOperator_apply]

lemma angularMomentumLoweringOperator_range (ψ : SchwartzSubmodule 3) :
    𝓛⁻ ψ ∈ SchwartzSubmodule 3 := by
  simp [angularMomentumLoweringOperator_apply]

lemma angularMomentumRaisingOperator_hasDenseDomain : (𝓛⁺).HasDenseDomain :=
  SchwartzSubmodule.dense 3 _

lemma angularMomentumLoweringOperator_hasDenseDomain : (𝓛⁻).HasDenseDomain :=
  SchwartzSubmodule.dense 3 _

/-!
### C.2. Hilbert-space commutation relations on the invariant domain
-/

/-- `[Lz, L₊] ψ = ℏ L₊ ψ` for every Schwartz vector in the Hilbert space. -/
lemma angularMomentumZOperator_commutation_raising (ψ : SchwartzSubmodule 3) :
    𝓛₃ 2 ⟨𝓛⁺ ψ, angularMomentumRaisingOperator_range ψ⟩ -
      𝓛⁺ ⟨𝓛₃ 2 ψ, angularMomentumDimThreeOperator_range 2 ψ⟩ = (ℏ : ℂ) • 𝓛⁺ ψ := by
  change schwartzIncl volume (𝐋₃ 2 ((schwartzEquiv volume).symm
      (schwartzEquiv volume (𝐋⁺ ((schwartzEquiv volume).symm ψ))))) -
    schwartzIncl volume (𝐋⁺ ((schwartzEquiv volume).symm
      (schwartzEquiv volume (𝐋₃ 2 ((schwartzEquiv volume).symm ψ))))) =
    (ℏ : ℂ) • schwartzIncl volume (𝐋⁺ ((schwartzEquiv volume).symm ψ))
  simp only [LinearEquiv.symm_apply_apply]
  have h := congrArg
    (fun A : 𝓢(Space 3, ℂ) →L[ℂ] 𝓢(Space 3, ℂ) =>
      schwartzIncl volume (A ((schwartzEquiv volume).symm ψ)))
    angularMomentumZ_commutation_raising
  simpa only [Ring.lie_def, ContinuousLinearMap.mul_def, sub_apply, comp_apply, smul_apply,
    map_sub, map_smul] using h

/-- `[Lz, L₋] ψ = -ℏ L₋ ψ` for every Schwartz vector in the Hilbert space. -/
lemma angularMomentumZOperator_commutation_lowering (ψ : SchwartzSubmodule 3) :
    𝓛₃ 2 ⟨𝓛⁻ ψ, angularMomentumLoweringOperator_range ψ⟩ -
      𝓛⁻ ⟨𝓛₃ 2 ψ, angularMomentumDimThreeOperator_range 2 ψ⟩ = -(ℏ : ℂ) • 𝓛⁻ ψ := by
  change schwartzIncl volume (𝐋₃ 2 ((schwartzEquiv volume).symm
      (schwartzEquiv volume (𝐋⁻ ((schwartzEquiv volume).symm ψ))))) -
    schwartzIncl volume (𝐋⁻ ((schwartzEquiv volume).symm
      (schwartzEquiv volume (𝐋₃ 2 ((schwartzEquiv volume).symm ψ))))) =
    -(ℏ : ℂ) • schwartzIncl volume (𝐋⁻ ((schwartzEquiv volume).symm ψ))
  simp only [LinearEquiv.symm_apply_apply]
  have h := congrArg
    (fun A : 𝓢(Space 3, ℂ) →L[ℂ] 𝓢(Space 3, ℂ) =>
      schwartzIncl volume (A ((schwartzEquiv volume).symm ψ)))
    angularMomentumZ_commutation_lowering
  simpa only [Ring.lie_def, ContinuousLinearMap.mul_def, sub_apply, comp_apply, smul_apply,
    map_sub, map_smul] using h

/-- `[L², L₊] ψ = 0` on the common invariant Schwartz domain. -/
lemma angularMomentumSqOperator_commutation_raising (ψ : SchwartzSubmodule 3) :
    𝓛² ⟨𝓛⁺ ψ, angularMomentumRaisingOperator_range ψ⟩ -
      𝓛⁺ ⟨𝓛² ψ, angularMomentumSqOperator_range ψ⟩ = 0 := by
  change schwartzIncl volume (𝐋² ((schwartzEquiv volume).symm
      (schwartzEquiv volume (𝐋⁺ ((schwartzEquiv volume).symm ψ))))) -
    schwartzIncl volume (𝐋⁺ ((schwartzEquiv volume).symm
      (schwartzEquiv volume (𝐋² ((schwartzEquiv volume).symm ψ))))) = 0
  simp only [LinearEquiv.symm_apply_apply]
  have h := congrArg
    (fun A : 𝓢(Space 3, ℂ) →L[ℂ] 𝓢(Space 3, ℂ) =>
      schwartzIncl volume (A ((schwartzEquiv volume).symm ψ)))
    angularMomentumSqr_commutation_raising
  simpa only [Ring.lie_def, ContinuousLinearMap.mul_def, sub_apply, comp_apply, zero_apply,
    map_sub, map_zero] using h

/-- `[L², L₋] ψ = 0` on the common invariant Schwartz domain. -/
lemma angularMomentumSqOperator_commutation_lowering (ψ : SchwartzSubmodule 3) :
    𝓛² ⟨𝓛⁻ ψ, angularMomentumLoweringOperator_range ψ⟩ -
      𝓛⁻ ⟨𝓛² ψ, angularMomentumSqOperator_range ψ⟩ = 0 := by
  change schwartzIncl volume (𝐋² ((schwartzEquiv volume).symm
      (schwartzEquiv volume (𝐋⁻ ((schwartzEquiv volume).symm ψ))))) -
    schwartzIncl volume (𝐋⁻ ((schwartzEquiv volume).symm
      (schwartzEquiv volume (𝐋² ((schwartzEquiv volume).symm ψ))))) = 0
  simp only [LinearEquiv.symm_apply_apply]
  have h := congrArg
    (fun A : 𝓢(Space 3, ℂ) →L[ℂ] 𝓢(Space 3, ℂ) =>
      schwartzIncl volume (A ((schwartzEquiv volume).symm ψ)))
    angularMomentumSqr_commutation_lowering
  simpa only [Ring.lie_def, ContinuousLinearMap.mul_def, sub_apply, comp_apply, zero_apply,
    map_sub, map_zero] using h

end
end QuantumMechanics
