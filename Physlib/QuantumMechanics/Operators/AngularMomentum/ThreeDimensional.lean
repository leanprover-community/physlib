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

- `angularMomentum3DOperator`: the Hilbert-space Cartesian components.
- `angularMomentumOperatorSqr_eq_sum_3D`: `L² = Lx² + Ly² + Lz²` on Schwartz maps.
- `angularMomentum3DOperator_isSymmetric`: symmetry of each Cartesian component.
- `angularMomentum3D_commutation`: `[Li, Lj] = iℏ ∑k εijk Lk`.
- `angularMomentumRaisingCLM`, `angularMomentumLoweringCLM`: `Lx ± i Ly` on Schwartz maps.
- `angularMomentumRaisingOperator`, `angularMomentumLoweringOperator`: their Hilbert-space lifts.
- `angularMomentumZOperator_commutation_raising`, `angularMomentumZOperator_commutation_lowering`:
  `[Lz, L±] = ±ℏ L±` on the Schwartz domain.
- `angularMomentumSqOperator_commutation_raising`, `angularMomentumSqOperator_commutation_lowering`:
  `[L², L±] = 0` on that domain.

Open the `AngularMomentum` scope for `𝐋x`, `𝐋y`, `𝐋z` on Schwartz maps and
`𝓛x`, `𝓛y`, `𝓛z`, `𝓛²` on the Hilbert space.
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
scoped[AngularMomentum] notation "𝐋x" => QuantumMechanics.angularMomentumOperator3D 0
@[inherit_doc QuantumMechanics.angularMomentumOperator3D]
scoped[AngularMomentum] notation "𝐋y" => QuantumMechanics.angularMomentumOperator3D 1
@[inherit_doc QuantumMechanics.angularMomentumOperator3D]
scoped[AngularMomentum] notation "𝐋z" => QuantumMechanics.angularMomentumOperator3D 2

/-- The Cartesian Hilbert-space components, ordered as `x, y, z`. -/
def angularMomentum3DOperator (i : Fin 3) :
    SpaceDHilbertSpace 3 →ₗ.[ℂ] SpaceDHilbertSpace 3 where
  domain := SchwartzSubmodule 3
  toFun := (schwartzIncl volume).1 ∘ₗ (angularMomentumOperator3D i).1 ∘ₗ
    (schwartzEquiv volume).symm.1

@[inherit_doc QuantumMechanics.angularMomentum3DOperator]
scoped[AngularMomentum] notation "𝓛x" => QuantumMechanics.angularMomentum3DOperator 0
@[inherit_doc QuantumMechanics.angularMomentum3DOperator]
scoped[AngularMomentum] notation "𝓛y" => QuantumMechanics.angularMomentum3DOperator 1
@[inherit_doc QuantumMechanics.angularMomentum3DOperator]
scoped[AngularMomentum] notation "𝓛z" => QuantumMechanics.angularMomentum3DOperator 2

open scoped AngularMomentum

lemma angularMomentumOperator3D_x : 𝐋x = 𝐋 1 2 := rfl
lemma angularMomentumOperator3D_y : 𝐋y = 𝐋 2 0 := rfl
lemma angularMomentumOperator3D_z : 𝐋z = 𝐋 0 1 := rfl

lemma angularMomentum3DOperator_x : 𝓛x = angularMomentumOperator 1 2 := rfl
lemma angularMomentum3DOperator_y : 𝓛y = angularMomentumOperator 2 0 := rfl
lemma angularMomentum3DOperator_z : 𝓛z = angularMomentumOperator 0 1 := rfl

/-!
### A.1. Hilbert-space transport
-/

variable (i : Fin 3)

lemma angularMomentum3DOperator_domain_eq :
    (angularMomentum3DOperator i).domain = SchwartzSubmodule 3 := rfl

lemma angularMomentum3DOperator_apply (ψ : SchwartzSubmodule 3) :
    angularMomentum3DOperator i ψ =
      schwartzEquiv volume (angularMomentumOperator3D i ((schwartzEquiv volume).symm ψ)) := rfl

lemma angularMomentum3DOperator_apply_ae (ψ : SchwartzSubmodule 3) :
    angularMomentum3DOperator i ψ =ᵐ[volume]
      angularMomentumOperator3D i ((schwartzEquiv volume).symm ψ) := schwartzEquiv_coe_ae _

lemma angularMomentum3DOperator_range (ψ : SchwartzSubmodule 3) :
    angularMomentum3DOperator i ψ ∈ SchwartzSubmodule 3 := by
  simp [angularMomentum3DOperator_apply]

/-- Composing two components stays on the common Schwartz domain. -/
lemma angularMomentum3DOperator_apply_apply (j : Fin 3) (ψ : SchwartzSubmodule 3) :
    angularMomentum3DOperator i
        ⟨angularMomentum3DOperator j ψ, angularMomentum3DOperator_range j ψ⟩ =
      schwartzEquiv volume (angularMomentumOperator3D i
        (angularMomentumOperator3D j ((schwartzEquiv volume).symm ψ))) := by
  change schwartzIncl volume (angularMomentumOperator3D i ((schwartzEquiv volume).symm
    (schwartzEquiv volume (angularMomentumOperator3D j ((schwartzEquiv volume).symm ψ))))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

lemma angularMomentum3DOperator_hasDenseDomain :
    (angularMomentum3DOperator i).HasDenseDomain := SchwartzSubmodule.dense 3 _

lemma angularMomentum3DOperator_isSymmetric :
    (angularMomentum3DOperator i).IsSymmetric := by
  fin_cases i <;> exact angularMomentumOperator_isSymmetric _ _

lemma angularMomentum3DOperator_isUnbounded :
    (angularMomentum3DOperator i).IsUnbounded :=
  (angularMomentum3DOperator_isSymmetric i).isUnbounded_iff_hasDenseDomain.mpr
    (angularMomentum3DOperator_hasDenseDomain i)

/-!
### A.2. Sum of the three squares
-/

/-- The antisymmetric-index definition agrees with the Cartesian sum of squares. -/
lemma angularMomentumOperatorSqr_eq_sum_3D :
    𝐋²[3] = ∑ i : Fin 3, angularMomentumOperator3D i ∘L angularMomentumOperator3D i := by
  simp only [angularMomentumOperatorSqr, Fin.sum_univ_three, angularMomentumOperator3D,
    angularMomentumCLM_eq_zero, angularMomentumCLM_antisymm (0 : Fin 3) 2,
    angularMomentumCLM_antisymm (1 : Fin 3) 0, angularMomentumCLM_antisymm (2 : Fin 3) 1,
    comp_zero, neg_comp, comp_neg, neg_neg, add_zero, zero_add]
  module

/-- The same Cartesian sum of squares, evaluated on a Hilbert-space Schwartz vector. -/
lemma angularMomentumSqOperator_apply_eq_sum_3D (ψ : SchwartzSubmodule 3) :
    angularMomentumSqOperator ψ = ∑ i : Fin 3, angularMomentum3DOperator i
      ⟨angularMomentum3DOperator i ψ, angularMomentum3DOperator_range i ψ⟩ := by
  simp [angularMomentumSqOperator_apply, angularMomentumOperatorSqr_eq_sum_3D,
    angularMomentum3DOperator_apply_apply]

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
lemma angularMomentum3D_commutation (j : Fin 3) :
    ⁅angularMomentumOperator3D i, angularMomentumOperator3D j⁆ =
      (I * ℏ) • ∑ k : Fin 3, (leviCivitaSymbol ![i, j, k] : ℂ) •
        angularMomentumOperator3D k := by
  simp only [leviCivitaSymbol_eq_det, Matrix.det_fin_three]
  fin_cases i <;> fin_cases j <;>
    norm_num [angularMomentumOperator3D, angularMomentum_commutation_angularMomentum,
      kroneckerDelta, Fin.sum_univ_three, angularMomentumCLM_eq_zero,
      angularMomentumCLM_antisymm (0 : Fin 3) 2, angularMomentumCLM_antisymm (1 : Fin 3) 0,
      angularMomentumCLM_antisymm (2 : Fin 3) 1]

/-- `[Lx, Ly] = iℏ Lz`. -/
lemma angularMomentum3D_commutation_xy : ⁅𝐋x, 𝐋y⁆ = (I * ℏ) • 𝐋z := by
  simpa [angularMomentumOperator3D, kroneckerDelta,
    angularMomentumCLM_antisymm (1 : Fin 3) 0] using
    angularMomentum_commutation_angularMomentum (d := 3) 1 2 2 0

/-- `[Ly, Lz] = iℏ Lx`. -/
lemma angularMomentum3D_commutation_yz : ⁅𝐋y, 𝐋z⁆ = (I * ℏ) • 𝐋x := by
  simpa [angularMomentumOperator3D, kroneckerDelta,
    angularMomentumCLM_antisymm (2 : Fin 3) 1] using
    angularMomentum_commutation_angularMomentum (d := 3) 2 0 0 1

/-- `[Lz, Lx] = iℏ Ly`. -/
lemma angularMomentum3D_commutation_zx : ⁅𝐋z, 𝐋x⁆ = (I * ℏ) • 𝐋y := by
  simpa [angularMomentumOperator3D, kroneckerDelta,
    angularMomentumCLM_antisymm (0 : Fin 3) 2] using
    angularMomentum_commutation_angularMomentum (d := 3) 0 1 1 2

/-- Angular momentum squared commutes with every Cartesian component on Schwartz maps. -/
lemma angularMomentumSqr_commutation_3D : ⁅𝐋²[3], angularMomentumOperator3D i⁆ = 0 := by
  fin_cases i <;> exact angularMomentumSqr_commutation_angularMomentum _ _

/-- The Cartesian commutation algebra on the common Hilbert-space Schwartz domain. -/
lemma angularMomentum3DOperator_commutation (j : Fin 3) (ψ : SchwartzSubmodule 3) :
    angularMomentum3DOperator i
        ⟨angularMomentum3DOperator j ψ, angularMomentum3DOperator_range j ψ⟩ -
      angularMomentum3DOperator j
        ⟨angularMomentum3DOperator i ψ, angularMomentum3DOperator_range i ψ⟩ =
      (I * ℏ) • ∑ k : Fin 3, (leviCivitaSymbol ![i, j, k] : ℂ) •
        angularMomentum3DOperator k ψ := by
  rw [angularMomentum3DOperator_apply_apply, angularMomentum3DOperator_apply_apply]
  have h := congrArg
    (fun A : 𝓢(Space 3, ℂ) →L[ℂ] 𝓢(Space 3, ℂ) =>
      schwartzIncl volume (A ((schwartzEquiv volume).symm ψ)))
    (angularMomentum3D_commutation i j)
  simpa only [Ring.lie_def, ContinuousLinearMap.mul_def, sub_apply, comp_apply, smul_apply,
    _root_.sum_apply, map_sub, map_smul, map_sum,
    angularMomentum3DOperator_apply, schwartzEquiv_apply_coe] using h

/-- `[L², Li] = 0` on the common invariant Hilbert-space domain. -/
lemma angularMomentumSqOperator_commutation_3D (ψ : SchwartzSubmodule 3) :
    angularMomentumSqOperator
        ⟨angularMomentum3DOperator i ψ, angularMomentum3DOperator_range i ψ⟩ -
      angularMomentum3DOperator i
        ⟨angularMomentumSqOperator ψ, angularMomentumSqOperator_range ψ⟩ = 0 := by
  change schwartzIncl volume (𝐋² ((schwartzEquiv volume).symm
      (schwartzEquiv volume (angularMomentumOperator3D i ((schwartzEquiv volume).symm ψ))))) -
    schwartzIncl volume (angularMomentumOperator3D i ((schwartzEquiv volume).symm
      (schwartzEquiv volume (𝐋² ((schwartzEquiv volume).symm ψ))))) = 0
  simp only [LinearEquiv.symm_apply_apply]
  have h := congrArg
    (fun A : 𝓢(Space 3, ℂ) →L[ℂ] 𝓢(Space 3, ℂ) =>
      schwartzIncl volume (A ((schwartzEquiv volume).symm ψ)))
    (angularMomentumSqr_commutation_3D i)
  simpa only [Ring.lie_def, ContinuousLinearMap.mul_def, sub_apply, comp_apply, zero_apply,
    map_sub, map_zero] using h

/-!
## C. Ladder operators

These operators act on arbitrary Schwartz vectors. No eigenstate or spectral assumptions
are used in their commutation relations.
-/

/-- The angular momentum raising operator `L₊ = Lx + i Ly` on Schwartz maps. -/
def angularMomentumRaisingCLM : 𝓢(Space 3, ℂ) →L[ℂ] 𝓢(Space 3, ℂ) := 𝐋x + I • 𝐋y

/-- The angular momentum lowering operator `L₋ = Lx - i Ly` on Schwartz maps. -/
def angularMomentumLoweringCLM : 𝓢(Space 3, ℂ) →L[ℂ] 𝓢(Space 3, ℂ) := 𝐋x - I • 𝐋y

@[inherit_doc QuantumMechanics.angularMomentumRaisingCLM]
scoped[AngularMomentum] notation "𝐋⁺" => QuantumMechanics.angularMomentumRaisingCLM
@[inherit_doc QuantumMechanics.angularMomentumLoweringCLM]
scoped[AngularMomentum] notation "𝐋⁻" => QuantumMechanics.angularMomentumLoweringCLM

/-- `[Lz, L₊] = ℏ L₊`. -/
lemma angularMomentumZ_commutation_raising : ⁅𝐋z, 𝐋⁺⁆ = (ℏ : ℂ) • 𝐋⁺ := by
  rw [angularMomentumRaisingCLM, lie_add, lie_smul, angularMomentum3D_commutation_zx,
    ← lie_skew 𝐋z 𝐋y, angularMomentum3D_commutation_yz]
  simp only [smul_neg, smul_smul, ← mul_assoc, I_mul_I, neg_one_mul]
  module

/-- `[Lz, L₋] = -ℏ L₋`. -/
lemma angularMomentumZ_commutation_lowering : ⁅𝐋z, 𝐋⁻⁆ = -(ℏ : ℂ) • 𝐋⁻ := by
  rw [angularMomentumLoweringCLM, lie_sub, lie_smul, angularMomentum3D_commutation_zx,
    ← lie_skew 𝐋z 𝐋y, angularMomentum3D_commutation_yz]
  simp only [smul_neg, smul_smul, ← mul_assoc, I_mul_I, neg_one_mul]
  module

/-- Angular momentum squared commutes with the raising operator. -/
lemma angularMomentumSqr_commutation_raising : ⁅𝐋²[3], 𝐋⁺⁆ = 0 := by
  simp [angularMomentumRaisingCLM, lie_add, lie_smul, angularMomentumSqr_commutation_3D]

/-- Angular momentum squared commutes with the lowering operator. -/
lemma angularMomentumSqr_commutation_lowering : ⁅𝐋²[3], 𝐋⁻⁆ = 0 := by
  simp [angularMomentumLoweringCLM, lie_sub, lie_smul, angularMomentumSqr_commutation_3D]

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
    𝓛⁺ ψ = 𝓛x ψ + I • 𝓛y ψ := by
  simp [angularMomentumRaisingOperator_apply, angularMomentumRaisingCLM,
    angularMomentum3DOperator_apply]

lemma angularMomentumLoweringOperator_apply_eq (ψ : SchwartzSubmodule 3) :
    𝓛⁻ ψ = 𝓛x ψ - I • 𝓛y ψ := by
  simp [angularMomentumLoweringOperator_apply, angularMomentumLoweringCLM,
    angularMomentum3DOperator_apply]

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
    𝓛z ⟨𝓛⁺ ψ, angularMomentumRaisingOperator_range ψ⟩ -
      𝓛⁺ ⟨𝓛z ψ, angularMomentum3DOperator_range 2 ψ⟩ = (ℏ : ℂ) • 𝓛⁺ ψ := by
  change schwartzIncl volume (𝐋z ((schwartzEquiv volume).symm
      (schwartzEquiv volume (𝐋⁺ ((schwartzEquiv volume).symm ψ))))) -
    schwartzIncl volume (𝐋⁺ ((schwartzEquiv volume).symm
      (schwartzEquiv volume (𝐋z ((schwartzEquiv volume).symm ψ))))) =
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
    𝓛z ⟨𝓛⁻ ψ, angularMomentumLoweringOperator_range ψ⟩ -
      𝓛⁻ ⟨𝓛z ψ, angularMomentum3DOperator_range 2 ψ⟩ = -(ℏ : ℂ) • 𝓛⁻ ψ := by
  change schwartzIncl volume (𝐋z ((schwartzEquiv volume).symm
      (schwartzEquiv volume (𝐋⁻ ((schwartzEquiv volume).symm ψ))))) -
    schwartzIncl volume (𝐋⁻ ((schwartzEquiv volume).symm
      (schwartzEquiv volume (𝐋z ((schwartzEquiv volume).symm ψ))))) =
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
