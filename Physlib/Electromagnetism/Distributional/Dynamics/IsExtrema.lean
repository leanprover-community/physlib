/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Distributional.Dynamics.Lagrangian
/-!

# Extrema of the Lagrangian density

## i. Overview

In this module we define what it means for an electromagnetic potential
to be an extremum of the Lagrangian density in presence of a Lorentz current density.

This is equivalent to the electromagnetic potential satisfying
Maxwell's equations with sources, i.e. Gauss's law and Ampère's law.

## ii. Key results

- `IsExtrema` : The condition on an electromagnetic potential to be an extrema of the lagrangian.

## iii. Table of contents

- A. Is Extema condition in the distributional case
  - A.1. IsExtrema and Gauss's law and Ampère's law
  - A.2. IsExtrema in terms of Vector Potentials
  - A.3. The exterma condition in terms of tensors
  - A.4. The invariance of the exterma condition under Lorentz transformations

## iv. References

* None.
-/

@[expose] public section
namespace Electromagnetism
open Module realLorentzTensor
open TensorSpecies
open Tensor ContDiff

/-!

## A. Is Extema condition in the distributional case

The above results looked at the extrema condition for electromagnetic potentials that are
functions. We now look at the case where the electromagnetic potential is a distribution.

-/

namespace DistElectromagneticPotential

/-- The proposition on an electromagnetic potential, corresponding to the statement that
  it is an extrema of the lagrangian. -/
def IsExtrema {d} (𝓕 : FreeSpace)
    (A : DistElectromagneticPotential d)
    (J : DistLorentzCurrentDensity d) : Prop := A.gradLagrangian 𝓕 J = 0

lemma isExtrema_iff_gradLagrangian {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d)
    (J : DistLorentzCurrentDensity d) :
    IsExtrema 𝓕 A J ↔ A.gradLagrangian 𝓕 J = 0 := by rfl

lemma isExtrema_iff_components {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d)
    (J : DistLorentzCurrentDensity d) :
    IsExtrema 𝓕 A J ↔ (∀ ε, A.gradLagrangian 𝓕 J ε (Sum.inl 0) = 0)
    ∧ (∀ ε i, A.gradLagrangian 𝓕 J ε (Sum.inr i) = 0) := by
  rw [isExtrema_iff_gradLagrangian]
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  ext1 ε
  funext i
  match i with
  | Sum.inl 0 => exact h.1 ε
  | Sum.inr j => exact h.2 ε j
/-!

### A.1. IsExtrema and Gauss's law and Ampère's law

We show that `A` is an extrema of the lagrangian if and only if Gauss's law and Ampère's law hold.
In other words,

$$\nabla \cdot \mathbf{E} = \frac{\rho}{\varepsilon_0}$$
and
$$\mu_0 \varepsilon_0 \frac{\partial \mathbf{E}_i}{\partial t} -
  \sum_j \partial_j \mathbf{B}_{j i} + \mu_0 \mathbf{J}_i = 0.$$
Here $\mathbf{B}$ is the magnetic field matrix.

-/
open Space
lemma isExtrema_iff_space_time {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d)
    (J : DistLorentzCurrentDensity d) :
    IsExtrema 𝓕 A J ↔
      (∀ ε, distSpaceDiv (A.electricField 𝓕.c) ε = (1/𝓕.ε₀) * (J.chargeDensity 𝓕.c) ε) ∧
      (∀ ε i, 𝓕.μ₀ * 𝓕.ε₀ * (Space.distTimeDeriv (A.electricField 𝓕.c)) ε i -
      ∑ j, ((PiLp.basisFun 2 ℝ (Fin d)).tensorProduct (PiLp.basisFun 2 ℝ (Fin d))).repr
        ((Space.distSpaceDeriv j (A.magneticFieldMatrix 𝓕.c)) ε) (j, i) +
      𝓕.μ₀ * J.currentDensity 𝓕.c ε i = 0) := by
  rw [isExtrema_iff_components]
  have hsurj : Function.Surjective (SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℝ) ℝ
      (SpaceTime.toTimeAndSpace 𝓕.c (d := d)).symm) := by
    intro f
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (SpaceTime.toTimeAndSpace 𝓕.c (d := d)).symm.symm f, ?_⟩
    ext x
    simp
  have hgauss : ∀ a b : ℝ,
      1 / (𝓕.μ₀ * 𝓕.c.val) * a - 𝓕.c.val * b = 0 ↔ a = 1 / 𝓕.ε₀ * b := by
    intro a b
    have c_sq_mul_eq : 𝓕.c.val * b * (𝓕.μ₀ * 𝓕.c.val) = 1 / 𝓕.ε₀ * b := by
      have hcb : 𝓕.c.val * b * (𝓕.μ₀ * 𝓕.c.val) = 𝓕.μ₀ * 𝓕.c.val ^ 2 * b := by ring
      rw [hcb, 𝓕.c_sq]
      field_simp
    rw [sub_eq_zero, div_mul_eq_mul_div, one_mul,
      div_eq_iff (mul_ne_zero 𝓕.μ₀_ne_zero 𝓕.c.val_ne_zero), c_sq_mul_eq]
  have hampere : ∀ T S C : ℝ, 𝓕.μ₀⁻¹ * (1 / 𝓕.c.val ^ 2 * T - S) + C = 0 ↔
      𝓕.μ₀ * 𝓕.ε₀ * T - S + 𝓕.μ₀ * C = 0 := by
    intro T S C
    have mu0_factor_eq : 𝓕.μ₀ * 𝓕.ε₀ * T - S + 𝓕.μ₀ * C
        = 𝓕.μ₀ * (𝓕.μ₀⁻¹ * (1 / 𝓕.c.val ^ 2 * T - S) + C) := by
      rw [𝓕.c_sq]
      field_simp
    rw [mu0_factor_eq, mul_eq_zero, or_iff_right 𝓕.μ₀_ne_zero]
  refine and_congr ?_ ?_
  · simp only [gradLagrangian_sum_inl_0, SpaceTime.distTimeSlice_symm_apply]
    rw [hsurj.forall]
    exact forall_congr' fun ε => hgauss _ _
  · simp only [gradLagrangian_sum_inr_i, SpaceTime.distTimeSlice_symm_apply]
    rw [hsurj.forall]
    exact forall_congr' fun ε => forall_congr' fun i => hampere _ _ _

/-!

### A.2. IsExtrema in terms of Vector Potentials

We show that `A` is an extrema of the lagrangian if and only if Gauss's law and Ampère's law hold.
In other words,

$$\nabla \cdot \mathbf{E} = \frac{\rho}{\varepsilon_0}$$
and
$$\mu_0 \varepsilon_0 \frac{\partial \mathbf{E}_i}{\partial t} -
  \sum_j -(\partial_j \partial_j \vec A_i - \partial_j \partial_i \vec A_j) +
  \mu_0 \mathbf{J}_i = 0.$$

-/

lemma isExtrema_iff_vectorPotential {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d)
    (J : DistLorentzCurrentDensity d) :
    IsExtrema 𝓕 A J ↔
      (∀ ε, distSpaceDiv (A.electricField 𝓕.c) ε = (1/𝓕.ε₀) * (J.chargeDensity 𝓕.c) ε) ∧
      (∀ ε i, 𝓕.μ₀ * 𝓕.ε₀ * distTimeDeriv (A.electricField 𝓕.c) ε i -
      (∑ x, -(distSpaceDeriv x (distSpaceDeriv x (A.vectorPotential 𝓕.c)) ε i
        - distSpaceDeriv x (distSpaceDeriv i (A.vectorPotential 𝓕.c)) ε x)) +
      𝓕.μ₀ * J.currentDensity 𝓕.c ε i = 0) := by
  rw [isExtrema_iff_space_time]
  refine and_congr (by rfl) ?_
  suffices ∀ ε i, ∑ x, -(distSpaceDeriv x (distSpaceDeriv x (A.vectorPotential 𝓕.c)) ε i
        - distSpaceDeriv x (distSpaceDeriv i (A.vectorPotential 𝓕.c)) ε x) =
        ∑ j, ((PiLp.basisFun 2 ℝ (Fin d)).tensorProduct (PiLp.basisFun 2 ℝ (Fin d))).repr
          ((Space.distSpaceDeriv j (A.magneticFieldMatrix 𝓕.c)) ε) (j, i) by
    conv_lhs => enter [2, 2]; rw [← this]
  intro ε i
  congr
  funext j
  rw [magneticFieldMatrix_distSpaceDeriv_basis_repr_eq_vector_potential]
  ring

/-!

### A.3. The exterma condition in terms of tensors

We show that `A` is an extrema of the lagrangian if and only if the equation
$$\frac{1}{\mu_0} \partial_\kappa F^{\kappa \nu'} - J^{\nu'} = 0,$$
holds.

-/
open SpaceTime minkowskiMatrix
set_option maxHeartbeats 600000 in
lemma isExterma_iff_tensor {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d)
    (J : DistLorentzCurrentDensity d) :
    IsExtrema 𝓕 A J ↔ ∀ ε,
    {((1/ 𝓕.μ₀ : ℝ) • distTensorDeriv A.fieldStrength ε | κ κ ν') + - (J ε | ν')}ᵀ = 0 := by
  apply Iff.intro
  · intro h
    simp only [IsExtrema] at h
    intro x
    have h1 : ((Tensorial.toTensor (M := Lorentz.Vector d)).symm
        (permT id (IsReindexing.auto) {((1/ 𝓕.μ₀ : ℝ) •
          distTensorDeriv A.fieldStrength x | κ κ ν') + - (J x | ν')}ᵀ)) = 0 := by
      funext ν
      have h2 : gradLagrangian 𝓕 A J x ν = 0 := by simp [h]
      rw [gradLagrangian_eq_tensor A J] at h2
      simp at h2
      have hn : minkowskiMatrix ν ν ≠ 0 := minkowskiMatrix.η_diag_ne_zero
      simp_all
    rw [EmbeddingLike.map_eq_zero_iff, permT_eq_zero_iff] at h1
    exact h1
  · intro h
    simp only [IsExtrema]
    ext1 x
    funext ν
    rw [gradLagrangian_eq_tensor A J, h]
    simp

/-!

### A.4. The invariance of the exterma condition under Lorentz transformations

We show that the Exterma condition is invariant under Lorentz transformations.
This implies that if an electromagnetic potential is an extrema in one inertial frame,
it is also an extrema in any other inertial frame.
In otherwords that the Maxwell's equations are Lorentz invariant.
A natural consequence of this is that the speed of light is the same in all inertial frames.

-/

lemma isExterma_equivariant {𝓕 : FreeSpace}
    (A : DistElectromagneticPotential d)
    (J : DistLorentzCurrentDensity d) (Λ : LorentzGroup d) :
    IsExtrema 𝓕 (Λ • A) (Λ • J) ↔ IsExtrema 𝓕 A J := by
  rw [isExterma_iff_tensor]
  conv_lhs =>
    enter [x, 1, 1, 2, 2, 2]
    rw [fieldStrength_equivariant, distTensorDeriv_equivariant]
    rw [lorentzGroup_smul_dist_apply]
  conv_lhs =>
    enter [x]
    rw [smul_comm]
    rw [Tensorial.toTensor_smul, lorentzGroup_smul_dist_apply, Tensorial.toTensor_smul]
    simp only [one_div, map_smul, actionT_smul,
      contrT_equivariant, map_neg, permT_equivariant]
    rw [smul_comm, ← Tensor.actionT_neg, ← Tensor.actionT_add]
  apply Iff.intro
  · intro h
    rw [isExterma_iff_tensor A J]
    intro x
    apply MulAction.injective Λ
    simp only [one_div, map_smul, map_neg,
      _root_.smul_add, actionT_smul, _root_.smul_neg, _root_.smul_zero]
    simpa only [Fin.isValue, schwartzAction_mul_apply, inv_mul_cancel, map_one,
      one_apply_eq_self, smul_add, actionT_smul, smul_neg] using h (schwartzAction Λ x)
  · intro h x
    rw [isExterma_iff_tensor A J] at h
    specialize h (schwartzAction Λ⁻¹ x)
    simp only [Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue, one_div, map_smul, map_neg] at h
    rw [h]
    simp

end DistElectromagneticPotential
end Electromagnetism
