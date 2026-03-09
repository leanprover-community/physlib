/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Electromagnetism.Basic
public import PhysLean.SpaceAndTime.SpaceTime.TimeSlice
public import PhysLean.Mathematics.VariationalCalculus.HasVarGradient
/-!

# The Electromagnetic Potential

## i. Overview

The electromagnetic potential `A^μ` is the fundamental objects in
electromagnetism. Mathematically it is related to a connection
on a `U(1)`-bundle.

We define the electromagnetic potential as a function from
spacetime to contravariant Lorentz vectors.

## ii. Key results

- `ElectromagneticPotential` : is the type of electromagnetic potentials.
- `ElectromagneticPotential.deriv` : the derivative tensor `∂_μ A^ν`.
- `DistElectromagneticPotential` : the type of electromagnetic potentials as distributions.

## iii. Table of contents

- A. The electromagnetic potential
  - A.1. The action on the space-time derivatives
  - A.2. Differentiability
  - A.3. Variational adjoint derivative of component
  - A.4. Variational adjoint derivative of derivatives of the potential
- B. The derivative tensor of the electromagnetic potential
  - B.1. Equivariance of the derivative tensor
  - B.2. The elements of the derivative tensor in terms of the basis
- C. The electromagnetic potential as a distribution
  - C.1. The derivative of the electromagnetic potential as a distribution
  - C.2. The derivative in terms of the basis
  - C.3. Equivariance of the derivative distribution

## iv. References

- https://quantummechanics.ucsd.edu/ph130a/130_notes/node452.html
- https://ph.qmul.ac.uk/sites/default/files/EMT10new.pdf

-/

@[expose] public section

namespace Electromagnetism
open Module realLorentzTensor
open IndexNotation
open TensorSpecies
open Tensor

/-!

## A. The electromagnetic potential

We define the electromagnetic potential as a function from spacetime to
contravariant Lorentz vectors, and prove some simple results about it.

-/
/-- The electromagnetic potential is a tensor `A^μ`. -/
noncomputable abbrev ElectromagneticPotential (d : ℕ := 3) :=
  SpaceTime d → Lorentz.Vector d

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one
/-!

### A.1. The action on the space-time derivatives

Given a ElectromagneticPotential `A^μ`, we can consider its derivative `∂_μ A^ν`.
Under a Lorentz transformation `Λ`, this transforms as
`∂_ μ (fun x => Λ • A (Λ⁻¹ • x))`, we write an expression for this in terms of the tensor.
`∂_ ρ A (Λ⁻¹ • x) κ`.

-/

lemma spaceTime_deriv_action_eq_sum {d} {μ ν : Fin 1 ⊕ Fin d} {x : SpaceTime d}
    (Λ : LorentzGroup d) (A : ElectromagneticPotential d) (hA : Differentiable ℝ A) :
    ∂_ μ (fun x => Λ • A (Λ⁻¹ • x)) x ν =
    ∑ κ, ∑ ρ, (Λ.1 ν κ * Λ⁻¹.1 ρ μ) * ∂_ ρ A (Λ⁻¹ • x) κ := by
  calc _
    _ = ((Λ • (∂_ μ (fun x => A (Λ⁻¹ • x)) x)) ν) := by
      have hdif : ∀ i, DifferentiableAt ℝ (fun x => A (Λ⁻¹ • x) i) x := by
          intro i
          apply Differentiable.differentiableAt
          revert i
          rw [SpaceTime.differentiable_vector]
          conv =>
            enter [2, x]; rw [← Lorentz.Vector.actionCLM_apply]
          apply Differentiable.fun_comp hA
          exact ContinuousLinearMap.differentiable (Lorentz.Vector.actionCLM Λ⁻¹)
      trans ∂_ μ (fun x => (Λ • A (Λ⁻¹ • x)) ν) x
      · rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq, SpaceTime.fderiv_vector]
        intro ν
        conv =>
          enter [2, x]; rw [← Lorentz.Vector.actionCLM_apply, ← Lorentz.Vector.actionCLM_apply]
        apply Differentiable.comp
        · exact ContinuousLinearMap.differentiable (Lorentz.Vector.actionCLM Λ)
        · apply Differentiable.comp
          · exact hA
          · exact ContinuousLinearMap.differentiable (Lorentz.Vector.actionCLM Λ⁻¹)
      conv_lhs =>
        enter [2, x]
        rw [Lorentz.Vector.smul_eq_sum]
      rw [SpaceTime.deriv_eq]
      rw [fderiv_fun_sum (𝕜 := ℝ)]
      conv_lhs =>
        enter [1, 2, i]
        rw [fderiv_const_mul (hdif i)]
      simp only [Nat.reduceSucc, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_smul',
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Lorentz.Vector.smul_eq_sum]
      congr
      funext κ
      congr
      rw [SpaceTime.deriv_eq, SpaceTime.fderiv_vector]
      · exact hA.comp (Lorentz.Vector.actionCLM Λ⁻¹).differentiable
      · intro i _
        apply DifferentiableAt.const_mul
        exact hdif i
    _ = (((Λ • (∑ ρ, Λ⁻¹.1 ρ μ • ∂_ ρ A (Λ⁻¹ • x)))) ν) := by
      rw [SpaceTime.deriv_comp_lorentz_action]
      · exact hA
    _ = (∑ κ, Λ.1 ν κ * (∑ ρ, Λ⁻¹.1 ρ μ • ∂_ ρ A (Λ⁻¹ • x) κ)) := by
      rw [Lorentz.Vector.smul_eq_sum]
      congr
      funext j
      congr
      rw [Lorentz.Vector.apply_sum]
      rfl
  apply Finset.sum_congr rfl (fun κ _ => ?_)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl (fun ρ _ => ?_)
  simp only [Nat.reduceSucc, smul_eq_mul]
  ring

/-!

### A.2. Differentiability

We show that the components of field strength tensor are differentiable if the potential is.
-/

lemma differentiable_component {d : ℕ}
    (A : ElectromagneticPotential d) (hA : Differentiable ℝ A) (μ : Fin 1 ⊕ Fin d) :
    Differentiable ℝ (fun x => A x μ) := by
  revert μ
  rw [SpaceTime.differentiable_vector]
  exact hA

/-!

### A.3. Variational adjoint derivative of component

We find the variational adjoint derivative of the components of the potential.
This will be used to find e.g. the variational derivative of the kinetic term,
and derive the equations of motion.

-/

open ContDiff
lemma hasVarAdjDerivAt_component {d : ℕ} (μ : Fin 1 ⊕ Fin d) (A : SpaceTime d → Lorentz.Vector d)
    (hA : ContDiff ℝ ∞ A) :
        HasVarAdjDerivAt (fun (A' : SpaceTime d → Lorentz.Vector d) x => A' x μ)
          (fun (A' : SpaceTime d → ℝ) x => A' x • Lorentz.Vector.basis μ) A := by
  let f : SpaceTime d → Lorentz.Vector d → ℝ := fun x v => v μ
  let f' : SpaceTime d → Lorentz.Vector d → ℝ → Lorentz.Vector d := fun x _ c =>
    c • Lorentz.Vector.basis μ
  change HasVarAdjDerivAt (fun A' x => f x (A' x)) (fun ψ x => f' x (A x) (ψ x)) A
  apply HasVarAdjDerivAt.fmap
  · fun_prop
  · fun_prop
  intro x A
  refine { differentiableAt := ?_, hasAdjoint_fderiv := ?_ }
  · fun_prop
  refine { adjoint_inner_left := ?_ }
  intro u v
  simp [f,f']
  simp [inner_smul_left, Lorentz.Vector.basis_inner]
  ring_nf
  rfl

/-!

### A.4. Variational adjoint derivative of derivatives of the potential

We find the variational adjoint derivative of the derivatives of the components of the potential.
This will again be used to find the variational derivative of the kinetic term,
and derive the equations of motion (Maxwell's equations).

-/

lemma deriv_hasVarAdjDerivAt {d} (μ ν : Fin 1 ⊕ Fin d) (A : SpaceTime d → Lorentz.Vector d)
    (hA : ContDiff ℝ ∞ A) :
    HasVarAdjDerivAt (fun (A : SpaceTime d → Lorentz.Vector d) x => ∂_ μ A x ν)
      (fun ψ x => - (fderiv ℝ ψ x) (Lorentz.Vector.basis μ) • Lorentz.Vector.basis ν) A := by
  have h0' := HasVarAdjDerivAt.fderiv' _ _
        (hF := hasVarAdjDerivAt_component ν A hA) A (Lorentz.Vector.basis μ)
  refine HasVarAdjDerivAt.congr (G := (fun (A : SpaceTime d →
    Lorentz.Vector d) x => ∂_ μ A x ν)) h0' ?_
  intro φ hφ
  funext x
  simp only
  rw [deriv_apply_eq μ ν φ]
  exact hφ.differentiable (by simp)

/-!

## B. The derivative tensor of the electromagnetic potential

We define the derivative as a tensor in `Lorentz.CoVector ⊗[ℝ] Lorentz.Vector` for the
electromagnetic potential `A^μ`. We then prove that this tensor transforms correctly
under Lorentz transformations.

-/

/-- The derivative of the electric potential, `∂_μ A^ν`. -/
noncomputable def deriv {d} (A : ElectromagneticPotential d) :
    SpaceTime d → Lorentz.CoVector d ⊗[ℝ] Lorentz.Vector d := fun x =>
  ∑ μ, ∑ ν, (∂_ μ A x ν) • Lorentz.CoVector.basis μ ⊗ₜ[ℝ] Lorentz.Vector.basis ν

/-!

### B.1. Equivariance of the derivative tensor

We show that the derivative tensor is equivariant under the action of the Lorentz group.
That is, `∂_μ (fun x => Λ • A (Λ⁻¹ • x)) = Λ • (∂_μ A (Λ⁻¹ • x))`, or in words:
applying the Lorentz transformation to the potential and then taking the derivative is the same
as taking the derivative and then applying the Lorentz transformation to the resulting tensor.

-/
lemma deriv_equivariant {d} {x : SpaceTime d} (A : ElectromagneticPotential d)
    (Λ : LorentzGroup d)
    (hf : Differentiable ℝ A) : deriv (fun x => Λ • A (Λ⁻¹ • x)) x = Λ • (deriv A (Λ⁻¹ • x)) := by
    calc _
      _ = ∑ μ, ∑ ν, ∑ κ, ∑ ρ, (Λ.1 ν κ * (Λ⁻¹.1 ρ μ • ∂_ ρ A (Λ⁻¹ • x) κ)) •
          (Lorentz.CoVector.basis μ) ⊗ₜ[ℝ]
          Lorentz.Vector.basis ν := by
        refine Finset.sum_congr rfl (fun μ _ => ?_)
        refine Finset.sum_congr rfl (fun ν _ => ?_)
        rw [spaceTime_deriv_action_eq_sum Λ A hf]
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl (fun κ _ => ?_)
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl (fun ρ _ => ?_)
        congr 1
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, smul_eq_mul]
        ring
      _ = ∑ μ, ∑ ν, ∑ κ, ∑ ρ, (∂_ ρ A (Λ⁻¹ • x) κ) •
          (Λ⁻¹.1 ρ μ • (Lorentz.CoVector.basis μ)) ⊗ₜ[ℝ]
          (Λ.1 ν κ • Lorentz.Vector.basis ν) := by
        refine Finset.sum_congr rfl (fun μ _ => ?_)
        refine Finset.sum_congr rfl (fun ν _ => ?_)
        refine Finset.sum_congr rfl (fun κ _ => ?_)
        refine Finset.sum_congr rfl (fun ρ _ => ?_)
        rw [smul_tmul, tmul_smul, tmul_smul, smul_smul, smul_smul]
        congr 1
        simp only [Nat.reduceSucc, smul_eq_mul]
        ring
      _ = ∑ κ, ∑ ρ, ∑ μ, ∑ ν, (∂_ ρ A (Λ⁻¹ • x) κ) •
          (Λ⁻¹.1 ρ μ • (Lorentz.CoVector.basis μ)) ⊗ₜ[ℝ]
          (Λ.1 ν κ • Lorentz.Vector.basis ν) := by
        conv_lhs => enter [2, μ]; rw [Finset.sum_comm]
        conv_lhs => rw [Finset.sum_comm]
        conv_lhs => enter [2, κ, 2, μ]; rw [Finset.sum_comm]
        conv_lhs => enter [2, κ]; rw [Finset.sum_comm]
      _ = ∑ κ, ∑ ρ, (∂_ ρ A (Λ⁻¹ • x) κ) • (∑ μ, Λ⁻¹.1 ρ μ • (Lorentz.CoVector.basis μ)) ⊗ₜ[ℝ]
          (∑ ν, Λ.1 ν κ • Lorentz.Vector.basis ν) := by
        conv_rhs =>
          enter [2, κ,2, ρ]; rw [sum_tmul, Finset.smul_sum]
          enter [2, μ]; rw [tmul_sum, Finset.smul_sum];
      _ = ∑ κ, ∑ ρ, (∂_ ρ A (Λ⁻¹ • x) κ) • (Λ • (Lorentz.CoVector.basis ρ)) ⊗ₜ[ℝ]
          (Λ • Lorentz.Vector.basis κ) := by
        apply Finset.sum_congr rfl (fun κ _ => ?_)
        apply Finset.sum_congr rfl (fun ρ _ => ?_)
        congr 2
        · rw [Lorentz.CoVector.smul_basis]
        · rw [Lorentz.Vector.smul_basis]
      _ = ∑ κ, ∑ ρ, (∂_ ρ A (Λ⁻¹ • x) κ) • Λ • ((Lorentz.CoVector.basis ρ) ⊗ₜ[ℝ]
        Lorentz.Vector.basis κ) := by
        apply Finset.sum_congr rfl (fun κ _ => ?_)
        apply Finset.sum_congr rfl (fun ρ _ => ?_)
        rw [Tensorial.smul_prod]
    rw [deriv]
    conv_rhs => rw [← Tensorial.smulLinearMap_apply]
    rw [Finset.sum_comm]
    simp
    rfl

/-!

### B.2. The elements of the derivative tensor in terms of the basis

We show that in the standard basis, the elements of the derivative tensor
are just equal to `∂_ μ A x ν`.

-/

@[simp]
lemma deriv_basis_repr_apply {d} {μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)}
    (A : ElectromagneticPotential d)
    (x : SpaceTime d) :
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (deriv A x) μν =
    ∂_ μν.1 A x μν.2 := by
  match μν with
  | (μ, ν) =>
  rw [deriv]
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply,
    Pi.smul_apply, Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, smul_eq_mul]
  rw [Finset.sum_eq_single μ, Finset.sum_eq_single ν]
  · simp
  · intro μ' _ h
    simp [h]
  · simp
  · intro ν' _ h
    simp [h]
  · simp

lemma toTensor_deriv_basis_repr_apply {d} (A : ElectromagneticPotential d)
    (x : SpaceTime d) (b : ComponentIdx (S := realLorentzTensor d)
      (Fin.append ![Color.down] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (deriv A x)) b =
    ∂_ (finSumFinEquiv.symm (b 0)) A x (finSumFinEquiv.symm (b 1)) := by
  rw [Tensorial.basis_toTensor_apply]
  rw [Tensorial.basis_map_prod]
  simp only [Nat.reduceSucc, Nat.reduceAdd, Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm, Fin.isValue]
  rw [Lorentz.Vector.tensor_basis_map_eq_basis_reindex,
    Lorentz.CoVector.tensor_basis_map_eq_basis_reindex]
  have hb : (((Lorentz.CoVector.basis (d := d)).reindex
      Lorentz.CoVector.indexEquiv.symm).tensorProduct
      (Lorentz.Vector.basis.reindex Lorentz.Vector.indexEquiv.symm)) =
      ((Lorentz.CoVector.basis (d := d)).tensorProduct (Lorentz.Vector.basis (d := d))).reindex
      (Lorentz.CoVector.indexEquiv.symm.prodCongr Lorentz.Vector.indexEquiv.symm) := by
    ext b
    match b with
    | ⟨i, j⟩ =>
    simp
  rw [hb]
  rw [Module.Basis.repr_reindex_apply, deriv_basis_repr_apply]
  rfl

end ElectromagneticPotential

/-!

## C. The electromagnetic potential as a distribution

-/

/-- The electromagnetic potential as a distribution and as a tensor `A^μ`. -/
noncomputable abbrev DistElectromagneticPotential (d : ℕ := 3) :=
  (SpaceTime d) →d[ℝ] Lorentz.Vector d

namespace DistElectromagneticPotential
open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix SchwartzMap
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

### C.1. The derivative of the electromagnetic potential as a distribution

-/

/-- The derivative of a electromagnetic potential, which is a distribution. -/
noncomputable def deriv {d} : DistElectromagneticPotential d →ₗ[ℝ]
    (SpaceTime d) →d[ℝ] Lorentz.CoVector d ⊗[ℝ] Lorentz.Vector d := distTensorDeriv

lemma deriv_eq_sum_sum {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    deriv A ε =∑ μ, ∑ ν, (SpaceTime.distDeriv μ A ε ν) •
      Lorentz.CoVector.basis μ ⊗ₜ[ℝ] Lorentz.Vector.basis ν := by
  simp [deriv, distTensorDeriv_apply]
  congr
  funext μ
  conv_lhs => rw [← Lorentz.Vector.basis.sum_repr (SpaceTime.distDeriv μ A ε)]
  rw [tmul_sum]
  congr
  funext ν
  simp
  rfl
/-!

### C.2. The derivative in terms of the basis

-/

@[simp]
lemma deriv_basis_repr_apply {d} {μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)}
    (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (deriv A ε) μν =
    distDeriv μν.1 A ε μν.2 := by
  match μν with
  | (μ, ν) =>
  rw [deriv_eq_sum_sum]
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply,
    Pi.smul_apply, Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, smul_eq_mul]
  rw [Finset.sum_eq_single μ, Finset.sum_eq_single ν]
  · simp
  · intro μ' _ h
    simp [h]
  · simp
  · intro ν' _ h
    simp [h]
  · simp

lemma toTensor_deriv_basis_repr_apply {d} (A : DistElectromagneticPotential d)
    (ε : 𝓢(SpaceTime d, ℝ)) (b : ComponentIdx (S := realLorentzTensor d)
      (Fin.append ![Color.down] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (deriv A ε)) b =
    distDeriv (finSumFinEquiv.symm (b 0)) A ε (finSumFinEquiv.symm (b 1)) := by
  rw [Tensorial.basis_toTensor_apply]
  rw [Tensorial.basis_map_prod]
  simp only [Nat.reduceSucc, Nat.reduceAdd, Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm, Fin.isValue]
  rw [Lorentz.Vector.tensor_basis_map_eq_basis_reindex,
    Lorentz.CoVector.tensor_basis_map_eq_basis_reindex]
  have hb : (((Lorentz.CoVector.basis (d := d)).reindex
      Lorentz.CoVector.indexEquiv.symm).tensorProduct
      (Lorentz.Vector.basis.reindex Lorentz.Vector.indexEquiv.symm)) =
      ((Lorentz.CoVector.basis (d := d)).tensorProduct (Lorentz.Vector.basis (d := d))).reindex
      (Lorentz.CoVector.indexEquiv.symm.prodCongr Lorentz.Vector.indexEquiv.symm) := by
    ext b
    match b with
    | ⟨i, j⟩ =>
    simp
  rw [hb]
  rw [Module.Basis.repr_reindex_apply, deriv_basis_repr_apply]
  rfl

/-!

### C.3. Equivariance of the derivative distribution

-/

lemma deriv_equivariant {d} {A : DistElectromagneticPotential d}
    (Λ : LorentzGroup d) : deriv (Λ • A) = Λ • deriv A := by
  rw [deriv, distTensorDeriv_equivariant]

end DistElectromagneticPotential

end Electromagnetism
