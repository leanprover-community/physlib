/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.CoVector.Basic
public import Physlib.Relativity.Tensors.RealTensor.Basic
/-!

# Tensorial nature of Lorentz covectors

We define the tensorial instance on `Lorentz.coVector`, and show
prove properties related to the Lorentz group action and the basis.

-/

@[expose] public section

open Module
open Matrix
open MatrixGroups
open Complex
open TensorProduct

noncomputable section

namespace Lorentz
open realLorentzTensor

namespace CoVector

open TensorSpecies
open Tensor

/-!

## Tensorial

-/

/-- The equivalence between the type of indices of a Lorentz vector and
  `Fin 1 ⊕ Fin d`. -/
def indexEquiv {d : ℕ} :
    ComponentIdx (S := (realLorentzTensor d)) ![Color.down] ≃ Fin 1 ⊕ Fin d :=
  ComponentIdx.single (S := realLorentzTensor d) (c := Color.down)

instance tensorial {d : ℕ} : Tensorial (realLorentzTensor d) ![.down] (CoVector d) where
  toTensor := LinearEquiv.symm <|
    Equiv.toLinearEquiv
    ((Tensor.basis (S := (realLorentzTensor d)) ![.down]).repr.toEquiv.trans <|
  Finsupp.equivFunOnFinite.trans <|
  (Equiv.piCongrLeft' _ indexEquiv))
    { map_add := fun x y => by
        simp [map_add]
        rfl
      map_smul := fun c x => by
        simp [_root_.map_smul]
        rfl}

open Tensorial

lemma toTensor_symm_apply {d : ℕ} (p : ℝT[d, .down]) :
    (toTensor (self := tensorial)).symm p =
    (Equiv.piCongrLeft' _ indexEquiv <|
    Finsupp.equivFunOnFinite <|
    (Tensor.basis (S := (realLorentzTensor d)) _).repr p) := rfl

lemma toTensor_symm_pure {d : ℕ} (p : Pure (realLorentzTensor d) ![.down]) (i : Fin 1 ⊕ Fin d) :
    (toTensor (self := tensorial)).symm p.toTensor i =
    ((Lorentz.coBasis d).repr (p 0)) (indexEquiv.symm i 0) := by
  rw [toTensor_symm_apply]
  simp only [Equiv.piCongrLeft'_apply, Finsupp.equivFunOnFinite_apply, Tensor.basis_repr_pure,
    Pure.component, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.prod_singleton,
    cons_val_zero]
  rfl

/-!

## Basis

-/

set_option backward.isDefEq.respectTransparency false in
lemma toTensor_symm_basis {d : ℕ} (μ : Fin 1 ⊕ Fin d) :
    (toTensor (self := tensorial)).symm (Tensor.basis ![Color.down] (indexEquiv.symm μ)) =
    basis μ := by
  funext i
  simp [Tensor.basis_apply, toTensor_symm_pure, Pure.basisVector, Finsupp.single_apply,
    indexEquiv]

lemma toTensor_basis_eq_tensor_basis {d : ℕ} (μ : Fin 1 ⊕ Fin d) :
    toTensor (basis μ) = Tensor.basis ![Color.down] (indexEquiv.symm μ) := by
  rw [← toTensor_symm_basis]
  simp

lemma basis_eq_map_tensor_basis {d} : basis =
    ((Tensor.basis (S := realLorentzTensor d) ![Color.down]).map
    toTensor.symm).reindex indexEquiv := by
  ext μ
  rw [← toTensor_symm_basis]
  simp

lemma tensor_basis_map_eq_basis_reindex {d} :
    (Tensor.basis (S := realLorentzTensor d) ![Color.down]).map toTensor.symm =
    basis.reindex indexEquiv.symm := by
  rw [basis_eq_map_tensor_basis]
  ext μ
  simp

lemma tensor_basis_repr_toTensor_apply {d : ℕ} (p : CoVector d) (μ : ComponentIdx ![Color.down]) :
    (Tensor.basis ![Color.down]).repr (toTensor p) μ =
    p (indexEquiv μ) := by
  obtain ⟨p, rfl⟩ := toTensor.symm.surjective p
  simp only [LinearEquiv.apply_symm_apply]
  apply induction_on_pure (t := p)
  · intro p
    simp only [Tensor.basis_repr_pure, Pure.component, Finset.univ_unique, Fin.default_eq_zero,
      Fin.isValue, Finset.prod_singleton, cons_val_zero, toTensor_symm_pure,
      Equiv.symm_apply_apply]
    rfl
  · intro r t h
    simp [h]
  · intro t1 t2 h1 h2
    simp [h1, h2]

/-!

## The action of the Lorentz group

-/

set_option backward.isDefEq.respectTransparency false in
lemma smul_eq_sum {d : ℕ} (i : Fin 1 ⊕ Fin d) (Λ : LorentzGroup d) (p : CoVector d) :
    (Λ • p) i = ∑ j, Λ⁻¹.1 j i * p j := by
  obtain ⟨p, rfl⟩ := toTensor.symm.surjective p
  rw [smul_toTensor_symm]
  apply induction_on_pure (t := p)
  · intro p
    rw [actionT_pure, toTensor_symm_pure]
    conv_lhs =>
      enter [1, 2]
      change (LorentzGroup.transpose Λ⁻¹) *ᵥ (p 0)
    rw [coBasis_repr_apply]
    conv_lhs => simp [indexEquiv]
    rw [mulVec_eq_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, transpose_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, toTensor_symm_pure, coBasis_repr_apply]
    rfl
  · intro r t h
    simp only [actionT_smul, _root_.map_smul, apply_smul, h, Finset.mul_sum, mul_left_comm]
  · intro t1 t2 h1 h2
    simp only [actionT_add, map_add, h1, h2, apply_add, mul_add, Finset.sum_add_distrib]

lemma smul_eq_mulVec {d} (Λ : LorentzGroup d) (p : CoVector d) :
    Λ • p = (LorentzGroup.transpose Λ⁻¹).1 *ᵥ p := by
  funext i
  rw [smul_eq_sum, mulVec_eq_sum]
  simp only [op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul,
    mul_comm]
  rfl

lemma smul_add {d : ℕ} (Λ : LorentzGroup d) (p q : CoVector d) :
    Λ • (p + q) = Λ • p + Λ • q := by simp

@[simp]
lemma smul_sub {d : ℕ} (Λ : LorentzGroup d) (p q : CoVector d) :
    Λ • (p - q) = Λ • p - Λ • q := by
  rw [smul_eq_mulVec, smul_eq_mulVec, smul_eq_mulVec, Matrix.mulVec_sub]

lemma smul_zero {d : ℕ} (Λ : LorentzGroup d) :
    Λ • (0 : CoVector d) = 0 := by
  rw [smul_eq_mulVec, Matrix.mulVec_zero]

lemma smul_neg {d : ℕ} (Λ : LorentzGroup d) (p : CoVector d) :
    Λ • (-p) = - (Λ • p) := by
  rw [smul_eq_mulVec, smul_eq_mulVec, Matrix.mulVec_neg]

/-- The Lorentz action on vectors as a continuous linear map. -/
def actionCLM {d : ℕ} (Λ : LorentzGroup d) :
    CoVector d →L[ℝ] CoVector d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => Λ • v
      map_add' := smul_add Λ
      map_smul' := fun c v => by
        funext i
        simp only [RingHom.id_apply, apply_smul, smul_eq_sum, Finset.mul_sum, mul_left_comm]}

lemma actionCLM_apply {d : ℕ} (Λ : LorentzGroup d) (p : CoVector d) :
    actionCLM Λ p = Λ • p := rfl

lemma smul_basis {d : ℕ} (Λ : LorentzGroup d) (μ : Fin 1 ⊕ Fin d) :
    Λ • basis μ = ∑ ν, Λ⁻¹.1 μ ν • basis ν := by
  funext i
  rw [smul_eq_sum, Fintype.sum_apply]
  simp only [apply_smul, basis_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

end CoVector

end Lorentz
