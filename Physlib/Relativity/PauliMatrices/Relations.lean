/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.PauliMatrices.ToTensor
public import Physlib.Relativity.Tensors.ComplexTensor.Units.Basic
public import Physlib.Relativity.Tensors.LeviCivita.Complex
/-!

## Contraction of indices of Pauli matrix.

The results in this file include contractions, anticommutators, and triple-product identities
for the Pauli four-vectors.

The current way this result is proved is by using tensor tree manipulations.
There is likely a more direct path to this result.

## References

* Dreiner, Haber and Martin, *Two-component spinor techniques and Feynman rules for quantum
  field theory and supersymmetry*, arXiv:0812.1594, equations (2.54) and (2.55), in the
  conventions `g = diag(+1, -1, -1, -1)` and `ε⁰¹²³ = +1`. [ref: Dreiner:2008tw]

-/

@[expose] public section

open Matrix
open TensorProduct

namespace PauliMatrix
open Fermion
open complexLorentzTensor
open TensorSpecies
open Tensor

/-- The statement that ` σᵥᵃᵇ σᵛᵃ'ᵇ' = 2 εᵃᵃ' εᵇᵇ'`. -/
lemma pauliCo_contr_pauliContr :
    {σ_^^ | ν α β ⊗ σ^^^ | ν α' β' = (2 : ℂ) •ₜ εL | α α' ⊗ εR | β β'}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  conv_rhs =>
    rw [permT_basis_repr_symm_apply]
    rw [_root_.map_smul]
    simp only [Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue, Fin.succAbove_zero,
      Function.comp_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw (transparency := .instances) [prodT_basis_repr_apply]
    simp only [Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue, Fin.succAbove_zero,
      Function.comp_apply]
    rw [leftMetric_eq_ofGaussianInt, rightMetric_eq_ofGaussianInt]
    simp only [Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue, Fin.succAbove_zero,
      Function.comp_apply, cons_val_zero, cons_val_one, head_cons, ofGaussianInt_basis_repr_apply]
    rw [← GaussianInt.toComplex.map_mul]
    change (2 : ℕ) * _
    rw [show ∀ a : GaussianInt, ((2 : ℕ) : ℂ) * GaussianInt.toComplex a =
      GaussianInt.toComplex ((2 : ℕ) * a) from fun a => by rw [map_mul, map_natCast]]
  rw [contrT_basis_repr_apply]
  conv_lhs =>
    enter [2, x]
    rw [prodT_basis_repr_apply]
    simp only [pauliCo_eq_ofGaussianInt, toTensor_eq_ofGaussianInt]
    simp only [Fin.isValue, Fin.cast_eq_self, ofGaussianInt_basis_repr_apply]
    left
    rw [← GaussianInt.toComplex.map_mul]
  conv_lhs =>
    enter [2, x]
    right
    rw (transparency := .instances) [contr_basis_gaussianInt]
  conv_lhs =>
    enter [2, x]
    rw [← GaussianInt.toComplex.map_mul]
  rw [← map_sum GaussianInt.toComplex]
  apply (Function.Injective.eq_iff GaussianInt.toComplex_injective).mpr
  revert b
  decide +kernel

lemma pauliCoDown_trace_pauliCo : {(σ___ | μ β α ⊗ σ_^^ | ν α β) = (2 •ₜ η' | μ ν)}ᵀ := by
  conv_lhs =>
    rw [pauliCoDown_eq_ofGaussianInt, pauliCo_eq_ofGaussianInt, prodT_ofGaussianInt_ofGaussianInt,
      contrT_ofGaussianInt, contrT_ofGaussianInt]
  conv_rhs =>
    rw [coMetric_eq_ofGaussianInt]
    rw [← map_nsmul]
  apply (Tensor.basis _).repr.injective
  ext b
  conv_rhs => rw [permT_basis_repr_symm_apply]
  simp only [ofGaussianInt_basis_repr_apply]
  apply (Function.Injective.eq_iff GaussianInt.toComplex_injective).mpr
  revert b
  decide +kernel

lemma pauliCo_trace_pauliCoDown: {σ_^^ | μ α β ⊗ σ___ | ν β α = 2 •ₜ η' | μ ν}ᵀ := by
  conv_lhs =>
    rw [pauliCoDown_eq_ofGaussianInt, pauliCo_eq_ofGaussianInt]
    rw [prodT_ofGaussianInt_ofGaussianInt,
      contrT_ofGaussianInt, contrT_ofGaussianInt]
  conv_rhs =>
    rw [coMetric_eq_ofGaussianInt]
    rw [← map_nsmul]
  apply (Tensor.basis _).repr.injective
  ext b
  conv_rhs => rw [permT_basis_repr_symm_apply]
  simp only [ofGaussianInt_basis_repr_apply]
  apply (Function.Injective.eq_iff GaussianInt.toComplex_injective).mpr
  decide +revert +kernel

lemma pauliContr_mul_pauliContrDown_add :
    {((σ^^^ | μ α β ⊗ σ^__ | ν β α') + (σ^^^ | ν α β ⊗ σ^__ | μ β α')) =
    2 •ₜ η | μ ν ⊗ δL | α α'}ᵀ := by
  conv_lhs =>
    rw [pauliContrDown_ofGaussianInt, toTensor_eq_ofGaussianInt, prodT_ofGaussianInt_ofGaussianInt,
      contrT_ofGaussianInt, permT_ofGaussianInt, ← map_add]
  conv_rhs =>
    rw [leftDualLeftUnit_eq_ofGaussianInt, contrMetric_eq_ofGaussianInt,
      prodT_ofGaussianInt_ofGaussianInt, ← map_nsmul, permT_ofGaussianInt]
  apply (Tensor.basis _).repr.injective
  ext b
  simp only [ofGaussianInt_basis_repr_apply]
  apply (Function.Injective.eq_iff GaussianInt.toComplex_injective).mpr
  decide +revert +kernel

lemma auliContrDown_pauliContr_mul_add :
    {((σ^__ | μ β α ⊗ σ^^^ | ν α β') + (σ^__ | ν β α ⊗ σ^^^ | μ α β')) =
    2 •ₜ η | μ ν ⊗ δR' | β β'}ᵀ := by
  conv_lhs =>
    rw [pauliContrDown_ofGaussianInt, toTensor_eq_ofGaussianInt, prodT_ofGaussianInt_ofGaussianInt,
      contrT_ofGaussianInt, permT_ofGaussianInt, ← map_add]
  conv_rhs =>
    rw [dualRightRightUnit_eq_ofGaussianInt, contrMetric_eq_ofGaussianInt,
      prodT_ofGaussianInt_ofGaussianInt, ← map_nsmul, permT_ofGaussianInt]
  apply (Tensor.basis _).repr.injective
  ext b
  simp only [ofGaussianInt_basis_repr_apply]
  apply (Function.Injective.eq_iff GaussianInt.toComplex_injective).mpr
  decide +revert +kernel

/-!

## Triple products

-/

/-- Gaussian integer components of a contraction of `σ^^^` with a copy whose Weyl indices
are dualized. -/
lemma pauliContr_mul_dualWeyl_eq_ofGaussianInt :
    {σ^^^ | μ α β ⊗ σ^^^ | ν τ(α') τ(β)}ᵀ = ofGaussianInt (fun b =>
      ∑ x : Fin 2, pauliContrComponent (b 0) (b 1) x *
        pauliContrDownComponent (b 2) x (b 3)) := by
  rw [toTensor_dualWeyl_eq_ofGaussianInt, toTensor_eq_ofGaussianInt,
    prodT_ofGaussianInt_ofGaussianInt, contrT_ofGaussianInt]
  congr

/-- Gaussian integer components of the reverse contraction of a Weyl-dualized `σ^^^` with
`σ^^^`. -/
lemma dualWeyl_mul_pauliContr_eq_ofGaussianInt :
    {σ^^^ | μ τ(α) τ(β) ⊗ σ^^^ | ν α β'}ᵀ = ofGaussianInt (fun b =>
      ∑ x : Fin 2, pauliContrDownComponent (b 0) (b 1) x *
        pauliContrComponent (b 2) x (b 3)) := by
  rw [toTensor_dualWeyl_eq_ofGaussianInt, toTensor_eq_ofGaussianInt,
    prodT_ofGaussianInt_ofGaussianInt, contrT_ofGaussianInt]
  congr

/-- Contracting `ε4ℂ` with a Lorentz-dualized `σ^^^` agrees with contracting it with
`pauliCo`. -/
lemma leviCivita_mul_pauliDual :
    ({ε4ℂ | μ ν ρ κ ⊗ σ^^^ | τ(κ) α β =
      ε4ℂ | μ ν ρ κ ⊗ σ_^^ | κ α β}ᵀ : Prop) := by
  conv_lhs =>
    simp only [leviCivita_eq_ofGaussianInt_prod, toTensor_dualLorentz_eq_ofGaussianInt]
    rw [prodT_ofGaussianInt_ofGaussianInt, contrT_ofGaussianInt]
  conv_rhs =>
    simp only [leviCivita_eq_ofGaussianInt_prod, pauliCo_eq_ofGaussianInt]
    rw [prodT_ofGaussianInt_ofGaussianInt, contrT_ofGaussianInt]
  apply (Tensor.basis _).repr.injective
  ext b
  rw [ofGaussianInt_basis_repr_apply, permT_basis_repr_symm_apply, ofGaussianInt_basis_repr_apply]
  apply (Function.Injective.eq_iff GaussianInt.toComplex_injective).mpr
  decide +revert +kernel

/-- The three-Pauli identity
`σ^μ barσ^ν σ^ρ = g^{μν} σ^ρ - g^{μρ} σ^ν + g^{νρ} σ^μ + i ε^{μνρκ} σ_κ`,
with barred and lowered forms expressed through index dualization `τ`. -/
lemma pauliContr_mul_pauliContrDown_mul_pauliContr : ({
    σ^^^ | μ α β ⊗ σ^^^ | ν τ(α') τ(β) ⊗ σ^^^ | ρ α' β' =
      ((((η | μ ν ⊗ σ^^^ | ρ α β') + (-((η | μ ρ ⊗ σ^^^ | ν α β'))))
        + (η | ν ρ ⊗ σ^^^ | μ α β'))
        + (Complex.I •ₜ (ε4ℂ | μ ν ρ κ ⊗ σ^^^ | τ(κ) α β')))
    }ᵀ : Prop) := by
  conv_lhs =>
    rw [pauliContr_mul_dualWeyl_eq_ofGaussianInt, toTensor_eq_ofGaussianInt,
      prodT_ofGaussianInt_ofGaussianInt, contrT_ofGaussianInt]
  conv_rhs =>
    rw [leviCivita_mul_pauliDual]
    simp only [contrMetric_eq_ofGaussianInt, toTensor_eq_ofGaussianInt,
      prodT_ofGaussianInt_ofGaussianInt]
    simp only [leviCivita_eq_ofGaussianInt_prod, pauliCo_eq_ofGaussianInt]
    rw [prodT_ofGaussianInt_ofGaussianInt, contrT_ofGaussianInt, permT_ofGaussianInt]
  apply (Tensor.basis _).repr.injective
  ext b
  rw [ofGaussianInt_basis_repr_apply, permT_basis_repr_symm_apply]
  simp only [map_add, Finsupp.coe_add, Pi.add_apply]
  simp only [permT_basis_repr_symm_apply, map_neg, Finsupp.coe_neg, Pi.neg_apply,
    map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, ofGaussianInt_basis_repr_apply]
  conv_rhs => arg 2; rw [show ∀ a : GaussianInt, Complex.I * GaussianInt.toComplex a =
    GaussianInt.toComplex (⟨0, 1⟩ * a) from fun a => by simp [GaussianInt.toComplex_def']]
  apply (show ∀ a b c d e : GaussianInt, a = b + -c + d + e → GaussianInt.toComplex a =
    GaussianInt.toComplex b + -GaussianInt.toComplex c + GaussianInt.toComplex d +
      GaussianInt.toComplex e from fun _ _ _ _ _ h => by simp [h])
  decide +revert +kernel

/-- The conjugate three-Pauli identity
`barσ^μ σ^ν barσ^ρ = g^{μν} barσ^ρ - g^{μρ} barσ^ν + g^{νρ} barσ^μ - i ε^{μνρκ} barσ_κ`,
with barred and lowered forms expressed through index dualization `τ`. -/
lemma pauliContrDown_mul_pauliContr_mul_pauliContrDown : ({
    σ^^^ | μ τ(α) τ(β) ⊗ σ^^^ | ν α β' ⊗ σ^^^ | ρ τ(α') τ(β') =
      ((((η | μ ν ⊗ σ^^^ | ρ τ(α') τ(β))
        + (-((η | μ ρ ⊗ σ^^^ | ν τ(α') τ(β)))))
        + (η | ν ρ ⊗ σ^^^ | μ τ(α') τ(β)))
        + ((-Complex.I) •ₜ (ε4ℂ | μ ν ρ κ ⊗ σ^^^ | τ(κ) τ(α') τ(β))))
    }ᵀ : Prop) := by
  conv_lhs =>
    rw [dualWeyl_mul_pauliContr_eq_ofGaussianInt, toTensor_dualWeyl_eq_ofGaussianInt,
      prodT_ofGaussianInt_ofGaussianInt, contrT_ofGaussianInt]
  conv_rhs =>
    simp only [contrMetric_eq_ofGaussianInt, toTensor_dualWeyl_eq_ofGaussianInt,
      prodT_ofGaussianInt_ofGaussianInt]
    simp only [leviCivita_eq_ofGaussianInt_prod, toTensor_dualAll_eq_ofGaussianInt]
    rw [prodT_ofGaussianInt_ofGaussianInt, contrT_ofGaussianInt, permT_ofGaussianInt]
  apply (Tensor.basis _).repr.injective
  ext b
  rw [ofGaussianInt_basis_repr_apply, permT_basis_repr_symm_apply]
  simp only [map_add, Finsupp.coe_add, Pi.add_apply]
  simp only [permT_basis_repr_symm_apply, map_neg, Finsupp.coe_neg, Pi.neg_apply,
    map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, ofGaussianInt_basis_repr_apply]
  conv_rhs => arg 2; rw [show ∀ a : GaussianInt, -Complex.I * GaussianInt.toComplex a =
    GaussianInt.toComplex (-⟨0, 1⟩ * a) from fun a => by simp [GaussianInt.toComplex_def']]
  apply (show ∀ a b c d e : GaussianInt, a = b + -c + d + e → GaussianInt.toComplex a =
    GaussianInt.toComplex b + -GaussianInt.toComplex c + GaussianInt.toComplex d +
      GaussianInt.toComplex e from fun _ _ _ _ _ h => by simp [h])
  decide +revert +kernel

end PauliMatrix
