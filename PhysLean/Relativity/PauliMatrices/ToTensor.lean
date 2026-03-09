/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Relativity.Tensors.ComplexTensor.Metrics.Basic
public import PhysLean.Relativity.PauliMatrices.AsTensor
public import PhysLean.Relativity.Tensors.ComplexTensor.Metrics.Basic
/-!

# Pauli matrices as a tensor

-/

@[expose] public section
open Module IndexNotation
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open OverColor.Discrete
noncomputable section

namespace PauliMatrix
open Fermion
open complexLorentzTensor
open TensorSpecies
open Tensor
open Tensorial

/-!

## Tensorial structure

The tensorial structure on the type
`Fin 1 ⊕ Fin 3 → Matrix (Fin 2) (Fin 2) ℂ`
and properties thereof.

-/

/-- The equivalence between the type of indices of a [.up, .upL, .upR] tensor and
  `(Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2`. -/
def indexEquiv : ComponentIdx (S := complexLorentzTensor) ![.up, .upL, .upR] ≃
    (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2 where
  toFun v := (finSumFinEquiv.symm (v 0 : Fin 4), v 1, v 2)
  invFun v := fun | 0 => finSumFinEquiv v.1 | 1 => v.2.1 | 2 => v.2.2
  left_inv v := by
    funext x
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Equiv.apply_symm_apply]
    fin_cases x
    <;> rfl
  right_inv v := by
    simp

instance tensorial : TensorSpecies.Tensorial complexLorentzTensor
    ![.up, .upL, .upR] (Fin 1 ⊕ Fin 3 → Matrix (Fin 2) (Fin 2) ℂ) where
  toTensor := LinearEquiv.symm <|
    Equiv.toLinearEquiv
    ((Tensor.basis (S := complexLorentzTensor) ![.up, .upL, .upR]).repr.toEquiv.trans <|
  Finsupp.equivFunOnFinite.trans <|
  (Equiv.piCongrLeft' _ indexEquiv).trans <|
  (Equiv.curry _ _ _).trans <|
  Equiv.piCongrRight fun _ => Equiv.curry _ _ _)
    { map_add := fun x y => by
        simp [Nat.succ_eq_add_one, Nat.reduceAdd, map_add]
        rfl
      map_smul := fun c x => by
        simp [Nat.succ_eq_add_one, Nat.reduceAdd, _root_.map_smul]
        rfl}

lemma toTensor_symm_apply (p : ℂT[.up, .upL, .upR]) :
    (toTensor (self := tensorial)).symm p =
    ((Equiv.piCongrRight fun _ => Equiv.curry _ _ _) <|
    (Equiv.curry _ _ _) <|
    Equiv.piCongrLeft' _ indexEquiv <|
    Finsupp.equivFunOnFinite <|
    (Tensor.basis (S := complexLorentzTensor) _).repr p) := rfl

lemma toTensor_symm_basis (b : (x : Fin (Nat.succ 0).succ.succ) →
    Fin (complexLorentzTensor.repDim (![Color.up, Color.upL, Color.upR] x))) :
    (toTensor (self := tensorial)).symm (Tensor.basis ![Color.up, Color.upL, Color.upR] b) =
    fun μ α β => if b 0 = finSumFinEquiv μ ∧ b 1 = α ∧ b 2 = β then 1 else 0 := by
  rw [toTensor_symm_apply]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Basis.repr_self, Finsupp.equivFunOnFinite_single,
    Equiv.curry_apply, Fin.isValue, cons_val_one, cons_val_zero, cons_val]
  funext μ α β
  simp only [Equiv.piCongrRight_apply, Equiv.curry_apply, Pi.map_apply, Function.curry_apply,
    Equiv.piCongrLeft'_apply, Fin.isValue]
  rw [Pi.single_apply]
  congr
  simp [indexEquiv]
  constructor
  · intro h
    subst h
    simp
  · intro h
    funext x
    fin_cases x
    · simp [h.1]
    · simp [h.2.1]
    · simp [h.2.2]

/-!

## Pauli matrices as a tensor

-/

/-- The Pauli matrices as a tensor `toTensor pauliMatrix` in `ℂT[.up, .upL, .upR]`. -/
scoped[PauliMatrix] notation "σ^^^" => toTensor pauliMatrix

lemma toTensor_basis_expand : σ^^^ =
    Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 0 | 1 => 0 | 2 => 0)
    + Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 0 | 1 => 1 | 2 => 1)
    + Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 1 | 1 => 0 | 2 => 1)
    + Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 1 | 1 => 1 | 2 => 0)
    - I • Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 2 | 1 => 0 | 2 => 1)
    + I • Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 2 | 1 => 1 | 2 => 0)
    + Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 3 | 1 => 0 | 2 => 0)
    - Tensor.basis ![Color.up, Color.upL, Color.upR] (fun | 0 => 3 | 1 => 1 | 2 => 1) := by
  apply toTensor (self := tensorial).symm.injective
  simp [toTensor_symm_basis]
  funext μ α β
  fin_cases μ <;> fin_cases α <;> fin_cases β
  all_goals
    simp
  all_goals
    try rw [if_pos (by decide)]
    try rw [if_neg (by decide)]
    try rw [if_neg (by decide)]
    try rw [if_pos (by decide)]
    simp [pauliMatrix]

open Lorentz in
lemma toTensor_eq_asConsTensor :
    σ^^^ = fromConstTriple PauliMatrix.asConsTensor := by
  symm
  trans fromTripleT PauliMatrix.asTensor
  · rw [fromConstTriple, congrArg fromTripleT PauliMatrix.asConsTensor_apply_one]
  rw [PauliMatrix.asTensor_expand, toTensor_basis_expand]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Equivalence.symm_inverse, Fin.isValue, map_sub,
    map_add, _root_.map_smul]
  rw [show complexContrBasis (Sum.inl 0) = complexContrBasisFin4 0 by {simp}]
  rw [show complexContrBasis (Sum.inr 0) = complexContrBasisFin4 1 by {simp}]
  rw [show complexContrBasis (Sum.inr 1) = complexContrBasisFin4 2 by {simp}]
  rw [show complexContrBasis (Sum.inr 2) = complexContrBasisFin4 3 by {simp}]
  conv_lhs =>
    enter [1, 1, 1, 1, 1, 1, 1]
    rw [← basis_up_eq, ← basis_upL_eq, ← basis_upR_eq]
    rw [fromTripleT_apply_basis]
  conv_lhs =>
    enter [1, 1, 1, 1, 1, 1, 2]
    rw [← basis_up_eq, ← basis_upL_eq, ← basis_upR_eq]
    rw [fromTripleT_apply_basis]
  conv_lhs =>
    enter [1, 1, 1, 1, 1, 2]
    rw [← basis_up_eq, ← basis_upL_eq, ← basis_upR_eq]
    rw [fromTripleT_apply_basis]
  conv_lhs =>
    enter [1, 1, 1, 1, 2]
    rw [← basis_up_eq, ← basis_upL_eq, ← basis_upR_eq]
    rw [fromTripleT_apply_basis]
  conv_lhs =>
    enter [1, 1, 1, 2]
    rw [← basis_up_eq, ← basis_upL_eq, ← basis_upR_eq]
    rw [fromTripleT_apply_basis]
  conv_lhs =>
    enter [1, 1, 2]
    rw [← basis_up_eq, ← basis_upL_eq, ← basis_upR_eq]
    rw [fromTripleT_apply_basis]
  conv_lhs =>
    enter [1, 2]
    rw [← basis_up_eq, ← basis_upL_eq, ← basis_upR_eq]
    rw [fromTripleT_apply_basis]
  conv_lhs =>
    enter [2]
    rw [← basis_up_eq, ← basis_upL_eq, ← basis_upR_eq]
    rw [fromTripleT_apply_basis]
  rfl

lemma toTensor_eq_ofRat : σ^^^ = ofRat (fun b =>
    if b 0 = 0 ∧ b 1 = b 2 then ⟨1, 0⟩ else
    if b 0 = 1 ∧ b 1 ≠ b 2 then ⟨1, 0⟩ else
    if b 0 = 2 ∧ b 1 = 0 ∧ b 2 = 1 then ⟨0, -1⟩ else
    if b 0 = 2 ∧ b 1 = 1 ∧ b 2 = 0 then ⟨0, 1⟩ else
    if b 0 = 3 ∧ b 1 = 0 ∧ b 2 = 0 then ⟨1, 0⟩ else
    if b 0 = 3 ∧ b 1 = 3 ∧ b 2 = 3 then ⟨-1, 0⟩ else 0) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [toTensor_basis_expand]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, cons_val_zero, cons_val_one]
  repeat rw [basis_eq_ofRat]
  simp only [Fin.isValue, map_sub, map_add, _root_.map_smul, Finsupp.coe_sub, Finsupp.coe_add,
    Finsupp.coe_smul, Pi.sub_apply, Pi.add_apply, ofRat_basis_repr_apply, Pi.smul_apply,
    smul_eq_mul, PhysLean.RatComplexNum.I_mul_toComplexNum, mul_ite, ne_eq, cons_val_two,
    Nat.succ_eq_add_one, Nat.reduceAdd]
  simp only [Fin.isValue, ← map_add, ← map_sub]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

@[simp]
lemma smul_eq_self (Λ : SL(2,ℂ)) : Λ • pauliMatrix = pauliMatrix := by
  rw [smul_eq, toTensor_eq_asConsTensor, actionT_fromConstTriple, ← toTensor_eq_asConsTensor]
  simp

@[simp]
lemma toTensor_smul_eq_self (Λ : SL(2,ℂ)) : Λ • σ^^^ = σ^^^ := by
  rw [toTensor_eq_asConsTensor]
  simp

/-!

## Variations of the pauli tensor

-/

/-- The Pauli matrices as the complex Lorentz tensor `σ_μ^α^{dot β}`. -/
abbrev pauliCo : ℂT[.down, .upL, .upR] :=
  permT id (PermCond.auto) {η' | μ ν ⊗ σ^^^ | ν α β}ᵀ

@[inherit_doc pauliCo]
scoped[PauliMatrix] notation "σ_^^" => PauliMatrix.pauliCo

/-- The Pauli matrices as the complex Lorentz tensor `σ_μ_{dot β}_α`. -/
abbrev pauliCoDown : ℂT[.down, .downR, .downL] :=
  permT id (PermCond.auto) {σ_^^ | μ α β ⊗ εR' | β β' ⊗ εL' | α α' }ᵀ

@[inherit_doc pauliCoDown]
scoped[PauliMatrix] notation "σ___" => PauliMatrix.pauliCoDown

/-- The Pauli matrices as the complex Lorentz tensor `σ^μ_{dot β}_α`. -/
abbrev pauliContrDown : ℂT[.up, .downR, .downL] :=
    permT id (PermCond.auto) {σ^^^ | μ α β ⊗ εR' | β β' ⊗ εL' | α α'}ᵀ

@[inherit_doc pauliContrDown]
scoped[PauliMatrix] notation "σ^__" => PauliMatrix.pauliContrDown

/-!

## Different forms
-/
open Lorentz

lemma pauliCo_eq_ofRat : pauliCo = ofRat (fun b =>
    if b 0 = 0 ∧ b 1 = b 2 then ⟨1, 0⟩ else
    if b 0 = 1 ∧ b 1 ≠ b 2 then ⟨-1, 0⟩ else
    if b 0 = 2 ∧ b 1 = 0 ∧ b 2 = 1 then ⟨0, 1⟩ else
    if b 0 = 2 ∧ b 1 = 1 ∧ b 2 = 0 then ⟨0, -1⟩ else
    if b 0 = 3 ∧ b 1 = 0 ∧ b 2 = 0 then ⟨-1, 0⟩ else
    if b 0 = 3 ∧ b 1 = 1 ∧ b 2 = 1 then ⟨1, 0⟩ else ⟨0, 0⟩) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [pauliCo]
  rw [permT_basis_repr_symm_apply]
  rw [contrT_basis_repr_apply]
  simp only [Tensorial.self_toTensor_apply]
  conv_lhs =>
    enter [2, x]
    rw [contr_basis_ratComplexNum]
    rw [prodT_basis_repr_apply]
    simp only [coMetric_eq_ofRat, ofRat_basis_repr_apply, toTensor_eq_ofRat]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  rw [← map_sum PhysLean.RatComplexNum.toComplexNum]
  rw [ofRat_basis_repr_apply]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

lemma pauliCoDown_eq_ofRat : pauliCoDown = ofRat (fun b =>
    if b 0 = 0 ∧ b 1 = b 2 then ⟨1, 0⟩ else
    if b 0 = 1 ∧ b 1 ≠ b 2 then ⟨1, 0⟩ else
    if b 0 = 2 ∧ b 1 = 0 ∧ b 2 = 1 then ⟨0, -1⟩ else
    if b 0 = 2 ∧ b 1 = 1 ∧ b 2 = 0 then ⟨0, 1⟩ else
    if b 0 = 3 ∧ b 1 = 1 ∧ b 2 = 1 then ⟨-1, 0⟩ else
    if b 0 = 3 ∧ b 1 = 0 ∧ b 2 = 0 then ⟨1, 0⟩ else ⟨0, 0⟩) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [pauliCoDown]
  rw [permT_basis_repr_symm_apply]
  rw [contrT_basis_repr_apply]
  simp only [Tensorial.self_toTensor_apply]
  conv_lhs =>
    enter [2, x]
    rw [contr_basis_ratComplexNum]
    rw [prodT_basis_repr_apply]
    rw [contrT_basis_repr_apply]
    simp only [coMetric_eq_ofRat, ofRat_basis_repr_apply,
      altLeftMetric_eq_ofRat]
    enter [1, 1, 2, y]
    rw [contr_basis_ratComplexNum]
    rw [prodT_basis_repr_apply]
    simp only [coMetric_eq_ofRat, ofRat_basis_repr_apply, pauliCo_eq_ofRat,
      altRightMetric_eq_ofRat]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  conv_lhs =>
    enter [2, x]
    rw [← map_sum PhysLean.RatComplexNum.toComplexNum]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  rw [← map_sum PhysLean.RatComplexNum.toComplexNum]
  rw [ofRat_basis_repr_apply]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

lemma pauliContrDown_ofRat : pauliContrDown = ofRat (fun b =>
    if b 0 = 0 ∧ b 1 = b 2 then ⟨1, 0⟩ else
    if b 0 = 1 ∧ b 1 ≠ b 2 then ⟨-1, 0⟩ else
    if b 0 = 2 ∧ b 1 = 0 ∧ b 2 = 1 then ⟨0, 1⟩ else
    if b 0 = 2 ∧ b 1 = 1 ∧ b 2 = 0 then ⟨0, -1⟩ else
    if b 0 = 3 ∧ b 1 = 1 ∧ b 2 = 1 then ⟨1, 0⟩ else
    if b 0 = 3 ∧ b 1 = 0 ∧ b 2 = 0 then ⟨-1, 0⟩ else 0) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [pauliContrDown]
  rw [permT_basis_repr_symm_apply]
  rw [contrT_basis_repr_apply]
  simp only [Tensorial.self_toTensor_apply]
  conv_lhs =>
    enter [2, x]
    rw [contr_basis_ratComplexNum]
    rw [prodT_basis_repr_apply]
    rw [contrT_basis_repr_apply]
    simp only [coMetric_eq_ofRat, ofRat_basis_repr_apply,
      altLeftMetric_eq_ofRat]
    enter [1, 1, 2, y]
    rw [contr_basis_ratComplexNum]
    rw [prodT_basis_repr_apply]
    simp only [coMetric_eq_ofRat,ofRat_basis_repr_apply, toTensor_eq_ofRat,
      altRightMetric_eq_ofRat]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  conv_lhs =>
    enter [2, x]
    rw [← map_sum PhysLean.RatComplexNum.toComplexNum]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  rw [← map_sum PhysLean.RatComplexNum.toComplexNum]
  rw [ofRat_basis_repr_apply]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

/-!

## Group actions

-/

/-- The tensor `pauliCo` is invariant under the action of `SL(2,ℂ)`. -/
lemma smul_pauliCo (g : SL(2,ℂ)) : g • pauliCo = pauliCo := by
  rw [← permT_equivariant, ← contrT_equivariant, ← prodT_equivariant]
  simp only [Tensorial.self_toTensor_apply]
  rw [toTensor_smul_eq_self, actionT_coMetric]
  rfl

set_option maxRecDepth 2000 in
/-- The tensor `pauliCoDown` is invariant under the action of `SL(2,ℂ)`. -/
lemma smul_pauliCoDown (g : SL(2,ℂ)) : g • pauliCoDown = pauliCoDown := by
  rw [← permT_equivariant, ← contrT_equivariant, ← prodT_equivariant,
    ← contrT_equivariant, ← prodT_equivariant]
  simp only [Tensorial.self_toTensor_apply]
  rw [smul_pauliCo, actionT_altLeftMetric, actionT_altRightMetric]
  rfl

/-- The tensor `pauliContrDown` is invariant under the action of `SL(2,ℂ)`. -/
lemma smul_pauliContrDown (g : SL(2,ℂ)) : g • pauliContrDown = pauliContrDown := by
  rw [← permT_equivariant, ← contrT_equivariant, ← prodT_equivariant,
    ← contrT_equivariant, ← prodT_equivariant]
  simp only [Tensorial.self_toTensor_apply]
  rw [toTensor_smul_eq_self, actionT_altLeftMetric, actionT_altRightMetric]
  rfl

end PauliMatrix
