/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Metrics.Basic
public import Physlib.Relativity.PauliMatrices.AsTensor
public import Physlib.Relativity.Tensors.ComplexTensor.Metrics.Basic
/-!

# Pauli matrices as a tensor

-/

@[expose] public section

open Module
open Matrix
open MatrixGroups
open Complex
open TensorProduct
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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
lemma toTensor_basis_expand : σ^^^ =
    Tensor.basis ![Color.up, Color.upL, Color.upR]
      (fun | 0 => (0 : Fin 4) | 1 => (0 : Fin 2) | 2 => (0 : Fin 2))
    + Tensor.basis ![Color.up, Color.upL, Color.upR]
      (fun | 0 => (0 : Fin 4) | 1 => (1 : Fin 2) | 2 => (1 : Fin 2))
    + Tensor.basis ![Color.up, Color.upL, Color.upR]
      (fun | 0 => (1 : Fin 4) | 1 => (0 : Fin 2) | 2 => (1 : Fin 2))
    + Tensor.basis ![Color.up, Color.upL, Color.upR]
      (fun | 0 => (1 : Fin 4) | 1 => (1 : Fin 2) | 2 => (0 : Fin 2))
    - I • Tensor.basis ![Color.up, Color.upL, Color.upR]
      (fun | 0 => (2 : Fin 4) | 1 => (0 : Fin 2) | 2 => (1 : Fin 2))
    + I • Tensor.basis ![Color.up, Color.upL, Color.upR]
      (fun | 0 => (2 : Fin 4) | 1 => (1 : Fin 2) | 2 => (0 : Fin 2))
    + Tensor.basis ![Color.up, Color.upL, Color.upR]
      (fun | 0 => (3 : Fin 4) | 1 => (0 : Fin 2) | 2 => (0 : Fin 2))
    - Tensor.basis ![Color.up, Color.upL, Color.upR]
      (fun | 0 => (3 : Fin 4) | 1 => (1 : Fin 2) | 2 => (1 : Fin 2)) := by
  apply toTensor (self := tensorial).symm.injective
  simp [toTensor_symm_basis]
  funext μ α β
  fin_cases μ <;> fin_cases α <;> fin_cases β
  all_goals
    simp
  all_goals
    try rw [ite_eq_left (by decide)]
    try rw [ite_eq_right (by decide)]
    try rw [ite_eq_right (by decide)]
    try rw [ite_eq_left (by decide)]
    simp [pauliMatrix]

open Lorentz in
lemma toTensor_eq_asConsTensor :
    σ^^^ = fromConstTriple (S := complexLorentzTensor)
      (c1 := Color.up) (c2 := Color.upL) (c3 := Color.upR) PauliMatrix.asConsTensor := by
  symm
  trans fromTripleT PauliMatrix.asTensor
  · rw [fromConstTriple, congrArg fromTripleT PauliMatrix.asConsTensor_apply_one]
  rw [PauliMatrix.asTensor_expand, toTensor_basis_expand]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, map_sub,
    map_add, _root_.map_smul]
  rw [show complexContrBasis (Sum.inl 0) = complexContrBasisFin4 0 by {simp}]
  rw [show complexContrBasis (Sum.inr 0) = complexContrBasisFin4 1 by {simp}]
  rw [show complexContrBasis (Sum.inr 1) = complexContrBasisFin4 2 by {simp}]
  rw [show complexContrBasis (Sum.inr 2) = complexContrBasisFin4 3 by {simp}]
  simp only [fromTripleT_apply_basis]
  rfl

/-- Rational-complex components of the contravariant Pauli four-vector. -/
def pauliContrComponent (mu : Fin 4) (a b : Fin 2) : Physlib.RatComplexNum :=
  if mu.val = 0 ∧ a.val = b.val then ⟨1, 0⟩ else
  if mu.val = 1 ∧ a.val ≠ b.val then ⟨1, 0⟩ else
  if mu.val = 2 ∧ a.val = 0 ∧ b.val = 1 then ⟨0, -1⟩ else
  if mu.val = 2 ∧ a.val = 1 ∧ b.val = 0 then ⟨0, 1⟩ else
  if mu.val = 3 ∧ a.val = 0 ∧ b.val = 0 then ⟨1, 0⟩ else
  if mu.val = 3 ∧ a.val = 1 ∧ b.val = 1 then ⟨-1, 0⟩ else 0

/-- Rational-complex components of the contravariant conjugate Pauli four-vector. -/
def pauliContrDownComponent (mu : Fin 4) (a b : Fin 2) : Physlib.RatComplexNum :=
  if mu.val = 0 ∧ a.val = b.val then ⟨1, 0⟩ else
  if mu.val = 1 ∧ a.val ≠ b.val then ⟨-1, 0⟩ else
  if mu.val = 2 ∧ a.val = 0 ∧ b.val = 1 then ⟨0, 1⟩ else
  if mu.val = 2 ∧ a.val = 1 ∧ b.val = 0 then ⟨0, -1⟩ else
  if mu.val = 3 ∧ a.val = 0 ∧ b.val = 0 then ⟨-1, 0⟩ else
  if mu.val = 3 ∧ a.val = 1 ∧ b.val = 1 then ⟨1, 0⟩ else 0

set_option backward.isDefEq.respectTransparency false in
lemma toTensor_eq_ofRat : σ^^^ = ofRat (fun b =>
    pauliContrComponent (b 0) (b 1) (b 2)) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [toTensor_basis_expand]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue]
  repeat rw [basis_eq_ofRat]
  simp only [Fin.isValue, map_sub, map_add, _root_.map_smul, Finsupp.coe_sub, Finsupp.coe_add,
    Finsupp.coe_smul, Pi.sub_apply, Pi.add_apply, ofRat_basis_repr_apply, Pi.smul_apply,
    smul_eq_mul, Physlib.RatComplexNum.I_mul_toComplexNum, mul_ite,
    Nat.succ_eq_add_one, Nat.reduceAdd]
  simp only [Fin.isValue, ← map_add, ← map_sub]
  apply (Function.Injective.eq_iff Physlib.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

set_option backward.isDefEq.respectTransparency false in
/-- Rational-complex components of `σ^^^` after dualizing its left-handed Weyl index. -/
lemma toTensor_dualLeft_eq_ofRat :
    {σ^^^ | μ τ(α) β}ᵀ =
      ofRat (fun b =>
        ∑ x : Fin 2, pauliContrComponent (b 0) x (b 2) *
          (if x.val = 0 ∧ (b 1).val = 1 then 1 else
            if (b 1).val = 0 ∧ x.val = 1 then -1 else 0)) := by
  let M : ℂT[.downL, .downL] := εL'
  conv_lhs =>
    rw [toTensor_eq_ofRat, toDualMapAtIndex]
    change crossToSlot 1 0 (by rfl) M (ofRat _)
    erw [crossToSlot_eq_crossToEnd, crossToEnd]
    simp only [LinearMap.compr₂_apply, LinearMap.comp_apply]
    dsimp only [M]
    rw [dualLeftMetric_eq_ofRat, prodT_ofRat_ofRat, permT_ofRat, contrT_ofRat,
      permT_ofRat, permT_ofRat]
  congr
  funext b
  decide +revert +kernel

set_option backward.isDefEq.respectTransparency false in
/-- Rational-complex components of `σ^^^` after dualizing both Weyl indices. -/
lemma toTensor_dualWeyl_eq_ofRat :
    {σ^^^ | μ τ(α) τ(β)}ᵀ =
      ofRat (fun b =>
        pauliContrDownComponent (b 0) (b 2) (b 1)) := by
  rw [toTensor_dualLeft_eq_ofRat]
  let M : ℂT[.downR, .downR] := εR'
  conv_lhs =>
    rw [toDualMapAtIndex]
    change crossToSlot 2 0 (by rfl) M (ofRat _)
    erw [crossToSlot_eq_crossToEnd, crossToEnd]
    simp only [LinearMap.compr₂_apply, LinearMap.comp_apply]
    dsimp only [M]
    rw [dualRightMetric_eq_ofRat, prodT_ofRat_ofRat, permT_ofRat, contrT_ofRat,
      permT_ofRat, permT_ofRat]
  congr
  funext b
  decide +revert +kernel

set_option backward.isDefEq.respectTransparency false in
/-- Rational-complex components of `σ^^^` after dualizing its Lorentz index. -/
lemma toTensor_dualLorentz_eq_ofRat :
    {σ^^^ | τ(μ) α β}ᵀ =
      ofRat (fun b => pauliContrDownComponent (b 0) (b 1) (b 2)) := by
  let M : ℂT[.down, .down] := η'
  conv_lhs =>
    rw [toTensor_eq_ofRat, toDualMapAtIndex]
    change crossToSlot 0 0 (by rfl) M (ofRat _)
    erw [crossToSlot_eq_crossToEnd, crossToEnd]
    simp only [LinearMap.compr₂_apply, LinearMap.comp_apply]
    dsimp only [M]
    rw [coMetric_eq_ofRat, prodT_ofRat_ofRat, permT_ofRat, contrT_ofRat,
      permT_ofRat, permT_ofRat]
  congr
  funext b
  decide +revert +kernel

set_option backward.isDefEq.respectTransparency false in
/-- Rational-complex components of `σ^^^` after dualizing its Lorentz and left-handed Weyl
indices. -/
lemma toTensor_dualLorentzLeft_eq_ofRat :
    {σ^^^ | τ(μ) τ(α) β}ᵀ = ofRat (fun b =>
      ∑ x : Fin 2, pauliContrDownComponent (b 0) x (b 2) *
        (if x.val = 0 ∧ (b 1).val = 1 then 1 else
          if (b 1).val = 0 ∧ x.val = 1 then -1 else 0)) := by
  rw [toTensor_dualLorentz_eq_ofRat]
  let M : ℂT[.downL, .downL] := εL'
  conv_lhs =>
    rw [toDualMapAtIndex]
    change crossToSlot 1 0 (by rfl) M (ofRat _)
    erw [crossToSlot_eq_crossToEnd, crossToEnd]
    simp only [LinearMap.compr₂_apply, LinearMap.comp_apply]
    dsimp only [M]
    rw [dualLeftMetric_eq_ofRat, prodT_ofRat_ofRat, permT_ofRat, contrT_ofRat,
      permT_ofRat, permT_ofRat]
  congr
  funext b
  decide +revert +kernel

set_option backward.isDefEq.respectTransparency false in
/-- Rational-complex components of `σ^^^` after dualizing all three indices. -/
lemma toTensor_dualAll_eq_ofRat :
    {σ^^^ | τ(μ) τ(α) τ(β)}ᵀ =
      ofRat (fun b => pauliContrComponent (b 0) (b 2) (b 1)) := by
  rw [toTensor_dualLorentzLeft_eq_ofRat]
  let M : ℂT[.downR, .downR] := εR'
  conv_lhs =>
    rw [toDualMapAtIndex]
    change crossToSlot 2 0 (by rfl) M (ofRat _)
    erw [crossToSlot_eq_crossToEnd, crossToEnd]
    simp only [LinearMap.compr₂_apply, LinearMap.comp_apply]
    dsimp only [M]
    rw [dualRightMetric_eq_ofRat, prodT_ofRat_ofRat, permT_ofRat, contrT_ofRat,
      permT_ofRat, permT_ofRat]
  congr
  funext b
  decide +revert +kernel

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma smul_eq_self (Λ : SL(2,ℂ)) : Λ • pauliMatrix = pauliMatrix := by
  rw [smul_eq, toTensor_eq_asConsTensor, actionT_fromConstTriple, ← toTensor_eq_asConsTensor]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma toTensor_smul_eq_self (Λ : SL(2,ℂ)) : Λ • σ^^^ = σ^^^ := by
  rw [toTensor_eq_asConsTensor]
  simp

/-!

## Variations of the pauli tensor

-/

/-- The Pauli matrices as the complex Lorentz tensor `σ_μ^α^{dot β}`. -/
abbrev pauliCo : ℂT[.down, .upL, .upR] :=
  permT id (IsReindexing.auto) {η' | μ ν ⊗ σ^^^ | ν α β}ᵀ

@[inherit_doc pauliCo]
scoped[PauliMatrix] notation "σ_^^" => PauliMatrix.pauliCo

/-- The Pauli matrices as the complex Lorentz tensor `σ_μ_{dot β}_α`. -/
abbrev pauliCoDown : ℂT[.down, .downR, .downL] :=
  permT id (IsReindexing.auto) {σ_^^ | μ α β ⊗ εR' | β β' ⊗ εL' | α α' }ᵀ

@[inherit_doc pauliCoDown]
scoped[PauliMatrix] notation "σ___" => PauliMatrix.pauliCoDown

/-- The Pauli matrices as the complex Lorentz tensor `σ^μ_{dot β}_α`. -/
abbrev pauliContrDown : ℂT[.up, .downR, .downL] :=
    permT id (IsReindexing.auto) {σ^^^ | μ α β ⊗ εR' | β β' ⊗ εL' | α α'}ᵀ

@[inherit_doc pauliContrDown]
scoped[PauliMatrix] notation "σ^__" => PauliMatrix.pauliContrDown

/-!

## Different forms
-/
open Lorentz

set_option backward.isDefEq.respectTransparency false in
lemma pauliCo_eq_ofRat : pauliCo = ofRat (fun b =>
    pauliContrDownComponent (b 0) (b 1) (b 2)) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [pauliCo]
  rw [permT_basis_repr_symm_apply]
  rw [contrT_basis_repr_apply]
  conv_lhs =>
    enter [2, x]
    rw [contr_basis_ratComplexNum]
    rw [prodT_basis_repr_apply]
    simp only [coMetric_eq_ofRat, ofRat_basis_repr_apply, toTensor_eq_ofRat]
    rw [← Physlib.RatComplexNum.toComplexNum.map_mul]
    rw [← Physlib.RatComplexNum.toComplexNum.map_mul]
  rw [← map_sum Physlib.RatComplexNum.toComplexNum]
  rw [ofRat_basis_repr_apply]
  apply (Function.Injective.eq_iff Physlib.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

set_option backward.isDefEq.respectTransparency false in
lemma pauliCoDown_eq_ofRat : pauliCoDown = ofRat (fun b =>
    pauliContrComponent (b 0) (b 1) (b 2)) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [pauliCoDown]
  rw [permT_basis_repr_symm_apply]
  rw [contrT_basis_repr_apply]
  conv_lhs =>
    enter [2, x]
    rw [contr_basis_ratComplexNum]
    rw [prodT_basis_repr_apply]
    rw [contrT_basis_repr_apply]
    simp only [coMetric_eq_ofRat, ofRat_basis_repr_apply,
      dualLeftMetric_eq_ofRat]
    enter [1, 1, 2, y]
    rw [contr_basis_ratComplexNum]
    rw [prodT_basis_repr_apply]
    simp only [coMetric_eq_ofRat, ofRat_basis_repr_apply, pauliCo_eq_ofRat,
      dualRightMetric_eq_ofRat]
    rw [← Physlib.RatComplexNum.toComplexNum.map_mul]
    rw [← Physlib.RatComplexNum.toComplexNum.map_mul]
  conv_lhs =>
    enter [2, x]
    rw [← map_sum Physlib.RatComplexNum.toComplexNum]
    rw [← Physlib.RatComplexNum.toComplexNum.map_mul]
    rw [← Physlib.RatComplexNum.toComplexNum.map_mul]
  rw [← map_sum Physlib.RatComplexNum.toComplexNum]
  rw [ofRat_basis_repr_apply]
  apply (Function.Injective.eq_iff Physlib.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

set_option backward.isDefEq.respectTransparency false in
lemma pauliContrDown_ofRat : pauliContrDown = ofRat (fun b =>
    pauliContrDownComponent (b 0) (b 1) (b 2)) := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [pauliContrDown]
  rw [permT_basis_repr_symm_apply]
  rw [contrT_basis_repr_apply]
  conv_lhs =>
    enter [2, x]
    rw [contr_basis_ratComplexNum]
    rw [prodT_basis_repr_apply]
    rw [contrT_basis_repr_apply]
    simp only [coMetric_eq_ofRat, ofRat_basis_repr_apply,
      dualLeftMetric_eq_ofRat]
    enter [1, 1, 2, y]
    rw [contr_basis_ratComplexNum]
    rw [prodT_basis_repr_apply]
    simp only [coMetric_eq_ofRat,ofRat_basis_repr_apply, toTensor_eq_ofRat,
      dualRightMetric_eq_ofRat]
    rw [← Physlib.RatComplexNum.toComplexNum.map_mul]
    rw [← Physlib.RatComplexNum.toComplexNum.map_mul]
  conv_lhs =>
    enter [2, x]
    rw [← map_sum Physlib.RatComplexNum.toComplexNum]
    rw [← Physlib.RatComplexNum.toComplexNum.map_mul]
    rw [← Physlib.RatComplexNum.toComplexNum.map_mul]
  rw [← map_sum Physlib.RatComplexNum.toComplexNum]
  rw [ofRat_basis_repr_apply]
  apply (Function.Injective.eq_iff Physlib.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

/-!

## Index dualization

-/

/-- Dualizing both Weyl indices of `σ^^^` gives `σ^__`. -/
lemma toTensor_dualWeyl_eq_pauliContrDown :
    ({σ^^^ | μ τ(α) τ(β) = σ^__ | μ β α}ᵀ : Prop) := by
  rw [toTensor_dualWeyl_eq_ofRat]
  rw [pauliContrDown_ofRat, permT_ofRat]
  congr

/-- Dualizing all three indices of `σ^^^` gives `σ___`. -/
lemma toTensor_dualAll_eq_pauliCoDown :
    ({σ^^^ | τ(μ) τ(α) τ(β) = σ___ | μ β α}ᵀ : Prop) := by
  rw [toTensor_dualAll_eq_ofRat]
  rw [pauliCoDown_eq_ofRat, permT_ofRat]
  congr

set_option backward.isDefEq.respectTransparency false in
/-- Lowering the Lorentz index of `σ^^^` with `τ` gives `σ_^^`. -/
lemma pauliDual_eq_pauliCo :
    ({σ^^^ | τ(μ) α β = σ_^^ | μ α β}ᵀ : Prop) := by
  rw [toTensor_dualLorentz_eq_ofRat, pauliCo_eq_ofRat, permT_ofRat]
  congr

set_option backward.isDefEq.respectTransparency false in
/-- Lowering the Lorentz index of `σ^__` with `τ` gives `σ___`. -/
lemma pauliContrDownDual_eq_pauliCoDown :
    ({σ^__ | τ(μ) β α = σ___ | μ β α}ᵀ : Prop) := by
  let h : IsReindexing ![Color.down, Color.downR, Color.downL]
      (Function.update ![Color.up, Color.downR, Color.downL] 0
        (![Color.down, Color.down] (Fin.succAbove 0 0))) id :=
    IsReindexing.auto
  have hDual :
      (toDualMapAtIndex (S := complexLorentzTensor) 0) pauliContrDown =
        permT (id : Fin 3 → Fin 3) h pauliCoDown := by
    change (toDualMapAtIndex (S := complexLorentzTensor) 0) pauliContrDown =
      permT id h pauliCoDown
    conv_lhs =>
      rw [pauliContrDown_ofRat]
      rw [toDualMapAtIndex]
      change crossToSlot (S := complexLorentzTensor) 0 0 rfl η' (ofRat _)
      rw [crossToSlot_eq_crossToEnd, crossToEnd]
      simp only [LinearMap.compr₂_apply, LinearMap.comp_apply]
      rw [coMetric_eq_ofRat]
      rw [prodT_ofRat_ofRat, permT_ofRat, contrT_ofRat, permT_ofRat, permT_ofRat]
    conv_rhs =>
      rw [pauliCoDown_eq_ofRat]
    apply (Tensor.basis _).repr.injective
    ext b
    conv_rhs =>
      rw [permT_basis_repr_symm_apply h]
      rw [ofRat_basis_repr_apply]
    conv_lhs =>
      rw [ofRat_basis_repr_apply]
    apply (Function.Injective.eq_iff Physlib.RatComplexNum.toComplexNum_injective).mpr
    revert b
    decide +kernel
  rw [hDual]
  apply permT_congr
  · decide
  · rfl

/-!

## Group actions

-/

set_option backward.isDefEq.respectTransparency false in
/-- The tensor `pauliCo` is invariant under the action of `SL(2,ℂ)`. -/
lemma smul_pauliCo (g : SL(2,ℂ)) : g • pauliCo = pauliCo := by
  rw [← permT_equivariant, ← contrT_equivariant, ← prodT_equivariant]
  rw [toTensor_smul_eq_self, actionT_coMetric]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2000 in
/-- The tensor `pauliCoDown` is invariant under the action of `SL(2,ℂ)`. -/
lemma smul_pauliCoDown (g : SL(2,ℂ)) : g • pauliCoDown = pauliCoDown := by
  rw [← permT_equivariant, ← contrT_equivariant, ← prodT_equivariant,
    ← contrT_equivariant, ← prodT_equivariant]
  rw [smul_pauliCo, actionT_dualLeftMetric, actionT_dualRightMetric]

set_option backward.isDefEq.respectTransparency false in
/-- The tensor `pauliContrDown` is invariant under the action of `SL(2,ℂ)`. -/
lemma smul_pauliContrDown (g : SL(2,ℂ)) : g • pauliContrDown = pauliContrDown := by
  rw [← permT_equivariant, ← contrT_equivariant, ← prodT_equivariant,
    ← contrT_equivariant, ← prodT_equivariant]
  rw [toTensor_smul_eq_self, actionT_dualLeftMetric, actionT_dualRightMetric]

end PauliMatrix
