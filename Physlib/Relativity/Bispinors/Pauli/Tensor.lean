/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman, Joseph Tooby-Smith, Andrea Pari
-/
module

public import Physlib.Relativity.Bispinors.Pauli.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Species
public import Physlib.Mathematics.ForMathlib.FiniteDimensional
/-!

# The Pauli matrices as a complex Lorentz tensor

The invariant tensor `σT^{μαβ̇}` of `SL(2, ℂ)`, its lowered forms, and its contraction identities.

## i. Overview

The Pauli matrices `σ^μ`, with `σ^0 = 1`, are a tensor with a vector index and a left- and a
right-handed Weyl index, `pauliTensor : ℂT[up, upL, upR]`. All three indices are upper, and the
components are `σT^{μαβ̇} = pauliMatrix μ α β`. Index heights in this file are those of the
colors: the numbers that the literature writes `σ^μ_{αβ̇}` sit here at upper Weyl indices. It is
the tensor of `ComplexVector.pauliVal` in `ComplexVector ⊗ (LeftHandedWeyl ⊗ RightHandedWeyl)`,
so it is invariant under `SL(2, ℂ)` because `ComplexVector.pauli` is an intertwining map.

The conventions are those of Dreiner, Haber and Martin: `η = diag(1, -1, -1, -1)`, and `ε^12 = 1`,
`ε_12 = -1` (`complexLorentz.formEntries`).

The lowered forms are written with `τ` in index notation, such as `{pauliTensor | τ(μ) α β}ᵀ` for
`σT_μ^{αβ̇}`. Lowering contracts the second index of `η` or `ε` (`Species.toDual`), so
`σT_μ^{αβ̇} = η_μν σT^{ναβ̇} = η_μμ σT^{μαβ̇}`. With both Weyl indices lowered,
`{pauliTensor | μ τ(α) τ(β)}ᵀ` is `σT^μ_{αβ̇}`: with rows `β̇` and columns `α` it is the matrix
`σ̄^μ = η_μμ σ^μ = (1, -σ⃗)`. Lowering both indices of a matrix with `ε` gives its adjugate,
transposed, and `adj σ^μ = σ̄^μ`, so the components of the lowered forms are matrix identities.

One identity is read off from the Pauli matrices, the trace identity `pauliCoDown_trace_pauliCo`,
`tr(σ̄_μ σ_ν) = 2 η_μν`: its components are the matrix traces of
`PauliMatrix.trace_pauliMatrix_mul_minkowskiMatrix_smul_pauliMatrix`. The others are derived from
it at tensor level, mostly by `tensor_regroup using` an identity proved before. The trace
identities `pauliCoDown_trace_pauliCo` and `pauliCo_trace_pauliCoDown` reproduce
`PauliMatrix.pauliCoDown_trace_pauliCo` and `PauliMatrix.pauliCo_trace_pauliCoDown` with proofs at
tensor level. Contracting with
`σ` gives a map `vectorToBispinor` from tensors with a vector index to tensors with two Weyl indices
and a map `bispinorToVector` back. The trace identity says that going there and back is `2`. Both
spaces have dimension `16`, so going back and there is `2` as well, which is the Fierz identity
`σT_ν^{αβ̇} σT^{να'β̇'} = 2 ε^{αα'} ε^{β̇β̇'}`. An upper Weyl index of `σT` is a lower one in the
literature, so this is `σ^μ_{αβ̇} σ_{μα'β̇'} = 2 ε_{αα'} ε_{β̇β̇'}`, where the sign of each `ε`
changes and the two signs cancel.
The anticommutators follow from the trace identities and the Schouten identity of `ε`.

## ii. Key results

- `complexLorentz.pauliTensor` : the Pauli matrices as a tensor `σT^{μαβ̇}`.
- `complexLorentz.tensorBasis_repr_pauliTensor` : its components are the Pauli matrices.
- `complexLorentz.pauliTensor_invariant` : `σ` is an invariant tensor of `SL(2, ℂ)`.
- `complexLorentz.tensorBasis_repr_pauliTensor_down` and
  `complexLorentz.tensorBasis_repr_pauliTensor_downAll` : the components of the lowered forms.
- `complexLorentz.pauliCoDown_trace_pauliCo`, `complexLorentz.pauliCo_trace_pauliCoDown`,
  `complexLorentz.pauliContr_trace_pauliContrDown` and
  `complexLorentz.pauliContrDown_trace_pauliContr` : the trace identities
  `tr(σ̄_μ σ_ν) = tr(σ_μ σ̄_ν) = 2 η_μν` and `tr(σ^μ σ̄^ν) = tr(σ̄^μ σ^ν) = 2 η^μν`, and
  `complexLorentz.pauliContrDown_trace_pauliCo` : the mixed trace `tr(σ̄^μ σ_ν) = 2 δ^μ_ν`.
- `complexLorentz.vectorToBispinor_bispinorToVector` : the maps `vectorToBispinor` and
  `bispinorToVector` are inverse up to `2`.
- `complexLorentz.pauliCo_contr_pauliContr` : the Fierz identity
  `σT_ν^{αβ̇} σT^{να'β̇'} = 2 ε^{αα'} ε^{β̇β̇'}`.
- `complexLorentz.pauliContr_mul_pauliContrDown_add` and
  `complexLorentz.pauliContrDown_pauliContr_mul_add` : the anticommutators
  `σ^μ σ̄^ν + σ^ν σ̄^μ = 2 η^μν` and `σ̄^μ σ^ν + σ̄^ν σ^μ = 2 η^μν`.

## iii. Table of contents

- A. The Pauli tensor
- B. Lowered indices
- C. Contraction identities
  - C.1. Traces
  - C.2. The Fierz identity
  - C.3. The anticommutators

## iv. References

* Dreiner, Haber and Martin, *Two-component spinor techniques and Feynman rules for quantum
  field theory and supersymmetry*, arXiv:0812.1594, in the conventions
  `g = diag(+1, -1, -1, -1)`. [ref: Dreiner:2008tw]

-/

@[expose] public section

open TensorProduct Fermion Lorentz MatrixGroups
open PauliMatrix (pauliMatrix)

namespace Tensor.complexLorentz

/-!

## A. The Pauli tensor

-/

/-- The Pauli matrices as the complex Lorentz tensor `σT^{μαβ̇}`, the tensor of
`ComplexVector.pauliVal`. -/
noncomputable def pauliTensor : ℂT[up, upL, upR] := {ComplexVector.pauliVal | μ α β}ᵀ

/-- `σT` is the Pauli tensor `pauliTensor`, to be distinguished from the Pauli matrices `σ`. -/
scoped[Tensor.complexLorentz] notation "σT" => pauliTensor

/-- The components of `σT^{μαβ̇}` are the entries of the Pauli matrices. -/
lemma tensorBasis_repr_pauliTensor (μ : Π i, Idx (![up, upL, upR] i).kind) :
    (complexLorentz.tensorBasis _).repr pauliTensor μ = pauliMatrix (μ 0) (μ 1) (μ 2) := by
  rw [pauliTensor, Species.tensorBasis_repr_reindex]
  -- The components of `pauliVal` in the product basis `e_μ ⊗ e_α ⊗ e_β̇` are `pauliVal_repr`.
  exact (Tensorial.tensorBasis_repr_toTensor_prod (S := complexLorentz) (c₁ := ![up])
    ComplexVector.basis (LeftHandedWeyl.basis.tensorProduct RightHandedWeyl.basis) (· 0)
    (fun ν => (ν (.inl 0), ν (.inr 0)))
    (Tensorial.tensorBasis_repr_toTensor_ofIndexSpace (S := complexLorentz) up)
    tensorBasis_repr_toTensor_leftRight _ _).trans (ComplexVector.pauliVal_repr _ _ _)

/-- `σT^{μαβ̇}` is an invariant tensor of `SL(2, ℂ)`, `g • σT = σT`. -/
lemma pauliTensor_invariant (g : SL(2, ℂ)) : g • pauliTensor = pauliTensor := by
  rw [pauliTensor, ← Species.equiv_smul, ← Tensorial.toTensor_rep, ← ComplexVector.pauli_apply_one]
  exact congrArg _ (congrArg _ (ComplexVector.pauli.map_invariant (v := 1) rfl))

/-!

## B. Lowered indices

-/

/-- The components of `σT_μ^{αβ̇} = η_μμ σT^{μαβ̇}`. -/
lemma tensorBasis_repr_pauliTensor_down (μ : Π i, Idx (![down, upL, upR] i).kind) :
    (complexLorentz.tensorBasis _).repr {pauliTensor | τ(ν) α β}ᵀ μ =
      minkowskiMatrix (μ 0) (μ 0) * pauliMatrix (μ 0) (μ 1) (μ 2) := by
  tensor_components [Species.tensorBasis_repr_toDualAt, formMatrix_apply,
    tensorBasis_repr_pauliTensor]
  -- Only the diagonal entry `η_μμ` of `η` contributes.
  exact Fintype.sum_eq_single _ fun x hx => by
    simp [formEntries, minkowskiMatrix.off_diag_zero (Ne.symm hx)]

/-- The components of `σT_{μαβ̇}`, with all three indices lowered, are the entries of `σ^μ` at the
row `β̇` and the column `α`. Lowering `μ` gives `σ̄^μ = η_μμ σ^μ`, and lowering both Weyl indices
takes it to its adjugate, transposed, with `adj σ̄^μ = σ^μ`. -/
lemma tensorBasis_repr_pauliTensor_downAll
    (μ : Π i, Idx (![down, downL, downR] i).kind) :
    (complexLorentz.tensorBasis _).repr {pauliTensor | τ(ν) τ(α) τ(β)}ᵀ μ =
      pauliMatrix (μ 0) (μ 2) (μ 1) := by
  -- `↓` unfolds the lowered vector index by `tensorBasis_repr_pauliTensor_down` first.
  tensor_components [Species.tensorBasis_repr_toDualAt, formMatrix_apply,
    ↓tensorBasis_repr_pauliTensor_down]
  exact (sum_metricRaw_mul_sum_metricRaw_mul _ _ _).trans
    (congrFun₂ (PauliMatrix.adjugate_minkowskiMatrix_smul_pauliMatrix _) _ _)

/-!

## C. Contraction identities

The trace identity `pauliCoDown_trace_pauliCo` is proved in components, from the trace identity
of the Pauli matrices. The other identities are derived from it at tensor level: the Fierz
identity by reading the trace identity as `bispinorToVector ∘ vectorToBispinor = 2`, and the
anticommutators by the Schouten identity of `ε`.

### C.1. Traces

-/

/-- The trace identity `tr(σ̄_μ σ_ν) = 2 η_μν`, as `σT_{μαβ̇} σT_ν^{αβ̇} = 2 η_μν`. -/
lemma pauliCoDown_trace_pauliCo :
    {pauliTensor | τ(μ) τ(α) τ(β) ⊗ pauliTensor | τ(ν) α β = (2 : ℂ) • η' | μ ν}ᵀ := by
  tensor_components [tensorBasis_repr_pauliTensor_downAll, tensorBasis_repr_pauliTensor_down,
    tensorBasis_repr_formTensor_vec .down]
  -- The components are `tr(σ^μᵀ σ̄^νᵀ) = tr(σ^μ σ̄^ν)`, written out as a double sum.
  exact (Matrix.trace_transpose_mul _ _).trans
    (PauliMatrix.trace_pauliMatrix_mul_minkowskiMatrix_smul_pauliMatrix _ _)

/-- The trace identity `tr(σ_μ σ̄_ν) = 2 η_μν`, as `σT_μ^{αβ̇} σT_{ναβ̇} = 2 η_μν`. -/
lemma pauliCo_trace_pauliCoDown :
    {pauliTensor | τ(μ) α β ⊗ pauliTensor | τ(ν) τ(α) τ(β) = (2 : ℂ) • η' | μ ν}ᵀ := by
  tensor_regroup using pauliCoDown_trace_pauliCo

/-- The mixed trace identity `tr(σ̄^μ σ_ν) = 2 δ^μ_ν`, as `σT^μ_{αβ̇} σT_ν^{αβ̇} = 2 δ^μ_ν`. -/
lemma pauliContrDown_trace_pauliCo :
    {pauliTensor | μ τ(α) τ(β) ⊗ pauliTensor | τ(ν) α β = (2 : ℂ) • δ' | ν μ}ᵀ := by
  have h : {pauliTensor | μ τ(α) τ(β) ⊗ pauliTensor | τ(ν) α β =
      {pauliTensor | τ(ρ) τ(α) τ(β) ⊗ pauliTensor | τ(ν) α β}ᵀ | ρ ν ⊗ η | μ ρ}ᵀ := by
    tensor_regroup
  rw [h, pauliCoDown_trace_pauliCo]
  tensor_regroup

/-!

### C.2. The Fierz identity

-/

/-- `p ↦ σT_μ^{αβ̇} p^{μα'β̇'}`, from a tensor with a vector index to one with two Weyl indices.
On a vector, with no `α'β̇'`, it is the bispinor `p^{αβ̇}` of `p^μ`. -/
noncomputable def vectorToBispinor : ℂT[up, upL, upR] →ₗ[ℂ] ℂT[upL, upR, upL, upR] where
  toFun p := {pauliTensor | τ(μ) α β ⊗ p | μ α' β'}ᵀ
  map_add' p q := by simp only [tmul_add, map_add]
  map_smul' r p := by simp only [tmul_smul, map_smul, RingHom.id_apply]

/-- `X ↦ σT^μ_{αβ̇} X^{αβ̇α'β̇'}`, from a tensor with two Weyl indices to one with a vector
index, the inverse of `vectorToBispinor` up to `2`. -/
noncomputable def bispinorToVector : ℂT[upL, upR, upL, upR] →ₗ[ℂ] ℂT[up, upL, upR] where
  toFun X := {pauliTensor | μ τ(α) τ(β) ⊗ X | α β α' β'}ᵀ
  map_add' X Y := by simp only [tmul_add, map_add]
  map_smul' r X := by simp only [tmul_smul, map_smul, RingHom.id_apply]

/-- `bispinorToVector ∘ vectorToBispinor = 2`, by the trace identity
`σT^μ_{αβ̇} σT_ν^{αβ̇} = 2 δ_ν^μ`. -/
lemma bispinorToVector_vectorToBispinor (p : ℂT[up, upL, upR]) :
    bispinorToVector (vectorToBispinor p) = (2 : ℂ) • p := by
  simp only [vectorToBispinor, bispinorToVector, LinearMap.coe_mk, AddHom.coe_mk]
  tensor_regroup using pauliContrDown_trace_pauliCo

/-- `vectorToBispinor ∘ bispinorToVector = 2`. -/
lemma vectorToBispinor_bispinorToVector (X : ℂT[upL, upR, upL, upR]) :
    vectorToBispinor (bispinorToVector X) = (2 : ℂ) • X :=
  LinearMap.comp_apply_eq_smul_of_comp_apply_eq_smul_of_finrank_eq
    (by rw [Species.finrank_tensor, Species.finrank_tensor]; rfl) two_ne_zero
    bispinorToVector_vectorToBispinor X

/-- The Fierz identity `σT_ν^{αβ̇} σT^{να'β̇'} = 2 ε^{αα'} ε^{β̇β̇'}`. -/
lemma pauliCo_contr_pauliContr :
    {pauliTensor | τ(ν) α β ⊗ pauliTensor | ν α' β' =
      (2 : ℂ) • {εL | α α' ⊗ εR | β β'}ᵀ | α α' β β'}ᵀ := by
  rw [map_smul, ← vectorToBispinor_bispinorToVector]
  refine congrArg vectorToBispinor ?_
  simp only [bispinorToVector, LinearMap.coe_mk, AddHom.coe_mk]
  -- Raising with `ε` contracts its second index, so both forms are swapped, with signs that cancel.
  tensor_regroup using formTensor_upL_antisymm, formTensor_upR_antisymm

/-!

### C.3. The anticommutators

A matrix product contracts the column of the first factor with the row of the second, so
`(σ^μ σ̄^ν)_{αα'}` is `σT^{μαβ̇} σT^ν_{α'β̇}`, summed over `β̇`.

-/

/-- The trace identity `tr(σ^μ σ̄^ν) = 2 η^μν`, as `σT^{μαβ̇} σT^ν_{αβ̇} = 2 η^μν`. -/
lemma pauliContr_trace_pauliContrDown :
    {pauliTensor | μ α β ⊗ pauliTensor | ν τ(α) τ(β) = (2 : ℂ) • η | μ ν}ᵀ := by
  have h : {pauliTensor | μ α β ⊗ pauliTensor | ν τ(α) τ(β) =
      {pauliTensor | ν τ(α) τ(β) ⊗ pauliTensor | τ(ρ) α β}ᵀ | ν ρ ⊗ η | μ ρ}ᵀ := by
    tensor_regroup
  rw [h, pauliContrDown_trace_pauliCo]
  tensor_regroup

/-- The trace identity `tr(σ̄^μ σ^ν) = 2 η^μν`, as `σT^μ_{αβ̇} σT^{ναβ̇} = 2 η^μν`. -/
lemma pauliContrDown_trace_pauliContr :
    {pauliTensor | μ τ(α) τ(β) ⊗ pauliTensor | ν α β = (2 : ℂ) • η | μ ν}ᵀ := by
  tensor_regroup using pauliContr_trace_pauliContrDown

/-- `σT^{μρβ̇} σT^{νγδ̇} ε_{β̇δ̇} (ε_{ργ} δ^α_α') = 2 η^μν δ^α_α'`, the trace identity
`pauliContr_trace_pauliContrDown` with the lowerings written as contractions with `ε`. -/
lemma pauliContr_pauliContr_eps_epsL_deltaL :
    {pauliTensor | μ r β ⊗ pauliTensor | ν g d ⊗ εR' | β d ⊗
      {εL' | r g ⊗ δL | α α'}ᵀ | r g α α' = (2 : ℂ) • {η | μ ν ⊗ δL | α α'}ᵀ | μ ν α α'}ᵀ := by
  tensor_regroup using pauliContr_trace_pauliContrDown

/-- The anticommutator `σ^μ σ̄^ν + σ^ν σ̄^μ = 2 η^μν`, as
`σT^{μαβ̇} σT^ν_{α'β̇} + σT^{ναβ̇} σT^μ_{α'β̇} = 2 η^μν δ^α_α'`. The Schouten identity splits
`ε_ργ δ^α_α'` in `pauliContr_pauliContr_eps_epsL_deltaL` into the two terms. -/
lemma pauliContr_mul_pauliContrDown_add :
    {pauliTensor | μ α β ⊗ pauliTensor | ν τ(α') τ(β) +
      pauliTensor | ν α β ⊗ pauliTensor | μ τ(α') τ(β) =
      (2 : ℂ) • {η | μ ν ⊗ δL | α α'}ᵀ | μ ν α α'}ᵀ := by
  rw [← pauliContr_pauliContr_eps_epsL_deltaL, schouten_downL]
  tensor_regroup

/-- `σT^{μγδ̇} σT^{ναρ̇} ε_{αγ} (ε_{ρ̇δ̇} δ_β̇^β̇') = 2 η^μν δ_β̇^β̇'`, the trace identity
`pauliContrDown_trace_pauliContr` with the lowerings written as contractions with `ε`. -/
lemma pauliContr_pauliContr_eps_epsR_deltaR :
    {pauliTensor | μ g d ⊗ pauliTensor | ν a r ⊗ εL' | a g ⊗
      {εR' | r d ⊗ δR' | β β'}ᵀ | r d β β' = (2 : ℂ) • {η | μ ν ⊗ δR' | β β'}ᵀ | μ ν β β'}ᵀ := by
  tensor_regroup using pauliContrDown_trace_pauliContr

/-- The anticommutator `σ̄^μ σ^ν + σ̄^ν σ^μ = 2 η^μν`, as
`σT^μ_{αβ̇} σT^{ναβ̇'} + σT^ν_{αβ̇} σT^{μαβ̇'} = 2 η^μν δ_β̇^β̇'`. The Schouten identity splits
`ε_ρ̇δ̇ δ_β̇^β̇'` in `pauliContr_pauliContr_eps_epsR_deltaR` into the two terms. -/
lemma pauliContrDown_pauliContr_mul_add :
    {pauliTensor | μ τ(α) τ(β) ⊗ pauliTensor | ν α β' +
      pauliTensor | ν τ(α) τ(β) ⊗ pauliTensor | μ α β' =
      (2 : ℂ) • {η | μ ν ⊗ δR' | β β'}ᵀ | μ ν β β'}ᵀ := by
  rw [← pauliContr_pauliContr_eps_epsR_deltaR, schouten_downR]
  tensor_regroup

end Tensor.complexLorentz
