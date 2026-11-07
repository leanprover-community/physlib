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

The lowered forms are written with `↓` in index notation, such as `{pauliTensor | ↓μ α β}ᵀ` for
`σT_μ^{αβ̇}`. Lowering contracts the first index of `η` or `ε` (`Species.toDual`), so
`σT_μ^{αβ̇} = η_μμ σT^{μαβ̇}`. With both Weyl indices lowered, `{pauliTensor | μ ↓α ↓β}ᵀ` is
`σT^μ_{αβ̇}`: with rows `β̇` and columns `α` it is the matrix `σ̄^μ = η_μμ σ^μ = (1, -σ⃗)`.
Lowering both indices of a matrix with `ε` gives its adjugate, transposed, and
`adj σ^μ = σ̄^μ`, so the components of the lowered forms are matrix identities.

One identity is read off from the Pauli matrices, the trace identity `pauliCoDown_trace_pauliCo`,
`tr(σ̄_μ σ_ν) = 2 η_μν`: its components are the matrix traces of
`PauliMatrix.trace_pauliMatrix_mul_minkowskiMatrix_smul_pauliMatrix`. The others are derived from
it at tensor level, by `tensor_regroup` and `tensor_slots`. The Fierz identity reads the trace
identity as `B ∘ A = 2` for the maps `pauliA` and `pauliB` between tensors with a vector index
and tensors with two Weyl indices. Both spaces have dimension `16`, so `A ∘ B = 2` as well, which
is the Fierz identity. The anticommutators follow from the trace identities and the Schouten
identity of `ε`.

## ii. Key results

- `complexLorentz.pauliTensor` : the Pauli matrices as a tensor `σT^{μαβ̇}`.
- `complexLorentz.tensorBasis_repr_pauliTensor` : its components are the Pauli matrices.
- `complexLorentz.pauliTensor_invariant` : `σ` is an invariant tensor of `SL(2, ℂ)`.
- `complexLorentz.pauliCoDown_trace_pauliCo`, `complexLorentz.pauliContr_trace_pauliContrDown`
  and `complexLorentz.pauliContrDown_trace_pauliContr` : the trace identities
  `tr(σ̄_μ σ_ν) = 2 η_μν` and `tr(σ^μ σ̄^ν) = tr(σ̄^μ σ^ν) = 2 η^μν`.
- `complexLorentz.pauliA_pauliB` : the maps `pauliA` and `pauliB` are inverse up to `2`.
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

namespace Tensors.complexLorentz

/-!

## A. The Pauli tensor

-/

/-- The Pauli matrices as the complex Lorentz tensor `σT^{μαβ̇}`, the tensor of
`ComplexVector.pauliVal`. -/
noncomputable def pauliTensor : ℂT[up, upL, upR] := {ComplexVector.pauliVal | μ α β}ᵀ

/-- `σT` is the Pauli tensor `pauliTensor`, to be distinguished from the Pauli matrices `σ`. -/
scoped[Tensors.complexLorentz] notation "σT" => pauliTensor

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
    (complexLorentz.tensorBasis _).repr {pauliTensor | ↓ν α β}ᵀ μ =
      minkowskiMatrix (μ 0) (μ 0) * pauliMatrix (μ 0) (μ 1) (μ 2) := by
  tensor_components [Species.tensorBasis_repr_toDualAt, formMatrix_apply,
    tensorBasis_repr_pauliTensor]
  -- Only the diagonal entry `η_μμ` of `η` contributes.
  exact Fintype.sum_eq_single _ fun x hx => by simp [formEntries, minkowskiMatrix.off_diag_zero hx]

/-- The components of `σT_{μαβ̇}`, with all indices lowered, are the entries of the adjugate of
`σ̄^μ = η_μμ σ^μ`, transposed: `σT^{μβα}` at the labels `(μ, α, β)`. -/
lemma tensorBasis_repr_pauliTensor_downAll
    (μ : Π i, Idx (![down, downL, downR] i).kind) :
    (complexLorentz.tensorBasis _).repr {pauliTensor | ↓ν ↓α ↓β}ᵀ μ =
      pauliMatrix (μ 0) (μ 2) (μ 1) := by
  -- `↓` unfolds the lowered vector index by `tensorBasis_repr_pauliTensor_down` first.
  tensor_components [Species.tensorBasis_repr_toDualAt, formMatrix_apply,
    ↓tensorBasis_repr_pauliTensor_down]
  exact (sum_metricRaw_mul_sum_metricRaw_mul _ _ _).trans
    (congrFun₂ (PauliMatrix.adjugate_minkowskiMatrix_smul_pauliMatrix _) _ _)

/-- `σT^μ_{αβ̇} = σT_{ραβ̇} η^ρμ`, raising the vector index of the fully lowered Pauli tensor. -/
lemma pauliContrDown_eq_pauliCoDown_contr :
    {pauliTensor | μ ↓α ↓β = {pauliTensor | ↓ρ ↓α ↓β ⊗ η | ρ μ}ᵀ | α β μ}ᵀ := by
  tensor_regroup

/-!

## C. Contraction identities

The trace identity `pauliCoDown_trace_pauliCo` is proved in components, from the trace identity
of the Pauli matrices. The other identities are derived from it at tensor level: the Fierz
identity by reading the trace identity as `B ∘ A = 2` for the maps `pauliA` and `pauliB`, and the
anticommutators by the Schouten identity of `ε`.

### C.1. Traces

-/

/-- The trace identity `tr(σ̄_μ σ_ν) = 2 η_μν`, as `σT_{μαβ̇} σT_ν^{αβ̇} = 2 η_μν`. -/
lemma pauliCoDown_trace_pauliCo :
    {pauliTensor | ↓μ ↓α ↓β ⊗ pauliTensor | ↓ν α β = (2 : ℂ) • η' | μ ν}ᵀ := by
  tensor_components [tensorBasis_repr_pauliTensor_downAll, tensorBasis_repr_pauliTensor_down,
    tensorBasis_repr_formTensor_vec .down]
  -- The components are `tr(σ^μᵀ σ̄^νᵀ) = tr(σ^μ σ̄^ν)`, written out as a double sum.
  exact (Matrix.trace_transpose_mul _ _).trans
    (PauliMatrix.trace_pauliMatrix_mul_minkowskiMatrix_smul_pauliMatrix _ _)

/-- The trace identity `tr(σ_μ σ̄_ν) = 2 η_μν`, as `σT_μ^{αβ̇} σT_{ναβ̇} = 2 η_μν`. -/
lemma pauliCo_trace_pauliCoDown :
    {pauliTensor | ↓μ α β ⊗ pauliTensor | ↓ν ↓α ↓β = (2 : ℂ) • η' | μ ν}ᵀ := by
  have h : {pauliTensor | ↓μ α β ⊗ pauliTensor | ↓ν ↓α ↓β =
      {pauliTensor | ↓ν ↓α ↓β ⊗ pauliTensor | ↓μ α β}ᵀ | ν μ}ᵀ := by
    tensor_regroup
  rw [h, pauliCoDown_trace_pauliCo]
  tensor_regroup

/-- The mixed trace identity `tr(σ̄^μ σ_ν) = 2 δ^μ_ν`, as `σT^μ_{αβ̇} σT_ν^{αβ̇} = 2 δ^μ_ν`. -/
lemma pauliContrDown_trace_pauliCo :
    {pauliTensor | μ ↓α ↓β ⊗ pauliTensor | ↓ν α β = (2 : ℂ) • δ' | ν μ}ᵀ := by
  have h : {pauliTensor | μ ↓α ↓β ⊗ pauliTensor | ↓ν α β =
      {pauliTensor | ↓ρ ↓α ↓β ⊗ pauliTensor | ↓ν α β}ᵀ | ρ ν ⊗ η | ρ μ}ᵀ := by
    rw [pauliContrDown_eq_pauliCoDown_contr]
    tensor_regroup
  rw [h, pauliCoDown_trace_pauliCo]
  tensor_regroup

/-!

### C.2. The Fierz identity

-/

/-- `p ↦ σT_μ^{αβ̇} p^{μα'β̇'}`, from a tensor with a vector index to one with two Weyl indices. -/
noncomputable def pauliA : ℂT[up, upL, upR] →ₗ[ℂ] ℂT[upL, upR, upL, upR] where
  toFun p := {pauliTensor | ↓μ α β ⊗ p | μ α' β'}ᵀ
  map_add' p q := by simp only [tmul_add, map_add]
  map_smul' r p := by simp only [tmul_smul, map_smul, RingHom.id_apply]

/-- `X ↦ σT^μ_{αβ̇} X^{αβ̇α'β̇'}`, from a tensor with two Weyl indices to one with a vector
index. -/
noncomputable def pauliB : ℂT[upL, upR, upL, upR] →ₗ[ℂ] ℂT[up, upL, upR] where
  toFun X := {pauliTensor | μ ↓α ↓β ⊗ X | α β α' β'}ᵀ
  map_add' X Y := by simp only [tmul_add, map_add]
  map_smul' r X := by simp only [tmul_smul, map_smul, RingHom.id_apply]

/-- `pauliB ∘ pauliA = 2`, by the trace identity `σT^μ_{αβ̇} σT_ν^{αβ̇} = 2 δ_ν^μ`. -/
lemma pauliB_pauliA (p : ℂT[up, upL, upR]) : pauliB (pauliA p) = (2 : ℂ) • p := by
  have h : pauliB (pauliA p) =
      {{pauliTensor | μ ↓α ↓β ⊗ pauliTensor | ↓ν α β}ᵀ | μ ν ⊗ p | ν α' β'}ᵀ := by
    simp only [pauliA, pauliB, LinearMap.coe_mk, AddHom.coe_mk]
    tensor_regroup
  rw [h, pauliContrDown_trace_pauliCo]
  tensor_regroup

/-- `pauliA ∘ pauliB = 2`: both spaces have dimension `16`, so the left inverse `pauliB / 2` of
`pauliA` is a right inverse. -/
lemma pauliA_pauliB (X : ℂT[upL, upR, upL, upR]) : pauliA (pauliB X) = (2 : ℂ) • X := by
  have hdim : Module.finrank ℂ ℂT[up, upL, upR] = Module.finrank ℂ ℂT[upL, upR, upL, upR] := by
    rw [Species.finrank_tensor, Species.finrank_tensor]
    rfl
  have h : ((2 : ℂ)⁻¹ • pauliB) ∘ₗ pauliA = LinearMap.id := LinearMap.ext fun p => by
    simp [pauliB_pauliA]
  have h' := LinearMap.congr_fun ((LinearMap.comp_eq_id_comm_of_finrank_eq hdim).2 h) X
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, LinearMap.id_apply] at h'
  exact (inv_smul_eq_iff₀ two_ne_zero).1 h'

/-- Raising both Weyl indices of `σT^μ_{αβ̇}` gives `σT^{μαβ̇}`. -/
lemma pauliTensor_raise_lower : {{pauliTensor | μ ↓α ↓β}ᵀ | μ ↑α ↑β}ᵀ = pauliTensor := by
  tensor_slots

/-- The Fierz identity `σT_ν^{αβ̇} σT^{να'β̇'} = 2 ε^{αα'} ε^{β̇β̇'}`: it is
`pauliA σT = pauliA (pauliB (εL ⊗ εR)) / 2`. -/
lemma pauliCo_contr_pauliContr :
    {pauliTensor | ↓ν α β ⊗ pauliTensor | ν α' β' =
      (2 : ℂ) • {εL | α α' ⊗ εR | β β'}ᵀ | α α' β β'}ᵀ := by
  rw [map_smul, ← pauliA_pauliB]
  refine congrArg pauliA ?_
  rw [← pauliTensor_raise_lower]
  simp only [pauliB, LinearMap.coe_mk, AddHom.coe_mk]
  tensor_regroup

/-!

### C.3. The anticommutators

-/

/-- `σT^{μαβ̇} = σT_ρ^{αβ̇} η^{ρμ}`, raising the lowered vector index again. -/
lemma pauliTensor_eq_pauliCo_contr : {pauliTensor | μ α β = pauliTensor | ↓ρ α β ⊗ η | ρ μ}ᵀ := by
  tensor_regroup

/-- The trace identity `tr(σ^μ σ̄^ν) = 2 η^μν`, as `σT^{μαβ̇} σT^ν_{αβ̇} = 2 η^μν`. -/
lemma pauliContr_trace_pauliContrDown :
    {pauliTensor | μ α β ⊗ pauliTensor | ν ↓α ↓β = (2 : ℂ) • η | μ ν}ᵀ := by
  have h : {pauliTensor | μ α β ⊗ pauliTensor | ν ↓α ↓β =
      {pauliTensor | ν ↓α ↓β ⊗ pauliTensor | ↓ρ α β}ᵀ | ν ρ ⊗ η | ρ μ}ᵀ := by
    nth_rw 1 [pauliTensor_eq_pauliCo_contr]
    tensor_regroup
  rw [h, pauliContrDown_trace_pauliCo]
  tensor_regroup

/-- The trace identity `tr(σ̄^μ σ^ν) = 2 η^μν`, as `σT^μ_{αβ̇} σT^{ναβ̇} = 2 η^μν`. -/
lemma pauliContrDown_trace_pauliContr :
    {pauliTensor | μ ↓α ↓β ⊗ pauliTensor | ν α β = (2 : ℂ) • η | μ ν}ᵀ := by
  have h : {pauliTensor | μ ↓α ↓β ⊗ pauliTensor | ν α β =
      {pauliTensor | ν α β ⊗ pauliTensor | μ ↓α ↓β}ᵀ | ν μ}ᵀ := by
    tensor_regroup
  rw [h, pauliContr_trace_pauliContrDown]
  tensor_regroup

/-- `σT^{μρβ̇} σT^{νγδ̇} ε_{δ̇β̇} (ε_{γρ} δ^α_α') = 2 η^μν δ^α_α'`, the trace identity
`pauliContr_trace_pauliContrDown` with the lowerings written as contractions with `ε`. -/
lemma pauliContr_pauliContr_eps_epsL_deltaL :
    {pauliTensor | μ r β ⊗ pauliTensor | ν g d ⊗ εR' | d β ⊗
      {εL' | g r ⊗ δL | α α'}ᵀ | g r α α' = (2 : ℂ) • {η | μ ν ⊗ δL | α α'}ᵀ | μ ν α α'}ᵀ := by
  have h : {pauliTensor | μ r β ⊗ pauliTensor | ν g d ⊗ εR' | d β ⊗
      {εL' | g r ⊗ δL | α α'}ᵀ | g r α α' =
      {pauliTensor | μ r β ⊗ pauliTensor | ν ↓r ↓β}ᵀ | μ ν ⊗ δL | α α'}ᵀ := by
    tensor_regroup
  rw [h, pauliContr_trace_pauliContrDown]
  tensor_regroup

/-- The anticommutator `σ^μ σ̄^ν + σ^ν σ̄^μ = 2 η^μν`, as
`σT^{μαβ̇} σT^ν_{α'β̇} + σT^{ναβ̇} σT^μ_{α'β̇} = 2 η^μν δ^α_α'`. The Schouten identity splits
`ε_γρ δ^α_α'` in `pauliContr_pauliContr_eps_epsL_deltaL` into the two terms. -/
lemma pauliContr_mul_pauliContrDown_add :
    {pauliTensor | μ α β ⊗ pauliTensor | ν ↓α' ↓β + pauliTensor | ν α β ⊗ pauliTensor | μ ↓α' ↓β =
      (2 : ℂ) • {η | μ ν ⊗ δL | α α'}ᵀ | μ ν α α'}ᵀ := by
  rw [← pauliContr_pauliContr_eps_epsL_deltaL, schouten_downL]
  tensor_regroup

/-- `σT^{μγδ̇} σT^{ναρ̇} ε_{γα} (ε_{δ̇ρ̇} δ_β̇^β̇') = 2 η^μν δ_β̇^β̇'`, the trace identity
`pauliContrDown_trace_pauliContr` with the lowerings written as contractions with `ε`. -/
lemma pauliContr_pauliContr_eps_epsR_deltaR :
    {pauliTensor | μ g d ⊗ pauliTensor | ν a r ⊗ εL' | g a ⊗
      {εR' | d r ⊗ δR' | β β'}ᵀ | d r β β' = (2 : ℂ) • {η | μ ν ⊗ δR' | β β'}ᵀ | μ ν β β'}ᵀ := by
  have h : {pauliTensor | μ g d ⊗ pauliTensor | ν a r ⊗ εL' | g a ⊗
      {εR' | d r ⊗ δR' | β β'}ᵀ | d r β β' =
      {pauliTensor | μ ↓a ↓r ⊗ pauliTensor | ν a r}ᵀ | μ ν ⊗ δR' | β β'}ᵀ := by
    tensor_regroup
  rw [h, pauliContrDown_trace_pauliContr]
  tensor_regroup

/-- The anticommutator `σ̄^μ σ^ν + σ̄^ν σ^μ = 2 η^μν`, as
`σT^μ_{αβ̇} σT^{ναβ̇'} + σT^ν_{αβ̇} σT^{μαβ̇'} = 2 η^μν δ_β̇^β̇'`. The Schouten identity splits
`ε_δ̇ρ̇ δ_β̇^β̇'` in `pauliContr_pauliContr_eps_epsR_deltaR` into the two terms. -/
lemma pauliContrDown_pauliContr_mul_add :
    {pauliTensor | μ ↓α ↓β ⊗ pauliTensor | ν α β' + pauliTensor | ν ↓α ↓β ⊗ pauliTensor | μ α β' =
      (2 : ℂ) • {η | μ ν ⊗ δR' | β β'}ᵀ | μ ν β β'}ᵀ := by
  rw [← pauliContr_pauliContr_eps_epsR_deltaR, schouten_downR]
  tensor_regroup

end Tensors.complexLorentz
