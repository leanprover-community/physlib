/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.PauliMatrices.ToTensor
/-!
# The Pauli tensor in components

The basis of `ℂT[.up, .upL, .upR]` indexed by a Lorentz and two spinor indices.

## i. Overview

`Physlib.Relativity.PauliMatrices.ToTensor` carries the Pauli matrices as the tensor
`σ^^^ : ℂT[.up, .upL, .upR]` and the equivalence `indexEquiv` identifying the component index
of that tensor with a triple `(μ, α, β)`. Reindexing the tensor basis along `indexEquiv` gives
`indexBasis`, the basis labelled by such triples, and `toTensor_eq_sum_indexBasis` expands the
Pauli tensor in it: the coefficient of `e_μ ⊗ e_α ⊗ e_β` is the entry `σ^μ_{α β}`. This is the
form in which the Pauli tensor enters a component computation.

## ii. Key results

- `PauliMatrix.indexBasis` : the basis of `ℂT[.up, .upL, .upR]` indexed by `(μ, α, β)`.
- `PauliMatrix.toTensor_eq_sum_indexBasis` : `σ^^^ = ∑ σ^μ_{α β} e_μ ⊗ e_α ⊗ e_β`.

## iii. Table of contents

- A. The basis indexed by a Lorentz and two spinor indices

## iv. References

The Pauli tensor and `indexEquiv` are in `Physlib.Relativity.PauliMatrices.ToTensor`.

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

## A. The basis indexed by a Lorentz and two spinor indices

-/

/-- The basis of `ℂT[.up, .upL, .upR]` indexed by `(Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2` through
  `indexEquiv`: `indexBasis (μ, α, β) = e_μ ⊗ e_α ⊗ e_β`. -/
noncomputable def indexBasis :
    Basis ((Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2) ℂ ℂT[.up, .upL, .upR] :=
  (Tensor.basis ![Color.up, Color.upL, Color.upR]).reindex indexEquiv

lemma indexBasis_apply (d : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2) :
    indexBasis d = Tensor.basis ![Color.up, Color.upL, Color.upR] (indexEquiv.symm d) :=
  Basis.reindex_apply _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The Pauli tensor as a sum over its components, `σ^^^ = ∑ σ^μ_{α β} e_μ ⊗ e_α ⊗ e_β`. -/
lemma toTensor_eq_sum_indexBasis : σ^^^ = ∑ d : (Fin 1 ⊕ Fin 3) × Fin 2 × Fin 2,
    pauliMatrix d.1 d.2.1 d.2.2 • indexBasis d := by
  have h : (toTensor (self := tensorial)).symm σ^^^ = pauliMatrix :=
    (toTensor (self := tensorial)).symm_apply_apply pauliMatrix
  conv_lhs => rw [← (Tensor.basis _).sum_repr σ^^^]
  rw [← indexEquiv.symm.sum_comp]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [indexBasis_apply]
  congr 1
  rw [toTensor_symm_apply] at h
  have h' := congrFun (congrFun (congrFun h d.1) d.2.1) d.2.2
  simpa using h'

end PauliMatrix

end
