/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.PauliMatrices.SelfAdjoint
public import PhyslibAlpha.Relativity.MinkowskiMatrix
/-!
# The covariant Pauli matrices as plain matrices

The Pauli matrices with the vector index lowered, and their completeness relation.

## i. Overview

`Physlib.Relativity.PauliMatrices.SelfAdjoint` carries the Pauli matrices as self-adjoint
matrices and as the basis `pauliBasis'` of the self-adjoint `2 × 2` matrices. Contracting
them against tensor components needs them as plain matrices, which is `pauliLower μ`, the
matrix underlying `pauliSelfAdjoint' μ`; `pauliBasis'_coe` identifies it with the basis vector
and `pauliLower_eq_smul` with `η_{μμ} σ^μ`. The Fierz completeness relation
`sum_pauliLower_mul_pauliLower` then says that these four matrices span the `2 × 2` matrices,
with the trace pairing as the duality and normalisation `2`; it is the relation which turns a
sum over a Lorentz index into a pair of Kronecker deltas on the spinor indices.

## ii. Key results

- `PauliMatrix.pauliLower` : the covariant Pauli matrices as plain matrices.
- `PauliMatrix.pauliBasis'_coe` : they underlie the basis `pauliBasis'`.
- `PauliMatrix.pauliLower_eq_smul` : lowering the index multiplies by the metric entry.
- `PauliMatrix.sum_pauliLower_mul_pauliLower` : the Fierz completeness relation.

## iii. Table of contents

- A. The covariant Pauli matrices as plain matrices

## iv. References

The self-adjoint Pauli matrices and the basis `pauliBasis'` are in
`Physlib.Relativity.PauliMatrices.SelfAdjoint`.

-/

@[expose] public section

namespace PauliMatrix

open Matrix Module KroneckerDelta
open Complex

/-!

## A. The covariant Pauli matrices as plain matrices

-/

/-- The Pauli matrices with the vector index lowered by the Minkowski metric,
  `σ_μ = η_{μμ} σ^μ`, as plain matrices: the underlying matrices of `pauliSelfAdjoint'`. -/
def pauliLower (μ : Fin 1 ⊕ Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := (pauliSelfAdjoint' μ).1

/-- The covariant Pauli matrices are the underlying matrices of the basis `pauliBasis'`. -/
lemma pauliBasis'_coe (μ : Fin 1 ⊕ Fin 3) : (pauliBasis' μ).1 = pauliLower μ := by
  rw [pauliBasis', Basis.coe_mk, pauliLower]

/-- Lowering the vector index multiplies by the diagonal entry of the metric. -/
lemma pauliLower_eq_smul (μ : Fin 1 ⊕ Fin 3) :
    pauliLower μ = ((minkowskiMatrixZ μ μ : ℤ) : ℂ) • pauliMatrix μ := by
  rcases μ with μ | μ <;> fin_cases μ <;> simp [pauliLower, pauliSelfAdjoint', minkowskiMatrixZ]

/-- The Fierz completeness relation: the covariant Pauli matrices span the `2 × 2` matrices,
  with the trace pairing as the duality and normalisation `2`. -/
lemma sum_pauliLower_mul_pauliLower (α α' β β' : Fin 2) :
    ∑ ρ : Fin 1 ⊕ Fin 3, pauliLower ρ β' β * pauliLower ρ α α'
      = 2 * ((if α = β then 1 else 0) * (if α' = β' then 1 else 0)) := by
  fin_cases α <;> fin_cases α' <;> fin_cases β <;> fin_cases β' <;>
    simp [pauliLower, pauliSelfAdjoint', pauliMatrix, Fintype.sum_sum_type, Fin.sum_univ_three] <;>
    norm_num [Complex.ext_iff]

end PauliMatrix
