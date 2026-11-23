/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.SL2C.Basic
public import PhyslibAlpha.Relativity.Fermions.Weyl.MetricPairing
public import PhyslibAlpha.Relativity.PauliMatrices.SelfAdjoint
/-!
# The action of `SL(2, ℂ)` on bispinor indices

A bispinor index is a left-handed and a right-handed Weyl index side by side, and the Pauli
matrices carry four-vector indices to bispinor indices.

## i. Overview

A bispinor index `(α, α̇)` is a left-handed and a right-handed Weyl index side by side, on which
`M ∈ SL(2, ℂ)` acts by `M_{αβ} conj(M_{α̇β̇})` (`bispinorMatrix`).

The covariant Pauli matrices change a four-vector index `μ` into a bispinor index,
`μ ↦ (σ_μ)_{αα̇}`. On every index of a coefficient tensor this is `pauliTransform`. As
`M σ_μ Mᴴ = Σ_ν Λ_{νμ} σ_ν`, it carries the action of the Lorentz matrix `Λ` of `M` to that of
`M` on bispinor indices, and by the trace orthogonality of the Pauli matrices it is injective (A).
On tensors this is `complexLorentzTensor.pauliTensorMap`, in
`PhyslibAlpha.Relativity.Bispinors.ComplexifiedAction`.

## ii. Key results

- `Lorentz.bispinorMatrix` : the action of `SL(2, ℂ)` on one bispinor index.
- `Lorentz.pauliTransform` : the change from four-vector indices to bispinor indices.
- `Lorentz.act_bispinorMatrix_pauliTransform` : it intertwines the two actions.
- `Lorentz.pauliTransform_injective` : it is injective.

## iii. Table of contents

- A. From four-vector indices to bispinor indices

## iv. References

* None.

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SlotAction Fermion

/-- The matrix by which `M ∈ SL(2, ℂ)` acts on one bispinor index `(α, α̇)`, a left-handed and a
  right-handed Weyl index, `M_{αβ} conj(M_{α̇β̇})`. -/
def bispinorMatrix (M : SL(2,ℂ)) : Fin 2 × Fin 2 → Fin 2 × Fin 2 → ℂ :=
  pairMatrix M.1 fun p q => star (M.1 p q)

/-!

## A. From four-vector indices to bispinor indices

-/

/-- The change from a four-vector index to a bispinor index by the covariant Pauli matrices,
  `μ ↦ (σ_μ)_{αα̇}`, on every index of a coefficient tensor. -/
def pauliTransform {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ((ι → Fin 1 ⊕ Fin 3) → ℂ) →ₗ[ℂ] ((ι → Fin 2 × Fin 2) → ℂ) :=
  transform fun μ p => PauliMatrix.pauliLower μ p.1 p.2

/-- The covariant Pauli matrices move as a covector, `M σ_μ Mᴴ = Σ_ν Λ_{νμ} σ_ν`, written
  entrywise against the action on a bispinor index. -/
lemma sum_pauliLower_mul_bispinorMatrix (M : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (q : Fin 2 × Fin 2) :
    ∑ p : Fin 2 × Fin 2, PauliMatrix.pauliLower μ p.1 p.2 * bispinorMatrix M q p
      = ∑ ν, (((SL2C.toLorentzGroup M).1 ν μ : ℝ) : ℂ) * PauliMatrix.pauliLower ν q.1 q.2 := by
  have h := congrArg (fun A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) => A.1 q.1 q.2)
    (SL2C.toSelfAdjointMap_basis (M := M) μ)
  simp only [SL2C.toSelfAdjointMap_apply, PauliMatrix.pauliBasis'_coe, AddSubgroup.val_finsetSum,
    selfAdjoint.val_smul, Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul] at h
  rw [← h, Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul, bispinorMatrix, pairMatrix]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- The Pauli change of indices carries the action of the Lorentz matrix of `M` on four-vector
  indices to the action of `M` on bispinor indices. -/
lemma act_bispinorMatrix_pauliTransform {ι : Type*} [Fintype ι] [DecidableEq ι] (M : SL(2,ℂ))
    (c : (ι → Fin 1 ⊕ Fin 3) → ℂ) :
    act (bispinorMatrix M) (pauliTransform c)
      = pauliTransform (act (fun a b => (((SL2C.toLorentzGroup M).1 a b : ℝ) : ℂ)) c) :=
  act_transform (sum_pauliLower_mul_bispinorMatrix M) c

/-- The trace orthogonality of the covariant Pauli matrices, `tr (σ_μ σ_ν) = 2 δ_{μν}`. -/
lemma sum_pauliLower_mul_pauliLower_swap (μ ν : Fin 1 ⊕ Fin 3) :
    ∑ p : Fin 2 × Fin 2, PauliMatrix.pauliLower μ p.1 p.2 * PauliMatrix.pauliLower ν p.2 p.1
      = 2 * if μ = ν then 1 else 0 := by
  rcases μ with μ | μ <;> rcases ν with ν | ν <;> fin_cases μ <;> fin_cases ν <;>
    simp [PauliMatrix.pauliLower, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
      Fintype.sum_prod_type] <;> norm_num [Complex.ext_iff]

/-- The Pauli change of indices is injective. Half the transposed Pauli matrices undo it. -/
lemma pauliTransform_injective {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Function.Injective (pauliTransform (ι := ι)) :=
  transform_injective (T' := fun p ν => 2⁻¹ * PauliMatrix.pauliLower ν p.2 p.1) fun μ ν => by
    simp_rw [mul_left_comm _ (2⁻¹ : ℂ), ← Finset.mul_sum, sum_pauliLower_mul_pauliLower_swap]
    split_ifs <;> norm_num


end Lorentz
