/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Basic
public import Physlib.Relativity.Tensors.OfInt
/-!

# The Levi-Civita tensor as a real Lorentz tensor

## i. Overview

This file defines the rank-four Levi-Civita tensor `εᵘᵛᵖᵟ` as a real Lorentz tensor in
`d = 3` spatial dimensions, with `ε⁰¹²³ = 1`, and proves its antisymmetry under each
adjacent transposition of indices.

The component on a multi-index `f` is the generalized Kronecker delta of `f` against the
identity, i.e. the sign of `f` when `f` is a permutation and `0` otherwise. The integer
components are carried by `TensorSpecies.Tensor.TensorInt.toTensor`.

## ii. Key results

- `leviCivita` : the rank-four Levi-Civita tensor `ε4`, with `ε⁰¹²³ = 1`.
- `leviCivita_basis_repr_apply` : its standard-basis components as a generalized Kronecker delta.
- `leviCivita_basis_repr_eq_leviCivitaSymbol` : its standard-basis components as the
  general-dimension Levi-Civita symbol `leviCivitaSymbol` at `ι = Fin 4`.
- `leviCivita_antisymm`, `leviCivita_antisymm_mid`, `leviCivita_antisymm_last` : antisymmetry
  under each adjacent transposition of the indices.

## iii. Table of contents

- A. Definition
- B. Components in the standard basis
- C. Antisymmetry

## iv. References

* None.
-/

@[expose] public section

open Matrix
open MatrixGroups
open TensorProduct
noncomputable section

namespace realLorentzTensor
open TensorSpecies
open Tensor
open KroneckerDelta

/-!

## A. Definition

-/

/-- The Levi-Civita tensor `εᵘᵛᵖᵟ` as a real Lorentz tensor in `d = 3`, with `ε⁰¹²³ = 1`.

The component on a multi-index `f` is the generalized Kronecker delta of `f` against the
identity, i.e. the sign of `f` when `f` is a permutation and `0` otherwise. -/
noncomputable def leviCivita : ℝT[3, .up, .up, .up, .up] :=
  TensorInt.toTensor (S := realLorentzTensor 3)
    (c := ![Color.up, Color.up, Color.up, Color.up]) fun f =>
    generalizedKroneckerDelta (fun i => finSumFinEquiv (f i)) (id : Fin 4 → Fin 4)

/-- The Levi-Civita tensor `εᵘᵛᵖᵟ` as a real Lorentz tensor. -/
scoped[realLorentzTensor] notation "ε4" => leviCivita

/-- The `TensorInt.toTensor` form of the Levi-Civita tensor. -/
lemma leviCivita_eq_ofInt : ε4 =
    TensorInt.toTensor (S := realLorentzTensor 3)
    (c := ![Color.up, Color.up, Color.up, Color.up]) fun f =>
    generalizedKroneckerDelta (fun i => finSumFinEquiv (f i)) (id : Fin 4 → Fin 4) :=
  rfl

/-- The Euclidean Levi-Civita symbol `ε_{ijkl}` in dimension 4. -/
def _root_.euclidLeviCivita (g : Fin 4 → Fin 4) : ℝ :=
  generalizedKroneckerDelta g (id : Fin 4 → Fin 4)

/-- The Euclidean Levi-Civita symbol in dimension 4 is the general-dimension
Levi-Civita symbol `leviCivitaSymbol` at `ι = Fin 4`, carried to the reals. -/
lemma _root_.euclidLeviCivita_eq_leviCivitaSymbol (g : Fin 4 → Fin 4) :
    euclidLeviCivita g = (leviCivitaSymbol g : ℝ) :=
  rfl

/-!

## B. Components in the standard basis

-/

/-- The components of the Levi-Civita tensor in the standard basis are the generalized
Kronecker delta of the multi-index against the identity. -/
lemma leviCivita_basis_repr_apply
    (b : ComponentIdx (S := realLorentzTensor 3) ![Color.up, Color.up, Color.up, Color.up]) :
    (Tensor.basis _).repr ε4 b
      = (generalizedKroneckerDelta (fun i => finSumFinEquiv (b i)) (id : Fin 4 → Fin 4) : ℝ) := by
  rw [leviCivita_eq_ofInt, TensorInt.basis_repr_apply]

/-- The components of the Levi-Civita tensor in the standard basis are the
general-dimension Levi-Civita symbol `leviCivitaSymbol` of the multi-index at
`ι = Fin 4`. -/
lemma leviCivita_basis_repr_eq_leviCivitaSymbol
    (b : ComponentIdx (S := realLorentzTensor 3) ![Color.up, Color.up, Color.up, Color.up]) :
    (Tensor.basis _).repr ε4 b
      = (leviCivitaSymbol (fun i => finSumFinEquiv (b i)) : ℝ) :=
  leviCivita_basis_repr_apply b

/-- The Levi-Civita tensor vanishes on any multi-index with a repeated value: if two distinct
index positions `i ≠ j` carry the same basis index, the component is zero. -/
lemma leviCivita_basis_repr_eq_zero_of_eq
    {b : ComponentIdx (S := realLorentzTensor 3) ![Color.up, Color.up, Color.up, Color.up]}
    {i j : Fin 4} (hij : i ≠ j) (h : b i = b j) :
    (Tensor.basis _).repr ε4 b = 0 := by
  rw [leviCivita_basis_repr_apply]
  have hdet : generalizedKroneckerDelta (fun i => finSumFinEquiv (b i))
      (id : Fin 4 → Fin 4) = 0 := by
    rw [show generalizedKroneckerDelta (fun i => finSumFinEquiv (b i)) (id : Fin 4 → Fin 4)
          = Matrix.det (fun a c => ((kroneckerDelta (finSumFinEquiv (b a)) (id c) : ℕ) : ℤ))
          from rfl]
    refine Matrix.det_zero_of_row_eq hij (funext fun c => ?_)
    rw [congrArg (⇑finSumFinEquiv) h]
  rw [hdet, Int.cast_zero]

/-!

## C. Antisymmetry

-/

/-- The Levi-Civita tensor is antisymmetric in its first two indices
`{ε4 | μ ν ρ σ = - ε4 | ν μ ρ σ}ᵀ`. -/
lemma leviCivita_antisymm : {ε4 | μ ν ρ σ = - (ε4 | ν μ ρ σ)}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [permT_basis_repr_symm_apply, leviCivita_eq_ofInt, TensorInt.basis_repr_apply,
    map_neg, Finsupp.neg_apply, TensorInt.basis_repr_apply, ← Int.cast_neg]
  congr 1
  rw [← generalizedKroneckerDelta_swap _ _ (Fin.zero_ne_one (n := 2))]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The Levi-Civita tensor is antisymmetric in its middle two indices
`{ε4 | μ ν ρ σ = - ε4 | μ ρ ν σ}ᵀ`. -/
lemma leviCivita_antisymm_mid : {ε4 | μ ν ρ σ = - (ε4 | μ ρ ν σ)}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [permT_basis_repr_symm_apply, leviCivita_eq_ofInt, TensorInt.basis_repr_apply,
    map_neg, Finsupp.neg_apply, TensorInt.basis_repr_apply, ← Int.cast_neg]
  congr 1
  rw [← generalizedKroneckerDelta_swap _ _ (show (1 : Fin 4) ≠ 2 by decide)]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The Levi-Civita tensor is antisymmetric in its last two indices
`{ε4 | μ ν ρ σ = - ε4 | μ ν σ ρ}ᵀ`. -/
lemma leviCivita_antisymm_last : {ε4 | μ ν ρ σ = - (ε4 | μ ν σ ρ)}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [permT_basis_repr_symm_apply, leviCivita_eq_ofInt, TensorInt.basis_repr_apply,
    map_neg, Finsupp.neg_apply, TensorInt.basis_repr_apply, ← Int.cast_neg]
  congr 1
  rw [← generalizedKroneckerDelta_swap _ _ (show (2 : Fin 4) ≠ 3 by decide)]
  congr 1
  funext i
  fin_cases i <;> rfl

end realLorentzTensor
