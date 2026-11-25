/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.Addition
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.NormalizedBasis
public import Physlib.Relativity.PauliMatrices.Basic
/-!

# Spin ½ and the Pauli matrices

The spin-½ representation `standard 1` is given by half the Pauli matrices.

## i. Overview

The spin-`n/2` representation `AngularMomentumRepresentation.standard n` acts on
`StandardSl2Module ℂ n = Fin (n + 1) → ℂ`, whose standard basis `v k = Pi.single k 1` is the
basis of `LinearMap.toMatrix'`. For `n = 1` the matrices of `Jx, Jy, Jz` in this basis are
`σ₁ / 2, σ₂ / 2, σ₃ / 2`, with `σ_i = pauliMatrix (Sum.inr i)`, and those of the ladder operators
`J₊, J₋` are `σ₊ = |↑⟩⟨↓|` and `σ₋ = |↓⟩⟨↑|`, written as matrix literals; they equal
`(1 / 2) (σ₁ + i σ₂)` and `(1 / 2) (σ₁ - i σ₂)` (A). No new operators are defined: spin ½ is
`standard 1`, and the lemmas identify its matrices.

Conventions. `ℏ = 1`. The spatial indices `0, 1, 2` label `x, y, z`. The basis is
`|↑⟩ = |0⟩ = v 0` (`m = +½`) and `|↓⟩ = |1⟩ = v 1` (`m = -½`), so `σ₃ |↑⟩ = |↑⟩`. Over `ℝ` the
normalised states `|½, m⟩ = normVec 1 a` with `m = ½ - a` are exactly these basis vectors (B).
The Condon–Shortley phase convention of `normVec` holds with no extra signs:
`J₊ |↓⟩ = |↑⟩` and `J₋ |↑⟩ = |↓⟩`.

The commutation relations `[Jᵢ, Jⱼ] = i εᵢⱼₖ Jₖ` are not restated here: for `standard 1` they are
the fields `comm_xy`, `comm_yz`, `comm_zx` of `AngularMomentumRepresentation`, and for the Pauli
matrices they are `PauliMatrix.pauliMatrix_commutator`, `[σᵢ, σⱼ] = 2i ∑ₖ εᵢⱼₖ σₖ`, with its
vector form `PauliMatrix.vectorMatrix_commutator` (`Physlib.Relativity.PauliMatrices.Basic`).

## ii. Key results

- `toMatrix'_standard_one_Jx`, `toMatrix'_standard_one_Jy`, `toMatrix'_standard_one_Jz` :
  `J = σ / 2` for spin ½.
- `toMatrix'_standard_one_Jp`, `toMatrix'_standard_one_Jm` : the ladder operators are `σ₊, σ₋`.
- `normVec_one_zero`, `normVec_one_one` : the normalised basis of spin ½ is the standard basis.

## iii. Table of contents

- A. The spin-½ operators as Pauli matrices
- B. The normalised basis

## iv. References

## A. The spin-½ operators as Pauli matrices

-/

@[expose] public section

namespace PhyslibAlpha.Sl2

open Matrix Complex PauliMatrix AngularMomentumRepresentation StandardSl2Module

/-- In the basis `v 0 = |↑⟩`, `v 1 = |↓⟩`, the spin-½ operator `Jx` is `σ₁ / 2`. -/
lemma toMatrix'_standard_one_Jx :
    LinearMap.toMatrix' (standard 1).Jx = (1 / 2 : ℂ) • pauliMatrix (Sum.inr 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix'_apply, standard, stdJx, ρE, ρF, pauliMatrix, Pi.single_apply]

/-- In the basis `v 0 = |↑⟩`, `v 1 = |↓⟩`, the spin-½ operator `Jy` is `σ₂ / 2`. -/
lemma toMatrix'_standard_one_Jy :
    LinearMap.toMatrix' (standard 1).Jy = (1 / 2 : ℂ) • pauliMatrix (Sum.inr 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix'_apply, standard, stdJy, ρE, ρF, pauliMatrix, Pi.single_apply] <;>
    ring

/-- In the basis `v 0 = |↑⟩`, `v 1 = |↓⟩`, the spin-½ operator `Jz` is `σ₃ / 2`. -/
lemma toMatrix'_standard_one_Jz :
    LinearMap.toMatrix' (standard 1).Jz = (1 / 2 : ℂ) • pauliMatrix (Sum.inr 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [LinearMap.toMatrix'_apply, standard, stdJz, ρH, pauliMatrix, Pi.single_apply]

/-- The raising operator `J₊ = Jx + i Jy` of spin ½ is `σ₊ = (σ₁ + i σ₂) / 2 = |↑⟩⟨↓|`. -/
lemma toMatrix'_standard_one_Jp : LinearMap.toMatrix' (standard 1).Jp = !![0, 1; 0, 0] := by
  ext i j
  rw [standard_Jp]
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix'_apply, ρE]

/-- The lowering operator `J₋ = Jx - i Jy` of spin ½ is `σ₋ = (σ₁ - i σ₂) / 2 = |↓⟩⟨↑|`. -/
lemma toMatrix'_standard_one_Jm : LinearMap.toMatrix' (standard 1).Jm = !![0, 0; 1, 0] := by
  ext i j
  rw [standard_Jm]
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix'_apply, ρF]

/-!

## B. The normalised basis

-/

/-- The normalised state `|½, ½⟩ = normVec 1 0` is the basis vector `v 0`. -/
lemma normVec_one_zero : normVec 1 0 = v 0 := by
  simp [normVec, normSq, vNat_eq_v]

/-- The normalised state `|½, -½⟩ = normVec 1 1` is the basis vector `v 1`. -/
lemma normVec_one_one : normVec 1 1 = v 1 := by
  simp [normVec, normSq, vNat_eq_v]

end PhyslibAlpha.Sl2
