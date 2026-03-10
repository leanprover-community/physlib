/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Relativity.Tensors.ComplexTensor.Units.Basic
/-!

## Symmetry lemmas relating to units

-/

@[expose] public section
open IndexNotation
open Matrix

namespace complexLorentzTensor

/-!

## Symmetry properties

-/
open TensorSpecies
open Tensor

/-- Swapping indices of `coContrUnit` returns `contrCoUnit`: `{δ' | μ ν = δ | ν μ}ᵀ`. -/
lemma coContrUnit_symm : {δ' | μ ν = δ | ν μ}ᵀ := by
  rw [coContrUnit, unitTensor_eq_permT_dual]
  rfl

/-- Swapping indices of `contrCoUnit` returns `coContrUnit`: `{δ | μ ν = δ' | ν μ}ᵀ`. -/
lemma contrCoUnit_symm : {δ | μ ν = δ' | ν μ}ᵀ := by
  rw [contrCoUnit, unitTensor_eq_permT_dual]
  rfl

/-- Swapping indices of `altLeftLeftUnit` returns
  `leftAltLeftUnit`: `{δL' | α α' = δL | α' α}ᵀ`. -/
lemma altLeftLeftUnit_symm : {δL' | α α' = δL | α' α}ᵀ := by
  rw [altLeftLeftUnit, unitTensor_eq_permT_dual]
  rfl

/-- Swapping indices of `leftAltLeftUnit` returns
  `altLeftLeftUnit`: `{δL | α α' = δL' | α' α}ᵀ`. -/
lemma leftAltLeftUnit_symm : {δL | α α' = δL' | α' α}ᵀ := by
  rw [leftAltLeftUnit, unitTensor_eq_permT_dual]
  rfl

/-- Swapping indices of `altRightRightUnit` returns `rightAltRightUnit`:
`{δR' | β β' = δR | β' β}ᵀ`.
-/
lemma altRightRightUnit_symm : {δR' | β β' = δR | β' β}ᵀ := by
  rw [altRightRightUnit, unitTensor_eq_permT_dual]
  rfl

/-- Swapping indices of `rightAltRightUnit` returns `altRightRightUnit`:
`{δR | β β' = δR' | β' β}ᵀ`.
-/
lemma rightAltRightUnit_symm : {δR | β β' = δR' | β' β}ᵀ := by
  rw [rightAltRightUnit, unitTensor_eq_permT_dual]
  rfl

end complexLorentzTensor
