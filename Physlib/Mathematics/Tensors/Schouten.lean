/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.ElabTactics

/-!

# The Schouten identity in index notation

The Schouten identity of an antisymmetric form on a kind with two labels, as an equation of
tensors.

## i. Overview

For an antisymmetric form `g` on a kind with two labels, such as the Weyl `ε`, the Schouten
identity `g_γρ δ^α_α' = g_γα' δ_ρ^α - g_ρα' δ_γ^α` lets one exchange an index of the form with
an index of a delta. It is `Species.formMatrix_schouten` read in components, here stated in index
notation for both orientations of the delta.

## ii. Key results

- `Species.schouten_formTensor_deltaTensor` and `Species.schouten_formTensor_deltaTensor_dual` :
  the Schouten identity of an antisymmetric form on a kind with two labels, for both orientations
  of the delta.

## iii. Table of contents

- A. The Schouten identity

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

/-!

## A. The Schouten identity

-/

namespace Tensor.Species

variable {k : Type} [RCLike k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] {S : Species k G K basisIdx}
    (c : Color K) [S.HasForm c.kind] [S.IsAntisymmetricForm c.kind]

/-- The Schouten identity for an antisymmetric form on a kind with two labels, such as the Weyl `ε`,
`g_γρ δ^α_α' = g_γα' δ_ρ^α - g_ρα' δ_γ^α`. -/
lemma schouten_formTensor_deltaTensor (h2 : Fintype.card (basisIdx c.kind) = 2) :
    {S.formTensor c | γ ρ ⊗ S.deltaTensor c | α α' =
      S.formTensor c | γ α' ⊗ S.deltaTensor c.dual | ρ α +
        -{S.formTensor c | ρ α' ⊗ S.deltaTensor c.dual | γ α}ᵀ | ρ α' γ α}ᵀ := by
  tensor_components [tensorBasis_repr_formTensor, tensorBasis_repr_deltaTensor_eq_one]
  rw [← sub_eq_add_neg]
  exact formMatrix_schouten c h2 _ _ _ _

/-- The Schouten identity with the delta read the other way,
`g_γρ δ_α^α' = g_γα δ_ρ^α' - g_ρα δ_γ^α'`. -/
lemma schouten_formTensor_deltaTensor_dual (h2 : Fintype.card (basisIdx c.kind) = 2) :
    {S.formTensor c | γ ρ ⊗ S.deltaTensor c.dual | α α' =
      S.formTensor c | γ α ⊗ S.deltaTensor c.dual | ρ α' +
        -{S.formTensor c | ρ α ⊗ S.deltaTensor c.dual | γ α'}ᵀ | ρ α γ α'}ᵀ := by
  tensor_components [tensorBasis_repr_formTensor, tensorBasis_repr_deltaTensor_eq_one]
  rw [← sub_eq_add_neg]
  -- `formMatrix_schouten` with the two labels of the delta swapped.
  have h (γ ρ α α' : basisIdx c.kind) : S.formMatrix c γ ρ * (if α = α' then 1 else 0) =
      S.formMatrix c γ α * (if ρ = α' then 1 else 0) -
        S.formMatrix c ρ α * (if γ = α' then 1 else 0) := by
    simpa only [@eq_comm _ α' α] using formMatrix_schouten c h2 γ ρ α α'
  exact h _ _ _ _

end Tensor.Species
