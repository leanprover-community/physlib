/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Physlib.ProbabilisticTheory.CStarAlgebra.Channel

/-!
# Completely positive channels

A channel between C⋆-algebras is completely positive when it stays positive on matrices of
operators.

## i. Overview

A channel between C⋆-algebras extends to a positive map of all operators. It is completely
positive when this extension, applied entry by entry, keeps positive `k × k` matrices of
operators positive for every `k`.

## ii. Key results

- `Channel.IsCompletelyPositive` : a channel is completely positive.
- `Channel.completelyPositiveEquiv` : completely positive channels are the same as unital
  completely positive maps of all operators.
- `Channel.isCompletelyPositive_ofStarAlgHom` : a unital star homomorphism is a completely
  positive channel.
- `Channel.completelyPositive` : the completely positive channels of a C⋆-algebra form a monoid
  under composition.

## iii. Table of contents

- A. Completely positive channels
- B. Star homomorphisms
- C. Composition

## iv. References

-/

@[expose] public section

open ProbabilisticTheory
open scoped CStarAlgebra

namespace Channel

variable {𝒜 ℬ 𝒞 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞]

/-! ## A. Completely positive channels -/

/-- A channel is completely positive when its extension to all operators keeps positive `k × k`
matrices of operators positive for every `k`. -/
def IsCompletelyPositive (Φ : Channel (ofCStarAlgebra 𝒜) (ofCStarAlgebra ℬ)) : Prop :=
  ∀ (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) 𝒜), 0 ≤ M → 0 ≤ M.map Φ.extend

/-- The completely positive map of all operators of a completely positive channel. -/
noncomputable def IsCompletelyPositive.toCompletelyPositiveMap
    {Φ : Channel (ofCStarAlgebra 𝒜) (ofCStarAlgebra ℬ)} (h : Φ.IsCompletelyPositive) :
    𝒜 →CP ℬ where
  toLinearMap := Φ.extend.toLinearMap
  map_cstarMatrix_nonneg' := h

/-- Completely positive channels are the same as unital completely positive maps of all
operators. -/
noncomputable def completelyPositiveEquiv :
    {Φ : Channel (ofCStarAlgebra 𝒜) (ofCStarAlgebra ℬ) // Φ.IsCompletelyPositive} ≃
      {f : 𝒜 →CP ℬ // f 1 = 1} where
  toFun Φ := ⟨Φ.2.toCompletelyPositiveMap, Φ.1.extend_one⟩
  invFun f :=
    ⟨.ofComplex { toLinearMap := f.1.toLinearMap, monotone' := OrderHomClass.mono f.1 } f.2,
      fun k M hM ↦ by
        erw [extend_ofComplex]
        exact f.1.map_cstarMatrix_nonneg' k M hM⟩
  left_inv Φ := Subtype.ext (ofComplex_extend Φ.1)
  right_inv f := Subtype.ext <| DFunLike.ext _ _ fun A ↦
    DFunLike.congr_fun (extend_ofComplex _ f.2) A

/-! ## B. Star homomorphisms -/

/-- The channel of a unital star homomorphism `π` applies `π` to every observable. -/
noncomputable def ofStarAlgHom (π : 𝒜 →⋆ₐ[ℂ] ℬ) : Channel (ofCStarAlgebra 𝒜) (ofCStarAlgebra ℬ) :=
  .ofComplex { toLinearMap := π.toLinearMap, monotone' := OrderHomClass.mono π } (map_one π)

@[simp]
lemma coe_ofStarAlgHom_apply (π : 𝒜 →⋆ₐ[ℂ] ℬ) (A : selfAdjoint 𝒜) :
    (ofStarAlgHom π A : ℬ) = π A := rfl

/-- The channel of a unital star homomorphism is completely positive. -/
lemma isCompletelyPositive_ofStarAlgHom (π : 𝒜 →⋆ₐ[ℂ] ℬ) :
    (ofStarAlgHom π).IsCompletelyPositive := by
  intro k M hM
  erw [extend_ofComplex]
  exact CompletelyPositiveMapClass.map_cstarMatrix_nonneg' π k M hM

/-! ## C. Composition -/

/-- The identity channel is completely positive. -/
lemma isCompletelyPositive_id : (Channel.id (ofCStarAlgebra 𝒜)).IsCompletelyPositive :=
  isCompletelyPositive_ofStarAlgHom (.id ℂ 𝒜)

/-- The composite of two completely positive channels is completely positive. -/
lemma IsCompletelyPositive.comp {Ψ : Channel (ofCStarAlgebra ℬ) (ofCStarAlgebra 𝒞)}
    {Φ : Channel (ofCStarAlgebra 𝒜) (ofCStarAlgebra ℬ)} (hΨ : Ψ.IsCompletelyPositive)
    (hΦ : Φ.IsCompletelyPositive) : (Ψ.comp Φ).IsCompletelyPositive := by
  intro k M hM
  rw [extend_comp]
  exact hΨ k _ (hΦ k M hM)

/-- The completely positive channels of a C⋆-algebra form a monoid under composition. -/
def completelyPositive : Submonoid (Channel (ofCStarAlgebra 𝒜) (ofCStarAlgebra 𝒜)) where
  carrier := {Φ | Φ.IsCompletelyPositive}
  mul_mem' := IsCompletelyPositive.comp
  one_mem' := isCompletelyPositive_id

end Channel
