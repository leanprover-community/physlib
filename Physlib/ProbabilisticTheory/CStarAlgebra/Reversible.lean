/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.CStarAlgebra.CompletelyPositive

/-!
# Reversible transformations of C⋆-algebras

Reversible transformations that are completely positive in both directions are ⋆-isomorphisms.

## i. Overview

A reversible transformation can be undone by another transformation. If both are completely
positive it is a ⋆-isomorphism of the operator algebras. Every ⋆-isomorphism is such a
transformation.

## ii. Key results

- `Channel.starAlgEquivOfInverse` : the ⋆-isomorphism of a completely positive channel with a
  completely positive inverse.
- `Channel.completelyPositiveReversibleEquiv` : reversible transformations that are completely
  positive in both directions are the ⋆-isomorphisms.
- `Channel.completelyPositiveUnitsEquiv` : the invertible completely positive channels of a system
  are its ⋆-automorphisms.

## iii. Table of contents

- A. Undoing a channel on all operators
- B. Channels with completely positive inverses
- C. Reversible transformations and ⋆-isomorphisms

## iv. References

* None.

-/

@[expose] public section

open ProbabilisticTheory

namespace Channel

variable {𝒜 ℬ : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  {Φ : Channel (ofCStarAlgebra 𝒜) (ofCStarAlgebra ℬ)}
  {Ψ : Channel (ofCStarAlgebra ℬ) (ofCStarAlgebra 𝒜)}

/-! ## A. Undoing a channel on all operators -/

/-- If `Ψ` undoes `Φ` on observables then their extensions cancel on all operators. -/
lemma extend_leftInverse_apply (h : Ψ.comp Φ = id _) (a : 𝒜) :
    Ψ.extend (Φ.extend a) = a := by
  simpa [extend_comp] using DFunLike.congr_fun (congrArg Channel.extend h) a

/-! ## B. Channels with completely positive inverses -/

/-- The Kadison–Schwarz inequalities for a channel and its inverse give equality on `a⋆ a`. -/
lemma extend_map_star_mul_self_of_inverse
    (hΦ : Φ.IsCompletelyPositive) (hΨ : Ψ.IsCompletelyPositive)
    (h₁ : Ψ.comp Φ = id _) (h₂ : Φ.comp Ψ = id _) (a : 𝒜) :
    Φ.extend (star a * a) = star (Φ.extend a) * Φ.extend a := by
  apply Function.LeftInverse.injective (extend_leftInverse_apply h₂)
  rw [extend_leftInverse_apply h₁]
  refine le_antisymm ?_ ?_
  · simpa only [extend_leftInverse_apply h₁] using hΨ.kadison_schwarz (Φ.extend a)
  · simpa only [extend_leftInverse_apply h₁] using
      OrderHomClass.mono Ψ.extend (hΦ.kadison_schwarz a)

/-- The ⋆-isomorphism of a completely positive channel with a completely positive inverse. -/
noncomputable def starAlgEquivOfInverse (hΦ : Φ.IsCompletelyPositive)
    (hΨ : Ψ.IsCompletelyPositive) (h₁ : Ψ.comp Φ = id _) (h₂ : Φ.comp Ψ = id _) :
    𝒜 ≃⋆ₐ[ℂ] ℬ where
  toFun := Φ.extend
  invFun := Ψ.extend
  left_inv := extend_leftInverse_apply h₁
  right_inv := extend_leftInverse_apply h₂
  map_add' := map_add Φ.extend
  map_smul' := map_smul Φ.extend
  map_star' := map_star Φ.extend
  map_mul' := Φ.extend.map_mul_of_map_star_mul_self
    (extend_map_star_mul_self_of_inverse hΦ hΨ h₁ h₂)

@[simp]
lemma starAlgEquivOfInverse_apply (hΦ : Φ.IsCompletelyPositive) (hΨ : Ψ.IsCompletelyPositive)
    (h₁ : Ψ.comp Φ = id _) (h₂ : Φ.comp Ψ = id _) (a : 𝒜) :
    starAlgEquivOfInverse hΦ hΨ h₁ h₂ a = Φ.extend a := rfl

/-! ## C. Reversible transformations and ⋆-isomorphisms -/

/-- A ⋆-isomorphism as a reversible transformation of observables. -/
noncomputable def reversibleOfStarAlgEquiv (E : 𝒜 ≃⋆ₐ[ℂ] ℬ) :
    Reversible (ofCStarAlgebra 𝒜) (ofCStarAlgebra ℬ) :=
  Reversible.ofChannels (ofStarAlgHom E.toStarAlgHom) (ofStarAlgHom E.symm.toStarAlgHom)
    (fun a ↦ Subtype.ext (E.symm_apply_apply a)) (fun b ↦ Subtype.ext (E.apply_symm_apply b))

/-- Reversible transformations that are completely positive in both directions are the
⋆-isomorphisms. -/
noncomputable def completelyPositiveReversibleEquiv :
    {e : Reversible (ofCStarAlgebra 𝒜) (ofCStarAlgebra ℬ) //
      e.toChannel.IsCompletelyPositive ∧ e.symm.toChannel.IsCompletelyPositive} ≃
      (𝒜 ≃⋆ₐ[ℂ] ℬ) where
  toFun e := starAlgEquivOfInverse e.2.1 e.2.2 (Channel.ext e.1.symm_apply_apply)
    (Channel.ext e.1.apply_symm_apply)
  invFun E := ⟨reversibleOfStarAlgEquiv E, isCompletelyPositive_ofStarAlgHom _,
    isCompletelyPositive_ofStarAlgHom _⟩
  left_inv e := Subtype.ext (Reversible.ext fun a ↦ Subtype.ext (e.1.toChannel.extend_apply a))
  right_inv E := StarAlgEquiv.ext (extend_ofStarAlgHom_apply E.toStarAlgHom)

/-- The invertible completely positive channels of a system are its ⋆-automorphisms. -/
noncomputable def completelyPositiveUnitsEquiv :
    (completelyPositive (𝒜 := 𝒜))ˣ ≃* (𝒜 ≃⋆ₐ[ℂ] 𝒜) where
  toFun u := starAlgEquivOfInverse u.1.2 u⁻¹.1.2 (congrArg Subtype.val u.inv_mul)
    (congrArg Subtype.val u.mul_inv)
  invFun E := ⟨⟨ofStarAlgHom E.toStarAlgHom, isCompletelyPositive_ofStarAlgHom _⟩,
    ⟨ofStarAlgHom E.symm.toStarAlgHom, isCompletelyPositive_ofStarAlgHom _⟩,
    Subtype.ext (Channel.ext fun a ↦ Subtype.ext (E.apply_symm_apply a)),
    Subtype.ext (Channel.ext fun a ↦ Subtype.ext (E.symm_apply_apply a))⟩
  left_inv u := Units.ext (Subtype.ext (Channel.ext fun a ↦ Subtype.ext (u.1.1.extend_apply a)))
  right_inv E := StarAlgEquiv.ext (extend_ofStarAlgHom_apply E.toStarAlgHom)
  map_mul' u v := StarAlgEquiv.ext fun a ↦ DFunLike.congr_fun (extend_comp u.1.1 v.1.1) a

end Channel
