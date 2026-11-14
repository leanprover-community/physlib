/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.CStarAlgebra.OrderUnit

/-!
# Channels of C⋆-algebras

Channels between the self-adjoint parts of C⋆-algebras extend uniquely to all operators.

## i. Overview

A channel acts on self-adjoint observables. Every operator decomposes into self-adjoint
real and imaginary parts, so a channel extends uniquely to a complex-linear map on all
operators. This extension is positive and preserves the identity. Restricting a unital positive
complex-linear map to observables recovers a channel.

## ii. Key results

- `Channel.complexExtension` : extend a real-linear map on self-adjoint elements.
- `Channel.complexExtension_unique` : uniqueness of the complex-linear extension.
- `Channel.extend` : a channel extended to all operators.
- `Channel.ofComplex` : a unital positive map restricted to a channel.
- `Channel.complexEquiv` : channels are the same as unital positive maps between all operators.
- `Channel.extend_comp` : extension respects composition.

## iii. Table of contents

- A. Complex extension
  - A.1. The extension
  - A.2. Agreement and uniqueness
- B. Channels on all operators

## iv. References

-/

@[expose] public section

/-! ## A. Complex extension -/

open ProbabilisticTheory ComplexStarModule ComplexOrder

namespace Channel

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]
  [AddCommGroup B] [Module ℂ B]
  {𝒜 ℬ 𝒞 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [CStarAlgebra 𝒞] [PartialOrder 𝒞] [StarOrderedRing 𝒞]

/-!

### A.1. The extension

-/

/-- The complex-linear extension of a real-linear map on self-adjoint operators to all
operators: `a ↦ φ (ℜ a) + i φ (ℑ a)`. -/
noncomputable def complexExtension (φ : selfAdjoint A →ₗ[ℝ] B) : A →ₗ[ℂ] B where
  toFun a := φ (ℜ a) + Complex.I • φ (ℑ a)
  map_add' a b := by
    simp only [map_add, smul_add]
    abel
  map_smul' z a := by
    simp only [realPart_smul, imaginaryPart_smul, map_add, map_sub, map_smul, RingHom.id_apply,
      ← Complex.coe_smul]
    have hI : Complex.I • Complex.I • φ (ℑ a) = -φ (ℑ a) := by
      rw [smul_smul, Complex.I_mul_I, neg_one_smul]
    conv_rhs => rw [← Complex.re_add_im z]
    linear_combination (norm := module) (-(z.im : ℂ)) • hI

lemma complexExtension_apply (φ : selfAdjoint A →ₗ[ℝ] B) (a : A) :
    complexExtension φ a = φ (ℜ a) + Complex.I • φ (ℑ a) := rfl

/-!

### A.2. Agreement and uniqueness

-/

/-- On self-adjoint operators the extension is the original map. -/
@[simp]
lemma complexExtension_coe (φ : selfAdjoint A →ₗ[ℝ] B) (a : selfAdjoint A) :
    complexExtension φ (a : A) = φ a := by
  simp [complexExtension_apply]

/-- A complex-linear map is determined by its values on self-adjoint operators. -/
lemma complexExtension_unique (φ : selfAdjoint A →ₗ[ℝ] B) (f : A →ₗ[ℂ] B)
    (h : ∀ a : selfAdjoint A, f a = φ a) : f = complexExtension φ := by
  ext a
  calc
    f a = f (realPart a : A) + Complex.I • f (imaginaryPart a : A) := by
      rw [← map_smul, ← map_add, realPart_add_I_smul_imaginaryPart]
    _ = complexExtension φ a := by rw [h, h]; rfl

/-!

## B. Channels on all operators

-/

/-- Extend a channel between observables to a positive map between all operators. -/
noncomputable def extend (Φ : Channel (ofCStarAlgebra 𝒜) (ofCStarAlgebra ℬ)) : 𝒜 →ₚ[ℂ] ℬ :=
  .mk₀ (complexExtension ((selfAdjoint.submodule ℝ ℬ).subtype ∘ₗ Φ.toLinearMap)) (by
    intro A hA
    obtain ⟨hr, hi⟩ := nonneg_iff_realPart_imaginaryPart.mp hA
    simp only [complexExtension_apply, hi, map_zero, smul_zero, add_zero]
    exact map_nonneg Φ hr)

/-- Extension agrees with the channel on every observable. -/
@[simp]
lemma extend_apply (Φ : Channel (ofCStarAlgebra 𝒜) (ofCStarAlgebra ℬ)) (A : selfAdjoint 𝒜) :
    Φ.extend (A : 𝒜) = (Φ A : ℬ) :=
  complexExtension_coe ((selfAdjoint.submodule ℝ ℬ).subtype ∘ₗ Φ.toLinearMap) A

/-- The extended channel preserves the identity. -/
@[simp]
lemma extend_one (Φ : Channel (ofCStarAlgebra 𝒜) (ofCStarAlgebra ℬ)) : Φ.extend 1 = 1 :=
  (Φ.extend_apply 1).trans (congrArg Subtype.val (map_one Φ))

/-- A unital positive map between all operators restricts to a channel between observables. -/
noncomputable def ofComplex (f : 𝒜 →ₚ[ℂ] ℬ) (h : f 1 = 1) :
    Channel (ofCStarAlgebra 𝒜) (ofCStarAlgebra ℬ) where
  toFun x := ⟨f x, x.2.map' f⟩
  map_add' x y := Subtype.ext (map_add f (x : 𝒜) y)
  map_smul' r x := Subtype.ext (map_smul f (r : ℂ) (x : 𝒜))
  monotone' _ _ hxy := OrderHomClass.mono f hxy
  map_one' := Subtype.ext h

/-- The restricted channel acts as the original map. -/
@[simp]
lemma coe_ofComplex_apply (f : 𝒜 →ₚ[ℂ] ℬ) (h : f 1 = 1) (x : selfAdjoint 𝒜) :
    (ofComplex f h x : ℬ) = f x := rfl

/-- Restricting an extended channel recovers the original channel. -/
@[simp]
lemma ofComplex_extend (Φ : Channel (ofCStarAlgebra 𝒜) (ofCStarAlgebra ℬ)) :
    ofComplex Φ.extend Φ.extend_one = Φ :=
  Channel.ext fun A => Subtype.ext (Φ.extend_apply A)

/-- A unital positive map is determined by its restriction to observables. -/
@[simp]
lemma extend_ofComplex (f : 𝒜 →ₚ[ℂ] ℬ) (h : f 1 = 1) : (ofComplex f h).extend = f :=
  PositiveLinearMap.toLinearMap_injective
    (complexExtension_unique _ f.toLinearMap fun _ => rfl).symm

/-- Channels between two systems are the same as unital positive maps between all their
operators. -/
noncomputable def complexEquiv :
    Channel (ofCStarAlgebra 𝒜) (ofCStarAlgebra ℬ) ≃ {f : 𝒜 →ₚ[ℂ] ℬ // f 1 = 1} where
  toFun Φ := ⟨Φ.extend, Φ.extend_one⟩
  invFun f := ofComplex f.1 f.2
  left_inv := ofComplex_extend
  right_inv f := Subtype.ext (extend_ofComplex f.1 f.2)

/-- Extending a composite channel agrees with composing the extensions. -/
lemma extend_comp (Ψ : Channel (ofCStarAlgebra ℬ) (ofCStarAlgebra 𝒞))
    (Φ : Channel (ofCStarAlgebra 𝒜) (ofCStarAlgebra ℬ)) :
    (Ψ.comp Φ).extend = Ψ.extend.comp Φ.extend :=
  PositiveLinearMap.toLinearMap_injective
    (complexExtension_unique _ (Ψ.extend.comp Φ.extend).toLinearMap fun A =>
      (congrArg Ψ.extend (Φ.extend_apply A)).trans (Ψ.extend_apply (Φ A))).symm

end Channel
