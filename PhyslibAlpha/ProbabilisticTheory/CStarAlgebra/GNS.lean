/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.State.Basic
public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!

# The GNS construction

Every state on a C⋆-algebra is the vector state of a cyclic unit vector in its GNS representation.

## i. Overview

Every state `ω` on a C⋆-algebra is a vector state of a representation. Mathlib's GNS construction
gives the Hilbert space `H_ω` and the representation `π_ω`. The image `Ω_ω` of `1` in `H_ω` is a
cyclic unit vector with `ω(a) = ⟪Ω_ω, π_ω(a) Ω_ω⟫`, and a faithful state gives a faithful
representation.

## ii. Key results

- `UnitalPositiveLinearMap.gnsRep` : the GNS representation of a state.
- `UnitalPositiveLinearMap.gnsCyclicVector` : the cyclic vector `Ω_ω`.
- `UnitalPositiveLinearMap.inner_gnsCyclicVector_gnsRep_gnsCyclicVector` : `ω(a) = ⟪Ω_ω, π_ω(a)
  Ω_ω⟫`.
- `UnitalPositiveLinearMap.denseRange_gnsRep_gnsCyclicVector` : `Ω_ω` is cyclic.
- `UnitalPositiveLinearMap.injective_gnsRep_of_isFaithful` : faithful states give faithful
  representations.

## iii. Table of contents

- A. The GNS representation
- B. The cyclic vector
- C. Faithful states

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace UnitalPositiveLinearMap

variable (ω : 𝓢[ℂ, A])

/-!

## A. The GNS representation

-/

/-- The GNS Hilbert space `H_ω` carried by a state `ω` on a unital C⋆-algebra: the Hilbert space
completion of `A` with respect to the (semi-)inner product `⟨x, y⟩ := ω(x⋆y)`. -/
noncomputable abbrev GNS := ω.toPositiveLinearMap.GNS

/-- The GNS representation `π_ω : A → B(H_ω)` carried by a state `ω`: the unital
`⋆`-homomorphism into the bounded operators on `ω.GNS` induced by left multiplication. -/
noncomputable abbrev gnsRep : A →⋆ₐ[ℂ] (ω.GNS →L[ℂ] ω.GNS) := ω.toPositiveLinearMap.gnsStarAlgHom

/-!

## B. The cyclic vector

-/

/-- The GNS cyclic vector `Ω_ω ∈ H_ω`: the image of `1 : A` under `A → ω.GNS`. -/
noncomputable def gnsCyclicVector : ω.GNS :=
  ((ω.toPositiveLinearMap.toPreGNS 1 : ω.toPositiveLinearMap.PreGNS) : ω.GNS)

/-- `π_ω(a) Ω_ω` is, concretely, the image of `a` itself under `A → ω.GNS` — since
`π_ω(a) Ω_ω = π_ω(a) · (\text{image of } 1) = \text{image of } (a \cdot 1) = \text{image of } a`. -/
lemma gnsRep_gnsCyclicVector (a : A) :
    ω.gnsRep a ω.gnsCyclicVector =
      ((ω.toPositiveLinearMap.toPreGNS a : ω.toPositiveLinearMap.PreGNS) : ω.GNS) := by
  show ω.toPositiveLinearMap.gnsStarAlgHom a
      ((ω.toPositiveLinearMap.toPreGNS 1 : ω.toPositiveLinearMap.PreGNS) : ω.GNS) = _
  rw [PositiveLinearMap.gnsStarAlgHom_apply]
  show ω.toPositiveLinearMap.gnsNonUnitalStarAlgHom a
      ((ω.toPositiveLinearMap.toPreGNS 1 : ω.toPositiveLinearMap.PreGNS) : ω.GNS) = _
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe, PositiveLinearMap.leftMulMapPreGNS_apply,
    PositiveLinearMap.ofPreGNS_toPreGNS, mul_one]

/-- `Ω_ω` has unit norm: `‖Ω_ω‖² = ω(1⋆1) = ω(1) = 1`. -/
@[simp]
lemma norm_gnsCyclicVector : ‖ω.gnsCyclicVector‖ = 1 := by
  have hsq : ((‖ω.gnsCyclicVector‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_pow]
    show (‖(_ : ω.toPositiveLinearMap.GNS)‖ : ℂ) ^ 2 = 1
    rw [gnsCyclicVector, UniformSpace.Completion.norm_coe,
      PositiveLinearMap.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul,
      show ω.toPositiveLinearMap 1 = ω 1 by rfl, map_one]
  have hsq' : ‖ω.gnsCyclicVector‖ ^ 2 = 1 := by exact_mod_cast hsq
  nlinarith [norm_nonneg ω.gnsCyclicVector]

/-- The defining identity of the GNS construction: `ω` is recovered as the vector state of `π_ω`
at the cyclic vector `Ω_ω`. -/
lemma inner_gnsCyclicVector_gnsRep_gnsCyclicVector (a : A) :
    ⟪ω.gnsCyclicVector, ω.gnsRep a ω.gnsCyclicVector⟫_ℂ = ω a := by
  rw [gnsRep_gnsCyclicVector, gnsCyclicVector, UniformSpace.Completion.inner_coe,
    PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.ofPreGNS_toPreGNS,
    PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul]
  rfl

/-- `Ω_ω` is cyclic: the orbit `π_ω(A) Ω_ω` is dense in `H_ω`, so every vector in `H_ω` is a limit
of vectors reachable from `Ω_ω` by applying elements of `A`. -/
lemma denseRange_gnsRep_gnsCyclicVector :
    DenseRange (fun a : A => ω.gnsRep a ω.gnsCyclicVector) := by
  have heq : (fun a : A => ω.gnsRep a ω.gnsCyclicVector) =
      (fun a : A => ((ω.toPositiveLinearMap.toPreGNS a :
        ω.toPositiveLinearMap.PreGNS) : ω.GNS)) := funext (gnsRep_gnsCyclicVector ω)
  rw [heq]
  have hden : DenseRange (((↑) : ω.toPositiveLinearMap.PreGNS → ω.GNS)) :=
    UniformSpace.Completion.denseRange_coe
  have hbij : Function.Bijective ω.toPositiveLinearMap.toPreGNS :=
    ω.toPositiveLinearMap.toPreGNS.toEquiv.bijective
  have : (fun a : A => ((ω.toPositiveLinearMap.toPreGNS a :
      ω.toPositiveLinearMap.PreGNS) : ω.GNS)) =
      ((↑) : ω.toPositiveLinearMap.PreGNS → ω.GNS) ∘ ω.toPositiveLinearMap.toPreGNS := rfl
  rw [this]
  exact hden.comp (Function.Surjective.denseRange hbij.surjective)
    (UniformSpace.Completion.continuous_coe _)

/-!

## C. Faithful states

-/

/-- A state is **faithful** when only `0` gives `x⋆x` weight `0` — the standard notion of a
faithful state on a C⋆-algebra, and the hypothesis under which the GNS representation `π_ω`
becomes injective. -/
def IsFaithful (ω : 𝓢[ℂ, A]) : Prop := ∀ x : A, ω (star x * x) = 0 → x = 0

/-- The GNS representation of a faithful state is faithful. -/
lemma injective_gnsRep_of_isFaithful (h : ω.IsFaithful) : Function.Injective ω.gnsRep := by
  have key : ∀ a : A, ω.gnsRep a = 0 → a = 0 := by
    intro a ha
    apply h
    have hzero : ω.gnsRep a ω.gnsCyclicVector = 0 := by rw [ha]; rfl
    rw [gnsRep_gnsCyclicVector] at hzero
    have hnorm : ‖(ω.toPositiveLinearMap.toPreGNS a : ω.toPositiveLinearMap.PreGNS)‖ = 0 := by
      have := congrArg norm hzero
      rwa [UniformSpace.Completion.norm_coe, norm_zero] at this
    have hsq : ((‖(ω.toPositiveLinearMap.toPreGNS a : ω.toPositiveLinearMap.PreGNS)‖ ^ 2 : ℝ) :
        ℂ) = 0 := by
      rw [hnorm]; norm_num
    rw [Complex.ofReal_pow, PositiveLinearMap.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS]
      at hsq
    exact hsq
  intro a b hab
  have hz : ω.gnsRep (a - b) = 0 := by rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (key _ hz)

end UnitalPositiveLinearMap

end ProbabilisticTheory
