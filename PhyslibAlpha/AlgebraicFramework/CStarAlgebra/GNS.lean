/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.Basic
public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!

# The Gelfand─Naimark─Segal (GNS) construction: the cyclic vector

Every state produces a Hilbert space it did not start with. Given a state `ω` on a unital
C⋆-algebra `A` — no Hilbert space assumed, no representation assumed, just a positive normalized
linear functional (`ω : 𝓢[A]`, `OVERVIEW.md` §13) — the GNS construction recovers both: a Hilbert
space `H_ω`, a `⋆`-representation `π_ω : A → B(H_ω)`, and inside `H_ω` a single unit vector `Ω_ω`
that reproduces `ω` as a vector state of the representation,

  `ω(a) = ⟪Ω_ω, π_ω(a) Ω_ω⟫`.

`Ω_ω` is *cyclic*: applying every `a ∈ A` to it sweeps out a dense subspace of `H_ω`, so nothing in
`H_ω` sits outside what `π_ω(A)` can reach starting from `Ω_ω`. This is the converse to §13's vector
states `ω_ψ(x) = ⟪ψ, xψ⟫`: every state, not only the ones already handed a Hilbert space to live on,
*is* a vector state — of the Hilbert space this construction builds for it out of `ω` alone.

`Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal` already builds `H_ω`
(`PositiveLinearMap.GNS`) and `π_ω` (`PositiveLinearMap.gnsStarAlgHom`) from an arbitrary positive
linear functional. Its docstring lists the missing cyclic vector as a `TODO`. This file supplies
exactly that: `Ω_ω`
is the image of `1 : A` inside `H_ω`, the defining identity above, cyclicity of `Ω_ω`, and
faithfulness of `π_ω` when `ω` itself is a faithful state.

## Main definitions

- `UnitalPositiveLinearMap.GNS`, `UnitalPositiveLinearMap.gnsRep` : `H_ω` and `π_ω`, read directly
  off a state `ω : 𝓢[A]` rather than through the bare positive functional mathlib works with.
- `UnitalPositiveLinearMap.gnsCyclicVector` : `Ω_ω`, the image of `1 : A` in `H_ω`, of unit norm
  (`norm_gnsCyclicVector`).
- `UnitalPositiveLinearMap.inner_gnsCyclicVector_gnsRep_gnsCyclicVector` : the defining identity
  `ω(a) = ⟪Ω_ω, π_ω(a) Ω_ω⟫`.
- `UnitalPositiveLinearMap.denseRange_gnsRep_gnsCyclicVector` : `Ω_ω` is cyclic — `π_ω(A) Ω_ω` is
  dense in `H_ω`.
- `UnitalPositiveLinearMap.IsFaithful`, `UnitalPositiveLinearMap.injective_gnsRep_of_isFaithful` : a
  faithful state gives an injective (hence genuinely faithful) representation `π_ω`.

-/

@[expose] public section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace UnitalPositiveLinearMap

variable (ω : 𝓢[A])

/-- The GNS Hilbert space `H_ω` carried by a state `ω` on a unital C⋆-algebra: the Hilbert space
completion of `A` with respect to the (semi-)inner product `⟨x, y⟩ := ω(x⋆y)`. -/
noncomputable abbrev GNS := ω.toPositiveLinearMap.GNS

/-- The GNS representation `π_ω : A → B(H_ω)` carried by a state `ω`: the unital
`⋆`-homomorphism into the bounded operators on `ω.GNS` induced by left multiplication. -/
noncomputable abbrev gnsRep : A →⋆ₐ[ℂ] (ω.GNS →L[ℂ] ω.GNS) := ω.toPositiveLinearMap.gnsStarAlgHom

/-- The GNS cyclic vector `Ω_ω ∈ H_ω`: the image of `1 : A` under `A → ω.GNS`. -/
noncomputable def gnsCyclicVector : ω.GNS :=
  ((ω.toPositiveLinearMap.toPreGNS 1 : ω.toPositiveLinearMap.PreGNS) : ω.GNS)

/-- `π_ω(a) Ω_ω` is, concretely, the image of `a` itself under `A → ω.GNS` — since
`π_ω(a) Ω_ω = π_ω(a) · (\text{image of } 1) = \text{image of } (a \cdot 1) = \text{image of } a`. -/
theorem gnsRep_gnsCyclicVector (a : A) :
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
theorem norm_gnsCyclicVector : ‖ω.gnsCyclicVector‖ = 1 := by
  have hsq : ((‖ω.gnsCyclicVector‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_pow]
    show (‖(_ : ω.toPositiveLinearMap.GNS)‖ : ℂ) ^ 2 = 1
    rw [gnsCyclicVector, UniformSpace.Completion.norm_coe,
      PositiveLinearMap.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul,
      UnitalPositiveLinearMap.coe_toPositiveLinearMap, map_one]
  have hsq' : ‖ω.gnsCyclicVector‖ ^ 2 = 1 := by exact_mod_cast hsq
  nlinarith [norm_nonneg ω.gnsCyclicVector]

/-- The defining identity of the GNS construction: `ω` is recovered as the vector state of `π_ω`
at the cyclic vector `Ω_ω`. -/
theorem inner_gnsCyclicVector_gnsRep_gnsCyclicVector (a : A) :
    ⟪ω.gnsCyclicVector, ω.gnsRep a ω.gnsCyclicVector⟫_ℂ = ω a := by
  rw [gnsRep_gnsCyclicVector, gnsCyclicVector, UniformSpace.Completion.inner_coe,
    PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.ofPreGNS_toPreGNS,
    PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul,
    UnitalPositiveLinearMap.coe_toPositiveLinearMap]

/-- `Ω_ω` is cyclic: the orbit `π_ω(A) Ω_ω` is dense in `H_ω`, so every vector in `H_ω` is a limit
of vectors reachable from `Ω_ω` by applying elements of `A`. -/
theorem denseRange_gnsRep_gnsCyclicVector :
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

/-- A state is **faithful** when only `0` gives `x⋆x` weight `0` — the standard notion of a
faithful state on a C⋆-algebra, and the hypothesis under which the GNS representation `π_ω`
becomes injective. -/
def IsFaithful (ω : 𝓢[A]) : Prop := ∀ x : A, ω (star x * x) = 0 → x = 0

/-- A faithful state's GNS representation `π_ω` is injective: `π_ω` genuinely embeds `A` into
`B(H_ω)` rather than merely mapping into it. -/
theorem injective_gnsRep_of_isFaithful (h : ω.IsFaithful) : Function.Injective ω.gnsRep := by
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
    rwa [UnitalPositiveLinearMap.coe_toPositiveLinearMap] at hsq
  intro a b hab
  have hz : ω.gnsRep (a - b) = 0 := by rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (key _ hz)

end UnitalPositiveLinearMap
