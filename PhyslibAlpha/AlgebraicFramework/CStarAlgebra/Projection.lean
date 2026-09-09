/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.SharpEffect
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection

/-!

# Projections in a C⋆-algebra

A projection is an idempotent effect: an effect `p : Effect (selfAdjoint A)` whose underlying
element satisfies `p * p = p`. This bundles `IsIdempotentElem.isSharp` (`SharpEffect.lean`) as a
genuine type, in the same style `PVM := {μ : POVM Ω E // μ.IsPVM}` bundles sharpness of every
effect a POVM assigns (`Representation/PVM.lean`) — a `Projection` is exactly the operator-level
data that makes a single POVM outcome a genuine projection.

Complementation and its involutivity are already available generically for *every* effect
(`Effect.complement`, `Effect.complement_complement`, `OrderUnit/Effect/Basic.lean`); the only new
ingredient needed to transport them to `Projection` is that the complement of an idempotent is
again idempotent, which needs no C⋆-algebraic input at all and is already
`IsIdempotentElem.one_sub` in Mathlib (`Algebra/Ring/Idempotent.lean`).

The one fact that is genuinely new to this codebase — nothing else here computes a spectrum — is
that the real spectrum of a projection lies in `{0, 1}`. This is exactly Mathlib's
`isIdempotentElem_iff_spectrum_subset`, specialized to the self-adjoint continuous functional
calculus that `selfAdjoint A` already carries for a C⋆-algebra `A`.

## Main definitions

- `Projection A`
- `Projection.isSharp` : every projection is a sharp effect (`IsIdempotentElem.isSharp`).
- `Projection.complement`, `Projection.complement_complement`
- `Projection.spectrum_subset_zero_one`

-/

@[expose] public section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A projection: an idempotent effect in the self-adjoint part of a C⋆-algebra. -/
def Projection (A : Type*) [CStarAlgebra A] [PartialOrder A] :=
  {p : Effect (selfAdjoint A) // IsIdempotentElem (((p : selfAdjoint A) : A))}

namespace Projection

/-- A projection, viewed as an effect, forgetting idempotence. -/
instance : CoeOut (Projection A) (Effect (selfAdjoint A)) := ⟨Subtype.val⟩

omit [StarOrderedRing A] in
@[ext]
lemma ext {p q : Projection A} (h : (p : Effect (selfAdjoint A)) = (q : Effect (selfAdjoint A))) :
    p = q :=
  Subtype.ext h

/-- Every projection is a sharp effect: it cannot be written as a nontrivial mixture of two
distinct effects. The payoff of `IsIdempotentElem.isSharp`. -/
theorem isSharp (p : Projection A) : Effect.IsSharp (p : Effect (selfAdjoint A)) :=
  p.2.isSharp

/-- The complementary projection `1 - p`. -/
def complement (p : Projection A) : Projection A :=
  ⟨Effect.complement (p : Effect (selfAdjoint A)), p.2.one_sub⟩

/-- Taking the complement twice returns the original projection. -/
@[simp]
lemma complement_complement (p : Projection A) : complement (complement p) = p :=
  Subtype.ext (Effect.complement_complement (p : Effect (selfAdjoint A)))

omit [StarOrderedRing A] in
/-- The real spectrum of a projection is contained in `{0, 1}`. -/
lemma spectrum_subset_zero_one (p : Projection A) :
    spectrum ℝ (((p : Effect (selfAdjoint A)) : selfAdjoint A) : A) ⊆ {0, 1} :=
  (isIdempotentElem_iff_spectrum_subset ℝ (((p : Effect (selfAdjoint A)) : selfAdjoint A) : A)
    ((p : Effect (selfAdjoint A)) : selfAdjoint A).2).mp p.2

end Projection
