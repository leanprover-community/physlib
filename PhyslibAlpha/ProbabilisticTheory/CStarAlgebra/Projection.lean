/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.SharpEffect
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection

/-!

# Projections

Projections of a C⋆-algebra: sharp idempotent effects with complements and spectrum in {0, 1}.

## i. Overview

A projection is an effect `p` with `p * p = p`. Projections are sharp effects, closed under
complement, and their spectrum lies in `{0, 1}`.

## ii. Key results

- `Projection` : projections of a C⋆-algebra.
- `Projection.isSharp` : projections are sharp.
- `Projection.complement` : the complementary projection `1 - p`.
- `Projection.spectrum_subset_zero_one` : the spectrum of a projection lies in `{0, 1}`.

## iii. Table of contents

- A. Projections
- B. Sharpness, complements and spectrum

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-!

## A. Projections

-/

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

/-!

## B. Sharpness, complements and spectrum

-/

/-- Every projection is a sharp effect. -/
lemma isSharp (p : Projection A) : Effect.IsSharp (p : Effect (selfAdjoint A)) :=
  p.2.isSharp

/-- The complementary projection `1 - p`. -/
noncomputable def complement (p : Projection A) : Projection A :=
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

end ProbabilisticTheory
