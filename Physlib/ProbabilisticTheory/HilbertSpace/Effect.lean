/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.CStarAlgebra.Effect
public import Physlib.ProbabilisticTheory.HilbertSpace.Basic

/-!
# Effects of subspaces

A subspace of a Hilbert space is a sharp yes-no measurement.

## i. Overview

A subspace `K` of the Hilbert space `H` asks whether the system lies in `K`. The orthogonal
projection onto `K` is the effect of this question. Its outcome no is the question for the
orthogonal complement `Kᗮ`. A smaller subspace gives a smaller effect. The effect of a subspace
is sharp. It is not a mixture of two other effects.

## ii. Key results

- `Submodule.toEffect` : the effect of a subspace.
- `Submodule.toEffect_le_toEffect_iff` : the order of effects is the inclusion of subspaces.
- `Submodule.toEffect_orthogonal` : the orthogonal complement gives the complementary effect.
- `Submodule.isSharp_toEffect` : the effect of a subspace is sharp.

## iii. Table of contents

- A. The effect of a subspace

## iv. References

- [ref: hall2013quantum]
-/

@[expose] public section

open ProbabilisticTheory Effect

namespace Submodule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## A. The effect of a subspace -/

/-- The effect of a subspace `K`: the orthogonal projection onto `K`. -/
noncomputable def toEffect (K : Submodule ℂ H) [K.HasOrthogonalProjection] :
    Effect (Observable 𝓑(H)) :=
  (isStarProjection_starProjection (U := K)).toEffect

@[simp]
lemma coe_toEffect (K : Submodule ℂ H) [K.HasOrthogonalProjection] :
    ((K.toEffect : Observable 𝓑(H)) : 𝓑(H)) = K.starProjection := rfl

/-- The order of effects is the inclusion of subspaces. -/
lemma toEffect_le_toEffect_iff {K L : Submodule ℂ H} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] : K.toEffect ≤ L.toEffect ↔ K ≤ L := by
  rw [← Subtype.coe_le_coe, ← Subtype.coe_le_coe, coe_toEffect, coe_toEffect]
  exact starProjection_le_starProjection_iff

/-- The orthogonal complement gives the complementary effect. -/
lemma toEffect_orthogonal (K : Submodule ℂ H) [K.HasOrthogonalProjection] :
    Kᗮ.toEffect = complement K.toEffect := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [coe_complement]
  simpa using starProjection_orthogonal' K

/-- The effect of a subspace is sharp. -/
lemma isSharp_toEffect (K : Submodule ℂ H) [K.HasOrthogonalProjection] :
    IsSharp K.toEffect :=
  Effect.isSharp_toEffect (isStarProjection_starProjection (U := K))

end Submodule
