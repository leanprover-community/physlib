/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.CStarAlgebra.Effect
public import Physlib.QuantumMechanics.HilbertSpaces.Basic

/-!
# Effects of subspaces

The sharp effects of a quantum system are exactly the closed subspaces of its Hilbert space.

## i. Overview

The orthogonal projection onto a closed subspace `K` of the Hilbert space `H` is an effect of the
quantum system. This effect is sharp. A smaller subspace gives a smaller effect and the orthogonal
complement `Kᗮ` gives the complementary effect `1 - P`.

Every sharp effect is the projection onto its range. So the sharp effects are exactly the closed
subspaces.

## ii. Key results

- `Submodule.toEffect` : the effect of a subspace.
- `Submodule.toEffect_orthogonal` : the orthogonal complement gives the complementary effect.
- `Submodule.starProjectionOrderIso` : the closed subspaces correspond to their projections.
- `Submodule.sharpEffectOrderIso` : the sharp effects are exactly the closed subspaces.

## iii. Table of contents

- A. The projection of a subspace as an effect
- B. Sharp effects are closed subspaces

## iv. References

-/

@[expose] public section

open ProbabilisticTheory Effect QuantumMechanics

namespace Submodule

variable? {H : Type*} [QuantumHilbertSpace H] =>
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## A. The projection of a subspace as an effect -/

/-- The effect of a subspace `K`, the orthogonal projection onto `K`. -/
noncomputable def toEffect (K : Submodule ℂ H) [K.HasOrthogonalProjection] : (quantum H).Effect :=
  ofProjection (isStarProjection_starProjection (U := K))

@[simp]
lemma coe_toEffect (K : Submodule ℂ H) [K.HasOrthogonalProjection] :
    (K.toEffect : 𝓑(H)) = K.starProjection := rfl

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
  isSharp_ofProjection (isStarProjection_starProjection (U := K))

/-! ## B. Sharp effects are closed subspaces -/

/-- The closed subspaces of `H` correspond to the projections onto them. -/
noncomputable def starProjectionOrderIso :
    ClosedSubmodule ℂ H ≃o {P : 𝓑(H) // IsStarProjection P} where
  toFun K := ⟨K.toSubmodule.starProjection, isStarProjection_starProjection⟩
  invFun P := ⟨(P : 𝓑(H)).range,
    ContinuousLinearMap.IsIdempotentElem.isClosed_range P.2.isIdempotentElem⟩
  left_inv K := ClosedSubmodule.toSubmodule_injective (range_starProjection K.toSubmodule)
  right_inv P := by
    have := ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range P.2.isIdempotentElem
    exact Subtype.ext ((ContinuousLinearMap.IsStarProjection.ext_iff isStarProjection_starProjection
      P.2).mpr (range_starProjection _))
  map_rel_iff' := starProjection_le_starProjection_iff.trans
    ClosedSubmodule.toSubmodule_le_toSubmodule

/-- The sharp effects of a quantum system are exactly the closed subspaces of its Hilbert space. -/
noncomputable def sharpEffectOrderIso :
    ClosedSubmodule ℂ H ≃o {e : (quantum H).Effect // IsSharp e} :=
  starProjectionOrderIso.trans projectionOrderIso

end Submodule
