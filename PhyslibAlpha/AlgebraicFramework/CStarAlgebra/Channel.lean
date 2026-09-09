/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-!

# Quantum channels between C⋆-algebras

A quantum channel between C⋆-algebras is a *unital completely positive* (UCP) map: complete
positivity, not mere positivity, is the physically correct notion at this level, since a channel
must stay positive even after being applied to one half of a larger, entangled system — exactly
what `CompletelyPositiveMap` (`A₁ →CP A₂`, matrix-amplified positivity) already captures. This
sidesteps needing a tensor product of order-unit spaces (flagged as missing in
`OrderUnit/Channel/Basic.lean`): matrix amplification tests positivity against every finite-rank
bystander system without constructing a tensor product explicitly.

A UCP map is automatically positive (`CompletelyPositiveMapClass` gives `OrderHomClass`), so
`Channel A₁ A₂` restricts, on the self-adjoint parts, to the abstract order-unit-level notion
already built (`OrderUnit/Channel/Basic.lean`'s `UnitalPositiveLinearMap`) — connecting the two is
future work, needing the positive/negative part decomposition of a self-adjoint element.

## Main definitions

- `Channel A₁ A₂`

-/

@[expose] public section

open scoped CStarAlgebra

variable {A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]
  [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂]
  [One A₁] [One A₂]

/-- A quantum channel: a unital completely positive map between C⋆-algebras. -/
structure Channel (A₁ A₂ : Type*) [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]
    [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂]
    [One A₁] [One A₂] extends A₁ →CP A₂, OneHom A₁ A₂

-- The inherited `OneHom` projection has no separately attachable docstring.
attribute [nolint docBlame] Channel.toOneHom

namespace Channel

instance : FunLike (Channel A₁ A₂) A₁ A₂ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

instance : LinearMapClass (Channel A₁ A₂) ℂ A₁ A₂ where
  map_add f := map_add f.toCompletelyPositiveMap
  map_smulₛₗ f := map_smulₛₗ f.toCompletelyPositiveMap

instance : CompletelyPositiveMapClass (Channel A₁ A₂) A₁ A₂ where
  map_cstarMatrix_nonneg' f := f.map_cstarMatrix_nonneg'

instance : OneHomClass (Channel A₁ A₂) A₁ A₂ where
  map_one f := f.map_one'

@[ext]
lemma ext {f g : Channel A₁ A₂} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

end Channel
