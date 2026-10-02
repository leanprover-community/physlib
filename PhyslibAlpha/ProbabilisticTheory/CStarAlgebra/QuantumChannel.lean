/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Restrict
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.OrderUnit

/-!

# Quantum channels

## i. Overview

A quantum channel between C⋆-algebras is a unital completely positive map: it stays positive when
applied to one half of any larger, possibly entangled, system. Complete positivity is Mathlib's
`CompletelyPositiveMap`. On self-adjoint parts every quantum channel is a channel between the
order-unit spaces of observables.

## ii. Key definitions

- `QuantumChannel A₁ A₂` : unital completely positive maps from `A₁` to `A₂`.
- `QuantumChannel.toChannel` : the channel it induces between the self-adjoint parts.

## iii. Table of contents

- A. Quantum channels
- B. The induced channel on observables

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped CStarAlgebra

variable {A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]
  [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂]
  [One A₁] [One A₂]

/-! ## A. Quantum channels -/

/-- A quantum channel: a unital completely positive map between C⋆-algebras. -/
structure QuantumChannel (A₁ A₂ : Type*) [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]
    [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂]
    [One A₁] [One A₂] extends A₁ →CP A₂, OneHom A₁ A₂

-- The inherited `OneHom` projection has no separately attachable docstring.
attribute [nolint docBlame] QuantumChannel.toOneHom

namespace QuantumChannel

instance : FunLike (QuantumChannel A₁ A₂) A₁ A₂ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

instance : LinearMapClass (QuantumChannel A₁ A₂) ℂ A₁ A₂ where
  map_add f := map_add f.toCompletelyPositiveMap
  map_smulₛₗ f := map_smulₛₗ f.toCompletelyPositiveMap

instance : CompletelyPositiveMapClass (QuantumChannel A₁ A₂) A₁ A₂ where
  map_cstarMatrix_nonneg' f := f.map_cstarMatrix_nonneg'

instance : OneHomClass (QuantumChannel A₁ A₂) A₁ A₂ where
  map_one f := f.map_one'

@[ext]
lemma ext {f g : QuantumChannel A₁ A₂} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-! ## B. The induced channel on observables -/

section Observables

variable {A₁ A₂ : Type*} [CStarAlgebra A₁] [CStarAlgebra A₂]
    [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂]

/-- The channel a quantum channel induces between the self-adjoint parts. -/
noncomputable def toChannel (f : QuantumChannel A₁ A₂) :
    Channel (selfAdjoint A₁) (selfAdjoint A₂) :=
  ({ toPositiveLinearMap := PositiveLinearMap.ofClass f
     map_one' := map_one f } : A₁ →ₚ₁[ℂ] A₂).restrictSA

end Observables

end QuantumChannel

end ProbabilisticTheory
