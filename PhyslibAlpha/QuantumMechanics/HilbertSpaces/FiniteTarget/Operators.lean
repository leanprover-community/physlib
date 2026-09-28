/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.Basic
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
/-!

# Operators on the Hilbert space of a finite target system

The bounded operators `𝓗[d] →L[ℂ] 𝓗[d]` form a C⋆-algebra, ordered by the Loewner order.
This file registers, directly on these operators,

- the real scalar action commuting with composition (`IsScalarTower ℝ`, `SMulCommClass ℝ`);
- the decomposition of a self-adjoint operator into positive and negative parts
  (`SelfAdjointDecompose`), from the continuous functional calculus.

These instances hold for the operators on any complex Hilbert space, but on `𝓗[d]` inferring
them unifies the two real actions on operators through the transferred complex module,
which runs out of budget. Stated here once, they let hermitian operators on `𝓗[d]` be used
where `SelfAdjointDecompose` is required, for instance as observables.

-/

@[expose] public section

namespace QuantumMechanics

namespace FiniteHilbertSpace

variable {d : Type*} [Fintype d] [DecidableEq d]

instance : IsScalarTower ℝ (𝓗[d] →L[ℂ] 𝓗[d]) (𝓗[d] →L[ℂ] 𝓗[d]) :=
  ⟨fun _ _ _ => by ext; simp⟩

instance : SMulCommClass ℝ (𝓗[d] →L[ℂ] 𝓗[d]) (𝓗[d] →L[ℂ] 𝓗[d]) :=
  ⟨fun _ _ _ => by ext; simp⟩

instance : SelfAdjointDecompose (𝓗[d] →L[ℂ] 𝓗[d]) := CFC.instSelfAdjointDecompose

end FiniteHilbertSpace

end QuantumMechanics
