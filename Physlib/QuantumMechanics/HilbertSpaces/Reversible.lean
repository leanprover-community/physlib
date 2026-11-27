/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.Normed.Operator.ContinuousAlgEquiv
public import Physlib.ProbabilisticTheory.CStarAlgebra.Reversible
public import Physlib.QuantumMechanics.HilbertSpaces.Basic

/-!
# Reversible quantum channels

The reversible quantum channels form the projective unitary group.

## i. Overview

A reversible quantum channel sends an observable `A` to `U A U⋆` for a unitary `U`, which is
unique up to a phase. So the reversible quantum channels form the projective unitary group of the
Hilbert space.

## ii. Key results

- `QuantumMechanics.ProjectiveUnitary` : unitaries up to a global phase.
- `QuantumMechanics.projectiveUnitaryEquiv` : the projective unitaries are the ⋆-automorphisms of
  the bounded operators.
- `QuantumMechanics.reversibleQuantumChannelEquiv` : the reversible quantum channels are the
  projective unitaries.
- `QuantumMechanics.extend_reversibleQuantumChannelEquiv_symm` : the reversible quantum channel
  of a unitary `U` sends `A` to `U A U⋆`.

## iii. Table of contents

- A. The projective unitary group
- B. Reversible quantum channels

## iv. References

* None.

-/

@[expose] public section

open ProbabilisticTheory

namespace QuantumMechanics

variable? (H : Type*) [QuantumHilbertSpace H] =>
  (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## A. The projective unitary group -/

/-- The projective unitary group of `H`, unitaries up to a global phase. -/
abbrev ProjectiveUnitary :=
  unitary 𝓑(H) ⧸ (Unitary.conjStarAlgAut ℂ 𝓑(H)).ker

/-- Every ⋆-automorphism of the bounded operators is conjugation by a unitary. -/
lemma conjStarAlgAut_surjective : Function.Surjective (Unitary.conjStarAlgAut ℂ 𝓑(H)) := by
  intro E
  obtain ⟨U, hU⟩ := E.eq_linearIsometryEquivConjStarAlgEquiv
    (NonUnitalStarAlgHom.isometry E E.injective).continuous
  refine ⟨Unitary.linearIsometryEquiv.symm U, ?_⟩
  rw [Unitary.conjStarAlgAut_symm_unitaryLinearIsometryEquiv]
  exact hU.symm

/-- The projective unitaries are the ⋆-automorphisms of the bounded operators. -/
noncomputable def projectiveUnitaryEquiv : ProjectiveUnitary H ≃* (𝓑(H) ≃⋆ₐ[ℂ] 𝓑(H)) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (conjStarAlgAut_surjective H)

/-! ## B. Reversible quantum channels -/

/-- The reversible quantum channels are the projective unitaries. -/
noncomputable def reversibleQuantumChannelEquiv : (QuantumChannel H H)ˣ ≃* ProjectiveUnitary H :=
  Channel.completelyPositiveUnitsEquiv.trans (projectiveUnitaryEquiv H).symm

/-- The reversible quantum channel of a unitary `U` sends `A` to `U A U⋆`. -/
lemma extend_reversibleQuantumChannelEquiv_symm (U : unitary 𝓑(H)) (A : 𝓑(H)) :
    ((reversibleQuantumChannelEquiv H).symm U : QuantumChannel H H).1.extend A =
      U * A * star (U : 𝓑(H)) :=
  Channel.extend_ofStarAlgHom_apply _ A

end QuantumMechanics
