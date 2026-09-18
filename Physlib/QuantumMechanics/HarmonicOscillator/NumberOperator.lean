/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import Physlib.QuantumMechanics.HarmonicOscillator.LadderOperators
/-!

# The number operators as unbounded operators

## i. Overview

The number operators `Nᵢ = aᵢ† aᵢ` of `LadderOperators.lean`, lifted to unbounded operators on the
Hilbert space with the Schwartz submodule as domain (like `momentumOperator`), and their symmetry.

## ii. Key results

- `numberOperator_isSymmetric`: the number operators are symmetric.

## iii. Table of contents

- A. The number operators as unbounded operators
- B. Symmetry

## iv. References

* None.

-/

@[expose] public section

noncomputable section
namespace QuantumMechanics.HarmonicOscillator

open SpaceDHilbertSpace MeasureTheory

variable {d : ℕ} (Q : HarmonicOscillator d) (i : Fin d)

/-!

## A. The number operators as unbounded operators

-/

/-- The number operator as an unbounded operator with domain the Schwartz submodule. -/
def numberOperator : Q.HS →ₗ.[ℂ] Q.HS where
  domain := SchwartzSubmodule d
  toFun := (schwartzIncl volume).1 ∘ₗ (Q.numberCLM i).1 ∘ₗ (schwartzEquiv volume).symm.1

lemma numberOperator_apply (ψ : SchwartzSubmodule d) :
    Q.numberOperator i ψ =
      schwartzEquiv volume (Q.numberCLM i ((schwartzEquiv volume).symm ψ)) :=
  rfl

/-!

## B. Symmetry

-/

/-- The number operator is symmetric. -/
lemma numberOperator_isSymmetric : (Q.numberOperator i).IsSymmetric := by
  intro ψ φ
  obtain ⟨f, rfl⟩ := (schwartzEquiv volume).surjective ψ
  obtain ⟨g, rfl⟩ := (schwartzEquiv volume).surjective φ
  simp only [numberOperator_apply, LinearEquiv.symm_apply_apply]
  exact Q.numberCLM_inner i f g

TODO "Prove that the number operators are essentially self-adjoint."

end QuantumMechanics.HarmonicOscillator

end
