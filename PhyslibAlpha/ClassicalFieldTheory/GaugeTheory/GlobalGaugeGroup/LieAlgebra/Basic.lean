/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.Basic
public import PhyslibAlpha.Mathematics.ForMathlib.Analysis.Normed.Algebra.MatrixLieAlgebra
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Subalgebra
/-!
# The Lie algebra of a global gauge group

The generators of the one-parameter subgroups of a global gauge group.

## i. Overview

The Lie algebra `𝔤` of a global gauge group `G ⊆ GL(κ, ℂ)` is determined by the group. It
is the real subspace of matrices `X` whose one-parameter subgroup `t ↦ exp (t X)` lies in
`G`, `Matrix.lieAlgebraOfIsClosed`. That this is a subspace closed under the commutator, and
invariant under conjugation by `G`, is proved there. A finite group has zero Lie algebra. For
a compact group inside the unitary group the generators `X` are anti-hermitian, and the
hermitian generators of physics are `−i X`.

The one-parameter subgroups of the generators are in
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.LieAlgebra.OneParameter`,
and the adjoint action of `G` on `𝔤` is in
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.LieAlgebra.Adjoint`.

## ii. Key results

- `GlobalGaugeGroup.lieAlgebra` : the Lie algebra of a global gauge group.
- `GlobalGaugeGroup.lieSubalgebra` : the Lie algebra as a Lie subalgebra of matrices.

## iii. Table of contents

- A. The Lie algebra
- B. The Lie algebra as a Lie subalgebra

## iv. References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer (2015).

-/

@[expose] public section

open Matrix NormedSpace

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ] (G : GlobalGaugeGroup κ)

/-!

## A. The Lie algebra

-/

/-- The Lie algebra of a global gauge group, the generators of its one-parameter
  subgroups. -/
def lieAlgebra : Submodule ℝ (Matrix κ κ ℂ) :=
  lieAlgebraOfIsClosed G.group G.isClosed

lemma mem_lieAlgebra_iff (X : Matrix κ κ ℂ) : X ∈ G.lieAlgebra ↔
    ∀ t : ℝ, exp (t • X) ∈ Set.range fun g : G.group => (g.1 : Matrix κ κ ℂ) := Iff.rfl

/-!

## B. The Lie algebra as a Lie subalgebra

-/

/-- The Lie algebra, as a Lie subalgebra of matrices under the commutator. -/
def lieSubalgebra : LieSubalgebra ℝ (Matrix κ κ ℂ) where
  toSubmodule := G.lieAlgebra
  lie_mem' hX hY := by
    rw [Ring.lie_def]
    exact commutator_mem_lieAlgebraOfIsClosed hX hY

@[simp]
lemma mem_lieSubalgebra {X : Matrix κ κ ℂ} : X ∈ G.lieSubalgebra ↔ X ∈ G.lieAlgebra := Iff.rfl

noncomputable instance : AddCommGroup G.lieSubalgebra := inferInstance

noncomputable instance : Module ℝ G.lieSubalgebra := inferInstance

noncomputable instance : LieRing G.lieSubalgebra := inferInstance

noncomputable instance : LieAlgebra ℝ G.lieSubalgebra := inferInstance

/-- The Lie algebra is finite-dimensional, as a subspace of the matrices. -/
instance : Module.Finite ℝ G.lieSubalgebra := inferInstance

end GlobalGaugeGroup
