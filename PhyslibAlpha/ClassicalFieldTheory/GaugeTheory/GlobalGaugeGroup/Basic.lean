/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Subalgebra
public import PhyslibAlpha.Mathematics.ForMathlib.Analysis.Normed.Algebra.MatrixLieAlgebra
/-!
# Global gauge groups

A global gauge group as a closed group of invertible matrices, with its Lie algebra.

## i. Overview

The global gauge group of a gauge theory is presented here as a closed subgroup `G` of the
general linear group `GL(κ, ℂ)`. These are the matrix Lie groups. They include every compact
Lie group, so every gauge group of the Standard Model and its extensions, as well as
non-compact groups such as `Sp(2n, ℝ)`, `SO(p, q)`, `SL(n, ℝ)` and the Lorentz group,
disconnected groups such as `O(n)`, and finite groups, whose Lie algebra is zero. A real
group sits inside `GL(κ, ℂ)` as the real matrices it contains. Lie groups with no faithful
finite-dimensional representation, such as the metaplectic group, are not covered.

The Lie algebra `𝔤` is determined by the group: it is the real subspace of matrices `X`
whose one-parameter subgroup `t ↦ exp (t X)` lies in `G`, `Matrix.lieAlgebraOfIsClosed`.
That this is a subspace closed under the commutator, and invariant under conjugation by `G`,
is proved there. For a compact group inside the unitary group the generators `X` are
anti-hermitian, and the hermitian generators of physics are `−i X`.

## ii. Key results

- `GlobalGaugeGroup` : a closed subgroup of a general linear group.
- `GlobalGaugeGroup.lieAlgebra` : its Lie algebra.
- `GlobalGaugeGroup.lieSubalgebra` : the Lie algebra as a Lie subalgebra of matrices.

## iii. Table of contents

- A. The structure
- B. The Lie algebra

## iv. References

* yang-mills-group, *OpenAI-YM-20261028*, `PublicTheory.lean`, the structure `GaugeGroup`,
  https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/PublicTheory.lean#L22-L33

-/

@[expose] public section

open Matrix NormedSpace

attribute [local instance 100] LieRing.ofAssociativeRing

/-!

## A. The structure

-/

/-- A global gauge group: a closed subgroup of the general linear group `GL(κ, ℂ)`. -/
structure GlobalGaugeGroup (κ : Type) [Fintype κ] [DecidableEq κ] where
  /-- The group, as a subgroup of the general linear group. -/
  group : Subgroup (GeneralLinearGroup κ ℂ)
  /-- The group is closed in the general linear group. -/
  isClosed : IsClosed (group : Set (GeneralLinearGroup κ ℂ))

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ] (G : GlobalGaugeGroup κ)

/-!

## B. The Lie algebra

-/

/-- The Lie algebra: the generators of the one-parameter subgroups of the group. -/
def lieAlgebra : Submodule ℝ (Matrix κ κ ℂ) :=
  lieAlgebraOfIsClosed G.group G.isClosed

lemma mem_lieAlgebra_iff (X : Matrix κ κ ℂ) : X ∈ G.lieAlgebra ↔
    ∀ t : ℝ, exp (t • X) ∈ Set.range fun g : G.group => (g.1 : Matrix κ κ ℂ) := Iff.rfl

/-- The Lie algebra, as a Lie subalgebra of matrices under the commutator. -/
def lieSubalgebra : LieSubalgebra ℝ (Matrix κ κ ℂ) where
  toSubmodule := G.lieAlgebra
  lie_mem' hX hY := by
    rw [Ring.lie_def]
    exact commutator_mem_lieAlgebraOfIsClosed hX hY

@[simp]
lemma mem_lieSubalgebra {X : Matrix κ κ ℂ} : X ∈ G.lieSubalgebra ↔ X ∈ G.lieAlgebra := Iff.rfl

noncomputable instance : LieRing G.lieSubalgebra := inferInstance

noncomputable instance : LieAlgebra ℝ G.lieSubalgebra := inferInstance

end GlobalGaugeGroup
