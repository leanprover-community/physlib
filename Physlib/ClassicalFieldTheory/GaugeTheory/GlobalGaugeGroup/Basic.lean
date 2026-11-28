/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
/-!
# Global gauge groups

A global gauge group as a closed group of invertible matrices.

## i. Overview

In a gauge theory a gauge transformation may vary from one spacetime point to the next, while
its value at each point lies in one fixed group. In an `SU(2)` gauge theory, for instance, it is
a function `U(x)` whose value at every point is a unitary `2 × 2` matrix of determinant one.
That fixed group is the global gauge group of the theory, so called because its own elements
are the gauge transformations which take the same value at every point.

We take a global gauge group to be a matrix Lie group, a closed subgroup `G` of the invertible
complex matrices `GL(κ, ℂ)`. This is general enough to include every compact Lie group, and
with them the gauge groups of the Standard Model. An element `g : G.group` is then a single
such matrix, which for `SU(2)` is the value `U(x)` of a gauge transformation at one point.

## ii. Key results

- `GlobalGaugeGroup` : a closed subgroup of a general linear group.
- `GlobalGaugeGroup.group` : the group, as a subgroup of the general linear group.
- `GlobalGaugeGroup.ofSubmonoid` : the group of units of a closed matrix submonoid.
- `GlobalGaugeGroup.mem_ofSubmonoid_iff_of_star_mem` : for unitary `S` stable under `†`,
  membership in the group is membership in `S`.

## iii. Table of contents

- A. Global gauge groups
- B. Global gauge groups from closed submonoids of matrices

## iv. References

* yang-mills-group, *OpenAI-YM-20261028*, `PublicTheory.lean`, the structure `GaugeGroup`,
  https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/PublicTheory.lean#L22-L33

-/

@[expose] public section

open Matrix

/-!

## A. Global gauge groups

-/

/-- A global gauge group, a closed subgroup of the general linear group `GL(κ, ℂ)`. -/
abbrev GlobalGaugeGroup (κ : Type) [Fintype κ] [DecidableEq κ] : Type :=
  ClosedSubgroup (GeneralLinearGroup κ ℂ)

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The gauge group as a subgroup of `GL(κ, ℂ)`. -/
abbrev group (G : GlobalGaugeGroup κ) : Subgroup (GeneralLinearGroup κ ℂ) := G.toSubgroup

/-- The group is closed in the general linear group. -/
lemma isClosed (G : GlobalGaugeGroup κ) : IsClosed (G.group : Set (GeneralLinearGroup κ ℂ)) :=
  G.isClosed'

/-!

## B. Global gauge groups from closed submonoids of matrices

Groups such as `SU(2)` are specified by matrix equations. When their solutions form a closed
submonoid, its units form a global gauge group.

-/

/-- The global gauge group of invertible matrices `g` with `g` and `g⁻¹` in a closed
  submonoid `S`. -/
def ofSubmonoid (S : Submonoid (Matrix κ κ ℂ)) (hS : IsClosed (S : Set (Matrix κ κ ℂ))) :
    GlobalGaugeGroup κ where
  toSubgroup := S.units
  isClosed' := (hS.preimage Units.continuous_val).inter (hS.preimage Units.continuous_coe_inv)

lemma mem_ofSubmonoid_iff {S : Submonoid (Matrix κ κ ℂ)} {hS : IsClosed (S : Set (Matrix κ κ ℂ))}
    {g : GeneralLinearGroup κ ℂ} :
    g ∈ (ofSubmonoid S hS).group ↔ (g : Matrix κ κ ℂ) ∈ S ∧ (↑g⁻¹ : Matrix κ κ ℂ) ∈ S :=
  Iff.rfl

/-- For unitary `S` stable under `†`, `g` lies in the group exactly when `g ∈ S`. -/
lemma mem_ofSubmonoid_iff_of_star_mem {S : Submonoid (Matrix κ κ ℂ)}
    {hS : IsClosed (S : Set (Matrix κ κ ℂ))} (hU : S ≤ unitaryGroup κ ℂ)
    (hstar : ∀ A ∈ S, star A ∈ S) {g : GeneralLinearGroup κ ℂ} :
    g ∈ (ofSubmonoid S hS).group ↔ (g : Matrix κ κ ℂ) ∈ S := by
  refine ⟨fun h => h.1, fun h => mem_ofSubmonoid_iff.2 ⟨h, ?_⟩⟩
  rw [Units.inv_eq_of_mul_eq_one_left ((mem_unitaryGroup_iff' (α := ℂ)).1 (hU h))]
  exact hstar _ h

end GlobalGaugeGroup
