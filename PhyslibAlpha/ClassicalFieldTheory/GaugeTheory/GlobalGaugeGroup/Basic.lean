/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

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

The global gauge group of a gauge theory is presented here as a closed subgroup `G` of the
general linear group `GL(κ, ℂ)`. These are the matrix Lie groups. They include every compact
Lie group, so every gauge group of the Standard Model and its extensions, as well as
non-compact groups such as `Sp(2n, ℝ)`, `SO(p, q)`, `SL(n, ℝ)` and the Lorentz group,
disconnected groups such as `O(n)`, and finite groups. A real group sits inside `GL(κ, ℂ)` as
the real matrices it contains. Lie groups with no faithful finite-dimensional
representation, such as the metaplectic group, are not covered.

Most groups of physical interest are cut out of the matrices by closed conditions, such as
unitarity, a determinant or an invariant bilinear form. Such conditions define a closed
submonoid of matrices, and its invertible elements whose inverses also satisfy the conditions
form a global gauge group, `GlobalGaugeGroup.ofSubmonoid`. The special cases `U(1)`, `SU(n)`,
`SO(n)` and `Sp(n)` are built this way in the files `SO.lean`, `SU.lean`, `Sp.lean` and `U1.lean`.

The Lie algebra of a global gauge group is in the `LieAlgebra` directory.

## ii. Key results

- `GlobalGaugeGroup` : a closed subgroup of a general linear group.
- `GlobalGaugeGroup.ofSubmonoid` : the global gauge group of the invertible elements of a
  closed submonoid of matrices.

## iii. Table of contents

- A. The structure
- B. Global gauge groups from closed submonoids of matrices

## iv. References

* yang-mills-group, *OpenAI-YM-20261028*, `PublicTheory.lean`, the structure `GaugeGroup`,
  https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/PublicTheory.lean#L22-L33

-/

@[expose] public section

open Matrix

/-!

## A. The structure

-/

/-- A global gauge group, a closed subgroup of the general linear group `GL(κ, ℂ)`. -/
structure GlobalGaugeGroup (κ : Type) [Fintype κ] [DecidableEq κ] where
  /-- The group, as a subgroup of the general linear group. -/
  group : Subgroup (GeneralLinearGroup κ ℂ)
  /-- The group is closed in the general linear group. -/
  isClosed : IsClosed (group : Set (GeneralLinearGroup κ ℂ))

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-!

## B. Global gauge groups from closed submonoids of matrices

-/

/-- The global gauge group of a closed submonoid `S` of matrices. Its elements are the
  invertible matrices which lie in `S` together with their inverses. -/
def ofSubmonoid (S : Submonoid (Matrix κ κ ℂ)) (hS : IsClosed (S : Set (Matrix κ κ ℂ))) :
    GlobalGaugeGroup κ where
  group := S.units
  isClosed := (hS.preimage Units.continuous_val).inter (hS.preimage Units.continuous_coe_inv)

lemma mem_ofSubmonoid_iff {S : Submonoid (Matrix κ κ ℂ)} {hS : IsClosed (S : Set (Matrix κ κ ℂ))}
    {g : GeneralLinearGroup κ ℂ} :
    g ∈ (ofSubmonoid S hS).group ↔ (g : Matrix κ κ ℂ) ∈ S ∧ (↑g⁻¹ : Matrix κ κ ℂ) ∈ S :=
  Iff.rfl

/-- For a submonoid of unitary matrices closed under the conjugate transpose, an invertible
  matrix lies in its global gauge group exactly when it lies in the submonoid, since its
  inverse is then its conjugate transpose. -/
lemma mem_ofSubmonoid_iff_of_star_mem {S : Submonoid (Matrix κ κ ℂ)}
    {hS : IsClosed (S : Set (Matrix κ κ ℂ))} (hU : S ≤ unitaryGroup κ ℂ)
    (hstar : ∀ A ∈ S, star A ∈ S) {g : GeneralLinearGroup κ ℂ} :
    g ∈ (ofSubmonoid S hS).group ↔ (g : Matrix κ κ ℂ) ∈ S := by
  refine ⟨fun h => h.1, fun h => mem_ofSubmonoid_iff.2 ⟨h, ?_⟩⟩
  rw [Units.inv_eq_of_mul_eq_one_left ((mem_unitaryGroup_iff' (α := ℂ)).1 (hU h))]
  exact hstar _ h

/-- The group structure of a global gauge group, recorded directly so that instance search
  does not pass through the units of the matrices. -/
instance (G : GlobalGaugeGroup κ) : Group G.group := inferInstance

end GlobalGaugeGroup
