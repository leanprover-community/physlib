/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.WaveEquation.Basic

/-!

# The Klein–Gordon equation

This file sets up the Klein–Gordon equation on spacetime for smooth fields and for distributions.

## i. Overview

Spacetime is `SpaceTime d` with the speed of light equal to one. The operator `operator m` is the
wave operator plus `m ^ 2` on smooth fields. The mass parameter `m` is any real number. The
operator does not enlarge support, so `equation m` packages it as a local operator. The operator
extends to distributions as `distributionOperator m`. The file `Solution` states the solution.

## ii. Key results

- `operator` : the Klein–Gordon operator on smooth fields.
- `equation` : the Klein–Gordon operator as a local operator.
- `distributionOperator` : the Klein–Gordon operator on distributions.
- `testOperator` : the Klein–Gordon operator on compactly supported smooth test functions.

## iii. Table of contents

- A. The operator on smooth fields
- B. The operator on distributions

## iv. References

None.

## A. The operator on smooth fields

`operator m` is `smoothWaveOperator + m ^ 2 • id`. The mass enters as a zeroth order term. The
field type and the dimension are unchanged. `equation m` records that the operator does not
enlarge support.

## B. The operator on distributions

`distributionOperator m` is the wave operator plus `m ^ 2` on `DistributionField d V`. On a test
function it is given by the same operator `testOperator m`, and `distributionOperator_apply`
states this.
-/

@[expose] public section

noncomputable section

open Minkowski WaveEquation

namespace KleinGordon.Spacetime

section
variable {d : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The massive wave operator, with mass measured in inverse spacetime-length units. -/
def operator (m : ℝ) : smoothFields d V →ₗ[ℝ] smoothFields d V :=
  smoothWaveOperator + (m ^ 2) • LinearMap.id

/-- Klein–Gordon is a local equation on the existing smooth spacetime field class. -/
def equation (m : ℝ) : LocalOperator (smoothFields d V) where
  operator := operator m
  support_operator u := (tsupport_add _ _).trans (Set.union_subset
    (smoothWaveOperator_support u) (tsupport_smul_subset_right (fun _ => m ^ 2) _))

/-- The Klein–Gordon operator on native distributions. -/
def distributionOperator (m : ℝ) : DistributionField d V →L[ℝ] DistributionField d V :=
  distributionWaveOperator + (m ^ 2) • ContinuousLinearMap.id ℝ _

/-- The Klein–Gordon operator on native compact smooth test functions. -/
def testOperator (m : ℝ) :
    _root_.TestFunction (⊤ : TopologicalSpace.Opens (SpaceTime d)) ℝ ⊤ →L[ℝ]
      _root_.TestFunction (⊤ : TopologicalSpace.Opens (SpaceTime d)) ℝ ⊤ :=
  testWaveOperator + (m ^ 2) • ContinuousLinearMap.id ℝ _

/-- The positive second-order operator has the same transpose on test functions. -/
lemma distributionOperator_apply (m : ℝ) (T : DistributionField d V)
    (φ : _root_.TestFunction (⊤ : TopologicalSpace.Opens (SpaceTime d)) ℝ ⊤) :
    distributionOperator m T φ = T (testOperator m φ) := by
  simp only [distributionOperator, testOperator, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, distributionWaveOperator_apply, map_add, map_smul]
end

end KleinGordon.Spacetime
