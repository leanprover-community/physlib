/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.LieAlgebra.Adjoint
public import Physlib.QFT.PerturbationTheory.FieldStatistics.Basic
public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Units
/-!
# Matter fields of a global gauge group

A matter field transforming under a continuous finite-dimensional representation of a global
gauge group.

## i. Overview

A matter field of a gauge theory with global gauge group `G` takes values in a
finite-dimensional complex vector space `V`, on which `G` acts through a continuous
representation `ρ : G → GL(V)` by invertible linear maps. Here `V` is a normed space, which
fixes its topology, the unique one of a finite-dimensional complex vector space, and makes the
linear maps `V →L[ℂ] V` a Banach algebra. Continuity is what lets `ρ` be differentiated to the
Lie algebra, in
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.DerivRep`,
and extended to the jets of gauge transformations, in
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.JetRep`.
As for any matter field, `V` also carries a representation of the Lorentz group, and the
field has a mass weight and a declared statistics.

## ii. Key results

- `GlobalGaugeGroup.MatterField` : a matter field transforming under a continuous
  representation of a global gauge group.

## iii. Table of contents

- A. Matter fields

## iv. References

* None.

-/

@[expose] public section

open MatrixGroups

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-!

## A. Matter fields

-/

/-- A matter field transforming under a continuous representation of the global gauge group
  `G`. It has a finite-dimensional complex normed target space `V`, the continuous
  representation `rep : G → GL(V)` by invertible linear maps, the Lorentz representation on
  `V`, the mass weight of the field (in the units in which a derivative has weight `2`), and
  its declared statistics. -/
structure MatterField (G : GlobalGaugeGroup κ) where
  /-- The target space of the field. -/
  V : Type
  [instNormedAddCommGroup : NormedAddCommGroup V]
  [instNormedSpace : NormedSpace ℂ V]
  [instFiniteDimensional : FiniteDimensional ℂ V]
  /-- The continuous representation of the global gauge group on the target space. -/
  rep : G.group →ₜ* (V →L[ℂ] V)ˣ
  /-- The representation of the Lorentz group on the target space. -/
  repLorentz : Representation ℂ SL(2,ℂ) V
  /-- The mass weight of the field. -/
  massWeight : ℕ
  /-- The statistics the field is declared to obey, bosonic or fermionic. -/
  statistic : FieldStatistic

attribute [instance] MatterField.instNormedAddCommGroup MatterField.instNormedSpace
  MatterField.instFiniteDimensional

/-- The target space of a matter field is complete, being finite-dimensional. -/
instance (G : GlobalGaugeGroup κ) (M : G.MatterField) : CompleteSpace M.V :=
  FiniteDimensional.completeSpace ℂ M.V

end GlobalGaugeGroup
