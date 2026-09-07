/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeBosons.AlgebraValued.Basic
public import Physlib.Particles.StandardModel.GaugeBosons.AlgebraValued.TransformsInAdjoint
public import Physlib.Particles.StandardModel.GaugeBosons.AlgebraValued.FieldStrength
public import Physlib.Particles.StandardModel.GaugeGroup.MaurerCartan.Truncation
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Free
/-!

# Algebra valued field strength

-/

@[expose] public section

namespace StandardModel
open Matrix MatrixGroups TensorProduct MvPowerSeries
variable {B : Type} [Ring B] [Algebra ℂ B]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

end StandardModel
