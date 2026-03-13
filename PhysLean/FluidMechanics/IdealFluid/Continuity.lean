/-
Copyright (c) 2026 Michał Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mogielnicki
-/

import PhysLean.FluidMechanics.IdealFluid.Basic
import PhysLean.Mathematics.Calculus.Divergence

/-!
This module introduces the continuity criterium.
There is potential to add various different lemmas expanding on this.
-/

open scoped InnerProductSpace
open Time
open Space

namespace IdealFluid

/-- defining satisfying the equation of continuity -/
def satisfiesContinuity (F : IdealFluid):
    Prop :=
      ∀ (t : Time) (pos : Space),
      ∂ₜ (fun t' => IdealFluid.density F t' pos) t +
      Space.div (fun pos' => IdealFluid.massFluxDensity F t pos') pos = 0


-- TODO: Add lemmas for continuity with different models.
-- TODO: Add definition and lemmas for Incompressibility.

end IdealFluid
