/-
Copyright (c) 2026 Michał Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mogielnicki
-/

import PhysLean.FluidMechanics.IdealFluid.Basic
import PhysLean.Mathematics.Calculus.Divergence

/-!
This module introduces:
steady flow,
... (still under construction)
-/

open scoped InnerProductSpace
open Time
open Space

namespace IdealFluid

/-- Determines whether a flow is steady -/
def isSteady (F: IdealFluid) :
    Prop :=
      ∀ (t : Time) (pos : Space), ∂ₜ (fun t' => IdealFluid.velocity F t' pos) t = 0

/-- Determines whether a flow is isentropic -/
def isIsentropic (F: IdealFluid):
    Prop :=
      ∀ (t: Time) (pos: Space), ∂ₜ (fun t' => IdealFluid.entropy F t' pos) t = 0

-- TODO: Provide the Bernoulli's equation (after fun derivatoins)

end IdealFluid
