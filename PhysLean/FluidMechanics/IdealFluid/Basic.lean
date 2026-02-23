/-
Copyright (c) 2026 Michał Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mogielnicki
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import PhysLean.SpaceAndTime.Space.Basic
import PhysLean.SpaceAndTime.Time.Basic
/-!
This module introduces the idea of an ideal fluid and the mass flux density
and basic physical properties, meant to be later used for proofs.
-/
open scoped InnerProductSpace

structure IdealFluid where
  density: Time → Space → ℝ
  velocity: Time → Space → EuclideanSpace ℝ (Fin 3)
  pressure: Time → Space → ℝ

  entropy: Time → Space → ℝ
  enthlapy: Time → Space → ℝ

  density_pos: ∀ t, pos 0 < density t pos

  /-- Ensuring that all are differentiable for more complex equations. -/
  density_contdiff: ContDiff ℝ 1 ( fun(s:Time × Space)=>density s.1 s.2)
  velocity_contdiff: ContDiff ℝ 1 ( fun(s:Time × Space)=>velocity s.1 s.2)
  pressure_contdiff: ContDiff ℝ 1 ( fun(s:Time × Space)=>pressure s.1 s.2)

  entropy_contdiff: ContDiff ℝ 1 ( fun(s:Time × Space)=>entropy s.1 s.2)
  enthlapy_contdiff: ContDiff ℝ 1 ( fun(s:Time × Space)=>enthlapy s.1 s.2)

namespace IdealFluid

/-!
Here lays defined:
  the mass flux density
  entropy flux density
  energy flux density
  flow out of a volume
-/

def massFluxDensity (F: IdealFluid) (t: Time) (pos: Space):
    EuclideanSpace ℝ (Fin 3) :=
     (IdealFluid.density F t pos) • (IdealFluid.velocity F t pos)

def entropyFluxDensity (F: IdealFluid) (t: Time) (pos: Space):
    EuclideanSpace ℝ (Fin 3) :=
      (IdealFluid.entropy F t pos) • (IdealFluid.density F t pos) • (IdealFluid.velocity F t pos)

noncomputable def energyFluxDensity (F: IdealFluid) (t: Time) (pos: Space):
    EuclideanSpace ℝ (Fin 3) :=
      let w := IdealFluid.enthlapy F t pos
      let v := IdealFluid.velocity F t pos
      let v_sq: ℝ := ⟪v,v⟫_ℝ
      let scalar := (IdealFluid.density F t pos)*(0.5*v_sq + w)

      scalar • v

/-Still a need to introduce flow out of volume-/

end IdealFluid
