/-
Copyright (c) 2026 Nicolas Rouquette. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
module

public import Physlib.Units.Basic
/-!

# The unit side, parametrised in the same basis

The dimension basis is parametric (`Dimension B`), but the *unit* side of the
bridge is hardwired in parallel: `LTMCTUnitChoices` has five named unit fields and
`LTMCTUnitChoices.dimScale` folds over exactly those five. This module provides the
generic twin, parametrised in the same basis `B`.

Every PhysLib base unit (`LengthUnit`, `TimeUnit`, …) is, structurally, a positive
real (`{ val : ℝ // 0 < val }`); the typed names carry no extra algebraic content.
So a unit choice over a basis `B` is a positive real per base dimension, and the
scaling homomorphism folds the per-base unit ratio over `B`:

* `UnitScale B` — a positive-real magnitude for each `b : B`.
* `UnitScale.dimScale : UnitScale B → UnitScale B → Dimension B →* ℝ≥0` — the
  `MonoidHom` `d ↦ ∏ b, (u₁ b / u₂ b) ^ d.exponent b`, generic in `B`.

The current five-field `LTMCTUnitChoices.dimScale` is the `LTMCTDimensionBase` instance of this
fold, written out by hand; `LTMCTUnitChoices.toScale` exhibits the correspondence.

-/

@[expose] public section

open NNReal
open scoped BigOperators

/-- A choice of unit for each base dimension of `B`: a positive-real magnitude per
  base. This is the basis-generic form of `LTMCTUnitChoices`. -/
@[ext]
structure UnitScale (B : Type) where
  /-- The positive-real magnitude of the chosen unit at each base dimension. -/
  scale : B → ℝ≥0
  /-- Each chosen unit has a positive magnitude. -/
  scale_pos : ∀ b, 0 < scale b

namespace UnitScale

variable {B : Type}

lemma ratio_ne_zero (u1 u2 : UnitScale B) (b : B) : u1.scale b / u2.scale b ≠ 0 :=
  (div_pos (u1.scale_pos b) (u2.scale_pos b)).ne'

/-- The dimension-scaling homomorphism, generic in the basis `B`: a quantity of
  dimension `d` rescales by `∏ b, (u1 b / u2 b) ^ d.exponent b` when changing the
  unit choice from `u1` to `u2`. This is the basis-generic form of
  `LTMCTUnitChoices.dimScale`. -/
noncomputable def dimScale [DimensionBasis B] [Fintype B]
    (u1 u2 : UnitScale B) : Dimension B →* ℝ≥0 where
  toFun d := ∏ b, (u1.scale b / u2.scale b) ^ (d.exponent b : ℝ)
  map_one' := by simp
  map_mul' d1 d2 := by
    simp only [Dimension.mul_exponent, Dimension.Exponent.coe_add, Rat.cast_add]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun b _ =>
      NNReal.rpow_add (u1.ratio_ne_zero u2 b) _ _

@[simp]
lemma dimScale_self [DimensionBasis B] [Fintype B] (u : UnitScale B) (d : Dimension B) :
    dimScale u u d = 1 := by
  simp only [dimScale, MonoidHom.coe_mk, OneHom.coe_mk]
  refine Finset.prod_eq_one fun b _ => ?_
  rw [div_self (u.scale_pos b).ne', NNReal.one_rpow]

@[simp]
lemma dimScale_one [DimensionBasis B] [Fintype B] (u1 u2 : UnitScale B) :
    dimScale u1 u2 1 = 1 := map_one _

/-- The scaling is transitive (a cocycle in the unit choices). -/
lemma dimScale_transitive [DimensionBasis B] [Fintype B]
    (u1 u2 u3 : UnitScale B) (d : Dimension B) :
    dimScale u1 u2 d * dimScale u2 u3 d = dimScale u1 u3 d := by
  simp only [dimScale, MonoidHom.coe_mk, OneHom.coe_mk, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← NNReal.mul_rpow]
  congr 1
  rw [div_mul_div_comm, mul_comm (u2.scale b), mul_div_mul_right _ _ (u2.scale_pos b).ne']

end UnitScale

/-!
## The current five-field `LTMCTUnitChoices` is the `LTMCTDimensionBase` instance

`LTMCTUnitChoices.toScale` reads the five typed units as a `UnitScale LTMCTDimensionBase`,
exhibiting the existing bespoke `dimScale` as the `LTMCTDimensionBase` case of the generic
fold.
-/

namespace LTMCTUnitChoices

/-- Read a five-field `LTMCTUnitChoices` as a `UnitScale` over `LTMCTDimensionBase`. -/
noncomputable def toScale (u : LTMCTUnitChoices) : UnitScale LTMCTDimensionBase where
  scale
    | .length => ⟨u.length.val, u.length.property.le⟩
    | .time => ⟨u.time.val, u.time.property.le⟩
    | .mass => ⟨u.mass.val, u.mass.property.le⟩
    | .charge => ⟨u.charge.val, u.charge.property.le⟩
    | .temperature => ⟨u.temperature.val, u.temperature.property.le⟩
  scale_pos b := by
    cases b
    · exact NNReal.coe_pos.mp u.length.property
    · exact NNReal.coe_pos.mp u.time.property
    · exact NNReal.coe_pos.mp u.mass.property
    · exact NNReal.coe_pos.mp u.charge.property
    · exact NNReal.coe_pos.mp u.temperature.property

end LTMCTUnitChoices
