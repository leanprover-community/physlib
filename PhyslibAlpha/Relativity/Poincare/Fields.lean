/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Relativity.Poincare.Basic
public import PhyslibAlpha.SpaceAndTime.SpaceTime.Fields

/-!

# The Poincaré action on smooth fields

The Poincaré group acts on smooth fields and on compactly supported smooth fields.

## i. Overview

The action `(g • u) x = u (g⁻¹ x)` sends smooth functions to smooth functions. It is linear and
it sends the support to the image of the support. So it preserves compact support. The file
restricts the action to the submodule of smooth fields and to the submodule of test fields.

## ii. Key results

- `PoincareGroup.actSmooth` : the action as a linear map on smooth fields.
- `PoincareGroup.actTest` : the action as a linear map on test fields.
- `PoincareGroup.tsupport_actSmooth` : the support of a transformed field.

## iii. Table of contents

- A. Smooth fields
- B. Test fields

## iv. References

None.

## A. Smooth fields

- `PoincareGroup.actSmooth` : the action as a linear map on smooth fields.

## B. Test fields

- `PoincareGroup.actTest` : the action as a linear map on test fields.
-/

@[expose] public section

noncomputable section

open scoped ContDiff Pointwise
open Lorentz Minkowski

namespace PoincareGroup

variable {d : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

section Smooth

/-- The action on points is smooth. -/
lemma contDiff_smul (g : PoincareGroup d) : ContDiff ℝ ∞ fun x : SpaceTime d => g • x := by
  change ContDiff ℝ ∞ fun x : SpaceTime d => g.lorentz • x + g.translation
  exact (Vector.actionCLM g.lorentz).contDiff.add contDiff_const

/-- The action preserves smooth functions. -/
lemma contDiff_act (g : PoincareGroup d) {u : SpaceTime d → V} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (act g u) :=
  hu.comp (contDiff_smul g⁻¹)

/-- The action as a linear map on smooth fields. -/
def actSmooth (g : PoincareGroup d) : smoothFields d V →ₗ[ℝ] smoothFields d V where
  toFun u := ⟨act g u.1, contDiff_act g u.2⟩
  map_add' u v := Subtype.ext (act_add g u.1 v.1)
  map_smul' c u := Subtype.ext (act_smul g c u.1)

/-- The value of a transformed smooth field. -/
@[simp]
lemma actSmooth_coe (g : PoincareGroup d) (u : smoothFields d V) :
    (actSmooth g u : SpaceTime d → V) = act g u.1 := rfl

/-- The support of a transformed smooth field is the image of the support. -/
lemma tsupport_actSmooth (g : PoincareGroup d) (u : smoothFields d V) :
    tsupport (actSmooth g u : SpaceTime d → V) = g • tsupport (u : SpaceTime d → V) :=
  tsupport_act g u.1

/-- The identity acts trivially on smooth fields. -/
lemma actSmooth_one (u : smoothFields d V) : actSmooth (1 : PoincareGroup d) u = u :=
  Subtype.ext (act_one u.1)

/-- The action on smooth fields is a left action. -/
lemma actSmooth_mul (g h : PoincareGroup d) (u : smoothFields d V) :
    actSmooth (g * h) u = actSmooth g (actSmooth h u) :=
  Subtype.ext (act_mul g h u.1)

end Smooth

section Test

omit [NormedSpace ℝ V] in
/-- The action preserves compact support. -/
lemma hasCompactSupport_act (g : PoincareGroup d) {u : SpaceTime d → V}
    (hu : HasCompactSupport u) : HasCompactSupport (act g u) := by
  have h : act g u = u ∘ g⁻¹.toHomeomorph := rfl
  rw [h]
  exact hu.comp_homeomorph g⁻¹.toHomeomorph

/-- The action preserves test fields. -/
lemma actSmooth_mem_testField (g : PoincareGroup d) {u : smoothFields d V}
    (hu : u ∈ compactFields (smoothFields d V)) :
    actSmooth g u ∈ compactFields (smoothFields d V) :=
  hasCompactSupport_act g hu

/-- The action as a linear map on test fields. -/
def actTest (g : PoincareGroup d) : TestField d V →ₗ[ℝ] TestField d V :=
  (actSmooth g).restrict fun _ hu => actSmooth_mem_testField g hu

/-- The value of a transformed test field. -/
@[simp]
lemma actTest_coe (g : PoincareGroup d) (f : TestField d V) :
    ((actTest g f : TestField d V) : smoothFields d V) = actSmooth g f := rfl

end Test

end PoincareGroup
