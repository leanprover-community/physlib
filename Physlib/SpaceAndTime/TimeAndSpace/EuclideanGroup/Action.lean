/-
Copyright (c) 2026 Rob Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob Sneiderman
-/
module

public import Physlib.SpaceAndTime.Space.EuclideanGroup.Action
public import Physlib.SpaceAndTime.TimeAndSpace.Basic
/-!

# The action of the Euclidean group on `TimeAndSpace`

## i. Overview

In this file we define the action of the Euclidean group on `TimeAndSpace d`. The action fixes
the time coordinate and acts on the space coordinate by the usual Euclidean-group action on
`Space d`.

## ii. Key results

- `TimeAndSpace.instMulActionEuclideanGroup` : The action of the Euclidean group on
  `TimeAndSpace d`.
- `TimeAndSpace.dist_smul` : The Euclidean group action on `TimeAndSpace d` preserves distance.
- `TimeAndSpace.smul_hasTemperateGrowth` : The Euclidean group action has temperate growth.
- `TimeAndSpace.antilipschitz_smul` : The Euclidean group action is antilipschitz.

## iii. Table of contents

- A. The Euclidean group action
- B. Temperate growth of the coordinate action

## iv. References

* None.
-/

@[expose] public section

namespace TimeAndSpace

variable {d : ℕ}

/-!

## A. The Euclidean group action

-/

/-- The Euclidean group acts on `TimeAndSpace d` by fixing time and acting on space. -/
noncomputable instance instMulActionEuclideanGroup :
    MulAction (EuclideanGroup d) (TimeAndSpace d) where
  smul g tx := (tx.1, g • tx.2)
  one_smul tx := by
    rcases tx with ⟨t, x⟩
    show ((t, (1 : EuclideanGroup d) • x) : TimeAndSpace d) = (t, x)
    simp
  mul_smul g h tx := by
    rcases tx with ⟨t, x⟩
    show ((t, (g * h) • x) : TimeAndSpace d) = (t, g • h • x)
    simp [mul_smul]

/-- Coordinate formula for the Euclidean-group action on `TimeAndSpace d`. -/
@[simp]
lemma smul_mk (g : EuclideanGroup d) (t : Time) (x : Space d) :
    g • ((t, x) : TimeAndSpace d) = (t, g • x) := by
  show ((t, g • x) : TimeAndSpace d) = (t, g • x)
  rfl

/-- The Euclidean-group action fixes the first coordinate. -/
@[simp]
lemma fst_smul (g : EuclideanGroup d) (tx : TimeAndSpace d) :
    (g • tx).1 = tx.1 := by
  rcases tx with ⟨t, x⟩
  rw [smul_mk]

/-- The Euclidean-group action applies to the second coordinate. -/
@[simp]
lemma snd_smul (g : EuclideanGroup d) (tx : TimeAndSpace d) :
    (g • tx).2 = g • tx.2 := by
  rcases tx with ⟨t, x⟩
  rw [smul_mk]

/-- The Euclidean-group action fixes the time projection. -/
lemma time_smul (g : EuclideanGroup d) (tx : TimeAndSpace d) :
    time (g • tx) = time tx := by
  simp [time]

/-- The Euclidean-group action applies to the space projection. -/
lemma space_smul (g : EuclideanGroup d) (tx : TimeAndSpace d) :
    space (g • tx) = g • space tx := by
  simp [space]

/-- The Euclidean-group action on `TimeAndSpace d` preserves product distance. -/
lemma dist_smul (g : EuclideanGroup d) (tx ty : TimeAndSpace d) :
    dist (g • tx) (g • ty) = dist tx ty := by
  rcases tx with ⟨t, x⟩
  rcases ty with ⟨t', x'⟩
  show dist ((t, g • x) : TimeAndSpace d) (t', g • x') = dist (t, x) (t', x')
  rw [Prod.dist_eq, Prod.dist_eq, EuclideanGroup.dist_smul]

/-!

## B. Temperate growth of the coordinate action

-/

/-- The linear part of the Euclidean-group action on `TimeAndSpace d`. -/
noncomputable def actionLinearMap (g : EuclideanGroup d) :
    TimeAndSpace d →L[ℝ] TimeAndSpace d :=
  ContinuousLinearMap.prod (ContinuousLinearMap.fst ℝ Time (Space d))
    (Space.basis.repr.symm.toContinuousLinearMap.comp
      ((EuclideanGroup.orthogonalToLinearIsometryEquiv g.linear).toContinuousLinearMap.comp
        (Space.basis.repr.toContinuousLinearMap.comp
          (ContinuousLinearMap.snd ℝ Time (Space d)))))

/-- The translation part of the Euclidean-group action on `TimeAndSpace d`. -/
noncomputable def actionTranslation (g : EuclideanGroup d) : TimeAndSpace d :=
  (0, Space.basis.repr.symm g.translation)

lemma smul_eq_actionLinearMap_add (g : EuclideanGroup d) (tx : TimeAndSpace d) :
    g • tx = actionLinearMap g tx + actionTranslation g := by
  refine Prod.ext ?_ ?_
  · simp [actionLinearMap, actionTranslation]
  · ext i
    have hx : tx.2 -ᵥ (0 : Space d) = Space.basis.repr tx.2 := by
      ext j
      simp [Space.vsub_apply, Space.zero_apply, Space.basis_repr_apply]
    rw [TimeAndSpace.snd_smul, EuclideanGroup.smul_apply]
    simp [actionLinearMap, actionTranslation, hx, Space.add_apply, Space.basis_repr_symm_apply]

/-- The Euclidean-group action on `TimeAndSpace d` has temperate growth. -/
lemma smul_hasTemperateGrowth (g : EuclideanGroup d) :
    Function.HasTemperateGrowth (fun tx : TimeAndSpace d => g • tx) := by
  have hfun : (fun tx : TimeAndSpace d => g • tx) =
      fun tx => actionLinearMap g tx + actionTranslation g := by
    funext tx
    exact smul_eq_actionLinearMap_add g tx
  rw [hfun]
  exact Function.HasTemperateGrowth.add (actionLinearMap g).hasTemperateGrowth
    (Function.HasTemperateGrowth.const (actionTranslation g))

/-- The Euclidean-group action on `TimeAndSpace d` is an isometry. -/
lemma isometry_smul (g : EuclideanGroup d) :
    Isometry (fun tx : TimeAndSpace d => g • tx) :=
  Isometry.of_dist_eq (TimeAndSpace.dist_smul g)

/-- The Euclidean-group action on `TimeAndSpace d` is antilipschitz. -/
lemma antilipschitz_smul (g : EuclideanGroup d) :
    AntilipschitzWith 1 (fun tx : TimeAndSpace d => g • tx) :=
  (isometry_smul g).antilipschitzWith

end TimeAndSpace
