/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import Physlib.ClassicalFieldTheory.Local.Variation
/-!
# Alpha extensions for admissible local variations

Euclidean components of admissible variations are test functions.

## i. Overview

This module adds the Euclidean component API needed by the coordinate-readout CFT stack in
`PhyslibAlpha`.

The underlying `AdmissibleVariation` structure remains the maintained one from `Physlib`; this file
only adds helper lemmas used by the Alpha development.

## ii. Key results

- `ClassicalFieldTheory.Local.AdmissibleVariation.coord_euclidean` : a Euclidean component of an
  admissible variation is again a test function.

## iii. Table of contents

- A. Euclidean components of admissible variations

## iv. References

* None.

-/

@[expose] public section

open Physlib

namespace ClassicalFieldTheory
namespace Local

/-!

## A. Euclidean components of admissible variations

-/

namespace AdmissibleVariation

variable {d m : ℕ}

/-- A Euclidean component of an admissible variation is again a test function. -/
@[fun_prop]
lemma coord_euclidean (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) (a : Fin m) :
    IsTestFunction (fun x => (η.toFun x) a) := by
  exact η.isTestFunction.comp_left (g := fun v : EuclideanSpace ℝ (Fin m) => v a)
    (by simp) (by fun_prop)

end AdmissibleVariation

end Local
end ClassicalFieldTheory
