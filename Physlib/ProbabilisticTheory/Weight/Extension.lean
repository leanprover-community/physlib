/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Weight.Basic
public import Physlib.ProbabilisticTheory.OrderUnit.ConeExtension

/-!
# Extending finite weights

Finite weights extend to real-linear functionals on all observables.

## i. Overview

Take the real value of a finite weight on positive observables, then use the common linear
extension from the positive cone.

## ii. Key results

- `Weight.IsFinite.toLinearMap` : extend a finite weight to all observables.

## iii. Table of contents

- A. Extending finite weights

## iv. References

-/

@[expose] public section

open ProbabilisticTheory
open scoped NNReal

/-! ## A. Extending finite weights -/

namespace Weight

variable {P : ProbabilisticTheory} {w : Weight P}

/-- A finite weight, read as a real-valued `ℝ≥0`-linear map on the positive cone. -/
noncomputable def IsFinite.toReal (hw : w.IsFinite) : PosCone P →ₗ[ℝ≥0] ℝ where
  toFun A := (w A).toReal
  map_add' := hw.toReal_map_add
  map_smul' := w.toReal_map_nnreal_smul

@[simp]
lemma IsFinite.toReal_apply (hw : w.IsFinite) (A : PosCone P) : hw.toReal A = (w A).toReal := rfl

/-- The `ℝ`-linear map extending a finite weight. -/
noncomputable def IsFinite.toLinearMap (hw : w.IsFinite) : P.Observables →ₗ[ℝ] ℝ :=
  PosCone.extend hw.toReal

@[simp]
lemma IsFinite.toLinearMap_coe (hw : w.IsFinite) (A : PosCone P) :
    hw.toLinearMap (A : P.Observables) = (w A).toReal := by
  simp [toLinearMap]

end Weight
