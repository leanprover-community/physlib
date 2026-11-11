/-
Copyright (c) 2026 Luca Mantani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luca Mantani
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Basic
/-!

# The unbroken gauge group

We define the gauge group `SU(3) × U(1)_EM` left unbroken by the Higgs vacuum.

## i. Overview

A non-zero Higgs vacuum breaks `SU(3) × SU(2) × U(1)` down to color and electromagnetism,
`SU(3) × U(1)_EM`. This file defines that group and its inclusion into `GaugeGroupI`.

## ii. Key results

- `UnbrokenGaugeGroupI`: The group `SU(3) × U(1)_EM`.
- `UnbrokenGaugeGroupI.incl`: Its inclusion `(h, u) ↦ (h, diag(u³, ū³), u)` into `GaugeGroupI`.

## iii. Table of contents

- A. The unbroken gauge group

## iv. References

* Peskin & Schroeder, An Introduction to QFT, chapter 20. [ref: peskin_schroeder_qft]

-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. The unbroken gauge group

-/

/-- The gauge group `SU(3) × U(1)_EM` left unbroken by the Higgs vacuum. As for `GaugeGroupI`,
  the `I` indicates that no discrete quotient is taken. -/
abbrev UnbrokenGaugeGroupI : Type := specialUnitaryGroup (Fin 3) ℂ × unitary ℂ

namespace UnbrokenGaugeGroupI

/-- The inclusion `(h, u) ↦ (h, diag(u³, ū³), u)` of `SU(3) × U(1)_EM` into `GaugeGroupI`. -/
noncomputable def incl : UnbrokenGaugeGroupI →* GaugeGroupI where
  toFun p := (p.1, GaugeGroupI.diagSU2 (p.2 ^ 3), p.2)
  map_one' := by simp
  map_mul' p q := by
    ext1 <;> simp [GaugeGroupI.toSU3, GaugeGroupI.toSU2, GaugeGroupI.toU1, mul_pow]

@[simp]
lemma incl_toSU3 (p : UnbrokenGaugeGroupI) : GaugeGroupI.toSU3 (incl p) = p.1 := rfl

@[simp]
lemma incl_toSU2 (p : UnbrokenGaugeGroupI) :
    GaugeGroupI.toSU2 (incl p) = GaugeGroupI.diagSU2 (p.2 ^ 3) := rfl

@[simp]
lemma incl_toU1 (p : UnbrokenGaugeGroupI) : GaugeGroupI.toU1 (incl p) = p.2 := rfl

end UnbrokenGaugeGroupI

end StandardModel
