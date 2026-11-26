/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Physlib.Electromagnetism.Kinematics.FieldStrength
public import PhyslibAlpha.Relativity.Tensors.Tensor2

/-!

# Electromagnetic field-strength coordinate components

Component bridge `emFieldStrengthComponents` extracting a `Tensor2 4` from Physlib's
coordinate-free electromagnetic field strength `ElectromagneticPotential.toFieldStrength`.

## i. Overview

In four-dimensional inertial Minkowski coordinates indexed by `Fin 4`, `emFieldStrengthComponents`
translates Physlib's `Electromagnetism.ElectromagneticPotential.toFieldStrength` via
`finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4` into `Tensor2 4`, and inherits antisymmetry
`F_{ij} = -F_{ji}` from `toFieldStrength_eval_antisymm`.

## ii. Key results

- `emFieldStrengthComponents` : `Tensor2 4` components of `A.toFieldStrength x`.
- `emFieldStrengthComponents_antisymm` : antisymmetry `F_{ij} = -F_{ji}`.

## iii. Table of contents

- A. Bridge to Physlib's `ElectromagneticPotential.toFieldStrength`

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 4 (Sec. 4.3). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 3 & Ch. 5.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 4
  (https://arxiv.org/pdf/gr-qc/9712019#page=109). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Bridge to Physlib's `ElectromagneticPotential.toFieldStrength`

Reindexing Physlib's electromagnetic field strength tensor maps coordinate components into
`Tensor2 4` while preserving antisymmetry.

-/

open TensorSpecies Tensor Tensorial

/-- Extract the coordinate components `Tensor2 4` of Physlib's electromagnetic field-strength
tensor `A.toFieldStrength x` via the index equivalence `finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4`. -/
noncomputable def emFieldStrengthComponents (A : Electromagnetism.ElectromagneticPotential 3)
    (x : SpaceTime 3) : Tensor2 4 :=
  fun i j => Tensor.toScalar
    {A.toFieldStrength x | [finSumFinEquiv.symm i] [finSumFinEquiv.symm j]}ᵀ

/-- Componentwise antisymmetry of `emFieldStrengthComponents`, inherited from
`ElectromagneticPotential.toFieldStrength_eval_antisymm`. -/
lemma emFieldStrengthComponents_antisymm (A : Electromagnetism.ElectromagneticPotential 3)
    (x : SpaceTime 3) (i j : Fin 4) :
    emFieldStrengthComponents A x i j = -emFieldStrengthComponents A x j i :=
  Electromagnetism.ElectromagneticPotential.toFieldStrength_eval_antisymm A x _ _

end GeneralRelativity
