/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Physlib.Relativity.SpeedOfLight
public import PhyslibAlpha.Relativity.Tensors.Tensor2

/-!

# Comoving perfect-fluid stress-energy

Perfect-fluid stress-energy tensor for a comoving observer in four dimensions.

## i. Overview

For a comoving observer `u = (-1, 0, 0, 0)`, mass density `ρ`, pressure `p`, and speed of light
`c`, the perfect-fluid stress-energy tensor is `T_{ij} = (ρ c² + p) u_i u_j + p g_{ij}`.

## ii. Key results

- `perfectFluidStressEnergy` : comoving perfect-fluid stress-energy tensor.

## iii. Table of contents

- A. Comoving perfect-fluid stress-energy

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 4 (Sec. 4.3). [ref: wald_1984_general_relativity]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 4 (Sec. 4.3)
  (https://arxiv.org/pdf/gr-qc/9712019#page=112). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Comoving perfect-fluid stress-energy

The comoving four-velocity has only a time component, so the fluid stress-energy is diagonal in
the observer frame up to the spatial metric term.

-/

/-- Comoving perfect-fluid stress-energy tensor `T_{ij} = (ρ c² + p) u_i u_j + p g_{ij}` for a
comoving observer `u = (-1, 0, 0, 0)` with speed of light `c`, mass density `ρ`, and pressure
`p`. -/
def perfectFluidStressEnergy (c : SpeedOfLight) (ρ p : ℝ) (g : Tensor2 4) : Tensor2 4 :=
  Matrix.of fun i j => (ρ * (c : ℝ) ^ 2 + p) * (if i = 0 ∧ j = 0 then 1 else 0) + p * g i j

end GeneralRelativity
