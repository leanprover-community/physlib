/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube.Basic
public import PhyslibAlpha.CondensedMatter.TightBindingChain.MaxCurrentState.FluctuationAngle
/-!

# The volumetric quantum of the open tight binding cube

## i. Overview

A cube `Nx × Ny × Nz` carries one constant `C` per axis (`uncertaintyRatio_alongX`,
`uncertaintyRatio_alongY`, `uncertaintyRatio_alongZ`), so its volumetric quantum is the product
`δ(Nx) δ(Ny) δ(Nz)` of the dimensional quanta `δ = C - 1` of its axes: it vanishes iff some axis
has `2` or `3` sites, is positive from `4 × 4 × 4` on, grows strictly in each axis and stays
below `(√(π² / 3 - 2) - 1)³`.

## ii. Key results

- `volQuantum` : the volumetric quantum `δ(Nx) δ(Ny) δ(Nz)` of the cube.
- `volQuantum_eq_zero_iff`, `volQuantum_pos` : it vanishes iff some axis has `2` or `3` sites.
- `volQuantum_lt_volQuantum_x` (and `y`, `z`), `volQuantum_lt` : strict growth in each axis,
  below its limit.

## iii. Table of contents

- A. The volumetric quantum

## iv. References

* H. P. Robertson, *A general formulation of the uncertainty principle and its classical
  interpretation*, Phys. Rev. 35 (1930) 667.

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open ProbabilisticTheory UnitalPositiveLinearMap

/-!

## A. The volumetric quantum

-/

variable (Tx Ty Tz : TightBindingChain)

/-- The volumetric quantum of the cube `Nx × Ny × Nz`: the product of the dimensional quanta of
its axes, each axis carrying its own `C` (`uncertaintyRatio_alongX`, `uncertaintyRatio_alongY`,
`uncertaintyRatio_alongZ`). -/
noncomputable def volQuantum : ℝ := Tx.dimQuantum * Ty.dimQuantum * Tz.dimQuantum

variable {Tx Ty Tz}

/-- The volumetric quantum vanishes iff some axis has `2` or `3` sites. -/
lemma volQuantum_eq_zero_iff (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 2 ≤ Tx.N) (hNy : 2 ≤ Ty.N) (hNz : 2 ≤ Tz.N) :
    volQuantum Tx Ty Tz = 0 ↔
      (Tx.N = 2 ∨ Tx.N = 3) ∨ (Ty.N = 2 ∨ Ty.N = 3) ∨ (Tz.N = 2 ∨ Tz.N = 3) := by
  rw [volQuantum, mul_eq_zero, mul_eq_zero, Tx.dimQuantum_eq_zero_iff hx hNx,
    Ty.dimQuantum_eq_zero_iff hy hNy, Tz.dimQuantum_eq_zero_iff hz hNz, or_assoc]

/-- From `4 × 4 × 4` on, the volumetric quantum is positive. -/
lemma volQuantum_pos (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) : 0 < volQuantum Tx Ty Tz :=
  mul_pos (mul_pos (Tx.dimQuantum_pos hx hNx) (Ty.dimQuantum_pos hy hNy))
    (Tz.dimQuantum_pos hz hNz)

/-- From `4 × 4 × 4` on, the volumetric quantum grows strictly along `x`. -/
lemma volQuantum_lt_volQuantum_x {Tx' : TightBindingChain} (hx : Tx.t ≠ 0) (hx' : Tx'.t ≠ 0)
    (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0) (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N)
    (h : Tx.N < Tx'.N) : volQuantum Tx Ty Tz < volQuantum Tx' Ty Tz := by
  have := Ty.dimQuantum_pos hy hNy
  have := Tz.dimQuantum_pos hz hNz
  unfold volQuantum
  gcongr
  exact dimQuantum_lt_dimQuantum hx hx' hNx h

/-- From `4 × 4 × 4` on, the volumetric quantum grows strictly along `y`. -/
lemma volQuantum_lt_volQuantum_y {Ty' : TightBindingChain} (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0)
    (hy' : Ty'.t ≠ 0) (hz : Tz.t ≠ 0) (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N)
    (h : Ty.N < Ty'.N) : volQuantum Tx Ty Tz < volQuantum Tx Ty' Tz := by
  have := Tx.dimQuantum_pos hx hNx
  have := Tz.dimQuantum_pos hz hNz
  unfold volQuantum
  gcongr
  exact dimQuantum_lt_dimQuantum hy hy' hNy h

/-- From `4 × 4 × 4` on, the volumetric quantum grows strictly along `z`. -/
lemma volQuantum_lt_volQuantum_z {Tz' : TightBindingChain} (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0)
    (hz : Tz.t ≠ 0) (hz' : Tz'.t ≠ 0) (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N)
    (h : Tz.N < Tz'.N) : volQuantum Tx Ty Tz < volQuantum Tx Ty Tz' := by
  have := Tx.dimQuantum_pos hx hNx
  have := Ty.dimQuantum_pos hy hNy
  unfold volQuantum
  gcongr
  exact dimQuantum_lt_dimQuantum hz hz' hNz h

/-- From `4 × 4 × 4` on, the volumetric quantum stays below `(√(π² / 3 - 2) - 1)³`. -/
lemma volQuantum_lt (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) :
    volQuantum Tx Ty Tz < (√(Real.pi ^ 2 / 3 - 2) - 1) ^ 3 := by
  have := Tx.dimQuantum_pos hx hNx
  have := Ty.dimQuantum_pos hy hNy
  have := Tz.dimQuantum_pos hz hNz
  rw [volQuantum, pow_three, ← mul_assoc]
  gcongr
  · exact Tx.dimQuantum_lt hx hNx
  · exact Ty.dimQuantum_lt hy hNy
  · exact Tz.dimQuantum_lt hz hNz

end TightBindingChain
end CondensedMatter
