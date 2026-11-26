/-
Copyright (c) 2026 Keith Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public meta import ProofWidgets.Component.HtmlDisplay
public meta import ProofWidgets.Component.Recharts
/-!

# Logarithmic correction to the entropy of a Schwarzschild black hole

Sen's one-loop coefficients of `ln a` in the entropy of a four-dimensional Schwarzschild black hole.

## i. Overview

At one loop the Euclidean gravitational path integral corrects the Bekenstein-Hawking entropy
`S_BH = A_H / (4 G ħ)` of a non-extremal black hole by a term proportional to `ln a`, where `a`
is the size of the black hole (`A_H ∼ a ^ (D - 2)`). Sen showed that the coefficient depends only
on low energy data: the trace anomaly coefficient `C_local` of the massless fields, and the
number of zero modes, which depends on the ensemble.

For uncharged black holes in `D = 4` with `n_S` scalars, `n_V` vectors, `n_F` Dirac fermions and
`n_{3/2}` spin-`3/2` fields, all massless and minimally coupled,
`C_local = (2 n_S - 26 n_V + 7 n_F - 233 / 2 n_{3/2} + 424) / 90`, the last term being the graviton
loop. The coefficient of `ln a` is then `C_local - N` where `N` counts the rotation generators
held fixed: `N = 1` (the Cartan generator) for fixed `J₃`, `N = 0` when all angular momenta are
summed, and `N = 3` when only rotation singlets are counted.

For pure gravity this gives `212 / 45`, `167 / 45` and `77 / 45`. Since `A_H = 4 π a ^ 2`, the
same correction is half the coefficient times `ln A_H`: for example `106 / 45 ln A_H` when all
angular momenta are summed.

This file records these coefficients and the change of variable between `ln a` and `ln A_H`. It
takes Sen's formulas as given; the one-loop computation itself is not formalized here.

## ii. Key results

- `MasslessFields.cLocal`: Sen's trace anomaly coefficient (1.2).
- `cLocal_pureGravity`: for pure gravity `C_local = 212 / 45`.
- `logCoeffMixed_pureGravity`, `logCoeffMicrocanonical_pureGravity`,
  `logCoeffSinglet_pureGravity`: the coefficients `212 / 45`, `167 / 45` and `77 / 45`.
- `mul_log_radius_eq_half_mul_log_area`: `c ln a = (c / 2) ln A_H` up to a constant.
- `logCoeffMixed_pureGravity_area`: the coefficient of `ln A_H` is `106 / 45`.

## iii. Table of contents

- A. Massless field content and the trace anomaly coefficient
- B. The coefficient of `ln a` in each ensemble
  - B.1. Definitions in `D` dimensions
  - B.2. Pure gravity in four dimensions
- C. From the size `a` to the horizon area
- D. Visualization

## iv. References

- A. Sen, "Logarithmic Corrections to Schwarzschild and Other Non-extremal Black Hole Entropy in
  Different Dimensions", JHEP 04 (2013) 156, arXiv:1205.0971. Equations (1.1), (1.2), (1.4),
  (1.5) and the paragraph following (1.5).

-/

@[expose] public section

namespace GeneralRelativity

namespace SchwarzschildLogCorrection

/-!

## A. Massless field content and the trace anomaly coefficient

-/

/-- The numbers of massless fields minimally coupled to gravity, besides the graviton:
  scalars, vectors, Dirac fermions and spin-`3/2` fields. -/
structure MasslessFields where
  /-- The number of massless scalar fields. -/
  nS : ℕ
  /-- The number of massless vector fields. -/
  nV : ℕ
  /-- The number of massless Dirac fields. -/
  nF : ℕ
  /-- The number of massless spin-`3/2` fields. -/
  nRS : ℕ

namespace MasslessFields

/-- Sen's coefficient `C_local` for an uncharged black hole in four dimensions, (1.2) of
  arXiv:1205.0971. The term `424` is the contribution of the graviton loop. -/
def cLocal (f : MasslessFields) : ℚ :=
  (2 * f.nS - 26 * f.nV + 7 * f.nF - 233 / 2 * f.nRS + 424) / 90

/-- Pure gravity: no massless fields besides the graviton. -/
def pureGravity : MasslessFields := ⟨0, 0, 0, 0⟩

lemma cLocal_pureGravity : pureGravity.cLocal = 212 / 45 := by
  norm_num [cLocal, pureGravity]

end MasslessFields

/-!

## B. The coefficient of `ln a` in each ensemble

### B.1. Definitions in `D` dimensions

-/

/-- The number `N_C = ⌊(D - 1) / 2⌋` of Cartan generators of the rotation group `SO(D - 1)`. -/
def numCartan (D : ℕ) : ℕ := (D - 1) / 2

/-- The number `N_R = (D - 1)(D - 2) / 2` of generators of the rotation group `SO(D - 1)`. -/
def numRotations (D : ℕ) : ℕ := (D - 1) * (D - 2) / 2

/-- The coefficient of `ln a` at fixed mass, Cartan angular momenta and charges, (1.1) of
  arXiv:1205.0971, for `nV` `U(1)` gauge fields. -/
def logCoeffMicrocanonical (D : ℕ) (cLocal : ℚ) (nV : ℕ) : ℚ :=
  cLocal - ((D : ℚ) - 4) / 2 - ((D : ℚ) - 2) / 2 * numCartan D - ((D : ℚ) - 4) / 2 * nV

/-- The coefficient of `ln a` at fixed mass and charges, all angular momenta summed, (1.4) of
  arXiv:1205.0971. -/
def logCoeffMixed (D : ℕ) (cLocal : ℚ) (nV : ℕ) : ℚ :=
  cLocal - ((D : ℚ) - 4) / 2 - ((D : ℚ) - 4) / 2 * nV

/-- The coefficient of `ln a` counting only rotation singlets, (1.5) of arXiv:1205.0971. -/
def logCoeffSinglet (D : ℕ) (cLocal : ℚ) (nV : ℕ) : ℚ :=
  cLocal - ((D : ℚ) - 4) / 2 - ((D : ℚ) - 2) / 2 * numRotations D - ((D : ℚ) - 4) / 2 * nV

/-!

### B.2. Pure gravity in four dimensions

-/

lemma logCoeffMixed_pureGravity :
    logCoeffMixed 4 MasslessFields.pureGravity.cLocal 0 = 212 / 45 := by
  norm_num [logCoeffMixed, MasslessFields.cLocal_pureGravity]

lemma logCoeffMicrocanonical_pureGravity :
    logCoeffMicrocanonical 4 MasslessFields.pureGravity.cLocal 0 = 167 / 45 := by
  norm_num [logCoeffMicrocanonical, numCartan, MasslessFields.cLocal_pureGravity]

/-- Sen's value `212 / 45 - 3` for the singlet ensemble of pure gravity, which he contrasts with
  the loop quantum gravity value `-2` quoted in the paragraph after (1.5) of arXiv:1205.0971. -/
lemma logCoeffSinglet_pureGravity :
    logCoeffSinglet 4 MasslessFields.pureGravity.cLocal 0 = 77 / 45 := by
  norm_num [logCoeffSinglet, numRotations, MasslessFields.cLocal_pureGravity]

/-!

## C. From the size `a` to the horizon area

In four dimensions the horizon of radius `a` has area `A_H = 4 π a ^ 2`, so `ln A_H` and `2 ln a`
differ by a constant. A correction `c ln a` is therefore `(c / 2) ln A_H` up to a constant.

-/

/-- A correction `c ln a` equals `(c / 2) ln (4 π a ^ 2)` up to the constant
  `(c / 2) ln (4 π)`. -/
lemma mul_log_radius_eq_half_mul_log_area (c a : ℝ) (ha : 0 < a) :
    c * Real.log a =
      c / 2 * Real.log (4 * Real.pi * a ^ 2) - c / 2 * Real.log (4 * Real.pi) := by
  have hπ : (4 * Real.pi) ≠ 0 := by positivity
  rw [Real.log_mul hπ (by positivity), Real.log_pow]
  push_cast
  ring

/-- With all angular momenta summed, pure gravity corrects the entropy by `106 / 45 ln A_H`. -/
lemma logCoeffMixed_pureGravity_area :
    (logCoeffMixed 4 MasslessFields.pureGravity.cLocal 0 : ℝ) / 2 = 106 / 45 := by
  rw [logCoeffMixed_pureGravity]
  norm_num

end SchwarzschildLogCorrection

end GeneralRelativity

end

/-!

## D. Visualization

Put the cursor on the `#html` line below to plot the correction `c ln a` against `ln a` for the
three ensembles of pure gravity, together with the loop quantum gravity value `-2 ln a` that Sen
quotes for comparison. The slopes are the rationals proved above.

-/

public meta section

open Lean ProofWidgets Recharts

namespace GeneralRelativity.SchwarzschildLogCorrection

/-- Data points `(ln a, c ln a)` for the four slopes, as JSON for the line chart. -/
def logCorrectionData (steps : ℕ := 20) (maxLog : Float := 10) : Array Json :=
  (Array.range (steps + 1)).map fun i =>
    let x := maxLog * i.toFloat / steps.toFloat
    json% {lna: $(x), mixed: $(212 / 45 * x), fixedJ: $(167 / 45 * x),
      singlet: $(77 / 45 * x), lqg: $(-2 * x)}

/-- Line chart of the logarithmic correction against `ln a`. -/
def logCorrectionPlot : ProofWidgets.Html :=
  let caption : ProofWidgets.Html := .text "Correction to S_BH against ln a, pure gravity \
    in D = 4. Blue: all J summed (212/45). Green: fixed J₃ (167/45). \
    Orange: rotation singlets (77/45). Red: loop quantum gravity value quoted by Sen (-2)."
  jsx%{<div>
    <p>{caption}</p>
    <LineChart width={480} height={320} data={logCorrectionData}>
      <XAxis dataKey?="lna" />
      <YAxis />
      <Line type={.linear} dataKey="mixed" stroke="#1f77b4" dot?={Bool.false} />
      <Line type={.linear} dataKey="fixedJ" stroke="#2ca02c" dot?={Bool.false} />
      <Line type={.linear} dataKey="singlet" stroke="#ff7f0e" dot?={Bool.false} />
      <Line type={.linear} dataKey="lqg" stroke="#d62728" dot?={Bool.false} />
    </LineChart>
  </div>}

#html logCorrectionPlot

end GeneralRelativity.SchwarzschildLogCorrection

end
