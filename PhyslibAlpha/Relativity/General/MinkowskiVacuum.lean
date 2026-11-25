/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
public import PhyslibAlpha.Relativity.Metrics.Minkowski
public import PhyslibAlpha.Relativity.Tensors.EinsteinTensor

/-!

# Minkowski spacetime as a vacuum solution

Verification that flat Minkowski spacetime satisfies the vacuum Einstein equations both
algebraically (`RiemannTensor.flat 4`) and through the coordinate differential pipeline.

## i. Overview

Combining the Minkowski `MetricTensor 4` (`minkowski`) and constant coordinate metric field
(`minkowskiCoordinateMetric`) with `EinsteinTensor` and `CoordinateMetric`, this module proves
that Minkowski spacetime is Ricci flat, scalar flat, and solves `G = 0`, and that its pipeline
Christoffel symbols, Riemann tensor, and Einstein tensor vanish identically.

## ii. Key results

- `minkowskiCoordinateMetric` : four-dimensional Minkowski spacetime as a `CoordinateMetric 4`.
- `minkowski_ricci_eq_zero`, `minkowski_ricciScalar_eq_zero`, `minkowski_einstein_eq_zero` :
  Minkowski spacetime is Ricci flat, scalar flat, and a vacuum solution of `G = 0`.
- `Pipeline.minkowski_christoffel`, `Pipeline.minkowski_riemann`, `Pipeline.minkowski_einstein`,
  `Pipeline.minkowski_riemannFromData` : Minkowski spacetime as a computed pipeline vacuum
  solution.

## iii. Table of contents

- A. Algebraic vacuum Einstein equations on Minkowski spacetime
- B. Pipeline vacuum verification on Minkowski spacetime

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Algebraic vacuum Einstein equations on Minkowski spacetime

-/

/-- The flat Riemann curvature tensor of four-dimensional Minkowski spacetime. -/
def minkowskiFlatRiemann : RiemannTensor 4 := RiemannTensor.flat 4

/-- The flat curvature tensor on Minkowski spacetime is Ricci flat. -/
lemma minkowski_ricci_eq_zero : ricci minkowski (RiemannTensor.flat 4) = 0 :=
  ricci_flat 4 minkowski

/-- The flat curvature tensor on Minkowski spacetime has zero scalar curvature. -/
lemma minkowski_ricciScalar_eq_zero : ricciScalar minkowski (RiemannTensor.flat 4) = 0 := by
  simp [ricciScalar]

/-- Minkowski spacetime is a vacuum solution of the Einstein equations. -/
lemma minkowski_einstein_eq_zero : einstein minkowski (RiemannTensor.flat 4) = 0 := by
  ext i j
  simp [einstein, minkowski_ricciScalar_eq_zero]

/-- `G = 0` and `Ric = 0` agree on Minkowski spacetime. -/
lemma minkowski_vacuum_iff_ricci_flat :
    einstein minkowski (RiemannTensor.flat 4) = 0 ↔
      ricci minkowski (RiemannTensor.flat 4) = 0 :=
  vacuum_iff_ricci_flat minkowski (RiemannTensor.flat 4)

/-!

## B. Pipeline vacuum verification on Minkowski spacetime

-/

/-- Four-dimensional Minkowski spacetime as a `CoordinateMetric 4` on all of `ℝ⁴`. -/
noncomputable def minkowskiCoordinateMetric : CoordinateMetric 4 where
  g := minkowskiG
  ginv := minkowskiG
  domain := Set.univ
  symm := fun _ => minkowskiMetric4_symm
  inv_left := fun _ _ => minkowskiMetric4_mul_self
  inv_right := fun _ _ => minkowskiMetric4_mul_self

/-- The pipeline produces vanishing Christoffel symbols for Minkowski spacetime. -/
lemma Pipeline.minkowski_christoffel (x : Fin 4 → ℝ) (k i j : Fin 4) :
    Pipeline.christoffel Pipeline.minkowskiG Pipeline.minkowskiG x k i j = 0 :=
  Pipeline.christoffel_const Pipeline.minkowskiG Pipeline.minkowskiG minkowskiMetric4 (fun _ =>
      rfl) x k i j

/-- The pipeline produces vanishing Riemann curvature for Minkowski spacetime. -/
lemma Pipeline.minkowski_riemann (x : Fin 4 → ℝ) (ρ σ μ ν : Fin 4) :
    Pipeline.riemann Pipeline.minkowskiG Pipeline.minkowskiG x ρ σ μ ν = 0 :=
  Pipeline.riemann_const Pipeline.minkowskiG Pipeline.minkowskiG minkowskiMetric4 (fun _ => rfl) x
      ρ σ μ ν

/-- Minkowski spacetime is a vacuum solution of the Einstein equations (`G_{ij} = 0`), computed
from the metric rather than assumed. -/
lemma Pipeline.minkowski_einstein (x : Fin 4 → ℝ) (i j : Fin 4) :
    Pipeline.einsteinTensorOf Pipeline.minkowskiG Pipeline.minkowskiG x i j = 0 :=
  Pipeline.einsteinTensorOf_const Pipeline.minkowskiG Pipeline.minkowskiG minkowskiMetric4 (fun _
      => rfl) x i j

/-- The data form returns zero curvature on Minkowski spacetime. -/
lemma Pipeline.minkowski_riemannFromData (x : Fin 4 → ℝ) (ρ σ μ ν : Fin 4) :
    Pipeline.riemannFromData (Pipeline.christoffel Pipeline.minkowskiG Pipeline.minkowskiG)
      (fun μ y a b c => Pipeline.pd μ
        (fun z => Pipeline.christoffel Pipeline.minkowskiG Pipeline.minkowskiG z a b c) y)
      x ρ σ μ ν = 0 := by
  rw [← Pipeline.riemann_eq_riemannFromData]
  exact Pipeline.minkowski_riemann x ρ σ μ ν

end GeneralRelativity
