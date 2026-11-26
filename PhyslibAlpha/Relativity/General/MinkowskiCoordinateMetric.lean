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

# The Minkowski coordinate metric and vacuum flatness

Coordinate-chart bundle `minkowskiCoordinateMetric` for flat Minkowski spacetime together with
verification that it satisfies the vacuum Einstein equations both through the differential pipeline
and algebraically.

## i. Overview

In global inertial coordinates `(t, x, y, z)` on `ℝ⁴`, flat Minkowski spacetime carries the
constant Lorentzian metric `η = diag(-1, 1, 1, 1)` bundled on `Set.univ` as
`minkowskiCoordinateMetric`. Because every metric component is position independent, all
Levi-Civita connection coefficients `Γ^k_{ij}` vanish identically, so the Riemann curvature, Ricci
tensor, scalar curvature, and Einstein tensor all vanish identically and Minkowski spacetime solves
the vacuum Einstein equations `G_{ij} = 0`.

## ii. Key results

- `minkowskiCoordinateMetric` : four-dimensional Minkowski spacetime as a `CoordinateMetric 4`.
- `Pipeline.minkowski_christoffel`, `Pipeline.minkowski_riemann`, `Pipeline.minkowski_einstein`,
  `Pipeline.minkowski_riemannFromData` : Minkowski spacetime as a computed pipeline vacuum
  solution.
- `minkowskiFlatRiemann`, `minkowski_ricci_eq_zero`, `minkowski_ricciScalar_eq_zero`,
  `minkowski_einstein_eq_zero`, `minkowski_vacuum_iff_ricci_flat` : algebraic vacuum properties.

## iii. Table of contents

- A. The Minkowski coordinate metric and pipeline flatness
- B. Algebraic vacuum Einstein equations on Minkowski spacetime

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 4 (Sec. 4.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 17.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 4
  (https://arxiv.org/pdf/gr-qc/9712019#page=104). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. The Minkowski coordinate metric and pipeline flatness

-/

/-- Four-dimensional Minkowski spacetime as a `CoordinateMetric 4` on all of `ℝ⁴`. -/
noncomputable def minkowskiCoordinateMetric : CoordinateMetric 4 where
  g := minkowskiMetricField
  ginv := minkowskiMetricField
  domain := Set.univ
  symm := fun _ => minkowskiMetric4_symm
  inv_left := fun _ _ => minkowskiMetric4_mul_self
  inv_right := fun _ _ => minkowskiMetric4_mul_self

/-- The pipeline produces vanishing Christoffel symbols for Minkowski spacetime. -/
lemma Pipeline.minkowski_christoffel (x : Fin 4 → ℝ) (k i j : Fin 4) :
    Pipeline.christoffel Pipeline.minkowskiMetricField Pipeline.minkowskiMetricField x k i j =
      0 :=
  Pipeline.christoffel_const Pipeline.minkowskiMetricField Pipeline.minkowskiMetricField
    minkowskiMetric4 (fun _ => rfl) x k i j

/-- The pipeline produces vanishing Riemann curvature for Minkowski spacetime. -/
lemma Pipeline.minkowski_riemann (x : Fin 4 → ℝ) (ρ σ μ ν : Fin 4) :
    Pipeline.riemann Pipeline.minkowskiMetricField Pipeline.minkowskiMetricField x ρ σ μ ν = 0 :=
  Pipeline.riemann_const Pipeline.minkowskiMetricField Pipeline.minkowskiMetricField
    minkowskiMetric4 (fun _ => rfl) x ρ σ μ ν

/-- Minkowski spacetime is a vacuum solution of the Einstein equations (`G_{ij} = 0`), computed
from the metric rather than assumed. -/
lemma Pipeline.minkowski_einstein (x : Fin 4 → ℝ) (i j : Fin 4) :
    Pipeline.einsteinTensorOf Pipeline.minkowskiMetricField Pipeline.minkowskiMetricField x i j =
      0 :=
  Pipeline.einsteinTensorOf_const Pipeline.minkowskiMetricField Pipeline.minkowskiMetricField
    minkowskiMetric4 (fun _ => rfl) x i j

/-- Explicit Christoffel-data evaluation of the Riemann tensor vanishes identically on flat
Minkowski spacetime. -/
lemma Pipeline.minkowski_riemannFromData (x : Fin 4 → ℝ) (ρ σ μ ν : Fin 4) :
    Pipeline.riemannFromData
      (Pipeline.christoffel Pipeline.minkowskiMetricField Pipeline.minkowskiMetricField)
      (fun μ y a b c => Pipeline.coordDeriv μ
        (fun z => Pipeline.christoffel Pipeline.minkowskiMetricField
          Pipeline.minkowskiMetricField z a b c) y)
      x ρ σ μ ν = 0 := by
  rw [← Pipeline.riemann_eq_riemannFromData]
  exact Pipeline.minkowski_riemann x ρ σ μ ν

/-!

## B. Algebraic vacuum Einstein equations on Minkowski spacetime

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

end GeneralRelativity
