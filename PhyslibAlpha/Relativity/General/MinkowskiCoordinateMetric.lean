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
- `minkowskiCoordinateMetric_christoffel`, `minkowskiCoordinateMetric_riemann`,
  `minkowskiCoordinateMetric_ricciTensorOf`, `minkowskiCoordinateMetric_ricciScalarOf`,
  `minkowskiCoordinateMetric_einsteinTensorOf`, `minkowskiCoordinateMetric_riemannFromData` :
  Minkowski spacetime as a computed `CoordinateMetric` vacuum solution.
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

Bundling the constant Minkowski metric field on `Set.univ` into `minkowskiCoordinateMetric` yields
identically zero Christoffel symbols and curvature tensors through the coordinate pipeline.

-/

/-- Four-dimensional Minkowski spacetime as a `CoordinateMetric 4` on all of `ℝ⁴`. -/
noncomputable def minkowskiCoordinateMetric : CoordinateMetric 4 where
  g := minkowskiMetricField
  ginv := minkowskiMetricField
  domain := Set.univ
  symm := fun _ => minkowskiMetric4_symm
  inv_left := fun _ _ => minkowskiMetric4_mul_self
  inv_right := fun _ _ => minkowskiMetric4_mul_self

/-- The coordinate pipeline produces vanishing Christoffel symbols for
`minkowskiCoordinateMetric`. -/
lemma minkowskiCoordinateMetric_christoffel (x : Fin 4 → ℝ) (k i j : Fin 4) :
    minkowskiCoordinateMetric.christoffel x k i j = 0 :=
  Pipeline.christoffel_const minkowskiCoordinateMetric.g minkowskiCoordinateMetric.ginv
    minkowskiMetric4 (fun _ => rfl) x k i j

/-- The coordinate pipeline produces vanishing Riemann curvature for
`minkowskiCoordinateMetric`. -/
lemma minkowskiCoordinateMetric_riemann (x : Fin 4 → ℝ) (ρ σ μ ν : Fin 4) :
    minkowskiCoordinateMetric.riemann x ρ σ μ ν = 0 :=
  Pipeline.riemann_const minkowskiCoordinateMetric.g minkowskiCoordinateMetric.ginv
    minkowskiMetric4 (fun _ => rfl) x ρ σ μ ν

/-- The coordinate pipeline produces vanishing Ricci curvature for
`minkowskiCoordinateMetric`. -/
lemma minkowskiCoordinateMetric_ricciTensorOf (x : Fin 4 → ℝ) (σ ν : Fin 4) :
    minkowskiCoordinateMetric.ricciTensorOf x σ ν = 0 :=
  Pipeline.ricciTensorOf_const minkowskiCoordinateMetric.g minkowskiCoordinateMetric.ginv
    minkowskiMetric4 (fun _ => rfl) x σ ν

/-- The coordinate pipeline produces vanishing scalar curvature for
`minkowskiCoordinateMetric`. -/
lemma minkowskiCoordinateMetric_ricciScalarOf (x : Fin 4 → ℝ) :
    minkowskiCoordinateMetric.ricciScalarOf x = 0 :=
  Pipeline.ricciScalarOf_const minkowskiCoordinateMetric.g minkowskiCoordinateMetric.ginv
    minkowskiMetric4 (fun _ => rfl) x

/-- `minkowskiCoordinateMetric` is a vacuum solution of the Einstein equations (`G_{ij} = 0`),
computed from the metric rather than assumed. -/
lemma minkowskiCoordinateMetric_einsteinTensorOf (x : Fin 4 → ℝ) (i j : Fin 4) :
    minkowskiCoordinateMetric.einsteinTensorOf x i j = 0 :=
  Pipeline.einsteinTensorOf_const minkowskiCoordinateMetric.g minkowskiCoordinateMetric.ginv
    minkowskiMetric4 (fun _ => rfl) x i j

/-- Explicit Christoffel-data evaluation of the Riemann tensor vanishes identically on
`minkowskiCoordinateMetric`. -/
lemma minkowskiCoordinateMetric_riemannFromData (x : Fin 4 → ℝ) (ρ σ μ ν : Fin 4) :
    Pipeline.riemannFromData
      (Pipeline.christoffel minkowskiCoordinateMetric.g minkowskiCoordinateMetric.ginv)
      (fun μ y a b c => Pipeline.coordDeriv μ
        (fun z => Pipeline.christoffel minkowskiCoordinateMetric.g
          minkowskiCoordinateMetric.ginv z a b c) y)
      x ρ σ μ ν = 0 := by
  rw [← Pipeline.riemann_eq_riemannFromData]
  exact minkowskiCoordinateMetric_riemann x ρ σ μ ν

/-!

## B. Algebraic vacuum Einstein equations on Minkowski spacetime

In the algebraic tensor formulation, the flat Riemann curvature tensor on Minkowski spacetime
immediately satisfies the vacuum Einstein equations.

-/

/-- The flat Riemann curvature tensor of four-dimensional Minkowski spacetime. -/
def minkowskiFlatRiemann : RiemannTensor 4 := RiemannTensor.flat 4

/-- The flat curvature tensor on Minkowski spacetime is Ricci flat. -/
lemma minkowski_ricci_eq_zero : ricci minkowski (RiemannTensor.flat 4) = 0 :=
  ricci_flat 4 minkowski

/-- The flat curvature tensor on Minkowski spacetime has zero scalar curvature. -/
lemma minkowski_ricciScalar_eq_zero : ricciScalar minkowski (RiemannTensor.flat 4) = 0 :=
  ricciScalar_flat minkowski

/-- Minkowski spacetime is a vacuum solution of the Einstein equations. -/
lemma minkowski_einstein_eq_zero : einstein minkowski (RiemannTensor.flat 4) = 0 :=
  einstein_flat minkowski

/-- `G = 0` and `Ric = 0` agree on Minkowski spacetime. -/
lemma minkowski_vacuum_iff_ricci_flat :
    einstein minkowski (RiemannTensor.flat 4) = 0 ↔
      ricci minkowski (RiemannTensor.flat 4) = 0 :=
  vacuum_iff_ricci_flat minkowski (RiemannTensor.flat 4)

end GeneralRelativity
