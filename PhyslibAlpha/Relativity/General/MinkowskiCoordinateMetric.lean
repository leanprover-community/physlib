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

# Flat Minkowski spacetime and the vacuum Einstein equations

Flat Minkowski spacetime in global inertial coordinates, with vanishing Christoffel symbols,
vanishing curvature tensors, and verification of the vacuum Einstein equations `G_{ij} = 0`.

## i. Overview

In global inertial coordinates `(t, x, y, z)` on `ℝ⁴`, flat Minkowski spacetime carries the
constant Lorentzian metric `η = diag(-1, 1, 1, 1)` on all of `ℝ⁴`. Because every metric component
is position independent, all Levi-Civita connection coefficients `Γ^k_{ij}` vanish identically, so
the Riemann curvature, Ricci tensor, scalar curvature, and Einstein tensor all vanish identically
and Minkowski spacetime solves the vacuum Einstein equations `G_{ij} = 0`.

## ii. Key results

- `minkowskiCoordinateMetric` : four-dimensional Minkowski spacetime as a `CoordinateMetric 4`.
- `minkowskiCoordinateMetric_christoffel`, `minkowskiCoordinateMetric_riemann`,
  `minkowskiCoordinateMetric_ricciTensor`, `minkowskiCoordinateMetric_ricciScalar`,
  `minkowskiCoordinateMetric_einsteinTensor`, `minkowskiCoordinateMetric_riemannFromData` :
  vanishing coordinate connection and curvature tensors of Minkowski spacetime.
- `minkowski_ricci_eq_zero`, `minkowski_ricciScalar_eq_zero`,
  `minkowski_einstein_eq_zero`, `minkowski_vacuum_iff_ricci_flat` : algebraic vacuum properties.

## iii. Table of contents

- A. The Minkowski coordinate metric and flatness
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

## A. The Minkowski coordinate metric and flatness

On global inertial coordinates covering all of `ℝ⁴`, the constant Minkowski metric has identically
vanishing Levi-Civita Christoffel symbols and curvature tensors.

-/

/-- Four-dimensional Minkowski spacetime as a `CoordinateMetric 4` on all of `ℝ⁴`. -/
noncomputable def minkowskiCoordinateMetric : CoordinateMetric 4 where
  g := minkowskiMetricField
  ginv := minkowskiMetricField
  domain := Set.univ
  symm := fun _ => minkowskiMetric4_symm
  inv_left := fun _ _ => minkowskiMetric4_mul_self
  inv_right := fun _ _ => minkowskiMetric4_mul_self

/-- In inertial coordinates, all Christoffel symbols of Minkowski spacetime vanish. -/
lemma minkowskiCoordinateMetric_christoffel (x : Fin 4 → ℝ) (k i j : Fin 4) :
    minkowskiCoordinateMetric.christoffel x k i j = 0 :=
  CoordinateCurvature.christoffel_const minkowskiCoordinateMetric.g minkowskiCoordinateMetric.ginv
    minkowskiMetric4 (fun _ => rfl) x k i j

/-- All coordinate Riemann curvature components of Minkowski spacetime vanish. -/
lemma minkowskiCoordinateMetric_riemann (x : Fin 4 → ℝ) (ρ σ μ ν : Fin 4) :
    minkowskiCoordinateMetric.riemann x ρ σ μ ν = 0 :=
  CoordinateCurvature.riemann_const minkowskiCoordinateMetric.g minkowskiCoordinateMetric.ginv
    minkowskiMetric4 (fun _ => rfl) x ρ σ μ ν

/-- Minkowski spacetime is Ricci flat in global inertial coordinates. -/
lemma minkowskiCoordinateMetric_ricciTensor (x : Fin 4 → ℝ) (σ ν : Fin 4) :
    minkowskiCoordinateMetric.ricciTensor x σ ν = 0 :=
  CoordinateCurvature.ricciTensor_const minkowskiCoordinateMetric.g minkowskiCoordinateMetric.ginv
    minkowskiMetric4 (fun _ => rfl) x σ ν

/-- Minkowski spacetime has vanishing scalar curvature in global inertial coordinates. -/
lemma minkowskiCoordinateMetric_ricciScalar (x : Fin 4 → ℝ) :
    minkowskiCoordinateMetric.ricciScalar x = 0 :=
  CoordinateCurvature.ricciScalar_const minkowskiCoordinateMetric.g minkowskiCoordinateMetric.ginv
    minkowskiMetric4 (fun _ => rfl) x

/-- Minkowski spacetime satisfies the vacuum Einstein equations (`G_{ij} = 0`). -/
lemma minkowskiCoordinateMetric_einsteinTensor (x : Fin 4 → ℝ) (i j : Fin 4) :
    minkowskiCoordinateMetric.einsteinTensor x i j = 0 :=
  CoordinateCurvature.einsteinTensor_const minkowskiCoordinateMetric.g
    minkowskiCoordinateMetric.ginv minkowskiMetric4 (fun _ => rfl) x i j

/-- Explicit Christoffel-data evaluation of the Riemann tensor vanishes identically on
`minkowskiCoordinateMetric`. -/
lemma minkowskiCoordinateMetric_riemannFromData (x : Fin 4 → ℝ) (ρ σ μ ν : Fin 4) :
    CoordinateCurvature.riemannFromData
      (CoordinateCurvature.christoffel minkowskiCoordinateMetric.g
        minkowskiCoordinateMetric.ginv)
      (fun μ y a b c => CoordinateCurvature.coordDeriv μ
        (fun z => CoordinateCurvature.christoffel minkowskiCoordinateMetric.g
          minkowskiCoordinateMetric.ginv z a b c) y)
      x ρ σ μ ν = 0 := by
  rw [← CoordinateCurvature.riemann_eq_riemannFromData]
  exact minkowskiCoordinateMetric_riemann x ρ σ μ ν

/-!

## B. Algebraic vacuum Einstein equations on Minkowski spacetime

In the algebraic tensor formulation, the vanishing Riemann tensor `RiemannTensor.flat 4` on
Minkowski spacetime immediately gives `Ric = 0`, `R = 0`, and the vacuum Einstein equations.

-/

/-- The flat curvature tensor on Minkowski spacetime is Ricci flat. -/
lemma minkowski_ricci_eq_zero : ricci minkowski (RiemannTensor.flat 4) = 0 :=
  ricci_flat 4 minkowski

/-- The flat curvature tensor on Minkowski spacetime has zero scalar curvature `R = 0`. -/
lemma minkowski_ricciScalar_eq_zero : ricciScalar minkowski (RiemannTensor.flat 4) = 0 :=
  ricciScalar_flat minkowski

/-- Minkowski spacetime is a vacuum solution of the Einstein equations. -/
lemma minkowski_einstein_eq_zero : einstein minkowski (RiemannTensor.flat 4) = 0 :=
  einstein_flat minkowski

/-- `G = 0` and `Ric = 0` are equivalent on Minkowski spacetime, as `vacuum_iff_ricci_flat` states
for any four-dimensional metric. -/
lemma minkowski_vacuum_iff_ricci_flat :
    einstein minkowski (RiemannTensor.flat 4) = 0 ↔
      ricci minkowski (RiemannTensor.flat 4) = 0 :=
  vacuum_iff_ricci_flat minkowski (RiemannTensor.flat 4)

end GeneralRelativity
