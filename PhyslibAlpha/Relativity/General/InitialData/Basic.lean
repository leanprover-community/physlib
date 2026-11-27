/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import PhyslibAlpha.Relativity.Metrics.Basic
public import PhyslibAlpha.Relativity.Metrics.RicciScalar
import Mathlib.Tactic.Linarith

/-!

# The initial value problem: constraint equations

The Hamiltonian and momentum constraints on a three-dimensional Cauchy slice.

## i. Overview

In the ADM 3+1 decomposition of vacuum general relativity, initial data on a spatial slice `Σ`
consist of a Riemannian 3-metric `h`, its 3D curvature tensor `R3`, and a symmetric extrinsic
curvature `K`. The normal components of `G = 0` impose the Hamiltonian constraint
`H = ³R + (tr K)² - K_ij K^ij = 0` and the momentum constraint
`M_i = g^{jk} (∇_j K_{ik} - ∇_i K_{jk}) = 0`,
where `∇` is the 3D Levi-Civita covariant derivative of `h` (reducing to coordinate partial
derivatives `∂` in locally flat / normal coordinates where `Γ = 0`).

This module defines `InitialData` and formalises the constraint functions together with their
reductions under time symmetry (`K = 0`) and maximal slicing (`tr K = 0`). Global development
existence (Choquet–Bruhat–Geroch) is quasilinear hyperbolic PDE theory and is neither formalised
nor axiomatised here.

## ii. Key results

- `InitialData`, `InitialData.momentumConstraint`, `InitialData.hamiltonianConstraint`,
  `InitialData.IsVacuumData` : Cauchy data and vacuum constraint equations.
- `InitialData.hamiltonianConstraint_zero_iff_ricciScalar_zero_of_K_zero` : time-symmetric
  vacuum data are scalar flat.
- `InitialData.hamiltonianConstraint_eq_of_trace_zero` : maximal-slicing reduction `H = ³R - K_ij
  K^ij`.
- `InitialData.trace_sq_eq_of_hamiltonianConstraint_zero`,
  `InitialData.momentumConstraint_zero_of_covariantDeriv_zero` : scalar-flat trace identity and
  vanishing momentum constraint under zero covariant derivative `∇K = 0`.

## iii. Table of contents

- A. Initial data and constraint equations
- B. Moment of time symmetry and maximal slicing reductions

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 10 (Sec. 10.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 21.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 4
  (https://arxiv.org/pdf/gr-qc/9712019#page=104). [ref: Carroll1997]
* R. Arnowitt, S. Deser, and C. W. Misner, *The Dynamics of General Relativity*, in *Gravitation: An
  Introduction to Current Research* (1962) (https://arxiv.org/pdf/gr-qc/0405109#page=1).
  [ref: ADM1962]
-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Initial data and constraint equations

An ADM Cauchy slice packages the induced Riemannian 3-metric `h`, its spatial Riemann curvature
`R3`, and the extrinsic curvature `K_{ij}` measuring how the slice embeds into 4D spacetime.

-/

/-- Initial data on a three-dimensional spatial slice: the induced Riemannian metric `h`, its
Riemann tensor `R3`, and the symmetric extrinsic curvature `K`. -/
structure InitialData where
  /-- Induced Riemannian 3-metric on the spatial slice. -/
  h : MetricTensor 3
  /-- Three-dimensional Riemann curvature tensor of `h`. -/
  R3 : RiemannTensor 3
  /-- Symmetric extrinsic curvature `K_{ij}` of the slice. -/
  K : Tensor2 3
  /-- Symmetry of the extrinsic curvature. -/
  Ksymm : IsSymm K

namespace InitialData

/-- Three-dimensional Levi-Civita covariant derivative of a rank-2 tensor `K`:
`∇_μ K_{ij} = ∂_μ K_{ij} - Γ^l_{μi} K_{lj} - Γ^l_{μj} K_{il}`. -/
def covariantDerivTensor2 (Γ : Fin 3 → Fin 3 → Fin 3 → ℝ) (dK : Fin 3 → Tensor2 3)
    (K : Tensor2 3) : Fin 3 → Tensor2 3 :=
  fun μ i j => dK μ i j - (∑ l, Γ l μ i * K l j) - (∑ l, Γ l μ j * K i l)

/-- In locally flat / normal coordinates where the 3D Christoffel symbols vanish (`Γ = 0`),
the covariant derivative `covariantDerivTensor2` reduces to the partial derivative table `dK`. -/
lemma covariantDerivTensor2_eq_of_zero (dK : Fin 3 → Tensor2 3) (K : Tensor2 3) :
    covariantDerivTensor2 0 dK K = dK := by
  ext μ i j
  simp [covariantDerivTensor2]

/-- The momentum constraint `M_i = g^{jk} (∇_j K_{ik} - ∇_i K_{jk})` on a spatial slice. The
table `dK μ i j = ∂_μ K_{ij}` holds coordinate partial derivatives of the extrinsic curvature, and
`covariantDerivTensor2` supplies the 3D Levi-Civita covariant derivative from `Γ`. -/
noncomputable def momentumConstraint (D : InitialData) (Γ : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (dK : Fin 3 → Tensor2 3) (i : Fin 3) : ℝ :=
  (∑ j, ∑ k, D.h.ginv j k * covariantDerivTensor2 Γ dK D.K j i k)
    - ∑ j, ∑ k, D.h.ginv j k * covariantDerivTensor2 Γ dK D.K i j k

/-- The Hamiltonian (energy) constraint `H = ³R + (tr K)² - K_ij K^ij`, contracting `K` with the
inverse spatial metric `D.h.ginv`. -/
noncomputable def hamiltonianConstraint (D : InitialData) : ℝ :=
  ricciScalar D.h D.R3 + (metricTrace D.h D.K) ^ 2
    - ∑ i, ∑ j, ∑ k, ∑ l, D.h.ginv i k * D.h.ginv j l * D.K i j * D.K k l

/-- Combined predicate stating that the data satisfy both vacuum constraints. -/
def IsVacuumData (D : InitialData) (Γ : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (dK : Fin 3 → Tensor2 3) : Prop :=
  D.hamiltonianConstraint = 0 ∧ ∀ i, D.momentumConstraint Γ dK i = 0

/-!

## B. Moment of time symmetry and maximal slicing reductions

At a moment of time symmetry (`K = 0`) or maximal slicing (`tr K = 0`), the Hamiltonian constraint
simplifies directly into algebraic conditions on the spatial scalar curvature `³R`.

-/

/-- At a moment of time symmetry (`K = 0`), the Hamiltonian constraint reduces to the 3D scalar
curvature. -/
lemma hamiltonianConstraint_eq_ricciScalar_of_K_zero (D : InitialData) (hK : D.K = 0) :
    D.hamiltonianConstraint = ricciScalar D.h D.R3 := by
  simp [hamiltonianConstraint, hK]

/-- At a moment of time symmetry (`K = 0`), vanishing Hamiltonian constraint is equivalent to
scalar flatness. -/
lemma hamiltonianConstraint_zero_iff_ricciScalar_zero_of_K_zero (D : InitialData)
    (hK : D.K = 0) : D.hamiltonianConstraint = 0 ↔ ricciScalar D.h D.R3 = 0 := by
  rw [hamiltonianConstraint_eq_ricciScalar_of_K_zero D hK]

/-- Under maximal slicing (`tr K = 0`), the Hamiltonian constraint becomes
`H = ³R - K_ij K^ij`. -/
lemma hamiltonianConstraint_eq_of_trace_zero (D : InitialData) (htr : metricTrace D.h D.K = 0) :
    D.hamiltonianConstraint =
      ricciScalar D.h D.R3 -
        ∑ i, ∑ j, ∑ k, ∑ l, D.h.ginv i k * D.h.ginv j l * D.K i j * D.K k l := by
  simp [hamiltonianConstraint, htr]

/-- On a scalar-flat slice, `H = 0` forces `(tr K)² = K_ij K^ij`. -/
lemma trace_sq_eq_of_hamiltonianConstraint_zero (D : InitialData)
    (hH : D.hamiltonianConstraint = 0) (hR : ricciScalar D.h D.R3 = 0) :
    (metricTrace D.h D.K) ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l, D.h.ginv i k * D.h.ginv j l * D.K i j * D.K k l := by
  simp only [hamiltonianConstraint] at hH
  linarith

/-- If the covariant derivative `∇K` vanishes everywhere on the spatial slice, the momentum
constraint holds identically. -/
lemma momentumConstraint_zero_of_covariantDeriv_zero (D : InitialData)
    (Γ : Fin 3 → Fin 3 → Fin 3 → ℝ) (dK : Fin 3 → Tensor2 3)
    (hdK : ∀ μ i j, covariantDerivTensor2 Γ dK D.K μ i j = 0) :
    ∀ i, D.momentumConstraint Γ dK i = 0 := by
  intro i
  simp [momentumConstraint, hdK]

end InitialData

end GeneralRelativity
