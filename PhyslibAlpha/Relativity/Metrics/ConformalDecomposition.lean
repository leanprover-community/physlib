/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.ConformalMetric
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The Lichnerowicz-York conformal decomposition (interface)

## i. Overview

This module states the conformal decomposition used to solve the Einstein
constraint equations.  It does not solve them.  The seed data are a 3-metric
`hbar`, a transverse-traceless tensor `sigma` and a mean extrinsic curvature
`tau`; the physical data are `h = phi^4 hbar` and `K = phi^{-2} sigma +
(tau/3) h`.  The Hamiltonian and momentum constraints then become the
Lichnerowicz equation for `phi` and the divergence equation for `sigma`.

The residuals below take the seed Laplacian, scalar curvature, divergence and
gradient as explicit arguments.  This repository has coordinate expressions for
those operators but no manifold elliptic theory, so the interface states the
system and leaves existence, regularity and uniqueness to the paper on the
constraint equations.

## ii. Key results

- `ConformalData` : seed metric, conformal factor, shift, TT tensor and mean
  curvature.
- `ConformalData.extrinsicCurvatureOfShift` : the same `K` with the conformal
  Killing term `(L beta)` added.
- `shiftMomentumResidual`, `IsShiftSolution` : the momentum constraint for the
  shift.
- `ShiftRegular` : the shift is `C^2` on the slice.
- `ConformalData.physicalMetric` : `h = phi^4 hbar`, packaged with its inverse.
- `ConformalData.extrinsicCurvature` : `K = phi^{-2} sigma + (tau/3) h`.
- `hamiltonianResidual` : `8 lap phi - R phi + |sigma|^2 phi^{-7}`.
- `linearisedHamiltonianResidual` : `8 lap psi - R psi - 7 |sigma|^2 psi phi^{-8}`,
  the algebraic linearisation; it is additive and homogeneous in the direction,
  reduces to the conformal Laplacian in vacuum, and is the Gateaux derivative of
  the Hamiltonian residual (`hasDerivAt_hamiltonianResidual`).  Its elliptic
  estimates are the open layer.
- `momentumResidual` : `(div sigma)_i - (2/3) phi^6 (grad tau)_i`.
- `IsLichnerowiczYorkSolution` : both residuals vanish.

## iii. Table of contents

- A. Conformal data
- B. The Lichnerowicz-York residuals
- C. The shift and the momentum constraint

## iv. References

* A. Lichnerowicz, *L'integration des equations de la gravitation relativiste
  et le probleme des n corps*, J. Math. Pures Appl. 23 (1944) 37-63.
* J. W. York, *Gravitational energy and the initial-value problem*,
  Phys. Rev. Lett. 26 (1971) 1656.
* Y. Choquet-Bruhat and J. W. York, *The Cauchy problem*, in *General
  Relativity and Gravitation* (Plenum, 1980).
* R. Bartnik and J. Isenberg, *The constraint equations*, in *The Einstein
  Equations and the Large Scale Behavior of Gravitational Fields* (2004),
  arXiv:gr-qc/0405092.
-/

@[expose] public section

open scoped ContDiff

namespace GeneralRelativity

/-! ## A. Conformal data -/

/-- Conformal data for the Lichnerowicz-York decomposition: a seed 3-metric
`hbar`, a positive conformal factor `phi`, a transverse-traceless tensor
`sigma`, and the mean extrinsic curvature `tau`. -/
structure ConformalData where
  /-- The seed 3-metric `hbar`. -/
  seed : MetricTensor 3
  /-- The conformal factor `phi`. -/
  phi : ℝ
  /-- Positivity of the conformal factor. -/
  phi_pos : 0 < phi
  /-- The transverse-traceless tensor `sigma`. -/
  sigma : Tensor2 3
  /-- The mean extrinsic curvature `tau`. -/
  meanCurvature : ℝ
  /-- The shift vector field `beta^i` on the slice. -/
  shift : (Fin 3 → ℝ) → Fin 3 → ℝ

namespace ConformalData

/-- The physical metric `h = phi^4 hbar`, with inverse `phi^{-4} hbar^{-1}`. -/
noncomputable def physicalMetric (D : ConformalData) : MetricTensor 3 :=
  conformalMetric D.seed (D.phi ^ 4) (pow_pos D.phi_pos 4).ne'

/-- The components of the physical metric are `phi^4 hbar_{ij}`. -/
lemma physicalMetric_g (D : ConformalData) :
    D.physicalMetric.g = fun i j => D.phi ^ 4 * D.seed.g i j := by
  rfl

/-! The physical extrinsic curvature `K = phi^{-2} sigma + (tau/3) h`. -/
noncomputable def extrinsicCurvature (D : ConformalData) : Tensor2 3 :=
  fun i j => (D.phi ^ 2)⁻¹ * D.sigma i j
    + (D.meanCurvature / 3) * D.physicalMetric.g i j

/-- The extrinsic curvature with the conformal Killing term of the shift,
`K = phi^{-2} ((L beta) + sigma) + (tau/3) h`.  The tensor `(L beta)` is
supplied by the caller: this repository has no manifold covariant derivative
with which to form it from `D.shift`. -/
noncomputable def extrinsicCurvatureOfShift (D : ConformalData) (killing : Tensor2 3) :
    Tensor2 3 :=
  fun i j => (D.phi ^ 2)⁻¹ * (killing i j + D.sigma i j)
    + (D.meanCurvature / 3) * D.physicalMetric.g i j

/-- With zero conformal Killing term the shift-decorated extrinsic curvature is
the decomposition without a shift. -/
lemma extrinsicCurvatureOfShift_zero (D : ConformalData) :
    D.extrinsicCurvatureOfShift 0 = D.extrinsicCurvature := by
  funext i j
  simp [extrinsicCurvatureOfShift, extrinsicCurvature]

/-- The shift is twice continuously differentiable on the slice.  Seed-metric
regularity stays in the chart layer (`ChartInitialData.Regular`), since
`ConformalData` stores the seed pointwise. -/
def ShiftRegular (D : ConformalData) : Prop :=
  ∀ i : Fin 3, ContDiff ℝ 2 (fun x : Fin 3 → ℝ => D.shift x i)

/-- The transverse-traceless condition on `sigma` with respect to the seed
metric: `hbar^{ij} sigma_{ij} = 0`. -/
def IsTransverseTraceless (D : ConformalData) : Prop :=
  (∑ i : Fin 3, ∑ j : Fin 3, D.seed.ginv i j * D.sigma i j) = 0

end ConformalData

/-! ## B. The Lichnerowicz-York residuals -/

/-- The Hamiltonian (Lichnerowicz) residual `8 lap phi - R phi + |sigma|^2
phi^{-7}`, with the value of the seed Laplacian at the point supplied
explicitly. -/
noncomputable def hamiltonianResidual (lapPhi R sigmaSq phi : ℝ) : ℝ :=
  8 * lapPhi - R * phi + sigmaSq / phi ^ 7

/-- The linearised Lichnerowicz operator at the conformal factor `phi` in the
direction `psi`: `8 lap psi - R psi - 7 sigmaSq psi / phi^8`.  It is the Gateaux
derivative of `hamiltonianResidual` in `phi`, computed algebraically; no elliptic
theory enters. -/
noncomputable def linearisedHamiltonianResidual (lapPsi R sigmaSq phi psi : ℝ) : ℝ :=
  8 * lapPsi - R * psi - 7 * sigmaSq * psi / phi ^ 8

/-- The linearised Lichnerowicz operator is additive in the direction `psi`
(and in the Laplacian `lap psi`). -/
lemma linearisedHamiltonianResidual_add
    (lapPsi1 lapPsi2 R sigmaSq phi psi1 psi2 : ℝ) :
    linearisedHamiltonianResidual (lapPsi1 + lapPsi2) R sigmaSq phi (psi1 + psi2) =
      linearisedHamiltonianResidual lapPsi1 R sigmaSq phi psi1
        + linearisedHamiltonianResidual lapPsi2 R sigmaSq phi psi2 := by
  unfold linearisedHamiltonianResidual
  ring

/-- The linearised Lichnerowicz operator is homogeneous in the direction `psi`
(and in the Laplacian `lap psi`). -/
lemma linearisedHamiltonianResidual_smul (c lapPsi R sigmaSq phi psi : ℝ) :
    linearisedHamiltonianResidual (c * lapPsi) R sigmaSq phi (c * psi) =
      c * linearisedHamiltonianResidual lapPsi R sigmaSq phi psi := by
  unfold linearisedHamiltonianResidual
  ring

/-- In vacuum (`sigmaSq = 0`) the linearised operator is the conformal
Laplacian `8 lap psi - R psi`. -/
lemma linearisedHamiltonianResidual_vacuum (lapPsi R phi psi : ℝ) :
    linearisedHamiltonianResidual lapPsi R 0 phi psi = 8 * lapPsi - R * psi := by
  simp [linearisedHamiltonianResidual]

/-- Linearising the Hamiltonian residual in the conformal factor: along the
line `phi + t psi` (with Laplacian `lapPhi + t lapPsi`) the residual has
derivative `linearisedHamiltonianResidual` at `t = 0`, provided `phi ≠ 0`.
This is the algebraic first variation; existence and estimates for the operator
are the elliptic layer and are not claimed here. -/
lemma hasDerivAt_hamiltonianResidual
    (lapPhi lapPsi R sigmaSq phi psi : ℝ) (hphi : phi ≠ 0) :
    HasDerivAt
      (fun t : ℝ => hamiltonianResidual (lapPhi + t * lapPsi) R sigmaSq (phi + t * psi))
      (linearisedHamiltonianResidual lapPsi R sigmaSq phi psi) 0 := by
  have hlin := HasDerivAt.add (hasDerivAt_const (0 : ℝ) lapPhi)
    (HasDerivAt.mul_const (hasDerivAt_id 0) lapPsi)
  have hphit := HasDerivAt.add (hasDerivAt_const (0 : ℝ) phi)
    (HasDerivAt.mul_const (hasDerivAt_id 0) psi)
  have hpow := HasDerivAt.pow hphit 7
  have hg := HasDerivAt.add
    (HasDerivAt.sub (HasDerivAt.const_mul 8 hlin) (HasDerivAt.const_mul R hphit))
    (HasDerivAt.div (hasDerivAt_const (0 : ℝ) sigmaSq) hpow (by simpa using pow_ne_zero 7 hphi))
  have hfun : (fun t : ℝ => hamiltonianResidual (lapPhi + t * lapPsi) R sigmaSq (phi + t * psi)) =
      (fun t => 8 * (lapPhi + t * lapPsi) - R * (phi + t * psi) +
        sigmaSq / (phi + t * psi) ^ 7) := by
    funext t
    simp [hamiltonianResidual]
  rw [hfun]
  convert hg using 1
  · funext t; simp [Pi.add_apply, Pi.sub_apply, id_eq, mul_comm]
  · simp only [Pi.add_apply, Pi.pow_apply, id_eq, zero_mul, zero_add, one_mul,
      linearisedHamiltonianResidual]
    field_simp [hphi]
    ring

/-- The momentum residual `(div sigma)_i - (2/3) phi^6 (grad tau)_i`. -/
noncomputable def momentumResidual (divSigma gradTau : Fin 3 → ℝ) (phi : ℝ) :
    Fin 3 → ℝ :=
  fun i => divSigma i - (2 / 3) * phi ^ 6 * gradTau i

/-- Vanishing of both Lichnerowicz-York residuals at a point: the two
constraints are satisfied there.  This states the system; it is not a solution
theorem. -/
structure IsLichnerowiczYorkSolution (D : ConformalData) (lapPhi R sigmaSq : ℝ)
    (divSigma gradTau : Fin 3 → ℝ) : Prop where
  /-- The Hamiltonian constraint vanishes. -/
  hamiltonian : hamiltonianResidual lapPhi R sigmaSq D.phi = 0
  /-- The momentum constraint vanishes. -/
  momentum : ∀ i, momentumResidual divSigma gradTau D.phi i = 0

/-- With constant mean curvature the momentum residual is the divergence of
`sigma`. -/
lemma momentumResidual_zero_gradTau (divSigma : Fin 3 → ℝ) (phi : ℝ) :
    momentumResidual divSigma (fun _ => 0) phi = divSigma := by
  funext i
  simp [momentumResidual]

/-! ## C. The shift and the momentum constraint -/

/-- The momentum residual with a shift: the divergence of the conformal Killing
term plus the divergence of `sigma`, minus the mean-curvature source. -/
noncomputable def shiftMomentumResidual (divKilling divSigma gradTau : Fin 3 → ℝ)
    (phi : ℝ) : Fin 3 → ℝ :=
  fun i => divKilling i + divSigma i - (2 / 3) * phi ^ 6 * gradTau i

/-- With constant mean curvature and transverse `sigma` the shift residual is
the divergence of the conformal Killing term. -/
lemma shiftMomentumResidual_zero (divKilling : Fin 3 → ℝ) (phi : ℝ) :
    shiftMomentumResidual divKilling (fun _ => 0) (fun _ => 0) phi = divKilling := by
  funext i
  simp [shiftMomentumResidual]

/-- The momentum constraint for the shift at a point: the shift residual
vanishes.  The covariant divergences are inputs, as in `momentumResidual`. -/
structure IsShiftSolution (D : ConformalData) (divKilling divSigma gradTau : Fin 3 → ℝ) :
    Prop where
  /-- The momentum constraint for the shift vanishes. -/
  momentum : ∀ i, shiftMomentumResidual divKilling divSigma gradTau D.phi i = 0

end GeneralRelativity
