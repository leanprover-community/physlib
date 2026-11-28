/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Cosmology.FLRW.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Linear scalar perturbations of an FLRW background

## i. Overview

This module starts the linear-perturbation layer of the alternatives programme
(T9.4).  It fixes the scalar sector of a metric perturbation on a comoving FLRW
background `S`, in the "supplied gradient" idiom used elsewhere in the
development: the two scalar potentials `phi`, `psi` and the supplied first and
second spatial-gradient data `B`, `E` are given as fields, so no spatial
derivative operator is needed.  The perturbed metric is the background metric
plus the scalar perturbation, and the module proves that the perturbation
vanishes for the zero data (background recovery) and that the perturbation is
symmetric whenever the second-gradient data `E` is symmetric.  The gauge
transformation and the Bardeen potentials are proved invariant, and the
anisotropic (ij-traceless) sector of the perturbed field equations is started:
its gauge-invariant source is `bardeenPhi - bardeenPsi`, so the two Bardeen
potentials coincide when the anisotropic stress vanishes.  The energy (00),
momentum (0i) and pressure (ij-trace) field equations are then stated in the
gauge-invariant Bardeen form and proved invariant under the scalar gauge
transformation.

## ii. Key results

- `ScalarPerturbation` : the scalar-sector data `(phi, psi, B, E)`.
- `perturbationMetric`, `perturbedMetric` : the scalar perturbation and the
  perturbed FLRW metric.
- `perturbationMetric_zero`, `perturbedMetric_zero` : background recovery.
- `perturbationMetric_symm` : symmetry from a symmetric `E`.
- `bardeenPhi`, `bardeenPsi` : the gauge-invariant Bardeen potentials.
- `bardeenPhi_invariant`, `bardeenPsi_invariant` : gauge invariance.
- `anisotropicSource`, `anisotropicSource_eq_bardeen` : the gauge-invariant
  anisotropic (ij-traceless) source `bardeenPhi - bardeenPsi`.
- `bardeenPhi_eq_bardeenPsi_of_no_anisotropic` : the Bardeen potentials
  coincide when the anisotropic stress vanishes.
- `anisotropicSource_gauge` : gauge invariance of the anisotropic source.
- `ScalarStress`, `BardeenData` : the gauge-invariant stress and Bardeen data.
- `energyEquation`, `momentumEquation`, `pressureEquation` : the perturbed
  field equations in Bardeen form.
- `PerturbedFieldEq` : the bundle of the three equations.
- `bardeenData_gauge`, `perturbedFieldEq_gauge` : gauge invariance of the
  Bardeen data and of the field equations.
- `bardeenEvolution` : the Bardeen evolution (master) equation, obtained from
  the energy and pressure equations in a perfect fluid with no anisotropic
  stress.

## iii. Table of contents

- A. The scalar-sector data
- B. The perturbed metric
- C. The gauge transformation and the Bardeen potentials
- D. The perturbed field equations: the anisotropic sector
- E. The perturbed field equations: the energy, momentum and pressure sectors

## iv. References

* V. F. Mukhanov, *Physical Foundations of Cosmology*, Cambridge, 2005, Ch. 6.
* S. Weinberg, *Cosmology*, Oxford, 2008, Ch. 5.
-/

@[expose] public section

open GeneralRelativity

namespace Cosmology

namespace FLRW

/-! ## A. The scalar-sector data -/

/-- The scalar-sector data of a linear metric perturbation on an FLRW
background: the two scalar potentials `phi`, `psi` and the supplied first and
second spatial-gradient fields `B`, `E`. -/
structure ScalarPerturbation where
  /-- The lapse perturbation potential. -/
  phi : (Fin 4 → ℝ) → ℝ
  /-- The curvature perturbation potential. -/
  psi : (Fin 4 → ℝ) → ℝ
  /-- The supplied first spatial gradient of the shift potential. -/
  B : (Fin 4 → ℝ) → (Fin 4 → ℝ)
  /-- The supplied second spatial gradient of the scalar potential. -/
  E : (Fin 4 → ℝ) → (Fin 4 → Fin 4 → ℝ)

/-- The zero scalar perturbation. -/
def ScalarPerturbation.zero : ScalarPerturbation where
  phi := 0
  psi := 0
  B := 0
  E := 0

/-! ## B. The perturbed metric -/

/-- The scalar metric perturbation `delta g` in comoving coordinates, built from
the lapse potential `phi`, the curvature potential `psi`, and the supplied
gradient data `B`, `E`:
`delta g_00 = -2 a^2 phi`, `delta g_0i = a^2 B_i`,
`delta g_ij = a^2 (-2 psi delta_ij + 2 E_ij)`. -/
noncomputable def perturbationMetric (S : FLRWSpacetime) (P : ScalarPerturbation)
    (x : Fin 4 → ℝ) : Tensor2 4 :=
  Matrix.of fun i j =>
    if i = 0 ∧ j = 0 then -2 * (S.a (x 0)) ^ 2 * P.phi x
    else if i = 0 then (S.a (x 0)) ^ 2 * P.B x j
    else if j = 0 then (S.a (x 0)) ^ 2 * P.B x i
    else (S.a (x 0)) ^ 2 * (-2 * P.psi x * (if i = j then 1 else 0) + 2 * P.E x i j)

/-- The perturbed FLRW metric `g + delta g`. -/
noncomputable def perturbedMetric (S : FLRWSpacetime) (P : ScalarPerturbation)
    (x : Fin 4 → ℝ) : Tensor2 4 :=
  S.metric x + perturbationMetric S P x

/-- The scalar perturbation vanishes for the zero data. -/
lemma perturbationMetric_zero (S : FLRWSpacetime) (x : Fin 4 → ℝ) :
    perturbationMetric S ScalarPerturbation.zero x = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [perturbationMetric, ScalarPerturbation.zero]

/-- The perturbed metric reduces to the background for the zero data. -/
lemma perturbedMetric_zero (S : FLRWSpacetime) (x : Fin 4 → ℝ) :
    perturbedMetric S ScalarPerturbation.zero x = S.metric x := by
  rw [perturbedMetric, perturbationMetric_zero]
  simp

/-- The scalar perturbation is symmetric whenever the second-gradient data `E`
is symmetric. -/
lemma perturbationMetric_symm (S : FLRWSpacetime) (P : ScalarPerturbation)
    (hE : ∀ x i j, P.E x i j = P.E x j i) (x : Fin 4 → ℝ) :
    IsSymm (perturbationMetric S P x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [perturbationMetric, hE, Matrix.transpose_apply]

/-! ## C. The gauge transformation and the Bardeen potentials -/

/-- The gauge-transformed lapse potential `phi - xi0' - (a'/a) xi0`. -/
noncomputable def gaugePhi (a a' phi xi0 xi0' : ℝ) : ℝ :=
  phi - xi0' - (a' / a) * xi0

/-- The gauge-transformed curvature potential `psi + (a'/a) xi0`. -/
noncomputable def gaugePsi (a a' psi xi0 : ℝ) : ℝ :=
  psi + (a' / a) * xi0

/-- The gauge-transformed shift gradient `B + xi0 - xi'`. -/
noncomputable def gaugeB (B xi0 xi' : ℝ) : ℝ :=
  B + xi0 - xi'

/-- The gauge-transformed second-gradient scalar `E - xi`. -/
noncomputable def gaugeE (E xi : ℝ) : ℝ :=
  E - xi

/-- The Bardeen lapse potential `Phi = phi + (a'/a)(B - E') + (B' - E'')`. -/
noncomputable def bardeenPhi (a a' phi B E' B' E'' : ℝ) : ℝ :=
  phi + (a' / a) * (B - E') + (B' - E'')

/-- The Bardeen curvature potential `Psi = psi - (a'/a)(B - E')`. -/
noncomputable def bardeenPsi (a a' psi B E' : ℝ) : ℝ :=
  psi - (a' / a) * (B - E')

/-- The Bardeen lapse potential is invariant under the scalar gauge
transformation. -/
lemma bardeenPhi_invariant (a a' phi B E' B' E'' xi0 xi0' xi' xi'') (ha : a ≠ 0) :
    bardeenPhi a a' (gaugePhi a a' phi xi0 xi0') (gaugeB B xi0 xi') (E' - xi')
        (B' + xi0' - xi'') (E'' - xi'') =
      bardeenPhi a a' phi B E' B' E'' := by
  simp only [bardeenPhi, gaugePhi, gaugeB]
  field_simp
  ring

/-- The Bardeen curvature potential is invariant under the scalar gauge
transformation. -/
lemma bardeenPsi_invariant (a a' psi B E' xi0 xi') (ha : a ≠ 0) :
    bardeenPsi a a' (gaugePsi a a' psi xi0) (gaugeB B xi0 xi') (E' - xi') =
      bardeenPsi a a' psi B E' := by
  simp only [bardeenPsi, gaugePsi, gaugeB]
  field_simp
  ring

/-! ## D. The perturbed field equations: the anisotropic sector -/

/-- The gauge-invariant anisotropic (ij-traceless) source of the perturbed
field equations, `bardeenPhi - bardeenPsi`, written out in the metric data:
`(phi - psi) + 2 (a'/a)(B - E') + (B' - E'')`. -/
noncomputable def anisotropicSource (a a' phi psi B E' B' E'' : ℝ) : ℝ :=
  (phi - psi) + 2 * (a' / a) * (B - E') + (B' - E'')

/-- The anisotropic source is the difference of the Bardeen potentials. -/
lemma anisotropicSource_eq_bardeen (a a' phi psi B E' B' E'' : ℝ) :
    anisotropicSource a a' phi psi B E' B' E'' =
      bardeenPhi a a' phi B E' B' E'' - bardeenPsi a a' psi B E' := by
  simp only [anisotropicSource, bardeenPhi, bardeenPsi]
  ring

/-- When the anisotropic stress vanishes, the two Bardeen potentials coincide:
the ij-traceless field equation forces `Phi = Psi`. -/
lemma bardeenPhi_eq_bardeenPsi_of_no_anisotropic (a a' phi psi B E' B' E'' κ sigma : ℝ)
    (h : anisotropicSource a a' phi psi B E' B' E'' = κ * sigma) (hs : sigma = 0) :
    bardeenPhi a a' phi B E' B' E'' = bardeenPsi a a' psi B E' := by
  rw [hs, mul_zero] at h
  rw [anisotropicSource_eq_bardeen a a' phi psi B E' B' E''] at h
  exact sub_eq_zero.mp h

/-- The anisotropic source is invariant under the scalar gauge transformation,
so the anisotropic field equation is gauge-invariant. -/
lemma anisotropicSource_gauge (a a' phi psi B E' B' E'' xi0 xi0' xi' xi'') (ha : a ≠ 0) :
    anisotropicSource a a' (gaugePhi a a' phi xi0 xi0') (gaugePsi a a' psi xi0)
        (gaugeB B xi0 xi') (E' - xi') (B' + xi0' - xi'') (E'' - xi'') =
      anisotropicSource a a' phi psi B E' B' E'' := by
  calc
    anisotropicSource a a' (gaugePhi a a' phi xi0 xi0') (gaugePsi a a' psi xi0)
        (gaugeB B xi0 xi') (E' - xi') (B' + xi0' - xi'') (E'' - xi'') =
        bardeenPhi a a' (gaugePhi a a' phi xi0 xi0') (gaugeB B xi0 xi')
          (E' - xi') (B' + xi0' - xi'') (E'' - xi'') -
          bardeenPsi a a' (gaugePsi a a' psi xi0) (gaugeB B xi0 xi') (E' - xi') :=
      anisotropicSource_eq_bardeen _ _ _ _ _ _ _ _
    _ = bardeenPhi a a' phi B E' B' E'' - bardeenPsi a a' psi B E' := by
      rw [bardeenPhi_invariant a a' phi B E' B' E'' xi0 xi0' xi' xi'' ha,
        bardeenPsi_invariant a a' psi B E' xi0 xi' ha]
    _ = anisotropicSource a a' phi psi B E' B' E'' :=
      (anisotropicSource_eq_bardeen a a' phi psi B E' B' E'').symm

/-! ## E. The perturbed field equations: the energy, momentum and pressure sectors -/

/-- The scalar-sector stress data of the perturbed matter, in the
gauge-invariant (Newtonian) form: the density and pressure perturbations
`deltaRho`, `deltaP`, the velocity potential `v`, and the anisotropic stress
`Pi`. -/
structure ScalarStress where
  /-- The density perturbation. -/
  deltaRho : ℝ
  /-- The pressure perturbation. -/
  deltaP : ℝ
  /-- The velocity potential. -/
  v : ℝ
  /-- The anisotropic stress. -/
  Pi : ℝ

/-- The gauge-invariant Bardeen data: the two Bardeen potentials `Phi`, `Psi`
and their supplied conformal-time derivatives and Laplacians. -/
@[ext]
structure BardeenData where
  /-- The Bardeen lapse potential. -/
  Phi : ℝ
  /-- The Bardeen curvature potential. -/
  Psi : ℝ
  /-- The conformal-time derivative of `Phi`. -/
  Phi1 : ℝ
  /-- The conformal-time derivative of `Psi`. -/
  Psi1 : ℝ
  /-- The second conformal-time derivative of `Psi`. -/
  Psi2 : ℝ
  /-- The Laplacian of `Phi`. -/
  lapPhi : ℝ
  /-- The Laplacian of `Psi`. -/
  lapPsi : ℝ

/-- The energy (00) field equation in Bardeen form,
`3 H (Psi' + H Phi) - lap Psi = -kappa a^2 deltaRho`. -/
def energyEquation (a H : ℝ) (D : BardeenData) (T : ScalarStress) (κ : ℝ) : Prop :=
  3 * H * (D.Psi1 + H * D.Phi) - D.lapPsi = -κ * a ^ 2 * T.deltaRho

/-- The momentum (0i) field equation in Bardeen form,
`Psi' + H Phi = kappa a^2 (rho + p) v`. -/
def momentumEquation (a H ρ p : ℝ) (D : BardeenData) (T : ScalarStress) (κ : ℝ) : Prop :=
  D.Psi1 + H * D.Phi = κ * a ^ 2 * (ρ + p) * T.v

/-- The pressure (ij-trace) field equation in Bardeen form,
`Psi'' + H (Phi' + 2 Psi') + (2 H' + H^2) Phi + (1/3) lap (Phi - Psi) =
kappa a^2 deltaP`. -/
def pressureEquation (a H H1 : ℝ) (D : BardeenData) (T : ScalarStress) (κ : ℝ) : Prop :=
  D.Psi2 + H * (D.Phi1 + 2 * D.Psi1) + (2 * H1 + H ^ 2) * D.Phi
    + (1 / 3) * (D.lapPhi - D.lapPsi) = κ * a ^ 2 * T.deltaP

/-- The perturbed field equations: the energy, momentum and pressure equations
in Bardeen form, bundled. -/
structure PerturbedFieldEq (a H H1 ρ p κ : ℝ) (D : BardeenData) (T : ScalarStress) : Prop where
  /-- The energy (00) equation. -/
  energy : energyEquation a H D T κ
  /-- The momentum (0i) equation. -/
  momentum : momentumEquation a H ρ p D T κ
  /-- The pressure (ij-trace) equation. -/
  pressure : pressureEquation a H H1 D T κ

/-- The scalar kinematics of a point: the background scale factor `a` and its
conformal-time derivative `a1`, the metric potentials `phi`, `psi`, `B`, `E1`,
`B1`, `E2`, and the supplied conformal-time derivatives and Laplacians of the
Bardeen potentials. -/
structure ScalarKinematics where
  /-- The background scale factor. -/
  a : ℝ
  /-- The conformal-time derivative of the scale factor. -/
  a1 : ℝ
  /-- The first scalar potential `phi`. -/
  phi : ℝ
  /-- The second scalar potential `psi`. -/
  psi : ℝ
  /-- The supplied first spatial gradient `B`. -/
  B : ℝ
  /-- The supplied first spatial gradient `E'`. -/
  E1 : ℝ
  /-- The supplied conformal-time derivative `B'`. -/
  B1 : ℝ
  /-- The supplied second spatial gradient `E''`. -/
  E2 : ℝ
  /-- The conformal-time derivative of `phi`. -/
  phi1 : ℝ
  /-- The conformal-time derivative of `psi`. -/
  psi1 : ℝ
  /-- The second conformal-time derivative of `psi`. -/
  psi2 : ℝ
  /-- The supplied Laplacian of `phi`. -/
  lapPhi : ℝ
  /-- The supplied Laplacian of `psi`. -/
  lapPsi : ℝ

/-- The Bardeen data of a kinematics point. -/
noncomputable def bardeenData (K : ScalarKinematics) : BardeenData where
  Phi := bardeenPhi K.a K.a1 K.phi K.B K.E1 K.B1 K.E2
  Psi := bardeenPsi K.a K.a1 K.psi K.B K.E1
  Phi1 := K.phi1
  Psi1 := K.psi1
  Psi2 := K.psi2
  lapPhi := K.lapPhi
  lapPsi := K.lapPsi

/-- The gauge transform of a kinematics point: the metric potentials transform
as in Section C, while the background and the supplied Bardeen derivative data
are inert. -/
noncomputable def gaugeKinematics (K : ScalarKinematics) (xi0 xi0' xi' xi'' : ℝ) : ScalarKinematics where
  a := K.a
  a1 := K.a1
  phi := gaugePhi K.a K.a1 K.phi xi0 xi0'
  psi := gaugePsi K.a K.a1 K.psi xi0
  B := gaugeB K.B xi0 xi'
  E1 := K.E1 - xi'
  B1 := K.B1 + xi0' - xi''
  E2 := K.E2 - xi''
  phi1 := K.phi1
  psi1 := K.psi1
  psi2 := K.psi2
  lapPhi := K.lapPhi
  lapPsi := K.lapPsi

/-- The Bardeen data is invariant under the scalar gauge transformation. -/
lemma bardeenData_gauge (K : ScalarKinematics) (xi0 xi0' xi' xi'' : ℝ) (ha : K.a ≠ 0) :
    bardeenData (gaugeKinematics K xi0 xi0' xi' xi'') = bardeenData K := by
  ext
  · simp only [bardeenData, gaugeKinematics]
    exact bardeenPhi_invariant K.a K.a1 K.phi K.B K.E1 K.B1 K.E2 xi0 xi0' xi' xi'' ha
  · simp only [bardeenData, gaugeKinematics]
    exact bardeenPsi_invariant K.a K.a1 K.psi K.B K.E1 xi0 xi' ha
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The perturbed field equations are invariant under the scalar gauge
transformation. -/
lemma perturbedFieldEq_gauge (K : ScalarKinematics) (T : ScalarStress) (H H1 ρ p κ : ℝ)
    (xi0 xi0' xi' xi'' : ℝ) (ha : K.a ≠ 0) :
    PerturbedFieldEq K.a H H1 ρ p κ (bardeenData (gaugeKinematics K xi0 xi0' xi' xi'')) T ↔
      PerturbedFieldEq K.a H H1 ρ p κ (bardeenData K) T := by
  rw [bardeenData_gauge K xi0 xi0' xi' xi'' ha]

/-- The Bardeen evolution (master) equation: in a perfect fluid with
`deltaP = c_s^2 deltaRho` and no anisotropic stress (so `Phi = Psi`), the
energy and pressure equations combine to
`Psi'' + 3 H (1 + c_s^2) Psi' + (2 H' + (1 + 3 c_s^2) H^2) Phi - c_s^2 lap Phi = 0`. -/
lemma bardeenEvolution (a H H1 κ c_s : ℝ) (D : BardeenData) (T : ScalarStress)
    (hPhi : D.Phi = D.Psi) (hPhi1 : D.Phi1 = D.Psi1) (hLap : D.lapPhi = D.lapPsi)
    (hcs : T.deltaP = c_s ^ 2 * T.deltaRho)
    (hE : energyEquation a H D T κ) (hP : pressureEquation a H H1 D T κ) :
    D.Psi2 + 3 * H * (1 + c_s ^ 2) * D.Psi1
      + (2 * H1 + (1 + 3 * c_s ^ 2) * H ^ 2) * D.Phi - c_s ^ 2 * D.lapPhi = 0 := by
  unfold energyEquation at hE
  unfold pressureEquation at hP
  rw [hPhi] at hE
  rw [hPhi, hPhi1, hLap] at hP
  rw [hcs] at hP
  rw [hPhi, hLap]
  nlinarith [hE, hP]

end FLRW

end Cosmology