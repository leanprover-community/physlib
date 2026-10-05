/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Particles.QED.Lagrangian
public import Physlib.Particles.QED.FieldStrength
public import Mathlib.Tactic.Module
/-!
# Mass dimensions in quantum electrodynamics

## i. Overview

The mass-dimension bookkeeping of QED, through the mass-weight scaling of
`Physlib.Particles.QED.Basic` (the algebra map multiplying each jet coordinate by `c`
to twice its mass dimension): the photon has dimension one, the electron
`3/2`, and each derivative adds one.  The theorems of this file identify the
composite fields and the terms of the Lagrangian as eigenvectors of the
scaling:

* the covariant derivative `D_μ ψ` is homogeneous of weight five — this is
  the statement that the electric coupling `e` is dimensionless, which is
  what makes QED renormalizable;
* the Maxwell term and the Dirac kinetic term have weight eight (mass
  dimension four), and the mass term weight six (dimension three);
* consequently `L(e, c² m)` scales to `c⁸ L(e, m)`: the Lagrangian has mass
  dimension four with the electron mass a coefficient of dimension one.

This file contains no definitions, only theorems.

## ii. Key results

- `JetAlgebra.massScale_A_zero`, `JetAlgebra.massScale_ψ`, … : the scaling of
  the jet coordinates.
- `JetAlgebra.massScale_covDψ` : the covariant derivative is homogeneous of
  weight five; the coupling is dimensionless.
- `JetAlgebra.massScale_maxwellTerm`, `JetAlgebra.massScale_diracKineticTerm`,
  `JetAlgebra.massScale_electronMassTerm` : the weights of the terms.
- `JetAlgebra.massScale_lagrangian` : **the QED Lagrangian has mass dimension
  four**.

## iii. Table of contents

- A. The scaling of the jet coordinates
- B. Homogeneity of the field strength and the covariant derivative
- C. The weights of the terms of the Lagrangian
- D. The mass dimension of the QED Lagrangian

## iv. References

The scaling maps are defined in `Physlib.Particles.QED.Basic`; the corresponding
grading for the lepton–gauge sector is
`Physlib.Particles.LeptonGaugeSector.JetAlgebra.MassDim`.

-/

@[expose] public section

/-! TODO: Upgrade the mass-weight scaling to a genuine filtration by submodules, following -/
/-! TODO: `LeptonGaugeSector.JetAlgebra.MassDim` (`MassWeightLESubmodule`), together with the -/
/-! TODO: derivative-order and fermion-parity gradings needed for classification arguments. -/

namespace QED

open TensorProduct

namespace Photon

namespace JetAlgebra

/-!

## A. The scaling of the jet coordinates

The photon-level scaling of the field strength and the Maxwell term, used to
lift the weight of the Maxwell term to the QED jet algebra.

-/

/-- The photon-level field strength has mass dimension two. -/
lemma massScale_fieldStrength_zero (c : ℝ) (μ ν : Fin 1 ⊕ Fin 3) :
    massScale c (fieldStrength 0 μ ν) = c ^ 4 • fieldStrength 0 μ ν := by
  rw [fieldStrength, zero_add, zero_add, map_sub, massScale_coord, massScale_coord,
    smul_sub]
  norm_num

/-- The photon-level Maxwell term has mass dimension four. -/
theorem massScale_maxwellTerm (c : ℝ) :
    massScale c maxwellTerm = c ^ 8 • maxwellTerm := by
  rw [maxwellTerm, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_smul, map_mul, massScale_fieldStrength_zero, smul_mul_smul_comm,
    ← pow_add, smul_comm]

end JetAlgebra

end Photon

namespace JetAlgebra

theorem massScale_A (c : ℝ) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    massScale c (A s μ) = (c : ℂ) ^ (2 + 2 * Multiset.card s) • A s μ := by
  simp only [A]
  rw [massScale_tmul, map_one, massScalePhoton_tmul,
    Photon.JetAlgebra.massScale_coord, TensorProduct.tmul_smul, real_smul_tmul,
    Complex.ofReal_pow]

theorem massScale_ψ (c : ℝ) (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2 ⊕ Fin 2) :
    massScale c (ψ s α) = (c : ℂ) ^ (3 + 2 * Multiset.card s) • ψ s α := by
  simp only [ψ]
  rw [massScale_tmul, map_one, Electron.JetAlgebra.massScale_ofGenerator, tmul_smul]
  rfl

theorem massScale_barψ (c : ℝ) (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2 ⊕ Fin 2) :
    massScale c (barψ s α) = (c : ℂ) ^ (3 + 2 * Multiset.card s) • barψ s α := by
  simp only [barψ]
  rw [massScale_tmul, map_one, Electron.JetAlgebra.massScale_ofGenerator, tmul_smul]
  rfl

/-- The photon jet coordinate has mass dimension one. -/
theorem massScale_A_zero (c : ℝ) (μ : Fin 1 ⊕ Fin 3) :
    massScale c (A 0 μ) = (c : ℂ) ^ 2 • A 0 μ := by
  rw [massScale_A]
  norm_num

/-- The electron jet coordinate has mass dimension `3/2`. -/
theorem massScale_ψ_zero (c : ℝ) (α : Fin 2 ⊕ Fin 2) :
    massScale c (ψ 0 α) = (c : ℂ) ^ 3 • ψ 0 α := by
  rw [massScale_ψ]
  norm_num

theorem massScale_barψ_zero (c : ℝ) (α : Fin 2 ⊕ Fin 2) :
    massScale c (barψ 0 α) = (c : ℂ) ^ 3 • barψ 0 α := by
  rw [massScale_barψ]
  norm_num

theorem massScale_ψ_singleton (c : ℝ) (μ : Fin 1 ⊕ Fin 3) (α : Fin 2 ⊕ Fin 2) :
    massScale c (ψ {μ} α) = (c : ℂ) ^ 5 • ψ {μ} α := by
  rw [massScale_ψ]
  norm_num

theorem massScale_barψ_singleton (c : ℝ) (μ : Fin 1 ⊕ Fin 3) (α : Fin 2 ⊕ Fin 2) :
    massScale c (barψ {μ} α) = (c : ℂ) ^ 5 • barψ {μ} α := by
  rw [massScale_barψ]
  norm_num

/-!

## B. Homogeneity of the field strength and the covariant derivative

-/

/-- The field strength has mass dimension two. -/
theorem massScale_fieldStrength_zero (c : ℝ) (μ ν : Fin 1 ⊕ Fin 3) :
    massScale c (fieldStrength 0 μ ν) = (c : ℂ) ^ 4 • fieldStrength 0 μ ν := by
  rw [fieldStrength_eq_sub, map_sub, massScale_A, massScale_A, smul_sub]
  norm_num

/-- **The covariant derivative is homogeneous**, of the same weight as the
  plain derivative: the electric coupling `e` is dimensionless.  This is the
  power-counting statement behind the renormalizability of QED. -/
theorem massScale_covDψ (c : ℝ) (e : ℝ) (μ : Fin 1 ⊕ Fin 3) (α : Fin 2 ⊕ Fin 2) :
    massScale c (covDψ e μ α) = (c : ℂ) ^ 5 • covDψ e μ α := by
  rw [covDψ, map_add, map_smul, map_mul, massScale_ψ_singleton, massScale_A_zero,
    massScale_ψ_zero]
  simp only [smul_mul_smul_comm, smul_add, smul_smul]
  module

theorem massScale_covDbarψ (c : ℝ) (e : ℝ) (μ : Fin 1 ⊕ Fin 3) (α : Fin 2 ⊕ Fin 2) :
    massScale c (covDbarψ e μ α) = (c : ℂ) ^ 5 • covDbarψ e μ α := by
  rw [covDbarψ, map_sub, map_smul, map_mul, massScale_barψ_singleton,
    massScale_A_zero, massScale_barψ_zero]
  simp only [smul_mul_smul_comm, smul_sub, smul_smul]
  module

/-!

## C. The weights of the terms of the Lagrangian

-/

/-- The Maxwell term has mass dimension four. -/
theorem massScale_maxwellTerm (c : ℝ) :
    massScale c maxwellTerm = (c : ℂ) ^ 8 • maxwellTerm := by
  simp only [maxwellTerm]
  rw [massScale_tmul, map_one, massScalePhoton_tmul,
    Photon.JetAlgebra.massScale_maxwellTerm, TensorProduct.tmul_smul,
    real_smul_tmul, Complex.ofReal_pow]

/-- The Dirac kinetic term has mass dimension four. -/
theorem massScale_diracKineticTerm (c : ℝ) (e : ℝ) :
    massScale c (diracKineticTerm e) = (c : ℂ) ^ 8 • diracKineticTerm e := by
  rw [diracKineticTerm, map_smul, map_sum, smul_smul,
    mul_comm ((c : ℂ) ^ 8) Complex.I, ← smul_smul]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, map_mul, massScale_barψ_zero, massScale_covDψ, smul_mul_smul_comm,
    ← pow_add, smul_comm]

/-- The conjugate Dirac kinetic term has mass dimension four. -/
theorem massScale_diracKineticTermBar (c : ℝ) (e : ℝ) :
    massScale c (diracKineticTermBar e) = (c : ℂ) ^ 8 • diracKineticTermBar e := by
  rw [diracKineticTermBar, map_smul, map_sum, smul_smul,
    mul_comm ((c : ℂ) ^ 8) (-Complex.I), ← smul_smul]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, map_mul, massScale_covDbarψ, massScale_ψ_zero, smul_mul_smul_comm,
    ← pow_add, smul_comm]

/-- The Dirac mass term has mass dimension three. -/
theorem massScale_electronMassTerm (c : ℝ) :
    massScale c electronMassTerm = (c : ℂ) ^ 6 • electronMassTerm := by
  rw [electronMassTerm, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, map_mul, massScale_barψ_zero, massScale_ψ_zero, smul_mul_smul_comm,
    ← pow_add, smul_comm]

/-!

## D. The mass dimension of the QED Lagrangian

-/

/-- **The QED Lagrangian has mass dimension four.**  Rescaling all fields by
  their mass weights takes `L(e, c² m)` to `c⁸ L(e, m)`: the coupling `e` is
  dimensionless and the electron mass is a coefficient of dimension one, so
  every term of the Lagrangian is renormalizable. -/
theorem massScale_lagrangian (c : ℝ) (e m : ℝ) :
    massScale c (lagrangian e (c ^ 2 * m)) = (c : ℂ) ^ 8 • lagrangian e m := by
  rw [lagrangian, lagrangian, map_sub, map_add, map_smul, map_smul,
    massScale_maxwellTerm, massScale_diracKineticTerm, massScale_electronMassTerm]
  simp only [smul_smul, smul_add, smul_sub]
  push_cast
  module

end JetAlgebra

end QED
