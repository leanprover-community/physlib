/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Particles.QED.Fields
/-!
# Spin-statistics of the QED fields

## i. Overview

The statistics of the fields of QED, as encoded in the QED jet algebra: the
electron jet coordinates anticommute among themselves and square to zero
(fermionic statistics), while the photon jet coordinates commute with
everything (bosonic statistics).

This file contains no definitions, only theorems about the fields of
`Physlib.Particles.QED.Fields`.

## ii. Key results

- `Electron.JetAlgebra.ofGenerator_mul_self`,
  `Electron.JetAlgebra.ofGenerator_anticommute` : fermionic statistics of the
  electron jet coordinates.
- `JetAlgebra.ψ_mul_ψ_anticomm`, `JetAlgebra.ψ_mul_barψ_anticomm`,
  `JetAlgebra.barψ_mul_barψ_anticomm` : the electron coordinates anticommute
  in the QED jet algebra.
- `JetAlgebra.ψ_mul_self`, `JetAlgebra.barψ_mul_self` : Pauli exclusion for
  the jet coordinates.
- `JetAlgebra.A_mul_A_comm`, `JetAlgebra.A_mul_ψ_comm`,
  `JetAlgebra.A_mul_barψ_comm` : the photon coordinates are bosonic.

## iii. Table of contents

- A. Fermionic statistics of the electron jet coordinates
- B. Fermionic statistics in the QED jet algebra
- C. Bosonic statistics of the photon jet coordinates

## iv. References

The fields are defined in `Physlib.Particles.QED.Fields`.

-/

@[expose] public section

namespace QED

/-!

## A. Fermionic statistics of the electron jet coordinates

-/

namespace Electron

namespace JetAlgebra

@[simp]
lemma ofGenerator_mul_self (j : JetGenerators) :
    ofGenerator j * ofGenerator j = 0 :=
  ExteriorAlgebra.ι_sq_zero _

/-- The jet coordinates of the electron anticommute: the electron is a
  fermion. -/
theorem ofGenerator_anticommute (i j : JetGenerators) :
    ofGenerator i * ofGenerator j = -(ofGenerator j * ofGenerator i) := by
  have h := ExteriorAlgebra.ι_sq_zero (R := ℂ) (M := JetComponentSpace)
    (Finsupp.single i 1 + Finsupp.single j 1)
  rw [map_add, add_mul, mul_add, mul_add, ExteriorAlgebra.ι_sq_zero,
    ExteriorAlgebra.ι_sq_zero, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

end JetAlgebra

end Electron

namespace JetAlgebra

/-!

## B. Fermionic statistics in the QED jet algebra

-/

/-- The electron jet coordinates anticommute. -/
theorem ψ_mul_ψ_anticomm (s t : Multiset (Fin 1 ⊕ Fin 3)) (α β : Fin 2 ⊕ Fin 2) :
    ψ s α * ψ t β = -(ψ t β * ψ s α) := by
  simp only [ψ, tmul_mul_tmul, one_mul]
  rw [Electron.JetAlgebra.ofGenerator_anticommute, tmul_neg]

/-- The electron and conjugate-electron jet coordinates anticommute. -/
theorem ψ_mul_barψ_anticomm (s t : Multiset (Fin 1 ⊕ Fin 3)) (α β : Fin 2 ⊕ Fin 2) :
    ψ s α * barψ t β = -(barψ t β * ψ s α) := by
  simp only [ψ, barψ, tmul_mul_tmul, one_mul]
  rw [Electron.JetAlgebra.ofGenerator_anticommute, tmul_neg]

/-- The conjugate-electron jet coordinates anticommute. -/
theorem barψ_mul_barψ_anticomm (s t : Multiset (Fin 1 ⊕ Fin 3)) (α β : Fin 2 ⊕ Fin 2) :
    barψ s α * barψ t β = -(barψ t β * barψ s α) := by
  simp only [barψ, tmul_mul_tmul, one_mul]
  rw [Electron.JetAlgebra.ofGenerator_anticommute, tmul_neg]

/-- Pauli exclusion: an electron jet coordinate squares to zero. -/
@[simp]
theorem ψ_mul_self (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2 ⊕ Fin 2) :
    ψ s α * ψ s α = 0 := by
  simp [ψ]

/-- Pauli exclusion: a conjugate electron jet coordinate squares to zero. -/
@[simp]
theorem barψ_mul_self (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2 ⊕ Fin 2) :
    barψ s α * barψ s α = 0 := by
  simp [barψ]

/-!

## C. Bosonic statistics of the photon jet coordinates

-/

/-- The photon jet coordinates commute among themselves: the photon is a
  boson. -/
theorem A_mul_A_comm (s t : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    A s μ * A t ν = A t ν * A s μ := by
  simp only [A, tmul_mul_tmul, mul_one]
  rw [mul_comm]

/-- The photon jet coordinates commute with the electron jet coordinates. -/
theorem A_mul_ψ_comm (s t : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (α : Fin 2 ⊕ Fin 2) :
    A s μ * ψ t α = ψ t α * A s μ := by
  simp only [A, ψ, tmul_mul_tmul, one_mul, mul_one]

/-- The photon jet coordinates commute with the conjugate electron jet
  coordinates. -/
theorem A_mul_barψ_comm (s t : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (α : Fin 2 ⊕ Fin 2) :
    A s μ * barψ t α = barψ t α * A s μ := by
  simp only [A, barψ, tmul_mul_tmul, one_mul, mul_one]

end JetAlgebra

end QED
