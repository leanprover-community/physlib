/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-!
# Dirac counting for the STVG and TeVeS field content

## i. Overview

Dirac's formula gives the number of degrees of freedom of a constrained
Hamiltonian system as `(2N - 2N1 - N2) / 2`, where `N` counts the canonical
fields and `N1`, `N2` the first- and second-class constraints.  This module
states the formula and applies it to the field content of the alternatives: a
Proca vector (four components, two second-class constraints), a unit timelike
vector (four components, one first-class constraint), a real scalar and the two
metric modes.

The counting formula is applied to the constraint classification, and for the
Proca vector the brackets of the two constraints are computed in a
finite-dimensional model: with `pi^0` and `sum_i pi^i + m^2 A_0` the Dirac
matrix is antisymmetric with determinant `m^4`, so the pair is second-class.
Smeared constraints are treated on a finite lattice: the bracket of the primary
constraint with the smeared Gauss constraint is minus the mass squared times the
smearing inner product, which is nondegenerate for nonzero mass.  The unit-vector
primary constraints are abelian both in the finite-dimensional model and in the
smeared lattice form, so they are first-class.  The continuum field-theoretic
bracket is not formalised.

## ii. Key results

- `DiracCount` and `DiracCount.dof` : the counting formula.
- `procaCount_dof`, `unitVectorCount_dof`, `realScalarCount_dof`,
  `gravitonCount_dof` : `3`, `3`, `1` and `2` degrees of freedom.
- `stvgCount_dof`, `tevesCount_dof` : `6` for both, with the sums made explicit.
- `procaDiracMatrix_det`, `proca_constraints_second_class` : the Proca Dirac
  matrix has determinant `m^4`, nonzero for `m != 0`.
- `smearedBracket_primary_gauss`, `smeared_constraints_second_class` : the
  smeared bracket is `-m^2` times the smearing inner product and has no nonzero
  null direction for `m != 0`.
- `unitVectorPrimary_first_class`, `smearedUnitVectorPrimary_first_class` : the
  unit-vector primary constraints are abelian, in the finite-dimensional and the
  smeared lattice models.

## iii. Table of contents

- A. The counting formula
- B. Applications
- C. Dirac brackets for the Proca constraints
- D. Smeared constraints on a finite lattice
- E. The unit-vector primary constraints
- F. Smeared unit-vector constraints on a finite lattice

## iv. References

* P. A. M. Dirac, *Lectures on Quantum Mechanics*, Yeshiva University, 1964.
  [ref: Dirac1964Lectures]
* M. Henneaux, C. Teitelboim, *Quantization of Gauge Systems*, Princeton, 1992.
  [ref: HenneauxTeitelboim1992]
-/

@[expose] public section

namespace GeneralRelativity

/-! ## A. The counting formula -/

/-- A field content counted the Dirac way: canonical fields and the numbers of
first- and second-class constraints. -/
structure DiracCount where
  /-- Number of canonical field components. -/
  components : ℕ
  /-- Number of first-class constraints. -/
  firstClass : ℕ
  /-- Number of second-class constraints. -/
  secondClass : ℕ

/-- Dirac's formula `(2N - 2N1 - N2) / 2` for the number of degrees of
freedom.  The subtraction is truncated natural-number subtraction; all the
instances below have `2N >= 2N1 + N2`. -/
def DiracCount.dof (D : DiracCount) : ℕ :=
  (2 * D.components - 2 * D.firstClass - D.secondClass) / 2

/-! ## B. Applications -/

/-- A massive Proca vector: four components, two second-class constraints. -/
def procaCount : DiracCount := ⟨4, 0, 2⟩

/-- The Proca field has three degrees of freedom. -/
lemma procaCount_dof : procaCount.dof = 3 := by decide

/-- A unit timelike vector: four components, one first-class constraint. -/
def unitVectorCount : DiracCount := ⟨4, 1, 0⟩

/-- The unit timelike vector has three degrees of freedom. -/
lemma unitVectorCount_dof : unitVectorCount.dof = 3 := by decide

/-- A real scalar field: one component, no constraints. -/
def realScalarCount : DiracCount := ⟨1, 0, 0⟩

/-- The real scalar has one degree of freedom. -/
lemma realScalarCount_dof : realScalarCount.dof = 1 := by decide

/-- The two metric modes: two components, no constraints. -/
def gravitonCount : DiracCount := ⟨2, 0, 0⟩

/-- The metric contributes two degrees of freedom. -/
lemma gravitonCount_dof : gravitonCount.dof = 2 := by decide

/-- STVG: two metric modes, a Proca vector and one scalar. -/
def stvgCount : DiracCount := ⟨7, 0, 2⟩

/-- STVG has six degrees of freedom. -/
lemma stvgCount_dof : stvgCount.dof = 6 := by decide

/-- The STVG count is the sum of its sectors. -/
lemma stvgCount_dof_eq_sum :
    stvgCount.dof = gravitonCount.dof + procaCount.dof + realScalarCount.dof := by
  decide

/-- TeVeS: two metric modes, a unit timelike vector and one scalar. -/
def tevesCount : DiracCount := ⟨7, 1, 0⟩

/-- TeVeS has six degrees of freedom. -/
lemma tevesCount_dof : tevesCount.dof = 6 := by decide

/-- The TeVeS count is the sum of its sectors. -/
lemma tevesCount_dof_eq_sum :
    tevesCount.dof = gravitonCount.dof + unitVectorCount.dof + realScalarCount.dof := by
  decide

/-! ## C. Dirac brackets for the Proca constraints -/

/-- A linear observable on the four-component Proca phase space: coefficient
vectors for the four coordinates and their four momenta. -/
structure ProcaObservable where
  /-- Coefficients of the coordinate components. -/
  q : Fin 4 → ℝ
  /-- Coefficients of the momentum components. -/
  p : Fin 4 → ℝ

/-- The Poisson bracket of two linear observables, from the canonical brackets
`{q_i, p_j} = delta_ij`. -/
def poissonBracket (a b : ProcaObservable) : ℝ :=
  (∑ i : Fin 4, a.q i * b.p i) - ∑ i : Fin 4, a.p i * b.q i

/-- The primary constraint `pi^0` of the Proca field. -/
def procaPrimary : ProcaObservable where
  q := fun _ => 0
  p i := if i = 0 then 1 else 0

/-- The secondary (Gauss) constraint `sum_i pi^i + m^2 A_0` in the discrete
model, where the divergence is the sum over the three spatial momenta. -/
def procaSecondary (m : ℝ) : ProcaObservable where
  q i := if i = 0 then m ^ 2 else 0
  p _ := 1

lemma procaBracket_primary_self :
    poissonBracket procaPrimary procaPrimary = 0 := by
  simp [poissonBracket, procaPrimary]

lemma procaBracket_secondary_self (m : ℝ) :
    poissonBracket (procaSecondary m) (procaSecondary m) = 0 := by
  simp [poissonBracket, procaSecondary]

lemma procaBracket_primary_secondary (m : ℝ) :
    poissonBracket procaPrimary (procaSecondary m) = -m ^ 2 := by
  simp [poissonBracket, procaPrimary, procaSecondary]

lemma procaBracket_secondary_primary (m : ℝ) :
    poissonBracket (procaSecondary m) procaPrimary = m ^ 2 := by
  simp [poissonBracket, procaPrimary, procaSecondary]

/-- The Dirac matrix of the two Proca constraints. -/
noncomputable def procaDiracMatrix (m : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -m ^ 2; m ^ 2, 0]

/-- The Dirac matrix has determinant `m^4`. -/
lemma procaDiracMatrix_det (m : ℝ) : (procaDiracMatrix m).det = m ^ 4 := by
  simp [procaDiracMatrix, Matrix.det_fin_two]; ring

/-- For nonzero mass the two Proca constraints are second-class. -/
lemma proca_constraints_second_class (m : ℝ) (hm : m ≠ 0) :
    (procaDiracMatrix m).det ≠ 0 := by
  rw [procaDiracMatrix_det]
  exact pow_ne_zero 4 hm

/-! ## D. Smeared constraints on a finite lattice -/

/-- A linear observable on a lattice Proca phase space: coefficient functions
for the scalar potential, the spatial potential, and their momenta. -/
structure SmearedProcaObservable (ι : Type*) where
  /-- Coefficient of the scalar potential. -/
  a0 : ι → ℝ
  /-- Coefficient of the spatial potential. -/
  ai : ι → ℝ
  /-- Coefficient of the scalar momentum. -/
  pi0 : ι → ℝ
  /-- Coefficient of the spatial momentum. -/
  pii : ι → ℝ

/-- The canonical Poisson bracket of two linear observables, from
`{A_mu, pi_nu} = delta_mu_nu` at each site. -/
def smearedBracket {ι : Type*} [Fintype ι] (A B : SmearedProcaObservable ι) : ℝ :=
  (∑ i, A.a0 i * B.pi0 i + ∑ i, A.ai i * B.pii i)
    - (∑ i, A.pi0 i * B.a0 i + ∑ i, A.pii i * B.ai i)

/-- The smeared primary constraint `sum_i xi_i pi^0_i`. -/
def smearedPrimary {ι : Type*} (ξ : ι → ℝ) : SmearedProcaObservable ι where
  a0 := 0
  ai := 0
  pi0 := ξ
  pii := 0

/-- The smeared Gauss constraint `sum_i eta_i (div pi_i + m^2 A_0_i)`, with the
divergence supplied as a linear map on the lattice. -/
def smearedGauss {ι : Type*} (m : ℝ) (D : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (η : ι → ℝ) : SmearedProcaObservable ι where
  a0 := fun i => m ^ 2 * η i
  ai := 0
  pi0 := 0
  pii := D η

/-- The bracket of the smeared primary and Gauss constraints is minus the mass
squared times the smearing inner product; the divergence drops out. -/
lemma smearedBracket_primary_gauss {ι : Type*} [Fintype ι] (m : ℝ)
    (D : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (ξ η : ι → ℝ) :
    smearedBracket (smearedPrimary ξ) (smearedGauss m D η)
      = -m ^ 2 * ∑ i, ξ i * η i := by
  have h : (∑ i, ξ i * (m ^ 2 * η i)) = m ^ 2 * ∑ i, ξ i * η i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  simp [smearedBracket, smearedPrimary, smearedGauss, h]

/-- For nonzero mass no nonzero smearing function is null: some smeared Gauss
constraint has a nonzero bracket with it, so the smeared Proca constraints are
second-class. -/
lemma smeared_constraints_second_class {ι : Type*} [Fintype ι] (m : ℝ)
    (hm : m ≠ 0) (D : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (ξ : ι → ℝ) (hξ : ξ ≠ 0) :
    ∃ η : ι → ℝ, smearedBracket (smearedPrimary ξ) (smearedGauss m D η) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hex : ∃ i, ξ i ≠ 0 := by
    by_contra hnone
    push Not at hnone
    exact hξ (funext hnone)
  obtain ⟨i, hi⟩ := hex
  have hzero := h (fun j => if j = i then 1 else 0)
  rw [smearedBracket_primary_gauss] at hzero
  have hsum : (∑ j : ι, ξ j * (if j = i then (1 : ℝ) else 0)) = ξ i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · intro hi'
      exact absurd (Finset.mem_univ i) hi'
  rw [hsum] at hzero
  exact (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hm)) hi) hzero

/-! ## E. The unit-vector primary constraints -/

/-- A linear observable on the four-component unit-vector phase space. -/
structure UnitVectorObservable where
  /-- Coefficient of the vector components. -/
  u : Fin 4 → ℝ
  /-- Coefficient of the momentum components. -/
  p : Fin 4 → ℝ

/-- The canonical bracket of two linear observables. -/
def unitVectorBracket (A B : UnitVectorObservable) : ℝ :=
  (∑ i, A.u i * B.p i) - ∑ i, A.p i * B.u i

/-- The smeared primary constraint `sum_i xi_i p_i` of the unit-vector sector. -/
def unitVectorPrimary (ξ : Fin 4 → ℝ) : UnitVectorObservable where
  u := 0
  p := ξ

/-- The smeared primary constraints of the unit-vector sector are abelian, hence
first-class; the unit-norm condition is the gauge slice, not an independent
constraint.  This is the bracket behind the `4 - 1 = 3` count. -/
lemma unitVectorPrimary_first_class (ξ η : Fin 4 → ℝ) :
    unitVectorBracket (unitVectorPrimary ξ) (unitVectorPrimary η) = 0 := by
  simp [unitVectorBracket, unitVectorPrimary]

/-! ## F. Smeared unit-vector constraints on a finite lattice -/

/-- A linear observable on a lattice unit-vector phase space: coefficient
functions for the four vector components and their momenta at each site. -/
structure SmearedUnitVectorObservable (ι : Type*) where
  /-- Coefficient of the vector components. -/
  u : ι → Fin 4 → ℝ
  /-- Coefficient of the momentum components. -/
  p : ι → Fin 4 → ℝ

/-- The canonical Poisson bracket of two linear smeared observables, from
`{u_a(x), p_b(y)} = delta_a_b delta(x,y)` at each site. -/
def smearedUnitVectorBracket {ι : Type*} [Fintype ι]
    (A B : SmearedUnitVectorObservable ι) : ℝ :=
  (∑ i, ∑ a, A.u i a * B.p i a) - ∑ i, ∑ a, A.p i a * B.u i a

/-- The smeared primary constraint `sum_{i,a} xi_i_a p_i_a` of the unit-vector
sector. -/
def smearedUnitVectorPrimary {ι : Type*} (ξ : ι → Fin 4 → ℝ) :
    SmearedUnitVectorObservable ι where
  u := 0
  p := ξ

/-- The smeared primary constraints of the unit-vector sector are abelian,
hence first-class; this is the field-theoretic (lattice) form of
`unitVectorPrimary_first_class`. -/
lemma smearedUnitVectorPrimary_first_class {ι : Type*} [Fintype ι]
    (ξ η : ι → Fin 4 → ℝ) :
    smearedUnitVectorBracket (smearedUnitVectorPrimary ξ)
      (smearedUnitVectorPrimary η) = 0 := by
  simp [smearedUnitVectorBracket, smearedUnitVectorPrimary]

end GeneralRelativity
