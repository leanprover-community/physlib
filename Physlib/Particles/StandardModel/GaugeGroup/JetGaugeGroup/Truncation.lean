/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.LocalGaugeData
public import Physlib.Relativity.JetRing.Matrix
/-!
# Truncation of the jet gauge group

## i. Overview

Truncating a jet of gauge transformations at order `n` sets to zero, in every matrix
entry, the Taylor coefficients of total degree above `n`. This `truncation n` is a plain
function into the matrix data, not a homomorphism into `JetGaugeGroupI`: deleting the
coefficients above order `n` breaks unitarity and multiplicativity at the orders between
`n + 1` and `2n`.

The homomorphic notion of a jet *trivial to order `n`* is the truncation filtration of the
local-gauge-data package, `localGaugeData.truncationKer n`, defined in
`Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.Truncation` through the value and
the Maurer–Cartan form of the jet alone. This file compares the two notions: a jet trivial to
order `n` in that sense truncates to the identity, `truncation_eq_one_of_mem_truncationKer`.
The argument is the Euler vanishing principle by degree on power series,
`JetRing.coeff_eq_zero_of_pderiv_eq_mul`, applied to the radial relation
`∂_ρ U = −i ω_ρ(U) U` between a jet and its Maurer–Cartan form.

## ii. Key results

- `JetGaugeGroupI.truncation` : the `n`-th truncation of a jet.
- `JetGaugeGroupI.truncation_eq_one_of_mem_truncationKer` : jets trivial to order `n`
  truncate to the identity.

## iii. Table of contents

- A. The truncation
- B. The comparison with the Maurer–Cartan filtration

-/

@[expose] public section

open MvPowerSeries

namespace StandardModel

namespace JetGaugeGroupI

open JetGaugeAlgebra JetRing

/-!

## A. The truncation

-/

/-- The `n`-th truncation of a jet of a gauge transformation: componentwise, all Taylor
  coefficients of total degree greater than `n` are set to zero. -/
noncomputable def truncation (n : ℕ) (U : JetGaugeGroupI) :
    Matrix (Fin 3) (Fin 3) JetRing × Matrix (Fin 2) (Fin 2) JetRing × JetRing :=
  (U.1.1.map (JetRing.truncation n), U.2.1.1.map (JetRing.truncation n),
    JetRing.truncation n U.2.2.1)

/-- Truncation of the identity jet is the identity value triple. -/
@[simp]
lemma truncation_one (n : ℕ) : truncation n (1 : JetGaugeGroupI) = 1 :=
  Prod.ext (Matrix.map_one _ (JetRing.truncation_zero n) (JetRing.truncation_one n))
    (Prod.ext (Matrix.map_one _ (JetRing.truncation_zero n) (JetRing.truncation_one n))
      (JetRing.truncation_one n))

/-!

## B. The comparison with the Maurer–Cartan filtration

-/

/-- The base-point Taylor data of the Maurer–Cartan form of a jet trivial to order `n`,
  read as power-series coefficients of a scalar component `f` of the jet gauge algebra
  through a scalar `ψ` of the gauge algebra computing evaluated iterated derivatives: they
  vanish below degree `n`. -/
lemma coeff_maurerCartanForm_eq_zero_of_mem_truncationKer (ψ : GaugeAlgebra → ℂ)
    (hψ : ψ 0 = 0) (f : JetGaugeAlgebra → JetRing)
    (hf : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (a : JetGaugeAlgebra),
      ψ (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv s a)) =
        constantCoeff (s.foldl (fun h ρ => pderiv ℂ ρ h) (f a)))
    {U : JetGaugeGroupI} {n : ℕ} (hU : U ∈ localGaugeData.truncationKer n) (ρ : Fin 1 ⊕ Fin 3)
    {m : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hm : Finsupp.degree m < n) :
    coeff m (f (maurerCartanForm U ρ)) = 0 := by
  have h0 := hU.2 (Finsupp.toMultiset m) ρ (by
    rw [← degree_toFinsupp_eq_card, Finsupp.toMultiset_toFinsupp]; exact hm)
  have h1 := congrArg ψ h0
  simp only [localGaugeData_evalLie, localGaugeData_iteratedDeriv, localGaugeData_maurerCartan,
    hψ] at h1
  rw [hf, constantCoeff_foldl_pderiv, Finsupp.toMultiset_toFinsupp] at h1
  exact (mul_eq_zero.mp h1).resolve_left (Nat.cast_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun ν _ => Nat.factorial_ne_zero _))

/-- The `su(3)` entries of `coeff_maurerCartanForm_eq_zero_of_mem_truncationKer`. -/
lemma coeff_maurerCartanForm_toSU3Matrix_eq_zero_of_mem_truncationKer {U : JetGaugeGroupI}
    {n : ℕ} (hU : U ∈ localGaugeData.truncationKer n) (ρ : Fin 1 ⊕ Fin 3)
    {m : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hm : Finsupp.degree m < n) (i j : Fin 3) :
    coeff m ((maurerCartanForm U ρ).toSU3Matrix i j) = 0 :=
  coeff_maurerCartanForm_eq_zero_of_mem_truncationKer (fun a => a.toSU3Matrix i j) (by simp)
    (fun a => a.toSU3Matrix i j)
    (fun s a => by rw [eval_toSU3Matrix_apply, iteratedDeriv_toSU3Matrix, Matrix.map_apply])
    hU ρ hm

/-- The `su(2)` entries of `coeff_maurerCartanForm_eq_zero_of_mem_truncationKer`. -/
lemma coeff_maurerCartanForm_toSU2Matrix_eq_zero_of_mem_truncationKer {U : JetGaugeGroupI}
    {n : ℕ} (hU : U ∈ localGaugeData.truncationKer n) (ρ : Fin 1 ⊕ Fin 3)
    {m : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hm : Finsupp.degree m < n) (i j : Fin 2) :
    coeff m ((maurerCartanForm U ρ).toSU2Matrix i j) = 0 :=
  coeff_maurerCartanForm_eq_zero_of_mem_truncationKer (fun a => a.toSU2Matrix i j) (by simp)
    (fun a => a.toSU2Matrix i j)
    (fun s a => by rw [eval_toSU2Matrix_apply, iteratedDeriv_toSU2Matrix, Matrix.map_apply])
    hU ρ hm

/-- The `u(1)` value of `coeff_maurerCartanForm_eq_zero_of_mem_truncationKer`. -/
lemma coeff_maurerCartanForm_toU1Value_eq_zero_of_mem_truncationKer {U : JetGaugeGroupI}
    {n : ℕ} (hU : U ∈ localGaugeData.truncationKer n) (ρ : Fin 1 ⊕ Fin 3)
    {m : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hm : Finsupp.degree m < n) :
    coeff m (maurerCartanForm U ρ).toU1Value = 0 :=
  coeff_maurerCartanForm_eq_zero_of_mem_truncationKer (fun a => a.toU1Value) (by simp)
    (fun a => a.toU1Value) (fun s a => by rw [eval_toU1Value_eq, iteratedDeriv_toU1Value]) hU ρ hm

/-- Maurer–Cartan triangularity for the Standard Model: a jet trivial to order `n` in the
  sense of the Maurer–Cartan filtration truncates to the identity at order `n`. On each
  factor the radial relation `∂_ρ U = −i ω_ρ(U) U` and the Euler vanishing principle
  propagate the vanishing of the Maurer–Cartan coefficients below degree `n` to the
  vanishing of the coefficients of `U` in nonzero degree up to `n`. -/
theorem truncation_eq_one_of_mem_truncationKer {U : JetGaugeGroupI} {n : ℕ}
    (hU : U ∈ localGaugeData.truncationKer n) : truncation n U = 1 := by
  have hstar3 : star U.1.1 * U.1.1 = 1 := by
    have h1 := (Matrix.mem_specialUnitaryGroup_iff.mp U.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff'] at h1
  have hstar2 : star U.2.1.1 * U.2.1.1 = 1 := by
    have h1 := (Matrix.mem_specialUnitaryGroup_iff.mp U.2.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff'] at h1
  have hstar1 : star U.2.2.1 * U.2.2.1 = 1 := (Unitary.mem_iff.mp U.2.2.2).1
  -- the radial relation `∂_ρ U = (−i ω_ρ) U` on each factor
  have hd3 : ∀ ρ, U.1.1.map (pderiv ℂ ρ) =
      ((-Complex.I) • (maurerCartanForm U ρ).toSU3Matrix) * U.1.1 := fun ρ => by
    rw [maurerCartanForm_toSU3Matrix, smul_smul, neg_mul, Complex.I_mul_I, neg_neg,
      one_smul, mul_assoc, hstar3, mul_one]
  have hd2 : ∀ ρ, U.2.1.1.map (pderiv ℂ ρ) =
      ((-Complex.I) • (maurerCartanForm U ρ).toSU2Matrix) * U.2.1.1 := fun ρ => by
    rw [maurerCartanForm_toSU2Matrix, smul_smul, neg_mul, Complex.I_mul_I, neg_neg,
      one_smul, mul_assoc, hstar2, mul_one]
  have hd1 : ∀ ρ, pderiv ℂ ρ U.2.2.1 =
      ((-Complex.I) • (maurerCartanForm U ρ).toU1Value) * U.2.2.1 := fun ρ => by
    rw [maurerCartanForm_toU1Value, smul_smul, neg_mul, Complex.I_mul_I, neg_neg,
      one_smul, mul_assoc, hstar1, mul_one]
  have heval : U.eval = 1 := hU.1
  rw [← truncation_one n]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact matrix_map_truncation_eq_one (congrArg (fun p => (p.1 : Matrix (Fin 3) (Fin 3) ℂ)) heval)
      fun i j p hp hpn => coeff_entry_eq_zero_of_map_pderiv_eq_mul hd3
        (fun ρ q hq i j => by
          rw [Matrix.smul_apply, map_smul,
            coeff_maurerCartanForm_toSU3Matrix_eq_zero_of_mem_truncationKer hU ρ hq, smul_zero])
        i j hp hpn
  · exact matrix_map_truncation_eq_one
      (congrArg (fun p => (p.2.1 : Matrix (Fin 2) (Fin 2) ℂ)) heval)
      fun i j p hp hpn => coeff_entry_eq_zero_of_map_pderiv_eq_mul hd2
        (fun ρ q hq i j => by
          rw [Matrix.smul_apply, map_smul,
            coeff_maurerCartanForm_toSU2Matrix_eq_zero_of_mem_truncationKer hU ρ hq, smul_zero])
        i j hp hpn
  · exact truncation_eq_one_of_coeff (congrArg (fun p => (p.2.2 : ℂ)) heval)
      fun p hp hpn => coeff_eq_zero_of_pderiv_eq_mul hd1
        (fun ρ q hq => by
          rw [map_smul, coeff_maurerCartanForm_toU1Value_eq_zero_of_mem_truncationKer hU ρ hq,
            smul_zero])
        hp hpn

end JetGaugeGroupI

end StandardModel
