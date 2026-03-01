/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.StandardModel.AnomalyCancellation.NoGrav.One.LinearParameterization
/-!
# Lemmas for 1 family SM Accs

The main result of this file is the conclusion of this paper:
  [Lohitsiri and Tong][Lohitsiri:2019fuu]

That every solution to the ACCs without gravity satisfies for free the gravitational anomaly.
-/

namespace SM
namespace SMNoGrav
namespace One

open SMCharges
open SMACCs
open BigOperators

/-- For a set of 1 family SM charges satisfying all ACCs except the gravitational,
  the charge of `Q` is zero if and only if `E` is zero. -/
lemma E_zero_iff_Q_zero {S : (SMNoGrav 1).Sols} : Q S.val (0 : Fin 1) = 0 ↔
    E S.val (0 : Fin 1) = 0 := by
  let S' := linearParameters.bijection.symm S.1.1
  have hC := cubeSol S
  have hS' := congrArg (fun S => S.val) (linearParameters.bijection.right_inv S.1.1)
  change S'.asCharges = S.val at hS'
  rw [← hS'] at hC
  exact Iff.intro (fun hQ => S'.cubic_zero_Q'_zero hC hQ) (fun hE => S'.cubic_zero_E'_zero hC hE)

/-- For a set of 1-family SM charges satisfying all ACCs except the gravitational,
  if the `Q` charge is zero then the charges satisfy the gravitational ACCs. -/
lemma accGrav_Q_zero {S : (SMNoGrav 1).Sols} (hQ : Q S.val (0 : Fin 1) = 0) :
    accGrav S.val = 0 := by
  rw [accGrav]
  simp only [SMSpecies_numberCharges, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, LinearMap.coe_mk, AddHom.coe_mk]
  erw [hQ, E_zero_iff_Q_zero.mp hQ]
  have h1 := SU2Sol S.1.1
  have h2 := SU3Sol S.1.1
  simp only [accSU2, SMSpecies_numberCharges, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton, LinearMap.coe_mk, AddHom.coe_mk, accSU3] at h1 h2
  erw [hQ] at h1 h2
  simp_all
  linear_combination 3 * h2

/-- For a set of 1-family SM charges satisfying all ACCs except the gravitational,
  if the `Q` charge is not zero then the charges satisfy the gravitational ACCs. -/
lemma accGrav_Q_ne_zero {S : (SMNoGrav 1).Sols} (hQ : Q S.val (0 : Fin 1) ≠ 0) :
    accGrav S.val = 0 := by
  have hE := E_zero_iff_Q_zero.mpr.mt hQ
  let S' := linearParametersQENeqZero.bijection.symm ⟨S.1.1, And.intro hQ hE⟩
  have hC := cubeSol S
  have hS' := congrArg (fun S => S.val.val)
    (linearParametersQENeqZero.bijection.right_inv ⟨S.1.1, And.intro hQ hE⟩)
  change _ = S.val at hS'
  rw [← hS'] at hC ⊢
  exact S'.grav_of_cubic hC

/-- Any solution to the 1-family ACCs without gravity satisfies the gravitational ACC. -/
theorem accGravSatisfied {S : (SMNoGrav 1).Sols} :
    accGrav S.val = 0 := by
  by_cases hQ : Q S.val (0 : Fin 1)= 0
  · exact accGrav_Q_zero hQ
  · exact accGrav_Q_ne_zero hQ

end One
end SMNoGrav
end SM
