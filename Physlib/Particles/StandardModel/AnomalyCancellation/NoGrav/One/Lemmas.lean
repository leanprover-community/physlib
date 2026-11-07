/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.AnomalyCancellation.NoGrav.One.LinearParameterization
/-!
# Lemmas for 1 family SM Accs

The main result of this file is the conclusion of this paper:
  [Lohitsiri and Tong][Lohitsiri:2019fuu] [ref: Lohitsiri:2019fuu]

That every solution to the ACCs without gravity satisfies for free the gravitational anomaly.

## References

* The main result of this file is the conclusion of this paper. [ref: Lohitsiri:2019fuu]
-/

@[expose] public section

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
  exact ⟨S'.cubic_zero_Q'_zero hC, S'.cubic_zero_E'_zero hC⟩

/-- For a set of 1-family SM charges satisfying all ACCs except the gravitational,
  if the `Q` charge is zero then the charges satisfy the gravitational ACCs. -/
lemma accGrav_Q_zero {S : (SMNoGrav 1).Sols} (hQ : Q S.val (0 : Fin 1) = 0) :
    accGrav S.val = 0 := by
  rw [accGrav]
  have hE := E_zero_iff_Q_zero.mp hQ
  simp_all only [toSpecies_apply_eq, Fin.isValue, sum_SMSpecies_numberCharges_one, LinearMap.coe_mk,
    AddHom.coe_mk]
  have h1 := SU2Sol S.1.1
  have h2 := SU3Sol S.1.1
  simp only [accSU2, toSpecies_apply_eq, Fin.isValue, sum_SMSpecies_numberCharges_one,
    LinearMap.coe_mk, AddHom.coe_mk, accSU3] at h1 h2
  linear_combination (norm := ring1!) 2 * h1 + 3 * h2 - 6 * hQ + hE

/-- For a set of 1-family SM charges satisfying all ACCs except the gravitational,
  if the `Q` charge is not zero then the charges satisfy the gravitational ACCs. -/
lemma accGrav_Q_ne_zero {S : (SMNoGrav 1).Sols} (hQ : Q S.val (0 : Fin 1) ≠ 0) :
    accGrav S.val = 0 := by
  have hE := E_zero_iff_Q_zero.mpr.mt hQ
  let S' := linearParametersQENeqZero.bijection.symm ⟨S.1.1, hQ, hE⟩
  have hC := cubeSol S
  have hS' := congrArg (fun S => S.val.val)
    (linearParametersQENeqZero.bijection.right_inv ⟨S.1.1, hQ, hE⟩)
  change _ = S.val at hS'
  rw [← hS'] at hC ⊢
  exact S'.grav_of_cubic hC

/-- Any solution to the 1-family ACCs without gravity satisfies the gravitational ACC. -/
theorem accGravSatisfied {S : (SMNoGrav 1).Sols} :
    accGrav S.val = 0 :=
  (em _).elim accGrav_Q_zero accGrav_Q_ne_zero

end One
end SMNoGrav
end SM
