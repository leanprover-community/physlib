/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Physlib.CondensedMatter.TightBindingChain.Basic
/-!

# The tight binding chain with open boundary conditions

The position operator and the Hamiltonian of the tight binding chain with open boundaries.

## i. Overview

A finite piece of a 1d solid has two ends: the electron cannot hop from the last site back to
the first. This is the tight binding chain with open boundary conditions. It also carries a
position operator, which the periodic chain lacks, since there the site `N` is identified
with the site `0`.

## ii. Key results

- `position` : the position operator `X = ∑ n, a n |n⟩⟨n|`.
- `openHamiltonian` : the Hamiltonian with open boundary conditions.
- `inner_openHamiltonian` : the open chain only hops between neighbouring sites.
- `inner_commutator_position` : `⟨m|(A X - X A)|n⟩ = a (n - m) ⟨m|A|n⟩`.

## iii. Table of contents

- A. The position operator
- B. The Hamiltonian with open boundary conditions
  - B.1. Hermiticity
  - B.2. Matrix elements
- C. Commutators with the position operator

## iv. References

* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]
-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open InnerProductSpace
variable (T : TightBindingChain)

/-!

## A. The position operator

-/

/-- The position operator `X = ∑ n, a n |n⟩⟨n|`, measuring from the site `0`. -/
noncomputable def position : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace :=
  ∑ n : Fin T.N, ((T.a * (n : ℕ) : ℝ) : ℂ) • |n⟩⟨n|

/-- The localized states are the eigenstates of the position operator. -/
lemma position_apply_localizedState (n : Fin T.N) :
    T.position |n⟩ = ((T.a * (n : ℕ) : ℝ) : ℂ) • |n⟩ := by
  simp [position, localizedComp_apply_localizedState]

/-- The position operator is hermitian. -/
lemma position_hermitian (ψ φ : T.HilbertSpace) :
    ⟪T.position ψ, φ⟫_ℂ = ⟪ψ, T.position φ⟫_ℂ := by
  simp only [position, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right, localizedComp_adjoint, Complex.conj_ofReal]

/-!

## B. The Hamiltonian with open boundary conditions

-/

/-- The Hamiltonian of the tight binding chain with open boundary conditions: the periodic
`hamiltonian` with one hopping between the end sites `0` and `N - 1` removed. For `N = 2` the
periodic chain counts the single bond twice, and one copy remains. -/
noncomputable def openHamiltonian : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace :=
  T.hamiltonian + (T.t : ℂ) • (|0⟩⟨-1| + |-1⟩⟨0|)

/-!

### B.1. Hermiticity

-/

/-- The Hamiltonian with open boundary conditions is hermitian. -/
lemma openHamiltonian_hermitian (ψ φ : T.HilbertSpace) :
    ⟪T.openHamiltonian ψ, φ⟫_ℂ = ⟪ψ, T.openHamiltonian φ⟫_ℂ := by
  simp only [openHamiltonian, LinearMap.add_apply, LinearMap.smul_apply, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, hamiltonian_hermitian,
    localizedComp_adjoint, Complex.conj_ofReal]
  ring

/-!

### B.2. Matrix elements

-/

/-- In `Fin N`, `m = n + 1` either as a step inside the chain or as the wrap from the last site
back to `0`. -/
private lemma eq_add_one_iff_val {N : ℕ} [NeZero N] (m n : Fin N) :
    m = n + 1 ↔ (m : ℕ) = n + 1 ∨ ((n : ℕ) + 1 = N ∧ (m : ℕ) = 0) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  rw [Fin.ext_iff, Fin.val_add_one]
  split_ifs with h <;> simp only [Fin.ext_iff, Fin.val_last] at h <;> omega

/-- The open chain hops only between neighbouring sites, with amplitude `-t`. -/
lemma inner_openHamiltonian (m n : Fin T.N) :
    ⟪|m⟩, T.openHamiltonian |n⟩⟫_ℂ =
      if m = n then (T.E0 : ℂ)
      else if (m : ℕ) + 1 = n ∨ (n : ℕ) + 1 = m then -(T.t : ℂ) else 0 := by
  simp only [openHamiltonian, LinearMap.add_apply, LinearMap.smul_apply,
    hamiltonian_apply_localizedState, localizedComp_apply_localizedState, inner_add_right,
    inner_sub_right, inner_smul_right, localizedState_orthonormal_eq_ite]
  rw [apply_ite (inner ℂ _), apply_ite (inner ℂ _)]
  simp only [inner_zero_right, localizedState_orthonormal_eq_ite]
  have h (k l : Fin T.N) : k = l - 1 ↔ l = k + 1 := by rw [eq_sub_iff_add_eq, eq_comm]
  have hl (k : Fin T.N) : -1 = k ↔ (k : ℕ) + 1 = T.N := by
    rw [neg_eq_iff_add_eq_zero, add_comm, eq_comm, eq_add_one_iff_val]
    simp
  simp only [h m n, hl n, eq_comm (a := m) (b := -1), hl m, eq_add_one_iff_val m n,
    eq_add_one_iff_val n m]
  simp only [Fin.ext_iff, Fin.val_zero]
  split_ifs <;> first | omega | ring

/-!

## C. Commutators with the position operator

-/

/-- Commuting with the position operator weighs each matrix element by the hopping distance:
`⟨m|(A X - X A)|n⟩ = a (n - m) ⟨m|A|n⟩`. -/
lemma inner_commutator_position (A : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace) (m n : Fin T.N) :
    ⟪|m⟩, (A ∘ₗ T.position - T.position ∘ₗ A) |n⟩⟫_ℂ =
      ((T.a * ((n : ℕ) - (m : ℕ)) : ℝ) : ℂ) * ⟪|m⟩, A |n⟩⟫_ℂ := by
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, inner_sub_right,
    ← position_hermitian, position_apply_localizedState, position_apply_localizedState,
    map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  push_cast
  ring

end TightBindingChain
end CondensedMatter
