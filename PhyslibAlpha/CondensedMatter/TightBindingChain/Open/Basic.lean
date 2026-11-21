/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Hasse
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
- `inner_openHamiltonian_eq_adjMatrix` : its matrix elements are `E0` times the identity minus `t`
  times the adjacency matrix of the path graph.
- `adjMatrix_pathGraph_mulVec_sin` : `sin ((m + 1) k π / (N + 1))` is an eigenvector of the
  adjacency matrix of the path graph, with eigenvalue `2 cos (k π / (N + 1))`.
- `openHamiltonian_sum_sin` : the standing waves are eigenvectors of the open chain, with energies
  `E0 - 2 t cos (k π / (N + 1))`.
- `inner_commutator_position` : `⟨m|(A X - X A)|n⟩ = a (n - m) ⟨m|A|n⟩`.

## iii. Table of contents

- A. The position operator
- B. The Hamiltonian with open boundary conditions
  - B.1. Hermiticity
  - B.2. Matrix elements
  - B.3. Eigenvectors
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

/-- The open chain is the hopping Hamiltonian of the path graph: the matrix element between
two sites is `E0` times the identity minus `t` times the adjacency matrix of `pathGraph N`. -/
lemma inner_openHamiltonian_eq_adjMatrix (m n : Fin T.N) :
    ⟪|m⟩, T.openHamiltonian |n⟩⟫_ℂ =
      (T.E0 : ℂ) * (1 : Matrix (Fin T.N) (Fin T.N) ℂ) m n -
        (T.t : ℂ) * (SimpleGraph.pathGraph T.N).adjMatrix ℂ m n := by
  rw [inner_openHamiltonian]
  by_cases h : m = n
  · subst h
    simp
  · simp [h, Matrix.one_apply_ne h, SimpleGraph.adjMatrix_apply, SimpleGraph.pathGraph_adj]
    split_ifs <;> simp_all

/-!

### B.3. Eigenvectors

-/

/-- For every `k`, `m ↦ sin ((m + 1) k π / (N + 1))` is an eigenvector of the adjacency matrix of
the path graph on `N` vertices, with eigenvalue `2 cos (k π / (N + 1))`. -/
lemma adjMatrix_pathGraph_mulVec_sin (N k : ℕ) :
    Matrix.mulVec ((SimpleGraph.pathGraph N).adjMatrix ℝ)
        (fun m : Fin N => Real.sin ((m + 1) * (k * Real.pi / (N + 1)))) =
      (2 * Real.cos (k * Real.pi / (N + 1))) •
        fun m : Fin N => Real.sin ((m + 1) * (k * Real.pi / (N + 1))) := by
  set θ := k * Real.pi / (N + 1)
  have hN : Real.sin ((N + 1) * θ) = 0 := by
    rw [mul_div_cancel₀ _ (by positivity)]
    exact Real.sin_nat_mul_pi k
  funext m
  have hm := m.isLt
  simp only [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply, SimpleGraph.pathGraph_adj,
    ite_mul, one_mul, zero_mul, Pi.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun j => if (m : ℕ) + 1 = j ∨ j + 1 = m then
    Real.sin ((j + 1) * θ) else 0)]
  rw [Finset.sum_eq_add ((m : ℕ) - 1) ((m : ℕ) + 1) (by omega)]
  · rw [ite_eq_left (Or.inl rfl)]
    generalize (m : ℕ) = i
    cases i with
    | zero =>
      simp only [zero_add, Nat.zero_sub, one_ne_zero, or_self, ite_false, CharP.cast_eq_zero]
      rw [show ((1 : ℕ) + 1 : ℝ) * θ = 2 * θ by push_cast; ring, Real.sin_two_mul, one_mul]
      ring
    | succ n =>
      rw [ite_eq_left (Or.inr (by omega))]
      push_cast
      rw [show (n + 1 : ℝ) * θ = (n + 1 + 1) * θ - θ by ring,
        show (n + 1 + 1 + 1 : ℝ) * θ = (n + 1 + 1) * θ + θ by ring, Real.sin_sub, Real.sin_add]
      ring
  · intro j _ hj
    simp only [ite_eq_right_iff]
    omega
  · intro h
    simp at h
    omega
  · intro h
    simp only [Finset.mem_range, not_lt] at h
    rw [ite_eq_left (Or.inl rfl), ← hN]
    congr 2
    norm_cast
    omega

/-- The open chain has the standing waves `∑ m, sin ((m + 1) k π / (N + 1)) |m⟩` as eigenvectors,
with energies `E0 - 2 t cos (k π / (N + 1))`. -/
lemma openHamiltonian_sum_sin (k : ℕ) :
    T.openHamiltonian (∑ m : Fin T.N, (Real.sin ((m + 1) * (k * Real.pi / (T.N + 1))) : ℂ) • |m⟩) =
      ((T.E0 - 2 * T.t * Real.cos (k * Real.pi / (T.N + 1)) : ℝ) : ℂ) •
        ∑ m : Fin T.N, (Real.sin ((m + 1) * (k * Real.pi / (T.N + 1))) : ℂ) • |m⟩ := by
  refine ext_inner_left_basis localizedState.toBasis fun n => ?_
  have h := congrFun (adjMatrix_pathGraph_mulVec_sin T.N k) n
  simp only [OrthonormalBasis.coe_toBasis, map_sum, map_smul, inner_sum, inner_smul_right,
    inner_openHamiltonian_eq_adjMatrix, localizedState_orthonormal_eq_ite] at h ⊢
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  have hA (x : Fin T.N) : (SimpleGraph.pathGraph T.N).adjMatrix ℂ n x =
      (((SimpleGraph.pathGraph T.N).adjMatrix ℝ n x : ℝ) : ℂ) := by
    by_cases hx : (SimpleGraph.pathGraph T.N).Adj n x <;> simp [hx]
  simp only [hA, mul_sub, Finset.sum_sub_distrib, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have h' := congrArg (fun r : ℝ => ((T.t * r : ℝ) : ℂ)) h
  simp only [Finset.mul_sum] at h'
  push_cast at h' ⊢
  simp only [mul_comm, mul_left_comm] at h' ⊢
  linear_combination -h'

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
