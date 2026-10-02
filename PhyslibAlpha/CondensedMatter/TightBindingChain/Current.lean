/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.OpenBoundary
/-!

# The current operator of the open tight binding chain

## i. Overview

By the Heisenberg equation the velocity of the electron is `dX/dt = i [H, X]` (with `ħ = 1`).
On the open tight binding chain this current operator `J = i (H X - X H)` only moves the
electron to a neighbouring site, with amplitude `∓ i a t`. Stationary states and localized
states carry no current.

## ii. Key results

- `current` : the current operator `J = i (H X - X H)`.
- `inner_current_eq` : `J` moves the electron exactly one site, with amplitude `∓ i a t`.
- `inner_current_self_of_eigen` : stationary states carry no current.
- `inner_current_localizedState` : localized states carry no current.

## iii. Table of contents

- A. The current operator
- B. Matrix elements
- C. States without current

## iv. References

* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]
-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open InnerProductSpace
variable (T : TightBindingChain)

/-!

## A. The current operator

-/

/-- The current operator `J = i (H X - X H)` of the open chain, the velocity `dX/dt`. -/
noncomputable def current : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace :=
  Complex.I • (T.openHamiltonian ∘ₗ T.position - T.position ∘ₗ T.openHamiltonian)

/-- The current operator is hermitian. -/
lemma current_hermitian (ψ φ : T.HilbertSpace) :
    ⟪T.current ψ, φ⟫_ℂ = ⟪ψ, T.current φ⟫_ℂ := by
  simp only [current, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
    openHamiltonian_hermitian, position_hermitian, Complex.conj_I]
  ring

/-!

## B. Matrix elements

-/

/-- The matrix elements of `J` are those of `H`, weighted by `i` times the hopping distance. -/
lemma inner_current (m n : Fin T.N) :
    ⟪|m⟩, T.current |n⟩⟫_ℂ =
      Complex.I * ((T.a * ((n : ℕ) - (m : ℕ)) : ℝ) : ℂ) * ⟪|m⟩, T.openHamiltonian |n⟩⟫_ℂ := by
  rw [current, LinearMap.smul_apply, inner_smul_right, inner_commutator_position, mul_assoc]

/-- The current moves the electron exactly one site, a distance `a`, with amplitude `∓ i a t`;
every other matrix element vanishes. -/
lemma inner_current_eq (m n : Fin T.N) :
    ⟪|m⟩, T.current |n⟩⟫_ℂ =
      if (m : ℕ) + 1 = n then -(Complex.I * (T.a * T.t : ℝ))
      else if (n : ℕ) + 1 = m then Complex.I * (T.a * T.t : ℝ) else 0 := by
  rw [inner_current, inner_openHamiltonian]
  by_cases hA : (m : ℕ) + 1 = n
  · have hn : ((n : ℕ) : ℂ) = (m : ℕ) + 1 := by exact_mod_cast hA.symm
    simp only [hA, Fin.ext_iff, true_or, ite_true, show (m : ℕ) ≠ n by omega, ite_false]
    push_cast [hn]
    ring
  by_cases hB : (n : ℕ) + 1 = m
  · have hm : ((m : ℕ) : ℂ) = (n : ℕ) + 1 := by exact_mod_cast hB.symm
    simp only [hA, hB, Fin.ext_iff, or_true, ite_true, show (m : ℕ) ≠ n by omega, ite_false]
    push_cast [hm]
    ring
  split_ifs with h <;> simp_all

/-!

## C. States without current

-/

/-- Stationary states carry no current: `⟨ψ|J|ψ⟩ = 0` whenever `H ψ = E ψ`. -/
lemma inner_current_self_of_eigen {ψ : T.HilbertSpace} {E : ℝ}
    (h : T.openHamiltonian ψ = (E : ℂ) • ψ) : ⟪ψ, T.current ψ⟫_ℂ = 0 := by
  rw [current, LinearMap.smul_apply, inner_smul_right, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, inner_sub_right, ← openHamiltonian_hermitian, h,
    map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal, sub_self, mul_zero]

/-- A localized electron carries no current: `⟨n|J|n⟩ = 0`. -/
lemma inner_current_localizedState (n : Fin T.N) : ⟪|n⟩, T.current |n⟩⟫_ℂ = 0 := by
  rw [inner_current, sub_self, mul_zero, Complex.ofReal_zero, mul_zero, zero_mul]

end TightBindingChain
end CondensedMatter
