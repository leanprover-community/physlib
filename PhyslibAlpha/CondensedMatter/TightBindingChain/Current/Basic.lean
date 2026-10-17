/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.Open.Basic
/-!

# The current operator of the open tight binding chain

The current operator `J = i (H X - X H)` of the open tight binding chain and its matrix elements.

## i. Overview

By the Heisenberg equation the velocity of the electron is `dX/dt = i [H, X]` (with `ħ = 1`).
On the open tight binding chain this current operator `J = i (H X - X H)` only moves the
electron to a neighbouring site, with amplitude `∓ i a t`. Stationary states and localized
states carry no current.

The current only sees the hopping part `K = H - E₀` of the Hamiltonian, its kinetic energy. With
position it closes on `K`: `J X - X J = i a² K`. With the Hamiltonian it gives the rate of change
of the current, and `H J - J H` is diagonal and vanishes inside the chain: the current changes only
at the two ends, `-2 i a t²` on the first site and `2 i a t²` on the last. Finally `K` and `J` share
no eigenvector: `K ψ = μ ψ` is a recurrence fixed by `ψ` on the first site, and `J ψ = 0` forces
`X ψ` to solve the same recurrence and vanish there.

## ii. Key results

- `current` : the current operator `J = i (H X - X H)`.
- `inner_current_eq` : `J` moves the electron exactly one site, with amplitude `∓ i a t`.
- `inner_current_self_of_eigen` : stationary states carry no current.
- `inner_current_localizedState` : localized states carry no current.
- `hopping` : the hopping part `K = H - E₀` of the Hamiltonian.
- `current_comp_position_sub` : `J X - X J = i a² K`.
- `inner_openHamiltonian_comp_current_sub` : `H J - J H` lives on the two ends of the chain.
- `eq_zero_of_hopping_eq_smul` : a solution of `K ψ = μ ψ` vanishing on the first site vanishes.
- `eq_zero_of_hopping_eq_smul_of_current_eq_zero` : `K` and `J` share no eigenvector.

## iii. Table of contents

- A. The current operator
- B. Matrix elements
- C. States without current
- D. The hopping part of the Hamiltonian
- E. Commutators of the current
- F. The hopping and the current share no eigenvector

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

/-!

## D. The hopping part of the Hamiltonian

-/

/-- The hopping part `K = H - E₀` of the open Hamiltonian: its kinetic energy. -/
noncomputable def hopping : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace :=
  T.openHamiltonian - (T.E0 : ℂ) • LinearMap.id

/-- `K` hops between neighbouring sites only, with amplitude `-t`, and has no diagonal. -/
lemma inner_hopping (m n : Fin T.N) :
    ⟪|m⟩, T.hopping |n⟩⟫_ℂ = if (m : ℕ) + 1 = n ∨ (n : ℕ) + 1 = m then -(T.t : ℂ) else 0 := by
  rw [hopping, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, inner_sub_right,
    inner_smul_right, inner_openHamiltonian, localizedState_orthonormal_eq_ite]
  by_cases h : m = n
  · subst h
    simp
  · simp [h]

/-- An operator in components: `⟨m|A ψ⟩ = ∑ n, ⟨m|A|n⟩ ⟨n|ψ⟩`. -/
lemma inner_apply_eq_sum (A : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace) (m : Fin T.N)
    (ψ : T.HilbertSpace) : ⟪|m⟩, A ψ⟫_ℂ = ∑ n, ⟪|m⟩, A |n⟩⟫_ℂ * ⟪|n⟩, ψ⟫_ℂ := by
  conv_lhs => rw [← T.localizedState.sum_repr' ψ]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right, mul_comm]

/-- Two vectors with the same components on every site are equal. -/
lemma ext_localizedState {ψ φ : T.HilbertSpace} (h : ∀ m, ⟪|m⟩, ψ⟫_ℂ = ⟪|m⟩, φ⟫_ℂ) : ψ = φ := by
  rw [← T.localizedState.sum_repr' ψ, ← T.localizedState.sum_repr' φ]
  simp only [h]

/-- The current only sees the hopping: `J = i (K X - X K)`. -/
lemma current_eq_hopping :
    T.current = Complex.I • (T.hopping ∘ₗ T.position - T.position ∘ₗ T.hopping) := by
  rw [current, hopping, LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.smul_comp,
    LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id]
  congr 1
  abel

/-- The matrix elements of `J` are those of `K`, weighted by `i` times the hopping distance. -/
lemma inner_current_hopping (m n : Fin T.N) :
    ⟪|m⟩, T.current |n⟩⟫_ℂ =
      Complex.I * ((T.a * ((n : ℕ) - (m : ℕ)) : ℝ) : ℂ) * ⟪|m⟩, T.hopping |n⟩⟫_ℂ := by
  rw [current_eq_hopping, LinearMap.smul_apply, inner_smul_right, inner_commutator_position,
    mul_assoc]

/-!

## E. Commutators of the current

-/

/-- **Position and current close on the kinetic energy.** `J X - X J = i a² K`. -/
lemma current_comp_position_sub :
    T.current ∘ₗ T.position - T.position ∘ₗ T.current =
      (Complex.I * (T.a : ℂ) ^ 2) • T.hopping := by
  refine T.localizedState.toBasis.ext fun n => T.ext_localizedState fun m => ?_
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.smul_apply, inner_smul_right]
  rw [inner_commutator_position, inner_current_hopping, inner_hopping]
  split_ifs with h
  · have hd : (((n : ℕ) : ℝ) - (m : ℕ)) ^ 2 = 1 := by
      rcases h with h | h
      · rw [← h]; push_cast; ring
      · rw [← h]; push_cast; ring
    have hd' : ((((n : ℕ) : ℝ) - (m : ℕ)) : ℂ) ^ 2 = 1 := by exact_mod_cast hd
    push_cast
    linear_combination (-(Complex.I * T.a ^ 2 * T.t)) * hd'
  · simp

/-- On the hopping, `⟨m|(K J - J K)|n⟩ = i a ∑ k, ⟨m|K|k⟩ ⟨k|K|n⟩ (n + m - 2 k)`. -/
lemma inner_hopping_comp_current_sub (m n : Fin T.N) :
    ⟪|m⟩, (T.hopping ∘ₗ T.current - T.current ∘ₗ T.hopping) |n⟩⟫_ℂ =
      ∑ k, Complex.I * T.a * ⟪|m⟩, T.hopping |k⟩⟫_ℂ * ⟪|k⟩, T.hopping |n⟩⟫_ℂ *
        (((n : ℕ) + (m : ℕ) - 2 * (k : ℕ) : ℝ) : ℂ) := by
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, inner_sub_right,
    T.inner_apply_eq_sum _ m, T.inner_apply_eq_sum T.current m, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_current_hopping, inner_current_hopping]
  push_cast
  ring

/-- Counting the left neighbour: `∑ k, [k + 1 = m] = [1 ≤ m]`. -/
private lemma sum_ite_succ_eq (m : Fin T.N) :
    ∑ k : Fin T.N, (if (k : ℕ) + 1 = m then (1 : ℂ) else 0) = if 1 ≤ (m : ℕ) then 1 else 0 := by
  split_ifs with hm
  · rw [Finset.sum_eq_single ⟨(m : ℕ) - 1, by omega⟩]
    · rw [ite_eq_left (by simp; omega)]
    · intro k _ hk
      exact ite_eq_right fun h => hk (Fin.ext (by simp; omega))
    · simp
  · exact Finset.sum_eq_zero fun k _ => ite_eq_right (by omega)

/-- Counting the right neighbour: `∑ k, [m + 1 = k] = [m + 1 < N]`. -/
private lemma sum_ite_eq_succ (m : Fin T.N) :
    ∑ k : Fin T.N, (if (m : ℕ) + 1 = k then (1 : ℂ) else 0) =
      if (m : ℕ) + 1 < T.N then 1 else 0 := by
  split_ifs with hm
  · rw [Finset.sum_eq_single ⟨(m : ℕ) + 1, hm⟩]
    · rw [ite_eq_left rfl]
    · intro k _ hk
      exact ite_eq_right fun h => hk (Fin.ext (by simp; omega))
    · simp
  · exact Finset.sum_eq_zero fun k _ => ite_eq_right (by omega)

/-- On the diagonal, a term of `inner_hopping_comp_current_sub` counts the neighbours of `m`. -/
private lemma hopping_term_self (m k : Fin T.N) :
    Complex.I * T.a * ⟪|m⟩, T.hopping |k⟩⟫_ℂ * ⟪|k⟩, T.hopping |m⟩⟫_ℂ *
        (((m : ℕ) + (m : ℕ) - 2 * (k : ℕ) : ℝ) : ℂ) =
      2 * Complex.I * T.a * T.t ^ 2 *
        ((if (k : ℕ) + 1 = m then 1 else 0) - (if (m : ℕ) + 1 = k then 1 else 0)) := by
  rw [inner_hopping, inner_hopping]
  by_cases h1 : (k : ℕ) + 1 = m
  · have h2 : ¬ (m : ℕ) + 1 = k := by omega
    have hm : ((m : ℕ) : ℝ) = k + 1 := by exact_mod_cast h1.symm
    simp only [h1, h2, or_true, true_or, ite_true, ite_false]
    push_cast [hm]
    ring
  · by_cases h2 : (m : ℕ) + 1 = k
    · have hk : ((k : ℕ) : ℝ) = m + 1 := by exact_mod_cast h2.symm
      simp only [h1, h2, or_false, false_or, ite_true, ite_false]
      push_cast [hk]
      ring
    · simp [h1, h2]

/-- Off the diagonal every term of `inner_hopping_comp_current_sub` vanishes: two hops from `m`
to `n ≠ m` pass through the midpoint. -/
private lemma hopping_term_ne {m n : Fin T.N} (h : m ≠ n) (k : Fin T.N) :
    Complex.I * T.a * ⟪|m⟩, T.hopping |k⟩⟫_ℂ * ⟪|k⟩, T.hopping |n⟩⟫_ℂ *
      (((n : ℕ) + (m : ℕ) - 2 * (k : ℕ) : ℝ) : ℂ) = 0 := by
  have hmn : (m : ℕ) ≠ n := fun e => h (Fin.ext e)
  rw [inner_hopping, inner_hopping]
  split_ifs with h1 h2
  · have hk : ((n : ℕ) : ℝ) + (m : ℕ) - 2 * (k : ℕ) = 0 := by
      have : (n : ℕ) + (m : ℕ) = 2 * k := by omega
      exact_mod_cast (by omega : ((n : ℕ) + (m : ℕ) : ℤ) - 2 * (k : ℕ) = 0)
    rw [hk, Complex.ofReal_zero, mul_zero]
  all_goals simp

/-- The current commutes with `H` as with its hopping part: `H J - J H = K J - J K`. -/
lemma openHamiltonian_comp_current_sub :
    T.openHamiltonian ∘ₗ T.current - T.current ∘ₗ T.openHamiltonian =
      T.hopping ∘ₗ T.current - T.current ∘ₗ T.hopping := by
  rw [hopping, LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.id_comp, LinearMap.comp_id]
  abel

/-- **The current changes only at the two ends of the chain.** `H J - J H` is diagonal, with
entry `-2 i a t²` on the first site, `2 i a t²` on the last, and `0` inside the chain. -/
lemma inner_openHamiltonian_comp_current_sub (m n : Fin T.N) :
    ⟪|m⟩, (T.openHamiltonian ∘ₗ T.current - T.current ∘ₗ T.openHamiltonian) |n⟩⟫_ℂ =
      if m = n then 2 * Complex.I * T.a * T.t ^ 2 *
        ((if 1 ≤ (m : ℕ) then 1 else 0) - (if (m : ℕ) + 1 < T.N then 1 else 0)) else 0 := by
  rw [openHamiltonian_comp_current_sub, inner_hopping_comp_current_sub]
  by_cases h : m = n
  · subst h
    rw [ite_eq_left rfl]
    simp only [hopping_term_self, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_ite_succ_eq,
      sum_ite_eq_succ]
  · rw [ite_eq_right h]
    exact Finset.sum_eq_zero fun k _ => T.hopping_term_ne h k

/-!

## F. The hopping and the current share no eigenvector

-/

/-- **The recurrence of the hopping.** A solution of `K ψ = μ ψ` vanishing on the first site
vanishes: the row `n` fixes `ψ (n + 1)` from `ψ n` and `ψ (n - 1)`. -/
lemma eq_zero_of_hopping_eq_smul (ht : T.t ≠ 0) (hN : 0 < T.N) {μ : ℂ} {ψ : T.HilbertSpace}
    (h : T.hopping ψ = μ • ψ) (h0 : ⟪|(⟨0, hN⟩ : Fin T.N)⟩, ψ⟫_ℂ = 0) : ψ = 0 := by
  have htc : -(T.t : ℂ) ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr ht)
  have key : ∀ j (hj : j < T.N), ⟪|(⟨j, hj⟩ : Fin T.N)⟩, ψ⟫_ℂ = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      rcases j with _ | i
      · exact h0
      · have hrow := congrArg (fun φ => ⟪|(⟨i, by omega⟩ : Fin T.N)⟩, φ⟫_ℂ) h
        simp only [inner_smul_right, ih i (by omega), mul_zero] at hrow
        rw [inner_apply_eq_sum, Finset.sum_eq_single ⟨i + 1, hj⟩] at hrow
        · rw [inner_hopping, ite_eq_left (Or.inl rfl)] at hrow
          exact (mul_eq_zero.mp hrow).resolve_left htc
        · intro k _ hk
          have hk' : (k : ℕ) ≠ i + 1 := fun e => hk (Fin.ext e)
          rw [inner_hopping]
          split_ifs with hadj
          · have hki : (k : ℕ) < i + 1 := by simp only at hadj; omega
            have := ih k hki k.2
            simp only [Fin.eta] at this
            rw [this, mul_zero]
          · rw [zero_mul]
        · simp
  exact T.ext_localizedState fun m => by rw [inner_zero_right]; exact key m m.2

/-- **The hopping and the current share no eigenvector.** For `t ≠ 0` and `N ≥ 2`, `K ψ = μ ψ`
and `J ψ = 0` force `ψ = 0`: `X ψ` solves the same recurrence and vanishes on the first site, so
`ψ` lives on the first site, from which `K` moves it. -/
lemma eq_zero_of_hopping_eq_smul_of_current_eq_zero (ht : T.t ≠ 0) (hN : 2 ≤ T.N) {μ : ℂ}
    {ψ : T.HilbertSpace} (hK : T.hopping ψ = μ • ψ) (hJ : T.current ψ = 0) : ψ = 0 := by
  have hX : T.position ψ = 0 := by
    refine T.eq_zero_of_hopping_eq_smul ht (by omega) (μ := μ) ?_ ?_
    · rw [current_eq_hopping, LinearMap.smul_apply, smul_eq_zero, LinearMap.sub_apply,
        LinearMap.comp_apply, LinearMap.comp_apply, sub_eq_zero] at hJ
      rw [hJ.resolve_left Complex.I_ne_zero, hK, map_smul]
    · rw [← position_hermitian, position_apply_localizedState]
      simp
  have hpos (m : Fin T.N) (hm : (m : ℕ) ≠ 0) : ⟪|m⟩, ψ⟫_ℂ = 0 := by
    have h := congrArg (fun φ => ⟪|m⟩, φ⟫_ℂ) hX
    simp only [← position_hermitian, position_apply_localizedState, inner_smul_left,
      inner_zero_right, Complex.conj_ofReal] at h
    have ha : ((T.a * (m : ℕ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos T.a_pos (by exact_mod_cast Nat.pos_of_ne_zero hm)).ne'
    exact (mul_eq_zero.mp h).resolve_left ha
  have h1 := congrArg (fun φ => ⟪|(⟨1, by omega⟩ : Fin T.N)⟩, φ⟫_ℂ) hK
  simp only [inner_smul_right] at h1
  rw [hpos _ one_ne_zero, mul_zero, inner_apply_eq_sum, Finset.sum_eq_single ⟨0, by omega⟩] at h1
  · rw [inner_hopping, ite_eq_left (Or.inr rfl)] at h1
    have h0 := (mul_eq_zero.mp h1).resolve_left (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr ht))
    refine T.ext_localizedState fun m => ?_
    rw [inner_zero_right]
    by_cases hm : (m : ℕ) = 0
    · rw [show m = ⟨0, by omega⟩ from Fin.ext hm, h0]
    · exact hpos m hm
  · intro k _ hk
    rw [hpos k (fun e => hk (Fin.ext e)), mul_zero]
  · simp

end TightBindingChain
end CondensedMatter
