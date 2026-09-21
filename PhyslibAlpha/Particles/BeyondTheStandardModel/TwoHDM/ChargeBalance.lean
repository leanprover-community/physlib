/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Tactic.Ring
/-!
# Charge balancing for polynomials

If the variables of a polynomial carry charges under a phase (here a single element `c` of infinite
order), then invariance under the simultaneous phase rotation `Xᵢ ↦ c^{wᵢ} Xᵢ` forces every
monomial to be *charge balanced* (net charge zero). This is the algebraic content of the statement
that a gauge invariant potential, restricted to a slice on which the gauge torus acts diagonally,
can only contain charge-balanced monomials.
-/

@[expose] public section

namespace MvPolynomial

open scoped Classical in
/-- Rescaling each variable `Xᵢ` by a constant `d i` multiplies the coefficient of the monomial `m`
  by `∏ᵢ (d i) ^ (m i)`. -/
lemma coeff_aeval_diag {σ R : Type*} [CommRing R] (d : σ → R) (f : MvPolynomial σ R)
    (m : σ →₀ ℕ) :
    (aeval (fun i => C (d i) * X i) f).coeff m = (m.prod fun i k => d i ^ k) * f.coeff m := by
  induction f using MvPolynomial.induction_on generalizing m with
  | C a =>
    rw [aeval_C, MvPolynomial.algebraMap_eq, coeff_C]
    by_cases hm : (0 : σ →₀ ℕ) = m
    · subst hm; simp
    · rw [ite_eq_right hm, mul_zero]
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp m, hq m, mul_add]
  | mul_X p i hp =>
    rw [map_mul, aeval_X]
    have hrw : (aeval (fun i => C (d i) * X i) p) * (C (d i) * X i)
        = C (d i) * ((aeval (fun i => C (d i) * X i) p) * X i) := by
      rw [mul_left_comm]
    rw [hrw, coeff_C_mul, coeff_mul_X', coeff_mul_X']
    by_cases hi : i ∈ m.support
    · rw [ite_eq_left hi, ite_eq_left hi, hp (m - Finsupp.single i 1)]
      have hmi : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
      have hle : Finsupp.single i 1 ≤ m := Finsupp.single_le_iff.mpr hmi
      have hsplit : m = (m - Finsupp.single i 1) + Finsupp.single i 1 :=
        (tsub_add_cancel_of_le hle).symm
      have hprod : (m.prod fun i k => d i ^ k)
          = ((m - Finsupp.single i 1).prod fun i k => d i ^ k) * d i := by
        conv_lhs => rw [hsplit]
        rw [Finsupp.prod_add_index' (by intro a; simp) (by intro a b c; rw [pow_add]),
          Finsupp.prod_single_index (by simp)]
        simp
      rw [hprod]
      ring
    · rw [ite_eq_right hi, ite_eq_right hi, mul_zero, mul_zero]

/-- **Charge balancing.** If each variable `Xᵢ` carries an integer charge `w i`, `c` is a phase of
  infinite order, and the polynomial `f` is invariant under the charge rotation
  `Xᵢ ↦ c^{wᵢ} Xᵢ`, then every monomial with nonzero net charge has vanishing coefficient. -/
lemma coeff_eq_zero_of_charge_ne_zero {σ K : Type*} [Field K] (w : σ → ℤ) (c : K) (hc : c ≠ 0)
    (hroot : ∀ n : ℤ, c ^ n = 1 → n = 0) {f : MvPolynomial σ K}
    (hf : aeval (fun i => C (c ^ (w i)) * X i) f = f) {m : σ →₀ ℕ}
    (hm : ∑ i ∈ m.support, (m i : ℤ) * w i ≠ 0) :
    f.coeff m = 0 := by
  classical
  have key := coeff_aeval_diag (fun i => c ^ (w i)) f m
  rw [hf] at key
  have hgen : ∀ s : Finset σ, ∏ i ∈ s, (c ^ (w i)) ^ (m i)
      = c ^ (∑ i ∈ s, (m i : ℤ) * w i) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | @insert x t hx ih =>
      rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add₀ hc]
      congr 1
      rw [← zpow_natCast (c ^ w x) (m x), ← zpow_mul, mul_comm]
  rw [Finsupp.prod, hgen] at key
  have hne : c ^ (∑ i ∈ m.support, (m i : ℤ) * w i) ≠ 1 := fun h => hm (hroot _ h)
  have h2 : (1 - c ^ (∑ i ∈ m.support, (m i : ℤ) * w i)) * f.coeff m = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hne
  · exact h

end MvPolynomial
