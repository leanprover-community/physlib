/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.Current
public import Mathlib.RingTheory.RootsOfUnity.Complex
/-!

# The current eigenstates of the open tight binding chain

## i. Overview

The standing waves `sin ((n + 1) k π / (N + 1))` of the open chain vanish just outside both
ends. Dressed with the phase `iⁿ`, they diagonalize the current operator `J`: the state
`∑ n, iⁿ sin ((n + 1) k π / (N + 1)) |n⟩` moves with current `2 a t cos (k π / (N + 1))`.

## ii. Key results

- `currentEigenstate` : the current eigenstate with quantum number `k`.
- `current_currentEigenstate` : `J ψ_k = 2 a t cos (k π / (N + 1)) ψ_k`.
- `norm_sq_currentEigenstate` : `‖ψ_k‖² = (N + 1) / 2` for `1 ≤ k ≤ N`.

## iii. Table of contents

- A. The current eigenstates
- B. The eigenvalue equation
- C. The norm

## iv. References

* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]
-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open InnerProductSpace
variable (T : TightBindingChain)

/-!

## A. The current eigenstates

-/

/-- The current eigenstate `∑ n, iⁿ sin ((n + 1) k π / (N + 1)) |n⟩`. -/
noncomputable def currentEigenstate (k : ℕ) : T.HilbertSpace :=
  ∑ n : Fin T.N, (Complex.I ^ (n : ℕ) *
    Real.sin (((n : ℕ) + 1) * (k * Real.pi / (T.N + 1)))) • |n⟩

/-- The current `2 a t cos (k π / (N + 1))` of the eigenstate with quantum number `k`. -/
noncomputable def currentEigenvalue (k : ℕ) : ℝ :=
  2 * T.a * T.t * Real.cos (k * Real.pi / (T.N + 1))

/-- The amplitude of the current eigenstate on the site `m`. -/
lemma inner_currentEigenstate (k : ℕ) (m : Fin T.N) :
    ⟪|m⟩, T.currentEigenstate k⟫_ℂ =
      Complex.I ^ (m : ℕ) * Real.sin (((m : ℕ) + 1) * (k * Real.pi / (T.N + 1))) := by
  rw [currentEigenstate, T.localizedState_orthonormal.inner_right_fintype]

/-!

## B. The eigenvalue equation

-/

/-- A sum over the sites picking at most one site. -/
lemma sum_ite_eq_of_unique {N : ℕ} (P : Fin N → Prop) [DecidablePred P] (v : ℂ)
    (h : ∀ n n', P n → P n' → n = n') (hv : (∀ n, ¬ P n) → v = 0) :
    ∑ n, (if P n then v else 0) = v := by
  by_cases hex : ∃ n, P n
  · obtain ⟨n, hn⟩ := hex
    rw [Finset.sum_eq_single n (fun b _ hb => ite_eq_right_iff.mpr fun hb' =>
      absurd (h _ _ hb' hn) hb) (by simp)]
    simp [hn]
  · simp [not_exists.mp hex, hv (not_exists.mp hex)]

/-- The current eigenstates satisfy `J ψ_k = 2 a t cos (k π / (N + 1)) ψ_k`. -/
lemma current_currentEigenstate (k : ℕ) :
    T.current (T.currentEigenstate k) =
      (T.currentEigenvalue k : ℂ) • T.currentEigenstate k := by
  have hN : Real.sin (((T.N : ℝ) + 1) * (k * Real.pi / (T.N + 1))) = 0 := by
    rw [mul_div_cancel₀ _ (by positivity)]
    exact Real.sin_nat_mul_pi k
  apply localizedState.repr.injective
  ext m
  simp only [OrthonormalBasis.repr_apply_apply]
  rw [inner_smul_right, inner_currentEigenstate, currentEigenvalue]
  simp only [currentEigenstate, map_sum, map_smul, inner_sum, inner_smul_right, inner_current_eq]
  generalize (k : ℝ) * Real.pi / (T.N + 1) = θ at hN ⊢
  have key (n : Fin T.N) : Complex.I ^ (n : ℕ) * Real.sin (((n : ℕ) + 1) * θ) *
      (if (m : ℕ) + 1 = n then -(Complex.I * (T.a * T.t : ℝ))
        else if (n : ℕ) + 1 = m then Complex.I * (T.a * T.t : ℝ) else 0) =
      (if (m : ℕ) + 1 = n then (T.a * T.t : ℝ) * Complex.I ^ (m : ℕ) *
        Real.sin (((m : ℕ) + 2) * θ) else 0) +
      if (n : ℕ) + 1 = m then (T.a * T.t : ℝ) * Complex.I ^ (m : ℕ) *
        Real.sin ((m : ℕ) * θ) else 0 := by
    by_cases hA : (m : ℕ) + 1 = n
    · have hn : (n : ℕ) = m + 1 := hA.symm
      simp only [hn, show ¬ ((m : ℕ) + 1 + 1 = m) by omega, ite_true, ite_false, add_zero]
      rw [show (((m + 1 : ℕ) : ℝ) + 1) = (m : ℕ) + 2 by push_cast; ring, pow_succ]
      linear_combination (-((T.a * T.t : ℝ) * Complex.I ^ (m : ℕ) *
        Real.sin (((m : ℕ) + 2) * θ))) * Complex.I_sq
    by_cases hB : (n : ℕ) + 1 = m
    · simp only [hA, hB, ite_true, ite_false, zero_add]
      rw [← hB]
      push_cast
      ring
    · simp [hA, hB]
  have hv1 (h : ∀ n : Fin T.N, ¬ ((m : ℕ) + 1 = n)) :
      Real.sin (((m : ℕ) + 2) * θ) = 0 := by
    have hm : (m : ℕ) + 1 = T.N := by
      by_contra hne
      exact h ⟨(m : ℕ) + 1, by omega⟩ rfl
    have hm' : ((m : ℕ) : ℝ) + 1 = T.N := by exact_mod_cast hm
    rw [show ((m : ℕ) + 2 : ℝ) = T.N + 1 by linarith, hN]
  have hv2 (h : ∀ n : Fin T.N, ¬ ((n : ℕ) + 1 = m)) : Real.sin ((m : ℕ) * θ) = 0 := by
    have hm : (m : ℕ) = 0 := by
      by_contra hne
      exact h ⟨(m : ℕ) - 1, by omega⟩ (Nat.sub_add_cancel (by omega))
    simp [hm]
  have hr : Real.sin (((m : ℕ) + 2) * θ) + Real.sin ((m : ℕ) * θ) =
      2 * Real.cos θ * Real.sin (((m : ℕ) + 1) * θ) := by
    rw [show ((m : ℕ) + 2) * θ = ((m : ℕ) + 1) * θ + θ by ring,
      show ((m : ℕ) : ℝ) * θ = ((m : ℕ) + 1) * θ - θ by ring, Real.sin_add, Real.sin_sub]
    ring
  rw [Finset.sum_congr rfl fun n _ => key n, Finset.sum_add_distrib,
    sum_ite_eq_of_unique _ _ (fun n n' h h' => Fin.ext (by omega)) fun h => by simp [hv1 h],
    sum_ite_eq_of_unique _ _ (fun n n' h h' => Fin.ext (by omega)) fun h => by simp [hv2 h]]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
  push_cast at hc ⊢
  linear_combination ((T.a : ℂ) * T.t * Complex.I ^ (m : ℕ)) * hc

/-!

## C. The norm

-/

/-- The cosines `cos (2 j k π / (N + 1))` sum to zero over `j < N + 1` for `1 ≤ k ≤ N`. -/
private lemma sum_cos_eq_zero {k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ T.N) :
    ∑ j ∈ Finset.range (T.N + 1), Real.cos (2 * (j * (k * Real.pi / (T.N + 1)))) = 0 := by
  have hζ := Complex.isPrimitiveRoot_exp (T.N + 1) (by omega)
  have hω := hζ.pow_ne_one_of_pos_of_lt (by omega : k ≠ 0) (by omega : k < T.N + 1)
  have hpow := ((pow_right_comm _ k (T.N + 1)).trans
    (congrArg (· ^ k) hζ.pow_eq_one)).trans (one_pow k)
  have h := congrArg Complex.re (geom_sum_eq hω (T.N + 1))
  rw [hpow, sub_self, zero_div, Complex.re_sum, Complex.zero_re] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_mul, ← Complex.exp_nat_mul, ← Complex.exp_ofReal_mul_I_re]
  congr 2
  push_cast
  ring

/-- The squared sines `sin² (j k π / (N + 1))` sum to `(N + 1) / 2` over `j < N + 1`. -/
private lemma sum_sin_sq {k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ T.N) :
    ∑ j ∈ Finset.range (T.N + 1), Real.sin (j * (k * Real.pi / (T.N + 1))) ^ 2 =
      (T.N + 1) / 2 := by
  simp only [Real.sin_sq_eq_half_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, sum_cos_eq_zero T hk hkN]
  simp

/-- The current eigenstates have squared norm `(N + 1) / 2` for `1 ≤ k ≤ N`. -/
lemma norm_sq_currentEigenstate {k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ T.N) :
    ‖T.currentEigenstate k‖ ^ 2 = (T.N + 1) / 2 := by
  rw [← localizedState.sum_sq_norm_inner_right]
  simp only [inner_currentEigenstate, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => Real.sin ((j + 1) * (k * Real.pi / (T.N + 1))) ^ 2),
    ← sum_sin_sq T hk hkN, Finset.sum_range_succ']
  simp

end TightBindingChain
end CondensedMatter
