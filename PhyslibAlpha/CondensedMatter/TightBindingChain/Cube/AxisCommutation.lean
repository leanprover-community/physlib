/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube.Basic
public import PhyslibAlpha.CondensedMatter.TightBindingChain.Current.MandelstamTamm
/-!

# Which observables of the open tight binding cube commute

## i. Overview

The six observables of the cube are the Hamiltonian `H` and the position `X` of each axis
(`cubePairs`). Two of them on different axes commute (`bracket_cubePairs_of_ne`). Here the
converse: `H` and `X` of one axis do not commute, since their bracket has a nonzero expectation in
the maximal current state, and by Robertson's relation the product of their variances is positive
in that state. So two distinct observables of the cube commute if and only if they lie on
different axes.

## ii. Key results

- `bracket_openHamiltonian_position_eq_zero_iff` : on one chain, `⁅H, X⁆ = 0` if and only if
  `t = 0` or the chain has a single site, so the hypotheses below cannot be dropped.
- `axisBracket_maxCurrentCubeVectorState_ne_zero` : in the maximal current state, the expectation
  of `⁅H, X⁆` is nonzero on each axis.
- `bracket_cubePairs_pair_ne_zero` : `H` and `X` of one axis do not commute.
- `bracket_cubePairs_eq_zero_iff` : two distinct observables of the cube commute if and only if
  they lie on different axes.
- `variance_mul_variance_cubePairs_pos` : in the maximal current state, `Var H · Var X > 0` on
  each axis.

## iii. Table of contents

- A. One chain: when `H` and `X` commute
- B. The pair of an axis does not commute
- C. Commuting and axes

## iv. References

* H. P. Robertson, *The uncertainty principle*, Phys. Rev. 34 (1929) 163.

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open scoped selfAdjoint
open ProbabilisticTheory UnitalPositiveLinearMap

variable {Tx Ty Tz : TightBindingChain}

/-!

## A. One chain: when `H` and `X` commute

-/

/-- Without hopping, or with a single site, the hopping operator is zero. -/
lemma hopping_eq_zero_of_degenerate (T : TightBindingChain) (h : T.t = 0 ∨ T.N < 2) :
    T.hopping = 0 := by
  refine T.localizedState.toBasis.ext fun n => T.ext_localizedState fun m => ?_
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.zero_apply, inner_zero_right]
  rw [T.inner_hopping]
  split_ifs with hc
  · rcases h with h | h
    · simp [h]
    · have := m.isLt
      have := n.isLt
      omega
  · rfl

/-- On one chain, the Hamiltonian and the position commute if and only if there is no hopping or
only one site. -/
lemma bracket_openHamiltonian_position_eq_zero_iff (T : TightBindingChain) :
    ⁅T.openHamiltonianObservable, T.positionObservable⁆ = 0 ↔ T.t = 0 ∨ T.N < 2 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hc
    push Not at hc
    have h0 := T.expectation_bracket_maxCurrentState
    rw [h] at h0
    exact T.bound_ne_zero hc.1 hc.2 (by simpa using h0.symm)
  · apply Subtype.ext
    rw [T.coe_bracket_openHamiltonian_position]
    refine ContinuousLinearMap.ext fun ψ => ?_
    change (-(1 / 2) : ℂ) • T.current ψ = 0
    rw [T.current_eq_hopping, T.hopping_eq_zero_of_degenerate h]
    simp

/-!

## B. The pair of an axis does not commute

-/

/-- In the maximal current state of the cube, the expectation of `⁅H, X⁆` is nonzero on each
axis. -/
lemma axisBracket_maxCurrentCubeVectorState_ne_zero (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0)
    (hz : Tz.t ≠ 0) (hNx : 2 ≤ Tx.N) (hNy : 2 ≤ Ty.N) (hNz : 2 ≤ Tz.N) (k : Fin 3) :
    Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) k ≠ 0 := by
  have hne : Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 0 *
      Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 1 *
      Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 2 ≠ 0 := fun h0 =>
    pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (Tx.bound_ne_zero hx hNx)
      (Ty.bound_ne_zero hy hNy)) (Tz.bound_ne_zero hz hNz))
      (by simpa [h0] using (Tx.sq_axisBracket_maxCurrentCubeState Ty Tz).symm)
  intro hk
  fin_cases k <;> simp_all

/-- The Hamiltonian and the position of one axis of the cube do not commute. -/
lemma bracket_cubePairs_pair_ne_zero (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 2 ≤ Tx.N) (hNy : 2 ≤ Ty.N) (hNz : 2 ≤ Tz.N) (k : Fin 3) :
    ⁅Tx.cubePairs Ty Tz (0, k), Tx.cubePairs Ty Tz (1, k)⁆ ≠ 0 := fun h =>
  axisBracket_maxCurrentCubeVectorState_ne_zero hx hy hz hNx hNy hNz k (by simp [axisBracket, h])

/-- In the maximal current state of the cube, the variances of `H` and `X` of each axis have a
positive product. -/
lemma variance_mul_variance_cubePairs_pos (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 2 ≤ Tx.N) (hNy : 2 ≤ Ty.N) (hNz : 2 ≤ Tz.N) (k : Fin 3) :
    0 < variance (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.cubePairs Ty Tz (0, k)) *
      variance (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.cubePairs Ty Tz (1, k)) :=
  lt_of_lt_of_le
    (sq_pos_of_ne_zero (axisBracket_maxCurrentCubeVectorState_ne_zero hx hy hz hNx hNy hNz k))
    (robertson (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.cubePairs Ty Tz (0, k))
      (Tx.cubePairs Ty Tz (1, k)))

/-!

## C. Commuting and axes

-/

/-- Two distinct observables of the cube commute if and only if they lie on different axes. -/
lemma bracket_cubePairs_eq_zero_iff (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 2 ≤ Tx.N) (hNy : 2 ≤ Ty.N) (hNz : 2 ≤ Tz.N) {p q : Fin 2 × Fin 3} (h : p ≠ q) :
    ⁅Tx.cubePairs Ty Tz p, Tx.cubePairs Ty Tz q⁆ = 0 ↔ p.2 ≠ q.2 := by
  refine ⟨fun h0 hk => ?_, Tx.bracket_cubePairs_of_ne Ty Tz⟩
  obtain ⟨j, k⟩ := p
  obtain ⟨j', k'⟩ := q
  simp only at hk
  subst hk
  have hne := bracket_cubePairs_pair_ne_zero (Tx := Tx) (Ty := Ty) (Tz := Tz) hx hy hz hNx hNy
    hNz k
  fin_cases j <;> fin_cases j' <;> simp at h ⊢
  · exact hne h0
  · rw [selfAdjoint.bracket_def, selfAdjoint.lieMul_swap, ← selfAdjoint.bracket_def] at h0
    exact hne (neg_eq_zero.mp h0)

end TightBindingChain
end CondensedMatter
