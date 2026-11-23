/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.Current.TimeReversal
public import PhyslibAlpha.CondensedMatter.TightBindingChain.VelocityBand.Basic
/-!

# The velocity band is open from four sites on

## i. Overview

Time reversal `Θ` (`Current/TimeReversal`) commutes with `H` and `X` and reverses the current `J`,
so it keeps the uncertainty defect, as does a global phase. A unit vector moving at the
speed limit is, up to a phase, an extreme current eigenstate, the maximal current state or its
time reverse, so it has the defect of the maximal current state. From four sites on this defect
is positive, and since the threshold is attained it lies strictly below the speed limit: the
velocity band is not empty.

## ii. Key results

- `defectOf_timeReversal`, `meanOf_current_timeReversal` : `Θ` keeps the defect and reverses
  the current.
- `defectOf_eq_of_meanOf_current_eq` : at the speed limit, the defect of the maximal current state.
- `threshold_lt_maxCurrent`, `maxCurrent_mem_velocityBand` : for `N ≥ 4` the band is not empty.
- `three_div_two_mul_abs_le_threshold` : for `N = 4` the threshold is at least `3/2 |a t|`.

## iii. Table of contents

- A. Time reversal and the uncertainty defect
- B. The speed limit is reached only by extreme eigenstates
- C. The band is not empty
- D. A vector of minimum uncertainty on four sites

## iv. References

* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]
-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open scoped ComplexOrder _root_.selfAdjoint
open InnerProductSpace QuantumMechanics.FiniteHilbertSpace
variable (T : TightBindingChain)

/-!

## A. Time reversal and the uncertainty defect

-/

lemma meanOf_timeReversal {A : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace}
    (hA : ∀ ψ, A (T.timeReversal ψ) = T.timeReversal (A ψ)) (ψ : T.HilbertSpace) :
    T.meanOf A (T.timeReversal ψ) = T.meanOf A ψ := by
  rw [meanOf, meanOf, hA, inner_timeReversal, Complex.conj_re]

lemma meanOf_current_timeReversal (ψ : T.HilbertSpace) :
    T.meanOf T.current (T.timeReversal ψ) = -T.meanOf T.current ψ := by
  rw [meanOf, meanOf, current_timeReversal, inner_neg_right, inner_timeReversal, Complex.neg_re,
    Complex.conj_re]

lemma flucOf_timeReversal {A : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace}
    (hA : ∀ ψ, A (T.timeReversal ψ) = T.timeReversal (A ψ)) (ψ : T.HilbertSpace) :
    T.flucOf A (T.timeReversal ψ) = T.timeReversal (T.flucOf A ψ) := by
  rw [flucOf, flucOf, hA, T.meanOf_timeReversal hA, timeReversal_sub, timeReversal_real_smul]

/-- Time reversal keeps the uncertainty defect. -/
lemma defectOf_timeReversal (ψ : T.HilbertSpace) :
    T.defectOf (T.timeReversal ψ) = T.defectOf ψ := by
  rw [defectOf, defectOf, T.flucOf_timeReversal T.openHamiltonian_timeReversal,
    T.flucOf_timeReversal T.position_timeReversal, norm_timeReversal, norm_timeReversal,
    inner_timeReversal, Complex.norm_conj]

/-- A global phase keeps the uncertainty defect. -/
lemma defectOf_smul {c : ℂ} (hc : ‖c‖ = 1) (ψ : T.HilbertSpace) :
    T.defectOf (c • ψ) = T.defectOf ψ := by
  have hm (A : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace) : T.meanOf A (c • ψ) = T.meanOf A ψ := by
    rw [meanOf, meanOf, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
      Complex.conj_mul', hc]
    simp
  have hf (A : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace) : T.flucOf A (c • ψ) = c • T.flucOf A ψ := by
    rw [flucOf, flucOf, hm, map_smul, smul_sub, smul_comm]
  rw [defectOf, defectOf, hf, hf, norm_smul, norm_smul, hc, one_mul, one_mul, inner_smul_left,
    inner_smul_right, ← mul_assoc, Complex.conj_mul', hc]
  simp

/-!

## B. The speed limit is reached only by extreme eigenstates

-/

/-- The time reverse of the longest standing wave is the shortest one. -/
lemma timeReversal_currentEigenstate_one :
    T.timeReversal (T.currentEigenstate 1) = T.currentEigenstate T.N := by
  have hv (ψ : T.HilbertSpace) (n : Fin T.N) : ψ.val n = ⟪|n⟩, ψ⟫_ℂ := by
    rw [inner_eq_val, localizedState, basisFun_apply, EuclideanSpace.inner_single_left, map_one,
      one_mul]
  ext n
  rw [timeReversal_val, hv, hv, inner_currentEigenstate, inner_currentEigenstate, map_mul,
    map_pow, Complex.conj_I, Complex.conj_ofReal, show ((((n : ℕ) + 1) * (T.N * Real.pi /
      (T.N + 1)) : ℝ)) = ((n : ℕ) + 1 : ℕ) * Real.pi - ((n : ℕ) + 1) * (1 * Real.pi / (T.N + 1))
      by field_simp; push_cast; ring, Real.sin_nat_mul_pi_sub, neg_pow]
  push_cast
  ring

/-- The maximal current state and its time reverse are the extreme current eigenstates. -/
lemma currentBasis_zero (ht : T.t ≠ 0) :
    T.currentBasis ht ⟨0, Nat.pos_of_neZero _⟩ = T.maxCurrentState := by
  simp [currentBasis, currentBasisVec, maxCurrentState]

lemma currentBasis_last (ht : T.t ≠ 0) :
    T.currentBasis ht ⟨T.N - 1, Nat.sub_lt (Nat.pos_of_neZero _) one_pos⟩ =
      T.timeReversal T.maxCurrentState := by
  simp only [currentBasis, OrthonormalBasis.coe_mk, currentBasisVec, maxCurrentState,
    timeReversal_smul, Complex.conj_ofReal, timeReversal_currentEigenstate_one]
  rw [show T.N - 1 + 1 = T.N by have := Nat.pos_of_neZero T.N; omega]

/-- A unit vector moving at the speed limit has the defect of the maximal current state. -/
lemma defectOf_eq_of_meanOf_current_eq (ht : T.t ≠ 0) {ψ : T.HilbertSpace} (hψ : ‖ψ‖ = 1)
    (hv : T.meanOf T.current ψ = T.maxCurrent) :
    T.defectOf ψ = T.defectOf T.maxCurrentState := by
  let b := T.currentBasis ht
  have hN := Nat.pos_of_neZero T.N
  let j : Fin T.N := if 0 < T.a * T.t then ⟨0, hN⟩ else ⟨T.N - 1, by omega⟩
  have hθ : 0 < Real.pi / (T.N + 1) := by positivity
  have hlt (k : Fin T.N) (hk : k ≠ j) : T.currentEigenvalue ((k : ℕ) + 1) < T.maxCurrent := by
    have hk1 : ((k : ℕ) + 1 : ℝ) ≤ T.N := by exact_mod_cast k.isLt
    have h0 : 0 ≤ (((k : ℕ) + 1 : ℕ) : ℝ) * Real.pi / (T.N + 1) := by positivity
    rw [currentEigenvalue, maxCurrent]
    by_cases hat : 0 < T.a * T.t
    · have hk0 : (1 : ℝ) ≤ (k : ℕ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr fun h => hk (Fin.ext (by simp [j, hat, h]))
      have hc := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.le
        (show (((k : ℕ) + 1 : ℕ) : ℝ) * Real.pi / (T.N + 1) ≤ Real.pi by
          rw [div_le_iff₀ (by positivity)]; push_cast; nlinarith [Real.pi_pos])
        (show Real.pi / (T.N + 1) < (((k : ℕ) + 1 : ℕ) : ℝ) * Real.pi / (T.N + 1) by
          rw [div_lt_div_iff_of_pos_right (by positivity)]; push_cast; nlinarith [Real.pi_pos])
      rw [abs_of_pos hat]
      nlinarith [mul_lt_mul_of_pos_left hc hat]
    · have hat' : T.a * T.t < 0 := lt_of_le_of_ne (not_lt.mp hat) (mul_ne_zero T.a_pos.ne' ht)
      have hk1' : ((k : ℕ) + 1 : ℝ) + 1 ≤ T.N := by
        exact_mod_cast (by omega : (k : ℕ) + 1 + 1 ≤ T.N ∨ (k : ℕ) + 1 = T.N).resolve_right
          fun h => hk (Fin.ext (by simp [j, hat]; omega))
      have hc := Real.cos_lt_cos_of_nonneg_of_le_pi h0 (by linarith)
        (show (((k : ℕ) + 1 : ℕ) : ℝ) * Real.pi / (T.N + 1) < Real.pi - Real.pi / (T.N + 1) by
          rw [div_lt_iff₀ (by positivity), sub_mul, div_mul_cancel₀ _ (by positivity)]
          push_cast; nlinarith [Real.pi_pos])
      rw [Real.cos_pi_sub, abs_of_neg hat'] at *
      nlinarith [mul_lt_mul_of_neg_left hc hat']
  have hw := b.sum_sq_norm_inner_right ψ
  rw [hψ, one_pow] at hw
  have hnn (k : Fin T.N) : 0 ≤ (T.maxCurrent - T.currentEigenvalue ((k : ℕ) + 1)) *
      ‖⟪b k, ψ⟫_ℂ‖ ^ 2 := mul_nonneg (sub_nonneg.mpr ((le_abs_self _).trans
        (T.abs_currentEigenvalue_le (by omega) (by omega)))) (sq_nonneg _)
  have hsum :
      ∑ k : Fin T.N, (T.maxCurrent - T.currentEigenvalue ((k : ℕ) + 1)) * ‖⟪b k, ψ⟫_ℂ‖ ^ 2 = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hw, mul_one]
    rw [← T.re_inner_current_eq_sum ht ψ]
    exact sub_eq_zero.mpr hv.symm
  have hz (k : Fin T.N) (hk : k ≠ j) : ⟪b k, ψ⟫_ℂ = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hnn k).mp hsum k (Finset.mem_univ _)
    rw [mul_eq_zero, or_iff_right (sub_ne_zero.mpr (hlt k hk).ne')] at this
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  have hψj : ψ = ⟪b j, ψ⟫_ℂ • b j := by
    conv_lhs => rw [← b.sum_repr' ψ]
    exact Finset.sum_eq_single j (fun k _ hk => by rw [hz k hk, zero_smul]) (by simp)
  have hc : ‖⟪b j, ψ⟫_ℂ‖ = 1 := by
    rw [Finset.sum_eq_single j (fun k _ hk => by rw [hz k hk, norm_zero, zero_pow two_ne_zero])
      (by simp)] at hw
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hw
  rw [hψj, T.defectOf_smul hc]
  by_cases hat : 0 < T.a * T.t
  · simp only [b, j, hat, ite_true, currentBasis_zero]
  · simp only [b, j, hat, ite_false, currentBasis_last, defectOf_timeReversal]

/-!

## C. The band is not empty

-/

/-- From four sites on, the threshold lies strictly below the speed limit. -/
lemma threshold_lt_maxCurrent (ht : T.t ≠ 0) (hN : 4 ≤ T.N) : T.threshold < T.maxCurrent := by
  obtain ⟨ψ, ⟨hψ, h0⟩, hv⟩ := T.exists_threshold
  have hψ' := mem_sphere_zero_iff_norm.mp hψ
  have hpos : T.defectOf T.maxCurrentState ≠ 0 := fun h => by
    rw [← T.centeredGramDefect_ofVec_eq T.norm_maxCurrentState] at h
    rcases (T.centeredGramDefect_maxCurrentState_eq_zero_iff ht (by omega)).mp h with h | h <;>
      omega
  refine (T.threshold_le_maxCurrent ht).lt_of_ne fun he => hpos ?_
  rcases eq_or_eq_neg_of_abs_eq (hv.trans he) with h | h
  · rw [← T.defectOf_eq_of_meanOf_current_eq ht hψ' h]
    exact h0
  · rw [← T.defectOf_eq_of_meanOf_current_eq ht ((T.norm_timeReversal ψ).trans hψ')
      (by rw [meanOf_current_timeReversal, h, neg_neg]), defectOf_timeReversal]
    exact h0

/-- From four sites on, the velocity band is not empty: it contains the speed limit. -/
lemma maxCurrent_mem_velocityBand (ht : T.t ≠ 0) (hN : 4 ≤ T.N) :
    T.maxCurrent ∈ T.velocityBand :=
  ⟨T.threshold_lt_maxCurrent ht hN, le_rfl⟩


/-!

## D. A vector of minimum uncertainty on four sites

-/

private lemma inner_localizedState_sum (c : Fin T.N → ℂ) (m : Fin T.N) :
    ⟪|m⟩, ∑ n, c n • |n⟩⟫_ℂ = c m := by
  rw [inner_sum]
  simp_rw [inner_smul_right, localizedState_orthonormal_eq_ite]
  simp

open ComplexConjugate in
private lemma inner_sum_sum (c d : Fin T.N → ℂ) :
    ⟪∑ n, c n • |n⟩, ∑ n, d n • |n⟩⟫_ℂ = ∑ n, conj (c n) * d n := by
  rw [← OrthonormalBasis.sum_inner_mul_inner localizedState]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← inner_conj_symm, inner_localizedState_sum, inner_localizedState_sum]

open ComplexConjugate in
/-- On four sites the threshold is at least `3/2 |a t|`: the unit vector
`√2/8 (2i, -(3 + i√3), √3 - 3i, 2)` has zero defect and current `3 a t / 2`. -/
lemma three_div_two_mul_abs_le_threshold (hN : T.N = 4) :
    3 / 2 * |T.a * T.t| ≤ T.threshold := by
  cases T with | mk N a ha E0 t => ?_
  simp only at hN; subst hN
  set T : TightBindingChain := ⟨4, a, ha, E0, t⟩
  set s : ℂ := ((√2 : ℝ) : ℂ) / 8
  set r : ℂ := ((√3 : ℝ) : ℂ)
  have hs : s ^ 2 = 1 / 32 := by
    have h : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    simp only [s]; linear_combination h / 64
  have hr : r ^ 2 = 3 := by
    simp only [r]; exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hI := Complex.I_sq
  have hsc : conj s = s := by simp [s, map_div₀, map_ofNat]
  have hrc : conj r = r := Complex.conj_ofReal _
  let c : Fin T.N → ℂ := ![2 * s * .I, -(s * (3 + r * .I)), s * (r - 3 * .I), 2 * s]
  let d : Fin T.N → ℂ := ![c 1, c 0 + c 2, c 1 + c 3, c 2]
  let ψ : T.HilbertSpace := ∑ n, c n • |n⟩
  let v : T.HilbertSpace := ∑ n, d n • |n⟩
  let l : ℂ := a * (r + 3 * .I) / 4
  have hH : T.openHamiltonian ψ = (E0 : ℂ) • ψ - (t : ℂ) • v := by
    refine T.ext_localizedState fun m => ?_
    rw [inner_apply_eq_sum]
    simp only [ψ, v, inner_sub_right, inner_smul_right, inner_openHamiltonian,
      inner_localizedState_sum]
    dsimp only [T]
    simp only [Fin.sum_univ_four]
    fin_cases m <;> simp [c, d, Fin.ext_iff, T] <;> ring
  have hX : T.position ψ = (((3 / 2 : ℝ) * a : ℝ) : ℂ) • ψ + l • v := by
    refine T.ext_localizedState fun m => ?_
    rw [← position_hermitian, position_apply_localizedState, inner_smul_left, Complex.conj_ofReal,
      inner_add_right, inner_smul_right, inner_smul_right, inner_localizedState_sum,
      inner_localizedState_sum]
    fin_cases m <;> simp [T, c, d, l]
    · linear_combination (3 * a * r * s / 4) * hI + (.I * a * s / 4) * hr
    · linear_combination (3 * a * s / 4) * hI + (-a * s / 4) * hr
    · linear_combination (3 * a * r * s / 4) * hI + (.I * a * s / 4) * hr
    · linear_combination (9 * a * s / 4) * hI + (-a * s / 4) * hr
  have hpp : ⟪ψ, ψ⟫_ℂ = 1 := by
    simp only [ψ, inner_sum_sum]; dsimp only [T]; simp only [Fin.sum_univ_four]
    simp [c, map_ofNat, hsc, hrc]
    linear_combination (-s ^ 2 * (r ^ 2 + 13)) * hI + (2 * s ^ 2) * hr + 32 * hs
  have hvv : ⟪v, v⟫_ℂ = 1 := by
    simp only [v, inner_sum_sum]; dsimp only [T]; simp only [Fin.sum_univ_four]
    simp [d, c, map_ofNat, hsc, hrc]
    linear_combination (-2 * s ^ 2 * (r ^ 2 + 5)) * hI + (4 * s ^ 2) * hr + 32 * hs
  have hpv : ⟪ψ, v⟫_ℂ = 0 := by
    simp only [ψ, v, inner_sum_sum]; dsimp only [T]; simp only [Fin.sum_univ_four]
    simp [d, c, map_ofNat, hsc, hrc]
    linear_combination (-2 * r * s ^ 2) * hI
  have hvp : ⟪v, ψ⟫_ℂ = 0 := by rw [← inner_conj_symm, hpv, map_zero]
  have hnorm (w : T.HilbertSpace) (h : ⟪w, w⟫_ℂ = 1) : ‖w‖ = 1 := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), h]; simp
  have hfH : T.flucOf T.openHamiltonian ψ = (-(t : ℂ)) • v := by
    have : T.meanOf T.openHamiltonian ψ = E0 := by
      simp only [meanOf, hH, inner_sub_right, inner_smul_right, hpp, hpv]; simp
    rw [flucOf, this, hH, ← Complex.coe_smul]; module
  have hfX : T.flucOf T.position ψ = l • v := by
    have : T.meanOf T.position ψ = 3 / 2 * a := by
      simp only [meanOf, hX, inner_add_right, inner_smul_right, hpp, hpv]; simp
    rw [flucOf, this, hX, ← Complex.coe_smul]; module
  have hdef : T.defectOf ψ = 0 := by
    rw [defectOf, hfH, hfX, inner_smul_left, inner_smul_right, hvv, norm_smul, norm_smul,
      hnorm v hvv]
    simp only [mul_one, norm_mul, Complex.norm_conj]; ring
  have hJ : T.meanOf T.current ψ = 3 / 2 * a * t := by
    have hc : ⟪ψ, T.current ψ⟫_ℂ = ((3 / 2 * a * t : ℝ) : ℂ) := by
      simp only [current, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        inner_smul_right, inner_sub_right]
      rw [← T.openHamiltonian_hermitian ψ (T.position ψ),
        ← T.position_hermitian ψ (T.openHamiltonian ψ), hH, hX]
      simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, hpp, hvv, hpv, hvp, Complex.conj_ofReal, l,
        map_div₀, map_mul, map_add, map_ofNat, hrc, Complex.conj_I]
      push_cast
      linear_combination (-3 * a * t / 2) * hI
    rw [meanOf, hc, Complex.ofReal_re]
  have hle := T.le_threshold ⟨mem_sphere_zero_iff_norm.mpr (hnorm ψ hpp), hdef⟩
  rwa [hJ, show (3 / 2 : ℝ) * a * t = 3 / 2 * (a * t) by ring, abs_mul (3 / 2 : ℝ),
    abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hle

end TightBindingChain
end CondensedMatter
