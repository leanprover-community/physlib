/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.VelocityBand
public import PhyslibAlpha.QuantumMechanics.HilbertSpaces.FiniteTarget.Product
/-!

# The velocity band is open from four sites on

## i. Overview

Time reversal `Θ` conjugates amplitudes. `H` and `X` are real, so they commute with `Θ`, while
the current `J` changes sign; the uncertainty defect is invariant. A unit vector moving at the
speed limit is, up to a phase, an extreme current eigenstate, the maximal current state or its
time reverse, so it has the defect of the maximal current state. From four sites on this defect
is positive, and since the threshold is attained it lies strictly below the speed limit: the
velocity band `Ϙ` is not empty.

## ii. Key results

- `timeReversal` : complex conjugation of amplitudes.
- `defectOf_timeReversal`, `meanOf_current_timeReversal` : `Θ` keeps the defect and reverses
  the current.
- `defectOf_eq_of_meanOf_current_eq` : at the speed limit, the defect of the maximal current state.
- `threshold_lt_maxCurrent`, `maxCurrent_mem_velocityBand` : for `N ≥ 4` the band is not empty.

## iii. Table of contents

- A. Time reversal
- B. The speed limit is reached only by extreme eigenstates
- C. The band is not empty

## iv. References

* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]
-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open scoped ComplexOrder selfAdjoint
open InnerProductSpace QuantumMechanics.FiniteHilbertSpace
variable (T : TightBindingChain)

/-!

## A. Time reversal

-/

/-- Time reversal: complex conjugation of the amplitudes. -/
noncomputable def timeReversal (ψ : T.HilbertSpace) : T.HilbertSpace :=
  ⟨WithLp.toLp 2 fun n => (starRingEnd ℂ) (ψ.val n)⟩

lemma timeReversal_val (ψ : T.HilbertSpace) (n : Fin T.N) :
    (T.timeReversal ψ).val n = (starRingEnd ℂ) (ψ.val n) := rfl

lemma timeReversal_sub (ψ φ : T.HilbertSpace) :
    T.timeReversal (ψ - φ) = T.timeReversal ψ - T.timeReversal φ := by
  ext n
  exact map_sub _ _ _

lemma timeReversal_smul (c : ℂ) (ψ : T.HilbertSpace) :
    T.timeReversal (c • ψ) = (starRingEnd ℂ) c • T.timeReversal ψ := by
  ext n
  exact map_mul _ _ _

lemma timeReversal_real_smul (r : ℝ) (ψ : T.HilbertSpace) :
    T.timeReversal (r • ψ) = r • T.timeReversal ψ := by
  rw [← Complex.coe_smul, timeReversal_smul, Complex.conj_ofReal, Complex.coe_smul]

lemma inner_timeReversal (ψ φ : T.HilbertSpace) :
    ⟪T.timeReversal ψ, T.timeReversal φ⟫_ℂ = (starRingEnd ℂ) ⟪ψ, φ⟫_ℂ := by
  simp only [inner_eq_val, PiLp.inner_apply, map_sum, RCLike.inner_apply, timeReversal_val,
    map_mul, Complex.conj_conj]

lemma norm_timeReversal (ψ : T.HilbertSpace) : ‖T.timeReversal ψ‖ = ‖ψ‖ := by
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ ψ, inner_timeReversal,
    RCLike.conj_re]

/-- An operator with real matrix elements commutes with time reversal. -/
lemma apply_timeReversal {A : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace}
    (hA : ∀ n m, (starRingEnd ℂ) ⟪|n⟩, A |m⟩⟫_ℂ = ⟪|n⟩, A |m⟩⟫_ℂ) (ψ : T.HilbertSpace) :
    A (T.timeReversal ψ) = T.timeReversal (A ψ) := by
  ext n
  rw [val_apply, timeReversal_val, val_apply, map_sum]
  exact Finset.sum_congr rfl fun m _ => by
    rw [map_mul, timeReversal_val, val_apply_basisFun]
    exact congrArg (· * _) (hA n m).symm

lemma openHamiltonian_timeReversal (ψ : T.HilbertSpace) :
    T.openHamiltonian (T.timeReversal ψ) = T.timeReversal (T.openHamiltonian ψ) :=
  T.apply_timeReversal (fun n m => by rw [inner_openHamiltonian]; split_ifs <;> simp) ψ

lemma position_timeReversal (ψ : T.HilbertSpace) :
    T.position (T.timeReversal ψ) = T.timeReversal (T.position ψ) :=
  T.apply_timeReversal (fun n m => by
    rw [position_apply_localizedState, inner_smul_right, localizedState_orthonormal_eq_ite]
    split_ifs <;> simp) ψ

/-- Time reversal reverses the current. -/
lemma current_timeReversal (ψ : T.HilbertSpace) :
    T.current (T.timeReversal ψ) = -T.timeReversal (T.current ψ) := by
  simp only [current, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    position_timeReversal, openHamiltonian_timeReversal, ← timeReversal_sub, timeReversal_smul,
    Complex.conj_I, neg_smul, neg_neg]

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
theorem threshold_lt_maxCurrent (ht : T.t ≠ 0) (hN : 4 ≤ T.N) : T.threshold < T.maxCurrent := by
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
theorem maxCurrent_mem_velocityBand (ht : T.t ≠ 0) (hN : 4 ≤ T.N) :
    T.maxCurrent ∈ T.velocityBand :=
  ⟨T.threshold_lt_maxCurrent ht hN, le_rfl⟩

end TightBindingChain
end CondensedMatter
