/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.NormalizedBasis

/-!

# Clebsch–Gordan coefficients

The orthonormal coupled basis `|J, M⟩` of `V(m) ⊗ V(n)` over `ℝ` and the Clebsch–Gordan
coefficients `⟨j₁ m₁ j₂ m₂ | J M⟩` in the standard normalisation and phase convention.

## i. Overview

The contravariant forms on `V(m)` and `V(n)` combine to a symmetric bilinear form on
`V(m) ⊗ V(n)` for which the diagonal raising and lowering operators are adjoint. For the
lowering strings `f^l w_k` of the highest-weight vectors `w_k` this gives

`⟨f^a w_k, f^b w_{k'}⟩ = δ_{kk'} δ_{ab} · a! N!/(N - a)! · ⟨w_k, w_k⟩`,  `N = m + n - 2k`,

and `⟨w_k, w_k⟩ > 0`. Normalising gives the orthonormal coupled basis
`|J, M⟩ = coupledVec m n k l` with `J = (m + n)/2 - k`, `M = J - l`, on which `J₊, J₋`
act by the textbook formulas. The Clebsch–Gordan coefficient is the inner product

`⟨j₁ m₁ j₂ m₂ | J M⟩ = cgCoefficient m n k l a b = ⟨u_a ⊗ u_b, |J, M⟩⟩`

with `j₁ = m/2`, `m₁ = j₁ - a`, `j₂ = n/2`, `m₂ = j₂ - b`. This file proves:

- the coupled states are orthonormal and satisfy the ladder relations of `|J, M⟩`;
- `⟨j₁ m₁ j₂ m₂ | J M⟩ = 0` unless `m₁ + m₂ = M`;
- the Condon–Shortley phase convention `⟨j₁ j₁ j₂ (J - j₁) | J J⟩ > 0`;
- every coupled state is `Σ ⟨j₁ m₁ j₂ m₂ | J M⟩ |j₁ m₁⟩ ⊗ |j₂ m₂⟩`, and the orthogonality
  relation `Σ_{m₁ m₂} ⟨j₁ m₁ j₂ m₂ | J M⟩ ⟨j₁ m₁ j₂ m₂ | J' M'⟩ = δ_{JJ'} δ_{MM'}`;
- the values `⟨j₁ j₁ j₂ j₂ | j₁+j₂, j₁+j₂⟩ = 1`, and for two spins `1/2` the singlet
  `⟨½ ½ ½ -½ | 0 0⟩ = 1/√2`, `⟨½ -½ ½ ½ | 0 0⟩ = -1/√2` and the triplet
  `⟨½ ½ ½ -½ | 1 0⟩ = ⟨½ -½ ½ ½ | 1 0⟩ = 1/√2`.

These properties determine the Clebsch–Gordan coefficients uniquely, so they agree with the
tabulated values. A closed formula (Racah's formula) is not proved here.

## ii. Key results

- `tensorForm`, `tensorForm_tensorF` (contravariance) and `tensorForm_stringVec`.
- `hwNormSq_pos`, `coupledVec`, `tensorForm_coupledVec` (orthonormality),
  `tensorF_coupledVec`, `tensorE_coupledVec_succ` (ladder relations).
- `cgCoefficient`, `cgCoefficient_eq_zero_of_ne`, `cgCoefficient_top_pos`,
  `coupledVec_eq_sum`, `sum_cgCoefficient_mul`.
- `cgCoefficient_stretched`, `cgCoefficient_singlet_up`, `cgCoefficient_singlet_down`,
  `cgCoefficient_triplet_zero_up`, `cgCoefficient_triplet_zero_down`.

## iii. Table of contents

- A. The form on the tensor product
- B. Inner products of the lowering strings
- C. The orthonormal coupled basis
- D. Clebsch–Gordan coefficients
  - D.1. Definition, weight rule and phase
  - D.2. Expansion and orthogonality
  - D.3. Values

## iv. References

- J. J. Sakurai and J. Napolitano, *Modern Quantum Mechanics*, 3rd ed., Cambridge University
  Press (2020), section 3.8.

## A. The form on the tensor product

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open StandardSl2Module

open scoped TensorProduct

variable {m n : ℕ}

variable (m n) in
/-- The contravariant form on `V(m) ⊗ V(n)`: `⟨x ⊗ y, x' ⊗ y'⟩ = ⟨x, x'⟩ ⟨y, y'⟩`. -/
def tensorForm : LinearMap.BilinForm ℝ (StandardSl2Module ℝ m ⊗[ℝ] StandardSl2Module ℝ n) :=
  LinearMap.BilinForm.tmul (invForm ℝ m) (invForm ℝ n)

lemma tensorForm_tmul (x x' : StandardSl2Module ℝ m) (y y' : StandardSl2Module ℝ n) :
    tensorForm m n (x ⊗ₜ y) (x' ⊗ₜ y') = invForm ℝ m x x' * invForm ℝ n y y' := by
  rw [tensorForm, LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul, mul_comm]

/-- Two bilinear forms on `V(m) ⊗ V(n)` agree if they agree on pure tensors. -/
lemma tensorBilin_ext
    {B B' : LinearMap.BilinForm ℝ (StandardSl2Module ℝ m ⊗[ℝ] StandardSl2Module ℝ n)}
    (h : ∀ x y x' y', B (x ⊗ₜ y) (x' ⊗ₜ y') = B' (x ⊗ₜ y) (x' ⊗ₜ y')) : B = B' :=
  TensorProduct.ext' fun x y => TensorProduct.ext' fun x' y' => h x y x' y'

lemma invForm_ρE_apply (x y : StandardSl2Module ℝ n) :
    invForm ℝ n (ρE x) y = invForm ℝ n x (ρF y) :=
  LinearMap.congr_fun (LinearMap.congr_fun invForm_comp_ρE x) y

lemma invForm_ρH_apply (x y : StandardSl2Module ℝ n) :
    invForm ℝ n (ρH x) y = invForm ℝ n x (ρH y) :=
  LinearMap.congr_fun (LinearMap.congr_fun invForm_comp_ρH x) y

/-- The form on the tensor product is symmetric. -/
lemma tensorForm_comm (x y : StandardSl2Module ℝ m ⊗[ℝ] StandardSl2Module ℝ n) :
    tensorForm m n x y = tensorForm m n y x := by
  have h : tensorForm m n = LinearMap.flip (tensorForm m n) := tensorBilin_ext fun x y x' y' => by
    rw [LinearMap.flip_apply, tensorForm_tmul, tensorForm_tmul, invForm_comm x, invForm_comm y]
  rw [h, LinearMap.flip_apply, ← h]

/-- The diagonal raising and lowering operators are adjoint: `⟨E x, y⟩ = ⟨x, F y⟩`. -/
lemma tensorForm_tensorE (x y : StandardSl2Module ℝ m ⊗[ℝ] StandardSl2Module ℝ n) :
    tensorForm m n (tensorE m n x) y = tensorForm m n x (tensorF m n y) := by
  have h : LinearMap.comp (tensorForm m n) (tensorE m n) =
      LinearMap.compl₂ (tensorForm m n) (tensorF m n) :=
    tensorBilin_ext fun x y x' y' => by
      simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, tensorE, tensorF, diagEnd_tmul,
        map_add, LinearMap.add_apply, tensorForm_tmul, invForm_ρE_apply]
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

/-- `⟨F x, y⟩ = ⟨x, E y⟩`. -/
lemma tensorForm_tensorF (x y : StandardSl2Module ℝ m ⊗[ℝ] StandardSl2Module ℝ n) :
    tensorForm m n (tensorF m n x) y = tensorForm m n x (tensorE m n y) := by
  rw [tensorForm_comm, ← tensorForm_tensorE, tensorForm_comm]

/-- The diagonal weight operator is symmetric. -/
lemma tensorForm_tensorH (x y : StandardSl2Module ℝ m ⊗[ℝ] StandardSl2Module ℝ n) :
    tensorForm m n (tensorH m n x) y = tensorForm m n x (tensorH m n y) := by
  have h : LinearMap.comp (tensorForm m n) (tensorH m n) =
      LinearMap.compl₂ (tensorForm m n) (tensorH m n) :=
    tensorBilin_ext fun x y x' y' => by
      simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, tensorH, diagEnd_tmul,
        map_add, LinearMap.add_apply, tensorForm_tmul, invForm_ρH_apply]
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

/-!

## B. Inner products of the lowering strings

-/

/-- Highest-weight vectors of different weight are orthogonal. -/
lemma tensorForm_hwVec_of_ne {k k' : ℕ} (hk : k ≠ k') :
    tensorForm m n (hwVec m n k) (hwVec m n k') = 0 := by
  have h := tensorForm_tensorH (hwVec (K := ℝ) m n k) (hwVec m n k')
  simp only [tensorH_hwVec, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  have hne : ((m : ℝ) + n - 2 * k) - ((m : ℝ) + n - 2 * k') ≠ 0 := by
    intro e
    apply hk
    have : (k : ℝ) = k' := by linarith
    exact_mod_cast this
  have h' : (((m : ℝ) + n - 2 * k) - ((m : ℝ) + n - 2 * k')) *
      tensorForm m n (hwVec m n k) (hwVec m n k') = 0 := by linear_combination h
  exact (mul_eq_zero.mp h').resolve_left hne

lemma stringVec_zero' (k : ℕ) : stringVec (K := ℝ) m n k 0 = hwVec m n k := by
  rw [stringVec, pow_zero, Module.End.one_apply]

/-- The inner products of the lowering strings:
`⟨f^a w_k, f^b w_{k'}⟩ = δ_{kk'} δ_{ab} · normSq (m + n - 2k) a · ⟨w_k, w_k⟩`. -/
lemma tensorForm_stringVec (hmn : 0 < m + n) {k k' : ℕ} (hkm : k ≤ m) (hkn : k ≤ n)
    (hk'm : k' ≤ m) (hk'n : k' ≤ n) (a b : ℕ) :
    tensorForm m n (stringVec m n k a) (stringVec m n k' b) =
      if k = k' ∧ a = b then
        (normSq (m + n - 2 * k) a : ℝ) * tensorForm m n (hwVec m n k) (hwVec m n k)
      else 0 := by
  induction a generalizing b with
  | zero =>
    rcases b with _ | b
    · rw [stringVec_zero', stringVec_zero']
      by_cases hk : k = k'
      · subst hk
        simp [normSq]
      · rw [tensorForm_hwVec_of_ne hk]
        simp [hk]
    · rw [← tensorF_stringVec, tensorForm_comm, tensorForm_tensorF, stringVec_zero',
        tensorE_hwVec hkm hkn, map_zero]
      simp
  | succ a ih =>
    rw [← tensorF_stringVec, tensorForm_tensorF]
    rcases b with _ | b
    · rw [tensorE_stringVec_zero hk'm hk'n, map_zero]
      simp
    · rw [tensorE_stringVec_succ hmn hk'm hk'n, map_smul, smul_eq_mul, ih b]
      by_cases h : k = k' ∧ a = b
      · obtain ⟨rfl, rfl⟩ := h
        simp only [and_self, ite_true, normSq_succ, Nat.cast_mul]
        rcases le_or_gt a (m + n - 2 * k) with ha | ha
        · rw [Nat.cast_sub ha]
          push_cast
          ring
        · have h0 : normSq (m + n - 2 * k) a = 0 := by
            simp [normSq, Nat.descFactorial_eq_zero_iff_lt.mpr ha]
          simp [h0]
      · simp [h]

variable (m n) in
/-- The squared norm `⟨w_k, w_k⟩` of the highest-weight vector `w_k`. -/
def hwNormSq (k : ℕ) : ℝ := tensorForm m n (hwVec m n k) (hwVec m n k)

/-- `⟨w_k, w_k⟩ = Σ_a cgCoeff(a)² · normSq m a · normSq n (k - a)`. -/
lemma hwNormSq_eq {k : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) :
    hwNormSq m n k = ∑ a ∈ Finset.range (k + 1),
      cgCoeff (K := ℝ) m n k a ^ 2 * (normSq m a : ℝ) * (normSq n (k - a) : ℝ) := by
  simp only [hwNormSq, hwVec, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, tensorForm_tmul, invForm_vNat, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hak : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [Finset.sum_eq_single a]
  · simp only [and_self, show a ≤ m by omega, show k - a ≤ n by omega, ite_true]
    ring
  · intro b _ hba
    simp only [mul_eq_zero, ite_eq_right_iff, Nat.cast_eq_zero, and_imp]
    exact Or.inr (Or.inr (Or.inl fun h => absurd h hba))
  · intro h
    exact absurd ha h

lemma cgCoeff_zero (k : ℕ) :
    cgCoeff (K := ℝ) m n k 0 = ((n - k).factorial * m.factorial : ℕ) := by
  simp [cgCoeff]

/-- `⟨w_k, w_k⟩ > 0`. -/
lemma hwNormSq_pos {k : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) : 0 < hwNormSq m n k := by
  rw [hwNormSq_eq hkm hkn]
  refine Finset.sum_pos' (fun a _ => by positivity) ⟨0, by simp, ?_⟩
  rw [cgCoeff_zero, Nat.sub_zero]
  have h1 : (0 : ℝ) < ((n - k).factorial * m.factorial : ℕ) := by positivity
  have h2 : (0 : ℝ) < normSq m 0 := by exact_mod_cast normSq_pos (Nat.zero_le m)
  have h3 : (0 : ℝ) < normSq n k := by exact_mod_cast normSq_pos hkn
  positivity

/-!

## C. The orthonormal coupled basis

-/

variable (m n) in
/-- The normalised coupled state `|J, M⟩` with `J = (m + n)/2 - k`, `M = J - l`. -/
def coupledVec (k l : ℕ) : StandardSl2Module ℝ m ⊗[ℝ] StandardSl2Module ℝ n :=
  (Real.sqrt ((normSq (m + n - 2 * k) l : ℝ) * hwNormSq m n k))⁻¹ • stringVec m n k l

/-- The coupled states are orthonormal. -/
lemma tensorForm_coupledVec (hmn : 0 < m + n) {k k' l l' : ℕ} (hkm : k ≤ m) (hkn : k ≤ n)
    (hk'm : k' ≤ m) (hk'n : k' ≤ n) (hl : l ≤ m + n - 2 * k) :
    tensorForm m n (coupledVec m n k l) (coupledVec m n k' l') =
      if k = k' ∧ l = l' then 1 else 0 := by
  simp only [coupledVec, map_smul, LinearMap.smul_apply, smul_eq_mul,
    tensorForm_stringVec hmn hkm hkn hk'm hk'n]
  by_cases h : k = k' ∧ l = l'
  · obtain ⟨rfl, rfl⟩ := h
    have hpos : 0 < (normSq (m + n - 2 * k) l : ℝ) * hwNormSq m n k :=
      mul_pos (by exact_mod_cast normSq_pos hl) (hwNormSq_pos hkm hkn)
    have hs := Real.mul_self_sqrt hpos.le
    have hs0 := (Real.sqrt_pos.mpr hpos).ne'
    simp only [and_self, ite_true]
    rw [hwNormSq] at hs hs0 ⊢
    field_simp
    linarith
  · simp [h]

lemma sqrt_coupled_succ {k l : ℕ} :
    Real.sqrt ((normSq (m + n - 2 * k) (l + 1) : ℝ) * hwNormSq m n k) =
      Real.sqrt ((normSq (m + n - 2 * k) l : ℝ) * hwNormSq m n k) *
        Real.sqrt (((l : ℝ) + 1) * (((m + n - 2 * k : ℕ) : ℝ) - l)) := by
  rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_mul (Nat.cast_nonneg _),
    sqrt_normSq_succ]
  ring

/-- `J₋ |J, M⟩ = √((J + M)(J - M + 1)) |J, M - 1⟩`. -/
lemma tensorF_coupledVec {k l : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) (hl : l < m + n - 2 * k) :
    tensorF m n (coupledVec m n k l) =
      Real.sqrt (((l : ℝ) + 1) * (((m + n - 2 * k : ℕ) : ℝ) - l)) • coupledVec m n k (l + 1) := by
  have hpos : 0 < (normSq (m + n - 2 * k) l : ℝ) * hwNormSq m n k :=
    mul_pos (by exact_mod_cast normSq_pos hl.le) (hwNormSq_pos hkm hkn)
  have hc : (0 : ℝ) < ((l : ℝ) + 1) * (((m + n - 2 * k : ℕ) : ℝ) - l) := by
    have : (l : ℝ) < ((m + n - 2 * k : ℕ) : ℝ) := by exact_mod_cast hl
    nlinarith
  have hs0 := (Real.sqrt_pos.mpr hpos).ne'
  have hr0 := (Real.sqrt_pos.mpr hc).ne'
  rw [coupledVec, coupledVec, map_smul, tensorF_stringVec, smul_smul, sqrt_coupled_succ]
  congr 1
  field_simp

/-- `J₊ |J, M⟩ = √((J - M)(J + M + 1)) |J, M + 1⟩`. -/
lemma tensorE_coupledVec_succ (hmn : 0 < m + n) {k l : ℕ} (hkm : k ≤ m) (hkn : k ≤ n)
    (hl : l < m + n - 2 * k) :
    tensorE m n (coupledVec m n k (l + 1)) =
      Real.sqrt (((l : ℝ) + 1) * (((m + n - 2 * k : ℕ) : ℝ) - l)) • coupledVec m n k l := by
  have hpos : 0 < (normSq (m + n - 2 * k) l : ℝ) * hwNormSq m n k :=
    mul_pos (by exact_mod_cast normSq_pos hl.le) (hwNormSq_pos hkm hkn)
  have hc : (0 : ℝ) < ((l : ℝ) + 1) * (((m + n - 2 * k : ℕ) : ℝ) - l) := by
    have : (l : ℝ) < ((m + n - 2 * k : ℕ) : ℝ) := by exact_mod_cast hl
    nlinarith
  have hs0 := (Real.sqrt_pos.mpr hpos).ne'
  have hr := Real.mul_self_sqrt hc.le
  have hr0 := (Real.sqrt_pos.mpr hc).ne'
  rw [coupledVec, coupledVec, map_smul, tensorE_stringVec_succ hmn hkm hkn, smul_smul,
    smul_smul, sqrt_coupled_succ]
  congr 1
  field_simp
  linarith

/-!

## D. Clebsch–Gordan coefficients

### D.1. Definition, weight rule and phase

-/

variable (m n) in
/-- The Clebsch–Gordan coefficient `⟨j₁ m₁ j₂ m₂ | J M⟩ = ⟨u_a ⊗ u_b, |J, M⟩⟩` with `j₁ = m/2`,
`m₁ = j₁ - a`, `j₂ = n/2`, `m₂ = j₂ - b`, `J = (m + n)/2 - k` and `M = J - l`. -/
def cgCoefficient (k l a b : ℕ) : ℝ :=
  tensorForm m n (normVec m a ⊗ₜ normVec n b) (coupledVec m n k l)

lemma tensorH_normVec_tmul (a b : ℕ) :
    tensorH m n (normVec m a ⊗ₜ normVec n b) =
      (((m : ℝ) - 2 * a) + ((n : ℝ) - 2 * b)) • (normVec m a ⊗ₜ normVec n b) := by
  rw [tensorH, diagEnd_tmul, ρH_normVec, ρH_normVec, ← TensorProduct.smul_tmul',
    TensorProduct.tmul_smul, ← add_smul]

lemma tensorH_coupledVec (hmn : 0 < m + n) {k : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) (l : ℕ) :
    tensorH m n (coupledVec m n k l) =
      (((m + n - 2 * k : ℕ) : ℝ) - 2 * l) • coupledVec m n k l := by
  rw [coupledVec, map_smul, tensorH_stringVec hmn hkm hkn, smul_comm]

/-- **Weight rule.** `⟨j₁ m₁ j₂ m₂ | J M⟩ = 0` unless `m₁ + m₂ = M`, i.e. `a + b = k + l`. -/
lemma cgCoefficient_eq_zero_of_ne (hmn : 0 < m + n) {k l a b : ℕ} (hkm : k ≤ m) (hkn : k ≤ n)
    (h : a + b ≠ k + l) : cgCoefficient m n k l a b = 0 := by
  have hs := tensorForm_tensorH (normVec m a ⊗ₜ normVec n b) (coupledVec m n k l)
  rw [tensorH_normVec_tmul, tensorH_coupledVec hmn hkm hkn] at hs
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hs
  have hcast : ((m + n - 2 * k : ℕ) : ℝ) = (m : ℝ) + n - 2 * k := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hcast] at hs
  have hne : (((m : ℝ) - 2 * a) + ((n : ℝ) - 2 * b)) - ((m : ℝ) + n - 2 * k - 2 * l) ≠ 0 := by
    intro e
    apply h
    have : (a : ℝ) + b = k + l := by linarith
    exact_mod_cast this
  have h' : ((((m : ℝ) - 2 * a) + ((n : ℝ) - 2 * b)) - ((m : ℝ) + n - 2 * k - 2 * l)) *
      cgCoefficient m n k l a b = 0 := by
    unfold cgCoefficient
    linear_combination hs
  exact (mul_eq_zero.mp h').resolve_left hne

lemma invForm_normVec_vNat {a : ℕ} (ha : a ≤ n) (c : ℕ) :
    invForm ℝ n (normVec n a) (vNat n c) = if a = c then Real.sqrt (normSq n a) else 0 := by
  rw [normVec, map_smul, LinearMap.smul_apply, invForm_vNat, smul_eq_mul]
  by_cases h : a = c
  · have hpos : (0 : ℝ) < normSq n a := by exact_mod_cast normSq_pos ha
    have hs := Real.mul_self_sqrt hpos.le
    have hs0 := (Real.sqrt_pos.mpr hpos).ne'
    subst h
    simp only [true_and, ha, ite_true]
    field_simp
    linarith
  · simp [h]

lemma tensorForm_normVec_hwVec {k a : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) (ha : a ≤ k) :
    tensorForm m n (normVec m a ⊗ₜ normVec n (k - a)) (hwVec m n k) =
      cgCoeff m n k a * Real.sqrt (normSq m a) * Real.sqrt (normSq n (k - a)) := by
  rw [hwVec, map_sum, Finset.sum_eq_single a]
  · rw [map_smul, smul_eq_mul, tensorForm_tmul, invForm_normVec_vNat (by omega),
      invForm_normVec_vNat (by omega)]
    simp only [ite_true]
    ring
  · intro c _ hca
    rw [map_smul, smul_eq_mul, tensorForm_tmul, invForm_normVec_vNat (by omega)]
    simp [Ne.symm hca]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- The coefficients of the top state `|J, J⟩`:
`⟨j₁ m₁ j₂ m₂ | J J⟩ = cgCoeff(a) · √(normSq m a) · √(normSq n (k - a)) / √⟨w_k, w_k⟩`. -/
lemma cgCoefficient_top {k a : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) (ha : a ≤ k) :
    cgCoefficient m n k 0 a (k - a) =
      cgCoeff m n k a * Real.sqrt (normSq m a) * Real.sqrt (normSq n (k - a)) /
        Real.sqrt (hwNormSq m n k) := by
  rw [cgCoefficient, coupledVec, stringVec_zero', map_smul, smul_eq_mul,
    tensorForm_normVec_hwVec hkm hkn ha]
  simp only [normSq, Nat.factorial_zero, Nat.descFactorial_zero, mul_one, Nat.cast_one, one_mul]
  rw [inv_mul_eq_div]

/-- **Condon–Shortley phase convention.** `⟨j₁ j₁ j₂ (J - j₁) | J J⟩ > 0`. -/
lemma cgCoefficient_top_pos {k : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) :
    0 < cgCoefficient m n k 0 0 k := by
  have h := cgCoefficient_top hkm hkn (Nat.zero_le k)
  rw [Nat.sub_zero] at h
  rw [h, cgCoeff_zero]
  have h1 : (0 : ℝ) < ((n - k).factorial * m.factorial : ℕ) := by positivity
  have h2 : (0 : ℝ) < Real.sqrt (normSq m 0) :=
    Real.sqrt_pos.mpr (by exact_mod_cast normSq_pos (Nat.zero_le m))
  have h3 : (0 : ℝ) < Real.sqrt (normSq n k) := Real.sqrt_pos.mpr (by exact_mod_cast normSq_pos hkn)
  have h4 : (0 : ℝ) < Real.sqrt (hwNormSq m n k) := Real.sqrt_pos.mpr (hwNormSq_pos hkm hkn)
  positivity

/-!

### D.2. Expansion and orthogonality

-/

/-- Every vector of `V(n)` is `Σ_a ⟨u_a, x⟩ u_a`. -/
lemma eq_sum_normVec (x : StandardSl2Module ℝ n) :
    x = ∑ a ∈ Finset.range (n + 1), invForm ℝ n (normVec n a) x • normVec n a := by
  have h : (LinearMap.id : Module.End ℝ (StandardSl2Module ℝ n)) =
      ∑ a ∈ Finset.range (n + 1), (invForm ℝ n (normVec n a)).smulRight (normVec n a) :=
    linearMap_ext_vNat fun c => by
      rw [LinearMap.id_apply, LinearMap.sum_apply]
      have hterm : ∀ a ∈ Finset.range (n + 1),
          ((invForm ℝ n (normVec n a)).smulRight (normVec n a)) (vNat n c) =
            if a = c then Real.sqrt (normSq n a) • normVec n a else 0 := fun a ha => by
        rw [LinearMap.smulRight_apply,
          invForm_normVec_vNat (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))]
        split_ifs <;> simp
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
      split_ifs with hc
      · have hc' : c ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
        have hpos : (0 : ℝ) < normSq n c := by exact_mod_cast normSq_pos hc'
        rw [normVec, smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr hpos).ne', one_smul]
      · rw [vNat_of_lt (by simpa using hc)]
  calc x = (LinearMap.id : Module.End ℝ (StandardSl2Module ℝ n)) x := rfl
    _ = _ := by rw [h, LinearMap.sum_apply]; rfl

/-- Every vector of `V(m) ⊗ V(n)` is `Σ_{a b} ⟨u_a ⊗ u_b, x⟩ u_a ⊗ u_b`. -/
lemma eq_sum_normVec_tmul (x : StandardSl2Module ℝ m ⊗[ℝ] StandardSl2Module ℝ n) :
    x = ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (n + 1),
      tensorForm m n (normVec m a ⊗ₜ normVec n b) x • (normVec m a ⊗ₜ normVec n b) := by
  have h : (LinearMap.id : Module.End ℝ (StandardSl2Module ℝ m ⊗[ℝ] StandardSl2Module ℝ n)) =
      ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (n + 1),
        (tensorForm m n (normVec m a ⊗ₜ normVec n b)).smulRight (normVec m a ⊗ₜ normVec n b) :=
    TensorProduct.ext' fun x y => by
      simp only [LinearMap.id_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
        tensorForm_tmul]
      conv_lhs => rw [eq_sum_normVec x, eq_sum_normVec y]
      simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul_smul]
      exact Finset.sum_comm
  calc x = (LinearMap.id : Module.End ℝ (StandardSl2Module ℝ m ⊗[ℝ] StandardSl2Module ℝ n)) x :=
        rfl
    _ = _ := by simp only [h, LinearMap.sum_apply, LinearMap.smulRight_apply]

/-- `|J, M⟩ = Σ_{m₁ m₂} ⟨j₁ m₁ j₂ m₂ | J M⟩ |j₁ m₁⟩ ⊗ |j₂ m₂⟩`. -/
lemma coupledVec_eq_sum (k l : ℕ) :
    coupledVec m n k l = ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (n + 1),
      cgCoefficient m n k l a b • (normVec m a ⊗ₜ normVec n b) :=
  eq_sum_normVec_tmul _

/-- **Orthogonality relation.**
`Σ_{m₁ m₂} ⟨j₁ m₁ j₂ m₂ | J M⟩ ⟨j₁ m₁ j₂ m₂ | J' M'⟩ = δ_{JJ'} δ_{MM'}`. -/
lemma sum_cgCoefficient_mul (hmn : 0 < m + n) {k k' l l' : ℕ} (hkm : k ≤ m) (hkn : k ≤ n)
    (hk'm : k' ≤ m) (hk'n : k' ≤ n) (hl : l ≤ m + n - 2 * k) :
    ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (n + 1),
      cgCoefficient m n k l a b * cgCoefficient m n k' l' a b =
        if k = k' ∧ l = l' then 1 else 0 := by
  rw [← tensorForm_coupledVec hmn hkm hkn hk'm hk'n hl]
  conv_rhs => rw [coupledVec_eq_sum k l]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rfl

/-!

### D.3. Values

-/

lemma hwNormSq_zero : hwNormSq m n 0 = ((n.factorial * m.factorial : ℕ) : ℝ) ^ 2 := by
  rw [hwNormSq_eq (Nat.zero_le m) (Nat.zero_le n)]
  simp [cgCoeff_zero, normSq]

/-- `⟨j₁ j₁ j₂ j₂ | j₁+j₂, j₁+j₂⟩ = 1`. -/
lemma cgCoefficient_stretched : cgCoefficient m n 0 0 0 0 = 1 := by
  have h := cgCoefficient_top (m := m) (n := n) (Nat.zero_le m) (Nat.zero_le n) (le_refl 0)
  rw [Nat.sub_self] at h
  rw [h, hwNormSq_zero, Real.sqrt_sq (by positivity), cgCoeff_zero, Nat.sub_zero]
  have hc : ((n.factorial * m.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [normSq, Nat.factorial_zero, Nat.descFactorial_zero, mul_one, Nat.cast_one,
    Real.sqrt_one]
  exact div_self hc

lemma hwNormSq_one_one : hwNormSq 1 1 1 = 2 := by
  rw [hwNormSq_eq le_rfl le_rfl]
  norm_num [Finset.sum_range_succ, cgCoeff, normSq]

/-- Singlet: `⟨½ ½ ½ -½ | 0 0⟩ = 1/√2`. -/
lemma cgCoefficient_singlet_up : cgCoefficient 1 1 1 0 0 1 = 1 / Real.sqrt 2 := by
  have h := cgCoefficient_top (m := 1) (n := 1) (k := 1) le_rfl le_rfl (Nat.zero_le 1)
  rw [Nat.sub_zero] at h
  rw [h, hwNormSq_one_one]
  norm_num [cgCoeff, normSq]

/-- Singlet: `⟨½ -½ ½ ½ | 0 0⟩ = -1/√2`. -/
lemma cgCoefficient_singlet_down : cgCoefficient 1 1 1 0 1 0 = -1 / Real.sqrt 2 := by
  have h := cgCoefficient_top (m := 1) (n := 1) (k := 1) le_rfl le_rfl le_rfl
  rw [Nat.sub_self] at h
  rw [h, hwNormSq_one_one]
  norm_num [cgCoeff, normSq]

lemma coupledVec_one_one_zero_one :
    coupledVec 1 1 0 1 = (1 / Real.sqrt 2) • tensorF 1 1 (coupledVec 1 1 0 0) := by
  rw [tensorF_coupledVec (Nat.zero_le 1) (Nat.zero_le 1) (by norm_num), smul_smul]
  have h2 : Real.sqrt ((((0 : ℕ) : ℝ) + 1) * (((1 + 1 - 2 * 0 : ℕ) : ℝ) - ((0 : ℕ) : ℝ))) =
      Real.sqrt 2 := by norm_num
  rw [h2, one_div, inv_mul_cancel₀ (by positivity), one_smul]

lemma ρE_normVec_one_zero : (ρE : Module.End ℝ (StandardSl2Module ℝ 1)) (normVec 1 0) = 0 := by
  rw [normVec, map_smul, ρE_vNat_zero, smul_zero]

lemma ρE_normVec_one_one :
    (ρE : Module.End ℝ (StandardSl2Module ℝ 1)) (normVec 1 1) = normVec 1 0 := by
  have h := ρE_normVec_succ (n := 1) (a := 0) (by norm_num)
  norm_num at h
  exact h

/-- Triplet: `⟨½ ½ ½ -½ | 1 0⟩ = 1/√2`. -/
lemma cgCoefficient_triplet_zero_up : cgCoefficient 1 1 0 1 0 1 = 1 / Real.sqrt 2 := by
  rw [cgCoefficient, coupledVec_one_one_zero_one, map_smul, smul_eq_mul, ← tensorForm_tensorE,
    tensorE, diagEnd_tmul, ρE_normVec_one_zero, ρE_normVec_one_one, TensorProduct.zero_tmul,
    zero_add]
  have := cgCoefficient_stretched (m := 1) (n := 1)
  rw [cgCoefficient] at this
  rw [this, mul_one]

/-- Triplet: `⟨½ -½ ½ ½ | 1 0⟩ = 1/√2`. -/
lemma cgCoefficient_triplet_zero_down : cgCoefficient 1 1 0 1 1 0 = 1 / Real.sqrt 2 := by
  rw [cgCoefficient, coupledVec_one_one_zero_one, map_smul, smul_eq_mul, ← tensorForm_tensorE,
    tensorE, diagEnd_tmul, ρE_normVec_one_zero, ρE_normVec_one_one, TensorProduct.tmul_zero,
    add_zero]
  have := cgCoefficient_stretched (m := 1) (n := 1)
  rw [cgCoefficient] at this
  rw [this, mul_one]

end PhyslibAlpha.Sl2
