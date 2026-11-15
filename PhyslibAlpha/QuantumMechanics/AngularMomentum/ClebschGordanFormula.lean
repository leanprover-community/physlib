/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.ClebschGordanCoefficients

/-!

# Closed formulas for the Clebsch–Gordan coefficients

The second orthogonality relation, an explicit single-sum formula and Racah's formula for
`⟨j₁ m₁ j₂ m₂ | J M⟩`.

## i. Overview

The coupled states `|J, M⟩` form an orthonormal basis of `V(m) ⊗ V(n)`, so every vector is
`Σ_{J M} ⟨J M | x⟩ |J M⟩`. Applied to product states this gives the second orthogonality relation
`Σ_{J M} ⟨j₁ m₁ j₂ m₂ | J M⟩ ⟨j₁ m₁' j₂ m₂' | J M⟩ = δ_{m₁ m₁'} δ_{m₂ m₂'}`.

For the closed formula, two computations are combined.

- The squared norm of the highest-weight vector `w_k` has the closed form
  `⟨w_k, w_k⟩ = k! m! n! (m - k)! (n - k)! (m + n - k + 1)! / (m + n - 2k + 1)!`.
  It reduces to the factorial identity
  `Σ_a C(k, a) (p + a)! (k + s - a)! · (p + s + 1)! = (p + k + s + 1)! p! s!`, proved by induction
  on `k` with Pascal's rule.
- The lowering operator on `V(m) ⊗ V(n)` is `f ⊗ 1 + 1 ⊗ f` with commuting summands, so the
  binomial theorem gives `f^l (v_a ⊗ v_b) = Σ_i C(l, i) v_{a+i} ⊗ v_{b+l-i}`.

Together with the coefficients of `w_k` from `TensorHighestWeight` this yields, with
`J = (m + n)/2 - k`, `M = J - l`, `m₁ = m/2 - α`, `m₂ = n/2 - β` and `α + β = k + l`, a formula
`⟨j₁ m₁ j₂ m₂ | J M⟩ = S · √(…)` with the single alternating sum
`S = Σ_a (-1)^a C(k, a) C(l, α - a) (n - k + a)! (m - a)!`.

Racah's formula has a different alternating sum. After dividing out factorials both sums become
binomial sums,
`L(k, α, s) = Σ_a (-1)^a C(k, a) C(r + k - a, α - a) C(p + a, s + a)` and
`R(k, α, s) = Σ_z (-1)^z C(k, z) C(r, α - z) C(p, s + z)`,
with lower indices in `ℤ` (`C(n, j) = 0` for `j < 0`). Pascal's rule shows that both satisfy
`X(k + 1, α, s) = X(k, α, s) - X(k, α - 1, s + 1)`, and they agree for `k = 0`, so `L = R`.
This proves Racah's formula.

For `n = 1`, coupling a spin `j₁ = m/2` with a spin `½`, the single sum has at most two terms and
the closed formula gives the four coefficients in square-root form, with `J = j₁ ± ½`.

## ii. Key results

- `eq_sum_coupledVec` and `sum_cgCoefficient_mul_cgCoefficient`: completeness of the coupled basis
  and the second orthogonality relation.
- `sum_choose_mul_factorial` and `hwNormSq_closed`: the closed norm of `w_k`.
- `tensorF_pow_tmul_vNat`: the explicit lowering.
- `cgCoefficient_eq_cgSum` and `cgCoefficient_closed`: the closed single-sum formula.
- `racahL_eq_racahR` and `cgCoefficient_racah`: Racah's formula.
- `cgCoefficient_add_half_up`, `cgCoefficient_add_half_down`, `cgCoefficient_sub_half_up`,
  `cgCoefficient_sub_half_down`: the coefficients for coupling with a spin `½`.

## iii. Table of contents

- A. Completeness and the second orthogonality relation
- B. The norm of the highest-weight vectors
  - B.1. A factorial identity
  - B.2. The closed norm
- C. The lowering strings in the product basis
- D. The closed formula
- E. Racah's formula
  - E.1. Binomial coefficients with an integer lower index
  - E.2. Two binomial sums with the same recursion
  - E.3. Racah's formula
- F. Coupling with a spin ½

## iv. References

- G. Racah, *Theory of complex spectra. II*, Phys. Rev. 62, 438 (1942).
- J. J. Sakurai and J. Napolitano, *Modern Quantum Mechanics*, 3rd ed., Cambridge University
  Press (2020), section 3.8.
- D. A. Varshalovich, A. N. Moskalev, V. K. Khersonskii, *Quantum Theory of Angular Momentum:
  Irreducible Tensors, Spherical Harmonics, Vector Coupling Coefficients, 3nj Symbols*, World
  Scientific (1988), Table 8.1, p. 271.

## A. Completeness and the second orthogonality relation

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open StandardSl2Module

open scoped TensorProduct

variable {m n : ℕ}

/-- `⟨|J, M⟩, f^{l'} w_{k'}⟩ = δ_{kk'} δ_{ll'} √(normSq N l · ⟨w_k, w_k⟩)`. -/
lemma tensorForm_coupledVec_stringVec (hmn : 0 < m + n) {k k' l l' : ℕ} (hkm : k ≤ m)
    (hkn : k ≤ n) (hk'm : k' ≤ m) (hk'n : k' ≤ n) (hl : l ≤ m + n - 2 * k) :
    tensorForm m n (coupledVec m n k l) (stringVec m n k' l') =
      if k = k' ∧ l = l' then
        Real.sqrt ((normSq (m + n - 2 * k) l : ℝ) * hwNormSq m n k)
      else 0 := by
  rw [coupledVec, map_smul, LinearMap.smul_apply, smul_eq_mul,
    tensorForm_stringVec hmn hkm hkn hk'm hk'n]
  by_cases h : k = k' ∧ l = l'
  · obtain ⟨rfl, rfl⟩ := h
    have hpos : 0 < (normSq (m + n - 2 * k) l : ℝ) * hwNormSq m n k :=
      mul_pos (by exact_mod_cast normSq_pos hl) (hwNormSq_pos hkm hkn)
    have hs := Real.mul_self_sqrt hpos.le
    have hs0 := (Real.sqrt_pos.mpr hpos).ne'
    simp only [and_self, ite_true]
    rw [← hwNormSq]
    field_simp
    linarith
  · simp [h]

/-- **Completeness.** Every vector of `V(m) ⊗ V(n)` is `Σ_{J M} ⟨|J, M⟩, x⟩ |J, M⟩`. -/
lemma eq_sum_coupledVec (hmn : 0 < m + n) (x : StandardSl2Module ℝ m ⊗[ℝ] StandardSl2Module ℝ n) :
    x = ∑ k ∈ Finset.range (min m n + 1), ∑ l ∈ Finset.range (m + n - 2 * k + 1),
      tensorForm m n (coupledVec m n k l) x • coupledVec m n k l := by
  have h : (LinearMap.id : Module.End ℝ (StandardSl2Module ℝ m ⊗[ℝ] StandardSl2Module ℝ n)) =
      ∑ k ∈ Finset.range (min m n + 1), ∑ l ∈ Finset.range (m + n - 2 * k + 1),
        (tensorForm m n (coupledVec m n k l)).smulRight (coupledVec m n k l) :=
    (tensorStringBasis (K := ℝ) hmn).ext fun i => by
      have hi1 := i.le_left
      have hi2 := i.le_right
      have hil : (i.2 : ℕ) ≤ m + n - 2 * (i.1 : ℕ) := Nat.lt_succ_iff.mp i.2.isLt
      rw [tensorStringBasis_apply, LinearMap.id_apply, LinearMap.sum_apply,
        Finset.sum_eq_single (i.1 : ℕ)]
      · rw [LinearMap.sum_apply, Finset.sum_eq_single (i.2 : ℕ)]
        · rw [LinearMap.smulRight_apply, tensorForm_coupledVec_stringVec hmn hi1 hi2 hi1 hi2 hil,
            ite_eq_left ⟨rfl, rfl⟩, coupledVec, smul_smul]
          have hpos : 0 < (normSq (m + n - 2 * (i.1 : ℕ)) i.2 : ℝ) * hwNormSq m n i.1 :=
            mul_pos (by exact_mod_cast normSq_pos hil) (hwNormSq_pos hi1 hi2)
          rw [mul_inv_cancel₀ (Real.sqrt_pos.mpr hpos).ne', one_smul]
        · intro l hl hne
          have hl' : l ≤ m + n - 2 * (i.1 : ℕ) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
          rw [LinearMap.smulRight_apply, tensorForm_coupledVec_stringVec hmn hi1 hi2 hi1 hi2 hl',
            ite_eq_right (fun h => hne h.2), zero_smul]
        · intro h
          exact absurd (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hil)) h
      · intro k hk hne
        have hk' : k ≤ min m n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [LinearMap.sum_apply]
        refine Finset.sum_eq_zero fun l hl => ?_
        have hl' : l ≤ m + n - 2 * k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
        rw [LinearMap.smulRight_apply, tensorForm_coupledVec_stringVec hmn (by omega) (by omega)
          hi1 hi2 hl', ite_eq_right (fun h => hne h.1), zero_smul]
      · intro h
        exact absurd (Finset.mem_range.mpr (by have := i.1.isLt; omega)) h
  calc x = (LinearMap.id : Module.End ℝ (StandardSl2Module ℝ m ⊗[ℝ] StandardSl2Module ℝ n)) x :=
        rfl
    _ = _ := by simp only [h, LinearMap.sum_apply, LinearMap.smulRight_apply]

/-- **Second orthogonality relation.**
`Σ_{J M} ⟨j₁ m₁ j₂ m₂ | J M⟩ ⟨j₁ m₁' j₂ m₂' | J M⟩ = δ_{m₁ m₁'} δ_{m₂ m₂'}`. -/
lemma sum_cgCoefficient_mul_cgCoefficient (hmn : 0 < m + n) {a b a' b' : ℕ} (ha : a ≤ m)
    (hb : b ≤ n) (ha' : a' ≤ m) (hb' : b' ≤ n) :
    ∑ k ∈ Finset.range (min m n + 1), ∑ l ∈ Finset.range (m + n - 2 * k + 1),
      cgCoefficient m n k l a b * cgCoefficient m n k l a' b' =
        if a = a' ∧ b = b' then 1 else 0 := by
  have h1 : tensorForm m n (normVec m a ⊗ₜ normVec n b) (normVec m a' ⊗ₜ normVec n b') =
      if a = a' ∧ b = b' then 1 else 0 := by
    rw [tensorForm_tmul, invForm_normVec ha ha', invForm_normVec hb hb']
    split_ifs <;> simp_all
  rw [← h1]
  conv_rhs => rw [eq_sum_coupledVec hmn (normVec m a' ⊗ₜ normVec n b')]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [cgCoefficient, cgCoefficient, tensorForm_comm (coupledVec m n k l)]
  ring

/-!

## B. The norm of the highest-weight vectors

### B.1. A factorial identity

-/

/-- `S(k, p, s) = Σ_{i + j = k} C(k, i) (p + i)! (s + j)!`. -/
def factorialSum (k p s : ℕ) : ℕ :=
  ∑ ij ∈ Finset.antidiagonal k, k.choose ij.1 * ((p + ij.1).factorial * (s + ij.2).factorial)

/-- Pascal's rule for `S`. -/
lemma factorialSum_succ (k p s : ℕ) :
    factorialSum (k + 1) p s = factorialSum k p (s + 1) + factorialSum k (p + 1) s := by
  have h := Finset.sum_antidiagonal_choose_succ_mul (R := ℕ)
    (fun i j => (p + i).factorial * (s + j).factorial) k
  simp only [Nat.cast_id] at h
  rw [factorialSum, h]
  congr 1
  · refine Finset.sum_congr rfl fun ij _ => ?_
    rw [show s + (ij.2 + 1) = s + 1 + ij.2 by ring]
  · refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.mem_antidiagonal] at hij
    rw [← Nat.choose_symm_of_eq_add hij.symm, show p + (ij.1 + 1) = p + 1 + ij.1 by ring]

/-- `S(k, p, s) · (p + s + 1)! = (p + k + s + 1)! p! s!`. -/
lemma factorialSum_mul (k p s : ℕ) :
    factorialSum k p s * (p + s + 1).factorial =
      (p + k + s + 1).factorial * p.factorial * s.factorial := by
  induction k generalizing p s with
  | zero =>
    simp only [factorialSum, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, Nat.choose_self,
      add_zero, one_mul]
    ring
  | succ k ih =>
    have h1 := ih p (s + 1)
    have h2 := ih (p + 1) s
    rw [show p + (s + 1) + 1 = p + s + 1 + 1 by ring, show p + k + (s + 1) + 1 = p + (k + 1) + s + 1
      by ring, Nat.factorial_succ (p + s + 1), Nat.factorial_succ s] at h1
    rw [show p + 1 + s + 1 = p + s + 1 + 1 by ring, show p + 1 + k + s + 1 = p + (k + 1) + s + 1
      by ring, Nat.factorial_succ (p + s + 1), Nat.factorial_succ p] at h2
    refine Nat.eq_of_mul_eq_mul_right (show 0 < p + s + 1 + 1 by omega) ?_
    rw [factorialSum_succ]
    linarith

/-- The factorial identity in the form used for `⟨w_k, w_k⟩`:
`Σ_a C(k, a) (p + a)! (s + k - a)! · (p + s + 1)! = (p + k + s + 1)! p! s!`. -/
lemma sum_choose_mul_factorial (k p s : ℕ) :
    (∑ a ∈ Finset.range (k + 1), k.choose a * ((p + a).factorial * (s + (k - a)).factorial)) *
      (p + s + 1).factorial = (p + k + s + 1).factorial * p.factorial * s.factorial := by
  rw [← factorialSum_mul, factorialSum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-!

### B.2. The closed norm

-/

/-- The numerator `k! m! n! (m + n - k + 1)! (n - k)! (m - k)!` of `⟨w_k, w_k⟩`. -/
def hwNormNum (m n k : ℕ) : ℕ :=
  k.factorial * m.factorial * n.factorial *
    ((m + n - k + 1).factorial * (n - k).factorial * (m - k).factorial)

lemma cgCoeff_sq_mul_normSq {k a : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) (ha : a ≤ k) :
    cgCoeff (K := ℝ) m n k a ^ 2 * (normSq m a : ℝ) * (normSq n (k - a) : ℝ) =
      ((k.choose a * ((n - k + a).factorial * (m - a).factorial) *
        (k.factorial * m.factorial * n.factorial) : ℕ) : ℝ) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial ha
  have h2 := Nat.factorial_mul_descFactorial (show a ≤ m by omega)
  have h3 := Nat.factorial_mul_descFactorial (show k - a ≤ n by omega)
  rw [show n - (k - a) = n - k + a by omega] at h3
  have hN : (k.choose a * (n - k + a).factorial * (m - a).factorial) ^ 2 *
      (a.factorial * m.descFactorial a) * ((k - a).factorial * n.descFactorial (k - a)) =
      k.choose a * ((n - k + a).factorial * (m - a).factorial) *
        (k.factorial * m.factorial * n.factorial) := by
    rw [← h1, ← h2, ← h3]
    ring
  have hs : ((-1 : ℝ) ^ a) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [cgCoeff, mul_pow, hs, one_mul, normSq, normSq]
  exact_mod_cast hN

/-- `⟨w_k, w_k⟩ (m + n - 2k + 1)! = k! m! n! (m + n - k + 1)! (n - k)! (m - k)!`. -/
lemma hwNormSq_mul_factorial {k : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) :
    hwNormSq m n k * ((m + n - 2 * k + 1).factorial : ℝ) = hwNormNum m n k := by
  have hterm : ∑ a ∈ Finset.range (k + 1),
      cgCoeff (K := ℝ) m n k a ^ 2 * (normSq m a : ℝ) * (normSq n (k - a) : ℝ) =
      ∑ a ∈ Finset.range (k + 1), ((k.choose a * ((n - k + a).factorial *
        (m - k + (k - a)).factorial) * (k.factorial * m.factorial * n.factorial) : ℕ) : ℝ) :=
    Finset.sum_congr rfl fun a ha => by
      have hak := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      rw [cgCoeff_sq_mul_normSq hkm hkn hak, show m - a = m - k + (k - a) by omega]
  have hnat := sum_choose_mul_factorial k (n - k) (m - k)
  rw [show n - k + (m - k) + 1 = m + n - 2 * k + 1 by omega,
    show n - k + k + (m - k) + 1 = m + n - k + 1 by omega] at hnat
  have h : (∑ a ∈ Finset.range (k + 1), k.choose a * ((n - k + a).factorial *
      (m - k + (k - a)).factorial)) * (k.factorial * m.factorial * n.factorial) *
      (m + n - 2 * k + 1).factorial = hwNormNum m n k := by
    rw [hwNormNum, ← hnat]
    ring
  rw [hwNormSq_eq hkm hkn, hterm, ← Nat.cast_sum, ← Nat.cast_mul, ← Finset.sum_mul, h]

/-- **The closed norm.**
`⟨w_k, w_k⟩ = k! m! n! (m + n - k + 1)! (n - k)! (m - k)! / (m + n - 2k + 1)!`. -/
lemma hwNormSq_closed {k : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) :
    hwNormSq m n k = hwNormNum m n k / ((m + n - 2 * k + 1).factorial : ℝ) :=
  eq_div_of_mul_eq (by exact_mod_cast (Nat.factorial_pos _).ne') (hwNormSq_mul_factorial hkm hkn)

/-!

## C. The lowering strings in the product basis

-/

lemma ρF_pow_vNat (a l : ℕ) :
    ((ρF : Module.End ℝ (StandardSl2Module ℝ n)) ^ l) (vNat n a) = vNat n (a + l) := by
  induction l with
  | zero => rfl
  | succ l ih => rw [pow_succ', Module.End.mul_apply, ih, ρF_vNat, add_assoc]

/-- The binomial theorem for the lowering operator:
`f^l (v_a ⊗ v_b) = Σ_i C(l, i) v_{a+i} ⊗ v_{b+l-i}`. -/
lemma tensorF_pow_tmul_vNat (a b l : ℕ) :
    (tensorF (K := ℝ) m n ^ l) (vNat m a ⊗ₜ vNat n b) =
      ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) • (vNat m (a + i) ⊗ₜ vNat n (b + (l - i))) := by
  have hc : Commute ((ρF : Module.End ℝ (StandardSl2Module ℝ m)).rTensor (StandardSl2Module ℝ n))
      ((ρF : Module.End ℝ (StandardSl2Module ℝ n)).lTensor (StandardSl2Module ℝ m)) := by
    rw [Commute, SemiconjBy, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  rw [tensorF, diagEnd, hc.add_pow, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply, LinearMap.rTensor_pow,
    LinearMap.lTensor_pow, map_nsmul, map_nsmul, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
    ρF_pow_vNat, ρF_pow_vNat, Nat.cast_smul_eq_nsmul]

/-!

## D. The closed formula

-/

/-- The alternating sum `Σ_{a ≤ min(k, α)} (-1)^a C(k, a) (n - k + a)! (m - a)! C(l, α - a)`. -/
def cgSum (m n k l α : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (k + 1), if a ≤ α then cgCoeff m n k a * (l.choose (α - a) : ℝ) else 0

lemma sum_choose_mul_ite {l a α : ℕ} (X : ℝ) :
    ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * (if α = a + i then X else 0) =
      if a ≤ α then (l.choose (α - a) : ℝ) * X else 0 := by
  by_cases ha : a ≤ α
  · rw [ite_eq_left ha, Finset.sum_eq_single (α - a)]
    · rw [ite_eq_left (by omega)]
    · intro i _ hi
      rw [ite_eq_right (by omega), mul_zero]
    · intro h
      rw [Finset.mem_range, not_lt] at h
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  · rw [ite_eq_right ha]
    exact Finset.sum_eq_zero fun i _ => by rw [ite_eq_right (by omega), mul_zero]

lemma tensorForm_normVec_tmul_vNat {α β a i k l : ℕ} (hα : α ≤ m) (hβ : β ≤ n)
    (h : α + β = k + l) (hak : a ≤ k) (hil : i ≤ l) :
    tensorForm m n (normVec m α ⊗ₜ normVec n β) (vNat m (a + i) ⊗ₜ vNat n (k - a + (l - i))) =
      if α = a + i then Real.sqrt (normSq m α) * Real.sqrt (normSq n β) else 0 := by
  rw [tensorForm_tmul, invForm_normVec_vNat hα, invForm_normVec_vNat hβ]
  by_cases hai : α = a + i
  · rw [ite_eq_left hai, ite_eq_left hai, ite_eq_left (by omega)]
  · rw [ite_eq_right hai, ite_eq_right hai, zero_mul]

/-- `⟨u_α ⊗ u_β, f^l w_k⟩ = cgSum · √(normSq m α) √(normSq n β)` for `α + β = k + l`. -/
lemma tensorForm_normVec_stringVec {k l α β : ℕ} (hα : α ≤ m) (hβ : β ≤ n)
    (h : α + β = k + l) :
    tensorForm m n (normVec m α ⊗ₜ normVec n β) (stringVec m n k l) =
      cgSum m n k l α * Real.sqrt (normSq m α) * Real.sqrt (normSq n β) := by
  rw [stringVec, hwVec, map_sum, map_sum, cgSum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hak : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [map_smul, tensorF_pow_tmul_vNat, map_smul, map_sum, smul_eq_mul]
  have hi : ∀ i ∈ Finset.range (l + 1), tensorForm m n (normVec m α ⊗ₜ normVec n β)
      ((l.choose i : ℝ) • (vNat m (a + i) ⊗ₜ vNat n (k - a + (l - i)))) =
      (l.choose i : ℝ) * (if α = a + i then Real.sqrt (normSq m α) * Real.sqrt (normSq n β)
        else 0) := fun i hi => by
    rw [map_smul, smul_eq_mul, tensorForm_normVec_tmul_vNat hα hβ h hak
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  rw [Finset.sum_congr rfl hi, sum_choose_mul_ite]
  split_ifs <;> ring

/-- The Clebsch–Gordan coefficient as one finite sum, with the norm of `w_k` still unevaluated. -/
lemma cgCoefficient_eq_cgSum {k l α β : ℕ} (hα : α ≤ m) (hβ : β ≤ n) (h : α + β = k + l) :
    cgCoefficient m n k l α β =
      (Real.sqrt ((normSq (m + n - 2 * k) l : ℝ) * hwNormSq m n k))⁻¹ *
        (cgSum m n k l α * Real.sqrt (normSq m α) * Real.sqrt (normSq n β)) := by
  rw [cgCoefficient, coupledVec, map_smul, smul_eq_mul, tensorForm_normVec_stringVec hα hβ h]

/-- **Closed formula for the Clebsch–Gordan coefficients.** For `α + β = k + l`, with
`N = m + n - 2k`,
`⟨j₁ m₁ j₂ m₂ | J M⟩ = cgSum · √(normSq m α · normSq n β · (N + 1)! / (normSq N l · hwNormNum))`.
For `α + β ≠ k + l` the coefficient vanishes by `cgCoefficient_eq_zero_of_ne`. -/
lemma cgCoefficient_closed {k l α β : ℕ} (hkm : k ≤ m) (hkn : k ≤ n)
    (hl : l ≤ m + n - 2 * k) (hα : α ≤ m) (hβ : β ≤ n) (h : α + β = k + l) :
    cgCoefficient m n k l α β = cgSum m n k l α *
      Real.sqrt ((normSq m α : ℝ) * normSq n β * (m + n - 2 * k + 1).factorial /
        ((normSq (m + n - 2 * k) l : ℝ) * hwNormNum m n k)) := by
  have hF : ((m + n - 2 * k + 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hX : (normSq (m + n - 2 * k) l : ℝ) ≠ 0 := by exact_mod_cast (normSq_pos hl).ne'
  have hw : hwNormSq m n k ≠ 0 := (hwNormSq_pos hkm hkn).ne'
  have hA : (0 : ℝ) ≤ normSq m α := Nat.cast_nonneg _
  have hB : (0 : ℝ) ≤ normSq n β := Nat.cast_nonneg _
  have hq : (normSq m α : ℝ) * normSq n β * (m + n - 2 * k + 1).factorial /
      ((normSq (m + n - 2 * k) l : ℝ) * (hwNormSq m n k * (m + n - 2 * k + 1).factorial)) =
      (normSq m α : ℝ) * normSq n β * ((normSq (m + n - 2 * k) l : ℝ) * hwNormSq m n k)⁻¹ := by
    field_simp
  rw [cgCoefficient_eq_cgSum hα hβ h, ← hwNormSq_mul_factorial hkm hkn, hq,
    Real.sqrt_mul (mul_nonneg hA hB), Real.sqrt_mul hA, Real.sqrt_inv]
  ring

/-!

## E. Racah's formula

### E.1. Binomial coefficients with an integer lower index

-/

/-- `C(n, j)` for `j ≥ 0` and `0` for `j < 0`. -/
def zchoose (n : ℕ) (j : ℤ) : ℤ := if 0 ≤ j then (n.choose j.toNat : ℤ) else 0

lemma zchoose_natCast (n t : ℕ) : zchoose n t = n.choose t := by
  simp [zchoose]

lemma zchoose_of_neg {n : ℕ} {j : ℤ} (h : j < 0) : zchoose n j = 0 := by
  rw [zchoose, ite_eq_right (not_le.mpr h)]

/-- Pascal's rule `C(n + 1, j) = C(n, j) + C(n, j - 1)` for all integers `j`. -/
lemma zchoose_succ (n : ℕ) (j : ℤ) : zchoose (n + 1) j = zchoose n j + zchoose n (j - 1) := by
  rcases lt_or_ge j 0 with hj | hj
  · rw [zchoose_of_neg hj, zchoose_of_neg hj, zchoose_of_neg (by omega), add_zero]
  · obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    rcases t with _ | t
    · rw [zchoose_natCast, zchoose_natCast, zchoose_of_neg (by omega)]
      simp
    · rw [zchoose_natCast, zchoose_natCast, show ((t + 1 : ℕ) : ℤ) - 1 = (t : ℤ) by push_cast; ring,
        zchoose_natCast, Nat.choose_succ_succ', Nat.cast_add, add_comm]

/-- Pascal's rule inside a binomial sum. -/
lemma sum_range_choose_succ_mul (f : ℕ → ℤ) (k : ℕ) :
    ∑ a ∈ Finset.range (k + 1 + 1), ((k + 1).choose a : ℤ) * f a =
      ∑ a ∈ Finset.range (k + 1), (k.choose a : ℤ) * f a +
        ∑ a ∈ Finset.range (k + 1), (k.choose a : ℤ) * f (a + 1) := by
  have h : ∑ a ∈ Finset.range (k + 1), (k.choose (a + 1) : ℤ) * f (a + 1) + f 0 =
      ∑ a ∈ Finset.range (k + 1), (k.choose a : ℤ) * f a := by
    have h1 := Finset.sum_range_succ' (fun a => (k.choose a : ℤ) * f a) (k + 1)
    have h2 := Finset.sum_range_succ (fun a => (k.choose a : ℤ) * f a) (k + 1)
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul] at h1
    simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero] at h2
    rw [← h2, h1]
  rw [Finset.sum_range_succ', Nat.choose_zero_right, Nat.cast_one, one_mul, ← h]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib]
  ring

/-!

### E.2. Two binomial sums with the same recursion

-/

/-- `L(k, α, s) = Σ_a (-1)^a C(k, a) C(r + k - a, α - a) C(p + a, s + a)`: the sum `cgSum` after
dividing out factorials. -/
def racahL (r p k : ℕ) (α s : ℤ) : ℤ :=
  ∑ a ∈ Finset.range (k + 1),
    (k.choose a : ℤ) * ((-1) ^ a * zchoose (r + k - a) (α - a) * zchoose (p + a) (s + a))

/-- `R(k, α, s) = Σ_z (-1)^z C(k, z) C(r, α - z) C(p, s + z)`: Racah's sum after dividing out
factorials. -/
def racahR (r p k : ℕ) (α s : ℤ) : ℤ :=
  ∑ z ∈ Finset.range (k + 1), (k.choose z : ℤ) * ((-1) ^ z * zchoose r (α - z) * zchoose p (s + z))

lemma racahL_succ (r p k : ℕ) (α s : ℤ) :
    racahL r p (k + 1) α s = racahL r p k α s - racahL r p k (α - 1) (s + 1) := by
  rw [racahL, sum_range_choose_succ_mul, racahL, racahL, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hak : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [show r + (k + 1) - a = r + k - a + 1 by omega,
    show r + (k + 1) - (a + 1) = r + k - a by omega, show p + (a + 1) = p + a + 1 by ring,
    zchoose_succ, zchoose_succ]
  push_cast
  ring_nf

lemma racahR_succ (r p k : ℕ) (α s : ℤ) :
    racahR r p (k + 1) α s = racahR r p k α s - racahR r p k (α - 1) (s + 1) := by
  rw [racahR, sum_range_choose_succ_mul, racahR, racahR, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  push_cast
  ring_nf

/-- **The transformation.** `L = R`, by induction on `k`: both satisfy
`X(k + 1, α, s) = X(k, α, s) - X(k, α - 1, s + 1)` and agree for `k = 0`. -/
lemma racahL_eq_racahR (r p k : ℕ) (α s : ℤ) : racahL r p k α s = racahR r p k α s := by
  induction k generalizing α s with
  | zero => simp [racahL, racahR]
  | succ k ih => rw [racahL_succ, racahR_succ, ih, ih]

/-!

### E.3. Racah's formula

-/

/-- Racah's alternating sum
`Σ_z (-1)^z / (z! (k - z)! (α - z)! (n - β - z)! (m - k - α + z)! (β - k + z)!)`
over the `z` for which all six arguments are nonnegative. In spin notation the arguments are
`z`, `j₁ + j₂ - J - z`, `j₁ - m₁ - z`, `j₂ + m₂ - z`, `J - j₂ + m₁ + z` and `J - j₁ - m₂ + z`. -/
def racahSum (m n k α β : ℕ) : ℝ :=
  ∑ z ∈ Finset.range (k + 1),
    if z ≤ α ∧ α ≤ m - k + z ∧ k ≤ β + z ∧ β + z ≤ n then
      (-1) ^ z / ((z.factorial * (k - z).factorial * (α - z).factorial * (n - β - z).factorial *
        (m - k + z - α).factorial * (β + z - k).factorial : ℕ) : ℝ)
    else 0

lemma cgSum_eq_racahL {k l α β : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) (hα : α ≤ m) (hβ : β ≤ n)
    (h : α + β = k + l) :
    cgSum m n k l α = (l.factorial : ℝ) * (m - α).factorial * (n - β).factorial *
      (racahL (m - k) (n - k) k α ((l : ℤ) - α) : ℝ) := by
  rw [cgSum, racahL, Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hak : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [show m - k + k - a = m - a by omega]
  by_cases haα : a ≤ α
  · rw [ite_eq_left haα]
    by_cases hal : α - a ≤ l
    · rw [show (α : ℤ) - a = ((α - a : ℕ) : ℤ) by omega,
        show (l : ℤ) - α + a = ((l - (α - a) : ℕ) : ℤ) by omega, zchoose_natCast, zchoose_natCast,
        cgCoeff]
      have h1 : (l.choose (α - a) : ℝ) * (α - a).factorial * (l - (α - a)).factorial =
          l.factorial := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hal
      have h2 : ((m - a).choose (α - a) : ℝ) * (α - a).factorial * (m - α).factorial =
          (m - a).factorial := by
        rw [show m - α = m - a - (α - a) by omega]
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega)
      have h3 : ((n - k + a).choose (l - (α - a)) : ℝ) * (l - (α - a)).factorial *
          (n - β).factorial = (n - k + a).factorial := by
        rw [show n - β = n - k + a - (l - (α - a)) by omega]
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega)
      have hne : ((α - a).factorial : ℝ) * (l - (α - a)).factorial ≠ 0 := by positivity
      refine mul_right_cancel₀ hne ?_
      push_cast
      linear_combination
        ((-1 : ℝ) ^ a * k.choose a * (n - k + a).factorial * (m - a).factorial) * h1 -
        ((-1 : ℝ) ^ a * k.choose a * l.factorial * (n - k + a).choose (l - (α - a)) *
          (l - (α - a)).factorial * (n - β).factorial) * h2 -
        ((-1 : ℝ) ^ a * k.choose a * l.factorial * (m - a).factorial) * h3
    · rw [Nat.choose_eq_zero_of_lt (by omega : l < α - a), Nat.cast_zero, mul_zero,
        zchoose_of_neg (show (l : ℤ) - α + a < 0 by omega)]
      simp
  · rw [ite_eq_right haα, zchoose_of_neg (show (α : ℤ) - a < 0 by omega)]
    simp

lemma racahR_eq_racahSum {k l α β : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) (h : α + β = k + l) :
    (racahR (m - k) (n - k) k α ((l : ℤ) - α) : ℝ) =
      (k.factorial : ℝ) * (m - k).factorial * (n - k).factorial * racahSum m n k α β := by
  rw [racahR, Int.cast_sum, racahSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hzk : z ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hz)
  by_cases hg : z ≤ α ∧ α ≤ m - k + z ∧ k ≤ β + z ∧ β + z ≤ n
  · rw [ite_eq_left hg]
    obtain ⟨g1, g2, g3, g4⟩ := hg
    rw [show (α : ℤ) - z = ((α - z : ℕ) : ℤ) by omega,
      show (l : ℤ) - α + z = ((β + z - k : ℕ) : ℤ) by omega, zchoose_natCast, zchoose_natCast]
    have h1 : (k.choose z : ℝ) * z.factorial * (k - z).factorial = k.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hzk
    have h2 : ((m - k).choose (α - z) : ℝ) * (α - z).factorial * (m - k + z - α).factorial =
        (m - k).factorial := by
      rw [show m - k + z - α = m - k - (α - z) by omega]
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega)
    have h3 : ((n - k).choose (β + z - k) : ℝ) * (β + z - k).factorial * (n - β - z).factorial =
        (n - k).factorial := by
      rw [show n - β - z = n - k - (β + z - k) by omega]
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega)
    have hD : ((z.factorial * (k - z).factorial * (α - z).factorial * (n - β - z).factorial *
        (m - k + z - α).factorial * (β + z - k).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    rw [mul_div_assoc', eq_div_iff hD, ← h1, ← h2, ← h3]
    push_cast
    ring
  · rw [ite_eq_right hg, mul_zero]
    have h0 : zchoose (m - k) ((α : ℤ) - z) = 0 ∨ zchoose (n - k) ((l : ℤ) - α + z) = 0 := by
      by_cases h1 : z ≤ α
      · by_cases h2 : α ≤ m - k + z
        · right
          by_cases h3 : k ≤ β + z
          · rw [show (l : ℤ) - α + z = ((β + z - k : ℕ) : ℤ) by omega, zchoose_natCast,
              Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
          · exact zchoose_of_neg (by omega)
        · left
          rw [show (α : ℤ) - z = ((α - z : ℕ) : ℤ) by omega, zchoose_natCast,
            Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
      · left
        exact zchoose_of_neg (by omega)
    rcases h0 with h0 | h0 <;> simp [h0]

/-- `cgSum = l! (m - α)! (n - β)! · k! (m - k)! (n - k)! · racahSum`. -/
lemma cgSum_eq_racahSum {k l α β : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) (hα : α ≤ m) (hβ : β ≤ n)
    (h : α + β = k + l) :
    cgSum m n k l α = (l.factorial : ℝ) * (m - α).factorial * (n - β).factorial *
      ((k.factorial : ℝ) * (m - k).factorial * (n - k).factorial) * racahSum m n k α β := by
  rw [cgSum_eq_racahL hkm hkn hα hβ h, racahL_eq_racahR, racahR_eq_racahSum hkm hkn h]
  ring

/-- **Racah's formula.** For `α + β = k + l`, with `j₁ = m/2`, `m₁ = j₁ - α`, `j₂ = n/2`,
`m₂ = j₂ - β`, `J = (m + n)/2 - k`, `M = J - l`,
`⟨j₁ m₁ j₂ m₂ | J M⟩ = √((2J + 1) (J + j₁ - j₂)! (J - j₁ + j₂)! (j₁ + j₂ - J)! / (j₁ + j₂ + J + 1)!)
  · √((J + M)! (J - M)! (j₁ - m₁)! (j₁ + m₁)! (j₂ - m₂)! (j₂ + m₂)!) · racahSum`. -/
lemma cgCoefficient_racah {k l α β : ℕ} (hkm : k ≤ m) (hkn : k ≤ n)
    (hl : l ≤ m + n - 2 * k) (hα : α ≤ m) (hβ : β ≤ n) (h : α + β = k + l) :
    cgCoefficient m n k l α β =
      Real.sqrt (((m + n - 2 * k + 1) * (m - k).factorial * (n - k).factorial * k.factorial : ℕ) /
        ((m + n - k + 1).factorial : ℝ)) *
      Real.sqrt (((m + n - 2 * k - l).factorial * l.factorial * α.factorial * (m - α).factorial *
        β.factorial * (n - β).factorial : ℕ) : ℝ) * racahSum m n k α β := by
  have hP : (0 : ℝ) ≤ (l.factorial : ℝ) * (m - α).factorial * (n - β).factorial *
      ((k.factorial : ℝ) * (m - k).factorial * (n - k).factorial) := by positivity
  have hA0 : (m.descFactorial α : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun h0 => by rw [Nat.descFactorial_eq_zero_iff_lt] at h0; omega
  have hB0 : (n.descFactorial β : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun h0 => by rw [Nat.descFactorial_eq_zero_iff_lt] at h0; omega
  have hX0 : ((m + n - 2 * k).descFactorial l : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun h0 => by rw [Nat.descFactorial_eq_zero_iff_lt] at h0; omega
  have key : (l.factorial : ℝ) * (m - α).factorial * (n - β).factorial *
      ((k.factorial : ℝ) * (m - k).factorial * (n - k).factorial) *
      Real.sqrt ((normSq m α : ℝ) * normSq n β * (m + n - 2 * k + 1).factorial /
        ((normSq (m + n - 2 * k) l : ℝ) * hwNormNum m n k)) =
      Real.sqrt (((m + n - 2 * k + 1) * (m - k).factorial * (n - k).factorial * k.factorial : ℕ) /
        ((m + n - k + 1).factorial : ℝ)) *
      Real.sqrt (((m + n - 2 * k - l).factorial * l.factorial * α.factorial * (m - α).factorial *
        β.factorial * (n - β).factorial : ℕ) : ℝ) := by
    rw [← Real.sqrt_sq hP, ← Real.sqrt_mul (sq_nonneg _), ← Real.sqrt_mul' _ (Nat.cast_nonneg _)]
    congr 1
    have hA := Nat.factorial_mul_descFactorial hα
    have hB := Nat.factorial_mul_descFactorial hβ
    have hX := Nat.factorial_mul_descFactorial hl
    simp only [normSq, hwNormNum]
    rw [Nat.factorial_succ (m + n - 2 * k), ← hA, ← hB, ← hX]
    push_cast
    field_simp
  rw [cgCoefficient_closed hkm hkn hl hα hβ h, cgSum_eq_racahSum hkm hkn hα hβ h, ← key]
  ring

/-!

## F. Coupling with a spin ½

-/

/-- `⟨j₁ m₁ ½ ½ | j₁ + ½, M⟩ = √((j₁ + M + ½)/(2j₁ + 1))`: with `j₁ = m/2`, `J = j₁ + ½` (`k = 0`),
`M = J - l` and `m₁ = j₁ - l`, the value is `√((m + 1 - l)/(m + 1))`. -/
lemma cgCoefficient_add_half_up {m l : ℕ} (hl : l ≤ m) :
    cgCoefficient m 1 0 l l 0 = Real.sqrt (((m + 1 - l : ℕ) : ℝ) / (m + 1)) := by
  have hS : cgSum m 1 0 l l = m.factorial := by simp [cgSum, cgCoeff]
  rw [cgCoefficient_closed (Nat.zero_le _) (Nat.zero_le _) (by omega) hl (Nat.zero_le _) (by omega),
    hS, ← Real.sqrt_sq (Nat.cast_nonneg (α := ℝ) m.factorial), ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  have hd : ((m + 1).descFactorial l : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega)).ne'
  simp only [normSq, hwNormNum, Nat.factorial_zero, Nat.descFactorial_zero, Nat.sub_zero,
    Nat.factorial_one]
  push_cast
  field_simp
  have h : (m + 1 - l) * (m + 1).descFactorial l = (m + 1) * m.descFactorial l :=
    Nat.succ_descFactorial m l
  rw [mul_comm ((m.descFactorial l : ℕ) : ℝ), mul_comm (((m + 1).descFactorial l : ℕ) : ℝ)]
  exact_mod_cast h.symm

/-- `⟨j₁ m₁ ½ -½ | j₁ + ½, M⟩ = √((j₁ - M + ½)/(2j₁ + 1))`: with `j₁ = m/2`, `J = j₁ + ½`
(`k = 0`), `M = J - (l + 1)` and `m₁ = j₁ - l`, the value is `√((l + 1)/(m + 1))`. -/
lemma cgCoefficient_add_half_down {m l : ℕ} (hl : l ≤ m) :
    cgCoefficient m 1 0 (l + 1) l 1 = Real.sqrt (((l + 1 : ℕ) : ℝ) / (m + 1)) := by
  have hS : cgSum m 1 0 (l + 1) l = m.factorial * (l + 1) := by simp [cgSum, cgCoeff]
  rw [cgCoefficient_closed (Nat.zero_le _) (Nat.zero_le _) (by omega) hl le_rfl (by omega),
    hS, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ m.factorial * (l + 1)),
    ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  have hd : (m.descFactorial l : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hl).ne'
  simp only [normSq, hwNormNum, Nat.factorial_zero, mul_zero, Nat.sub_zero, Nat.factorial_one,
    Nat.descFactorial_self, one_mul, mul_one]
  rw [Nat.succ_descFactorial_succ, Nat.factorial_succ l]
  push_cast
  field_simp

/-- `⟨j₁ m₁ ½ ½ | j₁ - ½, M⟩ = -√((j₁ - M + ½)/(2j₁ + 1))`: with `j₁ = m/2`, `J = j₁ - ½`
(`k = 1`), `M = J - l` and `m₁ = j₁ - (l + 1)`, the value is `-√((l + 1)/(m + 1))`. -/
lemma cgCoefficient_sub_half_up {m l : ℕ} (hl : l + 1 ≤ m) :
    cgCoefficient m 1 1 l (l + 1) 0 = -Real.sqrt (((l + 1 : ℕ) : ℝ) / (m + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hS : cgSum (m + 1) 1 1 l (l + 1) = -m.factorial := by
    simp [cgSum, cgCoeff, Finset.sum_range_succ]
  rw [cgCoefficient_closed (by omega) le_rfl (by omega) hl (Nat.zero_le _) (by omega), hS,
    neg_mul, neg_inj, ← Real.sqrt_sq (Nat.cast_nonneg (α := ℝ) m.factorial),
    ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  have hd : (m.descFactorial l : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega)).ne'
  simp only [normSq, hwNormNum, Nat.factorial_zero, Nat.descFactorial_zero,
    Nat.succ_descFactorial_succ, Nat.factorial_succ, Nat.sub_self,
    show m + 1 + 1 - 2 * 1 = m by omega, show m + 1 + 1 - 1 + 1 = m + 2 by omega,
    show m + 1 - 1 = m by omega]
  push_cast
  field_simp

/-- `⟨j₁ m₁ ½ -½ | j₁ - ½, M⟩ = √((j₁ + M + ½)/(2j₁ + 1))`: with `j₁ = m/2`, `J = j₁ - ½`
(`k = 1`), `M = J - l` and `m₁ = j₁ - l`, the value is `√((m - l)/(m + 1))`. -/
lemma cgCoefficient_sub_half_down {m l : ℕ} (hl : l + 1 ≤ m) :
    cgCoefficient m 1 1 l l 1 = Real.sqrt (((m - l : ℕ) : ℝ) / (m + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hS : cgSum (m + 1) 1 1 l l = m.factorial * ((m + 1 - l : ℕ) : ℝ) := by
    rcases l with _ | l
    · simp [cgSum, cgCoeff, Nat.factorial_succ]
      ring
    · simp [cgSum, cgCoeff, Finset.sum_range_succ, Nat.factorial_succ]
      rw [Nat.cast_sub (by omega)]
      ring
  rw [cgCoefficient_closed (by omega) le_rfl (by omega) (by omega) le_rfl (by omega), hS,
    ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ m.factorial * ((m + 1 - l : ℕ) : ℝ)),
    ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  have hd : (m.descFactorial l : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega)).ne'
  simp only [normSq, hwNormNum, Nat.factorial_zero, Nat.sub_self,
    show m + 1 + 1 - 2 * 1 = m by omega, show m + 1 + 1 - 1 + 1 = m + 2 by omega,
    show m + 1 - 1 = m by omega]
  have hr : (0 : ℝ) < ((m + 1 - l : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m + 1 - l)
  have hE : ((m + 1).descFactorial l : ℝ) =
      (m + 1) * m.descFactorial l / ((m + 1 - l : ℕ) : ℝ) := by
    rw [eq_div_iff hr.ne', mul_comm]
    exact_mod_cast Nat.succ_descFactorial m l
  simp only [Nat.factorial_one, Nat.descFactorial_self, one_mul, mul_one,
    Nat.factorial_succ (m + 1), Nat.factorial_succ m]
  push_cast
  rw [hE]
  field_simp

end PhyslibAlpha.Sl2
