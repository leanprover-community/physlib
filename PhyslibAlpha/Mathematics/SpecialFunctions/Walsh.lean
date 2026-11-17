/-
Copyright (c) 2026 Brent Yee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brent Yee
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Walsh characters

The Walsh characters on `Fin n → Fin 2` and the orthonormal basis of rescaled Walsh vectors.

## i. Overview

For `x z : Fin n → Fin 2` the Walsh character `walsh x z = ∏ i, (-1) ^ (x i * z i)` is the
additive character `z ↦ (-1) ^ (x ⬝ z)` of `(ZMod 2)ⁿ`. The orthogonality relation
`sum_walsh_mul_walsh` is the explicit form of the orthogonality of characters of a finite
abelian group, which Mathlib states as `AddChar.wInner_cWeight_eq_boole`. We work with the
explicit `Fin 2`-indexed form because `Fin n → Fin 2` is what indexes the computational basis
of `n` qubits. The matrix `Matrix.of walsh`, with entries `(-1) ^ (x ⬝ z)`, is the Sylvester
Hadamard matrix of order `2 ^ n` in the sense of Mathlib's `Matrix.IsHadamard`.

Rescaling by `(√(2 ^ n))⁻¹`, the vectors `z ↦ (√(2 ^ n))⁻¹ * walsh x z` form an orthonormal
basis `walshBasis n` of `EuclideanSpace ℂ (Fin n → Fin 2)`, and Parseval's identity for this
basis is `sum_norm_sq_sum_mul_inv_sqrt_mul_walsh`.

## ii. Key results

- `walshSign` : the sign `(-1) ^ (j * k)` on `Fin 2`.
- `walsh` : the Walsh character on `Fin n → Fin 2`.
- `sum_walsh_mul_walsh` : orthogonality of the Walsh characters.
- `walshBasis` : the orthonormal basis of rescaled Walsh vectors.
- `sum_norm_sq_sum_mul_inv_sqrt_mul_walsh` : Parseval's identity for the rescaled Walsh vectors.

## iii. Table of contents

- A. Signs on `Fin 2`
- B. Walsh characters
- C. The Walsh basis
  - C.1. Rescaled Walsh vectors
  - C.2. The orthonormal basis
  - C.3. Parseval's identity

## iv. References

- M. F. Pusey, J. Barrett and T. Rudolph, *On the reality of the quantum state*,
  Nature Phys. 8, 475–478 (2012), arXiv:1111.3328. [ref: Pusey:2011de]

-/

@[expose] public section

noncomputable section

/-!
## A. Signs on `Fin 2`

-/

/-- The sign `(-1) ^ (j * k)` for `j k : Fin 2`, as a complex number. -/
def walshSign (j k : Fin 2) : ℂ := if j = 1 ∧ k = 1 then -1 else 1

/-- The sign `walshSign 0 k` is `1`. -/
@[simp]
lemma walshSign_zero_left (k : Fin 2) : walshSign 0 k = 1 := by
  simp [walshSign]

/-- The sign `walshSign j 0` is `1`. -/
@[simp]
lemma walshSign_zero_right (j : Fin 2) : walshSign j 0 = 1 := by
  simp [walshSign]

/-- The sign `walshSign 1 1` is `-1`. -/
@[simp]
lemma walshSign_one_one : walshSign 1 1 = -1 := by
  simp [walshSign]

/-- The sign `(-1) ^ (j * k)` is symmetric in `j` and `k`. -/
lemma walshSign_comm (j k : Fin 2) : walshSign j k = walshSign k j := by
  fin_cases j <;> fin_cases k <;> simp

/-- A sign squares to one. -/
lemma walshSign_mul_self (j k : Fin 2) : walshSign j k * walshSign j k = 1 := by
  fin_cases j <;> fin_cases k <;> simp

/-- A sign equals its complex conjugate. -/
lemma conj_walshSign (j k : Fin 2) : starRingEnd ℂ (walshSign j k) = walshSign j k := by
  fin_cases j <;> fin_cases k <;> simp

/-- A sign has unit norm. -/
lemma norm_walshSign (j k : Fin 2) : ‖walshSign j k‖ = 1 := by
  fin_cases j <;> fin_cases k <;> simp

/-- Orthogonality of the signs on `Fin 2`. -/
lemma sum_walshSign_mul_walshSign (a b : Fin 2) :
    ∑ k, walshSign a k * walshSign b k = if a = b then 2 else 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [Fin.sum_univ_two]

/-!
## B. Walsh characters

-/

variable {n : ℕ}

/-- The Walsh character `∏ i, (-1) ^ (x i * z i)` on `Fin n → Fin 2`. -/
def walsh (x z : Fin n → Fin 2) : ℂ := ∏ i, walshSign (x i) (z i)

/-- The Walsh character is the product of the signs of the components. -/
lemma walsh_eq (x z : Fin n → Fin 2) : walsh x z = ∏ i, walshSign (x i) (z i) := rfl

/-- The Walsh character `walsh x z` is symmetric in `x` and `z`. -/
lemma walsh_comm (x z : Fin n → Fin 2) : walsh x z = walsh z x := by
  simp only [walsh_eq, walshSign_comm (x _)]

/-- A Walsh character squares to one. -/
lemma walsh_mul_self (x z : Fin n → Fin 2) : walsh x z * walsh x z = 1 := by
  simp only [walsh_eq, ← Finset.prod_mul_distrib, walshSign_mul_self, Finset.prod_const_one]

/-- A Walsh character equals its complex conjugate. -/
lemma conj_walsh (x z : Fin n → Fin 2) : starRingEnd ℂ (walsh x z) = walsh x z := by
  simp only [walsh_eq, map_prod, conj_walshSign]

/-- A Walsh character has unit norm. -/
lemma norm_walsh (x z : Fin n → Fin 2) : ‖walsh x z‖ = 1 := by
  simp [walsh_eq, norm_walshSign]

/-- Orthogonality of the Walsh characters. -/
lemma sum_walsh_mul_walsh (x y : Fin n → Fin 2) :
    ∑ z, walsh x z * walsh y z = if x = y then 2 ^ n else 0 := by
  simp only [walsh_eq, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum fun i k => walshSign (x i) k * walshSign (y i) k]
  simp only [sum_walshSign_mul_walshSign]
  split_ifs with h
  · subst h
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-!
## C. The Walsh basis

### C.1. Rescaled Walsh vectors

-/

/-- The rescaled Walsh vector `z ↦ (√(2 ^ n))⁻¹ * walsh x z` in
`EuclideanSpace ℂ (Fin n → Fin 2)`. -/
def walshVec (x : Fin n → Fin 2) : EuclideanSpace ℂ (Fin n → Fin 2) :=
  WithLp.toLp 2 fun z => (Real.sqrt (2 ^ n))⁻¹ * walsh x z

/-- The component `z` of `walshVec x` is `(√(2 ^ n))⁻¹ * walsh x z`. -/
@[simp]
lemma walshVec_apply (x z : Fin n → Fin 2) :
    walshVec x z = (Real.sqrt (2 ^ n))⁻¹ * walsh x z := rfl

/-- The rescaled Walsh vectors are orthonormal. -/
lemma orthonormal_walshVec : Orthonormal ℂ (walshVec (n := n)) := by
  rw [orthonormal_iff_ite]
  intro x y
  have hc : (((Real.sqrt (2 ^ n))⁻¹ : ℝ) : ℂ) ^ 2 = ((2 : ℂ) ^ n)⁻¹ := by
    rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by positivity)]
    push_cast
    rfl
  simp only [PiLp.inner_apply, walshVec_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal,
    conj_walsh]
  calc _ = (((Real.sqrt (2 ^ n))⁻¹ : ℝ) : ℂ) ^ 2 * ∑ z, walsh x z * walsh y z := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
    _ = _ := by
        rw [sum_walsh_mul_walsh, hc]
        split_ifs
        · exact inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)
        · exact mul_zero _

/-!
### C.2. The orthonormal basis

-/

/-- The orthonormal basis of `EuclideanSpace ℂ (Fin n → Fin 2)` formed by the rescaled Walsh
vectors `walshVec x`. -/
def walshBasis (n : ℕ) :
    OrthonormalBasis (Fin n → Fin 2) ℂ (EuclideanSpace ℂ (Fin n → Fin 2)) :=
  OrthonormalBasis.mk orthonormal_walshVec
    (orthonormal_walshVec.linearIndependent.span_eq_top_of_card_eq_finrank'
      finrank_euclideanSpace.symm).ge

/-- The vectors of `walshBasis n` are the rescaled Walsh vectors. -/
@[simp]
lemma coe_walshBasis (n : ℕ) : ⇑(walshBasis n) = walshVec :=
  OrthonormalBasis.coe_mk _ _

/-!
### C.3. Parseval's identity

-/

/-- Parseval's identity for the rescaled Walsh vectors. The vector
`x ↦ ∑ z, β z * (√(2 ^ n))⁻¹ * walsh x z` has the same squared norm as `β`. -/
lemma sum_norm_sq_sum_mul_inv_sqrt_mul_walsh (n : ℕ) (β : (Fin n → Fin 2) → ℂ) :
    ∑ x : Fin n → Fin 2, ‖∑ z, β z * ((Real.sqrt (2 ^ n))⁻¹ * walsh x z)‖ ^ 2 =
      ∑ z, ‖β z‖ ^ 2 := by
  have h := (walshBasis n).sum_sq_norm_inner_right (WithLp.toLp 2 β)
  rw [EuclideanSpace.norm_sq_eq] at h
  simp only [coe_walshBasis, PiLp.inner_apply, walshVec_apply, RCLike.inner_apply, map_mul,
    Complex.conj_ofReal, conj_walsh] at h
  simpa only [mul_comm (β _)] using h
