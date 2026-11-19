/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Trace
public import PhyslibAlpha.Mathematics.MultisetAntidiagonal
public import PhyslibAlpha.SpaceAndTime.SpaceTime.SpaceTimeAlgebra.Basic
/-!
# Matrices over the jet ring

Matrices of jets, their derivatives and Taylor coefficients, and the Euler (radial) transport.

## i. Overview

A gauge transformation near a point is a matrix with entries in `SpaceTimeAlgebra`, the jets at
that point. This file collects what is needed to work with such matrices entrywise.

The central construction is the Euler (radial) transport. The Euler operator
`E = ∑_ρ x_ρ ∂_ρ` multiplies a Taylor coefficient of degree `n` by `n`. Hence a matrix of jets
`W` vanishing at the base point with `E W = A W + W B`, for `A` and `B` vanishing at the base
point, is zero, since each of its coefficients is a multiple of coefficients of lower degree.
The same recursion, run forwards, solves the radial system `E U = R U` with `U = 1` at the base
point. This fundamental solution is unitary when `R` is anti-hermitian and has determinant one
when `R` is traceless, and its Maurer–Cartan matrix `(∂_μ U) U⁻¹` solves a linear radial system.
This is how a Lie algebra jet is integrated radially into a gauge jet, in
`GlobalGaugeGroup.exists_sum_X_smul_maurerCartan_eq`.

The remaining sections give the Leibniz rule for the Taylor coefficients of a product of
matrices of jets, the derivatives of conjugates and inverses in terms of Maurer–Cartan
matrices, and the invertible matrices of jets.

## ii. Key results

- `SpaceTimeAlgebra.matrix_eq_zero_of_euler_eq_mul_add_mul` : the vanishing principle for the
  Euler operator.
- `SpaceTimeAlgebra.exists_matrix_eulerTransport` : the Euler transport of a matrix of jets
  vanishing at the base point.
- `SpaceTimeAlgebra.eulerTransport_mul_star`, `SpaceTimeAlgebra.eulerTransport_det` : the Euler
  transport of an anti-hermitian, traceless matrix is unitary of determinant one.
- `SpaceTimeAlgebra.euler_map_pderiv_mul_inv_of_eulerTransport` : the radial system solved by
  the Maurer–Cartan matrix of an Euler transport.
- `SpaceTimeAlgebra.map_coeff_mul` : the Taylor coefficients of a product of matrices of jets.
- `SpaceTimeAlgebra.map_pderiv_conj_of_mul_eq_one` : the derivative of the conjugate of a
  matrix of jets by an invertible one, in terms of its Maurer–Cartan matrix.
- `SpaceTimeAlgebra.unitsEval`, `SpaceTimeAlgebra.unitsOfConstant` : evaluation at the base
  point and the inclusion of constants, for invertible matrices.

## iii. Table of contents

- A. The Euler operator and the Euler transport
- B. The Euler vanishing principle by degree on matrices
- C. Unitarity, determinant and Maurer–Cartan matrix of the Euler transport
- D. The Leibniz rule at the base point for matrices of power series
- E. Conjugation and derivatives of matrices of jets
- F. Invertible matrices of jets

## iv. References

* None.

-/

@[expose] public section

namespace SpaceTimeAlgebra

open MvPowerSeries

/-!

## A. The Euler operator and the Euler transport

-/

/-- Entrywise evaluation at the base point commutes with the conjugate transpose. -/
lemma mapMatrix_constantCoeff_star {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n SpaceTimeAlgebra) :
    (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix (star A) =
      star ((constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A) := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.star_apply]

/-- The Euler operator on matrices of jets acts entrywise on Taylor coefficients as
  multiplication by the total degree. -/
lemma coeff_sum_X_smul_map_pderiv {κ : Type}
    (M : Matrix κ κ SpaceTimeAlgebra) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) (i j : κ) :
    coeff p ((∑ ρ, (X ρ : SpaceTimeAlgebra) • M.map (pderiv ρ)) i j) =
      ((Finsupp.degree p : ℕ) : ℂ) * coeff p (M i j) := by
  rw [show (∑ ρ, (X ρ : SpaceTimeAlgebra) • M.map (pderiv ρ)) i j
      = ∑ ρ, (X ρ : SpaceTimeAlgebra) • pderiv ρ (M i j) from by
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun ρ _ => rfl]
  exact coeff_sum_X_smul_pderiv (M i j) p

/-- Multiplying on the left by a matrix of jets vanishing at the base point raises degrees, so
  the Taylor coefficient of `R M` in degree `|p|` only depends on the coefficients of `M` of
  lower degree. -/
lemma coeff_mul_apply_congr_left {κ : Type} [Fintype κ] {R : Matrix κ κ SpaceTimeAlgebra}
    (hR0 : ∀ i j, constantCoeff (R i j) = 0) (M N : Matrix κ κ SpaceTimeAlgebra)
    (p : (Fin 1 ⊕ Fin 3) →₀ ℕ)
    (h : ∀ (i j : κ) (q : (Fin 1 ⊕ Fin 3) →₀ ℕ), Finsupp.degree q < Finsupp.degree p →
      coeff q (M i j) = coeff q (N i j)) (i j : κ) :
    coeff p ((R * M) i j) = coeff p ((R * N) i j) := by
  simp only [Matrix.mul_apply, map_sum, coeff_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun q hq => ?_
  rcases eq_or_ne q.1 0 with h1 | h1
  · rw [h1, coeff_zero_eq_constantCoeff, hR0, zero_mul, zero_mul]
  · have h4 : Finsupp.degree q.1 + Finsupp.degree q.2 = Finsupp.degree p := by
      rw [← map_add, Finset.mem_antidiagonal.mp hq]
    have h3 := Nat.pos_of_ne_zero fun hc => h1 ((Finsupp.degree_eq_zero_iff _).mp hc)
    rw [h _ _ _ (by omega)]

/-- Multiplying on the right by a matrix of jets vanishing at the base point raises degrees.
  The transpose of `coeff_mul_apply_congr_left`. -/
lemma coeff_mul_apply_congr_right {κ : Type} [Fintype κ] {B : Matrix κ κ SpaceTimeAlgebra}
    (hB0 : ∀ i j, constantCoeff (B i j) = 0) (M N : Matrix κ κ SpaceTimeAlgebra)
    (p : (Fin 1 ⊕ Fin 3) →₀ ℕ)
    (h : ∀ (i j : κ) (q : (Fin 1 ⊕ Fin 3) →₀ ℕ), Finsupp.degree q < Finsupp.degree p →
      coeff q (M i j) = coeff q (N i j)) (i j : κ) :
    coeff p ((M * B) i j) = coeff p ((N * B) i j) := by
  simpa only [← Matrix.transpose_mul, Matrix.transpose_apply] using
    coeff_mul_apply_congr_left (R := B.transpose) (fun i j => hB0 j i) M.transpose N.transpose p
      (fun i j q hq => h j i q hq) j i

/-- The vanishing principle for the Euler operator. A matrix of jets vanishing at the
  base point and satisfying `E W = A W + W B` with `A`, `B` vanishing at the base point
  is zero. Each Taylor coefficient of `W` is a multiple of coefficients of strictly
  smaller degree, so all vanish by strong induction on the degree. -/
lemma matrix_eq_zero_of_euler_eq_mul_add_mul {κ : Type} [Fintype κ]
    {W : Matrix κ κ SpaceTimeAlgebra} (A B : Matrix κ κ SpaceTimeAlgebra)
    (hA : ∀ i j, constantCoeff (A i j) = 0) (hB : ∀ i j, constantCoeff (B i j) = 0)
    (h0 : ∀ i j, constantCoeff (W i j) = 0)
    (hW : ∑ ρ, (X ρ : SpaceTimeAlgebra) • W.map (pderiv ρ) = A * W + W * B) :
    W = 0 := by
  classical
  -- The right-hand side in degree `|p|` only sees the coefficients of `W` of lower degree.
  have hlow : ∀ p : (Fin 1 ⊕ Fin 3) →₀ ℕ,
      (∀ (i : κ) (j : κ) (q : (Fin 1 ⊕ Fin 3) →₀ ℕ),
        Finsupp.degree q < Finsupp.degree p → coeff q (W i j) = 0) →
      ∀ i j, coeff p ((A * W + W * B) i j) = 0 := by
    intro p hp i j
    rw [Matrix.add_apply, map_add,
      coeff_mul_apply_congr_left hA W 0 p (fun i j q hq => by simpa using hp i j q hq) i j,
      coeff_mul_apply_congr_right hB W 0 p (fun i j q hq => by simpa using hp i j q hq) i j]
    simp
  have hm : ∀ (n : ℕ) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ), Finsupp.degree p = n →
      ∀ i j, coeff p (W i j) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro p hp i j
      rcases Nat.eq_zero_or_pos n with hn | hn
      · have hp0 : p = 0 := (Finsupp.degree_eq_zero_iff _).mp (by omega)
        rw [hp0, coeff_zero_eq_constantCoeff]
        exact h0 i j
      · have h : coeff p ((∑ ρ, (X ρ : SpaceTimeAlgebra) • W.map (pderiv ρ)) i j) =
            coeff p ((A * W + W * B) i j) := congrArg (fun M => coeff p (M i j)) hW
        rw [coeff_sum_X_smul_map_pderiv,
          hlow p (fun i' j' q hq => ih (Finsupp.degree q) (by omega) q rfl i' j') i j] at h
        have hne : ((Finsupp.degree p : ℕ) : ℂ) ≠ 0 := by
          rw [hp]
          exact_mod_cast hn.ne'
        exact (mul_eq_zero.mp h).resolve_left hne
  ext i j : 1
  ext p
  rw [hm (Finsupp.degree p) p rfl i j]
  simp

/-- One step of the Euler recursion for the radial system `E U = R U`. It is the identity
  plus `R M` with each Taylor coefficient of degree `n > 0` divided by `n`, and the Euler
  transport of `R` is its fixed point, reached degree by degree. -/
noncomputable def eulerStep {κ : Type} [Fintype κ] [DecidableEq κ]
    (R M : Matrix κ κ SpaceTimeAlgebra) : Matrix κ κ SpaceTimeAlgebra :=
  1 + (R * M).map fun f =>
    show SpaceTimeAlgebra from fun m => if m = 0 then 0 else ((Finsupp.degree m : ℕ) : ℂ)⁻¹ * f m

/-- The Taylor coefficients of one step of the Euler recursion. -/
lemma coeff_eulerStep_apply {κ : Type} [Fintype κ] [DecidableEq κ]
    (R M : Matrix κ κ SpaceTimeAlgebra) (i j : κ) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    coeff p (eulerStep R M i j) = coeff p ((1 : Matrix κ κ SpaceTimeAlgebra) i j) +
      if p = 0 then 0 else ((Finsupp.degree p : ℕ) : ℂ)⁻¹ * coeff p ((R * M) i j) := by
  simp only [eulerStep, Matrix.add_apply, map_add]
  rfl

/-- The Euler (radial) transport of a jet matrix `R` vanishing at the base point,
  a fundamental solution of the radial system `E U = R U` based at the identity,
  built order-by-order by the Euler recursion. -/
lemma exists_matrix_eulerTransport {κ : Type} [Fintype κ] [DecidableEq κ]
    (R : Matrix κ κ SpaceTimeAlgebra) (hR0 : ∀ i j, constantCoeff (R i j) = 0) :
    ∃ U : Matrix κ κ SpaceTimeAlgebra, (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix U = 1 ∧
      ∑ ρ, (X ρ : SpaceTimeAlgebra) • U.map (pderiv ρ) = R * U := by
  classical
  set U : Matrix κ κ SpaceTimeAlgebra :=
    Matrix.of fun i j => show SpaceTimeAlgebra from fun m =>
        ((eulerStep R)^[Finsupp.degree m + 1] 1) i j m
  have hUco : ∀ (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) i j,
      coeff p (U i j) = coeff p (((eulerStep R)^[Finsupp.degree p + 1] 1) i j) :=
    fun _ _ _ => rfl
  -- The iterates of the recursion stabilise in each degree, at the value `eulerStep R U`.
  have hmain : ∀ (n : ℕ) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ), Finsupp.degree p = n → ∀ k, n < k →
      ∀ i j, coeff p (((eulerStep R)^[k] 1) i j) = coeff p ((eulerStep R U) i j) := fun n => by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro p hp k hk i j
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [Function.iterate_succ_apply', coeff_eulerStep_apply, coeff_eulerStep_apply]
      rcases eq_or_ne p 0 with h0 | h0
      · rw [ite_eq_left h0, ite_eq_left h0]
      · rw [ite_eq_right h0, ite_eq_right h0,
          coeff_mul_apply_congr_left hR0 _ U _ (fun i' j' q hq => ?_) i j]
        rw [hUco, ih (Finsupp.degree q) (by omega) q rfl k (by omega) i' j',
          ih (Finsupp.degree q) (by omega) q rfl (Finsupp.degree q + 1) (by omega) i' j']
  have hkey := fun (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) (i j : κ) =>
    (hUco p i j).trans (hmain _ p rfl _ (Nat.lt_succ_self _) i j)
  have hUone : (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix U = 1 := by
    ext i j
    simpa [coeff_eulerStep_apply, Matrix.one_apply, apply_ite, coeff_one] using hkey 0 i j
  refine ⟨U, hUone, ?_⟩
  ext i j : 1
  ext p
  rw [coeff_sum_X_smul_map_pderiv]
  rcases eq_or_ne p 0 with rfl | h0
  · rw [show ((Finsupp.degree (0 : (Fin 1 ⊕ Fin 3) →₀ ℕ) : ℕ) : ℂ) = 0 by simp, zero_mul]
    rw [Matrix.mul_apply, map_sum]
    exact (Finset.sum_eq_zero fun k _ => by
      rw [coeff_zero_eq_constantCoeff, map_mul, hR0, zero_mul]).symm
  · rw [hkey p i j, coeff_eulerStep_apply,
      show coeff p ((1 : Matrix κ κ SpaceTimeAlgebra) i j) = 0 from by
        simp [Matrix.one_apply, apply_ite, coeff_one, h0], zero_add, ite_eq_right h0, ← mul_assoc,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr fun hc => h0 ((Finsupp.degree_eq_zero_iff p).mp hc)),
      one_mul]

/-- The formal derivative `∂_μ` and the Euler operator `E` on matrices of jets commute up to
  `∂_μ` itself, `∂_μ (E M) = E (∂_μ M) + ∂_μ M`, since `∂_μ x_ρ = δ_{μρ}`. -/
lemma map_pderiv_sum_X_smul_map_pderiv {κ : Type} (μ : Fin 1 ⊕ Fin 3)
    (M : Matrix κ κ SpaceTimeAlgebra) :
    (∑ ρ, (X ρ : SpaceTimeAlgebra) • M.map (pderiv ρ)).map (pderiv μ) =
      ∑ ρ, (X ρ : SpaceTimeAlgebra) • (M.map (pderiv μ)).map (pderiv ρ) + M.map (pderiv μ) := by
  classical
  ext i j : 1
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, map_sum, Derivation.leibniz, pderiv_X, Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun ρ _ => by rw [SpaceTimeAlgebra.pderiv_comm]
  · simp [Pi.single_apply]

/-!

## B. The Euler vanishing principle by degree on matrices

-/

/-- The matrix form of `coeff_eq_zero_of_pderiv_eq_mul`. The entries of a matrix of power
  series satisfying `∂_ρ A = X_ρ A`, with the `X_ρ` vanishing below degree `n`, have no
  coefficients in nonzero degree up to `n`. -/
lemma coeff_entry_eq_zero_of_map_pderiv_eq_mul {κ : Type} [Fintype κ] {n : ℕ}
    {A : Matrix κ κ SpaceTimeAlgebra} {X : (Fin 1 ⊕ Fin 3) → Matrix κ κ SpaceTimeAlgebra}
    (hd : ∀ ρ, A.map (pderiv ρ) = X ρ * A)
    (hX : ∀ (ρ : Fin 1 ⊕ Fin 3) (q : (Fin 1 ⊕ Fin 3) →₀ ℕ), Finsupp.degree q < n →
      ∀ i j, coeff q (X ρ i j) = 0)
    (i j : κ) {p : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hp : p ≠ 0) (hpn : Finsupp.degree p ≤ n) :
    coeff p (A i j) = 0 := by
  refine coeff_eq_zero_of_coeff_pderiv_eq_zero (fun ρ q hq => ?_) hp hpn
  have h1 : pderiv ρ (A i j) = (X ρ * A) i j := by rw [← hd ρ, Matrix.map_apply]
  rw [h1, Matrix.mul_apply, map_sum]
  exact Finset.sum_eq_zero fun k _ => coeff_mul_eq_zero_of_lt (fun q' hq' => hX ρ q' hq' i k) _ hq

/-- A matrix of power series with identity value and no coefficients in nonzero degree up
  to `n` truncates to the identity. -/
lemma matrix_map_truncation_eq_one {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ}
    {A : Matrix κ κ SpaceTimeAlgebra}
        (h0 : (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A = 1)
    (hA : ∀ (i j : κ) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ), p ≠ 0 → Finsupp.degree p ≤ n →
      coeff p (A i j) = 0) :
    A.map (SpaceTimeAlgebra.truncation n) = (1 : Matrix κ κ SpaceTimeAlgebra).map
        (SpaceTimeAlgebra.truncation n) := by
  ext i j : 1
  simp only [Matrix.map_apply]
  ext m
  by_cases hm : Finsupp.degree m ≤ n
  · rw [SpaceTimeAlgebra.coeff_truncation_of_le hm, SpaceTimeAlgebra.coeff_truncation_of_le hm]
    rcases eq_or_ne m 0 with rfl | hm0
    · have h3 := congrArg (fun N => N i j) h0
      simpa [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply,
        apply_ite constantCoeff, coeff_zero_eq_constantCoeff] using h3
    · rw [hA i j m hm0 hm]
      rcases eq_or_ne i j with rfl | hij
      · rw [Matrix.one_apply_eq, coeff_one, ite_eq_right hm0]
      · rw [Matrix.one_apply_ne hij, map_zero]
  · rw [SpaceTimeAlgebra.coeff_truncation_of_gt (not_le.mp hm),
      SpaceTimeAlgebra.coeff_truncation_of_gt (not_le.mp hm)]

/-!

## C. Unitarity, determinant and Maurer–Cartan matrix of the Euler transport

-/

/-- The entrywise Leibniz rule for matrix products of jets. -/
lemma matrix_map_pderiv_mul {κ : Type} [Fintype κ] (ρ : Fin 1 ⊕ Fin 3)
    (M N : Matrix κ κ SpaceTimeAlgebra) :
    (M * N).map (pderiv ρ) = M.map (pderiv ρ) * N + M * N.map (pderiv ρ) := by
  ext i j : 1
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
    Derivation.leibniz, smul_eq_mul]
  exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib

/-- The Euler operator on matrices of jets is a derivation. -/
lemma sum_X_smul_map_pderiv_mul {κ : Type} [Fintype κ]
    (M N : Matrix κ κ SpaceTimeAlgebra) :
    ∑ ρ, (X ρ : SpaceTimeAlgebra) • (M * N).map (pderiv ρ) =
      (∑ ρ, (X ρ : SpaceTimeAlgebra) • M.map (pderiv ρ)) * N +
        M * ∑ ρ, (X ρ : SpaceTimeAlgebra) • N.map (pderiv ρ) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [matrix_map_pderiv_mul, smul_add, Matrix.smul_mul, Matrix.mul_smul]

/-- The Euler operator commutes with the conjugate transpose. -/
lemma sum_X_smul_map_pderiv_star {κ : Type}
    (M : Matrix κ κ SpaceTimeAlgebra) :
    ∑ ρ, (X ρ : SpaceTimeAlgebra) • (star M).map (pderiv ρ) =
      star (∑ ρ, (X ρ : SpaceTimeAlgebra) • M.map (pderiv ρ)) := by
  ext i j : 1
  simp only [Matrix.sum_apply, Matrix.star_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, star_sum, star_mul', star_X, ← SpaceTimeAlgebra.pderiv_star]

/-- The Euler operator kills the identity matrix. -/
lemma sum_X_smul_map_pderiv_one {κ : Type} [DecidableEq κ] :
    ∑ ρ, (X ρ : SpaceTimeAlgebra) • (1 : Matrix κ κ SpaceTimeAlgebra).map (pderiv ρ) = 0 := by
  refine Finset.sum_eq_zero fun ρ _ => ?_
  rw [show (1 : Matrix κ κ SpaceTimeAlgebra).map (pderiv ρ) = 0 from Matrix.ext fun i j => by
    simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ρ)], smul_zero]

/-- A fundamental solution of the radial system `E U = R U` based at the identity is
  unitary when `R` is anti-hermitian. `U U† − 1` vanishes at the base point and
  satisfies a homogeneous linear radial system, so it vanishes identically. -/
lemma eulerTransport_mul_star {κ : Type} [Fintype κ] [DecidableEq κ]
    {R U : Matrix κ κ SpaceTimeAlgebra} (hRstar : star R = -R)
    (hR0 : ∀ i j, constantCoeff (R i j) = 0)
    (hU0 : (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix U = 1)
    (hEU : ∑ ρ, (X ρ : SpaceTimeAlgebra) • U.map (pderiv ρ) = R * U) :
    U * star U = 1 := by
  have hEstar : ∑ ρ, (X ρ : SpaceTimeAlgebra) • (star U).map (pderiv ρ) = -(star U * R) := by
    rw [sum_X_smul_map_pderiv_star, hEU, star_mul, hRstar, Matrix.mul_neg]
  have hW0 : (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix (U * star U - 1) = 0 := by
    rw [map_sub, map_mul, mapMatrix_constantCoeff_star, hU0, star_one,
      mul_one, map_one, sub_self]
  have h0 : ∀ i j, constantCoeff ((U * star U - 1) i j) = 0 := fun i j => by
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using congrArg (fun M => M i j) hW0
  have hB : ∀ i j, constantCoeff ((-R) i j) = 0 := fun i j => by
    simp [hR0 i j]
  have hEW : ∑ ρ, (X ρ : SpaceTimeAlgebra) • (U * star U - 1).map (pderiv ρ) =
      R * (U * star U - 1) + (U * star U - 1) * (-R) := by
    have hsub : ∀ ρ : Fin 1 ⊕ Fin 3, (U * star U - 1).map (pderiv ρ) =
        (U * star U).map (pderiv ρ) - (1 : Matrix κ κ SpaceTimeAlgebra).map (pderiv ρ) :=
      fun ρ => Matrix.ext fun i j => by simp [Matrix.map_apply]
    simp only [hsub, smul_sub, Finset.sum_sub_distrib]
    rw [sum_X_smul_map_pderiv_mul, hEU, hEstar, sum_X_smul_map_pderiv_one, sub_zero]
    noncomm_ring
  exact sub_eq_zero.mp (matrix_eq_zero_of_euler_eq_mul_add_mul R (-R) hR0 hB h0 hEW)

/-- The radial Maurer–Cartan component of a unitary fundamental solution of the radial
  system `E V = −i P V` is `P`, `∑_μ x_μ · i (∂_μ V) V† = P`. -/
lemma sum_X_smul_mcMatrix_of_eulerTransport {κ : Type} [Fintype κ] [DecidableEq κ]
    {P V : Matrix κ κ SpaceTimeAlgebra} (hVu : V * star V = 1)
    (hEV : ∑ μ, (X μ : SpaceTimeAlgebra) • V.map (pderiv μ) = ((-Complex.I) • P) * V) :
    ∑ μ, (X μ : SpaceTimeAlgebra) • (Complex.I • (V.map (pderiv μ) * star V)) = P := by
  calc ∑ μ, (X μ : SpaceTimeAlgebra) • (Complex.I • (V.map (pderiv μ) * star V))
      = Complex.I • ((∑ μ, (X μ : SpaceTimeAlgebra) • V.map (pderiv μ)) * star V) := by
        rw [Finset.sum_mul, Finset.smul_sum]
        exact Finset.sum_congr rfl fun μ _ => by
          rw [Matrix.smul_mul, smul_comm Complex.I]
    _ = P := by
        rw [hEV, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc, hVu, mul_one, smul_smul]
        simp

/-- The radial component of the Maurer–Cartan matrix of an invertible solution `V` of the
  radial system `E V = R V` is `R`, `∑_μ x_μ (∂_μ V) V⁻¹ = R`. -/
lemma sum_X_smul_map_pderiv_mul_inv_of_eulerTransport {κ : Type} [Fintype κ] [DecidableEq κ]
    {R V W : Matrix κ κ SpaceTimeAlgebra} (hVW : V * W = 1)
    (hEV : ∑ μ, (X μ : SpaceTimeAlgebra) • V.map (pderiv μ) = R * V) :
    ∑ μ, (X μ : SpaceTimeAlgebra) • (V.map (pderiv μ) * W) = R := by
  simp only [← Matrix.smul_mul]
  rw [← Finset.sum_mul, hEV, Matrix.mul_assoc, hVW, Matrix.mul_one]

/-- The Maurer–Cartan matrix `ω = (∂_μ V) V⁻¹` of an invertible solution `V` of the radial
  system `E V = R V` solves the linear radial system `E ω + ω = ∂_μ R + R ω − ω R`. This is
  `∂_μ` of the radial system, with `∂_μ E = E ∂_μ + ∂_μ` and `E V⁻¹ = −V⁻¹ R`. -/
lemma euler_map_pderiv_mul_inv_of_eulerTransport {κ : Type} [Fintype κ] [DecidableEq κ]
    (μ : Fin 1 ⊕ Fin 3) {R V W : Matrix κ κ SpaceTimeAlgebra} (hVW : V * W = 1)
    (hWV : W * V = 1)
    (hEV : ∑ ρ, (X ρ : SpaceTimeAlgebra) • V.map (pderiv ρ) = R * V) :
    ∑ ρ, (X ρ : SpaceTimeAlgebra) • (V.map (pderiv μ) * W).map (pderiv ρ) +
        V.map (pderiv μ) * W =
      R.map (pderiv μ) + (R * (V.map (pderiv μ) * W) - V.map (pderiv μ) * W * R) := by
  -- The Euler operator on `V⁻¹`, from `E (V V⁻¹) = 0`.
  have hEW : ∑ ρ, (X ρ : SpaceTimeAlgebra) • W.map (pderiv ρ) = -(W * R) := by
    have h := sum_X_smul_map_pderiv_mul V W
    rw [hVW, sum_X_smul_map_pderiv_one, hEV] at h
    have h' := congrArg (W * ·) h
    simp only [Matrix.mul_zero, Matrix.mul_add, ← Matrix.mul_assoc, hWV, Matrix.one_mul] at h'
    rw [eq_neg_iff_add_eq_zero, add_comm]
    simpa [Matrix.mul_assoc, hVW] using h'.symm
  -- The Euler operator on `∂_μ V`, from `∂_μ` of the radial system.
  have hEdV : ∑ ρ, (X ρ : SpaceTimeAlgebra) • (V.map (pderiv μ)).map (pderiv ρ) =
      R.map (pderiv μ) * V + R * V.map (pderiv μ) - V.map (pderiv μ) := by
    have h := map_pderiv_sum_X_smul_map_pderiv μ V
    rw [hEV, matrix_map_pderiv_mul] at h
    rw [h]
    abel
  rw [sum_X_smul_map_pderiv_mul, hEdV, hEW]
  simp only [sub_mul, add_mul, Matrix.mul_assoc, hVW, Matrix.mul_one, Matrix.mul_neg]
  abel

/-- A fundamental solution of the radial system `E U = R U` based at the identity has
  determinant one when `R` is traceless. By Jacobi's formula the determinant is killed
  by the Euler operator, so it is the constant `1`. -/
lemma eulerTransport_det {κ : Type} [Fintype κ] [DecidableEq κ]
    {R U : Matrix κ κ SpaceTimeAlgebra}
    (hjac : ∀ (M : Matrix κ κ SpaceTimeAlgebra) (μ : Fin 1 ⊕ Fin 3),
      pderiv μ M.det = (M.map (pderiv μ) * M.adjugate).trace)
    (hRtr : R.trace = 0)
    (hU0 : (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix U = 1)
    (hEU : ∑ ρ, (X ρ : SpaceTimeAlgebra) • U.map (pderiv ρ) = R * U) :
    U.det = 1 := by
  have hEdet : ∑ ρ, (X ρ : SpaceTimeAlgebra) • pderiv ρ U.det = 0 := by
    calc ∑ ρ, (X ρ : SpaceTimeAlgebra) • pderiv ρ U.det
        = ∑ ρ, (X ρ : SpaceTimeAlgebra) • (U.map (pderiv ρ) * U.adjugate).trace := by
          exact Finset.sum_congr rfl fun ρ _ => by rw [hjac]
      _ = ((∑ ρ, (X ρ : SpaceTimeAlgebra) • U.map (pderiv ρ)) * U.adjugate).trace := by
          rw [Finset.sum_mul, Matrix.trace_sum]
          exact Finset.sum_congr rfl fun ρ _ => by
            rw [Matrix.smul_mul, Matrix.trace_smul]
      _ = (R * (U.det • (1 : Matrix κ κ SpaceTimeAlgebra))).trace := by
          rw [hEU, Matrix.mul_assoc, Matrix.mul_adjugate]
      _ = 0 := by
          rw [mul_smul_comm, mul_one, Matrix.trace_smul, hRtr, smul_zero]
  have hd0 : constantCoeff (U.det - 1) = 0 := by
    rw [map_sub, map_one, RingHom.map_det, hU0, Matrix.det_one, sub_self]
  have hEd : ∑ ρ, (X ρ : SpaceTimeAlgebra) • pderiv ρ (U.det - 1) = 0 := by
    calc ∑ ρ, (X ρ : SpaceTimeAlgebra) • pderiv ρ (U.det - 1)
        = ∑ ρ, (X ρ : SpaceTimeAlgebra) • pderiv ρ U.det := by
          exact Finset.sum_congr rfl fun ρ _ => by rw [map_sub, pderiv_one, sub_zero]
      _ = 0 := hEdet
  exact sub_eq_zero.mp (eq_zero_of_sum_X_smul_pderiv_eq_zero hd0 hEd)

/-!

## D. The Leibniz rule at the base point for matrices of power series

-/

/-- The entry of a multiset sum of matrices is the multiset sum of the entries. -/
lemma matrix_multiset_sum_apply {κ α : Type*} [AddCommMonoid α]
    (m : Multiset (Matrix κ κ α)) (i j : κ) :
    m.sum i j = (m.map fun A => A i j).sum := by
  induction m using Multiset.induction_on with
  | empty => rfl
  | cons A t ih =>
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, ← ih, Matrix.add_apply]

/-- The matrix Leibniz rule at the base point. The base-point Taylor coefficients of a
  product of matrices of jets are the antidiagonal convolution of the base-point
  coefficients of the factors. -/
lemma matrix_constantCoeff_iteratedPDeriv_mul {κ : Type} [Fintype κ]
    (s : Multiset (Fin 1 ⊕ Fin 3)) (M N : Matrix κ κ SpaceTimeAlgebra) :
    ((M * N).map fun f => constantCoeff (iteratedPDeriv s f))
      = (s.antidiagonal.map fun p =>
          (M.map fun f => constantCoeff (iteratedPDeriv p.1 f)) *
            (N.map fun f => constantCoeff (iteratedPDeriv p.2 f))).sum := by
  ext i j
  rw [Matrix.map_apply, Matrix.mul_apply, iteratedPDeriv_sum, map_sum]
  simp only [constantCoeff_iteratedPDeriv_mul]
  rw [← Multiset.sum_map_finsetSum, matrix_multiset_sum_apply, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
  rw [Function.comp_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [Matrix.map_apply, Matrix.map_apply]

/-- The Taylor coefficients of a product of matrices of jets are the antidiagonal
  convolution of the Taylor coefficients of the factors. -/
lemma map_coeff_mul {κ : Type} [Fintype κ] (M N : Matrix κ κ SpaceTimeAlgebra)
    (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    (M * N).map (coeff p) =
      ∑ x ∈ Finset.antidiagonal p, M.map (coeff x.1) * N.map (coeff x.2) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, coeff_mul, Matrix.sum_apply]
  exact Finset.sum_comm

/-- The matrix Leibniz rule at the base point for a commutator. The base-point Taylor
  coefficients of `M N − N M` are sums of commutators of base-point Taylor coefficients. -/
lemma matrix_constantCoeff_iteratedPDeriv_commutator {κ : Type} [Fintype κ]
    (s : Multiset (Fin 1 ⊕ Fin 3)) (M N : Matrix κ κ SpaceTimeAlgebra) :
    ((M * N - N * M).map fun f => constantCoeff (iteratedPDeriv s f))
      = (s.antidiagonal.map fun p =>
          (M.map fun f => constantCoeff (iteratedPDeriv p.1 f)) *
            (N.map fun f => constantCoeff (iteratedPDeriv p.2 f)) -
          (N.map fun f => constantCoeff (iteratedPDeriv p.2 f)) *
            (M.map fun f => constantCoeff (iteratedPDeriv p.1 f))).sum := by
  have hsub : ((M * N - N * M).map fun f => constantCoeff (iteratedPDeriv s f)) =
      ((M * N).map fun f => constantCoeff (iteratedPDeriv s f)) -
        ((N * M).map fun f => constantCoeff (iteratedPDeriv s f)) := by
    ext i j
    rw [Matrix.map_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply,
      sub_eq_add_neg, iteratedPDeriv_add, iteratedPDeriv_neg, map_add, map_neg, ← sub_eq_add_neg]
  have h2 := matrix_constantCoeff_iteratedPDeriv_mul s N M
  rw [← Multiset.map_swap_antidiagonal s, Multiset.map_map] at h2
  rw [hsub, matrix_constantCoeff_iteratedPDeriv_mul, h2, ← Multiset.sum_map_sub]
  rfl

/-!

## E. Conjugation and derivatives of matrices of jets

-/

section MatrixIdentities

variable {κ : Type}

/-- The entrywise derivative commutes with the conjugate transpose. -/
lemma star_map_pderiv (μ : Fin 1 ⊕ Fin 3) (A : Matrix κ κ SpaceTimeAlgebra) :
    star (A.map (pderiv μ)) = (star A).map (pderiv μ) := by
  ext i j : 1
  simp only [Matrix.star_apply, Matrix.map_apply]
  exact (SpaceTimeAlgebra.pderiv_star μ (A j i)).symm

/-- The entrywise derivative of a difference. -/
lemma map_pderiv_sub (μ : Fin 1 ⊕ Fin 3) (M N : Matrix κ κ SpaceTimeAlgebra) :
    (M - N).map (pderiv μ) = M.map (pderiv μ) - N.map (pderiv μ) := by
  ext i j : 1
  simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]

/-- The entrywise derivative of the inverse `V` of a matrix of jets `U`, through the
  differentiated relation `U V = 1`, `∂_μ V = −V (∂_μ U) V`. -/
lemma map_pderiv_of_mul_eq_one [Fintype κ] [DecidableEq κ] (μ : Fin 1 ⊕ Fin 3)
    {U V : Matrix κ κ SpaceTimeAlgebra} (hUV : U * V = 1) (hVU : V * U = 1) :
    V.map (pderiv μ) = -(V * U.map (pderiv μ) * V) := by
  have h1 : U * V.map (pderiv μ) = -(U.map (pderiv μ) * V) :=
    eq_neg_of_add_eq_zero_right (by
      rw [← SpaceTimeAlgebra.matrix_map_pderiv_mul, hUV]
      exact Matrix.ext fun i j => by
        simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv μ)])
  calc V.map (pderiv μ)
      = V * U * V.map (pderiv μ) := by rw [hVU, one_mul]
    _ = -(V * U.map (pderiv μ) * V) := by
        rw [mul_assoc, h1, mul_neg, ← mul_assoc]

/-- The entrywise derivative of the conjugate transpose of a unitary matrix, through the
  differentiated unitarity relation. -/
lemma map_pderiv_star_of_unitary [Fintype κ] [DecidableEq κ] (μ : Fin 1 ⊕ Fin 3)
    {U : Matrix κ κ SpaceTimeAlgebra}
    (hU : U * star U = 1) (hU' : star U * U = 1) :
    (star U).map (pderiv μ) = -(star U * U.map (pderiv μ) * star U) :=
  map_pderiv_of_mul_eq_one μ hU hU'

/-- The derivative of the conjugate `V A U` of a matrix of jets by an invertible matrix of
  jets `U` with inverse `V`, in terms of the Maurer–Cartan matrix `ω = (∂_μ U) V`,
  `∂_μ (V A U) = V (∂_μ A − (ω A − A ω)) U`. -/
lemma map_pderiv_conj_of_mul_eq_one [Fintype κ] [DecidableEq κ] (μ : Fin 1 ⊕ Fin 3)
    {U V : Matrix κ κ SpaceTimeAlgebra} (hUV : U * V = 1) (hVU : V * U = 1)
    (A : Matrix κ κ SpaceTimeAlgebra) :
    (V * A * U).map (pderiv μ) = V * (A.map (pderiv μ) -
      (U.map (pderiv μ) * V * A - A * (U.map (pderiv μ) * V))) * U := by
  rw [matrix_map_pderiv_mul, matrix_map_pderiv_mul, map_pderiv_of_mul_eq_one μ hUV hVU]
  simp only [mul_sub, sub_mul, add_mul, neg_mul, mul_assoc, hVU, mul_one]
  abel

/-- The cocycle law of Maurer–Cartan matrices, for invertible matrices of jets `U₁`, `U₂`
  with inverses `V₁`, `V₂`, `∂_μ (U₁ U₂) (V₂ V₁) = (∂_μ U₁) V₁ + U₁ ((∂_μ U₂) V₂) V₁`. -/
lemma map_pderiv_mul_mul_mul [Fintype κ] [DecidableEq κ] (μ : Fin 1 ⊕ Fin 3)
    {U₁ U₂ V₁ V₂ : Matrix κ κ SpaceTimeAlgebra} (h : U₂ * V₂ = 1) :
    (U₁ * U₂).map (pderiv μ) * (V₂ * V₁) =
      U₁.map (pderiv μ) * V₁ + U₁ * (U₂.map (pderiv μ) * V₂) * V₁ := by
  rw [matrix_map_pderiv_mul, add_mul]
  congr 1
  · rw [mul_assoc, ← mul_assoc U₂, h, one_mul]
  · simp only [mul_assoc]

/-- The derivative of a commutator of matrices of jets. -/
lemma map_pderiv_commutator [Fintype κ] (μ : Fin 1 ⊕ Fin 3) (A B : Matrix κ κ SpaceTimeAlgebra) :
    (A * B - B * A).map (pderiv μ) = (A.map (pderiv μ) * B - B * A.map (pderiv μ))
      + (A * B.map (pderiv μ) - B.map (pderiv μ) * A) := by
  rw [map_pderiv_sub, matrix_map_pderiv_mul, matrix_map_pderiv_mul]
  abel

/-- A constant matrix of jets has vanishing derivatives. -/
lemma map_pderiv_mapMatrix_C [Fintype κ] [DecidableEq κ] (μ : Fin 1 ⊕ Fin 3)
    (A : Matrix κ κ ℂ) : ((C : ℂ →+* SpaceTimeAlgebra).mapMatrix A).map (pderiv μ) = 0 := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, pderiv_C]

/-- The Maurer–Cartan matrix `i (∂_μ U) U†` of a unitary matrix of jets is hermitian. -/
lemma star_mcMatrix [Fintype κ] [DecidableEq κ] (μ : Fin 1 ⊕ Fin 3)
    {U : Matrix κ κ SpaceTimeAlgebra}
    (hU : U * star U = 1) (hU' : star U * U = 1) :
    star (Complex.I • (U.map (pderiv μ) * star U)) = Complex.I • (U.map (pderiv μ) * star U) := by
  rw [star_smul, star_mul, star_star, star_map_pderiv, map_pderiv_star_of_unitary μ hU hU',
    Complex.star_def, Complex.conj_I, neg_smul, mul_neg, smul_neg, neg_neg, ← mul_assoc,
    ← mul_assoc, hU, one_mul]

end MatrixIdentities

/-!

## F. Invertible matrices of jets

-/

section Units

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- Evaluation of an invertible matrix of jets at the base point, entrywise. -/
noncomputable def unitsEval : (Matrix κ κ SpaceTimeAlgebra)ˣ →* (Matrix κ κ ℂ)ˣ :=
  Units.map (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix.toMonoidHom

@[simp]
lemma unitsEval_val (U : (Matrix κ κ SpaceTimeAlgebra)ˣ) :
    (unitsEval U : Matrix κ κ ℂ) = (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix U := rfl

/-- An invertible matrix as a constant invertible matrix of jets, entrywise. -/
noncomputable def unitsOfConstant : (Matrix κ κ ℂ)ˣ →* (Matrix κ κ SpaceTimeAlgebra)ˣ :=
  Units.map (C : ℂ →+* SpaceTimeAlgebra).mapMatrix.toMonoidHom

@[simp]
lemma unitsOfConstant_val (g : (Matrix κ κ ℂ)ˣ) :
    (unitsOfConstant g : Matrix κ κ SpaceTimeAlgebra) =
      (C : ℂ →+* SpaceTimeAlgebra).mapMatrix g := rfl

/-- A constant invertible matrix of jets evaluates to itself at the base point. -/
lemma unitsEval_unitsOfConstant (g : (Matrix κ κ ℂ)ˣ) : unitsEval (unitsOfConstant g) = g := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, constantCoeff_C]

end Units

end SpaceTimeAlgebra
