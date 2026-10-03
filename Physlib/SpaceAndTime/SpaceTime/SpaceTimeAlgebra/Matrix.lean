/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Physlib.Mathematics.MultisetAntidiagonal
public import Physlib.SpaceAndTime.SpaceTime.SpaceTimeAlgebra.Basic
/-!
# Matrices over the jet ring

Results about matrices with entries in `SpaceTimeAlgebra`, chiefly the Euler (radial) transport: a
matrix of jets vanishing at the base point is the radial logarithmic derivative of a formal
fundamental solution.
-/

@[expose] public section

namespace SpaceTimeAlgebra

open MvPowerSeries

/-!

## The Euler operator toolkit on matrices

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
lemma coeff_sum_X_smul_map_pderiv {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ SpaceTimeAlgebra) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) (i j : κ) :
    coeff p ((∑ ρ, (X ρ : SpaceTimeAlgebra) • M.map (pderiv ρ)) i j) =
      ((Finsupp.degree p : ℕ) : ℂ) * coeff p (M i j) := by
  rw [show (∑ ρ, (X ρ : SpaceTimeAlgebra) • M.map (pderiv ρ)) i j
      = ∑ ρ, (X ρ : SpaceTimeAlgebra) • pderiv ρ (M i j) from by
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun ρ _ => rfl]
  exact coeff_sum_X_smul_pderiv (M i j) p

/-- The vanishing principle for the Euler operator: a matrix of jets vanishing at the
  base point and satisfying `E W = A W + W B` with `A`, `B` vanishing at the base point
  is zero. Each Taylor coefficient of `W` is a multiple of coefficients of strictly
  smaller degree, so all vanish by strong induction on the degree. -/
lemma matrix_eq_zero_of_euler_eq_mul_add_mul {κ : Type} [Fintype κ] [DecidableEq κ]
    {W : Matrix κ κ SpaceTimeAlgebra} (A B : Matrix κ κ SpaceTimeAlgebra)
    (hA : ∀ i j, constantCoeff (A i j) = 0) (hB : ∀ i j, constantCoeff (B i j) = 0)
    (h0 : ∀ i j, constantCoeff (W i j) = 0)
    (hW : ∑ ρ, (X ρ : SpaceTimeAlgebra) • W.map (pderiv ρ) = A * W + W * B) :
    W = 0 := by
  classical
  have hlow : ∀ p : (Fin 1 ⊕ Fin 3) →₀ ℕ,
      (∀ (i : κ) (j : κ) (q : (Fin 1 ⊕ Fin 3) →₀ ℕ),
        Finsupp.degree q < Finsupp.degree p → coeff q (W i j) = 0) →
      ∀ i j, coeff p ((A * W + W * B) i j) = 0 := by
    intro p hp i j
    have hAW : coeff p ((A * W) i j) = 0 := by
      rw [Matrix.mul_apply, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [coeff_mul]
      refine Finset.sum_eq_zero fun q hq => ?_
      rcases eq_or_ne q.1 0 with h1 | h1
      · rw [h1, coeff_zero_eq_constantCoeff, hA, zero_mul]
      · have h4 : Finsupp.degree q.1 + Finsupp.degree q.2 = Finsupp.degree p := by
          rw [← map_add, Finset.mem_antidiagonal.mp hq]
        have h3 := Nat.pos_of_ne_zero fun hc => h1 ((Finsupp.degree_eq_zero_iff _).mp hc)
        rw [hp _ _ q.2 (by omega), mul_zero]
    have hWB : coeff p ((W * B) i j) = 0 := by
      rw [Matrix.mul_apply, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [coeff_mul]
      refine Finset.sum_eq_zero fun q hq => ?_
      rcases eq_or_ne q.2 0 with h1 | h1
      · rw [h1, coeff_zero_eq_constantCoeff, hB, mul_zero]
      · have h4 : Finsupp.degree q.1 + Finsupp.degree q.2 = Finsupp.degree p := by
          rw [← map_add, Finset.mem_antidiagonal.mp hq]
        have h3 := Nat.pos_of_ne_zero fun hc => h1 ((Finsupp.degree_eq_zero_iff _).mp hc)
        rw [hp _ _ q.1 (by omega), zero_mul]
    rw [Matrix.add_apply, map_add, hAW, hWB, add_zero]
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

/-- The Euler (radial) transport of a jet matrix `R` vanishing at the base point:
  a fundamental solution of the radial system `E U = R U` based at the identity,
  built order-by-order by the Euler recursion. -/
lemma exists_matrix_eulerTransport {κ : Type} [Fintype κ] [DecidableEq κ]
    (R : Matrix κ κ SpaceTimeAlgebra) (hR0 : ∀ i j, constantCoeff (R i j) = 0) :
    ∃ U : Matrix κ κ SpaceTimeAlgebra, (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix U = 1 ∧
      ∑ ρ, (X ρ : SpaceTimeAlgebra) • U.map (pderiv ρ) = R * U := by
  classical
  have hRlow : ∀ (M N : Matrix κ κ SpaceTimeAlgebra) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ),
      (∀ (i : κ) (j : κ) (q : (Fin 1 ⊕ Fin 3) →₀ ℕ),
        Finsupp.degree q < Finsupp.degree p → coeff q (M i j) = coeff q (N i j)) →
      ∀ i j, coeff p ((R * M) i j) = coeff p ((R * N) i j) := fun M N p h i j => by
    simp only [Matrix.mul_apply, map_sum, coeff_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun q hq => ?_
    rcases eq_or_ne q.1 0 with h1 | h1
    · rw [h1, coeff_zero_eq_constantCoeff, hR0, zero_mul, zero_mul]
    · have h4 : Finsupp.degree q.1 + Finsupp.degree q.2 = Finsupp.degree p := by
        rw [← map_add, Finset.mem_antidiagonal.mp hq]
      have h3 := Nat.pos_of_ne_zero fun hc => h1 ((Finsupp.degree_eq_zero_iff _).mp hc)
      rw [h _ _ _ (by omega)]
  set T : Matrix κ κ SpaceTimeAlgebra → Matrix κ κ SpaceTimeAlgebra := fun M => 1 +
      (R * M).map fun f =>
    show SpaceTimeAlgebra from fun m => if m = 0 then 0 else ((Finsupp.degree m : ℕ) : ℂ)⁻¹ * f m
    with hT
  set U : Matrix κ κ SpaceTimeAlgebra :=
    Matrix.of fun i j => show SpaceTimeAlgebra from fun m =>
        (T^[Finsupp.degree m + 1] 1) i j m with hUd
  have hUco : ∀ (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) i j,
      coeff p (U i j) = coeff p ((T^[Finsupp.degree p + 1] 1) i j) := fun _ _ _ => rfl
  have hTco : ∀ (M : Matrix κ κ SpaceTimeAlgebra) i j (p : (Fin 1 ⊕ Fin 3) →₀ ℕ),
      coeff p ((T M) i j) = coeff p ((1 : Matrix κ κ SpaceTimeAlgebra) i j) +
        if p = 0 then 0 else ((Finsupp.degree p : ℕ) : ℂ)⁻¹ * coeff p ((R * M) i j) :=
    fun M i j p => by
      simp only [hT, Matrix.add_apply, map_add]
      rfl
  have hmain : ∀ (n : ℕ) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ), Finsupp.degree p = n → ∀ k, n < k →
      ∀ i j, coeff p ((T^[k] 1) i j) = coeff p ((T U) i j) := fun n => by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro p hp k hk i j
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [Function.iterate_succ_apply', hTco, hTco]
      rcases eq_or_ne p 0 with h0 | h0
      · rw [ite_eq_left h0, ite_eq_left h0]
      · rw [ite_eq_right h0, ite_eq_right h0, hRlow _ U _ (fun i' j' q hq => ?_) i j]
        rw [hUco, ih (Finsupp.degree q) (by omega) q rfl k (by omega) i' j',
          ih (Finsupp.degree q) (by omega) q rfl (Finsupp.degree q + 1) (by omega) i' j']
  have hkey := fun (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) (i j : κ) =>
    (hUco p i j).trans (hmain _ p rfl _ (Nat.lt_succ_self _) i j)
  have hUone : (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix U = 1 := by
    ext i j
    simpa [hTco, Matrix.one_apply, apply_ite, coeff_one] using hkey 0 i j
  refine ⟨U, hUone, ?_⟩
  ext i j : 1
  ext p
  rw [coeff_sum_X_smul_map_pderiv]
  rcases eq_or_ne p 0 with rfl | h0
  · rw [show ((Finsupp.degree (0 : (Fin 1 ⊕ Fin 3) →₀ ℕ) : ℕ) : ℂ) = 0 by simp, zero_mul]
    rw [Matrix.mul_apply, map_sum]
    exact (Finset.sum_eq_zero fun k _ => by
      rw [coeff_zero_eq_constantCoeff, map_mul, hR0, zero_mul]).symm
  · rw [hkey p i j, hTco, show coeff p ((1 : Matrix κ κ SpaceTimeAlgebra) i j) = 0 from by
      simp [Matrix.one_apply, apply_ite, coeff_one, h0], zero_add, ite_eq_right h0, ← mul_assoc,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr fun hc => h0 ((Finsupp.degree_eq_zero_iff p).mp hc)),
      one_mul]

/-!

## The Euler vanishing principle by degree on matrices

-/

/-- The matrix form of `coeff_eq_zero_of_pderiv_eq_mul`: the entries of a matrix of power
  series satisfying `∂_ρ A = X_ρ A`, with the `X_ρ` vanishing below degree `n`, have no
  coefficients in nonzero degree up to `n`. -/
lemma coeff_entry_eq_zero_of_map_pderiv_eq_mul {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ}
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

## Unitarity and determinant of the Euler transport

-/

/-- The entrywise Leibniz rule for matrix products of jets. -/
lemma matrix_map_pderiv_mul {κ : Type} [Fintype κ] [DecidableEq κ] (ρ : Fin 1 ⊕ Fin 3)
    (M N : Matrix κ κ SpaceTimeAlgebra) :
    (M * N).map (pderiv ρ) = M.map (pderiv ρ) * N + M * N.map (pderiv ρ) := by
  ext i j : 1
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
    Derivation.leibniz, smul_eq_mul]
  exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib

/-- The Euler operator on matrices of jets is a derivation. -/
lemma sum_X_smul_map_pderiv_mul {κ : Type} [Fintype κ] [DecidableEq κ]
    (M N : Matrix κ κ SpaceTimeAlgebra) :
    ∑ ρ, (X ρ : SpaceTimeAlgebra) • (M * N).map (pderiv ρ) =
      (∑ ρ, (X ρ : SpaceTimeAlgebra) • M.map (pderiv ρ)) * N +
        M * ∑ ρ, (X ρ : SpaceTimeAlgebra) • N.map (pderiv ρ) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [matrix_map_pderiv_mul, smul_add, Matrix.smul_mul, Matrix.mul_smul]

/-- The Euler operator commutes with the conjugate transpose. -/
lemma sum_X_smul_map_pderiv_star {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ SpaceTimeAlgebra) :
    ∑ ρ, (X ρ : SpaceTimeAlgebra) • (star M).map (pderiv ρ) =
      star (∑ ρ, (X ρ : SpaceTimeAlgebra) • M.map (pderiv ρ)) := by
  ext i j : 1
  simp only [Matrix.sum_apply, Matrix.star_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, star_sum, star_mul', star_X, ← SpaceTimeAlgebra.pderiv_star]

/-- The Euler operator kills the identity matrix. -/
lemma sum_X_smul_map_pderiv_one {κ : Type} [Fintype κ] [DecidableEq κ] :
    ∑ ρ, (X ρ : SpaceTimeAlgebra) • (1 : Matrix κ κ SpaceTimeAlgebra).map (pderiv ρ) = 0 := by
  refine Finset.sum_eq_zero fun ρ _ => ?_
  rw [show (1 : Matrix κ κ SpaceTimeAlgebra).map (pderiv ρ) = 0 from Matrix.ext fun i j => by
    simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ρ)], smul_zero]

/-- A fundamental solution of the radial system `E U = R U` based at the identity is
  unitary when `R` is anti-hermitian: `U U† − 1` vanishes at the base point and
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
  system `E V = −i P V` is `P`: `∑_μ x_μ · i (∂_μ V) V† = P`. -/
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

/-- A fundamental solution of the radial system `E U = R U` based at the identity has
  determinant one when `R` is traceless: by Jacobi's formula the determinant is killed
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

## The Leibniz rule at the base point for matrices of power series

-/

/-- The entry of a multiset sum of matrices is the multiset sum of the entries. -/
lemma matrix_multiset_sum_apply {κ α : Type*} [AddCommMonoid α]
    (m : Multiset (Matrix κ κ α)) (i j : κ) :
    m.sum i j = (m.map fun A => A i j).sum := by
  induction m using Multiset.induction_on with
  | empty => rfl
  | cons A t ih =>
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, ← ih, Matrix.add_apply]

/-- The matrix Leibniz rule at the base point: the base-point Taylor coefficients of a
  product of matrices of jets are the antidiagonal convolution of the base-point
  coefficients of the factors. -/
lemma matrix_constantCoeff_iteratedPDeriv_mul {κ : Type} [Fintype κ] [DecidableEq κ]
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

/-!

## Conjugation, scalars and derivatives of matrices of jets

-/

section MatrixIdentities

variable {κ : Type}

/-- Entrywise inclusion of constants commutes with the conjugate transpose. -/
lemma mapMatrix_C_star [Fintype κ] [DecidableEq κ] (A : Matrix κ κ ℂ) :
    (C : ℂ →+* SpaceTimeAlgebra).mapMatrix (star A) = star
        ((C : ℂ →+* SpaceTimeAlgebra).mapMatrix A) := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.star_apply]

/-- Entrywise inclusion of constants commutes with complex scalars. -/
lemma mapMatrix_C_smul [Fintype κ] [DecidableEq κ] (c : ℂ) (M : Matrix κ κ ℂ) :
    (C : ℂ →+* SpaceTimeAlgebra).mapMatrix (c • M) = c •
        (C : ℂ →+* SpaceTimeAlgebra).mapMatrix M := by
  ext i j : 1
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply,
    MvPowerSeries.smul_eq_C_mul, smul_eq_mul, map_mul]

/-- The entrywise constant coefficient commutes with complex scalars. -/
lemma mapMatrix_constantCoeff_smul [Fintype κ] [DecidableEq κ] (c : ℂ)
    (M : Matrix κ κ SpaceTimeAlgebra) :
    (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix (c • M)
      = c • (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix M := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply]

/-- The entrywise derivative commutes with the conjugate transpose. -/
lemma star_map_pderiv [Fintype κ] (μ : Fin 1 ⊕ Fin 3) (A : Matrix κ κ SpaceTimeAlgebra) :
    star (A.map (pderiv μ)) = (star A).map (pderiv μ) := by
  ext i j : 1
  simp only [Matrix.star_apply, Matrix.map_apply]
  exact (SpaceTimeAlgebra.pderiv_star μ (A j i)).symm

/-- Pulling a complex scalar out of the entrywise derivative. -/
lemma map_pderiv_smul (μ : Fin 1 ⊕ Fin 3) (c : ℂ) (M : Matrix κ κ SpaceTimeAlgebra) :
    (c • M).map (pderiv μ) = c • M.map (pderiv μ) :=
  Matrix.ext fun _ _ => Derivation.map_smul _ _ _

/-- The entrywise derivative of a difference. -/
lemma map_pderiv_sub (μ : Fin 1 ⊕ Fin 3) (M N : Matrix κ κ SpaceTimeAlgebra) :
    (M - N).map (pderiv μ) = M.map (pderiv μ) - N.map (pderiv μ) := by
  ext i j : 1
  simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]

/-- The entrywise derivative of the conjugate transpose of a unitary matrix, through the
  differentiated unitarity relation. -/
lemma map_pderiv_star_of_unitary [Fintype κ] [DecidableEq κ] (μ : Fin 1 ⊕ Fin 3)
    {U : Matrix κ κ SpaceTimeAlgebra}
    (hU : U * star U = 1) (hU' : star U * U = 1) :
    (star U).map (pderiv μ) = -(star U * U.map (pderiv μ) * star U) := by
  have h1 : U * (star U).map (pderiv μ) = -(U.map (pderiv μ) * star U) :=
    eq_neg_of_add_eq_zero_right (by
      rw [← SpaceTimeAlgebra.matrix_map_pderiv_mul, hU]
      exact Matrix.ext fun i j => by
        simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv μ)])
  calc (star U).map (pderiv μ)
      = star U * U * (star U).map (pderiv μ) := by rw [hU', one_mul]
    _ = -(star U * U.map (pderiv μ) * star U) := by
        rw [mul_assoc, h1, mul_neg, ← mul_assoc]

/-- The Maurer–Cartan matrix `i (∂_μ U) U†` of a unitary matrix of jets is hermitian. -/
lemma star_mcMatrix [Fintype κ] [DecidableEq κ] (μ : Fin 1 ⊕ Fin 3)
    {U : Matrix κ κ SpaceTimeAlgebra}
    (hU : U * star U = 1) (hU' : star U * U = 1) :
    star (Complex.I • (U.map (pderiv μ) * star U)) = Complex.I • (U.map (pderiv μ) * star U) := by
  rw [star_smul, star_mul, star_star, star_map_pderiv, map_pderiv_star_of_unitary μ hU hU',
    Complex.star_def, Complex.conj_I, neg_smul, mul_neg, smul_neg, neg_neg, ← mul_assoc,
    ← mul_assoc, hU, one_mul]

end MatrixIdentities

end SpaceTimeAlgebra
