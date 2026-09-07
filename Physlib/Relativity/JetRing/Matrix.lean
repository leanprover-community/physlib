/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.JetRing.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Trace
/-!
# Matrices over the jet ring

Results about matrices with entries in `JetRing`: entrywise truncation of matrix
products, and the formal Frobenius theorem (parallel transport): a flat family of
matrices is the logarithmic derivative of a formal fundamental solution.
-/

@[expose] public section

namespace JetRing

open MvPowerSeries

/-- Entrywise truncation of a matrix product only sees the factors through their
  entrywise truncations. -/
lemma matrix_truncation_mul {κ : Type} [Fintype κ] [DecidableEq κ] (n : ℕ)
    (A B : Matrix κ κ JetRing) :
    (A * B).map (truncation n) =
      (A.map (truncation n) * B.map (truncation n)).map (truncation n) := by
  ext i j : 1
  simp only [Matrix.map_apply, Matrix.mul_apply]
  rw [truncation_sum, truncation_sum]
  exact Finset.sum_congr rfl fun k _ => truncation_mul n _ _

/-- The congruence principle for entrywise-truncated matrix products. -/
lemma matrix_truncation_mul_congr {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ}
    {A A' B B' : Matrix κ κ JetRing}
    (hA : A.map (truncation n) = A'.map (truncation n))
    (hB : B.map (truncation n) = B'.map (truncation n)) :
    (A * B).map (truncation n) = (A' * B').map (truncation n) := by
  rw [matrix_truncation_mul, hA, hB, ← matrix_truncation_mul]

lemma matrix_truncation_star {κ : Type} [Fintype κ] [DecidableEq κ] (n : ℕ)
    (A : Matrix κ κ JetRing) :
    (star A).map (truncation n) = star (A.map (truncation n)) := by
  ext i j : 1
  simp only [Matrix.map_apply, Matrix.star_apply]
  exact truncation_star n (A j i)
/-!

### Parallel transport

The formal Frobenius theorem for the jet ring: a flat family of matrices `A_μ` is
the logarithmic derivative `(∂_μ F) F⁻¹` of a formal fundamental solution `F`,
unique once its value at the base point is fixed. Uniqueness is the vanishing
principle for first-order linear systems; existence is the Euler (radial)
recursion, with flatness entering to make the radial solution solve every
direction.

-/


/-- A flat gauge field is pure gauge, at the level of jets: if `A_μ` has vanishing
  field strength, `∂_μ A_ν − ∂_ν A_μ − [A_μ, A_ν] = 0`, then `A_μ = (∂_μ F) F⁻¹`
  for a Wilson line `F` based at the identity: `∂_μ F = A_μ F` with `F(0) = 1`.
  Here a Wilson line means the parallel transport of `A` from the base point —
  the path-ordered exponential `P exp(∫ A_μ dx^μ)`, path-independent since `A` is
  flat. `F` is built order-by-order in its Taylor expansion; it is unique by
  `JetRing.matrix_eq_zero_of_pderiv_eq_mul_add_mul`. -/
lemma exists_parallelTransport {κ : Type} [Fintype κ] [DecidableEq κ]
    (A : (Fin 1 ⊕ Fin 3) → Matrix κ κ JetRing)
    (hA : ∀ μ ν, (A ν).map (pderiv ℂ μ) - (A μ).map (pderiv ℂ ν) =
      A μ * A ν - A ν * A μ) :
    ∃ F : Matrix κ κ JetRing, (constantCoeff : JetRing →+* ℂ).mapMatrix F = 1 ∧
      ∀ μ, F.map (pderiv ℂ μ) = A μ * F := by
  open Finsupp Finset in
  set B : Matrix κ κ JetRing := ∑ ρ, (X ρ : JetRing) • A ρ with hB
  have hBlow : ∀ (M N : Matrix κ κ JetRing) p, (∀ i j q, degree q < degree p →
      coeff q (M i j) = coeff q (N i j)) →
      ∀ i j, coeff p ((B * M) i j) = coeff p ((B * N) i j) := fun M N p h i j => by
    simp only [Matrix.mul_apply, map_sum, coeff_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun q hq => ?_
    rcases eq_or_ne q.1 0 with h1 | h1
    · rw [h1, coeff_zero_eq_constantCoeff, show constantCoeff (B i k) = 0 from by
        simp [hB, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, constantCoeff_X],
        zero_mul, zero_mul]
    · have h4 : degree q.1 + degree q.2 = degree p := by rw [← map_add, mem_antidiagonal.mp hq]
      have h3 := Nat.pos_of_ne_zero fun hc => h1 ((degree_eq_zero_iff _).mp hc)
      rw [h _ _ _ (by omega)]
  set T : Matrix κ κ JetRing → Matrix κ κ JetRing := fun M => 1 + (B * M).map fun f =>
    show JetRing from fun m => if m = 0 then 0 else ((degree m : ℕ) : ℂ)⁻¹ * f m with hT
  set F : Matrix κ κ JetRing :=
    Matrix.of fun i j => show JetRing from fun m => (T^[degree m + 1] 1) i j m with hFd
  have hFco : ∀ p i j, coeff p (F i j) = coeff p ((T^[degree p + 1] 1) i j) := fun _ _ _ => rfl
  have hTco : ∀ (M : Matrix κ κ JetRing) i j p,
      coeff p ((T M) i j) = coeff p ((1 : Matrix κ κ JetRing) i j) +
        if p = 0 then 0 else ((degree p : ℕ) : ℂ)⁻¹ * coeff p ((B * M) i j) :=
    fun M i j p => by
      simp only [hT, Matrix.add_apply, map_add]
      rfl
  have hmain : ∀ n p, degree p = n → ∀ k, n < k → ∀ i j,
      coeff p ((T^[k] 1) i j) = coeff p ((T F) i j) := fun n => by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro p hp k hk i j; obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [Function.iterate_succ_apply', hTco, hTco]; rcases eq_or_ne p 0 with h0 | h0
      · rw [if_pos h0, if_pos h0]
      · rw [if_neg h0, if_neg h0, hBlow _ F _ (fun i' j' q hq => ?_) i j]
        rw [hFco, ih (degree q) (hp ▸ hq) q rfl k (by omega) i' j',
          ih (degree q) (hp ▸ hq) q rfl (degree q + 1) (by omega) i' j']
  have hkey := fun p (i j : κ) => (hFco p i j).trans (hmain _ p rfl _ (Nat.lt_succ_self _) i j)
  have hFone : (constantCoeff : JetRing →+* ℂ).mapMatrix F = 1 := by
    ext i j; simpa [hTco, Matrix.one_apply, apply_ite, coeff_one] using hkey 0 i j
  have hEco : ∀ (M : Matrix κ κ JetRing) p i j,
      coeff p ((∑ ρ, (X ρ : JetRing) • M.map (pderiv ℂ ρ)) i j) =
        ((degree p : ℕ) : ℂ) * coeff p (M i j) := fun M p i j => by
    have ht : ∀ ρ, coeff p (((X ρ : JetRing) • M.map (pderiv ℂ ρ)) i j) =
        (p ρ : ℂ) * coeff p (M i j) := fun ρ => by
      rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
        show (X ρ : JetRing) = monomial (single ρ 1) 1 from rfl, coeff_monomial_mul]
      by_cases h : single ρ 1 ≤ p
      · have hρ : 1 ≤ p ρ := by simpa using single_le_iff.mp h
        rw [if_pos h, one_mul, coeff_pderiv, tsub_add_cancel_of_le h, tsub_apply,
          single_eq_same, Nat.cast_sub hρ]; push_cast; ring
      · have hρ : p ρ = 0 := by by_contra hc; exact h (single_le_iff.mpr (by omega))
        rw [if_neg h, hρ]; simp
    rw [Matrix.sum_apply, map_sum, Finset.sum_congr rfl fun ρ _ => ht ρ, ← Finset.sum_mul,
      ← Nat.cast_sum, ← degree_eq_sum]
  have hleib : ∀ ρ (M N : Matrix κ κ JetRing), (M * N).map (pderiv ℂ ρ) =
      M.map (pderiv ℂ ρ) * N + M * N.map (pderiv ℂ ρ) := fun ρ M N => by
    ext i j : 1; simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
      Derivation.leibniz, smul_eq_mul]
    exact (Finset.sum_congr rfl fun k _ => by ring).trans sum_add_distrib
  set G := fun ν : Fin 1 ⊕ Fin 3 => F.map (pderiv ℂ ν) - A ν * F with hG
  have hstar : ∀ μ ν, (G ν).map (pderiv ℂ μ) =
      (G μ).map (pderiv ℂ ν) + (A μ * G ν - A ν * G μ) := fun μ ν => by
    have hcm : ∀ (M : Matrix κ κ JetRing), (M.map (pderiv ℂ ν)).map (pderiv ℂ μ) =
        (M.map (pderiv ℂ μ)).map (pderiv ℂ ν) :=
      fun M => Matrix.ext fun _ _ => pderiv_comm _ _ _
    simp only [hG]
    rw [Matrix.map_sub _ (fun a b => map_sub _ a b), Matrix.map_sub _ (fun a b => map_sub _ a b),
      hcm, hleib μ (A ν) F, hleib ν (A μ) F, sub_eq_iff_eq_add.mp (hA μ ν)]
    noncomm_ring
  have hG0 : (∑ ρ, (X ρ : JetRing) • G ρ) = 0 := by
    have h1 : (∑ ρ, (X ρ : JetRing) • G ρ) =
        (∑ ρ, (X ρ : JetRing) • F.map (pderiv ℂ ρ)) - B * F := by
      rw [hB, Finset.sum_mul, ← sum_sub_distrib]
      exact Finset.sum_congr rfl fun ρ _ => by rw [hG]; rw [smul_sub, Matrix.smul_mul]
    rw [h1, sub_eq_zero]; ext i j : 1; ext p; rw [hEco]
    rcases eq_or_ne p 0 with rfl | h0
    · have h := hBlow F 0 0 (fun _ _ q hq => absurd hq (by simp)) i j
      simp only [mul_zero, Matrix.zero_apply, map_zero] at h; simp [h]
    · rw [hkey p i j, hTco, show coeff p ((1 : Matrix κ κ JetRing) i j) = 0 from by
        simp [Matrix.one_apply, apply_ite, coeff_one, h0], zero_add, if_neg h0, ← mul_assoc,
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr fun hc => h0 ((degree_eq_zero_iff p).mp hc)),
        one_mul]
  have hS2 : ∀ ν, (∑ ρ, (X ρ : JetRing) • (G ρ).map (pderiv ℂ ν)) = - G ν := by
    intro ν
    have hmap : ((∑ ρ, (X ρ : JetRing) • G ρ).map (pderiv ℂ ν)) =
        G ν + ∑ ρ, (X ρ : JetRing) • (G ρ).map (pderiv ℂ ν) := by
      ext i j : 1; simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, map_sum, Derivation.leibniz, Matrix.add_apply]
      rw [sum_add_distrib, sum_eq_single_of_mem (f := fun ρ => G ρ i j * pderiv ℂ ν (X ρ))
          ν (mem_univ ν) fun b _ hb => by rw [pderiv_X_of_ne hb, mul_zero]]
      rw [pderiv_X_self, mul_one]; exact add_comm _ _
    rw [hG0, Matrix.map_zero _ (map_zero _)] at hmap
    exact eq_neg_of_add_eq_zero_right hmap.symm
  have halg : ∀ ν p i j,
      (((degree p : ℕ) : ℂ) + 1) * coeff p (G ν i j) = coeff p ((B * G ν) i j) := by
    intro ν p i j; have hs1 : (∑ ρ, (X ρ : JetRing) • (G ν).map (pderiv ℂ ρ)) =
        (∑ ρ, (X ρ : JetRing) • (G ρ).map (pderiv ℂ ν)) +
          (B * G ν - A ν * ∑ ρ, (X ρ : JetRing) • G ρ) := by
      rw [Finset.sum_congr rfl fun ρ _ => congrArg ((X ρ : JetRing) • ·) (hstar ρ ν)]
      simp only [smul_add, smul_sub, sum_add_distrib, sum_sub_distrib]
      congr 1; congr 1
      · rw [hB, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => (Matrix.smul_mul _ _ _).symm
      · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => (Matrix.mul_smul _ _ _).symm
    rw [hG0, mul_zero, sub_zero, hS2] at hs1
    have h := congrArg (fun M => coeff p (M i j)) hs1
    simp only [Matrix.add_apply, Matrix.neg_apply, map_add, map_neg] at h
    rw [hEco] at h; linear_combination h
  have hzero : ∀ ν, G ν = 0 := fun ν => by
    have hm : ∀ n q, degree q = n → ∀ i j, coeff q (G ν i j) = 0 := fun n => by
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro q hq i j; have h := halg ν q i j
        rw [hBlow (G ν) 0 q (fun i' j' r hr => by
            rw [ih (degree r) (hq ▸ hr) r rfl i' j', Matrix.zero_apply, map_zero]) i j,
          mul_zero] at h
        simp only [Matrix.zero_apply, map_zero] at h
        exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast Nat.succ_ne_zero (degree q))
    ext i j : 1; ext p; rw [hm (degree p) p rfl i j, Matrix.zero_apply, map_zero]
  exact ⟨F, hFone, fun ν => sub_eq_zero.mp (hzero ν)⟩


/-!

## The Euler operator toolkit on matrices

-/

/-- Entrywise evaluation at the base point commutes with the conjugate transpose. -/
lemma mapMatrix_constantCoeff_star {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n JetRing) :
    (constantCoeff : JetRing →+* ℂ).mapMatrix (star A) =
      star ((constantCoeff : JetRing →+* ℂ).mapMatrix A) := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.star_apply]

/-- The Euler operator on matrices of jets acts entrywise on Taylor coefficients as
  multiplication by the total degree. -/
lemma coeff_sum_X_smul_map_pderiv {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ JetRing) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) (i j : κ) :
    coeff p ((∑ ρ, (X ρ : JetRing) • M.map (pderiv ℂ ρ)) i j) =
      ((Finsupp.degree p : ℕ) : ℂ) * coeff p (M i j) := by
  rw [show (∑ ρ, (X ρ : JetRing) • M.map (pderiv ℂ ρ)) i j
      = ∑ ρ, (X ρ : JetRing) • pderiv ℂ ρ (M i j) from by
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun ρ _ => rfl]
  exact coeff_sum_X_smul_pderiv (M i j) p

/-- The vanishing principle for the Euler operator: a matrix of jets vanishing at the
  base point and satisfying `E W = A W + W B` with `A`, `B` vanishing at the base point
  is zero. Each Taylor coefficient of `W` is a multiple of coefficients of strictly
  smaller degree, so all vanish by strong induction on the degree. -/
lemma matrix_eq_zero_of_euler_eq_mul_add_mul {κ : Type} [Fintype κ] [DecidableEq κ]
    {W : Matrix κ κ JetRing} (A B : Matrix κ κ JetRing)
    (hA : ∀ i j, constantCoeff (A i j) = 0) (hB : ∀ i j, constantCoeff (B i j) = 0)
    (h0 : ∀ i j, constantCoeff (W i j) = 0)
    (hW : ∑ ρ, (X ρ : JetRing) • W.map (pderiv ℂ ρ) = A * W + W * B) :
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
      · have h : coeff p ((∑ ρ, (X ρ : JetRing) • W.map (pderiv ℂ ρ)) i j) =
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
    (R : Matrix κ κ JetRing) (hR0 : ∀ i j, constantCoeff (R i j) = 0) :
    ∃ U : Matrix κ κ JetRing, (constantCoeff : JetRing →+* ℂ).mapMatrix U = 1 ∧
      ∑ ρ, (X ρ : JetRing) • U.map (pderiv ℂ ρ) = R * U := by
  classical
  have hRlow : ∀ (M N : Matrix κ κ JetRing) (p : (Fin 1 ⊕ Fin 3) →₀ ℕ),
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
  set T : Matrix κ κ JetRing → Matrix κ κ JetRing := fun M => 1 + (R * M).map fun f =>
    show JetRing from fun m => if m = 0 then 0 else ((Finsupp.degree m : ℕ) : ℂ)⁻¹ * f m
    with hT
  set U : Matrix κ κ JetRing :=
    Matrix.of fun i j => show JetRing from fun m => (T^[Finsupp.degree m + 1] 1) i j m with hUd
  have hUco : ∀ (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) i j,
      coeff p (U i j) = coeff p ((T^[Finsupp.degree p + 1] 1) i j) := fun _ _ _ => rfl
  have hTco : ∀ (M : Matrix κ κ JetRing) i j (p : (Fin 1 ⊕ Fin 3) →₀ ℕ),
      coeff p ((T M) i j) = coeff p ((1 : Matrix κ κ JetRing) i j) +
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
      · rw [if_pos h0, if_pos h0]
      · rw [if_neg h0, if_neg h0, hRlow _ U _ (fun i' j' q hq => ?_) i j]
        rw [hUco, ih (Finsupp.degree q) (by omega) q rfl k (by omega) i' j',
          ih (Finsupp.degree q) (by omega) q rfl (Finsupp.degree q + 1) (by omega) i' j']
  have hkey := fun (p : (Fin 1 ⊕ Fin 3) →₀ ℕ) (i j : κ) =>
    (hUco p i j).trans (hmain _ p rfl _ (Nat.lt_succ_self _) i j)
  have hUone : (constantCoeff : JetRing →+* ℂ).mapMatrix U = 1 := by
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
  · rw [hkey p i j, hTco, show coeff p ((1 : Matrix κ κ JetRing) i j) = 0 from by
      simp [Matrix.one_apply, apply_ite, coeff_one, h0], zero_add, if_neg h0, ← mul_assoc,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr fun hc => h0 ((Finsupp.degree_eq_zero_iff p).mp hc)),
      one_mul]

/-!

## Unitarity and determinant of the Euler transport

-/

/-- The entrywise Leibniz rule for matrix products of jets. -/
lemma matrix_map_pderiv_mul {κ : Type} [Fintype κ] [DecidableEq κ] (ρ : Fin 1 ⊕ Fin 3)
    (M N : Matrix κ κ JetRing) :
    (M * N).map (pderiv ℂ ρ) = M.map (pderiv ℂ ρ) * N + M * N.map (pderiv ℂ ρ) := by
  ext i j : 1
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
    Derivation.leibniz, smul_eq_mul]
  exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib

/-- The Euler operator on matrices of jets is a derivation. -/
lemma sum_X_smul_map_pderiv_mul {κ : Type} [Fintype κ] [DecidableEq κ]
    (M N : Matrix κ κ JetRing) :
    ∑ ρ, (X ρ : JetRing) • (M * N).map (pderiv ℂ ρ) =
      (∑ ρ, (X ρ : JetRing) • M.map (pderiv ℂ ρ)) * N +
        M * ∑ ρ, (X ρ : JetRing) • N.map (pderiv ℂ ρ) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [matrix_map_pderiv_mul, smul_add, Matrix.smul_mul, Matrix.mul_smul]

/-- The Euler operator commutes with the conjugate transpose. -/
lemma sum_X_smul_map_pderiv_star {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ JetRing) :
    ∑ ρ, (X ρ : JetRing) • (star M).map (pderiv ℂ ρ) =
      star (∑ ρ, (X ρ : JetRing) • M.map (pderiv ℂ ρ)) := by
  ext i j : 1
  simp only [Matrix.sum_apply, Matrix.star_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, star_sum, star_mul', star_X, ← JetRing.pderiv_star]

/-- The Euler operator kills the identity matrix. -/
lemma sum_X_smul_map_pderiv_one {κ : Type} [Fintype κ] [DecidableEq κ] :
    ∑ ρ, (X ρ : JetRing) • (1 : Matrix κ κ JetRing).map (pderiv ℂ ρ) = 0 := by
  refine Finset.sum_eq_zero fun ρ _ => ?_
  rw [show (1 : Matrix κ κ JetRing).map (pderiv ℂ ρ) = 0 from Matrix.ext fun i j => by
    simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ℂ ρ)], smul_zero]

/-- A fundamental solution of the radial system `E U = R U` based at the identity is
  unitary when `R` is anti-hermitian: `U U† − 1` vanishes at the base point and
  satisfies a homogeneous linear radial system, so it vanishes identically. -/
lemma eulerTransport_mul_star {κ : Type} [Fintype κ] [DecidableEq κ]
    {R U : Matrix κ κ JetRing} (hRstar : star R = -R)
    (hR0 : ∀ i j, constantCoeff (R i j) = 0)
    (hU0 : (constantCoeff : JetRing →+* ℂ).mapMatrix U = 1)
    (hEU : ∑ ρ, (X ρ : JetRing) • U.map (pderiv ℂ ρ) = R * U) :
    U * star U = 1 := by
  have hEstar : ∑ ρ, (X ρ : JetRing) • (star U).map (pderiv ℂ ρ) = -(star U * R) := by
    rw [sum_X_smul_map_pderiv_star, hEU, star_mul, hRstar, Matrix.mul_neg]
  have hW0 : (constantCoeff : JetRing →+* ℂ).mapMatrix (U * star U - 1) = 0 := by
    rw [map_sub, map_mul, mapMatrix_constantCoeff_star, hU0, star_one,
      mul_one, map_one, sub_self]
  have h0 : ∀ i j, constantCoeff ((U * star U - 1) i j) = 0 := fun i j => by
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using congrArg (fun M => M i j) hW0
  have hB : ∀ i j, constantCoeff ((-R) i j) = 0 := fun i j => by
    simp [hR0 i j]
  have hEW : ∑ ρ, (X ρ : JetRing) • (U * star U - 1).map (pderiv ℂ ρ) =
      R * (U * star U - 1) + (U * star U - 1) * (-R) := by
    have hsub : ∀ ρ : Fin 1 ⊕ Fin 3, (U * star U - 1).map (pderiv ℂ ρ) =
        (U * star U).map (pderiv ℂ ρ) - (1 : Matrix κ κ JetRing).map (pderiv ℂ ρ) :=
      fun ρ => Matrix.ext fun i j => by simp [Matrix.map_apply]
    simp only [hsub, smul_sub, Finset.sum_sub_distrib]
    rw [sum_X_smul_map_pderiv_mul, hEU, hEstar, sum_X_smul_map_pderiv_one, sub_zero]
    noncomm_ring
  exact sub_eq_zero.mp (matrix_eq_zero_of_euler_eq_mul_add_mul R (-R) hR0 hB h0 hEW)

/-- A fundamental solution of the radial system `E U = R U` based at the identity has
  determinant one when `R` is traceless: by Jacobi's formula the determinant is killed
  by the Euler operator, so it is the constant `1`. -/
lemma eulerTransport_det {κ : Type} [Fintype κ] [DecidableEq κ]
    {R U : Matrix κ κ JetRing}
    (hjac : ∀ (M : Matrix κ κ JetRing) (μ : Fin 1 ⊕ Fin 3),
      pderiv ℂ μ M.det = (M.map (pderiv ℂ μ) * M.adjugate).trace)
    (hRtr : R.trace = 0)
    (hU0 : (constantCoeff : JetRing →+* ℂ).mapMatrix U = 1)
    (hEU : ∑ ρ, (X ρ : JetRing) • U.map (pderiv ℂ ρ) = R * U) :
    U.det = 1 := by
  have hEdet : ∑ ρ, (X ρ : JetRing) • pderiv ℂ ρ U.det = 0 := by
    calc ∑ ρ, (X ρ : JetRing) • pderiv ℂ ρ U.det
        = ∑ ρ, (X ρ : JetRing) • (U.map (pderiv ℂ ρ) * U.adjugate).trace := by
          exact Finset.sum_congr rfl fun ρ _ => by rw [hjac]
      _ = ((∑ ρ, (X ρ : JetRing) • U.map (pderiv ℂ ρ)) * U.adjugate).trace := by
          rw [Finset.sum_mul, Matrix.trace_sum]
          exact Finset.sum_congr rfl fun ρ _ => by
            rw [Matrix.smul_mul, Matrix.trace_smul]
      _ = (R * (U.det • (1 : Matrix κ κ JetRing))).trace := by
          rw [hEU, Matrix.mul_assoc, Matrix.mul_adjugate]
      _ = 0 := by
          rw [mul_smul_comm, mul_one, Matrix.trace_smul, hRtr, smul_zero]
  have hd0 : constantCoeff (U.det - 1) = 0 := by
    rw [map_sub, map_one, RingHom.map_det, hU0, Matrix.det_one, sub_self]
  have hEd : ∑ ρ, (X ρ : JetRing) • pderiv ℂ ρ (U.det - 1) = 0 := by
    calc ∑ ρ, (X ρ : JetRing) • pderiv ℂ ρ (U.det - 1)
        = ∑ ρ, (X ρ : JetRing) • pderiv ℂ ρ U.det := by
          exact Finset.sum_congr rfl fun ρ _ => by rw [map_sub, pderiv_one, sub_zero]
      _ = 0 := hEdet
  exact sub_eq_zero.mp (eq_zero_of_sum_X_smul_pderiv_eq_zero hd0 hEd)

/-!

## Jacobi's formula on the matrix factors, and degree bookkeeping

-/

lemma jacobi_fin3 (M : Matrix (Fin 3) (Fin 3) JetRing) (μ : Fin 1 ⊕ Fin 3) :
    pderiv ℂ μ M.det = (M.map (pderiv ℂ μ) * M.adjugate).trace := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.map_apply, Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.head_fin_const, Matrix.empty_val', Matrix.cons_val_fin_one,
    map_sub, map_add, Derivation.leibniz, smul_eq_mul]
  ring

lemma jacobi_fin2 (M : Matrix (Fin 2) (Fin 2) JetRing) (μ : Fin 1 ⊕ Fin 3) :
    pderiv ℂ μ M.det = (M.map (pderiv ℂ μ) * M.adjugate).trace := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.mul_apply,
    Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one, Fin.sum_univ_two, Matrix.cons_val_one,
    map_sub, Derivation.leibniz, smul_eq_mul]
  ring

end JetRing
