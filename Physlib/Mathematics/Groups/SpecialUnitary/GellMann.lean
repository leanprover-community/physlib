/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Physlib.Mathematics.Groups.SpecialUnitary.Algebra
/-!
# The generalized Gell-Mann matrices

## i. Overview

The generalized Gell-Mann matrices are the standard basis of the traceless complex `N × N`
matrices, the complexified Lie algebra of `SU(N)`, generalizing the Pauli matrices (`N = 2`) and
the Gell-Mann matrices (`N = 3`). There are `N² - 1` of them, of three kinds:

- for `j < k` the symmetric matrix `E_jk + E_kj`,
- for `j < k` the antisymmetric matrix `-i E_jk + i E_kj`,
- for `1 ≤ n ≤ N - 1` the diagonal matrix `√(2 / (n (n + 1))) (E_00 + ⋯ + E_(n-1)(n-1) - n E_nn)`.

They are hermitian and traceless, and orthogonal under the trace form, `tr (λ_a λ_b) = 2 δ_ab`.
Orthogonality makes them linearly independent, and there are as many as the dimension of the
traceless matrices, so they form a basis, `GellMann.basis`, whose coordinates are read off by the
trace form, `GellMann.basis_repr_apply`. Being hermitian they lie in the real Lie algebra `su(N)`
of traceless hermitian matrices, and there they form a real basis, `GellMann.realBasis`: the
coordinates `tr (λ_a H) / 2` of a traceless hermitian matrix `H` are real (E).

## ii. Key results

- `GellMann.Index` : the labels of the generalized Gell-Mann matrices.
- `GellMann.matrix` : the generalized Gell-Mann matrices.
- `GellMann.trace_matrix_mul_matrix` : `tr (λ_a λ_b) = 2 δ_ab`.
- `GellMann.basis` : the basis of the traceless matrices they form.
- `GellMann.realBasis` : the basis of the real Lie algebra `su(N)` they form.

## iii. Table of contents

- A. The matrices
- B. The diagonal profiles
- C. Orthogonality
- D. The basis
- E. The real basis of `su(N)`

-/

@[expose] public section

open Matrix Module

namespace GellMann

/-!

## A. The matrices

-/

/-- The labels of the generalized Gell-Mann matrices: a pair `j < k` for each symmetric and each
  antisymmetric matrix, and `l : Fin (N - 1)` for the diagonal matrix of size `n = l + 1`. -/
abbrev Index (N : ℕ) : Type :=
  {p : Fin N × Fin N // p.1 < p.2} ⊕ {p : Fin N × Fin N // p.1 < p.2} ⊕ Fin (N - 1)

variable {N : ℕ}

/-- The diagonal profile of size `n = l + 1`: `1` on the first `n` entries, `-n` on the next, and
  `0` beyond. -/
def diagProfile (l : Fin (N - 1)) (m : Fin N) : ℂ :=
  if m.val < l.val + 1 then 1 else if m.val = l.val + 1 then -((l.val + 1 : ℕ) : ℂ) else 0

/-- The normalization `√(2 / (n (n + 1)))` of the diagonal matrix of size `n = l + 1`. -/
noncomputable def diagNorm (l : Fin (N - 1)) : ℂ :=
  (Real.sqrt (2 / (((l.val + 1 : ℕ) : ℝ) * ((l.val + 2 : ℕ) : ℝ))) : ℂ)

/-- The generalized Gell-Mann matrices. -/
noncomputable def matrix : Index N → Matrix (Fin N) (Fin N) ℂ
  | .inl p => single p.1.1 p.1.2 1 + single p.1.2 p.1.1 1
  | .inr (.inl p) => single p.1.1 p.1.2 (-Complex.I) + single p.1.2 p.1.1 Complex.I
  | .inr (.inr l) => diagNorm l • diagonal (diagProfile l)

/-!

## B. The diagonal profiles

-/

/-- The profile as a function of the position, `1` below `n`, `-n` at `n`, `0` above. -/
private def profile (n m : ℕ) : ℂ := if m < n then 1 else if m = n then -(n : ℂ) else 0

private lemma sum_range_profile {n : ℕ} :
    ∀ M, n < M → ∑ m ∈ Finset.range M, profile n m = 0 := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base =>
    rw [Finset.sum_range_succ, Finset.sum_congr rfl fun m hm => (show profile n m = 1 by
      simp [profile, Finset.mem_range.1 hm])]
    simp [profile]
  | succ M hM ih =>
    rw [Finset.sum_range_succ, ih]
    simp [profile, show ¬ M < n by omega, show M ≠ n by omega]

lemma sum_diagProfile (l : Fin (N - 1)) : ∑ m, diagProfile l m = 0 := by
  change ∑ m : Fin N, profile (l.val + 1) m.val = 0
  rw [Fin.sum_univ_eq_sum_range (fun m => profile (l.val + 1) m)]
  exact sum_range_profile N (by omega)

private lemma profile_mul_of_lt {n n' : ℕ} (h : n < n') (m : ℕ) :
    profile n m * profile n' m = profile n m := by
  unfold profile
  by_cases h1 : m < n
  · simp [h1, show m < n' by omega]
  · by_cases h2 : m = n
    · simp [h2, h]
    · simp [h1, h2]

private lemma profile_mul_self (n m : ℕ) :
    profile n m * profile n m = (if m < n then 1 else 0) + (if m = n then (n : ℂ) ^ 2 else 0) := by
  unfold profile
  by_cases h1 : m < n
  · simp [h1, show m ≠ n by omega]
  · by_cases h2 : m = n
    · simp [h2]
      ring
    · simp [h1, h2]

private lemma sum_range_indicator_lt {n : ℕ} :
    ∀ M, n ≤ M → ∑ m ∈ Finset.range M, (if m < n then (1 : ℂ) else 0) = n := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base =>
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℂ)) fun m hm => by
      simp [Finset.mem_range.1 hm]]
    simp
  | succ M hM ih =>
    rw [Finset.sum_range_succ, ih]
    simp [show ¬ M < n by omega]

/-- The diagonal profiles are orthogonal, with `∑ d_l (m)² = n (n + 1)` for `n = l + 1`. -/
lemma sum_diagProfile_mul (l l' : Fin (N - 1)) :
    ∑ m, diagProfile l m * diagProfile l' m
      = if l = l' then ((l.val + 1 : ℕ) : ℂ) * ((l.val + 2 : ℕ) : ℂ) else 0 := by
  change ∑ m : Fin N, profile (l.val + 1) m.val * profile (l'.val + 1) m.val = _
  rw [Fin.sum_univ_eq_sum_range (fun m => profile (l.val + 1) m * profile (l'.val + 1) m)]
  have hl := l.isLt
  have hl' := l'.isLt
  rcases lt_trichotomy l l' with h | rfl | h
  · have h' := Fin.lt_def.1 h
    simp only [h.ne, ↓reduceIte]
    simp_rw [profile_mul_of_lt (show l.val + 1 < l'.val + 1 by omega)]
    exact sum_range_profile N (by omega)
  · simp only [↓reduceIte]
    simp_rw [profile_mul_self, Finset.sum_add_distrib,
      sum_range_indicator_lt (n := l.val + 1) N (by omega), Finset.sum_ite_eq',
      Finset.mem_range, (show l.val + 1 < N by omega)]
    simp only [↓reduceIte]
    push_cast
    ring
  · have h' := Fin.lt_def.1 h
    simp only [h.ne', ↓reduceIte]
    simp_rw [mul_comm (profile (l.val + 1) _),
      profile_mul_of_lt (show l'.val + 1 < l.val + 1 by omega)]
    exact sum_range_profile N (by omega)

/-- The square of the normalization of the diagonal matrix of size `n = l + 1` is
  `2 / (n (n + 1))`. -/
lemma diagNorm_mul_self (l : Fin (N - 1)) :
    diagNorm l * diagNorm l * (((l.val + 1 : ℕ) : ℂ) * ((l.val + 2 : ℕ) : ℂ)) = 2 := by
  rw [diagNorm, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  have h1 : ((l.val : ℂ) + 1) ≠ 0 := by norm_cast
  have h2 : ((l.val : ℂ) + 2) ≠ 0 := by norm_cast
  push_cast
  field_simp

/-!

## C. Orthogonality

-/

/-- The trace of a symmetric Gell-Mann matrix against `X`. -/
lemma trace_matrix_inl_mul (p : {p : Fin N × Fin N // p.1 < p.2}) (X : Matrix (Fin N) (Fin N) ℂ) :
    (matrix (.inl p) * X).trace = X p.1.2 p.1.1 + X p.1.1 p.1.2 := by
  simp [matrix, Matrix.add_mul, trace_add, trace_single_mul]

/-- The trace of an antisymmetric Gell-Mann matrix against `X`. -/
lemma trace_matrix_inr_inl_mul (p : {p : Fin N × Fin N // p.1 < p.2})
    (X : Matrix (Fin N) (Fin N) ℂ) :
    (matrix (.inr (.inl p)) * X).trace
      = -Complex.I * X p.1.2 p.1.1 + Complex.I * X p.1.1 p.1.2 := by
  simp [matrix, Matrix.add_mul, trace_add, trace_single_mul]

/-- The trace of a diagonal Gell-Mann matrix against `X`. -/
lemma trace_matrix_inr_inr_mul (l : Fin (N - 1)) (X : Matrix (Fin N) (Fin N) ℂ) :
    (matrix (.inr (.inr l)) * X).trace = diagNorm l * ∑ m, diagProfile l m * X m m := by
  simp [matrix, trace, diagonal_mul, Finset.mul_sum]

/-- The entries of a symmetric Gell-Mann matrix. -/
lemma matrix_inl_apply (p : {p : Fin N × Fin N // p.1 < p.2}) (m n : Fin N) :
    matrix (.inl p) m n
      = (if p.1.1 = m ∧ p.1.2 = n then 1 else 0) + (if p.1.2 = m ∧ p.1.1 = n then 1 else 0) := by
  simp [matrix, single_apply]

/-- The entries of an antisymmetric Gell-Mann matrix. -/
lemma matrix_inr_inl_apply (p : {p : Fin N × Fin N // p.1 < p.2}) (m n : Fin N) :
    matrix (.inr (.inl p)) m n = (if p.1.1 = m ∧ p.1.2 = n then -Complex.I else 0)
      + (if p.1.2 = m ∧ p.1.1 = n then Complex.I else 0) := by
  simp [matrix, single_apply]

/-- The entries of a diagonal Gell-Mann matrix. -/
lemma matrix_inr_inr_apply (l : Fin (N - 1)) (m n : Fin N) :
    matrix (.inr (.inr l)) m n = if m = n then diagNorm l * diagProfile l m else 0 := by
  simp [matrix, diagonal_apply]

/-- Two ordered pairs `j < k` and `j' < k'` never match crosswise. -/
private lemma not_cross {j k j' k' : Fin N} (h : j < k) (h' : j' < k') :
    ¬ (j' = k ∧ k' = j) ∧ ¬ (k' = j ∧ j' = k) :=
  ⟨by rintro ⟨rfl, rfl⟩; exact lt_asymm h h', by rintro ⟨rfl, rfl⟩; exact lt_asymm h h'⟩

/-- The symmetric Gell-Mann matrices are orthogonal to all others and have norm `2`. -/
lemma trace_matrix_inl_mul_matrix (p : {p : Fin N × Fin N // p.1 < p.2}) (b : Index N) :
    (matrix (.inl p) * matrix b).trace = if .inl p = b then 2 else 0 := by
  obtain ⟨⟨j, k⟩, hjk⟩ := p
  rcases b with ⟨⟨j', k'⟩, hjk'⟩ | ⟨⟨j', k'⟩, hjk'⟩ | l' <;>
  simp only [trace_matrix_inl_mul, matrix_inl_apply, matrix_inr_inl_apply,
    matrix_inr_inr_apply, Sum.inl.injEq, reduceCtorEq, Subtype.mk.injEq, Prod.mk.injEq,
    ↓reduceIte]
  · simp only at hjk hjk'
    obtain ⟨e1, e2⟩ := not_cross hjk hjk'
    by_cases h : j = j' ∧ k = k'
    · obtain ⟨rfl, rfl⟩ := h
      simp only [e1, e2, and_self, ↓reduceIte]
      ring_nf
    · have h3 : ¬ (k' = k ∧ j' = j) := fun h' => h ⟨h'.2.symm, h'.1.symm⟩
      have h4 : ¬ (j' = j ∧ k' = k) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
      simp [e1, e2, h3, h4]
      exact fun h1 h2 => h ⟨h1, h2⟩
  · simp only at hjk hjk'
    obtain ⟨e1, e2⟩ := not_cross hjk hjk'
    by_cases h : j = j' ∧ k = k'
    · obtain ⟨rfl, rfl⟩ := h
      simp only [e1, e2, and_self, ↓reduceIte]
      ring_nf
    · have h3 : ¬ (k' = k ∧ j' = j) := fun h' => h ⟨h'.2.symm, h'.1.symm⟩
      have h4 : ¬ (j' = j ∧ k' = k) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
      simp [e1, e2, h3, h4]
  · simp only at hjk
    simp [hjk.ne, hjk.ne']

/-- The antisymmetric Gell-Mann matrices are orthogonal to all others and have norm `2`. -/
lemma trace_matrix_inr_inl_mul_matrix (p : {p : Fin N × Fin N // p.1 < p.2}) (b : Index N) :
    (matrix (.inr (.inl p)) * matrix b).trace = if .inr (.inl p) = b then 2 else 0 := by
  obtain ⟨⟨j, k⟩, hjk⟩ := p
  rcases b with ⟨⟨j', k'⟩, hjk'⟩ | ⟨⟨j', k'⟩, hjk'⟩ | l' <;>
  simp only [trace_matrix_inr_inl_mul, matrix_inl_apply, matrix_inr_inl_apply,
    matrix_inr_inr_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Subtype.mk.injEq,
    Prod.mk.injEq, ↓reduceIte]
  · simp only at hjk hjk'
    obtain ⟨e1, e2⟩ := not_cross hjk hjk'
    by_cases h : j = j' ∧ k = k'
    · obtain ⟨rfl, rfl⟩ := h
      simp only [e1, e2, and_self, ↓reduceIte]
      ring_nf
    · have h3 : ¬ (k' = k ∧ j' = j) := fun h' => h ⟨h'.2.symm, h'.1.symm⟩
      have h4 : ¬ (j' = j ∧ k' = k) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
      simp [e1, e2, h3, h4]
  · simp only at hjk hjk'
    obtain ⟨e1, e2⟩ := not_cross hjk hjk'
    by_cases h : j = j' ∧ k = k'
    · obtain ⟨rfl, rfl⟩ := h
      simp only [e1, e2, and_self, ↓reduceIte]
      ring_nf
      simp
    · have h3 : ¬ (k' = k ∧ j' = j) := fun h' => h ⟨h'.2.symm, h'.1.symm⟩
      have h4 : ¬ (j' = j ∧ k' = k) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
      simp [e1, e2, h3, h4]
      exact fun h1 h2 => h ⟨h1, h2⟩
  · simp only at hjk
    simp [hjk.ne, hjk.ne']

/-- The diagonal Gell-Mann matrices are orthogonal to all others and have norm `2`. -/
lemma trace_matrix_inr_inr_mul_matrix (l : Fin (N - 1)) (b : Index N) :
    (matrix (.inr (.inr l)) * matrix b).trace = if .inr (.inr l) = b then 2 else 0 := by
  rcases b with ⟨⟨j', k'⟩, hjk'⟩ | ⟨⟨j', k'⟩, hjk'⟩ | l' <;>
  simp only [trace_matrix_inr_inr_mul, matrix_inl_apply, matrix_inr_inl_apply,
    matrix_inr_inr_apply, Sum.inr.injEq, reduceCtorEq, ↓reduceIte]
  · simp only at hjk'
    rw [Finset.sum_eq_zero fun x _ => ?_, mul_zero]
    by_cases h1 : j' = x
    · subst h1
      simp [hjk'.ne']
    · simp [h1]
  · simp only at hjk'
    rw [Finset.sum_eq_zero fun x _ => ?_, mul_zero]
    by_cases h1 : j' = x
    · subst h1
      simp [hjk'.ne']
    · simp [h1]
  · have hs : ∑ x, diagProfile l x * (diagNorm l' * diagProfile l' x)
        = diagNorm l' * ∑ x, diagProfile l x * diagProfile l' x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hs, sum_diagProfile_mul]
    by_cases h : l = l'
    · subst h
      simp only [↓reduceIte]
      rw [← diagNorm_mul_self l]
      ring
    · simp [h]

/-- The generalized Gell-Mann matrices are orthogonal under the trace form:
  `tr (λ_a λ_b) = 2 δ_ab`. -/
lemma trace_matrix_mul_matrix (a b : Index N) :
    (matrix a * matrix b).trace = if a = b then 2 else 0 := by
  rcases a with p | p | l
  · exact trace_matrix_inl_mul_matrix p b
  · exact trace_matrix_inr_inl_mul_matrix p b
  · exact trace_matrix_inr_inr_mul_matrix l b

/-!

## D. The basis

-/

/-- The generalized Gell-Mann matrices are traceless. -/
lemma trace_matrix (a : Index N) : (matrix a).trace = 0 := by
  rcases a with ⟨⟨j, k⟩, hjk⟩ | ⟨⟨j, k⟩, hjk⟩ | l
  · simp only at hjk
    rw [matrix, trace_add, trace_single_eq_of_ne (h := hjk.ne),
      trace_single_eq_of_ne (h := hjk.ne'), add_zero]
  · simp only at hjk
    rw [matrix, trace_add, trace_single_eq_of_ne (h := hjk.ne),
      trace_single_eq_of_ne (h := hjk.ne'), add_zero]
  · simp [matrix, trace_smul, trace_diagonal, sum_diagProfile]

/-- The generalized Gell-Mann matrices are hermitian. -/
lemma conjTranspose_matrix (a : Index N) : (matrix a)ᴴ = matrix a := by
  rcases a with ⟨⟨j, k⟩, hjk⟩ | ⟨⟨j, k⟩, hjk⟩ | l
  · simp [matrix, conjTranspose_single, add_comm]
  · simp [matrix, conjTranspose_single, add_comm]
  · ext m n
    simp only [matrix, conjTranspose_apply, Matrix.smul_apply, diagonal_apply]
    by_cases h : m = n
    · subst h
      simp [diagNorm, diagProfile]
      split_ifs <;> simp
    · simp [h, Ne.symm h]

/-- The generalized Gell-Mann matrices as traceless matrices. -/
noncomputable def traceless (a : Index N) :
    ↥(LinearMap.ker (Matrix.traceLinearMap (Fin N) ℂ ℂ)) :=
  ⟨matrix a, trace_matrix a⟩

/-- The generalized Gell-Mann matrices are linearly independent, by orthogonality. -/
lemma linearIndependent_traceless : LinearIndependent ℂ (traceless (N := N)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  have h := congrArg (fun x : ↥(LinearMap.ker (Matrix.traceLinearMap (Fin N) ℂ ℂ)) =>
    (matrix a * x.1).trace) hg
  simp only [Submodule.coe_sum, Submodule.coe_smul, traceless, Matrix.mul_sum,
    Matrix.mul_smul, trace_sum, trace_smul, trace_matrix_mul_matrix, smul_eq_mul, mul_ite,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ZeroMemClass.coe_zero,
    trace_zero] at h
  simpa using h

/-- There are `N² - 1` ordered pairs with `j < k`, counted twice, and `N - 1` diagonal labels:
  `2 #{j < k} + N = N²`. -/
lemma two_mul_card_lt_add :
    2 * Fintype.card {p : Fin N × Fin N // p.1 < p.2} + N = N * N := by
  have h1 : Fintype.card {p : Fin N × Fin N // p.1 < p.2}
      = Fintype.card {p : Fin N × Fin N // p.2 < p.1} :=
    Fintype.card_congr ((Equiv.prodComm _ _).subtypeEquiv fun _ => Iff.rfl)
  have h2 : Fintype.card {p : Fin N × Fin N // p.1 = p.2} = N := by
    rw [Fintype.card_subtype, show (Finset.univ.filter fun p : Fin N × Fin N => p.1 = p.2)
      = Finset.univ.diag by ext; simp [Finset.mem_diag], Finset.diag_card, Finset.card_univ,
      Fintype.card_fin]
  have h3 : Fintype.card {p : Fin N × Fin N // p.1 < p.2}
      + Fintype.card {p : Fin N × Fin N // p.2 < p.1}
      + Fintype.card {p : Fin N × Fin N // p.1 = p.2} = N * N := by
    simp only [Fintype.card_subtype, Finset.card_filter, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun p _ => (show ((if p.1 < p.2 then 1 else 0) +
      (if p.2 < p.1 then 1 else 0) + (if p.1 = p.2 then 1 else 0) : ℕ) = 1 by
        rcases lt_trichotomy p.1 p.2 with h | h | h
        · simp [h, lt_asymm h, h.ne]
        · simp [h]
        · simp [h, lt_asymm h, h.ne'])]
    simp
  omega

/-- The traceless `N × N` matrices have dimension `N² - 1`. -/
lemma finrank_traceless :
    finrank ℂ ↥(LinearMap.ker (Matrix.traceLinearMap (Fin N) ℂ ℂ)) = N * N - 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact Nat.le_zero.1 ((Submodule.finrank_le _).trans (by rw [Module.finrank_matrix]; simp))
  · have hsurj : LinearMap.range (Matrix.traceLinearMap (Fin N) ℂ ℂ) = ⊤ :=
      LinearMap.range_eq_top.2 fun c => ⟨single ⟨0, hN⟩ ⟨0, hN⟩ c, by simp⟩
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin N) ℂ ℂ)
    rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_matrix, Module.finrank_self,
      Fintype.card_fin] at h
    omega

lemma card_index : Fintype.card (Index N)
    = finrank ℂ ↥(LinearMap.ker (Matrix.traceLinearMap (Fin N) ℂ ℂ)) := by
  have h := two_mul_card_lt_add (N := N)
  rw [finrank_traceless, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · omega

/-- **The generalized Gell-Mann basis** of the traceless complex `N × N` matrices. -/
noncomputable def basis : Basis (Index N) ℂ ↥(LinearMap.ker (Matrix.traceLinearMap (Fin N) ℂ ℂ)) :=
  basisOfLinearIndependentOfCardEqFinrank' _ linearIndependent_traceless card_index

@[simp]
lemma basis_apply_val (a : Index N) : (basis a).1 = matrix a := by
  simp [basis, traceless]

/-- The coordinates of a traceless matrix in the Gell-Mann basis are read off by the trace form,
  `x = ∑ (tr (λ_a x) / 2) λ_a`. -/
lemma basis_repr_apply (x : ↥(LinearMap.ker (Matrix.traceLinearMap (Fin N) ℂ ℂ))) (a : Index N) :
    basis.repr x a = (matrix a * x.1).trace / 2 := by
  conv_rhs => rw [← basis.sum_repr x]
  simp only [Submodule.coe_sum, Submodule.coe_smul, basis_apply_val, Matrix.mul_sum,
    Matrix.mul_smul, trace_sum, trace_smul, trace_matrix_mul_matrix, smul_eq_mul, mul_ite,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  ring

/-!

## E. The real basis of `su(N)`

-/

/-- The generalized Gell-Mann matrices as elements of the real Lie algebra `su(N)`. -/
noncomputable def hermitian (a : Index N) : SUAlgebraOver ℂ N :=
  SUAlgebraOver.ofMatrix (matrix a) (conjTranspose_matrix a) (trace_matrix a)

/-- The generalized Gell-Mann matrices are linearly independent over the reals. -/
lemma linearIndependent_hermitian : LinearIndependent ℝ (hermitian (N := N)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  have h := congrArg (fun x : SUAlgebraOver ℂ N => (matrix a * x.1).trace) hg
  simp only [Submodule.coe_sum, Submodule.coe_smul, hermitian, SUAlgebraOver.ofMatrix_val,
    Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, trace_matrix_mul_matrix, smul_ite,
    smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ZeroMemClass.coe_zero,
    Matrix.mul_zero, trace_zero] at h
  simpa [Complex.real_smul] using h

/-- The trace pairing of two hermitian matrices is real. -/
lemma trace_mul_ofReal_re {A H : Matrix (Fin N) (Fin N) ℂ} (hA : Aᴴ = A) (hH : Hᴴ = H) :
    (((A * H).trace.re : ℝ) : ℂ) = (A * H).trace := by
  refine Complex.conj_eq_iff_re.1 ?_
  change star (A * H).trace = _
  rw [← trace_conjTranspose, conjTranspose_mul, hA, hH, trace_mul_comm]

/-- A traceless hermitian matrix is the real combination `∑ (tr (λ_a H) / 2) λ_a` of the
  generalized Gell-Mann matrices. -/
lemma eq_sum_re_trace_smul_hermitian (H : SUAlgebraOver ℂ N) :
    ∑ a, ((matrix a * H.1).trace.re / 2) • hermitian a = H := by
  refine SUAlgebraOver.ext ?_
  have hH : H.1 ∈ LinearMap.ker (Matrix.traceLinearMap (Fin N) ℂ ℂ) := H.trace_val
  have h := congrArg Subtype.val (basis.sum_repr ⟨H.1, hH⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, basis_apply_val, basis_repr_apply] at h
  simp only [Submodule.coe_sum, Submodule.coe_smul, hermitian, SUAlgebraOver.ofMatrix_val]
  conv_rhs => rw [← h]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Complex.coe_smul, Complex.ofReal_div, trace_mul_ofReal_re (conjTranspose_matrix a)
    H.star_val]
  rfl

/-- **The generalized Gell-Mann basis** of the real Lie algebra `su(N)`. -/
noncomputable def realBasis : Basis (Index N) ℝ (SUAlgebraOver ℂ N) :=
  Basis.mk linearIndependent_hermitian fun H _ =>
    (Submodule.mem_span_range_iff_exists_fun ℝ).2 ⟨_, eq_sum_re_trace_smul_hermitian H⟩

@[simp]
lemma realBasis_apply_val (a : Index N) : (realBasis a).1 = matrix a := by
  simp [realBasis, hermitian]

end GellMann
