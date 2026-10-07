/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Physlib.Relativity.PauliMatrices.Basic
public import Physlib.Mathematics.Groups.SpecialUnitary.LieAlgebra.Adjoint
/-!

# The generalized Gell-Mann matrices

The generalized Gell-Mann matrices, aswell as the specific results in the n = 3 case.

## i. Overview

The generalized Gell-Mann matrices are the standard basis of `su(n)`, generalizing the Pauli
matrices (`n = 2`) and the Gell-Mann matrices (`n = 3`). They are labelled by `GellMannIndex n`,
which has `n² - 1` elements, of three kinds (A):

- for `p < q` the symmetric matrix `E_pq + E_qp`,
- for `p < q` the antisymmetric matrix `-i E_pq + i E_qp`,
- for `1 ≤ m ≤ n - 1` the diagonal matrix `√(2 / (m (m + 1))) (E_00 + ⋯ + E_(m-1)(m-1) - m E_mm)`.

They are orthogonal under the contraction, `adjointContr (λ_i ⊗ λ_j) = tr (λ_i λ_j) = 2 δ_ij`, and
so linearly independent. For `n = 3` they are the Gell-Mann matrices `λ₁, …, λ₈` (B).

As there are as many as the dimension `n² - 1` of `su(n)`, they form a basis, whose coordinates
are the contractions `adjointContr (λ_i ⊗ x) / 2`, and its base change is a basis of the
complexification (C). In this basis the adjoint action of `g ∈ SU(n)` is a real orthogonal matrix,
with entries `re tr (λ_i g λ_j g†) / 2` (D).

## ii. Key results

- `SULieAlgebra.GellMannIndex` : the labels of the generalized Gell-Mann matrices.
- `SULieAlgebra.gellMannMatrices` : the generalized Gell-Mann matrices.
- `SULieAlgebra.adjointContr_gellMannMatrices` : the Gell-Mann matrices are orthogonal.
- `SULieAlgebra.gellMannMatrices_two` : for `n = 2`, the Pauli matrices `σ₁, σ₂, σ₃`.
- `SULieAlgebra.gellMannMatrices_three` : for `n = 3`, the Gell-Mann matrices `λ₁, …, λ₈`.
- `SULieAlgebra.gellMannBasis` : the Gell-Mann basis of `su(n)`.
- `SULieAlgebra.gellMannBasisℂ` : the Gell-Mann basis of the complexification of `su(n)`.
- `SULieAlgebra.adjointGellMannBasis` : the matrix of the adjoint action in the Gell-Mann basis.
- `SULieAlgebra.adjointGellMannBasis_transpose_mul_self` : that matrix is orthogonal.
- `SULieAlgebra.gellMannStructureConst` : the structure constants, `[λ_a, λ_b] = 2 i f_abc λ_c`.

## iii. Table of contents

- A. The indexing type of the Gell-Mann matrices
  - A.1. The `n = 2` and `n = 3` equivalences
  - A.2. The cardinality of `GellMannIndex`
- B. The generalized Gell-Mann matrices
  - B.1. Symmetry properties
  - B.2. Explicit forms
  - B.3. Orthogonality
    - B.3.1. Between different types
    - B.3.2. Between the same type
    - B.3.3. Overall
  - B.4. Linear independence
  - B.5. The Pauli and Gell-Mann matrices
- C. The Gell-Mann basis
  - C.1. The basis of `su(n)`
  - C.2. The basis of the complexification
- D. The adjoint action in the Gell-Mann basis
- E. The structure constants

## iv. References

* https://mathworld.wolfram.com/GeneralizedGell-MannMatrix.html

-/

@[expose] public section

namespace SULieAlgebra

open Matrix

/-!

## A. The indexing type of the Gell-Mann matrices

-/

/-- The indexing type of the Gell-Mann matrices. -/
inductive GellMannIndex (n : ℕ)
  | symm (p : Fin n) (q : Fin n) (h : p < q) : GellMannIndex n
  | antisymm (p : Fin n) (q : Fin n) (h : p < q) : GellMannIndex n
  | diag (l : Fin (n - 1)) : GellMannIndex n
deriving DecidableEq, Repr, Fintype

/-!

### A.1. The `n = 2` and `n = 3` equivalences

-/

/-- For `n = 2`, the labelling of the generalized Gell-Mann matrices as the Pauli matrices
  `σ₁, σ₂, σ₃` (as `0, 1, 2`): the symmetric, antisymmetric and diagonal matrices. -/
def GellMannIndex.equivTwo : GellMannIndex 2 ≃ Fin 3 where
  toFun
    | .symm _ _ _ => 0
    | .antisymm _ _ _ => 1
    | .diag _ => 2
  invFun := ![.symm 0 1 (by simp), .antisymm 0 1 (by simp), .diag 0]
  left_inv := by
    rintro (⟨p, q, h⟩ | ⟨p, q, h⟩ | l)
    · fin_cases p <;> fin_cases q <;> first | rfl | simp at h
    · fin_cases p <;> fin_cases q <;> first | rfl | simp at h
    · fin_cases l
      rfl
  right_inv i := by fin_cases i <;> rfl

/-- For `n = 3`, the labelling of the Gell-Mann matrices in the standard order `λ₁, …, λ₈`
  (as `0, …, 7`): `λ₁, λ₂, λ₃` are the symmetric, antisymmetric and diagonal matrices of the first
  two coordinates, `λ₄, λ₅` the symmetric and antisymmetric ones of the coordinates `0, 2`,
  `λ₆, λ₇` those of the coordinates `1, 2`, and `λ₈` the second diagonal matrix. -/
def GellMannIndex.equivThree : GellMannIndex 3 ≃ Fin 8 where
  toFun
    | .symm p q _ => if p.1 = 0 then (if q.1 = 1 then 0 else 3) else 5
    | .antisymm p q _ => if p.1 = 0 then (if q.1 = 1 then 1 else 4) else 6
    | .diag l => if l.1 = 0 then 2 else 7
  invFun := ![.symm 0 1 (by simp), .antisymm 0 1 (by simp), .diag 0, .symm 0 2 (by simp),
    .antisymm 0 2 (by simp), .symm 1 2 (by simp), .antisymm 1 2 (by simp), .diag 1]
  left_inv := by
    rintro (⟨p, q, h⟩ | ⟨p, q, h⟩ | l)
    · fin_cases p <;> fin_cases q <;> first | rfl | simp [Fin.lt_def] at h
    · fin_cases p <;> fin_cases q <;> first | rfl | simp [Fin.lt_def] at h
    · fin_cases l <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-!

### A.2. The cardinality of `GellMannIndex`

-/

/-- There are `n² - 1` generalized Gell-Mann matrices: `n (n - 1) / 2` symmetric ones, as many
  antisymmetric ones, and `n - 1` diagonal ones. -/
lemma gellMannIndex_card {n : ℕ} : Fintype.card (GellMannIndex n) = n ^ 2 - 1 := by
  let e : GellMannIndex n ≃ {p : Fin n × Fin n // p.1 < p.2} ⊕ {p : Fin n × Fin n // p.1 < p.2} ⊕
      Fin (n - 1) :=
    { toFun
        | .symm p q h => .inl ⟨(p, q), h⟩
        | .antisymm p q h => .inr (.inl ⟨(p, q), h⟩)
        | .diag l => .inr (.inr l)
      invFun
        | .inl x => .symm x.1.1 x.1.2 x.2
        | .inr (.inl x) => .antisymm x.1.1 x.1.2 x.2
        | .inr (.inr l) => .diag l
      left_inv := by rintro (_ | _ | _) <;> rfl
      right_inv := by rintro (⟨⟨p, q⟩, h⟩ | ⟨⟨p, q⟩, h⟩ | l) <;> rfl }
  -- the pairs `p < q`, `q < p` and `p = q` together make up all `n²` pairs
  have h1 : Fintype.card {p : Fin n × Fin n // p.1 < p.2}
      = Fintype.card {p : Fin n × Fin n // p.2 < p.1} :=
    Fintype.card_congr ((Equiv.prodComm _ _).subtypeEquiv fun _ => Iff.rfl)
  have h2 : Fintype.card {p : Fin n × Fin n // p.1 = p.2} = n := by
    rw [Fintype.card_subtype, show (Finset.univ.filter fun p : Fin n × Fin n => p.1 = p.2)
      = Finset.univ.diag by ext; simp [Finset.mem_diag], Finset.diag_card, Finset.card_univ,
      Fintype.card_fin]
  have h3 : Fintype.card {p : Fin n × Fin n // p.1 < p.2}
      + Fintype.card {p : Fin n × Fin n // p.2 < p.1}
      + Fintype.card {p : Fin n × Fin n // p.1 = p.2} = n * n := by
    simp only [Fintype.card_subtype, Finset.card_filter, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun p _ => (show ((if p.1 < p.2 then 1 else 0) +
      (if p.2 < p.1 then 1 else 0) + (if p.1 = p.2 then 1 else 0) : ℕ) = 1 by
        rcases lt_trichotomy p.1 p.2 with h | h | h
        · simp [h, lt_asymm h, h.ne]
        · simp [h]
        · simp [h, lt_asymm h, h.ne'])]
    simp
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, sq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · omega

/-!

## B. The generalized Gell-Mann matrices

-/

/-- The generalized Gell-Mann matrices, as elements of `su(n)`:

- for `p < q`, the symmetric matrix `E_pq + E_qp`,
- for `p < q`, the antisymmetric matrix `-i E_pq + i E_qp`,
- for `l : Fin (n - 1)`, with `m = l + 1`, the diagonal matrix
  `√(2 / (m (m + 1))) (E_00 + ⋯ + E_(m-1)(m-1) - m E_mm)`. -/
noncomputable def gellMannMatrices {n : ℕ} : GellMannIndex n → SULieAlgebra n ℂ
  | .symm p q h => ofMatrix (single p q 1 + single q p 1)
      (by simp [star_eq_conjTranspose, conjTranspose_single, add_comm])
      (by rw [trace_add, trace_single_eq_of_ne _ _ _ h.ne, trace_single_eq_of_ne _ _ _ h.ne',
        add_zero])
  | .antisymm p q h => ofMatrix (single p q (-Complex.I) + single q p Complex.I)
      (by simp [star_eq_conjTranspose, conjTranspose_single, add_comm])
      (by rw [trace_add, trace_single_eq_of_ne _ _ _ h.ne, trace_single_eq_of_ne _ _ _ h.ne',
        add_zero])
  | .diag l => ofMatrix (diagonal fun x =>
      (Real.sqrt (2 / (((l.1 + 1 : ℕ) : ℝ) * ((l.1 + 1 : ℕ) + 1))) : ℂ) *
        if x.1 < l.1 + 1 then 1 else if x.1 = l.1 + 1 then -((l.1 + 1 : ℕ) : ℂ) else 0)
      (by
        ext x y
        simp only [star_apply, diagonal_apply]
        split_ifs <;> simp_all [Complex.conj_ofReal]
        omega)
      (by
        have hl := l.2
        rw [trace_diagonal, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun x =>
          if x < l.1 + 1 then (1 : ℂ) else if x = l.1 + 1 then -((l.1 + 1 : ℕ) : ℂ) else 0),
          Finset.sum_congr rfl fun x _ => (show (if x < l.1 + 1 then (1 : ℂ) else if x = l.1 + 1
            then -((l.1 + 1 : ℕ) : ℂ) else 0) = (if x < l.1 + 1 then 1 else 0) +
              if x = l.1 + 1 then -((l.1 + 1 : ℕ) : ℂ) else 0 by
              split_ifs <;> first | omega | simp),
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_boole,
          show (Finset.range n).filter (· < l.1 + 1) = Finset.range (l.1 + 1) by
            ext; simp; omega, Finset.card_range]
        simp [show l.1 + 1 < n by omega])

/-!

### B.1. Symmetry properties

-/

/-- The symmetric generalized Gell-Mann matrices are symmetric. -/
lemma gellMannMatrices_symm_isSymm {n : ℕ} (p q : Fin n) (h : p < q) :
    Matrix.IsSymm (gellMannMatrices (.symm p q h)).1 := by
  simp [gellMannMatrices, Matrix.IsSymm, transpose_single, add_comm]

/-- The antisymmetric generalized Gell-Mann matrices are antisymmetric. -/
lemma gellMannMatrices_antisymm_transpose {n : ℕ} (p q : Fin n) (h : p < q) :
    (gellMannMatrices (.antisymm p q h)).1ᵀ = -(gellMannMatrices (.antisymm p q h)).1 := by
  rw [gellMannMatrices, val_ofMatrix, transpose_add, transpose_single, transpose_single, neg_add,
    ← single_neg, ← single_neg, neg_neg, add_comm]

/-- The diagonal generalized Gell-Mann matrices are diagonal. -/
lemma gellMannMatrices_diag_isDiag {n : ℕ} (l : Fin (n - 1)) :
    Matrix.IsDiag (gellMannMatrices (.diag l)).1 :=
  isDiag_diagonal _

/-!

### B.2. Explicit forms

-/

lemma gellMannMatrices_symm_val_eq {n : ℕ} (p q : Fin n) (h : p < q) :
    (gellMannMatrices (.symm p q h)).1 = single p q 1 + single q p 1 := by rfl

lemma gellMannMatrices_antisymm_val_eq {n : ℕ} (p q : Fin n) (h : p < q) :
    (gellMannMatrices (.antisymm p q h)).1 = single p q (-Complex.I) + single q p Complex.I := by
  rfl

lemma gellMannMatrices_diag_val_eq {n : ℕ} (l : Fin (n - 1)) :
    (gellMannMatrices (.diag l)).1 = diagonal fun x =>
      (Real.sqrt (2 / (((l.1 + 1 : ℕ) : ℝ) * ((l.1 + 1 : ℕ) + 1))) : ℂ) *
        if x.1 < l.1 + 1 then 1 else if x.1 = l.1 + 1 then -((l.1 + 1 : ℕ) : ℂ) else 0 := by
  rfl

/-!

### B.3. Orthogonality

-/

/-!

#### B.3.1. Between different types

-/

@[simp]
lemma adjointContr_gellMannMatrices_symm_antisymm_eq_zero {n : ℕ} (p q : Fin n) (h : p < q)
    (p' q' : Fin n) (h' : p' < q') :
    adjointContr (gellMannMatrices (.symm p q h) ⊗ₜ gellMannMatrices (.antisymm p' q' h')) = 0 := by
  simp only [adjointContr_tmul, gellMannMatrices_symm_val_eq, gellMannMatrices_antisymm_val_eq,
    Matrix.add_mul, trace_add, trace_single_mul, Matrix.add_apply, single_apply, Fin.ext_iff,
    smul_eq_mul]
  split_ifs <;> norm_num

@[simp]
lemma adjointContr_gellMannMatrices_symm_diag_eq_zero {n : ℕ} (p q : Fin n) (h : p < q)
    (l : Fin (n - 1)) :
    adjointContr (gellMannMatrices (.symm p q h) ⊗ₜ gellMannMatrices (.diag l)) = 0 := by
  rw [adjointContr_tmul, gellMannMatrices_symm_val_eq, gellMannMatrices_diag_val_eq]
  simp [Matrix.add_mul, trace_add, trace_single_mul, h.ne, h.ne']

@[simp]
lemma adjointContr_gellMannMatrices_antisymm_symm_eq_zero {n : ℕ} (p q : Fin n) (h : p < q)
    (p' q' : Fin n) (h' : p' < q') :
    adjointContr (gellMannMatrices (.antisymm p q h) ⊗ₜ gellMannMatrices (.symm p' q' h')) = 0 := by
  simp only [adjointContr_tmul, gellMannMatrices_antisymm_val_eq, gellMannMatrices_symm_val_eq,
    Matrix.add_mul, trace_add, trace_single_mul, Matrix.add_apply, single_apply, Fin.ext_iff,
    smul_eq_mul]
  split_ifs <;> norm_num

@[simp]
lemma adjointContr_gellMannMatrices_antisymm_diag_eq_zero {n : ℕ} (p q : Fin n) (h : p < q)
    (l : Fin (n - 1)) :
    adjointContr (gellMannMatrices (.antisymm p q h) ⊗ₜ gellMannMatrices (.diag l)) = 0 := by
  rw [adjointContr_tmul, gellMannMatrices_antisymm_val_eq, gellMannMatrices_diag_val_eq]
  simp [Matrix.add_mul, trace_add, trace_single_mul, h.ne, h.ne']

@[simp]
lemma adjointContr_gellMannMatrices_diag_symm_eq_zero {n : ℕ} (l : Fin (n - 1)) (p q : Fin n)
    (h : p < q) :
    adjointContr (gellMannMatrices (.diag l) ⊗ₜ gellMannMatrices (.symm p q h)) = 0 := by
  rw [adjointContr_tmul, gellMannMatrices_diag_val_eq, gellMannMatrices_symm_val_eq]
  simp [Matrix.mul_add, trace_add, trace_mul_single, h.ne, h.ne']

@[simp]
lemma adjointContr_gellMannMatrices_diag_antisymm_eq_zero {n : ℕ} (l : Fin (n - 1)) (p q : Fin n)
    (h : p < q) :
    adjointContr (gellMannMatrices (.diag l) ⊗ₜ gellMannMatrices (.antisymm p q h)) = 0 := by
  rw [adjointContr_tmul, gellMannMatrices_diag_val_eq, gellMannMatrices_antisymm_val_eq]
  simp [Matrix.mul_add, trace_add, trace_mul_single, h.ne, h.ne']

/-!

#### B.3.2. Between the same type

-/

lemma adjointContr_gellMannMatrices_symm_orthogonal {n : ℕ} (p q : Fin n) (h : p < q)
    (p' q' : Fin n) (h' : p' < q') :
    adjointContr (gellMannMatrices (.symm p q h) ⊗ₜ gellMannMatrices (.symm p' q' h')) =
      if p = p' ∧ q = q' then 2 else 0 := by
  have := Fin.lt_def.1 h
  have := Fin.lt_def.1 h'
  simp only [adjointContr_tmul, gellMannMatrices_symm_val_eq, Matrix.add_mul, trace_add,
    trace_single_mul, Matrix.add_apply, single_apply, Fin.ext_iff, smul_eq_mul]
  split_ifs <;> (try norm_num) <;> omega

lemma adjointContr_gellMannMatrices_antisymm_orthogonal {n : ℕ} (p q : Fin n) (h : p < q)
    (p' q' : Fin n) (h' : p' < q') :
    adjointContr (gellMannMatrices (.antisymm p q h) ⊗ₜ gellMannMatrices (.antisymm p' q' h')) =
      if p = p' ∧ q = q' then 2 else 0 := by
  have := Fin.lt_def.1 h
  have := Fin.lt_def.1 h'
  simp only [adjointContr_tmul, gellMannMatrices_antisymm_val_eq, Matrix.add_mul, trace_add,
    trace_single_mul, Matrix.add_apply, single_apply, Fin.ext_iff, smul_eq_mul]
  split_ifs <;> (try norm_num) <;> omega

lemma adjointContr_gellMannMatrices_diag_orthogonal {n : ℕ} (l l' : Fin (n - 1)) :
    adjointContr (gellMannMatrices (.diag l) ⊗ₜ gellMannMatrices (.diag l')) =
      if l = l' then 2 else 0 := by
  apply Complex.ofReal_injective
  rw [ofReal_adjointContr_tmul, gellMannMatrices_diag_val_eq, gellMannMatrices_diag_val_eq,
    diagonal_mul_diagonal, trace_diagonal, show ((if l = l' then (2 : ℝ) else 0 : ℝ) : ℂ)
      = if l.1 + 1 = l'.1 + 1 then 2 else 0 by
        simp only [add_left_inj, ← Fin.ext_iff]
        split_ifs <;> simp]
  obtain ⟨hm0, hmn⟩ : 0 < l.1 + 1 ∧ l.1 + 1 < n := by have := l.2; omega
  obtain ⟨hm0', hmn'⟩ : 0 < l'.1 + 1 ∧ l'.1 + 1 < n := by have := l'.2; omega
  generalize l.1 + 1 = m at *
  generalize l'.1 + 1 = m' at *
  have hsum : ∑ x : Fin n, (if x.1 < m then (1 : ℂ) else if x.1 = m then -(m : ℂ) else 0) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun x => if x < m then (1 : ℂ) else if x = m then -(m : ℂ)
      else 0), Finset.sum_congr rfl fun x _ => (show (if x < m then (1 : ℂ) else if x = m then
        -(m : ℂ) else 0) = (if x < m then 1 else 0) + if x = m then -(m : ℂ) else 0 by
          split_ifs <;> first | omega | simp), Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_boole, show (Finset.range n).filter (· < m) = Finset.range m by ext; simp; omega,
      Finset.card_range]
    simp [hmn]
  have hsum' : ∑ x : Fin n,
      (if x.1 < m' then (1 : ℂ) else if x.1 = m' then -(m' : ℂ) else 0) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun x => if x < m' then (1 : ℂ) else if x = m' then -(m' : ℂ)
      else 0), Finset.sum_congr rfl fun x _ => (show (if x < m' then (1 : ℂ) else if x = m' then
        -(m' : ℂ) else 0) = (if x < m' then 1 else 0) + if x = m' then -(m' : ℂ) else 0 by
          split_ifs <;> first | omega | simp), Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_boole, show (Finset.range n).filter (· < m') = Finset.range m' by
        ext; simp; omega, Finset.card_range]
    simp [hmn']
  set c := (Real.sqrt (2 / ((m : ℝ) * (m + 1))) : ℂ) with hc
  set c' := (Real.sqrt (2 / ((m' : ℝ) * (m' + 1))) : ℂ) with hc'
  rcases lt_trichotomy m m' with h | rfl | h
  · rw [ite_eq_right h.ne, Finset.sum_congr rfl (g := fun x : Fin n => c * c' *
      if x.1 < m then 1 else if x.1 = m then -(m : ℂ) else 0) fun x _ => by
        split_ifs <;> first | omega | ring, ← Finset.mul_sum, hsum, mul_zero]
  · rw [ite_eq_left rfl, Finset.sum_congr rfl (g := fun x : Fin n => c ^ 2 *
      ((if x.1 < m then 1 else 0) + if x.1 = m then (m : ℂ) ^ 2 else 0)) fun x _ => by
        split_ifs <;> first | omega | ring, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range
        (fun x => (if x < m then (1 : ℂ) else 0) + if x = m then (m : ℂ) ^ 2 else 0),
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_boole,
      show (Finset.range n).filter (· < m) = Finset.range m by ext; simp; omega,
      Finset.card_range, ite_eq_left (Finset.mem_range.2 hmn), hc, ← Complex.ofReal_pow,
      Real.sq_sqrt (by positivity)]
    have : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
    have : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    push_cast
    field_simp
    ring
  · rw [ite_eq_right h.ne', Finset.sum_congr rfl (g := fun x : Fin n => c * c' *
      if x.1 < m' then 1 else if x.1 = m' then -(m' : ℂ) else 0) fun x _ => by
        split_ifs <;> first | omega | ring, ← Finset.mul_sum, hsum', mul_zero]

/-!

#### B.3.3. Overall

-/

lemma adjointContr_gellMannMatrices {n : ℕ} (i j : GellMannIndex n) :
    adjointContr (gellMannMatrices i ⊗ₜ gellMannMatrices j) = if i = j then 2 else 0 := by
  rcases i with ⟨p, q, h⟩ | ⟨p, q, h⟩ | l <;> rcases j with ⟨p', q', h'⟩ | ⟨p', q', h'⟩ | l' <;>
    simp only [adjointContr_gellMannMatrices_symm_orthogonal,
      adjointContr_gellMannMatrices_antisymm_orthogonal,
      adjointContr_gellMannMatrices_diag_orthogonal,
      adjointContr_gellMannMatrices_symm_antisymm_eq_zero,
      adjointContr_gellMannMatrices_symm_diag_eq_zero,
      adjointContr_gellMannMatrices_antisymm_symm_eq_zero,
      adjointContr_gellMannMatrices_antisymm_diag_eq_zero,
      adjointContr_gellMannMatrices_diag_symm_eq_zero,
      adjointContr_gellMannMatrices_diag_antisymm_eq_zero, GellMannIndex.symm.injEq,
      GellMannIndex.antisymm.injEq, GellMannIndex.diag.injEq, reduceCtorEq, ↓reduceIte]

/-!

### B.4. Linear independence

-/

/-- The generalized Gell-Mann matrices are linearly independent over `ℝ`, being orthogonal under
  the contraction. -/
lemma linearIndependent_gellMannMatrices {n : ℕ} :
    LinearIndependent ℝ (gellMannMatrices (n := n)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (fun x => adjointContr (gellMannMatrices i ⊗ₜ x)) hg
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum, map_smul,
    adjointContr_gellMannMatrices, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, TensorProduct.tmul_zero, map_zero] at h
  simpa using h

/-!

### B.5. The Pauli and Gell-Mann matrices

-/

/-- For `n = 2` the generalized Gell-Mann matrices are the Pauli matrices `σ₁, σ₂, σ₃`, labelled
  by `GellMannIndex.equivTwo`. -/
lemma gellMannMatrices_two (i : Fin 3) :
    (gellMannMatrices (GellMannIndex.equivTwo.symm i)).1 = PauliMatrix.pauliMatrix (Sum.inr i) := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [GellMannIndex.equivTwo, gellMannMatrices, PauliMatrix.pauliMatrix, one_add_one_eq_two]

/-- For `n = 3` the generalized Gell-Mann matrices are the Gell-Mann matrices `λ₁, …, λ₈`, labelled
  in the standard order by `GellMannIndex.equivThree`. -/
lemma gellMannMatrices_three :
    (fun i => (gellMannMatrices (GellMannIndex.equivThree.symm i)).1) =
    ![!![0, 1, 0; 1, 0, 0; 0, 0, 0],
      !![0, -Complex.I, 0; Complex.I, 0, 0; 0, 0, 0],
      !![1, 0, 0; 0, -1, 0; 0, 0, 0],
      !![0, 0, 1; 0, 0, 0; 1, 0, 0],
      !![0, 0, -Complex.I; 0, 0, 0; Complex.I, 0, 0],
      !![0, 0, 0; 0, 0, 1; 0, 1, 0],
      !![0, 0, 0; 0, 0, -Complex.I; 0, Complex.I, 0],
      (1 / Real.sqrt 3 : ℂ) • !![1, 0, 0; 0, 1, 0; 0, 0, -2]] := by
  funext i
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [GellMannIndex.equivThree, gellMannMatrices, one_add_one_eq_two, div_mul_eq_div_div,
      show (2 : ℝ) + 1 = 3 by norm_num]

/-!

## C. The Gell-Mann basis

### C.1. The basis of `su(n)`

-/

/-- The generalized Gell-Mann basis of `su(n)`. -/
noncomputable def gellMannBasis {n : ℕ} : Module.Basis (GellMannIndex n) ℝ (SULieAlgebra n ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank' _ linearIndependent_gellMannMatrices
    (by rw [gellMannIndex_card, finrank_eq])

@[simp]
lemma gellMannBasis_apply {n : ℕ} (i : GellMannIndex n) : gellMannBasis i = gellMannMatrices i := by
  simp [gellMannBasis]

/-- The coordinates in the Gell-Mann basis are the contractions with the Gell-Mann matrices,
  `x = ∑ (adjointContr (λ_i ⊗ x) / 2) λ_i`. -/
lemma gellMannBasis_repr_apply {n : ℕ} (x : SULieAlgebra n ℂ) (i : GellMannIndex n) :
    gellMannBasis.repr x i = adjointContr (gellMannMatrices i ⊗ₜ x) / 2 := by
  conv_rhs => rw [← gellMannBasis.sum_repr x]
  simp only [gellMannBasis_apply, TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum,
    map_smul, adjointContr_gellMannMatrices, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  ring

/-!

### C.2. The basis of the complexification

-/

/-- The generalized Gell-Mann basis `1 ⊗ λ_i` of the complexification `ℂ ⊗[ℝ] su(n)`. -/
noncomputable def gellMannBasisℂ {n : ℕ} : Module.Basis (GellMannIndex n) ℂ (Complexification n) :=
  Algebra.TensorProduct.basis ℂ gellMannBasis

lemma gellMannBasisℂ_apply {n : ℕ} (i : GellMannIndex n) :
    gellMannBasisℂ i = 1 ⊗ₜ gellMannMatrices i := by
  rw [gellMannBasisℂ, Algebra.TensorProduct.basis_apply, gellMannBasis_apply]

@[simp]
lemma toMatrixℂ_gellMannBasisℂ {n : ℕ} (i : GellMannIndex n) :
    toMatrixℂ (gellMannBasisℂ i) = (gellMannMatrices i).1 := by
  rw [gellMannBasisℂ_apply, toMatrixℂ_tmul, one_smul]

/-- The coordinates in the complex Gell-Mann basis are the contractions with the Gell-Mann
  matrices, `A = ∑ (adjointℂContr (λ_i ⊗ A) / 2) λ_i`. -/
lemma gellMannBasisℂ_repr_apply {n : ℕ} (A : Complexification n) (i : GellMannIndex n) :
    gellMannBasisℂ.repr A i = adjointℂContr (gellMannBasisℂ i ⊗ₜ A) / 2 := by
  conv_rhs => rw [← gellMannBasisℂ.sum_repr A]
  simp only [gellMannBasisℂ_apply, TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum,
    map_smul, adjointℂContr_one_tmul, adjointContr_gellMannMatrices, smul_eq_mul, apply_ite,
    Complex.ofReal_ofNat, Complex.ofReal_zero, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  ring

/-!

## D. The adjoint action in the Gell-Mann basis

-/

/-- The matrix of the adjoint action of `g` in the Gell-Mann basis, a real matrix. -/
noncomputable def adjointGellMannBasis {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) :
    Matrix (GellMannIndex n) (GellMannIndex n) ℝ :=
  LinearMap.toMatrix gellMannBasis gellMannBasis (adjoint g)

/-- The entries of the matrix of the adjoint action, `re tr (λ_i g λ_j g†) / 2`. -/
lemma adjointGellMannBasis_apply {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ)
    (i j : GellMannIndex n) : adjointGellMannBasis g i j =
      ((gellMannMatrices i).1 * (g.1 * (gellMannMatrices j).1 * star g.1)).trace.re / 2 := by
  rw [adjointGellMannBasis, LinearMap.toMatrix_apply, gellMannBasis_repr_apply,
    adjointContr_tmul, gellMannBasis_apply, adjoint_val]

/-- The matrix of the adjoint action of `g⁻¹` is the transpose of that of `g`, the adjoint action
  preserving the contraction. -/
lemma adjointGellMannBasis_inv {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) :
    adjointGellMannBasis g⁻¹ = (adjointGellMannBasis g)ᵀ := by
  ext i j
  rw [transpose_apply, adjointGellMannBasis, adjointGellMannBasis, LinearMap.toMatrix_apply,
    LinearMap.toMatrix_apply, gellMannBasis_repr_apply, gellMannBasis_repr_apply,
    gellMannBasis_apply, gellMannBasis_apply, ← adjointContr_adjoint g,
    Representation.self_inv_apply, adjointContr_symm]

/-- The matrix of the adjoint action is orthogonal. -/
lemma adjointGellMannBasis_transpose_mul_self {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) :
    (adjointGellMannBasis g)ᵀ * adjointGellMannBasis g = 1 := by
  rw [← adjointGellMannBasis_inv, adjointGellMannBasis, adjointGellMannBasis,
    ← LinearMap.toMatrix_mul, ← map_mul, inv_mul_cancel, map_one, LinearMap.toMatrix_one]

/-- The matrix of the complex adjoint action in the complex Gell-Mann basis is the real matrix of
  the adjoint action. -/
lemma toMatrix_adjointℂ_gellMannBasisℂ {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) :
    LinearMap.toMatrix gellMannBasisℂ gellMannBasisℂ (adjointℂ g) =
      (adjointGellMannBasis g).map (algebraMap ℝ ℂ) :=
  LinearMap.toMatrix_baseChange ℂ (adjoint g) gellMannBasis gellMannBasis

/-- The adjoint action on a Gell-Mann matrix is a combination of Gell-Mann matrices with
  coefficients the entries of the matrix of the adjoint action,
  `g λ_j g† = ∑ i, R_ij(g) λ_i`. -/
lemma adjoint_gellMannMatrices {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (j : GellMannIndex n) :
    adjoint g (gellMannMatrices j) = ∑ i, adjointGellMannBasis g i j • gellMannMatrices i := by
  conv_lhs => rw [← gellMannBasis.sum_repr (adjoint g (gellMannMatrices j))]
  simp only [adjointGellMannBasis, LinearMap.toMatrix_apply, gellMannBasis_apply]

/-- The adjoint action on the coordinates in the Gell-Mann basis is multiplication by the matrix of
  the adjoint action, `A^i ↦ R_ij(g) A^j`. -/
lemma gellMannBasis_repr_adjoint {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ)
    (x : SULieAlgebra n ℂ) :
    gellMannBasis.repr (adjoint g x) = adjointGellMannBasis g *ᵥ gellMannBasis.repr x :=
  (LinearMap.toMatrix_mulVec_repr gellMannBasis gellMannBasis (adjoint g) x).symm

/-!

## E. The structure constants

-/

/-- The structure constants of `su(n)` in the Gell-Mann basis, with the physics normalisation
  `[λ_a, λ_b] = 2 i ∑ c, f_abc λ_c`, read off by the contraction:
  `f_abc = tr ([λ_a, λ_b] λ_c) / (4 i) = -(1 / 4) adjointContr (⁅λ_a, λ_b⁆ ⊗ λ_c)`. -/
noncomputable def gellMannStructureConst {n : ℕ} (a b c : GellMannIndex n) : ℝ :=
  -(1 / 4) * adjointContr (⁅gellMannMatrices a, gellMannMatrices b⁆ ⊗ₜ gellMannMatrices c)

/-- The bracket of two Gell-Mann matrices in terms of the structure constants,
  `⁅λ_a, λ_b⁆ = -2 ∑ c, f_abc λ_c`, the bracket `⁅x, y⁆ = i (x y - y x)` carrying a factor `i`. -/
lemma lie_gellMannMatrices {n : ℕ} (a b : GellMannIndex n) :
    ⁅gellMannMatrices a, gellMannMatrices b⁆ =
      ∑ c, (-2 * gellMannStructureConst a b c) • gellMannMatrices c := by
  conv_lhs => rw [← gellMannBasis.sum_repr ⁅gellMannMatrices a, gellMannMatrices b⁆]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [gellMannBasis_repr_apply, gellMannBasis_apply, gellMannStructureConst, adjointContr_symm]
  ring_nf

/-- The structure constants are antisymmetric in their first two indices. -/
lemma gellMannStructureConst_swap {n : ℕ} (a b c : GellMannIndex n) :
    gellMannStructureConst b a c = -gellMannStructureConst a b c := by
  rw [gellMannStructureConst, gellMannStructureConst, ← lie_skew, TensorProduct.neg_tmul,
    map_neg adjointContr]
  ring

/-- The structure constants are invariant under cyclic permutations of their indices, the
  contraction being invariant under the bracket. With `gellMannStructureConst_swap`, they are
  totally antisymmetric. -/
lemma gellMannStructureConst_cycle {n : ℕ} (a b c : GellMannIndex n) :
    gellMannStructureConst b c a = gellMannStructureConst a b c := by
  rw [gellMannStructureConst, gellMannStructureConst, adjointContr_lie (gellMannMatrices a),
    adjointContr_symm (gellMannMatrices a)]

end SULieAlgebra
