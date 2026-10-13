/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.RingTheory.TensorProduct.Free
public import Physlib.Mathematics.Groups.SpecialUnitary.LieAlgebra.Contractions
/-!

# The generalized Gell-Mann matrices

The generalized Gell-Mann matrices, orthogonality, the basis and the structure constants they form.

## i. Overview

The generalized Gell-Mann matrices are the standard basis of `su(n)`, generalizing the Pauli
matrices (`n = 2`) and the Gell-Mann matrices (`n = 3`). They are labelled by `GellMannIndex n`,
which has `n² - 1` elements, of three kinds (A):

- for `p < q` the symmetric matrix `E_pq + E_qp`,
- for `p < q` the antisymmetric matrix `-i E_pq + i E_qp`,
- for `1 ≤ m ≤ n - 1` the diagonal matrix `√(2 / (m (m + 1))) (E_00 + ⋯ + E_(m-1)(m-1) - m E_mm)`.

They are orthogonal under the contraction, `adjointContr (λ_i ⊗ λ_j) = tr (λ_i λ_j) = 2 δ_ij`, and
so linearly independent (B).

As there are as many as the dimension `n² - 1` of `su(n)`, they form a basis, whose coordinates
are the contractions `adjointContr (λ_i ⊗ x) / 2`, and its base change is a basis of the
complexification (C). In this basis the bracket defines the structure constants
`[λ_a, λ_b] = 2 i f_abc λ_c`, which are totally antisymmetric (D).

## ii. Key results

- `SULieAlgebra.GellMannIndex` : the labels of the generalized Gell-Mann matrices.
- `SULieAlgebra.gellMannMatrices` : the generalized Gell-Mann matrices.
- `SULieAlgebra.adjointContr_gellMannMatrices` : the Gell-Mann matrices are orthogonal.
- `SULieAlgebra.gellMannBasis` : the Gell-Mann basis of `su(n)`.
- `SULieAlgebra.gellMannBasisℂ` : the Gell-Mann basis of the complexification of `su(n)`.
- `SULieAlgebra.gellMannStructureConst` : the structure constants, `[λ_a, λ_b] = 2 i f_abc λ_c`.

## iii. Table of contents

- A. The indexing type of the Gell-Mann matrices
  - A.1. The cardinality of `GellMannIndex`
- B. The generalized Gell-Mann matrices
  - B.1. Symmetry properties
  - B.2. Explicit forms
  - B.3. Orthogonality
    - B.3.1. Between different types
    - B.3.2. Between the same type
    - B.3.3. The full orthogonality relation
  - B.4. Linear independence
- C. The Gell-Mann basis
  - C.1. The basis of `su(n)`
  - C.2. The basis of the complexification
- D. The structure constants

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

### A.1. The cardinality of `GellMannIndex`

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
  | .diag l => ofMatrix (diagonal fun x => (√(2 / ((l.1 + 1) * (l.1 + 2))) : ℝ) *
      if x.1 ≤ l.1 then 1 else if x.1 = l.1 + 1 then -(l.1 + 1 : ℂ) else 0)
      (by
        ext x y
        simp only [star_apply, diagonal_apply]
        split_ifs <;> simp_all [Complex.conj_ofReal]
        omega)
      (by
        have hl := l.2
        rw [trace_diagonal, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun x =>
          if x ≤ l.1 then (1 : ℂ) else if x = l.1 + 1 then -(l.1 + 1 : ℂ) else 0),
          ← Finset.sum_range_add_sum_Ico _ (show l.1 + 2 ≤ n by omega), Finset.sum_range_succ,
          Finset.sum_congr (s₁ := Finset.range (l.1 + 1)) rfl fun x hx =>
            ite_eq_left (Nat.lt_succ_iff.1 (Finset.mem_range.1 hx)),
          Finset.sum_eq_zero (s := Finset.Ico (l.1 + 2) n) fun x hx => by
            have := (Finset.mem_Ico.1 hx).1
            rw [ite_eq_right (by omega), ite_eq_right (by omega)]]
        simp)

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
    (gellMannMatrices (.diag l)).1 = diagonal fun x => (√(2 / ((l.1 + 1) * (l.1 + 2))) : ℝ) *
      if x.1 ≤ l.1 then 1 else if x.1 = l.1 + 1 then -(l.1 + 1 : ℂ) else 0 := by
  rfl

/-!

### B.3. Orthogonality

-/

/-!

#### B.3.1. Between different types

-/

lemma adjointContr_gellMannMatrices_symm_antisymm_eq_zero {n : ℕ} (p q : Fin n) (h : p < q)
    (p' q' : Fin n) (h' : p' < q') :
    adjointContr (gellMannMatrices (.symm p q h) ⊗ₜ gellMannMatrices (.antisymm p' q' h')) = 0 := by
  simp only [adjointContr_tmul, gellMannMatrices_symm_val_eq, gellMannMatrices_antisymm_val_eq,
    Matrix.add_mul, trace_add, trace_single_mul, Matrix.add_apply, single_apply, Fin.ext_iff,
    smul_eq_mul]
  split_ifs <;> norm_num

lemma adjointContr_gellMannMatrices_symm_diag_eq_zero {n : ℕ} (p q : Fin n) (h : p < q)
    (l : Fin (n - 1)) :
    adjointContr (gellMannMatrices (.symm p q h) ⊗ₜ gellMannMatrices (.diag l)) = 0 := by
  rw [adjointContr_tmul, gellMannMatrices_symm_val_eq, gellMannMatrices_diag_val_eq]
  simp [Matrix.add_mul, trace_add, trace_single_mul, h.ne, h.ne']

lemma adjointContr_gellMannMatrices_antisymm_symm_eq_zero {n : ℕ} (p q : Fin n) (h : p < q)
    (p' q' : Fin n) (h' : p' < q') :
    adjointContr (gellMannMatrices (.antisymm p q h) ⊗ₜ gellMannMatrices (.symm p' q' h')) = 0 := by
  simp only [adjointContr_tmul, gellMannMatrices_antisymm_val_eq, gellMannMatrices_symm_val_eq,
    Matrix.add_mul, trace_add, trace_single_mul, Matrix.add_apply, single_apply, Fin.ext_iff,
    smul_eq_mul]
  split_ifs <;> norm_num

lemma adjointContr_gellMannMatrices_antisymm_diag_eq_zero {n : ℕ} (p q : Fin n) (h : p < q)
    (l : Fin (n - 1)) :
    adjointContr (gellMannMatrices (.antisymm p q h) ⊗ₜ gellMannMatrices (.diag l)) = 0 := by
  rw [adjointContr_tmul, gellMannMatrices_antisymm_val_eq, gellMannMatrices_diag_val_eq]
  simp [Matrix.add_mul, trace_add, trace_single_mul, h.ne, h.ne']

lemma adjointContr_gellMannMatrices_diag_symm_eq_zero {n : ℕ} (l : Fin (n - 1)) (p q : Fin n)
    (h : p < q) :
    adjointContr (gellMannMatrices (.diag l) ⊗ₜ gellMannMatrices (.symm p q h)) = 0 := by
  rw [adjointContr_tmul, gellMannMatrices_diag_val_eq, gellMannMatrices_symm_val_eq]
  simp [Matrix.mul_add, trace_add, trace_mul_single, h.ne, h.ne']

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

/-- The diagonal Gell-Mann matrices are normalized, `tr (λ_l λ_l) = 2`. -/
lemma adjointContr_gellMannMatrices_diag_self {n : ℕ} (l : Fin (n - 1)) :
    adjointContr (gellMannMatrices (.diag l) ⊗ₜ gellMannMatrices (.diag l)) = 2 := by
  have hl := l.2
  apply Complex.ofReal_injective
  rw [ofReal_adjointContr_tmul, Complex.ofReal_ofNat, gellMannMatrices_diag_val_eq,
    diagonal_mul_diagonal, trace_diagonal,
    Fin.sum_univ_eq_sum_range (fun x => ((√(2 / ((l.1 + 1) * (l.1 + 2))) : ℝ) : ℂ) *
      (if x ≤ l.1 then 1 else if x = l.1 + 1 then -(l.1 + 1 : ℂ) else 0) *
      (((√(2 / ((l.1 + 1) * (l.1 + 2))) : ℝ) : ℂ) *
      (if x ≤ l.1 then 1 else if x = l.1 + 1 then -(l.1 + 1 : ℂ) else 0))),
    ← Finset.sum_range_add_sum_Ico _ (show l.1 + 2 ≤ n by omega), Finset.sum_range_succ,
    Finset.sum_congr (s₁ := Finset.range (l.1 + 1)) rfl fun x hx => by
      rw [ite_eq_left (Nat.lt_succ_iff.1 (Finset.mem_range.1 hx))],
    Finset.sum_eq_zero (s := Finset.Ico (l.1 + 2) n) fun x hx => by
      have := (Finset.mem_Ico.1 hx).1
      rw [ite_eq_right (by omega), ite_eq_right (by omega), mul_zero, zero_mul]]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_add,
    Nat.cast_one, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, ↓reduceIte, add_zero]
  have hc : ((√(2 / ((l.1 + 1) * (l.1 + 2))) : ℝ) : ℂ) * ((√(2 / ((l.1 + 1) * (l.1 + 2))) : ℝ) : ℂ)
      * ((l.1 + 1) * (l.1 + 2)) = 2 := by
    have : (l.1 : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : l.1 + 2 ≠ 0)
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    field_simp
  linear_combination hc

lemma adjointContr_gellMannMatrices_diag_orthogonal {n : ℕ} (l l' : Fin (n - 1)) :
    adjointContr (gellMannMatrices (.diag l) ⊗ₜ gellMannMatrices (.diag l')) =
      if l = l' then 2 else 0 := by
  -- for `a < b`, `λ_b` is constant on the support of `λ_a`, so `λ_a λ_b` is a multiple of `λ_a`
  have hmul {a b : Fin (n - 1)} (h : a < b) :
      (gellMannMatrices (.diag a)).1 * (gellMannMatrices (.diag b)).1 =
        ((√(2 / ((b.1 + 1) * (b.1 + 2))) : ℝ) : ℂ) • (gellMannMatrices (.diag a)).1 := by
    have := Fin.lt_def.1 h
    rw [gellMannMatrices_diag_val_eq, gellMannMatrices_diag_val_eq, diagonal_mul_diagonal,
      ← diagonal_smul]
    congr 1
    funext x
    rw [Pi.smul_apply, smul_eq_mul]
    split_ifs <;> first | omega | ring
  rcases lt_trichotomy l l' with h | rfl | h
  · rw [ite_eq_right h.ne, ← Complex.ofReal_inj, ofReal_adjointContr_tmul, hmul h, trace_smul,
      trace_val_eq_zero, smul_zero, Complex.ofReal_zero]
  · rw [adjointContr_gellMannMatrices_diag_self, ite_eq_left rfl]
  · rw [ite_eq_right h.ne', ← Complex.ofReal_inj, ofReal_adjointContr_tmul, trace_mul_comm,
      hmul h, trace_smul, trace_val_eq_zero, smul_zero, Complex.ofReal_zero]

/-!

#### B.3.3. The full orthogonality relation

-/

/-- The generalized Gell-Mann matrices are orthogonal under the trace pairing,
  with normalization `tr (λ_i λ_j) = 2 δ_ij`. -/
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

## D. The structure constants

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
