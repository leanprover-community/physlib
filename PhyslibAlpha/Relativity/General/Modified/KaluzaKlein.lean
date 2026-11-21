/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Einstein
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!

# Five-dimensional Kaluza–Klein unification

Five-dimensional Kaluza–Klein metric ansatz, explicit analytical inverse, triangular veilbein
factorization, compact-circle diffeomorphism to `U(1)` gauge equivalence, and 5D-to-4D
Einstein–Maxwell curvature reduction.

## i. Overview

Kaluza–Klein theory unifies four-dimensional General Relativity and Maxwell electromagnetism inside
a five-dimensional spacetime metric `G_{AB}` (`A, B ∈ {0, 1, 2, 3, 4}`) constructed from a 4D
metric `g_{μν}`, an electromagnetic four-potential `A_μ`, and a dilaton scalar `φ`:
`G_{μν} = g_{μν} + φ² A_μ A_ν`, `G_{μ4} = φ² A_μ`, `G_{44} = φ²`.

This module formalizes `kkMetric`, proves its exact inverse `kkMetricInv` and packages
`kkMetricTensor : MetricTensor 5`, derives the upper-unitriangular congruence factorization
`kkMetric = U B Uᵀ` with `det U = 1`, proves that a 5D coordinate shift `y' = y + λ(x)` pulls back
`kkMetric g4 A φ` to the `U(1)` gauge-transformed metric `kkMetric g4 (A + ∂λ) φ`, and proves the
Kaluza miracle `R^{(5)} = R^{(4)} - ¼ F_{μν} F^{μν}` and the equivalence between the 5D horizontal
vacuum Einstein equations and the 4D Einstein–Maxwell equations with traceless Maxwell
stress-energy.

## ii. Key results

- `kkMetric`, `kkMetricInv`, `kkMetricInv_mul_kkMetric`, `kkMetricTensor` : 5D Kaluza–Klein metric,
  analytical inverse, and `MetricTensor 5` package.
- `kkTriangular`, `kkBlockDiag`, `kkMetric_eq_triangular_conj`, `det_kkTriangular` :
  upper-unitriangular congruence factorization `G = U B Uᵀ` with `det U = 1`.
- `kkGaugeJacobian`, `det_kkGaugeJacobian`, `kkGaugeJacobian_pullback` : compact-circle
  diffeomorphism Jacobian (`det J = 1`) inducing the `U(1)` gauge shift `A_μ ↦ A_μ + ∂_μ λ`.
- `maxwellF2`, `maxwellStressEnergy`, `maxwellStressEnergy_trace_zero` : 4D Maxwell field-strength
  invariant, stress-energy tensor, and 4D conformal tracelessness.
- `kkScalar5D_eq`, `kkEinstein4D_eq_zero_iff` : Kaluza miracle `R^{(5)} = R^{(4)} - ¼ F²` and
  4D Einstein–Maxwell field equations from 5D vacuum gravity.

## iii. Table of contents

- A. Five-dimensional Kaluza–Klein metric, inverse, and determinant
- B. Compact-circle diffeomorphisms and U(1) gauge transformations
- C. Five-dimensional curvature reduction and Maxwell stress-energy

## iv. References

* None.

-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace KaluzaKlein

/-!

## A. Five-dimensional Kaluza–Klein metric, inverse, and determinant

-/

/-- Five-component extension `(A_0, A_1, A_2, A_3, 1)` of a 4D gauge potential `A`. -/
def potExt (A : Fin 4 → ℝ) : Fin 5 → ℝ := ![A 0, A 1, A 2, A 3, 1]

/-- Five-dimensional zero-padded embedding of a 4D rank-2 tensor `g4`. -/
def metric4Ext (g4 : Tensor2 4) : Tensor2 5 :=
  fun i j =>
    if hi : i.val < 4 then
      if hj : j.val < 4 then g4 ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
    else 0

/-- Five-dimensional Kaluza–Klein metric `G_{AB} = g^{(4)}_{AB} + φ² A_A A_B` with `A_4 = 1`. -/
def kkMetric (g4 : Tensor2 4) (A : Fin 4 → ℝ) (φ : ℝ) : Tensor2 5 :=
  fun i j => metric4Ext g4 i j + φ ^ 2 * potExt A i * potExt A j

/-- Symmetry of `kkMetric g4 A φ` whenever `g4` is symmetric. -/
lemma kkMetric_symm (g4 : Tensor2 4) (hg : IsSymm g4) (A : Fin 4 → ℝ) (φ : ℝ) :
    IsSymm (kkMetric g4 A φ) := by
  intro i j
  unfold kkMetric metric4Ext
  by_cases hi : i.val < 4 <;> by_cases hj : j.val < 4
  · simp only [hi, hj, ↓reduceDIte, hg ⟨i.val, hi⟩ ⟨j.val, hj⟩]; ring
  · simp only [hi, hj, ↓reduceDIte]; ring
  · simp only [hi, hj, ↓reduceDIte]; ring
  · simp only [hi, hj, ↓reduceDIte]; ring

/-- Contravariant 4D potential `A^μ = ∑_ν g^{μν} A_ν`. -/
def potUp (ginv4 : Tensor2 4) (A : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  ∑ k : Fin 4, ginv4 i k * A k

/-- Five-dimensional analytical inverse of the Kaluza–Klein metric `kkMetric g4 A φ`. -/
noncomputable def kkMetricInv (ginv4 : Tensor2 4) (A : Fin 4 → ℝ) (φ : ℝ) : Tensor2 5 :=
  fun i j =>
    if hi : i.val < 4 then
      if hj : j.val < 4 then ginv4 ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else -potUp ginv4 A ⟨i.val, hi⟩
    else
      if hj : j.val < 4 then -potUp ginv4 A ⟨j.val, hj⟩
      else 1 / φ ^ 2 + ∑ k : Fin 4, A k * potUp ginv4 A k

private lemma sum_fin5_split (f : Fin 5 → ℝ) :
    (∑ k : Fin 5, f k) = (∑ k : Fin 4, f ⟨k.val, by omega⟩) + f 4 := by
  simp only [Fin.sum_univ_five, Fin.sum_univ_four]
  rfl

/-- Left-inverse identity `kkMetricInv * kkMetric = 1` for any `M : MetricTensor 4` and `φ ≠ 0`. -/
lemma kkMetricInv_mul_kkMetric (M : MetricTensor 4) (A : Fin 4 → ℝ) (φ : ℝ) (hφ : φ ≠ 0) :
    kkMetricInv M.ginv A φ * kkMetric M.g A φ = 1 := by
  have hφ2 : φ ^ 2 ≠ 0 := pow_ne_zero 2 hφ
  have hid : ∀ a b : Fin 4, (∑ k : Fin 4, M.ginv a k * M.g k b) = if a = b then 1 else 0 := by
    intro a b
    have h := congrFun (congrFun M.inv_right a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  have hA : ∀ b : Fin 4, (∑ k : Fin 4, potUp M.ginv A k * M.g k b) = A b := by
    intro b
    unfold potUp
    calc (∑ k : Fin 4, (∑ m : Fin 4, M.ginv k m * A m) * M.g k b)
        = ∑ m : Fin 4, A m * ∑ k : Fin 4, M.g b k * M.ginv k m := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by rw [M.symm k b]; ring
      _ = A b := by
          have hright : ∀ m : Fin 4,
              (∑ k : Fin 4, M.g b k * M.ginv k m) = if b = m then 1 else 0 := by
            intro m
            have h := congrFun (congrFun M.inv_left b) m
            simpa [Matrix.mul_apply, Matrix.one_apply] using h
          simp [hright]
  have hpot : ∀ k : Fin 4, potExt A ⟨k.val, by omega⟩ = A k := by
    intro k; fin_cases k <;> rfl
  have hx4 : ∀ x : Fin 4, (⟨x.val, by omega⟩ : Fin 5).val < 4 := fun x => x.isLt
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply, sum_fin5_split]
  by_cases hi : i.val < 4 <;> by_cases hj : j.val < 4
  · let i4 : Fin 4 := ⟨i.val, hi⟩
    let j4 : Fin 4 := ⟨j.val, hj⟩
    have hij : (i = j) ↔ (i4 = j4) := by
      simp [i4, j4, Fin.ext_iff]
    have hj_pot : potExt A j = A j4 := hpot j4
    simp only [kkMetricInv, kkMetric, metric4Ext, hi, hj, hx4, ↓reduceDIte,
      show ¬((4 : Fin 5).val < 4) by decide, hpot, hj_pot, show potExt A 4 = 1 from rfl, hij]
    have hsplit :
        (∑ x : Fin 4, M.ginv i4 x * (M.g x j4 + φ ^ 2 * A x * A j4))
          = (∑ x : Fin 4, M.ginv i4 x * M.g x j4) + φ ^ 2 * A j4 * potUp M.ginv A i4 := by
      unfold potUp
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      refine congrArg (_ + ·) (Finset.sum_congr rfl fun x _ => by ring)
    change (∑ x : Fin 4, M.ginv i4 x * (M.g x j4 + φ ^ 2 * A x * A j4))
      + -potUp M.ginv A i4 * (0 + φ ^ 2 * 1 * A j4) = if i4 = j4 then 1 else 0
    rw [hsplit, hid i4 j4]
    ring
  · let i4 : Fin 4 := ⟨i.val, hi⟩
    have hj4 : j = 4 := by ext; omega
    subst hj4
    have hij : i ≠ 4 := by intro h; rw [h] at hi; exact absurd hi (by decide)
    simp only [kkMetricInv, kkMetric, metric4Ext, hi, hx4, show ¬((4 : Fin 5).val < 4) by decide,
      ↓reduceDIte, hpot, show potExt A 4 = 1 from rfl, hij, ↓reduceIte]
    have hsum : (∑ x : Fin 4, M.ginv i4 x * (0 + φ ^ 2 * A x * 1))
        = φ ^ 2 * potUp M.ginv A i4 := by
      unfold potUp
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => by ring
    change (∑ x : Fin 4, M.ginv i4 x * (0 + φ ^ 2 * A x * 1))
      + -potUp M.ginv A i4 * (0 + φ ^ 2 * 1 * 1) = 0
    rw [hsum]
    ring
  · let j4 : Fin 4 := ⟨j.val, hj⟩
    have hi4 : i = 4 := by ext; omega
    subst hi4
    have hij : (4 : Fin 5) ≠ j := by intro h; rw [← h] at hj; exact absurd hj (by decide)
    have hj_pot : potExt A j = A j4 := hpot j4
    simp only [kkMetricInv, kkMetric, metric4Ext, hj, hx4, show ¬((4 : Fin 5).val < 4) by decide,
      ↓reduceDIte, hpot, hj_pot, show potExt A 4 = 1 from rfl, hij, ↓reduceIte]
    have hsplit :
        (∑ x : Fin 4, -potUp M.ginv A x * (M.g x j4 + φ ^ 2 * A x * A j4))
          = -(∑ x : Fin 4, potUp M.ginv A x * M.g x j4)
            - φ ^ 2 * A j4 * (∑ x : Fin 4, A x * potUp M.ginv A x) := by
      have hterm : ∀ x : Fin 4,
          -potUp M.ginv A x * (M.g x j4 + φ ^ 2 * A x * A j4) =
            -(potUp M.ginv A x * M.g x j4) - φ ^ 2 * A j4 * (A x * potUp M.ginv A x) := by
        intro x; ring
      simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
    change (∑ x : Fin 4, -potUp M.ginv A x * (M.g x j4 + φ ^ 2 * A x * A j4))
      + (1 / φ ^ 2 + ∑ k : Fin 4, A k * potUp M.ginv A k) * (0 + φ ^ 2 * 1 * A j4) = 0
    rw [hsplit, hA j4]
    field_simp [hφ2]
    ring
  · have hi4 : i = 4 := by ext; omega
    have hj4 : j = 4 := by ext; omega
    subst hi4; subst hj4
    simp only [kkMetricInv, kkMetric, metric4Ext, hx4, show ¬((4 : Fin 5).val < 4) by decide,
      ↓reduceDIte, hpot, show potExt A 4 = 1 from rfl, ↓reduceIte]
    have hsum :
        (∑ x : Fin 4, -potUp M.ginv A x * (0 + φ ^ 2 * A x * 1))
          = -(φ ^ 2 * (∑ x : Fin 4, A x * potUp M.ginv A x)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => by ring
    change (∑ x : Fin 4, -potUp M.ginv A x * (0 + φ ^ 2 * A x * 1))
      + (1 / φ ^ 2 + ∑ k : Fin 4, A k * potUp M.ginv A k) * (0 + φ ^ 2 * 1 * 1) = 1
    rw [hsum]
    field_simp [hφ2]
    ring

/-- Symmetry of `kkMetricInv M.ginv A φ` for any `M : MetricTensor 4`. -/
lemma kkMetricInv_symm (M : MetricTensor 4) (A : Fin 4 → ℝ) (φ : ℝ) :
    IsSymm (kkMetricInv M.ginv A φ) := by
  have hginv_symm : IsSymm M.ginv := by
    have hgt : M.g.transpose = M.g := Matrix.ext fun a b => M.symm b a
    have h : M.ginv.transpose = M.ginv := by
      calc M.ginv.transpose
          = M.ginv.transpose * (M.g * M.ginv) := by rw [M.inv_left, Matrix.mul_one]
        _ = (M.ginv.transpose * M.g) * M.ginv := by rw [Matrix.mul_assoc]
        _ = (M.g.transpose * M.ginv).transpose * M.ginv := by
            rw [Matrix.transpose_mul, Matrix.transpose_transpose]
        _ = M.ginv := by
            rw [hgt, M.inv_left, Matrix.transpose_one, Matrix.one_mul]
    intro a b
    exact congrFun (congrFun h b) a
  intro i j
  unfold kkMetricInv
  by_cases hi : i.val < 4 <;> by_cases hj : j.val < 4
  · simp [hi, hj, hginv_symm ⟨i.val, hi⟩ ⟨j.val, hj⟩]
  · simp [hi, hj]
  · simp [hi, hj]
  · simp [hi, hj]

/-- Right-inverse identity `kkMetric * kkMetricInv = 1`. -/
lemma kkMetric_mul_kkMetricInv (M : MetricTensor 4) (A : Fin 4 → ℝ) (φ : ℝ) (hφ : φ ≠ 0) :
    kkMetric M.g A φ * kkMetricInv M.ginv A φ = 1 := by
  have hL := kkMetricInv_mul_kkMetric M A φ hφ
  have hT := congrArg Matrix.transpose hL
  rw [Matrix.transpose_mul, Matrix.transpose_one] at hT
  have hs1 : (kkMetric M.g A φ).transpose = kkMetric M.g A φ :=
    Matrix.ext fun i j => kkMetric_symm M.g M.symm A φ j i
  have hs2 : (kkMetricInv M.ginv A φ).transpose = kkMetricInv M.ginv A φ :=
    Matrix.ext fun i j => kkMetricInv_symm M A φ j i
  rwa [hs1, hs2] at hT

/-- Package the 5D Kaluza–Klein metric and its inverse as a `MetricTensor 5`. -/
noncomputable def kkMetricTensor (M : MetricTensor 4) (A : Fin 4 → ℝ) (φ : ℝ) (hφ : φ ≠ 0) :
    MetricTensor 5 where
  g := kkMetric M.g A φ
  ginv := kkMetricInv M.ginv A φ
  symm := kkMetric_symm M.g M.symm A φ
  inv_left := kkMetric_mul_kkMetricInv M A φ hφ
  inv_right := kkMetricInv_mul_kkMetric M A φ hφ

/-- Upper-unitriangular Kaluza–Klein frame matrix `U` with `U_{μ4} = A_μ` and `1` on the
diagonal. -/
def kkTriangular (A : Fin 4 → ℝ) : Tensor2 5 :=
  fun i j =>
    if i = j then 1
    else if hi : i.val < 4 then
      if j = 4 then A ⟨i.val, hi⟩ else 0
    else 0

/-- Block-diagonal 5D matrix `diag(g4, φ²)`. -/
def kkBlockDiag (g4 : Tensor2 4) (φ : ℝ) : Tensor2 5 :=
  fun i j =>
    if hi : i.val < 4 then
      if hj : j.val < 4 then g4 ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
    else if i = 4 ∧ j = 4 then φ ^ 2 else 0

/-- The upper-unitriangular Kaluza–Klein frame matrix `kkTriangular A` has unit determinant. -/
lemma det_kkTriangular (A : Fin 4 → ℝ) : Matrix.det (kkTriangular A) = 1 := by
  have htri : Matrix.BlockTriangular (kkTriangular A) id := by
    intro i j hij
    have hne : i ≠ j := ne_of_gt hij
    have hj4 : j ≠ 4 := by
      intro h; subst h
      change 4 < i at hij
      omega
    simp [kkTriangular, hne, hj4]
  rw [Matrix.det_of_isUpperTriangular htri]
  refine Finset.prod_eq_one fun i _ => ?_
  simp [kkTriangular]

private lemma val_lt_four_0 : (0 : Fin 5).val < 4 := by decide
private lemma val_lt_four_1 : (1 : Fin 5).val < 4 := by decide
private lemma val_lt_four_2 : (2 : Fin 5).val < 4 := by decide
private lemma val_lt_four_3 : (3 : Fin 5).val < 4 := by decide
private lemma not_val_lt_four_4 : ¬((4 : Fin 5).val < 4) := by decide
private lemma fin4_mk_0 (h : (0 : Fin 5).val < 4) : (⟨(0 : Fin 5).val, h⟩ : Fin 4) = 0 := rfl
private lemma fin4_mk_1 (h : (1 : Fin 5).val < 4) : (⟨(1 : Fin 5).val, h⟩ : Fin 4) = 1 := rfl
private lemma fin4_mk_2 (h : (2 : Fin 5).val < 4) : (⟨(2 : Fin 5).val, h⟩ : Fin 4) = 2 := rfl
private lemma fin4_mk_3 (h : (3 : Fin 5).val < 4) : (⟨(3 : Fin 5).val, h⟩ : Fin 4) = 3 := rfl
private lemma potExt_0 (A : Fin 4 → ℝ) : potExt A 0 = A 0 := rfl
private lemma potExt_1 (A : Fin 4 → ℝ) : potExt A 1 = A 1 := rfl
private lemma potExt_2 (A : Fin 4 → ℝ) : potExt A 2 = A 2 := rfl
private lemma potExt_3 (A : Fin 4 → ℝ) : potExt A 3 = A 3 := rfl
private lemma potExt_4 (A : Fin 4 → ℝ) : potExt A 4 = 1 := rfl

/-- Congruence factorization `kkMetric g4 A φ = U * diag(g4, φ²) * Uᵀ`. -/
lemma kkMetric_eq_triangular_conj (g4 : Tensor2 4) (A : Fin 4 → ℝ) (φ : ℝ) :
    kkMetric g4 A φ = kkTriangular A * kkBlockDiag g4 φ * (kkTriangular A).transpose := by
  ext i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by fin_cases i <;> decide
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by fin_cases j <;> decide
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_five,
    kkMetric, metric4Ext, kkTriangular, kkBlockDiag,
    val_lt_four_0, val_lt_four_1, val_lt_four_2, val_lt_four_3, not_val_lt_four_4,
    fin4_mk_0, fin4_mk_1, fin4_mk_2, fin4_mk_3,
    Fin.isValue, Fin.reduceEq, and_self, and_false, ↓reduceIte, ↓reduceDIte]
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    simp only [val_lt_four_0, val_lt_four_1, val_lt_four_2, val_lt_four_3, not_val_lt_four_4,
      fin4_mk_0, fin4_mk_1, fin4_mk_2, fin4_mk_3,
      potExt_0, potExt_1, potExt_2, potExt_3, potExt_4,
      Fin.isValue, Fin.reduceEq, ↓reduceIte, ↓reduceDIte] <;>
    ring

/-!

## B. Compact-circle diffeomorphisms and U(1) gauge transformations

-/

/-- Jacobian matrix `(∂x'^A / ∂x^B)` of a 5D compact-circle coordinate shift `x'^4 = x^4 + λ(x^μ)`
with 4D gradient `dlam_μ = ∂_μ λ`. -/
def kkGaugeJacobian (dlam : Fin 4 → ℝ) : Tensor2 5 :=
  fun i j =>
    if i = j then 1
    else if i = 4 then
      if hj : j.val < 4 then dlam ⟨j.val, hj⟩ else 0
    else 0

/-- A compact-circle shift is volume-preserving: `det (kkGaugeJacobian dlam) = 1`. -/
lemma det_kkGaugeJacobian (dlam : Fin 4 → ℝ) : Matrix.det (kkGaugeJacobian dlam) = 1 := by
  rw [← Matrix.det_transpose]
  have htri : Matrix.BlockTriangular (kkGaugeJacobian dlam).transpose id := by
    intro i j hij
    have hne : j ≠ i := ne_of_lt hij
    have hj4 : j ≠ 4 := by
      intro h; subst h
      change 4 < i at hij
      omega
    simp [kkGaugeJacobian, hne, hj4]
  rw [Matrix.det_of_isUpperTriangular htri]
  refine Finset.prod_eq_one fun i _ => ?_
  simp [kkGaugeJacobian]

/-- Five-dimensional diffeomorphism-to-`U(1)`-gauge theorem: pulling back `kkMetric g4 A φ` by
the compact-circle shift Jacobian `kkGaugeJacobian dlam` shifts the 4D electromagnetic potential by
`A_μ ↦ A_μ + dlam_μ` while leaving `g4` and `φ` invariant. -/
lemma kkGaugeJacobian_pullback (g4 : Tensor2 4) (A dlam : Fin 4 → ℝ) (φ : ℝ) :
    (kkGaugeJacobian dlam).transpose * kkMetric g4 A φ * kkGaugeJacobian dlam =
      kkMetric g4 (fun μ => A μ + dlam μ) φ := by
  ext i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by fin_cases i <;> decide
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by fin_cases j <;> decide
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_five,
    kkMetric, metric4Ext, kkGaugeJacobian,
    val_lt_four_0, val_lt_four_1, val_lt_four_2, val_lt_four_3, not_val_lt_four_4,
    fin4_mk_0, fin4_mk_1, fin4_mk_2, fin4_mk_3,
    potExt_0, potExt_1, potExt_2, potExt_3, potExt_4,
    Fin.isValue, Fin.reduceEq, ↓reduceIte, ↓reduceDIte]
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    simp only [val_lt_four_0, val_lt_four_1, val_lt_four_2, val_lt_four_3, not_val_lt_four_4,
      fin4_mk_0, fin4_mk_1, fin4_mk_2, fin4_mk_3,
      potExt_0, potExt_1, potExt_2, potExt_3, potExt_4,
      Fin.isValue, Fin.reduceEq, ↓reduceIte, ↓reduceDIte] <;>
    ring

/-!

## C. Five-dimensional curvature reduction and Maxwell stress-energy

-/

/-- Four-dimensional Maxwell field-strength quadratic invariant `F_{ab} F^{ab} = g^{ac} g^{bd}
F_{ab} F_{cd}`. -/
def maxwellF2 (M : MetricTensor 4) (F : Tensor2 4) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4, M.ginv a c * M.ginv b d * F a b * F c d

/-- Four-dimensional electromagnetic stress-energy tensor
`T^{EM}_{ab} = g^{cd} F_{ac} F_{bd} - ¼ g_{ab} F_{cd} F^{cd}`. -/
noncomputable def maxwellStressEnergy (M : MetricTensor 4) (F : Tensor2 4) (a b : Fin 4) : ℝ :=
  (∑ c : Fin 4, ∑ d : Fin 4, M.ginv c d * F a c * F b d) - (1 / 4) * M.g a b * maxwellF2 M F

/-- In four spacetime dimensions (`d = 4`), the Maxwell stress-energy tensor is identically
trace-free: `g^{ab} T^{EM}_{ab} = 0`. -/
lemma maxwellStressEnergy_trace_zero (M : MetricTensor 4) (F : Tensor2 4) :
    (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b * maxwellStressEnergy M F a b) = 0 := by
  have htr_g : (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b * M.g a b) = 4 := by
    have hdiag : ∀ a : Fin 4, (∑ b : Fin 4, M.ginv a b * M.g a b) = 1 := by
      intro a
      have h1 : (∑ b : Fin 4, M.ginv a b * M.g a b) = ∑ b : Fin 4, M.ginv a b * M.g b a :=
        Finset.sum_congr rfl fun b _ => by rw [M.symm a b]
      rw [h1]
      have h := congrFun (congrFun M.inv_right a) a
      simpa [Matrix.mul_apply, Matrix.one_apply] using h
    simp [hdiag]
  unfold maxwellStressEnergy
  simp only [mul_sub, Finset.sum_sub_distrib]
  have h1 :
      (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b *
        (∑ c : Fin 4, ∑ d : Fin 4, M.ginv c d * F a c * F b d))
        = maxwellF2 M F := by
    unfold maxwellF2
    refine Finset.sum_congr rfl fun a _ => ?_
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun d _ => by ring
  have h2 :
      (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b * ((1 / 4) * M.g a b * maxwellF2 M F))
        = (1 / 4) * (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b * M.g a b) * maxwellF2 M F := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [h1, h2, htr_g]
  ring

/-- Fifth-dimension `(4, 4)` Kaluza–Klein Ricci component at unit dilaton `φ = 1`:
`R^{(5)}_{44} = ¼ F_{ab} F^{ab}`. -/
noncomputable def kkRicci44 (M : MetricTensor 4) (F : Tensor2 4) : ℝ :=
  (1 / 4) * maxwellF2 M F

/-- Horizontal 4D Kaluza–Klein Ricci components at unit dilaton `φ = 1`:
`R^{(5)}_{ab} = R^{(4)}_{ab} - ½ g^{cd} F_{ac} F_{bd}`. -/
noncomputable def kkRicci4D (M : MetricTensor 4) (R4 : Tensor2 4) (F : Tensor2 4)
    (a b : Fin 4) : ℝ :=
  R4 a b - (1 / 2) * ∑ c : Fin 4, ∑ d : Fin 4, M.ginv c d * F a c * F b d

/-- Five-dimensional Kaluza–Klein scalar curvature `R^{(5)} = g^{ab} R^{(5)}_{ab} + R^{(5)}_{44}` at
unit dilaton `φ = 1`. -/
noncomputable def kkScalar5D (M : MetricTensor 4) (R4 : Tensor2 4) (F : Tensor2 4) : ℝ :=
  (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b * kkRicci4D M R4 F a b) + kkRicci44 M F

/-- The Kaluza miracle: the 5D Einstein–Hilbert scalar curvature `R^{(5)}` reduces identically to
the 4D Einstein–Maxwell Lagrangian `R^{(4)} - ¼ F_{ab} F^{ab}`. -/
lemma kkScalar5D_eq (M : MetricTensor 4) (R4 : Tensor2 4) (F : Tensor2 4) :
    kkScalar5D M R4 F =
      (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b * R4 a b) - (1 / 4) * maxwellF2 M F := by
  unfold kkScalar5D kkRicci4D kkRicci44
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hF :
      (∑ a : Fin 4, ∑ b : Fin 4,
        M.ginv a b * ((1 / 2) * ∑ c : Fin 4, ∑ d : Fin 4, M.ginv c d * F a c * F b d))
        = (1 / 2) * maxwellF2 M F := by
    unfold maxwellF2
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun d _ => by ring
  rw [hF]
  ring

/-- Vanishing of the 5D horizontal Kaluza–Klein Einstein tensor `G^{(5)}_{ab} = R^{(5)}_{ab} -
½ g_{ab} R^{(5)} = 0` is equivalent to the 4D Einstein–Maxwell equation
`G^{(4)}_{ab} = ½ T^{EM}_{ab}`. -/
lemma kkEinstein4D_eq_zero_iff (M : MetricTensor 4) (R4 : Tensor2 4) (F : Tensor2 4)
    (a b : Fin 4) :
    kkRicci4D M R4 F a b - (1 / 2) * M.g a b * kkScalar5D M R4 F = 0 ↔
      R4 a b - (1 / 2) * M.g a b * (∑ c : Fin 4, ∑ d : Fin 4, M.ginv c d * R4 c d) =
        (1 / 2) * maxwellStressEnergy M F a b := by
  rw [kkScalar5D_eq]
  unfold kkRicci4D maxwellStressEnergy
  constructor <;> intro h <;> linarith

end KaluzaKlein

end Modified

end GeneralRelativity
