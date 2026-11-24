/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.Notation
public import PhyslibAlpha.Relativity.Metrics.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!

# Five-dimensional Kaluza–Klein metric ansatz

Five-dimensional Kaluza–Klein metric `G_{AB}`, explicit analytical inverse `G^{AB}`, and
certification as a `MetricTensor 5`.

## i. Overview

Kaluza–Klein theory packages a four-dimensional metric `g_{μν}`, an electromagnetic four-potential
`A_μ`, and a dilaton scalar `φ` into the five-dimensional metric `G_{μν} = g_{μν} + φ² A_μ A_ν`,
`G_{μ4} = φ² A_μ`, `G_{44} = φ²`. This module defines `KaluzaKleinData`, `kkMetric`, and
`kkMetricInv`, proves both two-sided inverse relations and symmetry, and bundles `kkMetricTensor`.

## ii. Key results

- `KaluzaKleinData` : 5D Kaluza–Klein configuration `(M, A, φ)`.
- `potExt`, `metric4Ext`, `kkMetric`, `potUp`, `kkMetricInv` : 5D metric and analytical inverse.
- `kkMetricInv_mul_kkMetric`, `kkMetric_mul_kkMetricInv`, `kkMetricTensor` : certified
  `MetricTensor 5` package.

## iii. Table of contents

- A. Five-dimensional Kaluza–Klein metric and inverse

## iv. References

* Theodor Kaluza, *Zum Unitätsproblem der Physik*, *Sitzungsberichte der Preu\ssischen Akademie
  der Wissenschaften zu Berlin, Mathematisch-Physikalische Klasse* (1921). [ref: Kaluza1921]
* Oskar Klein, *Quantentheorie und fünfdimensionale Relativitätstheorie*, *Zeitschrift für Physik*
  (1926). [ref: Klein1926]
* Oskar Klein, *The Atomicity of Electricity as a Quantum Theory Law*, *Nature* (1926). [ref:
  Klein1926Nature]

-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace KaluzaKlein

/-!

## A. Five-dimensional Kaluza–Klein metric and inverse

-/

/-- Five-dimensional Kaluza–Klein configuration pairing a 4D metric `M`, electromagnetic
four-potential `A`, and dilaton scalar `φ`. -/
structure KaluzaKleinData where
  /-- Nondegenerate four-dimensional spacetime metric. -/
  M : MetricTensor 4
  /-- Electromagnetic four-potential `A_μ`. -/
  A : Fin 4 → ℝ
  /-- Scalar dilaton field `φ`. -/
  φ : ℝ

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

end KaluzaKlein

end Modified

end GeneralRelativity
