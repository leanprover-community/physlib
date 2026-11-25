/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.Notation
public import PhyslibAlpha.Relativity.Metrics.MetricTrace
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
- `extendedPotential`, `metric4Ext`, `kkMetric`, `contravariantPotential`, `kkMetricInv` : 5D
  metric and analytical inverse.
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

/-- Five-component extension `(A_0, A_1, A_2, A_3, 1)` of a 4D gauge potential `A`. Padding with
the fifth component `1` allows `kkMetric` to express the off-diagonal `(μ, 4)` and `(4, 4)`
Kaluza–Klein entries as a uniform product `φ² A_A A_B` on `Fin 5` without index case-splitting. -/
def extendedPotential (A : Fin 4 → ℝ) : Fin 5 → ℝ := ![A 0, A 1, A 2, A 3, 1]

@[simp]
private lemma extendedPotential_apply_lt (A : Fin 4 → ℝ) {i : Fin 5} (hi : i.val < 4) :
    extendedPotential A i = A ⟨i.val, hi⟩ := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact absurd hi (by decide)

@[simp]
private lemma extendedPotential_four (A : Fin 4 → ℝ) :
    extendedPotential A 4 = 1 := rfl

/-- Five-dimensional zero-padded embedding of a 4D rank-2 tensor `g4`. This auxiliary block
extension lets `kkMetric` write the Kaluza–Klein metric ansatz uniformly over `Fin 5 × Fin 5`
without splitting `4 × 4` vs. fifth-dimension cases in its top-level formula. -/
def metric4Ext (g4 : Tensor2 4) : Tensor2 5 :=
  fun i j =>
    if hi : i.val < 4 then
      if hj : j.val < 4 then g4 ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
    else 0

/-- Five-dimensional Kaluza–Klein metric `G_{AB} = g^{(4)}_{AB} + φ² A_A A_B` with `A_4 = 1`. -/
def kkMetric (g4 : Tensor2 4) (A : Fin 4 → ℝ) (φ : ℝ) : Tensor2 5 :=
  fun i j => metric4Ext g4 i j + φ ^ 2 * extendedPotential A i * extendedPotential A j

/-- The 5D Kaluza–Klein metric of a `KaluzaKleinData` bundle. -/
def KaluzaKleinData.metric (D : KaluzaKleinData) : Tensor2 5 :=
  kkMetric D.M.g D.A D.φ

@[simp]
private lemma kkMetric_apply_lt_lt (g4 : Tensor2 4) (A : Fin 4 → ℝ) (φ : ℝ)
    {i j : Fin 5} (hi : i.val < 4) (hj : j.val < 4) :
    kkMetric g4 A φ i j =
      g4 ⟨i.val, hi⟩ ⟨j.val, hj⟩ + φ ^ 2 * A ⟨i.val, hi⟩ * A ⟨j.val, hj⟩ := by
  simp only [kkMetric, metric4Ext, hi, hj, ↓reduceDIte, extendedPotential_apply_lt]

@[simp]
private lemma kkMetric_apply_lt_four (g4 : Tensor2 4) (A : Fin 4 → ℝ) (φ : ℝ)
    {i : Fin 5} (hi : i.val < 4) :
    kkMetric g4 A φ i 4 = φ ^ 2 * A ⟨i.val, hi⟩ := by
  simp only [kkMetric, metric4Ext, hi, show ¬((4 : Fin 5).val < 4) by decide, ↓reduceDIte,
    extendedPotential_apply_lt, extendedPotential_four]
  ring

@[simp]
private lemma kkMetric_apply_four_lt (g4 : Tensor2 4) (A : Fin 4 → ℝ) (φ : ℝ)
    {j : Fin 5} (hj : j.val < 4) :
    kkMetric g4 A φ 4 j = φ ^ 2 * A ⟨j.val, hj⟩ := by
  simp only [kkMetric, metric4Ext, hj, show ¬((4 : Fin 5).val < 4) by decide, ↓reduceDIte,
    extendedPotential_apply_lt, extendedPotential_four]
  ring

@[simp]
private lemma kkMetric_apply_four_four (g4 : Tensor2 4) (A : Fin 4 → ℝ) (φ : ℝ) :
    kkMetric g4 A φ 4 4 = φ ^ 2 := by
  simp only [kkMetric, metric4Ext, show ¬((4 : Fin 5).val < 4) by decide, ↓reduceDIte,
    extendedPotential_four]
  ring

/-- Symmetry of `kkMetric g4 A φ` whenever `g4` is symmetric. -/
lemma kkMetric_symm (g4 : Tensor2 4) (hg : IsSymm g4) (A : Fin 4 → ℝ) (φ : ℝ) :
    IsSymm (kkMetric g4 A φ) := by
  ext i j
  simp only [Matrix.transpose_apply, kkMetric, metric4Ext]
  by_cases hi : i.val < 4 <;> by_cases hj : j.val < 4
  · simp only [hi, hj, ↓reduceDIte, hg.apply ⟨i.val, hi⟩ ⟨j.val, hj⟩]; ring
  · simp only [hi, hj, ↓reduceDIte]; ring
  · simp only [hi, hj, ↓reduceDIte]; ring
  · simp only [hi, hj, ↓reduceDIte]; ring

/-- Contravariant 4D potential `A^μ = ∑_ν g^{μν} A_ν`. -/
def contravariantPotential (ginv4 : Tensor2 4) (A : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  ∑ k : Fin 4, ginv4 i k * A k

/-- Five-dimensional analytical inverse of the Kaluza–Klein metric `kkMetric g4 A φ`. -/
noncomputable def kkMetricInv (ginv4 : Tensor2 4) (A : Fin 4 → ℝ) (φ : ℝ) : Tensor2 5 :=
  fun i j =>
    if hi : i.val < 4 then
      if hj : j.val < 4 then ginv4 ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else -contravariantPotential ginv4 A ⟨i.val, hi⟩
    else
      if hj : j.val < 4 then -contravariantPotential ginv4 A ⟨j.val, hj⟩
      else 1 / φ ^ 2 + ∑ k : Fin 4, A k * contravariantPotential ginv4 A k

@[simp]
private lemma kkMetricInv_apply_lt_lt (ginv4 : Tensor2 4) (A : Fin 4 → ℝ) (φ : ℝ)
    {i j : Fin 5} (hi : i.val < 4) (hj : j.val < 4) :
    kkMetricInv ginv4 A φ i j = ginv4 ⟨i.val, hi⟩ ⟨j.val, hj⟩ := by
  simp [kkMetricInv, hi, hj]

@[simp]
private lemma kkMetricInv_apply_lt_four (ginv4 : Tensor2 4) (A : Fin 4 → ℝ) (φ : ℝ)
    {i : Fin 5} (hi : i.val < 4) :
    kkMetricInv ginv4 A φ i 4 = -contravariantPotential ginv4 A ⟨i.val, hi⟩ := by
  simp [kkMetricInv, hi]

@[simp]
private lemma kkMetricInv_apply_four_lt (ginv4 : Tensor2 4) (A : Fin 4 → ℝ) (φ : ℝ)
    {j : Fin 5} (hj : j.val < 4) :
    kkMetricInv ginv4 A φ 4 j = -contravariantPotential ginv4 A ⟨j.val, hj⟩ := by
  simp [kkMetricInv, hj]

@[simp]
private lemma kkMetricInv_apply_four_four (ginv4 : Tensor2 4) (A : Fin 4 → ℝ) (φ : ℝ) :
    kkMetricInv ginv4 A φ 4 4 =
      1 / φ ^ 2 + ∑ k : Fin 4, A k * contravariantPotential ginv4 A k := by
  simp [kkMetricInv]

private lemma sum_fin5_split (f : Fin 5 → ℝ) :
    (∑ k : Fin 5, f k) = (∑ k : Fin 4, f ⟨k.val, by omega⟩) + f 4 := by
  simp only [Fin.sum_univ_five, Fin.sum_univ_four]
  rfl

private lemma contravariantPotential_mul_g (M : MetricTensor 4) (A : Fin 4 → ℝ) (b : Fin 4) :
    (∑ k : Fin 4, contravariantPotential M.ginv A k * M.g k b) = A b :=
  M.sum_mul_ginv_g_apply b A

private lemma kkMetricInv_mul_kkMetric_44 (M : MetricTensor 4) (A : Fin 4 → ℝ) (φ : ℝ)
    {i j : Fin 5} (hi : i.val < 4) (hj : j.val < 4) :
    (∑ k : Fin 5, kkMetricInv M.ginv A φ i k * kkMetric M.g A φ k j) =
      if i = j then 1 else 0 := by
  let i4 : Fin 4 := ⟨i.val, hi⟩
  let j4 : Fin 4 := ⟨j.val, hj⟩
  have hij : (i = j) ↔ (i4 = j4) := by simp [i4, j4, Fin.ext_iff]
  rw [sum_fin5_split]
  have h1 : ∀ x : Fin 4,
      kkMetricInv M.ginv A φ i ⟨x.val, by omega⟩ * kkMetric M.g A φ ⟨x.val, by omega⟩ j =
        M.ginv i4 x * M.g x j4 + φ ^ 2 * A j4 * (M.ginv i4 x * A x) := by
    intro x
    rw [kkMetricInv_apply_lt_lt M.ginv A φ hi x.isLt,
      kkMetric_apply_lt_lt M.g A φ x.isLt hj]
    ring
  simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, M.sum_ginv_mul_g_left i4 j4,
    kkMetricInv_apply_lt_four M.ginv A φ hi, kkMetric_apply_four_lt M.g A φ hj, hij]
  simp only [contravariantPotential]
  ring

private lemma kkMetricInv_mul_kkMetric_45 (M : MetricTensor 4) (A : Fin 4 → ℝ) (φ : ℝ)
    {i : Fin 5} (hi : i.val < 4) :
    (∑ k : Fin 5, kkMetricInv M.ginv A φ i k * kkMetric M.g A φ k 4) = 0 := by
  let i4 : Fin 4 := ⟨i.val, hi⟩
  rw [sum_fin5_split]
  have h1 : ∀ x : Fin 4,
      kkMetricInv M.ginv A φ i ⟨x.val, by omega⟩ * kkMetric M.g A φ ⟨x.val, by omega⟩ 4 =
        φ ^ 2 * (M.ginv i4 x * A x) := by
    intro x
    rw [kkMetricInv_apply_lt_lt M.ginv A φ hi x.isLt, kkMetric_apply_lt_four M.g A φ x.isLt]
    ring
  simp only [h1, ← Finset.mul_sum, kkMetricInv_apply_lt_four M.ginv A φ hi,
    kkMetric_apply_four_four M.g A φ, contravariantPotential]
  ring

private lemma kkMetricInv_mul_kkMetric_54 (M : MetricTensor 4) (A : Fin 4 → ℝ) (φ : ℝ)
    (hφ : φ ≠ 0) {j : Fin 5} (hj : j.val < 4) :
    (∑ k : Fin 5, kkMetricInv M.ginv A φ 4 k * kkMetric M.g A φ k j) = 0 := by
  let j4 : Fin 4 := ⟨j.val, hj⟩
  have hφ2 : φ ^ 2 ≠ 0 := pow_ne_zero 2 hφ
  rw [sum_fin5_split]
  have h1 : ∀ x : Fin 4,
      kkMetricInv M.ginv A φ 4 ⟨x.val, by omega⟩ * kkMetric M.g A φ ⟨x.val, by omega⟩ j =
        -(contravariantPotential M.ginv A x * M.g x j4)
          - φ ^ 2 * A j4 * (A x * contravariantPotential M.ginv A x) := by
    intro x
    rw [kkMetricInv_apply_four_lt M.ginv A φ x.isLt, kkMetric_apply_lt_lt M.g A φ x.isLt hj]
    ring
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
    contravariantPotential_mul_g M A j4, kkMetricInv_apply_four_four M.ginv A φ,
    kkMetric_apply_four_lt M.g A φ hj]
  field_simp [hφ2]
  ring

private lemma kkMetricInv_mul_kkMetric_55 (M : MetricTensor 4) (A : Fin 4 → ℝ) (φ : ℝ)
    (hφ : φ ≠ 0) :
    (∑ k : Fin 5, kkMetricInv M.ginv A φ 4 k * kkMetric M.g A φ k 4) = 1 := by
  have hφ2 : φ ^ 2 ≠ 0 := pow_ne_zero 2 hφ
  rw [sum_fin5_split]
  have h1 : ∀ x : Fin 4,
      kkMetricInv M.ginv A φ 4 ⟨x.val, by omega⟩ * kkMetric M.g A φ ⟨x.val, by omega⟩ 4 =
        -(φ ^ 2 * (A x * contravariantPotential M.ginv A x)) := by
    intro x
    rw [kkMetricInv_apply_four_lt M.ginv A φ x.isLt, kkMetric_apply_lt_four M.g A φ x.isLt]
    ring
  simp only [h1, Finset.sum_neg_distrib, ← Finset.mul_sum,
    kkMetricInv_apply_four_four M.ginv A φ, kkMetric_apply_four_four M.g A φ]
  field_simp [hφ2]
  ring

/-- Left-inverse identity `kkMetricInv * kkMetric = 1` for any `M : MetricTensor 4` and `φ ≠ 0`. -/
lemma kkMetricInv_mul_kkMetric (M : MetricTensor 4) (A : Fin 4 → ℝ) (φ : ℝ) (hφ : φ ≠ 0) :
    kkMetricInv M.ginv A φ * kkMetric M.g A φ = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hi : i.val < 4 <;> by_cases hj : j.val < 4
  · exact kkMetricInv_mul_kkMetric_44 M A φ hi hj
  · have hj4 : j = 4 := by ext; omega
    have hij : i ≠ 4 := by intro h; rw [h] at hi; exact absurd hi (by decide)
    simp only [hj4, hij, ↓reduceIte]
    exact kkMetricInv_mul_kkMetric_45 M A φ hi
  · have hi4 : i = 4 := by ext; omega
    have hij : (4 : Fin 5) ≠ j := by intro h; rw [← h] at hj; exact absurd hj (by decide)
    simp only [hi4, hij, ↓reduceIte]
    exact kkMetricInv_mul_kkMetric_54 M A φ hφ hj
  · have hi4 : i = 4 := by ext; omega
    have hj4 : j = 4 := by ext; omega
    simp only [hi4, hj4, ↓reduceIte]
    exact kkMetricInv_mul_kkMetric_55 M A φ hφ

/-- Symmetry of `kkMetricInv M.ginv A φ` for any `M : MetricTensor 4`. -/
lemma kkMetricInv_symm (M : MetricTensor 4) (A : Fin 4 → ℝ) (φ : ℝ) :
    IsSymm (kkMetricInv M.ginv A φ) := by
  have hginv_symm : IsSymm M.ginv := M.ginv_symm
  ext i j
  simp only [Matrix.transpose_apply, kkMetricInv]
  by_cases hi : i.val < 4 <;> by_cases hj : j.val < 4
  · simp [hi, hj, hginv_symm.apply ⟨i.val, hi⟩ ⟨j.val, hj⟩]
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
    (kkMetric_symm M.g M.symm A φ).eq
  have hs2 : (kkMetricInv M.ginv A φ).transpose = kkMetricInv M.ginv A φ :=
    (kkMetricInv_symm M A φ).eq
  rwa [hs1, hs2] at hT

/-- Package the 5D Kaluza–Klein metric and its inverse as a `MetricTensor 5`. -/
noncomputable def kkMetricTensor (M : MetricTensor 4) (A : Fin 4 → ℝ) (φ : ℝ) (hφ : φ ≠ 0) :
    MetricTensor 5 where
  g := kkMetric M.g A φ
  ginv := kkMetricInv M.ginv A φ
  symm := kkMetric_symm M.g M.symm A φ
  inv_left := kkMetric_mul_kkMetricInv M A φ hφ
  inv_right := kkMetricInv_mul_kkMetric M A φ hφ

/-- The inverse 5D Kaluza–Klein metric of a `KaluzaKleinData` bundle. -/
noncomputable def KaluzaKleinData.metricInv (D : KaluzaKleinData) : Tensor2 5 :=
  kkMetricInv D.M.ginv D.A D.φ

end KaluzaKlein

end Modified

end GeneralRelativity
