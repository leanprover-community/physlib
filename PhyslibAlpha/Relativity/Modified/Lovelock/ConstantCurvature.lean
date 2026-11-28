/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Modified.Lovelock.Basic
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
/-!

# Constant-curvature Lovelock models

The constant-curvature algebraic tensor and its Gauss–Bonnet and Lanczos values.

## i. Overview

On `R^{ab}_{cd} = κ (δ^a_c δ^b_d - δ^a_d δ^b_c)`, the Gauss–Bonnet density is topological in four
dimensions while the Lanczos variation is non-zero in five.

## ii. Key results

- `constantCurvature` : constant-curvature algebraic tensor.
- `ricciMixed_constantCurvature`, `ricciScalar_constantCurvature`,
  `ricciSq_constantCurvature`, `riemannSq_constantCurvature` : general-`n` curvature values.
- `gaussBonnetScalar_constantCurvature` : `𝒢 = n (n - 1) (n - 2) (n - 3) κ²`.
- `gaussBonnetScalar_constantCurvature_four` : `𝒢 = 24 κ²` in 4D.
- `lanczosTensor_constantCurvature_five` : `H^i_i = -12 κ²` in 5D.

## iii. Table of contents

- A. Constant-curvature models

## iv. References

* David Lovelock, *The Four-Dimensionality of Space and the Einstein Tensor*, *Journal of
  Mathematical Physics* 13, pp. 874-876 (1972). [ref: Lovelock1972]
* T. Padmanabhan and D. Kothawala, *Lanczos-Lovelock Models of Gravity*, *Physics Reports* (2013),
  Sec. 2-3 (https://arxiv.org/pdf/1302.2151#page=4). [ref: PadmanabhanKothawala2013]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace Lovelock

/-!

## A. Constant-curvature models

A constant-curvature model is fixed by one scalar `κ`: its Riemann tensor is the maximally
symmetric combination of Kronecker deltas, so every contraction of it is an algebraic expression
in `κ` and the dimension `n`.

-/

/-- Constant-curvature model `R^{ab}_{cd} = κ (δ^a_c δ^b_d - δ^a_d δ^b_c)` in `n` dimensions. -/
def constantCurvature (n : ℕ) (κ : ℝ) : AlgebraicCurvature n where
  rUp a b c d :=
    κ * ((if a = c then 1 else 0) * (if b = d then 1 else 0)
      - (if a = d then 1 else 0) * (if b = c then 1 else 0))
  antisymm12 a b c d := by ring
  antisymm34 a b c d := by ring

/-- Mixed Ricci tensor of a constant-curvature model: `R^i_j = (n - 1) κ δ^i_j`. -/
lemma ricciMixed_constantCurvature {n : ℕ} (κ : ℝ) (i j : Fin n) :
    (constantCurvature n κ).ricciMixed i j = if i = j then ((n : ℝ) - 1) * κ else 0 := by
  by_cases h : i = j
  · subst j
    simp only [AlgebraicCurvature.ricciMixed, constantCurvature, ite_true, one_mul]
    have hterm : ∀ b : Fin n,
        κ * (1 - (if i = b then (1:ℝ) else 0) * (if b = i then 1 else 0))
          = κ * (1 - if i = b then 1 else 0) := by
      intro b
      by_cases hib : i = b
      · subst b; simp only [ite_true]; ring
      · rw [ite_eq_right hib, ite_eq_right (Ne.symm hib)]
        ring
    simp_rw [hterm, ← Finset.mul_sum]
    have hs : (∑ b : Fin n, (1 - if i = b then (1:ℝ) else 0)) = (n : ℝ) - 1 := by
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]
      simp [Finset.sum_const, Fintype.card_fin]
    rw [hs]
    ring
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun b _ => ?_
    have hb : (constantCurvature n κ).rUp i b j b = 0 := by
      by_cases hib : i = b
      · subst b
        simp only [constantCurvature, ite_eq_right h, ite_true]
        ring
      · simp only [constantCurvature, ite_eq_right h, ite_eq_right hib, ite_true]
        ring
    exact hb

/-- Ricci scalar of a constant-curvature model: `R = n (n - 1) κ`. -/
lemma ricciScalar_constantCurvature {n : ℕ} (κ : ℝ) :
    (constantCurvature n κ).ricciScalar = (n : ℝ) * ((n : ℝ) - 1) * κ := by
  rw [← AlgebraicCurvature.trace_ricciMixed]
  simp_rw [ricciMixed_constantCurvature]
  simp [Finset.sum_const, Fintype.card_fin]
  ring

/-- Ricci-square of a constant-curvature model: `R_{ij} R^{ij} = n ((n - 1) κ)²`. -/
lemma ricciSq_constantCurvature {n : ℕ} (κ : ℝ) :
    (constantCurvature n κ).ricciSq = (n : ℝ) * (((n : ℝ) - 1) * κ) ^ 2 := by
  simp only [AlgebraicCurvature.ricciSq]
  simp_rw [ricciMixed_constantCurvature]
  have hinner : ∀ a : Fin n,
      (∑ b : Fin n,
        (if a = b then ((n : ℝ) - 1) * κ else 0) *
          (if b = a then ((n : ℝ) - 1) * κ else 0)) = (((n : ℝ) - 1) * κ) ^ 2 := by
    intro a
    rw [Finset.sum_eq_single a]
    · simp only [ite_eq_left rfl, ite_true]; ring
    · intro b _ hb
      rw [ite_eq_right hb, ite_eq_right (Ne.symm hb)]
      ring
    · intro ha; exact (ha (Finset.mem_univ a)).elim
  simp_rw [hinner]
  simp [Finset.sum_const, Fintype.card_fin]

/-- Inner curvature contraction of a constant-curvature model:
`∑ c d, R^{cd}{}_{ab} R_{ab}{}^{cd}` equals `0` when `a = b` and `2 κ²` otherwise. -/
private lemma rUp_inner_constantCurvature {n : ℕ} (κ : ℝ) (a b : Fin n) :
    (∑ c : Fin n, ∑ d : Fin n,
      (constantCurvature n κ).rUp c d a b * (constantCurvature n κ).rUp a b c d)
    = if a = b then 0 else 2 * κ ^ 2 := by
  by_cases hab : a = b
  · subst b
    rw [ite_eq_left rfl]
    apply Finset.sum_eq_zero; intro c _
    apply Finset.sum_eq_zero; intro d _
    simp only [constantCurvature, ite_true]
    ring
  · rw [ite_eq_right hab]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    have ha : (∑ d : Fin n,
        (constantCurvature n κ).rUp a d a b * (constantCurvature n κ).rUp a b a d) = κ ^ 2 := by
      rw [Finset.sum_eq_single b]
      · simp only [constantCurvature, ite_true, ite_eq_right hab, ite_eq_right (Ne.symm hab)]
        ring
      · intro d _ hd
        simp only [constantCurvature, ite_true, ite_eq_right hab, ite_eq_right (Ne.symm hab),
          ite_eq_right hd]
        ring
      · intro hb; exact (hb (Finset.mem_univ b)).elim
    have hb : (∑ c ∈ Finset.univ.erase a,
        ∑ d : Fin n, (constantCurvature n κ).rUp c d a b * (constantCurvature n κ).rUp a b c d)
        = κ ^ 2 := by
      rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single a]
        · simp only [constantCurvature, ite_true, ite_eq_right hab, ite_eq_right (Ne.symm hab)]
          ring
        · intro d _ hd
          simp only [constantCurvature, ite_true, ite_eq_right hab, ite_eq_right (Ne.symm hab),
            ite_eq_right hd, ite_eq_right (Ne.symm hd)]
          ring
        · intro ha; exact (ha (Finset.mem_univ a)).elim
      · intro c hc_mem hc
        have hca : c ≠ a := Finset.ne_of_mem_erase hc_mem
        apply Finset.sum_eq_zero; intro d _
        simp only [constantCurvature, ite_true, ite_eq_right hab, ite_eq_right (Ne.symm hab),
          ite_eq_right hc, ite_eq_right (Ne.symm hc), ite_eq_right hca, ite_eq_right (Ne.symm hca)]
        ring
      · intro hb
        exfalso
        exact hb (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩)
    rw [ha, hb]
    ring

/-- Riemann-square of a constant-curvature model: `R_{abcd} R^{abcd} = 2 n (n - 1) κ²`. -/
lemma riemannSq_constantCurvature {n : ℕ} (κ : ℝ) :
    (constantCurvature n κ).riemannSq = 2 * (n : ℝ) * ((n : ℝ) - 1) * κ ^ 2 := by
  simp only [AlgebraicCurvature.riemannSq]
  simp_rw [rUp_inner_constantCurvature κ]
  have htwo : ∀ a : Fin n, (∑ b : Fin n, (if a = b then 0 else 2 * κ ^ 2))
      = ((n : ℝ) - 1) * (2 * κ ^ 2) := by
    intro a
    simp_rw [show ∀ b : Fin n, (if a = b then 0 else 2 * κ ^ 2)
        = 2 * κ ^ 2 - (if a = b then 2 * κ ^ 2 else 0) by
      intro b; split <;> simp]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]
    simp [Finset.sum_const, Fintype.card_fin]
    ring
  simp_rw [htwo]
  simp [Finset.sum_const, Fintype.card_fin]
  ring

/-- Gauss–Bonnet scalar of a constant-curvature model:
`𝒢 = n (n - 1) (n - 2) (n - 3) κ²`. -/
lemma gaussBonnetScalar_constantCurvature {n : ℕ} (κ : ℝ) :
    (constantCurvature n κ).gaussBonnetScalar =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) * κ ^ 2 := by
  simp only [AlgebraicCurvature.gaussBonnetScalar, ricciScalar_constantCurvature,
    ricciSq_constantCurvature, riemannSq_constantCurvature]
  ring

/-- In `n = 4`, a space of constant sectional curvature `κ` has non-vanishing Gauss–Bonnet
topological density `𝒢 = 24 κ²`, even though its metric variation `H^i_j` vanishes identically. -/
lemma gaussBonnetScalar_constantCurvature_four (κ : ℝ) :
    (constantCurvature 4 κ).gaussBonnetScalar = 24 * κ ^ 2 := by
  rw [gaussBonnetScalar_constantCurvature]
  norm_num

/-- In `n = 5`, the Gauss–Bonnet variation tensor `H^i_j` is dynamically non-trivial: on a 5D
constant-curvature space it evaluates to `H^i_i = -12 κ²`. -/
lemma lanczosTensor_constantCurvature_five (κ : ℝ) (i : Fin 5) :
    (constantCurvature 5 κ).lanczosTensor i i = -12 * κ ^ 2 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by fin_cases i <;> decide
  simp only [AlgebraicCurvature.lanczosTensor]
  rw [gaussBonnetScalar_constantCurvature, ricciScalar_constantCurvature]
  simp only [ricciMixed_constantCurvature]
  simp only [constantCurvature]
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;>
    ring

end Lovelock

end Modified

end GeneralRelativity
