/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Generalized Kronecker deltas and symmetric-group coset decompositions

Antisymmetric `k`-index generalized Kronecker delta `δ^{a_0 … a_{k-1}}_{b_0 … b_{k-1}}`,
pigeonhole vanishing for `n < k`, and coset decompositions of `S_4` and `S_5`.

## i. Overview

In `n` dimensions, any `k`-index generalized Kronecker delta vanishes identically whenever
`n < k` by the pigeonhole principle. Pairing this with the coset split `perm_fin5_fiber_split`
underlies the proof of the four-dimensional Bach–Lanczos identity in `Lovelock.Basic`.

## ii. Key results

- `genKronecker`, `genKronecker_eq_zero_of_lt` : `k`-index generalized Kronecker delta and
  dimensional pigeonhole vanishing.
- `perm_fin5_fiber_split` : antisymmetric permutation-sum coset split on `S_5`.

## iii. Table of contents

- A. Generalized Kronecker delta and dimensional vanishing
- B. Antisymmetric coset decompositions of `S_4` and `S_5`

## iv. References

* Cornelius Lanczos, *A Remarkable Property of the Riemann-Christoffel Tensor in Four Dimensions*,
  *Annals of Mathematics* (1938). [ref: Lanczos1938]
* David Lovelock, *The Einstein Tensor and Its Generalizations*, *Journal of Mathematical Physics*
  (1971). [ref: Lovelock1971]
* David Lovelock, *The Four-Dimensionality of Space and the Einstein Tensor*, *Journal of
  Mathematical Physics* (1972). [ref: Lovelock1972]
* T. Padmanabhan and D. Kothawala, *Lanczos-Lovelock Models of Gravity*, *Physics Reports* (2013)
  (https://arxiv.org/abs/1302.2151). [ref: PadmanabhanKothawala2013]

-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace Lovelock

open Equiv

/-!

## A. Generalized Kronecker delta and dimensional vanishing

-/

/-- Generalized `k`-index Kronecker delta `δ^{a_0 … a_{k-1}}_{b_0 … b_{k-1}}` in `n` dimensions,
defined as the signed sum over all permutations `σ ∈ S_k`. -/
noncomputable def genKronecker {n : ℕ} (k : ℕ) (a b : Fin k → Fin n) : ℝ :=
  ∑ σ : Perm (Fin k), ((Perm.sign σ : ℤ) : ℝ) * ∏ t : Fin k, if a t = b (σ t) then 1 else 0

/-- Pigeonhole vanishing of the generalized Kronecker delta: in dimension `n < k`, any `k`-index
generalized Kronecker delta vanishes identically. -/
lemma genKronecker_eq_zero_of_lt {n k : ℕ} (h : n < k) (a b : Fin k → Fin n) :
    genKronecker k a b = 0 := by
  have hcard : Fintype.card (Fin n) < Fintype.card (Fin k) := by
    simpa [Fintype.card_fin] using h
  obtain ⟨s₁, s₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt a hcard
  let τ : Perm (Fin k) := Equiv.swap s₁ s₂
  have hτ_sign : ((Perm.sign τ : ℤ) : ℝ) = -1 := by
    simp [τ, Perm.sign_swap hne]
  have hτ_a : ∀ t : Fin k, a (τ t) = a t := by
    intro t
    by_cases ht1 : t = s₁
    · subst ht1; simp [τ, heq]
    · by_cases ht2 : t = s₂
      · subst ht2; simp [τ, heq]
      · simp [τ, Equiv.swap_apply_of_ne_of_ne ht1 ht2]
  have hprod : ∀ σ : Perm (Fin k),
      (∏ t : Fin k, if a t = b ((σ * τ) t) then (1 : ℝ) else 0)
        = ∏ t : Fin k, if a t = b (σ t) then (1 : ℝ) else 0 := by
    intro σ
    rw [← Equiv.prod_comp τ (fun t => if a t = b (σ t) then (1 : ℝ) else 0)]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [Perm.mul_apply, hτ_a t]
  have hsum : genKronecker k a b = -genKronecker k a b := by
    unfold genKronecker
    conv_lhs => rw [← Equiv.sum_comp (Equiv.mulRight τ)]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hmr : Equiv.mulRight τ σ = σ * τ := rfl
    rw [hmr, hprod σ, map_mul, Units.val_mul, Int.cast_mul, hτ_sign]
    ring
  linarith

/-!

## B. Antisymmetric coset decompositions of `S_4` and `S_5`

-/

private abbrev p4 (a : Fin 4) (b : Fin 3) (c : Fin 2) : Perm (Fin 4) :=
  Perm.decomposeFin.symm (a, Perm.decomposeFin.symm (b, Perm.decomposeFin.symm (c, 1)))

private lemma p4_sign (a : Fin 4) (b : Fin 3) (c : Fin 2) :
    Perm.sign (p4 a b c) =
      (if a = 0 then 1 else -1) * (if b = 0 then 1 else -1) * (if c = 0 then 1 else -1) := by
  decide +revert

private lemma p5_sign (k : Fin 5) (a : Fin 4) (b : Fin 3) (c : Fin 2) :
    Perm.sign (Perm.decomposeFin.symm (k, p4 a b c)) =
      (if k = 0 then 1 else -1) * Perm.sign (p4 a b c) := by
  decide +revert

private lemma sum_perm_fin4_eq (g : Perm (Fin 4) → ℝ) :
    (∑ q : Perm (Fin 4), g q) = ∑ a : Fin 4, ∑ b : Fin 3, ∑ c : Fin 2, g (p4 a b c) := by
  rw [← Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_unique]
  rfl

/-- Six-coset decomposition of `S_4` for any 4-argument function antisymmetric in its first pair
and second pair. -/
private lemma perm_fin4_split (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h12 : ∀ a b c d, F a b c d = -F b a c d)
    (h34 : ∀ a b c d, F a b c d = -F a b d c) :
    (∑ q : Perm (Fin 4), ((Perm.sign q : ℤ) : ℝ) * F (q 0) (q 1) (q 2) (q 3))
      = 4 * (F 0 1 2 3 - F 0 2 1 3 + F 0 3 1 2 + F 1 2 0 3 - F 1 3 0 2 + F 2 3 0 1) := by
  rw [sum_perm_fin4_eq]
  simp_rw [p4_sign]
  simp only [Fin.sum_univ_four, Fin.sum_univ_three, Fin.sum_univ_two,
    Fin.isValue, Fin.reduceEq, ↓reduceIte,
    Units.val_mul, Int.cast_mul, Units.val_one, Int.cast_one,
    Units.val_neg, Int.cast_neg]
  change
    1 * 1 * 1 * F 0 1 2 3 + 1 * 1 * -1 * F 0 1 3 2 +
      (1 * -1 * 1 * F 0 2 1 3 + 1 * -1 * -1 * F 0 2 3 1) +
      (1 * -1 * 1 * F 0 3 2 1 + 1 * -1 * -1 * F 0 3 1 2) +
    (-1 * 1 * 1 * F 1 0 2 3 + -1 * 1 * -1 * F 1 0 3 2 +
      (-1 * -1 * 1 * F 1 2 0 3 + -1 * -1 * -1 * F 1 2 3 0) +
      (-1 * -1 * 1 * F 1 3 2 0 + -1 * -1 * -1 * F 1 3 0 2)) +
    (-1 * 1 * 1 * F 2 1 0 3 + -1 * 1 * -1 * F 2 1 3 0 +
      (-1 * -1 * 1 * F 2 0 1 3 + -1 * -1 * -1 * F 2 0 3 1) +
      (-1 * -1 * 1 * F 2 3 0 1 + -1 * -1 * -1 * F 2 3 1 0)) +
    (-1 * 1 * 1 * F 3 1 2 0 + -1 * 1 * -1 * F 3 1 0 2 +
      (-1 * -1 * 1 * F 3 2 1 0 + -1 * -1 * -1 * F 3 2 0 1) +
      (-1 * -1 * 1 * F 3 0 2 1 + -1 * -1 * -1 * F 3 0 1 2)) =
    4 * (F 0 1 2 3 - F 0 2 1 3 + F 0 3 1 2 + F 1 2 0 3 - F 1 3 0 2 + F 2 3 0 1)
  simp_rw [h12 1 0, h12 2 0, h12 3 0, h12 2 1, h12 3 1, h12 3 2]
  simp_rw [h34 _ _ 1 0, h34 _ _ 2 0, h34 _ _ 3 0, h34 _ _ 2 1, h34 _ _ 3 1, h34 _ _ 3 2]
  ring

lemma perm_fin5_fiber_split (k : Fin 5) (F : Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℝ)
    (h12 : ∀ a b c d, F a b c d = -F b a c d)
    (h34 : ∀ a b c d, F a b c d = -F a b d c) :
    (∑ q : Perm (Fin 4),
      ((Perm.sign (Perm.decomposeFin.symm (k, q)) : ℤ) : ℝ) *
        F (Perm.decomposeFin.symm (k, q) 1) (Perm.decomposeFin.symm (k, q) 2)
          (Perm.decomposeFin.symm (k, q) 3) (Perm.decomposeFin.symm (k, q) 4))
      = ((if k = 0 then (1 : ℝ) else -1)) * 4 *
        (let s := fun m : Fin 4 => Equiv.swap 0 k m.succ
         F (s 0) (s 1) (s 2) (s 3) - F (s 0) (s 2) (s 1) (s 3) + F (s 0) (s 3) (s 1) (s 2)
           + F (s 1) (s 2) (s 0) (s 3) - F (s 1) (s 3) (s 0) (s 2)
           + F (s 2) (s 3) (s 0) (s 1)) := by
  let s : Fin 4 → Fin 5 := fun m => Equiv.swap 0 k m.succ
  have hsign : ∀ q : Perm (Fin 4),
      ((Perm.sign (Perm.decomposeFin.symm (k, q)) : ℤ) : ℝ) *
        F (Perm.decomposeFin.symm (k, q) 1) (Perm.decomposeFin.symm (k, q) 2)
          (Perm.decomposeFin.symm (k, q) 3) (Perm.decomposeFin.symm (k, q) 4) =
      (if k = 0 then (1 : ℝ) else -1) *
        (((Perm.sign q : ℤ) : ℝ) * F (s (q 0)) (s (q 1)) (s (q 2)) (s (q 3))) := by
    intro q
    let a := (Perm.decomposeFin q).1
    let q1 := (Perm.decomposeFin q).2
    let b := (Perm.decomposeFin q1).1
    let q2 := (Perm.decomposeFin q1).2
    let c := (Perm.decomposeFin q2).1
    let d := (Perm.decomposeFin q2).2
    have hq : q = p4 a b c := by
      have hd : d = 1 := Subsingleton.elim d 1
      dsimp [p4, a, b, c, q1, q2]
      rw [← hd]
      simp [d, q2, q1]
    rw [hq]
    change ((Perm.sign (Perm.decomposeFin.symm (k, p4 a b c)) : ℤ) : ℝ) *
        F (Perm.decomposeFin.symm (k, p4 a b c) (Fin.succ 0))
          (Perm.decomposeFin.symm (k, p4 a b c) (Fin.succ 1))
          (Perm.decomposeFin.symm (k, p4 a b c) (Fin.succ 2))
          (Perm.decomposeFin.symm (k, p4 a b c) (Fin.succ 3)) = _
    rw [p5_sign k a b c, Perm.decomposeFin_symm_apply_succ,
      Perm.decomposeFin_symm_apply_succ, Perm.decomposeFin_symm_apply_succ,
      Perm.decomposeFin_symm_apply_succ, Units.val_mul, Int.cast_mul]
    split_ifs <;> simp <;> ring
  simp_rw [hsign, ← Finset.mul_sum]
  rw [perm_fin4_split (fun x y z w => F (s x) (s y) (s z) (s w))
    (fun a b c d => h12 (s a) (s b) (s c) (s d))
    (fun a b c d => h34 (s a) (s b) (s c) (s d))]
  ring

end Lovelock

end Modified

end GeneralRelativity
