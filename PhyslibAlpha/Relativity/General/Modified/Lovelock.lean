/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Einstein
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Lovelock and Gauss–Bonnet higher-curvature gravity

Generalized Kronecker deltas, dimensional pigeonhole vanishing, algebraic curvature tensors,
the Gauss–Bonnet scalar and Lanczos–Bach–Lovelock tensor, the five-index Lovelock contraction
identity in arbitrary dimension `n`, and identical vanishing of the Gauss–Bonnet variation in four
dimensions.

## i. Overview

Lovelock's theorem characterizes the most general symmetric, divergence-free second-rank tensors
constructed from a metric and its first two derivatives in `n` spacetime dimensions. At quadratic
order in curvature, the unique Lovelock combination is the Gauss–Bonnet density
`𝒢 = R² - 4 R^a_b R^b_a + R^{cd}_{ab} R^{ab}_{cd}`, whose metric variation yields the Lanczos
tensor `H^i_j`. Expressing `H^i_j` as `-⅛ δ^{i a b c d}_{j e f g h} R^{e f}_{a b} R^{g h}_{c d}`
shows that `H^i_j = 0` identically whenever `n ≤ 4` because any 5-index antisymmetrized Kronecker
tensor vanishes by the pigeonhole principle in fewer than 5 dimensions.

## ii. Key results

- `genKronecker`, `genKronecker_eq_zero_of_lt` : `k`-index generalized Kronecker delta and
  pigeonhole vanishing for `n < k`.
- `AlgCurvature`, `gaussBonnetScalar`, `gaussBonnetTensor` : algebraic `(2,2)` curvature structure,
  quadratic Gauss–Bonnet invariant, and Lanczos tensor `H^i_j`.
- `lovelockContract5`, `lovelockContract5_eq_zero_of_lt`,
  `lovelockContract5_eq_neg_eight_gaussBonnet` : 5-index Kronecker contraction and exact identity
  `lovelockContract5 C i j = -8 * gaussBonnetTensor C i j` in arbitrary dimension `n`.
- `gaussBonnetTensor_eq_zero_of_lt_five`, `gaussBonnetTensor_four_eq_zero` : Bach–Lanczos theorem
  that the Gauss–Bonnet variation vanishes identically in `n ≤ 4`.
- `constCurv`, `gaussBonnetScalar_constCurv_four`, `gaussBonnetTensor_constCurv_five` :
  constant-curvature spaces demonstrating non-zero 4D topological scalar vs non-zero 5D dynamical
  variation.

## iii. Table of contents

- A. Generalized Kronecker delta and dimensional vanishing
- B. Algebraic curvature tensors and Gauss–Bonnet invariants
- C. Five-index Lovelock contraction and four-dimensional vanishing

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

## B. Algebraic curvature tensors and Gauss–Bonnet invariants

-/

/-- Algebraic `(2,2)` mixed Riemann curvature tensor `R^{ab}_{cd}` in `n` dimensions, carrying
antisymmetry in both the upper index pair `(a, b)` and the lower index pair `(c, d)`. -/
structure AlgCurvature (n : ℕ) where
  /-- Mixed `(2,2)` curvature components `R^{ab}_{cd}`. -/
  rUp : Fin n → Fin n → Fin n → Fin n → ℝ
  /-- Antisymmetry in the first (upper) pair of indices: `R^{ab}_{cd} = -R^{ba}_{cd}`. -/
  antisymm12 : ∀ a b c d, rUp a b c d = -rUp b a c d
  /-- Antisymmetry in the second (lower) pair of indices: `R^{ab}_{cd} = -R^{ab}_{dc}`. -/
  antisymm34 : ∀ a b c d, rUp a b c d = -rUp a b d c

/-- Mixed `(1,1)` Ricci tensor `R^i_j = ∑_b R^{ib}_{jb}`. -/
def AlgCurvature.ricciMixed {n : ℕ} (C : AlgCurvature n) (i j : Fin n) : ℝ :=
  ∑ b : Fin n, C.rUp i b j b

/-- Scalar curvature `R = ∑_{a,b} R^{ab}_{ab}`. -/
def AlgCurvature.scalarCurv {n : ℕ} (C : AlgCurvature n) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n, C.rUp a b a b

/-- Trace of the squared Ricci tensor equals the scalar curvature: `∑_i R^i_i = R`. -/
lemma AlgCurvature.trace_ricciMixed {n : ℕ} (C : AlgCurvature n) :
    (∑ i : Fin n, C.ricciMixed i i) = C.scalarCurv := by
  rfl

/-- Quadratic Ricci invariant `R^a_b R^b_a`. -/
def AlgCurvature.ricciSq {n : ℕ} (C : AlgCurvature n) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n, C.ricciMixed a b * C.ricciMixed b a

/-- Quadratic Riemann (Kretschmann) invariant `R^{cd}_{ab} R^{ab}_{cd}`. -/
def AlgCurvature.riemannSq {n : ℕ} (C : AlgCurvature n) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp c d a b * C.rUp a b c d

/-- Quadratic Gauss–Bonnet scalar density `𝒢 = R² - 4 R^a_b R^b_a + R^{cd}_{ab} R^{ab}_{cd}`. -/
def AlgCurvature.gaussBonnetScalar {n : ℕ} (C : AlgCurvature n) : ℝ :=
  C.scalarCurv ^ 2 - 4 * C.ricciSq + C.riemannSq

/-- Mixed `(1,1)` Lanczos–Bach–Gauss–Bonnet variation tensor
`H^i_j = -½ δ^i_j 𝒢 + 2 R R^i_j - 4 R^i_c R^c_j - 4 R^{ic}_{jb} R^b_c + 2 R^{cd}_{jb} R^{ib}_{cd}`.
-/
noncomputable def AlgCurvature.gaussBonnetTensor {n : ℕ} (C : AlgCurvature n) (i j : Fin n) : ℝ :=
  -(1 / 2) * (if i = j then C.gaussBonnetScalar else 0)
    + 2 * C.scalarCurv * C.ricciMixed i j
    - 4 * (∑ c : Fin n, C.ricciMixed i c * C.ricciMixed c j)
    - 4 * (∑ b : Fin n, ∑ c : Fin n, C.rUp i c j b * C.ricciMixed b c)
    + 2 * (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp c d j b * C.rUp i b c d)

/-!

## C. Five-index Lovelock contraction and four-dimensional vanishing

-/

/-- Five-index Lovelock Kronecker contraction
`L^i_j = ∑_{a,b,c,d} ∑_{p ∈ S_5} sgn(p) δ^{v_{p(0)}}_j R^{v_{p(1)} v_{p(2)}}_{a b}
R^{v_{p(3)} v_{p(4)}}_{c d}` with `v = (i, a, b, c, d)`. -/
noncomputable def lovelockContract5 {n : ℕ} (C : AlgCurvature n) (i j : Fin n) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
    ∑ p : Perm (Fin 5), ((Perm.sign p : ℤ) : ℝ) *
      (if ![i, a, b, c, d] (p 0) = j then (1 : ℝ) else 0) *
      C.rUp (![i, a, b, c, d] (p 1)) (![i, a, b, c, d] (p 2)) a b *
      C.rUp (![i, a, b, c, d] (p 3)) (![i, a, b, c, d] (p 4)) c d

/-- Equivalence of `lovelockContract5` with the full 8-index generalized Kronecker sum over
`a, b, c, d, e, f, g, h`. -/
lemma lovelockContract5_eq_kronecker_sum {n : ℕ} (C : AlgCurvature n) (i j : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
      ∑ e : Fin n, ∑ f : Fin n, ∑ g : Fin n, ∑ h : Fin n,
        genKronecker 5 ![i, a, b, c, d] ![j, e, f, g, h] * C.rUp e f a b * C.rUp g h c d)
      = lovelockContract5 C i j := by
  unfold lovelockContract5
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  let top : Fin 5 → Fin n := ![i, a, b, c, d]
  have hinner :
      (∑ e : Fin n, ∑ f : Fin n, ∑ g : Fin n, ∑ h : Fin n,
        genKronecker 5 top ![j, e, f, g, h] * C.rUp e f a b * C.rUp g h c d)
        = ∑ p : Perm (Fin 5), ((Perm.sign p : ℤ) : ℝ) *
            (if top (p 0) = j then (1 : ℝ) else 0) *
            C.rUp (top (p 1)) (top (p 2)) a b * C.rUp (top (p 3)) (top (p 4)) c d := by
    have hgk : ∀ e f g h : Fin n,
        genKronecker 5 top ![j, e, f, g, h] =
          ∑ p : Perm (Fin 5), ((Perm.sign p : ℤ) : ℝ) *
            ((if top (p 0) = j then (1 : ℝ) else 0) * (if top (p 1) = e then (1 : ℝ) else 0) *
             (if top (p 2) = f then (1 : ℝ) else 0) * (if top (p 3) = g then (1 : ℝ) else 0) *
             (if top (p 4) = h then (1 : ℝ) else 0)) := by
      intro e f g h
      unfold genKronecker
      rw [← Equiv.sum_comp (Equiv.inv (Perm (Fin 5)))]
      refine Finset.sum_congr rfl fun p _ => ?_
      have hinv : Equiv.inv (Perm (Fin 5)) p = p⁻¹ := rfl
      rw [hinv, Perm.sign_inv]
      congr 1
      rw [← Equiv.prod_comp p]
      have hp : ∀ t : Fin 5,
          (if top (p t) = ![j, e, f, g, h] (p⁻¹ (p t)) then (1 : ℝ) else 0) =
            (if top (p t) = ![j, e, f, g, h] t then (1 : ℝ) else 0) := by
        intro t
        rw [Perm.inv_def, Equiv.symm_apply_apply]
      simp_rw [hp]
      have h0 : (if top (p 0) = ![j, e, f, g, h] 0 then (1 : ℝ) else 0) =
          (if top (p 0) = j then (1 : ℝ) else 0) := rfl
      have h1 : (if top (p 1) = ![j, e, f, g, h] 1 then (1 : ℝ) else 0) =
          (if top (p 1) = e then (1 : ℝ) else 0) := rfl
      have h2 : (if top (p 2) = ![j, e, f, g, h] 2 then (1 : ℝ) else 0) =
          (if top (p 2) = f then (1 : ℝ) else 0) := rfl
      have h3 : (if top (p 3) = ![j, e, f, g, h] 3 then (1 : ℝ) else 0) =
          (if top (p 3) = g then (1 : ℝ) else 0) := rfl
      have h4 : (if top (p 4) = ![j, e, f, g, h] 4 then (1 : ℝ) else 0) =
          (if top (p 4) = h then (1 : ℝ) else 0) := rfl
      rw [Fin.prod_univ_five, h0, h1, h2, h3, h4]
    simp_rw [hgk, Finset.sum_mul]
    have hcomm : ∀ (F : Fin n → Perm (Fin 5) → ℝ),
        (∑ x : Fin n, ∑ p : Perm (Fin 5), F x p) = ∑ p : Perm (Fin 5), ∑ x : Fin n, F x p :=
      fun _ => Finset.sum_comm
    simp_rw [hcomm]
    refine Finset.sum_congr rfl fun p _ => ?_
    have he : ∀ e : Fin n,
        (∑ f : Fin n, ∑ g : Fin n, ∑ h : Fin n,
          ((Perm.sign p : ℤ) : ℝ) *
            ((if top (p 0) = j then (1 : ℝ) else 0) * (if top (p 1) = e then (1 : ℝ) else 0) *
             (if top (p 2) = f then (1 : ℝ) else 0) * (if top (p 3) = g then (1 : ℝ) else 0) *
             (if top (p 4) = h then (1 : ℝ) else 0)) * C.rUp e f a b * C.rUp g h c d) =
        if top (p 1) = e then
          ((Perm.sign p : ℤ) : ℝ) * (if top (p 0) = j then (1 : ℝ) else 0) *
            C.rUp e (top (p 2)) a b * C.rUp (top (p 3)) (top (p 4)) c d
        else 0 := by
      intro e
      by_cases he1 : top (p 1) = e
      · subst he1
        simp only [↓reduceIte, mul_one]
        have hf : ∀ f : Fin n,
            (∑ g : Fin n, ∑ h : Fin n,
              ((Perm.sign p : ℤ) : ℝ) *
                ((if top (p 0) = j then (1 : ℝ) else 0) * (if top (p 2) = f then (1 : ℝ) else 0) *
                 (if top (p 3) = g then (1 : ℝ) else 0) * (if top (p 4) = h then (1 : ℝ) else 0)) *
                C.rUp (top (p 1)) f a b * C.rUp g h c d) =
            if top (p 2) = f then
              ((Perm.sign p : ℤ) : ℝ) * (if top (p 0) = j then (1 : ℝ) else 0) *
                C.rUp (top (p 1)) f a b * C.rUp (top (p 3)) (top (p 4)) c d
            else 0 := by
          intro f
          by_cases hf2 : top (p 2) = f
          · subst hf2
            simp only [↓reduceIte, mul_one]
            have hg : ∀ g : Fin n,
                (∑ h : Fin n,
                  ((Perm.sign p : ℤ) : ℝ) *
                    ((if top (p 0) = j then (1 : ℝ) else 0) *
                      (if top (p 3) = g then (1 : ℝ) else 0) *
                     (if top (p 4) = h then (1 : ℝ) else 0)) *
                    C.rUp (top (p 1)) (top (p 2)) a b * C.rUp g h c d) =
                if top (p 3) = g then
                  ((Perm.sign p : ℤ) : ℝ) * (if top (p 0) = j then (1 : ℝ) else 0) *
                    C.rUp (top (p 1)) (top (p 2)) a b * C.rUp g (top (p 4)) c d
                else 0 := by
              intro g
              by_cases hg3 : top (p 3) = g
              · subst hg3
                simp only [↓reduceIte, mul_one]
                have hh : ∀ h : Fin n,
                    ((Perm.sign p : ℤ) : ℝ) *
                      ((if top (p 0) = j then (1 : ℝ) else 0) *
                        (if top (p 4) = h then (1 : ℝ) else 0)) *
                      C.rUp (top (p 1)) (top (p 2)) a b * C.rUp (top (p 3)) h c d =
                    if top (p 4) = h then
                      ((Perm.sign p : ℤ) : ℝ) * (if top (p 0) = j then (1 : ℝ) else 0) *
                        C.rUp (top (p 1)) (top (p 2)) a b * C.rUp (top (p 3)) h c d
                    else 0 := by
                  intro h; split_ifs <;> ring
                simp_rw [hh]; simp
              · simp [hg3]
            simp_rw [hg]; simp
          · simp [hf2]
        simp_rw [hf]; simp
      · simp [he1]
    simp_rw [he]; simp
  exact hinner

/-- In dimension `n < 5`, the 5-index Lovelock contraction vanishes identically. -/
lemma lovelockContract5_eq_zero_of_lt {n : ℕ} (hn : n < 5) (C : AlgCurvature n) (i j : Fin n) :
    lovelockContract5 C i j = 0 := by
  rw [← lovelockContract5_eq_kronecker_sum]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ =>
    Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun f _ =>
    Finset.sum_eq_zero fun g _ => Finset.sum_eq_zero fun h _ => ?_
  rw [genKronecker_eq_zero_of_lt hn]
  ring

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
lemma perm_fin4_split (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
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

private lemma perm_fin5_fiber_split (k : Fin 5) (F : Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℝ)
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

private lemma sum4_swap13 {n : ℕ} (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, f a b c d) =
      ∑ c : Fin n, ∑ b : Fin n, ∑ a : Fin n, ∑ d : Fin n, f a b c d := by
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext b
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

private lemma sum4_swap_pairs {n : ℕ} (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, f a b c d) =
      ∑ c : Fin n, ∑ d : Fin n, ∑ a : Fin n, ∑ b : Fin n, f a b c d := by
  conv_lhs =>
    arg 2; ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext c
    arg 2; ext a
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext c
    rw [Finset.sum_comm]

private lemma fiber_zero_sum {n : ℕ} (C : AlgCurvature n) (i j : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
      (if i = j then (1 : ℝ) else 0) * 4 *
        (C.rUp a b a b * C.rUp c d c d - C.rUp a c a b * C.rUp b d c d
          + C.rUp a d a b * C.rUp b c c d + C.rUp b c a b * C.rUp a d c d
          - C.rUp b d a b * C.rUp a c c d + C.rUp c d a b * C.rUp a b c d))
      = 4 * (if i = j then C.gaussBonnetScalar else 0) := by
  have h1 : (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp a b a b * C.rUp c d c d)
      = C.scalarCurv ^ 2 := by
    unfold AlgCurvature.scalarCurv
    rw [sq]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
  have h2 : (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp a c a b * C.rUp b d c d)
      = C.ricciSq := by
    unfold AlgCurvature.ricciSq AlgCurvature.ricciMixed
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [sum4_swap13]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
    rw [C.antisymm12 a c a b, C.antisymm34 c a a b]; ring
  have h3 : (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp a d a b * C.rUp b c c d)
      = -C.ricciSq := by
    rw [← h2]
    simp_rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [C.antisymm34 b d d c]; ring
  have h4 : (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp b c a b * C.rUp a d c d)
      = -C.ricciSq := by
    rw [← h2, Finset.sum_comm]
    simp_rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [C.antisymm34 a c b a]; ring
  have h5 : (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp b d a b * C.rUp a c c d)
      = C.ricciSq := by
    rw [← h2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [C.antisymm34 a c b a, C.antisymm34 b d d c]; ring
  simp_rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2, h3, h4, h5]
  unfold AlgCurvature.gaussBonnetScalar AlgCurvature.riemannSq
  split_ifs <;> ring

private lemma fiber_one_sum {n : ℕ} (C : AlgCurvature n) (i j : Fin n) :
    (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
      (C.rUp i b j b * C.rUp c d c d - C.rUp i c j b * C.rUp b d c d
        + C.rUp i d j b * C.rUp b c c d + C.rUp b c j b * C.rUp i d c d
        - C.rUp b d j b * C.rUp i c c d + C.rUp c d j b * C.rUp i b c d))
      = C.scalarCurv * C.ricciMixed i j
        - 2 * (∑ c : Fin n, C.ricciMixed i c * C.ricciMixed c j)
        - 2 * (∑ b : Fin n, ∑ c : Fin n, C.rUp i c j b * C.ricciMixed b c)
        + (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp c d j b * C.rUp i b c d) := by
  have h1 : (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp i b j b * C.rUp c d c d)
      = C.scalarCurv * C.ricciMixed i j := by
    unfold AlgCurvature.scalarCurv AlgCurvature.ricciMixed
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => by ring
  have h2 : (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp i c j b * C.rUp b d c d)
      = ∑ b : Fin n, ∑ c : Fin n, C.rUp i c j b * C.ricciMixed b c := by
    unfold AlgCurvature.ricciMixed
    simp_rw [Finset.mul_sum]
  have h3 : (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp i d j b * C.rUp b c c d)
      = -(∑ b : Fin n, ∑ c : Fin n, C.rUp i c j b * C.ricciMixed b c) := by
    rw [← h2]
    simp_rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [C.antisymm34 b d d c]; ring
  have h4 : (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp b c j b * C.rUp i d c d)
      = -(∑ c : Fin n, C.ricciMixed i c * C.ricciMixed c j) := by
    unfold AlgCurvature.ricciMixed
    simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => ?_
    rw [C.antisymm12 b c j b]; ring
  have h5 : (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp b d j b * C.rUp i c c d)
      = ∑ c : Fin n, C.ricciMixed i c * C.ricciMixed c j := by
    unfold AlgCurvature.ricciMixed
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2; ext c
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun b _ => ?_
    rw [C.antisymm12 b d j b, C.antisymm34 i c c d]; ring
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2, h3, h4, h5]
  ring

/-- The 5-index Lovelock Kronecker contraction equals `-8` times the Gauss–Bonnet variation tensor
`H^i_j` in every dimension `n`. -/
lemma lovelockContract5_eq_neg_eight_gaussBonnet {n : ℕ} (C : AlgCurvature n) (i j : Fin n) :
    lovelockContract5 C i j = -8 * C.gaussBonnetTensor i j := by
  unfold lovelockContract5
  have hperm : ∀ a b c d : Fin n,
      (∑ p : Perm (Fin 5), ((Perm.sign p : ℤ) : ℝ) *
        (if ![i, a, b, c, d] (p 0) = j then (1 : ℝ) else 0) *
        C.rUp (![i, a, b, c, d] (p 1)) (![i, a, b, c, d] (p 2)) a b *
        C.rUp (![i, a, b, c, d] (p 3)) (![i, a, b, c, d] (p 4)) c d) =
      ((if i = j then (1 : ℝ) else 0) * 4 *
        (C.rUp a b a b * C.rUp c d c d - C.rUp a c a b * C.rUp b d c d
          + C.rUp a d a b * C.rUp b c c d + C.rUp b c a b * C.rUp a d c d
          - C.rUp b d a b * C.rUp a c c d + C.rUp c d a b * C.rUp a b c d)) +
      ((if a = j then (1 : ℝ) else 0) * (-1 * 4 *
        (C.rUp i b a b * C.rUp c d c d - C.rUp i c a b * C.rUp b d c d
          + C.rUp i d a b * C.rUp b c c d + C.rUp b c a b * C.rUp i d c d
          - C.rUp b d a b * C.rUp i c c d + C.rUp c d a b * C.rUp i b c d))) +
      ((if b = j then (1 : ℝ) else 0) * (-1 * 4 *
        (C.rUp a i a b * C.rUp c d c d - C.rUp a c a b * C.rUp i d c d
          + C.rUp a d a b * C.rUp i c c d + C.rUp i c a b * C.rUp a d c d
          - C.rUp i d a b * C.rUp a c c d + C.rUp c d a b * C.rUp a i c d))) +
      ((if c = j then (1 : ℝ) else 0) * (-1 * 4 *
        (C.rUp a b a b * C.rUp i d c d - C.rUp a i a b * C.rUp b d c d
          + C.rUp a d a b * C.rUp b i c d + C.rUp b i a b * C.rUp a d c d
          - C.rUp b d a b * C.rUp a i c d + C.rUp i d a b * C.rUp a b c d))) +
      ((if d = j then (1 : ℝ) else 0) * (-1 * 4 *
        (C.rUp a b a b * C.rUp c i c d - C.rUp a c a b * C.rUp b i c d
          + C.rUp a i a b * C.rUp b c c d + C.rUp b c a b * C.rUp a i c d
          - C.rUp b i a b * C.rUp a c c d + C.rUp c i a b * C.rUp a b c d))) := by
    intro a b c d
    rw [← Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]
    let v : Fin 5 → Fin n := ![i, a, b, c, d]
    have hfiber : ∀ k : Fin 5,
        (∑ q : Perm (Fin 4),
          ((Perm.sign (Perm.decomposeFin.symm (k, q)) : ℤ) : ℝ) *
            (if v (Perm.decomposeFin.symm (k, q) 0) = j then (1 : ℝ) else 0) *
            C.rUp (v (Perm.decomposeFin.symm (k, q) 1)) (v (Perm.decomposeFin.symm (k, q) 2)) a b *
            C.rUp (v (Perm.decomposeFin.symm (k, q) 3)) (v (Perm.decomposeFin.symm (k, q) 4)) c d)
        = (if v k = j then (1 : ℝ) else 0) *
          ((if k = 0 then (1 : ℝ) else -1) * 4 *
            (let s := fun m : Fin 4 => v (Equiv.swap 0 k m.succ)
             C.rUp (s 0) (s 1) a b * C.rUp (s 2) (s 3) c d
               - C.rUp (s 0) (s 2) a b * C.rUp (s 1) (s 3) c d
               + C.rUp (s 0) (s 3) a b * C.rUp (s 1) (s 2) c d
               + C.rUp (s 1) (s 2) a b * C.rUp (s 0) (s 3) c d
               - C.rUp (s 1) (s 3) a b * C.rUp (s 0) (s 2) c d
               + C.rUp (s 2) (s 3) a b * C.rUp (s 0) (s 1) c d)) := by
      intro k
      have hpull :
          (∑ q : Perm (Fin 4),
            ((Perm.sign (Perm.decomposeFin.symm (k, q)) : ℤ) : ℝ) *
              (if v (Perm.decomposeFin.symm (k, q) 0) = j then (1 : ℝ) else 0) *
              C.rUp (v (Perm.decomposeFin.symm (k, q) 1))
                (v (Perm.decomposeFin.symm (k, q) 2)) a b *
              C.rUp (v (Perm.decomposeFin.symm (k, q) 3))
                (v (Perm.decomposeFin.symm (k, q) 4)) c d)
          = (if v k = j then (1 : ℝ) else 0) *
            (∑ q : Perm (Fin 4),
              ((Perm.sign (Perm.decomposeFin.symm (k, q)) : ℤ) : ℝ) *
                (C.rUp (v (Perm.decomposeFin.symm (k, q) 1))
                  (v (Perm.decomposeFin.symm (k, q) 2)) a b *
                 C.rUp (v (Perm.decomposeFin.symm (k, q) 3))
                  (v (Perm.decomposeFin.symm (k, q) 4)) c d)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Perm.decomposeFin_symm_apply_zero]
        ring
      rw [hpull]
      congr 1
      exact perm_fin5_fiber_split k
        (fun x y z w => C.rUp (v x) (v y) a b * C.rUp (v z) (v w) c d)
        (fun x y z w => by rw [C.antisymm12 (v x) (v y)]; ring)
        (fun x y z w => by rw [C.antisymm12 (v z) (v w)]; ring)
    rw [Finset.sum_congr rfl fun k _ => hfiber k, Fin.sum_univ_five]
    change
      (if i = j then (1 : ℝ) else 0) *
        ((1 : ℝ) * 4 *
          (C.rUp a b a b * C.rUp c d c d - C.rUp a c a b * C.rUp b d c d
            + C.rUp a d a b * C.rUp b c c d + C.rUp b c a b * C.rUp a d c d
            - C.rUp b d a b * C.rUp a c c d + C.rUp c d a b * C.rUp a b c d)) +
      (if a = j then (1 : ℝ) else 0) *
        ((-1 : ℝ) * 4 *
          (C.rUp i b a b * C.rUp c d c d - C.rUp i c a b * C.rUp b d c d
            + C.rUp i d a b * C.rUp b c c d + C.rUp b c a b * C.rUp i d c d
            - C.rUp b d a b * C.rUp i c c d + C.rUp c d a b * C.rUp i b c d)) +
      (if b = j then (1 : ℝ) else 0) *
        ((-1 : ℝ) * 4 *
          (C.rUp a i a b * C.rUp c d c d - C.rUp a c a b * C.rUp i d c d
            + C.rUp a d a b * C.rUp i c c d + C.rUp i c a b * C.rUp a d c d
            - C.rUp i d a b * C.rUp a c c d + C.rUp c d a b * C.rUp a i c d)) +
      (if c = j then (1 : ℝ) else 0) *
        ((-1 : ℝ) * 4 *
          (C.rUp a b a b * C.rUp i d c d - C.rUp a i a b * C.rUp b d c d
            + C.rUp a d a b * C.rUp b i c d + C.rUp b i a b * C.rUp a d c d
            - C.rUp b d a b * C.rUp a i c d + C.rUp i d a b * C.rUp a b c d)) +
      (if d = j then (1 : ℝ) else 0) *
        ((-1 : ℝ) * 4 *
          (C.rUp a b a b * C.rUp c i c d - C.rUp a c a b * C.rUp b i c d
            + C.rUp a i a b * C.rUp b c c d + C.rUp b c a b * C.rUp a i c d
            - C.rUp b i a b * C.rUp a c c d + C.rUp c i a b * C.rUp a b c d)) = _
    ring
  simp_rw [hperm]
  simp only [Finset.sum_add_distrib]
  rw [fiber_zero_sum C i j]
  have hf1 :
      (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        (if a = j then (1 : ℝ) else 0) * (-1 * 4 *
          (C.rUp i b a b * C.rUp c d c d - C.rUp i c a b * C.rUp b d c d
            + C.rUp i d a b * C.rUp b c c d + C.rUp b c a b * C.rUp i d c d
            - C.rUp b d a b * C.rUp i c c d + C.rUp c d a b * C.rUp i b c d)))
      = -4 * (C.scalarCurv * C.ricciMixed i j
        - 2 * (∑ c : Fin n, C.ricciMixed i c * C.ricciMixed c j)
        - 2 * (∑ b : Fin n, ∑ c : Fin n, C.rUp i c j b * C.ricciMixed b c)
        + (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp c d j b * C.rUp i b c d)) := by
    have ha : ∀ a : Fin n,
        (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          (if a = j then (1 : ℝ) else 0) * (-1 * 4 *
            (C.rUp i b a b * C.rUp c d c d - C.rUp i c a b * C.rUp b d c d
              + C.rUp i d a b * C.rUp b c c d + C.rUp b c a b * C.rUp i d c d
              - C.rUp b d a b * C.rUp i c c d + C.rUp c d a b * C.rUp i b c d)))
        = if a = j then -4 *
            (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
              (C.rUp i b j b * C.rUp c d c d - C.rUp i c j b * C.rUp b d c d
                + C.rUp i d j b * C.rUp b c c d + C.rUp b c j b * C.rUp i d c d
                - C.rUp b d j b * C.rUp i c c d + C.rUp c d j b * C.rUp i b c d))
          else 0 := by
      intro a
      by_cases haj : a = j
      · subst haj
        simp only [↓reduceIte, one_mul, ← Finset.mul_sum]
        ring
      · simp [haj]
    simp_rw [ha]; simp [fiber_one_sum C i j]
  have hf2 :
      (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        (if b = j then (1 : ℝ) else 0) * (-1 * 4 *
          (C.rUp a i a b * C.rUp c d c d - C.rUp a c a b * C.rUp i d c d
            + C.rUp a d a b * C.rUp i c c d + C.rUp i c a b * C.rUp a d c d
            - C.rUp i d a b * C.rUp a c c d + C.rUp c d a b * C.rUp a i c d)))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        (if a = j then (1 : ℝ) else 0) * (-1 * 4 *
          (C.rUp i b a b * C.rUp c d c d - C.rUp i c a b * C.rUp b d c d
            + C.rUp i d a b * C.rUp b c c d + C.rUp b c a b * C.rUp i d c d
            - C.rUp b d a b * C.rUp i c c d + C.rUp c d a b * C.rUp i b c d)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [C.antisymm12 b i b a, C.antisymm34 i b b a,
      C.antisymm34 b c b a, C.antisymm34 b d b a,
      C.antisymm34 i c b a, C.antisymm34 i d b a,
      C.antisymm34 c d b a, C.antisymm12 b i c d]
    ring
  have hf3 :
      (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        (if c = j then (1 : ℝ) else 0) * (-1 * 4 *
          (C.rUp a b a b * C.rUp i d c d - C.rUp a i a b * C.rUp b d c d
            + C.rUp a d a b * C.rUp b i c d + C.rUp b i a b * C.rUp a d c d
            - C.rUp b d a b * C.rUp a i c d + C.rUp i d a b * C.rUp a b c d)))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        (if a = j then (1 : ℝ) else 0) * (-1 * 4 *
          (C.rUp i b a b * C.rUp c d c d - C.rUp i c a b * C.rUp b d c d
            + C.rUp i d a b * C.rUp b c c d + C.rUp b c a b * C.rUp i d c d
            - C.rUp b d a b * C.rUp i c c d + C.rUp c d a b * C.rUp i b c d)) := by
    rw [sum4_swap_pairs]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [C.antisymm12 a i a b, C.antisymm12 b d c d,
      C.antisymm12 b d a b, C.antisymm12 a i c d,
      C.antisymm12 a d a b, C.antisymm12 b i c d,
      C.antisymm12 b i a b, C.antisymm12 a d c d]
    ring
  have hf4 :
      (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        (if d = j then (1 : ℝ) else 0) * (-1 * 4 *
          (C.rUp a b a b * C.rUp c i c d - C.rUp a c a b * C.rUp b i c d
            + C.rUp a i a b * C.rUp b c c d + C.rUp b c a b * C.rUp a i c d
            - C.rUp b i a b * C.rUp a c c d + C.rUp c i a b * C.rUp a b c d)))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        (if c = j then (1 : ℝ) else 0) * (-1 * 4 *
          (C.rUp a b a b * C.rUp i d c d - C.rUp a i a b * C.rUp b d c d
            + C.rUp a d a b * C.rUp b i c d + C.rUp b i a b * C.rUp a d c d
            - C.rUp b d a b * C.rUp a i c d + C.rUp i d a b * C.rUp a b c d)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [C.antisymm12 d i d c, C.antisymm34 i d d c,
      C.antisymm34 b i d c, C.antisymm34 a b d c,
      C.antisymm34 b d d c, C.antisymm34 a d d c,
      C.antisymm34 a i d c, C.antisymm12 d i a b]
    ring
  rw [hf4, hf3, hf2, hf1]
  unfold AlgCurvature.gaussBonnetTensor
  ring

/-- Bach–Lanczos theorem in arbitrary dimension `n < 5`: the Gauss–Bonnet variation tensor
`H^i_j` vanishes identically whenever `n < 5`. -/
lemma gaussBonnetTensor_eq_zero_of_lt_five {n : ℕ} (hn : n < 5) (C : AlgCurvature n)
    (i j : Fin n) : C.gaussBonnetTensor i j = 0 := by
  have h1 := lovelockContract5_eq_neg_eight_gaussBonnet C i j
  have h0 := lovelockContract5_eq_zero_of_lt hn C i j
  linarith

/-- Bach–Lanczos theorem in four dimensions: the Gauss–Bonnet variation tensor `H^i_j` vanishes
identically for every algebraic curvature tensor on a 4D spacetime. -/
lemma gaussBonnetTensor_four_eq_zero (C : AlgCurvature 4) (i j : Fin 4) :
    C.gaussBonnetTensor i j = 0 :=
  gaussBonnetTensor_eq_zero_of_lt_five (by decide) C i j

/-- Constant-curvature model `R^{ab}_{cd} = κ (δ^a_c δ^b_d - δ^a_d δ^b_c)` in `n` dimensions. -/
def constCurv (n : ℕ) (κ : ℝ) : AlgCurvature n where
  rUp a b c d :=
    κ * ((if a = c then 1 else 0) * (if b = d then 1 else 0)
      - (if a = d then 1 else 0) * (if b = c then 1 else 0))
  antisymm12 a b c d := by ring
  antisymm34 a b c d := by ring

/-- In `n = 4`, a space of constant sectional curvature `κ` has non-vanishing Gauss–Bonnet
topological density `𝒢 = 24 κ²`, even though its metric variation `H^i_j` vanishes identically. -/
lemma gaussBonnetScalar_constCurv_four (κ : ℝ) :
    (constCurv 4 κ).gaussBonnetScalar = 24 * κ ^ 2 := by
  unfold AlgCurvature.gaussBonnetScalar AlgCurvature.scalarCurv AlgCurvature.ricciSq
    AlgCurvature.riemannSq AlgCurvature.ricciMixed constCurv
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  ring

private lemma ricciMixed_constCurv_five (κ : ℝ) (i j : Fin 5) :
    (constCurv 5 κ).ricciMixed i j = if i = j then 4 * κ else 0 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by fin_cases i <;> decide
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by fin_cases j <;> decide
  unfold AlgCurvature.ricciMixed constCurv
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;>
    ring

private lemma scalarCurv_constCurv_five (κ : ℝ) :
    (constCurv 5 κ).scalarCurv = 20 * κ := by
  rw [← AlgCurvature.trace_ricciMixed]
  simp only [ricciMixed_constCurv_five, Fin.sum_univ_five, ↓reduceIte]
  ring

private lemma gaussBonnetScalar_constCurv_five (κ : ℝ) :
    (constCurv 5 κ).gaussBonnetScalar = 120 * κ ^ 2 := by
  unfold AlgCurvature.gaussBonnetScalar AlgCurvature.ricciSq AlgCurvature.riemannSq
  rw [scalarCurv_constCurv_five]
  simp only [ricciMixed_constCurv_five]
  unfold constCurv
  simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  ring

/-- In `n = 5`, the Gauss–Bonnet variation tensor `H^i_j` is dynamically non-trivial: on a 5D
constant-curvature space it evaluates to `H^i_i = -12 κ²`. -/
lemma gaussBonnetTensor_constCurv_five (κ : ℝ) (i : Fin 5) :
    (constCurv 5 κ).gaussBonnetTensor i i = -12 * κ ^ 2 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by fin_cases i <;> decide
  unfold AlgCurvature.gaussBonnetTensor
  rw [gaussBonnetScalar_constCurv_five, scalarCurv_constCurv_five]
  simp only [ricciMixed_constCurv_five]
  unfold constCurv
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;>
    ring

end Lovelock

end Modified

end GeneralRelativity
