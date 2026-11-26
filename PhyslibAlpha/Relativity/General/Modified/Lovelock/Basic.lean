/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Modified.Lovelock.GeneralizedKronecker
public import PhyslibAlpha.Relativity.Tensors.Tensor2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Lovelock and Gauss–Bonnet higher-curvature gravity

Algebraic `(2,2)` curvature tensors, the Gauss–Bonnet scalar and Lanczos–Bach–Lovelock variation
tensor, the five-index Lovelock contraction identity, and identical vanishing in four dimensions.

## i. Overview

At quadratic order in curvature, the Gauss–Bonnet density `𝒢 = R² - 4 R^a_b R^b_a + R^{cd}_{ab}
R^{ab}_{cd}` yields the Lanczos variation tensor `H^i_j`. Expressing `H^i_j` via the 5-index
generalized Kronecker contraction `L^i_j = -8 H^i_j` proves that `H^i_j = 0` in `n ≤ 4`
dimensions while contrasting with non-zero 5D dynamics on constant-curvature spaces.

## ii. Key results

- `AlgCurvature`, `AlgCurvature.gaussBonnetScalar`, `AlgCurvature.lanczosTensor` : algebraic
  `(2,2)` curvature structure, quadratic Gauss–Bonnet invariant, and Lanczos tensor `H^i_j`.
- `lovelockContract5`, `lovelockContract5_eq_zero_of_lt`,
  `lovelockContract5_eq_neg_eight_lanczos` : 5-index contraction and `L^i_j = -8 H^i_j`.
- `bach_lanczos_lt_five`, `bach_lanczos_four` : 4D Bach–Lanczos
  vanishing theorem.
- `constantCurvature`, `gaussBonnetScalar_constantCurvature_four`,
  `lanczosTensor_constantCurvature_five` : 4D topological invariant vs non-zero 5D variation.

## iii. Table of contents

- A. Algebraic curvature tensors and Gauss–Bonnet invariants
- B. Five-index Lovelock contraction and four-dimensional vanishing

## iv. References

* Cornelius Lanczos, *A Remarkable Property of the Riemann-Christoffel Tensor in Four Dimensions*,
  *Annals of Mathematics* 39, pp. 842-850 (1938). [ref: Lanczos1938]
* David Lovelock, *The Einstein Tensor and Its Generalizations*, *Journal of Mathematical Physics*
  12, pp. 498-501 (1971), Sec. 2-3. [ref: Lovelock1971]
* David Lovelock, *The Four-Dimensionality of Space and the Einstein Tensor*, *Journal of
  Mathematical Physics* 13, pp. 874-876 (1972). [ref: Lovelock1972]
* T. Padmanabhan and D. Kothawala, *Lanczos-Lovelock Models of Gravity*, *Physics Reports* (2013),
  Sec. 2-3 (https://arxiv.org/pdf/1302.2151#page=4). [ref: PadmanabhanKothawala2013]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace Lovelock

open Equiv

/-!

## A. Algebraic curvature tensors and Gauss–Bonnet invariants

The quadratic Gauss–Bonnet scalar density `𝒢` and its variation tensor `H^i_j` (Lanczos tensor)
depend solely on the algebraic pair antisymmetries of mixed curvature components `R^{ab}_{cd}`.

-/

/-- Abstract algebraic `(2,2)` mixed Riemann curvature tensor `R^{ab}_{cd}` in `n` dimensions,
carrying antisymmetry in `(a, b)` and `(c, d)`. Kept separate from `RiemannTensor` because the
Bach–Lanczos dimension-dependent vanishing theorem depends only on algebraic pair antisymmetry and
the mixed index structure `R^{ab}_{cd}` rather than metric lowering or the Bianchi identity. -/
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
def AlgCurvature.ricciScalar {n : ℕ} (C : AlgCurvature n) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n, C.rUp a b a b

/-- Trace of the mixed Ricci tensor equals the scalar curvature: `∑_i R^i_i = R`. -/
lemma AlgCurvature.trace_ricciMixed {n : ℕ} (C : AlgCurvature n) :
    (∑ i : Fin n, C.ricciMixed i i) = C.ricciScalar := by
  rfl

/-- Quadratic Ricci invariant `R^a_b R^b_a`. -/
def AlgCurvature.ricciSq {n : ℕ} (C : AlgCurvature n) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n, C.ricciMixed a b * C.ricciMixed b a

/-- Quadratic Riemann (Kretschmann) invariant `R^{cd}_{ab} R^{ab}_{cd}`. -/
def AlgCurvature.riemannSq {n : ℕ} (C : AlgCurvature n) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp c d a b * C.rUp a b c d

/-- Quadratic Gauss–Bonnet scalar density `𝒢 = R² - 4 R^a_b R^b_a + R^{cd}_{ab} R^{ab}_{cd}`. -/
def AlgCurvature.gaussBonnetScalar {n : ℕ} (C : AlgCurvature n) : ℝ :=
  C.ricciScalar ^ 2 - 4 * C.ricciSq + C.riemannSq

/-- Mixed `(1,1)` Lanczos–Bach–Gauss–Bonnet variation tensor
`H^i_j = -½ δ^i_j 𝒢 + 2 R R^i_j - 4 R^i_c R^c_j - 4 R^{ic}_{jb} R^b_c + 2 R^{cd}_{jb} R^{ib}_{cd}`.
-/
noncomputable def AlgCurvature.lanczosTensor {n : ℕ} (C : AlgCurvature n) (i j : Fin n) : ℝ :=
  -(1 / 2) * (if i = j then C.gaussBonnetScalar else 0)
    + 2 * C.ricciScalar * C.ricciMixed i j
    - 4 * (∑ c : Fin n, C.ricciMixed i c * C.ricciMixed c j)
    - 4 * (∑ b : Fin n, ∑ c : Fin n, C.rUp i c j b * C.ricciMixed b c)
    + 2 * (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp c d j b * C.rUp i b c d)

/-!

## B. Five-index Lovelock contraction and four-dimensional vanishing

By decomposing `lovelockContract5` into its `S_4` cosets via `perm_fin5_fiber_split` and
contrasting `n ≤ 4` with `n = 5`, we isolate the Bach–Lanczos identity `-8 H^i_j = L^i_j = 0` in
four spacetime dimensions.

-/

/-- Five-index Lovelock Kronecker contraction
`L^i_j = ∑_{a,b,c,d} ∑_{p ∈ S_5} sgn(p) δ^{v_{p(0)}}_j R^{v_{p(1)} v_{p(2)}}_{a b}
R^{v_{p(3)} v_{p(4)}}_{c d}` with `v = (i, a, b, c, d)`, isolating the algebraic antisymmetrized
contraction so dimension-dependent Bach–Lanczos vanishing reduces to `S_5` coset combinatorics. -/
noncomputable def lovelockContract5 {n : ℕ} (C : AlgCurvature n) (i j : Fin n) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
    ∑ p : Perm (Fin 5), ((Perm.sign p : ℤ) : ℝ) *
      (if ![i, a, b, c, d] (p 0) = j then (1 : ℝ) else 0) *
      C.rUp (![i, a, b, c, d] (p 1)) (![i, a, b, c, d] (p 2)) a b *
      C.rUp (![i, a, b, c, d] (p 3)) (![i, a, b, c, d] (p 4)) c d

private lemma sum4_ite_eq_mul {n : ℕ} (a₁ a₂ a₃ a₄ : Fin n)
    (g : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ e : Fin n, ∑ f : Fin n, ∑ k : Fin n, ∑ h : Fin n,
      ((if a₁ = e then (1 : ℝ) else 0) * (if a₂ = f then (1 : ℝ) else 0) *
       (if a₃ = k then (1 : ℝ) else 0) * (if a₄ = h then (1 : ℝ) else 0)) * g e f k h) =
      g a₁ a₂ a₃ a₄ := by
  simp [Finset.sum_ite_eq]

/-- Equivalence of `lovelockContract5` with the full 8-index generalized Kronecker sum over
`a, b, c, d, e, f, g, h`. -/
lemma lovelockContract5_eq_kronecker_sum {n : ℕ} (C : AlgCurvature n) (i j : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
      ∑ e : Fin n, ∑ f : Fin n, ∑ g : Fin n, ∑ h : Fin n,
        genKronecker 5 ![i, a, b, c, d] ![j, e, f, g, h] * C.rUp e f a b * C.rUp g h c d)
      = lovelockContract5 C i j := by
  simp only [lovelockContract5]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  have hgk : ∀ e f g h : Fin n,
      genKronecker 5 ![i, a, b, c, d] ![j, e, f, g, h] =
        ∑ p : Perm (Fin 5), ((Perm.sign p : ℤ) : ℝ) *
          (if ![i, a, b, c, d] (p 0) = j then (1 : ℝ) else 0) *
          ((if ![i, a, b, c, d] (p 1) = e then (1 : ℝ) else 0) *
           (if ![i, a, b, c, d] (p 2) = f then (1 : ℝ) else 0) *
           (if ![i, a, b, c, d] (p 3) = g then (1 : ℝ) else 0) *
           (if ![i, a, b, c, d] (p 4) = h then (1 : ℝ) else 0)) :=
    genKronecker_five_eq_sum_perm i j a b c d
  simp_rw [hgk, Finset.sum_mul]
  have hcomm : ∀ (F : Fin n → Perm (Fin 5) → ℝ),
      (∑ x : Fin n, ∑ p : Perm (Fin 5), F x p) = ∑ p : Perm (Fin 5), ∑ x : Fin n, F x p :=
    fun _ => Finset.sum_comm
  simp_rw [hcomm]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hfact : ∀ e f g h : Fin n,
      (((Perm.sign p : ℤ) : ℝ) * (if ![i, a, b, c, d] (p 0) = j then (1 : ℝ) else 0) *
        ((if ![i, a, b, c, d] (p 1) = e then (1 : ℝ) else 0) *
         (if ![i, a, b, c, d] (p 2) = f then (1 : ℝ) else 0) *
         (if ![i, a, b, c, d] (p 3) = g then (1 : ℝ) else 0) *
         (if ![i, a, b, c, d] (p 4) = h then (1 : ℝ) else 0))) *
        C.rUp e f a b * C.rUp g h c d =
      ((if ![i, a, b, c, d] (p 1) = e then (1 : ℝ) else 0) *
       (if ![i, a, b, c, d] (p 2) = f then (1 : ℝ) else 0) *
       (if ![i, a, b, c, d] (p 3) = g then (1 : ℝ) else 0) *
       (if ![i, a, b, c, d] (p 4) = h then (1 : ℝ) else 0)) *
        (((Perm.sign p : ℤ) : ℝ) * (if ![i, a, b, c, d] (p 0) = j then (1 : ℝ) else 0) *
          C.rUp e f a b * C.rUp g h c d) := by
    intro e f g h; ring
  simp_rw [hfact]
  exact sum4_ite_eq_mul (![i, a, b, c, d] (p 1)) (![i, a, b, c, d] (p 2))
    (![i, a, b, c, d] (p 3)) (![i, a, b, c, d] (p 4))
    (fun e f g h => ((Perm.sign p : ℤ) : ℝ) *
      (if ![i, a, b, c, d] (p 0) = j then (1 : ℝ) else 0) *
      C.rUp e f a b * C.rUp g h c d)

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

private lemma fiber_zero_sum_1 {n : ℕ} (C : AlgCurvature n) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp a b a b * C.rUp c d c d) =
      C.ricciScalar ^ 2 := by
  simp only [AlgCurvature.ricciScalar, sq]
  simp_rw [Finset.sum_mul, Finset.mul_sum]

private lemma fiber_zero_sum_2 {n : ℕ} (C : AlgCurvature n) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp a c a b * C.rUp b d c d) =
      C.ricciSq := by
  simp only [AlgCurvature.ricciSq, AlgCurvature.ricciMixed]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [sum4_swap13]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
  rw [C.antisymm12 a c a b, C.antisymm34 c a a b]; ring

private lemma fiber_zero_sum_3 {n : ℕ} (C : AlgCurvature n) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp a d a b * C.rUp b c c d) =
      -C.ricciSq := by
  rw [← fiber_zero_sum_2 C]
  simp_rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [C.antisymm34 b d d c]; ring

private lemma fiber_zero_sum_4 {n : ℕ} (C : AlgCurvature n) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp b c a b * C.rUp a d c d) =
      -C.ricciSq := by
  rw [← fiber_zero_sum_2 C, Finset.sum_comm]
  simp_rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [C.antisymm34 a c b a]; ring

private lemma fiber_zero_sum_5 {n : ℕ} (C : AlgCurvature n) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp b d a b * C.rUp a c c d) =
      C.ricciSq := by
  rw [← fiber_zero_sum_2 C, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [C.antisymm34 a c b a, C.antisymm34 b d d c]; ring

private lemma fiber_zero_sum {n : ℕ} (C : AlgCurvature n) (i j : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
      (if i = j then (1 : ℝ) else 0) * 4 *
        (C.rUp a b a b * C.rUp c d c d - C.rUp a c a b * C.rUp b d c d
          + C.rUp a d a b * C.rUp b c c d + C.rUp b c a b * C.rUp a d c d
          - C.rUp b d a b * C.rUp a c c d + C.rUp c d a b * C.rUp a b c d))
      = 4 * (if i = j then C.gaussBonnetScalar else 0) := by
  simp_rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, fiber_zero_sum_1, fiber_zero_sum_2,
    fiber_zero_sum_3, fiber_zero_sum_4, fiber_zero_sum_5,
    AlgCurvature.gaussBonnetScalar, AlgCurvature.riemannSq]
  split_ifs <;> ring

private lemma fiber_one_sum_1 {n : ℕ} (C : AlgCurvature n) (i j : Fin n) :
    (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp i b j b * C.rUp c d c d) =
      C.ricciScalar * C.ricciMixed i j := by
  simp only [AlgCurvature.ricciScalar, AlgCurvature.ricciMixed]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => by ring

private lemma fiber_one_sum_2 {n : ℕ} (C : AlgCurvature n) (i j : Fin n) :
    (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp i c j b * C.rUp b d c d) =
      ∑ b : Fin n, ∑ c : Fin n, C.rUp i c j b * C.ricciMixed b c := by
  simp only [AlgCurvature.ricciMixed]
  simp_rw [Finset.mul_sum]

private lemma fiber_one_sum_3 {n : ℕ} (C : AlgCurvature n) (i j : Fin n) :
    (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp i d j b * C.rUp b c c d) =
      -(∑ b : Fin n, ∑ c : Fin n, C.rUp i c j b * C.ricciMixed b c) := by
  rw [← fiber_one_sum_2 C i j]
  simp_rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [C.antisymm34 b d d c]; ring

private lemma fiber_one_sum_4 {n : ℕ} (C : AlgCurvature n) (i j : Fin n) :
    (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp b c j b * C.rUp i d c d) =
      -(∑ c : Fin n, C.ricciMixed i c * C.ricciMixed c j) := by
  simp only [AlgCurvature.ricciMixed]
  simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => ?_
  rw [C.antisymm12 b c j b]; ring

private lemma fiber_one_sum_5 {n : ℕ} (C : AlgCurvature n) (i j : Fin n) :
    (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp b d j b * C.rUp i c c d) =
      ∑ c : Fin n, C.ricciMixed i c * C.ricciMixed c j := by
  simp only [AlgCurvature.ricciMixed]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext c
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun b _ => ?_
  rw [C.antisymm12 b d j b, C.antisymm34 i c c d]; ring

private lemma fiber_one_sum {n : ℕ} (C : AlgCurvature n) (i j : Fin n) :
    (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
      (C.rUp i b j b * C.rUp c d c d - C.rUp i c j b * C.rUp b d c d
        + C.rUp i d j b * C.rUp b c c d + C.rUp b c j b * C.rUp i d c d
        - C.rUp b d j b * C.rUp i c c d + C.rUp c d j b * C.rUp i b c d))
      = C.ricciScalar * C.ricciMixed i j
        - 2 * (∑ c : Fin n, C.ricciMixed i c * C.ricciMixed c j)
        - 2 * (∑ b : Fin n, ∑ c : Fin n, C.rUp i c j b * C.ricciMixed b c)
        + (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp c d j b * C.rUp i b c d) := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, fiber_one_sum_1, fiber_one_sum_2,
    fiber_one_sum_3, fiber_one_sum_4, fiber_one_sum_5]
  ring

private lemma perm5_fiber_split_v {n : ℕ} (C : AlgCurvature n) (j a b c d : Fin n)
    (v : Fin 5 → Fin n) (k : Fin 5) :
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

private lemma lovelock_perm_sum {n : ℕ} (C : AlgCurvature n) (i j a b c d : Fin n) :
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
  rw [← Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl fun k _ => perm5_fiber_split_v C j a b c d ![i, a, b, c, d] k]
  have hv0 : (![i, a, b, c, d] : Fin 5 → Fin n) 0 = i := rfl
  have hv1 : (![i, a, b, c, d] : Fin 5 → Fin n) 1 = a := rfl
  have hv2 : (![i, a, b, c, d] : Fin 5 → Fin n) 2 = b := rfl
  have hv3 : (![i, a, b, c, d] : Fin 5 → Fin n) 3 = c := rfl
  have hv4 : (![i, a, b, c, d] : Fin 5 → Fin n) 4 = d := rfl
  simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, ↓reduceIte,
    Equiv.swap_apply_def, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show (2 : Fin 4).succ = 3 from rfl, show (3 : Fin 4).succ = 4 from rfl,
    hv0, hv1, hv2, hv3, hv4]
  ring

private lemma fiber_sum_a_j {n : ℕ} (C : AlgCurvature n) (i j : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
      (if a = j then (1 : ℝ) else 0) * (-1 * 4 *
        (C.rUp i b a b * C.rUp c d c d - C.rUp i c a b * C.rUp b d c d
          + C.rUp i d a b * C.rUp b c c d + C.rUp b c a b * C.rUp i d c d
          - C.rUp b d a b * C.rUp i c c d + C.rUp c d a b * C.rUp i b c d)))
    = -4 * (C.ricciScalar * C.ricciMixed i j
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

private lemma fiber_sum_b_j {n : ℕ} (C : AlgCurvature n) (i j : Fin n) :
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

private lemma fiber_sum_c_j {n : ℕ} (C : AlgCurvature n) (i j : Fin n) :
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

private lemma fiber_sum_d_j {n : ℕ} (C : AlgCurvature n) (i j : Fin n) :
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

/-- The 5-index Lovelock Kronecker contraction equals `-8` times the Gauss–Bonnet variation tensor
`H^i_j` in every dimension `n`. -/
lemma lovelockContract5_eq_neg_eight_lanczos {n : ℕ} (C : AlgCurvature n) (i j : Fin n) :
    lovelockContract5 C i j = -8 * C.lanczosTensor i j := by
  simp only [lovelockContract5]
  simp_rw [lovelock_perm_sum C i j]
  simp only [Finset.sum_add_distrib]
  rw [fiber_zero_sum C i j, fiber_sum_d_j, fiber_sum_c_j, fiber_sum_b_j, fiber_sum_a_j]
  simp only [AlgCurvature.lanczosTensor]
  ring

/-- Bach–Lanczos theorem in arbitrary dimension `n < 5`: the Gauss–Bonnet variation tensor
`H^i_j` vanishes identically whenever `n < 5`. -/
lemma bach_lanczos_lt_five {n : ℕ} (hn : n < 5) (C : AlgCurvature n)
    (i j : Fin n) : C.lanczosTensor i j = 0 := by
  have h1 := lovelockContract5_eq_neg_eight_lanczos C i j
  have h0 := lovelockContract5_eq_zero_of_lt hn C i j
  linarith

/-- Bach–Lanczos theorem in four dimensions: the Gauss–Bonnet variation tensor `H^i_j` vanishes
identically for every algebraic curvature tensor on a 4D spacetime. -/
lemma bach_lanczos_four (C : AlgCurvature 4) (i j : Fin 4) :
    C.lanczosTensor i j = 0 :=
  bach_lanczos_lt_five (by decide) C i j

/-- Constant-curvature model `R^{ab}_{cd} = κ (δ^a_c δ^b_d - δ^a_d δ^b_c)` in `n` dimensions. -/
def constantCurvature (n : ℕ) (κ : ℝ) : AlgCurvature n where
  rUp a b c d :=
    κ * ((if a = c then 1 else 0) * (if b = d then 1 else 0)
      - (if a = d then 1 else 0) * (if b = c then 1 else 0))
  antisymm12 a b c d := by ring
  antisymm34 a b c d := by ring

/-- In `n = 4`, a space of constant sectional curvature `κ` has non-vanishing Gauss–Bonnet
topological density `𝒢 = 24 κ²`, even though its metric variation `H^i_j` vanishes identically. -/
lemma gaussBonnetScalar_constantCurvature_four (κ : ℝ) :
    (constantCurvature 4 κ).gaussBonnetScalar = 24 * κ ^ 2 := by
  simp only [AlgCurvature.gaussBonnetScalar, AlgCurvature.ricciScalar, AlgCurvature.ricciSq,
    AlgCurvature.riemannSq, AlgCurvature.ricciMixed, constantCurvature,
    Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  ring

private lemma ricciMixed_constantCurvature_five (κ : ℝ) (i j : Fin 5) :
    (constantCurvature 5 κ).ricciMixed i j = if i = j then 4 * κ else 0 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by fin_cases i <;> decide
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by fin_cases j <;> decide
  simp only [AlgCurvature.ricciMixed, constantCurvature]
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;>
    ring

private lemma ricciScalar_constantCurvature_five (κ : ℝ) :
    (constantCurvature 5 κ).ricciScalar = 20 * κ := by
  rw [← AlgCurvature.trace_ricciMixed]
  simp only [ricciMixed_constantCurvature_five, Fin.sum_univ_five, ↓reduceIte]
  ring

private lemma gaussBonnetScalar_constantCurvature_five (κ : ℝ) :
    (constantCurvature 5 κ).gaussBonnetScalar = 120 * κ ^ 2 := by
  simp only [AlgCurvature.gaussBonnetScalar, AlgCurvature.ricciSq, AlgCurvature.riemannSq]
  rw [ricciScalar_constantCurvature_five]
  simp only [ricciMixed_constantCurvature_five]
  simp only [constantCurvature, Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  ring

/-- In `n = 5`, the Gauss–Bonnet variation tensor `H^i_j` is dynamically non-trivial: on a 5D
constant-curvature space it evaluates to `H^i_i = -12 κ²`. -/
lemma lanczosTensor_constantCurvature_five (κ : ℝ) (i : Fin 5) :
    (constantCurvature 5 κ).lanczosTensor i i = -12 * κ ^ 2 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by fin_cases i <;> decide
  simp only [AlgCurvature.lanczosTensor]
  rw [gaussBonnetScalar_constantCurvature_five, ricciScalar_constantCurvature_five]
  simp only [ricciMixed_constantCurvature_five]
  simp only [constantCurvature]
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, ↓reduceIte] <;>
    ring

end Lovelock

end Modified

end GeneralRelativity
