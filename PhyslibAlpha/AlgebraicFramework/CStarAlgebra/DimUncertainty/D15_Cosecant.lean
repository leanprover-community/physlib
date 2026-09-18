/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Algebra.Polynomial.Splits

/-!
# Classical cosecant identity via Chebyshev

Self-contained classical analysis identity:
\[
\sum_{k=1}^{N-1}\csc^2(k\pi/N)=(N^2-1)/3.
\]
Proof via the Chebyshev polynomial of the second kind `U_{N-1}`: its
roots are `cos(kπ/N)`, and the logarithmic derivative evaluated at `±1`
(decomposing `1/(1-x²) = ½(1/(1-x) + 1/(1+x))`) gives the closed sum.

Does not depend on any object defined in another file of this package:
it is a classical analysis result, self-contained over `Mathlib`.
-/

@[expose] public section

noncomputable section

set_option maxHeartbeats 1000000

open Polynomial Polynomial.Chebyshev Real
open scoped BigOperators

namespace IdentidadCosecanteChebyshev

/-! ## Chebyshev: `U_n` factors into real linears -/

theorem U_splits_real (n : ℕ) : (U ℝ n).Splits := by
  rw [splits_iff_card_roots]
  cases n with
  | zero =>
    simp [U_zero]
  | succ m =>
    set N := m + 1 with hN
    have hdeg : (U ℝ N).natDegree = N := natDegree_U_natCast (R := ℝ) N
    rw [roots_U_real N]
    have hinj :
        Set.InjOn (fun k : ℕ ↦ cos ((k + 1) * π / (N + 1))) (Finset.range N) :=
      (Finset.range N).nodup_map_iff_injOn.mp (roots_U_real_nodup N)
    have hcard :
        ((Finset.range N).image fun k : ℕ ↦
            cos ((k + 1) * π / (N + 1))).card = N := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    show (Multiset.card _) = _
    rw [hdeg]
    exact hcard

/-! ## Derivatives of `U_n` at `±1` -/

theorem U_deriv_eval_one (n : ℕ) :
    (derivative (U ℝ (n : ℤ))).eval (1 : ℝ) =
      ((n : ℝ) + 2) * ((n : ℝ) + 1) * (n : ℝ) / 3 := by
  have h := derivative_U_eval_one (R := ℝ) (n : ℤ)
  -- `3 * U'(1) = (n+2)(n+1)n` with integer coercions
  push_cast at h
  linarith

theorem U_deriv_eval_neg_one (n : ℕ) :
    (derivative (U ℝ (n : ℤ))).eval (-1 : ℝ) =
      -((-1 : ℝ) ^ n) *
        (((n : ℝ) + 2) * ((n : ℝ) + 1) * (n : ℝ) / 3) := by
  -- Parity: U_n(-x) = (-1)^n U_n(x)
  have hfun :
      (fun x : ℝ ↦ (U ℝ (n : ℤ)).eval (-x)) =
        fun x ↦ (-1 : ℝ) ^ n * (U ℝ (n : ℤ)).eval x := by
    funext x
    rw [U_eval_neg (R := ℝ) n x, Int.cast_negOnePow_natCast]
  have hL : HasDerivAt (fun x : ℝ ↦ (U ℝ (n : ℤ)).eval (-x))
      (-(derivative (U ℝ (n : ℤ))).eval (-1)) 1 := by
    have h := (U ℝ (n : ℤ)).hasDerivAt (-1 : ℝ)
    have hc := h.comp (1 : ℝ) (hasDerivAt_id' (𝕜 := ℝ) 1).neg
    rw [mul_neg_one] at hc
    exact hc
  have hR : HasDerivAt
      (fun x : ℝ ↦ (-1 : ℝ) ^ n * (U ℝ (n : ℤ)).eval x)
      ((-1 : ℝ) ^ n * (derivative (U ℝ (n : ℤ))).eval 1) 1 :=
    ((U ℝ (n : ℤ)).hasDerivAt (1 : ℝ)).const_mul _
  have heq : HasDerivAt (fun x : ℝ ↦ (U ℝ (n : ℤ)).eval (-x))
      ((-1 : ℝ) ^ n * (derivative (U ℝ (n : ℤ))).eval 1) 1 :=
    hfun ▸ hR
  have hder := HasDerivAt.unique hL heq
  -- -U'(-1) = (-1)^n U'(1)
  have hUd1 := U_deriv_eval_one n
  rw [hUd1] at hder
  linarith

/-! ## Sums over roots -/


theorem sum_one_div_one_sub_roots (n : ℕ) (hn : 1 ≤ n) :
    ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 - z)).sum =
      (((n : ℝ) + 1) ^ 2 - 1) / 3 := by
  have hsplit : (U ℝ (n : ℤ)).Splits := U_splits_real n
  have hne : (U ℝ (n : ℤ)).eval (1 : ℝ) ≠ 0 := by
    rw [U_eval_one]; positivity
  have hlog := hsplit.eval_derivative_div_eval_of_ne_zero hne
  have hU1 : (U ℝ (n : ℤ)).eval (1 : ℝ) = (n : ℝ) + 1 := by
    simp
  have hUd := U_deriv_eval_one n
  have hratio :
      (derivative (U ℝ (n : ℤ))).eval (1 : ℝ) / (U ℝ (n : ℤ)).eval (1 : ℝ) =
        (((n : ℝ) + 1) ^ 2 - 1) / 3 := by
    rw [hUd, hU1]
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [this]; ring
  rw [← hratio, hlog]

theorem sum_one_div_one_add_roots (n : ℕ) (hn : 1 ≤ n) :
    ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 + z)).sum =
      (((n : ℝ) + 1) ^ 2 - 1) / 3 := by
  have hsplit : (U ℝ (n : ℤ)).Splits := U_splits_real n
  have hU : (U ℝ (n : ℤ)).eval (-1 : ℝ) = (-1 : ℝ) ^ n * ((n : ℝ) + 1) := by
    rw [U_eval_neg_one (R := ℝ) (n : ℤ), Int.cast_negOnePow_natCast]
    push_cast; ring
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hpow : (-1 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hne : (U ℝ (n : ℤ)).eval (-1 : ℝ) ≠ 0 := by
    rw [hU]; exact mul_ne_zero hpow hn1
  have hlog := hsplit.eval_derivative_div_eval_of_ne_zero hne
  -- U'(-1)/U(-1) = ∑ 1/(-1-z) = -∑ 1/(1+z)
  have hUd := U_deriv_eval_neg_one n
  have hratio :
      (derivative (U ℝ (n : ℤ))).eval (-1 : ℝ) / (U ℝ (n : ℤ)).eval (-1 : ℝ) =
        -((((n : ℝ) + 1) ^ 2 - 1) / 3) := by
    rw [hUd, hU]
    field_simp [hpow, hn1]; ring
  have hmap :
      ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (-1 - z)).sum =
        -((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 + z)).sum := by
    have hpt :
        ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (-1 - z)) =
          (U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ -((1 : ℝ) / (1 + z)) := by
      refine Multiset.map_congr rfl fun z _ => ?_
      have : (-1 - z : ℝ) = -(1 + z) := by ring
      rw [this, div_neg]
    rw [hpt, Multiset.sum_map_neg]
  have : -((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 + z)).sum =
      -((((n : ℝ) + 1) ^ 2 - 1) / 3) := by
    rwa [← hmap, ← hlog]
  linarith

theorem root_abs_lt_one {n : ℕ} {z : ℝ}
    (hz : z ∈ (U ℝ (n : ℤ)).roots) (hn : 1 ≤ n) : |z| < 1 := by
  have hroots := roots_U_real n
  rw [hroots, Finset.mem_val, Finset.mem_image] at hz
  obtain ⟨k, hk, rfl⟩ := hz
  have hklt : k < n := Finset.mem_range.mp hk
  have hθpos : 0 < (k + 1 : ℝ) * π / (n + 1) := by positivity
  have hθlt : (k + 1 : ℝ) * π / (n + 1) < π := by
    have : (k + 1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt hklt
    calc
      (k + 1 : ℝ) * π / (n + 1) ≤ n * π / (n + 1) := by gcongr
      _ < π := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [pi_pos]
  have hsin : 0 < sin ((k + 1 : ℝ) * π / (n + 1)) :=
    sin_pos_of_pos_of_lt_pi hθpos hθlt
  have hpyth := sin_sq_add_cos_sq ((k + 1 : ℝ) * π / (n + 1))
  have hsq : cos ((k + 1 : ℝ) * π / (n + 1)) ^ 2 < 1 := by
    nlinarith [mul_pos hsin hsin]
  exact (sq_lt_one_iff_abs_lt_one _).mp hsq

theorem sum_one_div_one_sub_sq_roots (n : ℕ) (hn : 1 ≤ n) :
    ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 - z ^ 2)).sum =
      (((n : ℝ) + 1) ^ 2 - 1) / 3 := by
  have h1 := sum_one_div_one_sub_roots n hn
  have h2 := sum_one_div_one_add_roots n hn
  have hpoint (z : ℝ) (hz : z ∈ (U ℝ (n : ℤ)).roots) :
      (1 : ℝ) / (1 - z ^ 2) =
        (1 / 2 : ℝ) * ((1 : ℝ) / (1 - z) + (1 : ℝ) / (1 + z)) := by
    have habs := root_abs_lt_one hz hn
    have hz1 : z ≠ 1 := by
      intro h; rw [h, abs_one] at habs; linarith
    have hzm1 : z ≠ -1 := by
      intro h; rw [h, abs_neg, abs_one] at habs; linarith
    have hden : (1 - z ^ 2 : ℝ) ≠ 0 := by
      intro h
      have : z ^ 2 = 1 := by linarith
      have : |z| = 1 := (sq_eq_one_iff.mp this).elim (by intro; simp [*]) (by intro; simp [*])
      -- |z|=1 contradice |z|<1
      linarith [habs]
    have hz1' : (1 - z : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
    have hzm : (1 + z : ℝ) ≠ 0 := by
      intro h; exact hzm1 (by linarith)
    field_simp [hz1', hzm, hden]
    ring
  -- lift the pointwise identity to the sum over the multiset
  have hdecomp :
      ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 - z ^ 2)).sum =
        (1 / 2 : ℝ) *
          (((U ℝ (n : ℤ)).roots.map fun z ↦ (1 : ℝ) / (1 - z)).sum +
            ((U ℝ (n : ℤ)).roots.map fun z ↦ (1 : ℝ) / (1 + z)).sum) := by
    classical
    calc
      ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 - z ^ 2)).sum
          = ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦
              (1 / 2 : ℝ) * ((1 : ℝ) / (1 - z) + (1 : ℝ) / (1 + z))).sum := by
            refine congr_arg Multiset.sum (Multiset.map_congr rfl fun z hz => hpoint z hz)
      _ = (1 / 2 : ℝ) *
            ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦
              ((1 : ℝ) / (1 - z) + (1 : ℝ) / (1 + z))).sum := by
            simp [Multiset.sum_map_mul_left]
      _ = (1 / 2 : ℝ) *
            (((U ℝ (n : ℤ)).roots.map fun z ↦ (1 : ℝ) / (1 - z)).sum +
              ((U ℝ (n : ℤ)).roots.map fun z ↦ (1 : ℝ) / (1 + z)).sum) := by
            simp [Multiset.sum_map_add]
  rw [hdecomp, h1, h2]
  ring

/-- **Classical cosecant identity.** `∑_{k=1}^{N-1} csc²(kπ/N) = (N²-1)/3`. -/
theorem sum_csc_sq (N : ℕ) (hN : 2 ≤ N) :
    ∑ k ∈ Finset.Ico 1 N, (sin ((k : ℝ) * π / N))⁻¹ ^ 2 =
      ((N : ℝ) ^ 2 - 1) / 3 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hsum := sum_one_div_one_sub_sq_roots n hn
  classical
  have hinj :
      Set.InjOn (fun k : ℕ ↦ cos ((k + 1) * π / (n + 1))) (Finset.range n) :=
    (Finset.range n).nodup_map_iff_injOn.mp (roots_U_real_nodup n)
  -- sum over roots as multiset → sum over `range n`
  have hfin :
      ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 - z ^ 2)).sum =
        ∑ k ∈ Finset.range n,
          (1 : ℝ) / (1 - cos ((k + 1 : ℝ) * π / (n + 1)) ^ 2) := by
    rw [roots_U_real n, Finset.image_val_of_injOn hinj, Multiset.map_map]
    rfl
  -- 1 - cos² = sin²
  have hsin :
      ∑ k ∈ Finset.range n,
          (1 : ℝ) / (1 - cos ((k + 1 : ℝ) * π / (n + 1)) ^ 2) =
        ∑ k ∈ Finset.range n, (sin ((k + 1 : ℝ) * π / (n + 1)))⁻¹ ^ 2 := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have h1 : (1 : ℝ) - cos ((k + 1 : ℝ) * π / (n + 1)) ^ 2 =
        sin ((k + 1 : ℝ) * π / (n + 1)) ^ 2 := by
      linarith [sin_sq_add_cos_sq ((k + 1 : ℝ) * π / (n + 1))]
    rw [h1, one_div, inv_pow]
  -- reindex `Ico 1 (n+1)` as image of `range n` under `·+1`
  have himg :
      Finset.Ico 1 (n + 1) = (Finset.range n).image (fun k ↦ k + 1) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨k - 1, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [himg, Finset.sum_image (fun x _ y _ h => by simpa using h)]
  push_cast
  rw [← hsin, ← hfin]
  exact hsum

end IdentidadCosecanteChebyshev
