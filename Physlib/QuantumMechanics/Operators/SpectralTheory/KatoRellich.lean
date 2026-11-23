/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Physlib.QuantumMechanics.Operators.SpectralTheory.SelfAdjoint
public import Physlib.QuantumMechanics.Operators.SpectralTheory.Symmetric
public import Mathlib.Analysis.Complex.Convex
/-!

# The Kato–Rellich theorem

## i. Overview

A symmetric perturbation `B` of an essentially self-adjoint operator `A` keeps essential
self-adjointness when it is small relative to `A`: if `D(A) ⊆ D(B)` and
`‖B x‖ ≤ a ‖A x‖ + b ‖x‖` with `a < 1`, then `A + B` is essentially self-adjoint on `D(A)`.
This is the standard tool for showing that Schrödinger operators `-Δ + V` are essentially
self-adjoint.

The proof works with defect numbers. For `μ > 0` large enough the relative bound becomes
`‖B x‖ ≤ c ‖(A - μ i) x‖` with `c < 1`. Since the range of `A - μ i` is dense, a vector orthogonal
to the range of `A + B - μ i` satisfies `‖y‖² ≤ c ‖y‖²` and vanishes. The defect numbers of
`A + B` at `±μ i` are therefore zero, and by constancy on the half-planes also at `±i`.

## ii. Key results

- `LinearPMap.IsSymmetric.norm_sub_smul_I_sq` : `‖(A - μ i) x‖² = ‖A x‖² + μ² ‖x‖²` for symmetric
  `A`.
- `LinearPMap.IsEssentiallySelfAdjoint.range_sub_orthogonal_eq_bot` : for an essentially
  self-adjoint operator the range of `A - z` is dense for non-real `z`.
- `LinearPMap.IsEssentiallySelfAdjoint.add_of_relBound` : the Kato–Rellich theorem.

## iii. Table of contents

- A. Estimates for symmetric operators
- B. Dense ranges and defect numbers
- C. The Kato–Rellich theorem

## iv. References

- M. Reed, B. Simon, *Methods of Modern Mathematical Physics II*, Theorem X.12.
- K. Schmüdgen, *Unbounded Self-Adjoint Operators on Hilbert Space*, Theorem 8.5.

-/

@[expose] public section

namespace LinearPMap

open Complex
open scoped InnerProductSpace

/-!
## A. Estimates for symmetric operators
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {A B : H →ₗ.[ℂ] H}

/-- For a symmetric operator and real `μ`, `‖(A - μ i) x‖² = ‖A x‖² + μ² ‖x‖²`. -/
lemma IsSymmetric.norm_sub_smul_I_sq (hA : A.IsSymmetric) (μ : ℝ) (x : A.domain) :
    ‖A x - ((μ : ℂ) * I) • (x : H)‖ ^ 2 = ‖A x‖ ^ 2 + μ ^ 2 * ‖(x : H)‖ ^ 2 := by
  have h : (⟪A x, (x : H)⟫_ℂ).im = 0 := by
    refine conj_eq_iff_im.mp ?_
    rw [inner_conj_symm]
    exact (hA x x).symm
  have hre : RCLike.re ⟪A x, ((μ : ℂ) * I) • (x : H)⟫_ℂ = 0 := by
    rw [inner_smul_right]
    simp [h]
  rw [@norm_sub_sq ℂ, norm_smul, hre, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, mul_one, mul_pow, sq_abs]
  ring

variable [CompleteSpace H]

/-!
## B. Dense ranges and defect numbers
-/

/-- If `A` is essentially self-adjoint, symmetric and densely defined, then for non-real `z` the
orthogonal complement of the range of `A - z` is trivial. -/
lemma IsEssentiallySelfAdjoint.range_sub_orthogonal_eq_bot (hA : A.IsEssentiallySelfAdjoint)
    (hsym : A.IsSymmetric) (hdense : A.HasDenseDomain) {z : ℂ} (hz : z.im ≠ 0) :
    (A - z • 1).toFun.rangeᗮ = ⊥ := by
  have hreg := hsym.mem_regularityDomain_of_im_ne_zero hz
  have hcl : A.closure.IsClosed := (hsym.isClosable hdense).closure_isClosed
  have h1 : A.closure.defectNumber z = 0 := by
    have hregc : z ∈ A.closure.regularityDomain := by
      rwa [regularityDomain_closure]
    exact (hcl.defectNumber_eq_zero_iff hregc).mpr
      (LinearMap.range_eq_top.mpr (IsSelfAdjoint.sub_smul_surjective hA hz))
  rw [defectNumber_closure hreg, defectNumber_eq] at h1
  have := Submodule.rank_eq_zero.mp h1
  simpa using this

/-- Key step of the Kato–Rellich theorem: a relative bound `‖B x‖ ≤ c ‖(A - μ i) x‖` with
`c < 1` forces the defect number of `A + B` at `μ i` to vanish. -/
lemma IsEssentiallySelfAdjoint.defectNumber_add_eq_zero (hA : A.IsEssentiallySelfAdjoint)
    (hAsym : A.IsSymmetric) (hAdense : A.HasDenseDomain) (hdom : A.domain ≤ B.domain)
    {μ : ℝ} (hμ : μ ≠ 0) {c : ℝ} (hc : c < 1)
    (hbound : ∀ (x : H) (hx : x ∈ A.domain),
      ‖B ⟨x, hdom hx⟩‖ ≤ c * ‖A ⟨x, hx⟩ - ((μ : ℂ) * I) • x‖) :
    (A + B).defectNumber ((μ : ℂ) * I) = 0 := by
  set z : ℂ := (μ : ℂ) * I with hz_def
  have hz : z.im ≠ 0 := by simpa [hz_def] using hμ
  rw [defectNumber_eq]
  refine Submodule.rank_eq_zero.mpr ?_
  rw [deficiencySubspace_coe, eq_bot_iff]
  intro y hy
  rw [Submodule.mem_bot]
  -- `y` is orthogonal to `(A + B - z) x`, so `⟪(A - z) x, y⟫ = -⟪B x, y⟫`.
  have hperp : ∀ (x : H) (hx : x ∈ A.domain),
      ⟪A ⟨x, hx⟩ - z • x, y⟫_ℂ = -⟪B ⟨x, hdom hx⟩, y⟫_ℂ := by
    intro x hx
    have hmem : (A + B - z • 1).toFun ⟨x, ⟨⟨hx, hdom hx⟩, trivial⟩⟩ ∈
        (A + B - z • 1).toFun.range := LinearMap.mem_range_self _ _
    have h0 := (Submodule.mem_orthogonal _ _).mp hy _ hmem
    have h0' : ⟪A ⟨x, hx⟩ + B ⟨x, hdom hx⟩ - z • x, y⟫_ℂ = 0 := h0
    rw [inner_sub_left, inner_add_left] at h0'
    rw [inner_sub_left]
    linear_combination h0'
  -- The range of `A - z` is dense.
  have hK := hA.range_sub_orthogonal_eq_bot hAsym hAdense hz
  have hKdense : Dense ((A - z • 1).toFun.range : Set H) := by
    refine Submodule.dense_iff_topologicalClosure_eq_top.mpr ?_
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hK, Submodule.bot_orthogonal_eq_top]
  -- The estimate `‖⟪u, y⟫‖ ≤ c ‖u‖ ‖y‖` holds on the range and hence everywhere.
  have hS : ((A - z • 1).toFun.range : Set H) ⊆ {u | ‖⟪u, y⟫_ℂ‖ ≤ c * ‖u‖ * ‖y‖} := by
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have hxA : x ∈ A.domain := hx.1
    have hu : (A - z • 1).toFun ⟨x, hx⟩ = A ⟨x, hxA⟩ - z • x := rfl
    change ‖⟪(A - z • 1).toFun ⟨x, hx⟩, y⟫_ℂ‖ ≤ c * ‖(A - z • 1).toFun ⟨x, hx⟩‖ * ‖y‖
    rw [hu]
    rw [hperp x hxA, norm_neg]
    calc ‖⟪B ⟨x, hdom hxA⟩, y⟫_ℂ‖ ≤ ‖B ⟨x, hdom hxA⟩‖ * ‖y‖ := norm_inner_le_norm _ _
      _ ≤ c * ‖A ⟨x, hxA⟩ - z • x‖ * ‖y‖ :=
        mul_le_mul_of_nonneg_right (hbound x hxA) (norm_nonneg y)
  have hclosed : _root_.IsClosed {u : H | ‖⟪u, y⟫_ℂ‖ ≤ c * ‖u‖ * ‖y‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hy' : y ∈ {u : H | ‖⟪u, y⟫_ℂ‖ ≤ c * ‖u‖ * ‖y‖} := by
    have := closure_minimal hS hclosed
    rw [hKdense.closure_eq] at this
    exact this (Set.mem_univ y)
  have h1 : ‖y‖ ^ 2 ≤ c * ‖y‖ * ‖y‖ := by
    rw [← @inner_self_eq_norm_sq ℂ]
    exact (Complex.re_le_norm _).trans hy'
  have h2 : ‖y‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖y‖]
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg y])

/-!
## C. The Kato–Rellich theorem
-/

/-- **Kato–Rellich theorem** (essentially self-adjoint version). Let `A` be essentially
self-adjoint and `B` symmetric with `D(A) ⊆ D(B)` and `‖B x‖ ≤ a ‖A x‖ + b ‖x‖` for some `a < 1`.
Then `A + B` is essentially self-adjoint on `D(A)`. -/
lemma IsEssentiallySelfAdjoint.add_of_relBound (hA : A.IsEssentiallySelfAdjoint)
    (hAsym : A.IsSymmetric) (hAdense : A.HasDenseDomain) (hB : B.IsSymmetric)
    (hdom : A.domain ≤ B.domain) {a b : ℝ} (ha : a < 1)
    (hbound : ∀ (x : H) (hx : x ∈ A.domain),
      ‖B ⟨x, hdom hx⟩‖ ≤ a * ‖A ⟨x, hx⟩‖ + b * ‖x‖) :
    (A + B).IsEssentiallySelfAdjoint := by
  set a' := max a 0 with ha'_def
  set b' := max b 0 with hb'_def
  have ha' : a' < 1 := max_lt ha one_pos
  have ha'0 : 0 ≤ a' := le_max_right _ _
  have hb'0 : 0 ≤ b' := le_max_right _ _
  set μ : ℝ := b' / (1 - a') + 1 with hμ_def
  have hμ : 0 < μ := by have : 0 ≤ b' / (1 - a') := div_nonneg hb'0 (by linarith); linarith
  set c : ℝ := a' + b' / μ with hc_def
  have hc : c < 1 := by
    have h1a : 0 < 1 - a' := by linarith
    have h2 : b' < μ * (1 - a') := (div_lt_iff₀ h1a).mp (by linarith)
    have h3 : b' / μ < 1 - a' := by rw [div_lt_iff₀ hμ]; linarith
    linarith
  -- the relative bound with respect to `A ∓ μ i`
  have hrel : ∀ (s : ℝ), |s| = μ → ∀ (x : H) (hx : x ∈ A.domain),
      ‖B ⟨x, hdom hx⟩‖ ≤ c * ‖A ⟨x, hx⟩ - ((s : ℂ) * I) • x‖ := by
    intro s hs x hx
    set N := ‖A ⟨x, hx⟩ - ((s : ℂ) * I) • x‖ with hN_def
    have hN := hAsym.norm_sub_smul_I_sq s ⟨x, hx⟩
    have hs2 : s ^ 2 = μ ^ 2 := by rw [← sq_abs, hs]
    have hN0 : 0 ≤ N := norm_nonneg _
    have hAx : ‖A ⟨x, hx⟩‖ ≤ N := by
      nlinarith [norm_nonneg (A ⟨x, hx⟩), sq_nonneg (s * ‖x‖)]
    have hxN : μ * ‖x‖ ≤ N := by
      nlinarith [norm_nonneg x, sq_nonneg ‖A ⟨x, hx⟩‖, hμ]
    have hB1 : ‖B ⟨x, hdom hx⟩‖ ≤ a' * ‖A ⟨x, hx⟩‖ + b' * ‖x‖ :=
      (hbound x hx).trans (add_le_add
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
    have hbx : b' * ‖x‖ ≤ b' / μ * N := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
      nlinarith [norm_nonneg x]
    calc ‖B ⟨x, hdom hx⟩‖ ≤ a' * ‖A ⟨x, hx⟩‖ + b' * ‖x‖ := hB1
      _ ≤ a' * N + b' / μ * N := add_le_add (mul_le_mul_of_nonneg_left hAx ha'0) hbx
      _ = c * N := by rw [hc_def]; ring
  have hsum := hAsym.add hB
  have hdense' : (A + B).HasDenseDomain := by
    rw [LinearPMap.HasDenseDomain, add_domain, inf_eq_left.mpr hdom]
    exact hAdense
  have hdp := hA.defectNumber_add_eq_zero hAsym hAdense hdom hμ.ne' hc (hrel μ (abs_of_pos hμ))
  have hdm := hA.defectNumber_add_eq_zero hAsym hAdense hdom (neg_ne_zero.mpr hμ.ne') hc
    (hrel (-μ) (by rw [abs_neg, abs_of_pos hμ]))
  have hcl := hsum.isClosable hdense'
  refine hsum.isEssentiallySelfAdjoint_of_defectNumber_eq_zero hdense' ?_ ?_
  · have hsub := (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected.subset_connectedComponentIn
      (x := (μ : ℂ) * I) (by simpa using hμ)
      (fun z hz => hsum.mem_regularityDomain_of_im_ne_zero (ne_of_gt hz))
    rw [← hcl.defectNumber_const (hsub (show (0 : ℝ) < I.im by simp))]
    exact hdp
  · have hsub := (convex_halfSpace_im_lt (0 : ℝ)).isPreconnected.subset_connectedComponentIn
      (x := ((-μ : ℝ) : ℂ) * I) (by simpa using hμ)
      (fun z hz => hsum.mem_regularityDomain_of_im_ne_zero (ne_of_lt hz))
    rw [← hcl.defectNumber_const (hsub (show (-I).im < (0 : ℝ) by simp))]
    exact hdm

end LinearPMap
