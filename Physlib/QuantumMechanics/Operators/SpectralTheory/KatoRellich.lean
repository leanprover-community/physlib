/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Physlib.QuantumMechanics.Operators.SpectralTheory.EssentiallySelfAdjoint

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

- `LinearPMap.IsEssentiallySelfAdjoint.defectNumber_add_eq_zero` : a relative bound
  `‖B x‖ ≤ c ‖(A - z) x‖` with `c < 1` forces the defect number of `A + B` at a non-real `z` to
  vanish.
- `LinearPMap.IsEssentiallySelfAdjoint.add_of_relBound` : the Kato–Rellich theorem.

## iii. Table of contents

- A. Defect numbers of relatively bounded perturbations
- B. The Kato–Rellich theorem

## iv. References

- M. Reed, B. Simon, *Methods of Modern Mathematical Physics II*, Theorem X.12.
- K. Schmüdgen, *Unbounded Self-Adjoint Operators on Hilbert Space*, Theorem 8.5.

-/

@[expose] public section

namespace LinearPMap

open Complex
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A B : H →ₗ.[ℂ] H}

/-!

## A. Defect numbers of relatively bounded perturbations

-/

/-- Key step of the Kato–Rellich theorem: a relative bound `‖B x‖ ≤ c ‖(A - z) x‖` with
`c < 1` forces the defect number of `A + B` at a non-real `z` to vanish. -/
lemma IsEssentiallySelfAdjoint.defectNumber_add_eq_zero (hA : A.IsEssentiallySelfAdjoint)
    (hdom : A.domain ≤ B.domain) {z : ℂ} (hz : z.im ≠ 0) {c : ℝ} (hc : c < 1)
    (hbound : ∀ (x : H) (hx : x ∈ A.domain), ‖B ⟨x, hdom hx⟩‖ ≤ c * ‖A ⟨x, hx⟩ - z • x‖) :
    (A + B).defectNumber z = 0 := by
  rw [defectNumber_eq]
  refine Submodule.rank_eq_zero.mpr ?_
  rw [deficiencySubspace_coe, eq_bot_iff]
  intro y hy
  -- On the dense range of `A - z` we have `‖⟪u, y⟫‖ ≤ c ‖u‖ ‖y‖`, hence also for `u = y`.
  have hy' : ‖⟪y, y⟫_ℂ‖ ≤ c * ‖y‖ * ‖y‖ := by
    refine (hA.dense_range_sub_smul hz).induction (P := fun u => ‖⟪u, y⟫_ℂ‖ ≤ c * ‖u‖ * ‖y‖)
      ?_ (isClosed_le (by fun_prop) (by fun_prop)) y
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have h0 : ⟪A ⟨x, hx.1⟩ + B ⟨x, hdom hx.1⟩ - z • x, y⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal _ _).mp hy _
        (LinearMap.mem_range_self (A + B - z • 1).toFun ⟨x, ⟨⟨hx.1, hdom hx.1⟩, trivial⟩⟩)
    have h1 : ⟪A ⟨x, hx.1⟩ - z • x, y⟫_ℂ = -⟪B ⟨x, hdom hx.1⟩, y⟫_ℂ := by
      rw [inner_sub_left, inner_add_left] at h0
      rw [inner_sub_left]
      linear_combination h0
    change ‖⟪A ⟨x, hx.1⟩ - z • x, y⟫_ℂ‖ ≤ c * ‖A ⟨x, hx.1⟩ - z • x‖ * ‖y‖
    rw [h1, norm_neg]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hbound x hx.1) (norm_nonneg y))
  have h2 : ‖y‖ ^ 2 ≤ c * ‖y‖ * ‖y‖ := by
    rw [← @inner_self_eq_norm_sq ℂ]
    exact (Complex.re_le_norm _).trans hy'
  have h3 : ‖y‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖y‖]
  rw [Submodule.mem_bot]
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg y])

/-!

## B. The Kato–Rellich theorem

-/

/-- **Kato–Rellich theorem** (essentially self-adjoint version). Let `A` be essentially
self-adjoint and `B` symmetric with `D(A) ⊆ D(B)` and `‖B x‖ ≤ a ‖A x‖ + b ‖x‖` for some `a < 1`.
Then `A + B` is essentially self-adjoint on `D(A)`. -/
lemma IsEssentiallySelfAdjoint.add_of_relBound (hA : A.IsEssentiallySelfAdjoint)
    (hB : B.IsSymmetric) (hdom : A.domain ≤ B.domain) {a b : ℝ} (ha : a < 1)
    (hbound : ∀ (x : H) (hx : x ∈ A.domain),
      ‖B ⟨x, hdom hx⟩‖ ≤ a * ‖A ⟨x, hx⟩‖ + b * ‖x‖) :
    (A + B).IsEssentiallySelfAdjoint := by
  -- Without loss of generality `0 ≤ a` and `0 ≤ b`.
  obtain ⟨a', b', ha'0, hb'0, ha', hbound'⟩ : ∃ a' b' : ℝ, 0 ≤ a' ∧ 0 ≤ b' ∧ a' < 1 ∧
      ∀ (x : H) (hx : x ∈ A.domain), ‖B ⟨x, hdom hx⟩‖ ≤ a' * ‖A ⟨x, hx⟩‖ + b' * ‖x‖ :=
    ⟨max a 0, max b 0, le_max_right _ _, le_max_right _ _, max_lt ha one_pos,
      fun x hx => (hbound x hx).trans (by gcongr <;> exact le_max_left _ _)⟩
  set μ : ℝ := b' / (1 - a') + 1 with hμ_def
  have hμ : 0 < μ := by linarith [div_nonneg hb'0 (sub_nonneg.mpr ha'.le)]
  set c : ℝ := a' + b' / μ with hc_def
  have hc : c < 1 := by
    have h : b' < μ * (1 - a') := (div_lt_iff₀ (sub_pos.mpr ha')).mp (by linarith)
    have h' : b' / μ < 1 - a' := by rw [div_lt_iff₀ hμ]; linarith
    linarith
  -- The relative bound with respect to `A - s i` for `s = ± μ`.
  have hrel (s : ℝ) (hs : s ^ 2 = μ ^ 2) (x : H) (hx : x ∈ A.domain) :
      ‖B ⟨x, hdom hx⟩‖ ≤ c * ‖A ⟨x, hx⟩ - ((s : ℂ) * I) • x‖ := by
    set N := ‖A ⟨x, hx⟩ - ((s : ℂ) * I) • x‖
    have hN := hA.isSymmetric.norm_sub_smul_I_sq s ⟨x, hx⟩
    have hAN : ‖A ⟨x, hx⟩‖ ≤ N := by
      nlinarith [norm_nonneg (A ⟨x, hx⟩), norm_nonneg (A ⟨x, hx⟩ - ((s : ℂ) * I) • x),
        sq_nonneg (s * ‖x‖)]
    have hxN : μ * ‖x‖ ≤ N := by
      nlinarith [norm_nonneg x, norm_nonneg (A ⟨x, hx⟩ - ((s : ℂ) * I) • x),
        sq_nonneg ‖A ⟨x, hx⟩‖]
    calc ‖B ⟨x, hdom hx⟩‖ ≤ a' * ‖A ⟨x, hx⟩‖ + b' / μ * (μ * ‖x‖) := by
          rw [← mul_assoc, div_mul_cancel₀ _ hμ.ne']
          exact hbound' x hx
      _ ≤ a' * N + b' / μ * N :=
          add_le_add (mul_le_mul_of_nonneg_left hAN ha'0)
            (mul_le_mul_of_nonneg_left hxN (div_nonneg hb'0 hμ.le))
      _ = c * N := by rw [hc_def]; ring
  have hsum := hA.isSymmetric.add hB
  have hdense : (A + B).HasDenseDomain := by
    rw [HasDenseDomain, add_domain, inf_eq_left.mpr hdom]
    exact hA.hasDenseDomain
  refine hsum.isEssentiallySelfAdjoint_of_defectNumber_eq_zero hdense ?_ ?_
  · rw [hsum.defectNumber_eq_of_im_pos hdense (z₂ := (μ : ℂ) * I) (by simp) (by simpa using hμ)]
    exact hA.defectNumber_add_eq_zero hdom (by simpa using hμ.ne') hc (hrel μ rfl)
  · rw [hsum.defectNumber_eq_of_im_neg hdense (z₂ := ((-μ : ℝ) : ℂ) * I) (by simp)
      (by simpa using hμ)]
    exact hA.defectNumber_add_eq_zero hdom (by simpa using hμ.ne') hc (hrel (-μ) (by ring))

end LinearPMap
