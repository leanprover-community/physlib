/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Matrix.Order

/-!
# A determinant bound for positive semidefinite matrices

If `S - i W` and `S + i W` are positive semidefinite for real matrices `S` and `W`, then
`|det W| ≤ det S`.

## i. Overview

For a positive definite `A` its inverse square root `T` satisfies `T A Tᴴ = 1`. If `A - B` and
`A + B` are positive semidefinite for a hermitian `B`, the eigenvalues of `T B Tᴴ` lie between `-1`
and `1`. So `‖det B‖ ≤ det A`. If `A` is only positive semidefinite, adding `ε` makes it positive
definite and the bound follows as `ε → 0`.

## ii. Key results

- `Matrix.PosDef.norm_det_le_re_det` : `‖det B‖ ≤ det A` when `A` is positive definite and `A ± B`
  are positive semidefinite.
- `Matrix.abs_det_le_det_of_posSemidef` : `|det W| ≤ det S` when `S ± i W` are positive
  semidefinite.

## iii. Table of contents

- A. The inverse square root of a positive definite matrix
- B. The determinant bound

## iv. References

* None.

-/

@[expose] public section

namespace Matrix

open scoped ComplexOrder MatrixOrder
open Unitary Filter Topology

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## A. The inverse square root of a positive definite matrix -/

/-- The inverse square root `T` of a positive definite `A` satisfies `T A Tᴴ = 1`. -/
lemma PosDef.inv_sqrt_mul_mul_conjTranspose {A : Matrix n n ℂ} (hA : A.PosDef) :
    (CFC.sqrt A)⁻¹ * A * ((CFC.sqrt A)⁻¹)ᴴ = 1 := by
  have hs : (CFC.sqrt A)ᴴ = CFC.sqrt A := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hu : IsUnit (CFC.sqrt A).det := by
    rw [hA.posSemidef.det_sqrt, isUnit_iff_ne_zero, RCLike.sqrt_of_nonneg hA.det_pos.le]
    exact RCLike.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (RCLike.pos_iff.mp hA.det_pos).1).ne'
  rw [conjTranspose_nonsing_inv, hs]
  nth_rw 2 [← CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
  rw [← mul_assoc, nonsing_inv_mul _ hu, one_mul, mul_nonsing_inv _ hu]

/-! ## B. The determinant bound -/

/-- The eigenvalues of a hermitian `K` with `1 − K` and `1 + K` positive semidefinite lie in
`[−1, 1]`. -/
lemma IsHermitian.abs_eigenvalues_le_one {K : Matrix n n ℂ} (hK : K.IsHermitian)
    (hm : (1 - K).PosSemidef) (hp : (1 + K).PosSemidef) (i : n) : |hK.eigenvalues i| ≤ 1 := by
  set v := hK.eigenvectorBasis i
  have hv : star (v : n → ℂ) ⬝ᵥ (v : n → ℂ) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
      hK.eigenvectorBasis.orthonormal.1 i]
    simp
  have h0 := hm.re_dotProduct_nonneg (v : n → ℂ)
  have h1 := hp.re_dotProduct_nonneg (v : n → ℂ)
  rw [sub_mulVec, one_mulVec, dotProduct_sub, hK.mulVec_eigenvectorBasis, dotProduct_smul,
    hv] at h0
  rw [add_mulVec, one_mulVec, dotProduct_add, hK.mulVec_eigenvectorBasis, dotProduct_smul,
    hv] at h1
  simp at h0 h1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- If `A` is positive definite, `B` hermitian and `A − B`, `A + B` positive semidefinite, then
`‖det B‖ ≤ re (det A)`: conjugating by the inverse square root of `A` puts `B` between `−1` and
`1`. -/
lemma PosDef.norm_det_le_re_det {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.IsHermitian)
    (h₁ : (A - B).PosSemidef) (h₂ : (A + B).PosSemidef) : ‖B.det‖ ≤ (A.det).re := by
  set T := (CFC.sqrt A)⁻¹
  have hT := hA.inv_sqrt_mul_mul_conjTranspose
  set K := T * B * Tᴴ
  have hK : K.IsHermitian := by
    simp only [IsHermitian, K, conjTranspose_mul, conjTranspose_conjTranspose, hB.eq, mul_assoc]
  have hm : (1 - K).PosSemidef := by
    have := h₁.mul_mul_conjTranspose_same T
    rwa [mul_sub, sub_mul, hT] at this
  have hp : (1 + K).PosSemidef := by
    have := h₂.mul_mul_conjTranspose_same T
    rwa [mul_add, add_mul, hT] at this
  have hdetK : ‖K.det‖ ≤ 1 := by
    rw [hK.det_eq_prod_eigenvalues, norm_prod]
    refine Finset.prod_le_one₀ (by simp) ?_
    intro i _
    rw [RCLike.norm_ofReal]
    exact hK.abs_eigenvalues_le_one hm hp i
  have hdetA : A.det = ((∏ i, hA.1.eigenvalues i : ℝ) : ℂ) := by
    rw [hA.1.det_eq_prod_eigenvalues]
    push_cast
    rfl
  have hprod : 0 < ∏ i, hA.1.eigenvalues i := Finset.prod_pos (by simp [hA.eigenvalues_pos])
  have hBK : B.det = K.det * A.det := by
    have h := congrArg det hT
    rw [det_mul, det_mul, det_one] at h
    simp only [K, det_mul]
    linear_combination (-B.det) * h
  rw [hBK, norm_mul, hdetA, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hprod]
  nlinarith [norm_nonneg K.det]

/-- If `A - B` and `A + B` are positive semidefinite for a hermitian `B`, then
`‖det B‖ ≤ re (det A)`. Adding `ε` makes `A` positive definite and the bound follows as `ε → 0`. -/
lemma PosSemidef.norm_det_le_re_det {A B : Matrix n n ℂ} (hB : B.IsHermitian)
    (h₁ : (A - B).PosSemidef) (h₂ : (A + B).PosSemidef) : ‖B.det‖ ≤ (A.det).re := by
  have hA : A.PosSemidef := by
    simpa [← two_smul ℂ A, smul_smul] using
      (h₁.add h₂).smul (Complex.zero_le_real.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have key (ε : ℝ) (hε : 0 < ε) : ‖B.det‖ ≤ ((A + (ε : ℂ) • 1).det).re := by
    have hε1 := (PosSemidef.one (n := n) (R := ℂ)).smul (Complex.zero_le_real.mpr hε.le)
    refine (PosDef.posSemidef_add hA
      ((PosDef.one (n := n) (R := ℂ)).smul (Complex.zero_lt_real.mpr hε))).norm_det_le_re_det hB
      ?_ ?_
    · rw [add_sub_right_comm]; exact h₁.add hε1
    · rw [add_right_comm]; exact h₂.add hε1
  have hc : Continuous fun ε : ℝ ↦ ((A + (ε : ℂ) • 1).det).re := by fun_prop
  have hlim := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  rw [Complex.ofReal_zero, zero_smul, add_zero] at hlim
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall key)

/-- For real `S` and `W`, if `S - i W` and `S + i W` are positive semidefinite then
`|det W| ≤ det S`. -/
lemma abs_det_le_det_of_posSemidef {S W : Matrix n n ℝ}
    (h₁ : (S.map Complex.ofReal - Complex.I • W.map Complex.ofReal).PosSemidef)
    (h₂ : (S.map Complex.ofReal + Complex.I • W.map Complex.ofReal).PosSemidef) :
    |W.det| ≤ S.det := by
  have hS : (S.map Complex.ofReal).PosSemidef := by
    simpa [← two_smul ℂ (S.map Complex.ofReal), smul_smul] using
      (h₁.add h₂).smul (Complex.zero_le_real.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hB := h₂.1.sub hS.1
  rw [add_sub_cancel_left] at hB
  have h := PosSemidef.norm_det_le_re_det hB h₁ h₂
  rwa [det_smul, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
    show (W.map Complex.ofReal).det = W.det from (RingHom.map_det Complex.ofRealHom W).symm,
    show (S.map Complex.ofReal).det = S.det from (RingHom.map_det Complex.ofRealHom S).symm,
    Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re] at h

end Matrix
