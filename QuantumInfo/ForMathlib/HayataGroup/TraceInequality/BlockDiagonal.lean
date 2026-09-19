/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kento Mori, Hayata Yamasaki
-/
module

public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.LownerHeinzTheorem

/-!
# `2 × 2` block operators on a Hilbert sum

This file develops the operator-matrix ("block operator") calculus on the two-fold Hilbert
sum `ℋ ⊕ ℋ`, the main tool in the block-operator proof of the Jensen operator inequality.

## Main definitions

* `HSum ℋ`: the `ℓ²` direct sum `ℋ ⊕ ℋ` of two copies of a Hilbert space `ℋ`, realised as
  `PiLp 2 (fun _ : Fin 2 => ℋ)`.
* `hsumProj`, `hsumIncl`: the coordinate projections `HSum ℋ →L[ℂ] ℋ` and inclusions
  `ℋ →L[ℂ] HSum ℋ` exhibiting `HSum ℋ` as a direct sum; they are mutually adjoint.
* `blockDiagonal A B`: the block-diagonal operator `diag(A, B)` on `HSum ℋ`.
* `blockOp A00 A01 A10 A11`: a general `2 × 2` block operator on `HSum ℋ`.
* `blockDiagonalHom`: the `⋆`-algebra homomorphism `(A, B) ↦ diag(A, B)`.

Here `L ℋ = ℋ →L[ℂ] ℋ` is the algebra of bounded operators (quantum observables) on `ℋ`;
representing a pair of observables as a block-diagonal operator on `ℋ ⊕ ℋ` is the dilation
trick underlying the operator inequalities used throughout quantum information theory.
-/

@[expose] public section

namespace JensenOperatorInequality

universe u

open LownerHeinzTheorem

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

/-- A two-fold Hilbert sum used for the block-operator proof of Jensen's inequality.
The inner-product instance on `ℋ` is unused by the underlying type synonym but kept to
document that `HSum ℋ` is the `ℓ²` direct sum of two copies of a Hilbert space. -/
@[nolint unusedArguments]
abbrev HSum (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] : Type u :=
  PiLp 2 (fun _ : Fin 2 => ℋ)

/-- The continuous linear equivalence between the Hilbert sum `HSum ℋ` and the plain
function space `Fin 2 → ℋ`, forgetting the `ℓ²` inner-product structure on the index. -/
noncomputable def hsumEquiv (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] :
    HSum ℋ ≃L[ℂ] (Fin 2 → ℋ) :=
  PiLp.continuousLinearEquiv (p := (2 : ENNReal)) (𝕜 := ℂ) (β := fun _ : Fin 2 => ℋ)

/-- The `i`-th coordinate projection `HSum ℋ →L[ℂ] ℋ` of the Hilbert sum onto its
`i`-th summand. -/
noncomputable def hsumProj (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (i : Fin 2) : HSum ℋ →L[ℂ] ℋ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℋ) i) ∘L
    (hsumEquiv ℋ).toContinuousLinearMap

/-- The `i`-th coordinate inclusion `ℋ →L[ℂ] HSum ℋ`, embedding `ℋ` as the `i`-th summand
of the Hilbert sum and placing `0` in the other summand. -/
noncomputable def hsumIncl (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (i : Fin 2) : ℋ →L[ℂ] HSum ℋ :=
  (hsumEquiv ℋ).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.single ℂ (fun _ : Fin 2 => ℋ) i)

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem hsumProj_hsumIncl_apply (i j : Fin 2) (x : ℋ) :
    hsumProj ℋ i (hsumIncl ℋ j x) = if i = j then x else 0 := by
  fin_cases i <;> fin_cases j <;> simp [hsumProj, hsumIncl, hsumEquiv]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem inner_hsumIncl_hsumIncl (i j : Fin 2) (x y : ℋ) :
    inner ℂ (hsumIncl ℋ i x) (hsumIncl ℋ j y) = if i = j then inner ℂ x y else 0 := by
  fin_cases i <;> fin_cases j <;> simp [hsumIncl, hsumEquiv, PiLp.inner_apply]

omit [Nontrivial ℋ] in
@[simp] theorem hsumIncl_adjoint (i : Fin 2) :
    (hsumIncl ℋ i).adjoint = hsumProj ℋ i := by
  fin_cases i
  · ext x
    refine ext_inner_right ℂ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp [hsumProj, hsumIncl, hsumEquiv, PiLp.inner_apply]
  · ext x
    refine ext_inner_right ℂ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp [hsumProj, hsumIncl, hsumEquiv, PiLp.inner_apply]

omit [Nontrivial ℋ] in
@[simp] theorem hsumProj_adjoint (i : Fin 2) :
    (hsumProj ℋ i).adjoint = hsumIncl ℋ i := by
  calc
    (hsumProj ℋ i).adjoint = ((hsumIncl ℋ i).adjoint).adjoint := by
      rw [hsumIncl_adjoint (ℋ := ℋ) i]
    _ = hsumIncl ℋ i := ContinuousLinearMap.adjoint_adjoint _

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem hsumIncl_proj_sum (z : HSum ℋ) :
    hsumIncl ℋ 0 (hsumProj ℋ 0 z) + hsumIncl ℋ 1 (hsumProj ℋ 1 z) = z := by
  ext i
  fin_cases i <;> simp [hsumProj, hsumIncl, hsumEquiv]

/-- The block diagonal operator `diag(A, B)` on the two-fold Hilbert sum. -/
noncomputable def blockDiagonal (A B : L ℋ) : L (HSum ℋ) :=
  hsumIncl ℋ 0 ∘L A ∘L hsumProj ℋ 0 + hsumIncl ℋ 1 ∘L B ∘L hsumProj ℋ 1

/-- A general `2 × 2` block operator on `HSum ℋ`. -/
noncomputable def blockOp (A00 A01 A10 A11 : L ℋ) : L (HSum ℋ) :=
  hsumIncl ℋ 0 ∘L A00 ∘L hsumProj ℋ 0 +
    hsumIncl ℋ 0 ∘L A01 ∘L hsumProj ℋ 1 +
    hsumIncl ℋ 1 ∘L A10 ∘L hsumProj ℋ 0 +
    hsumIncl ℋ 1 ∘L A11 ∘L hsumProj ℋ 1

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
theorem blockOp_ext {T S : L (HSum ℋ)}
    (h0 : ∀ z : HSum ℋ, hsumProj ℋ 0 (T z) = hsumProj ℋ 0 (S z))
    (h1 : ∀ z : HSum ℋ, hsumProj ℋ 1 (T z) = hsumProj ℋ 1 (S z)) :
    T = S := by
  ext z i
  fin_cases i
  · exact h0 z
  · exact h1 z

omit [Nontrivial ℋ] in
@[simp] theorem blockDiagonal_star (A B : L ℋ) :
    star (blockDiagonal (ℋ := ℋ) A B) = blockDiagonal (ℋ := ℋ) (star A) (star B) := by
  ext z i
  fin_cases i
  · simp [blockDiagonal, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp]
  · simp [blockDiagonal, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp]

/-- The `ℝ`-`⋆`-algebra homomorphism sending a pair of operators `(A, B)` to the
block-diagonal operator `diag(A, B)` on the Hilbert sum. -/
noncomputable def blockDiagonalHom : (L ℋ × L ℋ) →⋆ₐ[ℝ] L (HSum ℋ) where
  toFun p := blockDiagonal (ℋ := ℋ) p.1 p.2
  map_one' := by
    ext z
    simp [blockDiagonal]
  map_mul' := by
    intro p q
    ext z i
    fin_cases i <;>
      simp [blockDiagonal, hsumProj, hsumIncl, hsumEquiv, ContinuousLinearMap.mul_def]
  map_zero' := by
    ext z i
    fin_cases i <;> simp [blockDiagonal]
  map_add' := by
    intro p q
    ext z i
    fin_cases i <;>
      simp [blockDiagonal, hsumProj, hsumIncl, hsumEquiv, add_apply]
  commutes' := by
    intro r
    ext z i
    fin_cases i <;> {
      simp [blockDiagonal, hsumProj, hsumIncl, hsumEquiv, Algebra.algebraMap_eq_smul_one]
    }
  map_star' := by
    intro p
    simp

omit [Nontrivial ℋ] in
@[simp] theorem blockDiagonalHom_apply (p : L ℋ × L ℋ) :
    blockDiagonalHom (ℋ := ℋ) p = blockDiagonal (ℋ := ℋ) p.1 p.2 :=
  rfl

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem hsumProj_blockDiagonal_zero (A B : L ℋ) (z : HSum ℋ) :
    hsumProj ℋ 0 (blockDiagonal A B z) = A (hsumProj ℋ 0 z) := by
  simp [blockDiagonal]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem hsumProj_blockDiagonal_one (A B : L ℋ) (z : HSum ℋ) :
    hsumProj ℋ 1 (blockDiagonal A B z) = B (hsumProj ℋ 1 z) := by
  simp [blockDiagonal]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem blockDiagonal_one :
    blockDiagonal (ℋ := ℋ) (1 : L ℋ) (1 : L ℋ) = (1 : L (HSum ℋ)) := by
  ext z i
  fin_cases i <;> simp [blockDiagonal]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
theorem blockDiagonal_nonneg {A B : L ℋ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ blockDiagonal (ℋ := ℋ) A B := by
  have hApos : A.IsPositive := ContinuousLinearMap.nonneg_iff_isPositive.mp hA
  have hBpos : B.IsPositive := ContinuousLinearMap.nonneg_iff_isPositive.mp hB
  refine ContinuousLinearMap.nonneg_iff_isPositive.mpr ?_
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro z
  have hAz := (ContinuousLinearMap.isPositive_iff_complex A).mp hApos (hsumProj ℋ 0 z)
  have hBz := (ContinuousLinearMap.isPositive_iff_complex B).mp hBpos (hsumProj ℋ 1 z)
  have hz0 :
      inner ℂ ((hsumIncl ℋ 0) (A (hsumProj ℋ 0 z))) z =
        inner ℂ (A (hsumProj ℋ 0 z)) (hsumProj ℋ 0 z) := by
    simp [hsumProj, hsumIncl, hsumEquiv, PiLp.inner_apply]
  have hz1 :
      inner ℂ ((hsumIncl ℋ 1) (B (hsumProj ℋ 1 z))) z =
        inner ℂ (B (hsumProj ℋ 1 z)) (hsumProj ℋ 1 z) := by
    simp [hsumProj, hsumIncl, hsumEquiv, PiLp.inner_apply]
  constructor
  · dsimp [blockDiagonal]
    erw [inner_add_left, hz0, hz1]
    calc
      ↑(RCLike.re
          (inner ℂ (A (hsumProj ℋ 0 z)) (hsumProj ℋ 0 z) +
            inner ℂ (B (hsumProj ℋ 1 z)) (hsumProj ℋ 1 z))) =
          ↑(RCLike.re (inner ℂ (A (hsumProj ℋ 0 z)) (hsumProj ℋ 0 z)) +
            RCLike.re (inner ℂ (B (hsumProj ℋ 1 z)) (hsumProj ℋ 1 z))) := by
            simp
      _ = inner ℂ (A (hsumProj ℋ 0 z)) (hsumProj ℋ 0 z) +
          inner ℂ (B (hsumProj ℋ 1 z)) (hsumProj ℋ 1 z) := by
            have hsumre :
                (↑(RCLike.re (inner ℂ (A (hsumProj ℋ 0 z)) (hsumProj ℋ 0 z)) +
                    RCLike.re (inner ℂ (B (hsumProj ℋ 1 z)) (hsumProj ℋ 1 z))) : ℂ) =
                  ((RCLike.re (inner ℂ (A (hsumProj ℋ 0 z)) (hsumProj ℋ 0 z)) : ℂ) +
                    (RCLike.re (inner ℂ (B (hsumProj ℋ 1 z)) (hsumProj ℋ 1 z)) : ℂ)) := by
                  simp
            rw [hsumre, hAz.1, hBz.1]
  · dsimp [blockDiagonal]
    erw [inner_add_left, hz0, hz1]
    exact add_nonneg hAz.2 hBz.2

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem hsumProj_blockOp_zero (A00 A01 A10 A11 : L ℋ) (z : HSum ℋ) :
    hsumProj ℋ 0 (blockOp (ℋ := ℋ) A00 A01 A10 A11 z) =
      A00 (hsumProj ℋ 0 z) + A01 (hsumProj ℋ 1 z) := by
  simp [blockOp]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem hsumProj_blockOp_one (A00 A01 A10 A11 : L ℋ) (z : HSum ℋ) :
    hsumProj ℋ 1 (blockOp (ℋ := ℋ) A00 A01 A10 A11 z) =
      A10 (hsumProj ℋ 0 z) + A11 (hsumProj ℋ 1 z) := by
  simp [blockOp]

omit [Nontrivial ℋ] in
@[simp] theorem blockOp_star (A00 A01 A10 A11 : L ℋ) :
    star (blockOp (ℋ := ℋ) A00 A01 A10 A11) =
      blockOp (ℋ := ℋ) (star A00) (star A10) (star A01) (star A11) := by
  ext z i
  fin_cases i
  · simp [blockOp, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp]
    abel
  · simp [blockOp, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp]
    abel

end JensenOperatorInequality
