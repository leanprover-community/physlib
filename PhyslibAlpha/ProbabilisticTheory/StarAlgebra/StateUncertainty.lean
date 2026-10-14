/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.GNS
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Lie
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.Uncertainty

/-!

# Uncertainty relations for states on a `*`-algebra

The Robertson–Schrödinger relation and Robertson's relation for several observables hold for a
state on any unital `*`-algebra, with no norm on the algebra.

## i. Overview

A state `ω` on a unital `*`-algebra `A`, as in `AlgState`, gives the positive semidefinite inner
product `⟨x, y⟩ = ω(x⋆ y)` on `A`. The fluctuation `a - ω(a)` of a self-adjoint `a` is again
self-adjoint, because `ω(a)` is real. For a family of observables `a_j`, the inner products of
their fluctuations form the matrix `Σ + iΩ`, where `Σ` is the covariance matrix and `Ω` the
matrix of expectations of brackets. It is a Gram matrix, so it is positive semidefinite, and so
is its transpose `Σ - iΩ`. Hence `|det Ω| ≤ det Σ`, by `Matrix.abs_det_le_det_of_posSemidef`.
For two observables, Cauchy–Schwarz gives `Cov(a, b)² + ω⟨⁅a, b⁆⟩² ≤ Var a · Var b`.

If `ω` is invariant under a `⋆`-automorphism `σ` with `σ a = a` and `σ b = -b`, then
`ω(a b) = ω(σ (a b)) = -ω(a b)` and `ω(b) = 0`, so the entries `Σ_ab` and `Ω_ab` vanish.

The C⋆-algebra version is `UnitalPositiveLinearMap.robertson_det`. This one also applies to an
algebra that is not complete, such as the quasi-local algebra of an infinite crystal, and so to
its translation invariant states and the thermodynamic limit states of `InvariantState`.

## ii. Key results

- `AlgState.covarianceMatrix`, `AlgState.bracketMatrix` : the matrices `Σ` and `Ω`.
- `AlgState.gram_fluctuation` : `Σ + iΩ` is the Gram matrix of the fluctuations.
- `AlgState.robertson_schrodinger` : the Robertson–Schrödinger relation.
- `AlgState.robertson_det` : **Robertson's relation for several observables**,
  `|det Ω| ≤ det Σ`.
- `AlgState.covariance_eq_zero_of_symm`, `AlgState.bracket_eq_zero_of_symm` : in a state
  invariant under a `⋆`-automorphism, an even and an odd observable have `Σ_ab = Ω_ab = 0`.

## iii. Table of contents

- A. Fluctuations
- B. The matrices `Σ` and `Ω`
- C. Uncertainty relations
- D. Symmetric states

## iv. References

* H. P. Robertson, *An indeterminacy relation for several observables and its classical
  interpretation*, Phys. Rev. 46 (1934) 794.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace AlgState

open scoped ComplexOrder InnerProductSpace selfAdjoint
open Matrix

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A] (ω : AlgState A)

/-! ## A. Fluctuations -/

/-- A self-adjoint element has a real expectation. -/
lemma apply_selfAdjoint (a : selfAdjoint A) : ω (a : A) = ((ω (a : A)).re : ℂ) := by
  have h := ω.map_star a
  rw [a.property.star_eq] at h
  exact (Complex.conj_eq_iff_re.mp h.symm).symm

/-- The fluctuation `a - ω(a)` of an observable. -/
def fluctuation (a : selfAdjoint A) : A := (a : A) - ω (a : A) • 1

lemma star_fluctuation (a : selfAdjoint A) : star (ω.fluctuation a) = ω.fluctuation a := by
  rw [fluctuation, star_sub, star_smul, star_one, a.property.star_eq, apply_selfAdjoint,
    Complex.star_def, Complex.conj_ofReal]

/-- The covariance `Re ω((a - ω(a)) (b - ω(b)))` of two observables. -/
noncomputable def covariance (a b : selfAdjoint A) : ℝ :=
  (ω (ω.fluctuation a * ω.fluctuation b)).re

/-- The variance of an observable. -/
noncomputable def variance (a : selfAdjoint A) : ℝ := ω.covariance a a

/-- The expectation of the bracket of two observables. -/
noncomputable def bracket (a b : selfAdjoint A) : ℝ := (ω ((⁅a, b⁆ : selfAdjoint A) : A)).re

/-- `ω((a - ω(a)) (b - ω(b))) = ω(a b) - ω(a) ω(b)`. -/
lemma apply_fluctuation_mul (a b : selfAdjoint A) :
    ω (ω.fluctuation a * ω.fluctuation b) = ω ((a : A) * b) - ω (a : A) * ω (b : A) := by
  simp only [fluctuation, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_sub, smul_smul]
  change ω.toLinearMap _ = ω.toLinearMap _ - ω.toLinearMap _ * ω.toLinearMap _
  simp only [_root_.map_sub, _root_.map_smul, ω.map_one', smul_eq_mul]
  have e (x : A) : ω x = ω.toLinearMap x := rfl
  simp only [e]
  ring

/-- The bracket is the imaginary part of `ω((a - ω(a)) (b - ω(b)))`. -/
lemma bracket_eq_im (a b : selfAdjoint A) :
    ω.bracket a b = (ω (ω.fluctuation a * ω.fluctuation b)).im := by
  have hba : ω ((b : A) * a) = star (ω ((a : A) * b)) := by
    rw [← ω.map_star, star_mul, a.property.star_eq, b.property.star_eq]
  have hsub : ω ((⁅a, b⁆ : selfAdjoint A) : A) =
      -(Complex.I / 2) * (ω ((a : A) * b) - ω ((b : A) * a)) := by
    rw [selfAdjoint.coe_bracket]
    change ω.toLinearMap _ = _
    rw [_root_.map_smul, _root_.map_sub, smul_eq_mul]
    rfl
  rw [bracket, hsub, hba, apply_fluctuation_mul, ω.apply_selfAdjoint a, ω.apply_selfAdjoint b]
  simp only [Complex.star_def, Complex.mul_re, Complex.neg_re, Complex.div_ofNat_re,
    Complex.I_re, Complex.neg_im, Complex.div_ofNat_im, Complex.I_im, Complex.sub_re,
    Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-! ## B. The matrices `Σ` and `Ω` -/

variable {ι : Type*}

/-- The covariance matrix `Σ_jk = Cov(a_j, a_k)` of a family of observables. -/
noncomputable def covarianceMatrix (a : ι → selfAdjoint A) : Matrix ι ι ℝ :=
  of fun j k => ω.covariance (a j) (a k)

/-- The matrix `Ω_jk = ω⟨⁅a_j, a_k⁆⟩` of expectations of brackets. -/
noncomputable def bracketMatrix (a : ι → selfAdjoint A) : Matrix ι ι ℝ :=
  of fun j k => ω.bracket (a j) (a k)

/-- The fluctuation of an observable as a vector of the pre-Hilbert space of the state. -/
def fluctuationVector (a : selfAdjoint A) : ω.PreGNS := ω.toPre (ω.fluctuation a)

lemma inner_fluctuationVector (a b : selfAdjoint A) :
    ⟪ω.fluctuationVector a, ω.fluctuationVector b⟫_ℂ =
      ω (ω.fluctuation a * ω.fluctuation b) := by
  rw [inner_pre]
  change ω (star (ω.fluctuation a) * ω.fluctuation b) = _
  rw [star_fluctuation]

/-- **`Σ + iΩ` is the Gram matrix of the fluctuations.** -/
lemma gram_fluctuation (a : ι → selfAdjoint A) :
    gram ℂ (fun j => ω.fluctuationVector (a j)) =
      (ω.covarianceMatrix a).map ((↑) : ℝ → ℂ) +
        Complex.I • (ω.bracketMatrix a).map ((↑) : ℝ → ℂ) := by
  ext j k
  rw [gram, of_apply, inner_fluctuationVector]
  apply Complex.ext <;>
    simp [covarianceMatrix, bracketMatrix, covariance, bracket_eq_im]

/-- `Σ - iΩ` is the transpose of the Gram matrix. -/
lemma transpose_gram_fluctuation (a : ι → selfAdjoint A) :
    (gram ℂ (fun j => ω.fluctuationVector (a j)))ᵀ =
      (ω.covarianceMatrix a).map ((↑) : ℝ → ℂ) -
        Complex.I • (ω.bracketMatrix a).map ((↑) : ℝ → ℂ) := by
  ext j k
  rw [transpose_apply, gram, of_apply, ← inner_conj_symm, inner_fluctuationVector]
  apply Complex.ext <;>
    simp [covarianceMatrix, bracketMatrix, covariance, bracket_eq_im]

/-! ## C. Uncertainty relations -/

/-- **The Robertson–Schrödinger relation** for a state on a `*`-algebra:
`Cov(a, b)² + ω⟨⁅a, b⁆⟩² ≤ Var a · Var b`. -/
lemma robertson_schrodinger (a b : selfAdjoint A) :
    ω.covariance a b ^ 2 + ω.bracket a b ^ 2 ≤ ω.variance a * ω.variance b := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (ω.fluctuationVector a) (ω.fluctuationVector b)
  have hn (c : selfAdjoint A) : ‖ω.fluctuationVector c‖ ^ 2 = ω.variance c := by
    rw [@norm_sq_eq_re_inner ℂ, inner_fluctuationVector]
    rfl
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, hn, hn, inner_fluctuationVector, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply] at h2
  rw [covariance, bracket_eq_im]
  nlinarith [h2]

/-- **Robertson's uncertainty relation for several observables** for a state on a `*`-algebra:
for every finite family of observables, `|det Ω| ≤ det Σ`. -/
lemma robertson_det [Fintype ι] [DecidableEq ι] (a : ι → selfAdjoint A) :
    |(ω.bracketMatrix a).det| ≤ (ω.covarianceMatrix a).det := by
  have hG := posSemidef_gram ℂ fun j => ω.fluctuationVector (a j)
  exact abs_det_le_det_of_posSemidef
    (by rw [← transpose_gram_fluctuation]; exact hG.transpose)
    (by rw [← gram_fluctuation]; exact hG)

/-! ## D. Symmetric states -/

section Symm

variable (σ : A ≃⋆ₐ[ℂ] A) (hω : ∀ x, ω (σ x) = ω x) {a b : selfAdjoint A}
  (ha : σ (a : A) = a) (hb : σ (b : A) = -b)
include hω hb

lemma apply_eq_zero_of_symm : ω (b : A) = 0 := by
  have h := hω b
  rw [hb] at h
  change ω.toLinearMap (-(b : A)) = ω.toLinearMap b at h
  rw [_root_.map_neg] at h
  linear_combination -h / 2

include ha in
lemma apply_mul_eq_zero_of_symm : ω ((a : A) * b) = 0 := by
  have h := hω ((a : A) * b)
  rw [_root_.map_mul, ha, hb, mul_neg] at h
  change ω.toLinearMap (-((a : A) * b)) = ω.toLinearMap ((a : A) * b) at h
  rw [_root_.map_neg] at h
  linear_combination -h / 2

include ha in
/-- **In a symmetric state, an even and an odd observable have covariance zero.** -/
lemma covariance_eq_zero_of_symm : ω.covariance a b = 0 := by
  rw [covariance, apply_fluctuation_mul, apply_mul_eq_zero_of_symm ω σ hω ha hb,
    apply_eq_zero_of_symm ω σ hω hb]
  simp

include ha in
/-- **In a symmetric state, an even and an odd observable have a bracket of expectation
zero.** -/
lemma bracket_eq_zero_of_symm : ω.bracket a b = 0 := by
  rw [bracket_eq_im, apply_fluctuation_mul, apply_mul_eq_zero_of_symm ω σ hω ha hb,
    apply_eq_zero_of_symm ω σ hω hb]
  simp

end Symm

end AlgState

end ProbabilisticTheory
