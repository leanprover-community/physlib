/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.StateUncertainty
public import Mathlib.RepresentationTheory.Irreducible

/-!

# The covariance form of a state and its symmetries

## i. Overview

A state `ω` on a unital `*`-algebra `A` has the covariance form
`C(a, b) = ω(a⋆ b) - conj (ω a) ω(b)`, the inner product of the fluctuations `a - ω(a)` and
`b - ω(b)` in the pre-Hilbert space of the state. It is antilinear in `a` and linear in `b`. For
observables, `C(a, b) = Cov(a, b) + i ω⟨⁅a, b⁆⟩`, so `C` contains both matrices `Σ` and `Ω` of
Robertson's relation.

If `ω` is invariant under a `⋆`-automorphism `σ`, then `C(σ a, σ b) = C(a, b)`. If `σ` acts on
two finite families of elements by the matrices `R` and `S`, the matrix of covariances `M`
satisfies `Rᴴ M S = M`. When `R` is unitary this says `M S = R M`, so `M` is an intertwining map,
and by Schur's lemma it vanishes when a group acts on the two families by inequivalent
irreducible representations. For one-dimensional representations this says that elements
transforming with different characters have covariance zero. With `ℤ/2` it gives the vanishing of
the covariance between an even and an odd element; with translations it gives the vanishing of
the covariance between different crystal momenta.

## ii. Key results

- `AlgState.covarianceForm` : the covariance form `C(a, b) = ω(a⋆ b) - conj (ω a) ω(b)`.
- `AlgState.covarianceForm_selfAdjoint` : `C(a, b) = Cov(a, b) + i ω⟨⁅a, b⁆⟩` for observables.
- `AlgState.covarianceForm_map` : a symmetry of the state preserves `C`.
- `AlgState.posSemidef_covarianceMatrixForm` : the matrix of `C` on a family is positive
  semidefinite.
- `AlgState.conjTranspose_mul_covarianceMatrixForm_mul` : `Rᴴ M S = M`.
- `AlgState.covarianceForm_eq_zero_of_character` : elements transforming with different
  unitary characters have covariance zero.
- `AlgState.covarianceMatrixForm_eq_zero_of_irreducible` : **Schur's lemma** for covariances,
  families transforming under inequivalent irreducible unitary representations have covariance
  zero.

## iii. Table of contents

- A. The covariance form
- B. Symmetries
- C. Matrices of covariances
- D. Schur's lemma

## iv. References

* E. Wigner, Group Theory and its Application to the Quantum Mechanics of Atomic Spectra,
  Chapter 21.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace AlgState

open scoped ComplexOrder InnerProductSpace
open Matrix

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A] (ω : AlgState A)

/-! ## A. The covariance form -/

/-- The fluctuation `a - ω(a)` of an element, as a linear map. -/
def fluctuationMap : A →ₗ[ℂ] A where
  toFun a := a - ω a • 1
  map_add' a b := by rw [ω.map_add, add_smul]; abel
  map_smul' c a := by rw [ω.map_smul, mul_smul, smul_sub]; rfl

lemma fluctuationMap_apply (a : A) : ω.fluctuationMap a = a - ω a • 1 := rfl

/-- The covariance form `C(a, b) = ω(a⋆ b) - conj (ω a) ω(b)`, the inner product of the
fluctuations in the pre-Hilbert space of the state. -/
noncomputable def covarianceForm (a b : A) : ℂ :=
  ⟪ω.toPre (ω.fluctuationMap a), ω.toPre (ω.fluctuationMap b)⟫_ℂ

lemma covarianceForm_apply (a b : A) :
    ω.covarianceForm a b = ω (star a * b) - star (ω a) * ω b := by
  rw [covarianceForm, inner_pre]
  change ω (star (a - ω a • 1) * (b - ω b • 1)) = _
  rw [star_sub, star_smul, star_one, sub_mul, mul_sub, mul_sub, smul_mul_assoc, one_mul,
    mul_smul_comm, mul_one, smul_mul_assoc, one_mul, smul_smul]
  change ω.toLinearMap _ = _
  simp only [_root_.map_sub, _root_.map_smul, smul_eq_mul]
  have e (x : A) : ω.toLinearMap x = ω x := rfl
  simp only [e, ω.map_one, ω.map_star]
  ring

lemma covarianceForm_smul_left (c : ℂ) (a b : A) :
    ω.covarianceForm (c • a) b = star c * ω.covarianceForm a b := by
  rw [covarianceForm, covarianceForm, _root_.map_smul, _root_.map_smul, inner_smul_left]
  rfl

lemma covarianceForm_smul_right (c : ℂ) (a b : A) :
    ω.covarianceForm a (c • b) = c * ω.covarianceForm a b := by
  rw [covarianceForm, covarianceForm, _root_.map_smul, _root_.map_smul, inner_smul_right]

lemma covarianceForm_sum_left {ι : Type*} (s : Finset ι) (a : ι → A) (b : A) :
    ω.covarianceForm (∑ i ∈ s, a i) b = ∑ i ∈ s, ω.covarianceForm (a i) b := by
  simp only [covarianceForm, map_sum, sum_inner]

lemma covarianceForm_sum_right {ι : Type*} (s : Finset ι) (a : A) (b : ι → A) :
    ω.covarianceForm a (∑ i ∈ s, b i) = ∑ i ∈ s, ω.covarianceForm a (b i) := by
  simp only [covarianceForm, map_sum, inner_sum]

/-- For observables, `C(a, b) = Cov(a, b) + i ω⟨⁅a, b⁆⟩`. -/
lemma covarianceForm_selfAdjoint (a b : selfAdjoint A) :
    ω.covarianceForm a b = ω.covariance a b + Complex.I * ω.bracket a b := by
  have h : ω.covarianceForm a b = ω (ω.fluctuation a * ω.fluctuation b) := by
    rw [covarianceForm_apply, apply_fluctuation_mul, ω.apply_selfAdjoint a]
    simp
  rw [h, covariance, bracket_eq_im]
  apply Complex.ext <;> simp

/-! ## B. Symmetries -/

section Symm

variable (σ : A ≃⋆ₐ[ℂ] A) (hω : ∀ x, ω (σ x) = ω x)
include hω

/-- **A symmetry of the state preserves the covariance form**: `C(σ a, σ b) = C(a, b)`. -/
lemma covarianceForm_map (a b : A) : ω.covarianceForm (σ a) (σ b) = ω.covarianceForm a b := by
  rw [covarianceForm_apply, covarianceForm_apply, ← StarHomClass.map_star, ← _root_.map_mul, hω,
    hω, hω]

/-- Elements multiplied by `χ` and `χ'` under a symmetry, with `conj χ · χ' ≠ 1`, have
covariance zero. -/
lemma covarianceForm_eq_zero_of_smul {a b : A} {χ χ' : ℂ} (ha : σ a = χ • a) (hb : σ b = χ' • b)
    (h : star χ * χ' ≠ 1) : ω.covarianceForm a b = 0 := by
  have e := ω.covarianceForm_map σ hω a b
  rw [ha, hb, covarianceForm_smul_left, covarianceForm_smul_right, ← mul_assoc] at e
  have e' : (star χ * χ' - 1) * ω.covarianceForm a b = 0 := by linear_combination e
  exact (mul_eq_zero.mp e').resolve_left (sub_ne_zero.mpr h)

/-- **An even and an odd element have covariance zero.** -/
lemma covarianceForm_eq_zero_of_neg {a b : A} (ha : σ a = a) (hb : σ b = -b) :
    ω.covarianceForm a b = 0 :=
  ω.covarianceForm_eq_zero_of_smul σ hω (χ := 1) (χ' := -1) (by rw [one_smul, ha])
    (by rw [neg_one_smul, hb]) (by norm_num)

end Symm

section Character

variable {Γ : Type*} [Group Γ] (α : Γ →* (A ≃⋆ₐ[ℂ] A)) (hα : ∀ g x, ω (α g x) = ω x)
include hα

/-- **Elements transforming with different unitary characters have covariance zero.** If
`α g a = χ g • a` and `α g b = χ' g • b` with `|χ g| = 1` and `χ ≠ χ'`, then `C(a, b) = 0`. -/
lemma covarianceForm_eq_zero_of_character {a b : A} {χ χ' : Γ → ℂ} (hχ : ∀ g, ‖χ g‖ = 1)
    (ha : ∀ g, α g a = χ g • a) (hb : ∀ g, α g b = χ' g • b) (hne : χ ≠ χ') :
    ω.covarianceForm a b = 0 := by
  obtain ⟨g, hg⟩ := Function.ne_iff.mp hne
  refine ω.covarianceForm_eq_zero_of_smul (α g) (hα g) (ha g) (hb g) fun h => hg ?_
  have hn : star (χ g) * χ g = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hχ]
    norm_num
  linear_combination -(χ g) * h + χ' g * hn

end Character

/-! ## C. Matrices of covariances -/

section Matrix

variable {ι κ : Type*}

/-- The matrix `M_ik = C(a_i, b_k)` of covariances of two families. -/
noncomputable def covarianceMatrixForm (a : ι → A) (b : κ → A) : Matrix ι κ ℂ :=
  of fun i k => ω.covarianceForm (a i) (b k)

variable [Fintype ι] [Fintype κ]

/-- **The matrix of covariances of a family is positive semidefinite**, being a Gram matrix. -/
lemma posSemidef_covarianceMatrixForm (a : ι → A) : (ω.covarianceMatrixForm a a).PosSemidef := by
  have h : ω.covarianceMatrixForm a a =
      gram ℂ fun i => ω.toPre (ω.fluctuationMap (a i)) := by
    ext i k
    rfl
  rw [h]
  exact posSemidef_gram ℂ _

/-- **A symmetry of the state preserves the matrix of covariances**: if `σ` acts on the two
families by the matrices `R` and `S`, then `Rᴴ M S = M`. -/
lemma conjTranspose_mul_covarianceMatrixForm_mul (σ : A ≃⋆ₐ[ℂ] A) (hω : ∀ x, ω (σ x) = ω x)
    {a : ι → A} {b : κ → A} {R : Matrix ι ι ℂ} {S : Matrix κ κ ℂ}
    (ha : ∀ i, σ (a i) = ∑ j, R j i • a j) (hb : ∀ k, σ (b k) = ∑ l, S l k • b l) :
    Rᴴ * ω.covarianceMatrixForm a b * S = ω.covarianceMatrixForm a b := by
  ext i k
  have e := ω.covarianceForm_map σ hω (a i) (b k)
  rw [ha, hb, covarianceForm_sum_left] at e
  simp only [covarianceForm_sum_right, covarianceForm_smul_left, covarianceForm_smul_right] at e
  simp only [mul_apply, conjTranspose_apply, covarianceMatrixForm, of_apply, Finset.sum_mul]
  rw [← e, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end Matrix

/-! ## D. Schur's lemma -/

section Schur

variable {Γ : Type*} [Group Γ] (α : Γ →* (A ≃⋆ₐ[ℂ] A)) (hα : ∀ g x, ω (α g x) = ω x)
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  (ρ : Representation ℂ Γ (ι → ℂ)) (π : Representation ℂ Γ (κ → ℂ))
include hα

/-- If `α` acts on the families `a` and `b` by `ρ` and `π`, with `ρ` unitary, then the matrix of
covariances intertwines `π` with `ρ`. -/
lemma covarianceMatrixForm_isIntertwining {a : ι → A} {b : κ → A}
    (hρ : ∀ g, LinearMap.toMatrix' (ρ g) ∈ unitaryGroup ι ℂ)
    (ha : ∀ g i, α g (a i) = ∑ j, LinearMap.toMatrix' (ρ g) j i • a j)
    (hb : ∀ g k, α g (b k) = ∑ l, LinearMap.toMatrix' (π g) l k • b l) (g : Γ) :
    toLin' (ω.covarianceMatrixForm a b) ∘ₗ π g =
      ρ g ∘ₗ toLin' (ω.covarianceMatrixForm a b) := by
  have e := ω.conjTranspose_mul_covarianceMatrixForm_mul (α g) (hα g) (ha g) (hb g)
  have hR : LinearMap.toMatrix' (ρ g) * (LinearMap.toMatrix' (ρ g))ᴴ = 1 :=
    mem_unitaryGroup_iff.mp (hρ g)
  have h : ω.covarianceMatrixForm a b * LinearMap.toMatrix' (π g) =
      LinearMap.toMatrix' (ρ g) * ω.covarianceMatrixForm a b := by
    calc ω.covarianceMatrixForm a b * LinearMap.toMatrix' (π g)
        = LinearMap.toMatrix' (ρ g) * (LinearMap.toMatrix' (ρ g))ᴴ *
            ω.covarianceMatrixForm a b * LinearMap.toMatrix' (π g) := by
          rw [hR, Matrix.one_mul]
      _ = LinearMap.toMatrix' (ρ g) * ((LinearMap.toMatrix' (ρ g))ᴴ *
            ω.covarianceMatrixForm a b * LinearMap.toMatrix' (π g)) := by
          simp only [Matrix.mul_assoc]
      _ = LinearMap.toMatrix' (ρ g) * ω.covarianceMatrixForm a b := by rw [e]
  have h' := congrArg toLin' h
  rwa [toLin'_mul, toLin'_mul, toLin'_toMatrix', toLin'_toMatrix'] at h'

/-- **Schur's lemma for covariances.** If a group of symmetries of the state acts on the family
`a` by the irreducible unitary representation `ρ` and on the family `b` by the irreducible
representation `π`, and `π` and `ρ` are not equivalent, then `C(a_i, b_k) = 0` for all `i, k`. -/
lemma covarianceMatrixForm_eq_zero_of_irreducible [ρ.IsIrreducible] [π.IsIrreducible]
    [IsEmpty (π.Equiv ρ)] {a : ι → A} {b : κ → A}
    (hρ : ∀ g, LinearMap.toMatrix' (ρ g) ∈ unitaryGroup ι ℂ)
    (ha : ∀ g i, α g (a i) = ∑ j, LinearMap.toMatrix' (ρ g) j i • a j)
    (hb : ∀ g k, α g (b k) = ∑ l, LinearMap.toMatrix' (π g) l k • b l) :
    ω.covarianceMatrixForm a b = 0 := by
  let f : Representation.IntertwiningMap π ρ :=
    (toLin' (ω.covarianceMatrixForm a b)).intertwiningMap_of_isIntertwiningMap π ρ fun g v =>
      LinearMap.congr_fun (ω.covarianceMatrixForm_isIntertwining α hα ρ π hρ ha hb g) v
  have hf : f = 0 := Subsingleton.elim _ _
  have h : toLin' (ω.covarianceMatrixForm a b) = 0 := by
    ext v i
    exact congrFun (congrArg (fun φ : Representation.IntertwiningMap π ρ => φ (Pi.single v 1)) hf) i
  exact toLin'.injective (h.trans (map_zero _).symm)

end Schur

end AlgState

end ProbabilisticTheory
