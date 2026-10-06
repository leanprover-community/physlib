/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.QuantumMechanics.HilbertSpaces.FiniteTarget.Operators
public import PhyslibAlpha.QuantumMechanics.HilbertSpaces.FiniteTarget.Product
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.State.VectorUncertainty
/-!

# Product states of a product of finite targets

## i. Overview

The product state `(ψ ⊗ φ) (a, b) = ψ a φ b` of two unit vectors describes two uncorrelated
coordinates. An observable acting on one coordinate only sees that coordinate: its mean, its
variance, its covariance with another such observable and their centered Gram defect are those
of the factor state.

## ii. Key results

- `prodVec` : the product vector `ψ ⊗ φ`, of norm `‖ψ‖ ‖φ‖` by `norm_prodVec`.
- `onFst_prodVec`, `onSnd_prodVec` : `(A ⊗ 1) (ψ ⊗ φ) = A ψ ⊗ φ` and `(1 ⊗ B) (ψ ⊗ φ) = ψ ⊗ B φ`.
- `onFstObservable`, `onSndObservable` : an observable acting on one coordinate.
- `variance_onFstObservable`, `covariance_onFstObservable`,
  `centeredGramDefect_onFstObservable` : the statistics of the first coordinate.
- `variance_onSndObservable`, `covariance_onSndObservable`,
  `centeredGramDefect_onSndObservable` : the statistics of the second coordinate.

## iii. Table of contents

- A. Product vectors
- B. Observables on one coordinate
- C. Statistics of the first coordinate
- D. Statistics of the second coordinate

## iv. References

* None.

-/

@[expose] public section

namespace QuantumMechanics

namespace FiniteHilbertSpace

open scoped ComplexOrder selfAdjoint
open ProbabilisticTheory
open InnerProductSpace UnitalPositiveLinearMap

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-!

## A. Product vectors

-/

/-- The product vector `(ψ ⊗ φ) (a, b) = ψ a φ b`. -/
noncomputable def prodVec (ψ : 𝓗[α]) (φ : 𝓗[β]) : 𝓗[α × β] :=
  ⟨WithLp.toLp 2 fun p => ψ.val p.1 * φ.val p.2⟩

lemma prodVec_val (ψ : 𝓗[α]) (φ : 𝓗[β]) (p : α × β) :
    (prodVec ψ φ).val p = ψ.val p.1 * φ.val p.2 := rfl

/-- `⟪ψ ⊗ φ, ψ' ⊗ φ'⟫ = ⟪ψ, ψ'⟫ ⟪φ, φ'⟫`. -/
lemma inner_prodVec (ψ ψ' : 𝓗[α]) (φ φ' : 𝓗[β]) :
    ⟪prodVec ψ φ, prodVec ψ' φ'⟫_ℂ = ⟪ψ, ψ'⟫_ℂ * ⟪φ, φ'⟫_ℂ := by
  rw [inner_eq_sum, Fintype.sum_prod_type, inner_eq_val ψ, inner_eq_val φ, PiLp.inner_apply,
    PiLp.inner_apply, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    simp only [prodVec_val, RCLike.inner_apply, map_mul]
    ring

/-- `‖ψ ⊗ φ‖ = ‖ψ‖ ‖φ‖`. -/
lemma norm_prodVec (ψ : 𝓗[α]) (φ : 𝓗[β]) : ‖prodVec ψ φ‖ = ‖ψ‖ * ‖φ‖ := by
  have h := inner_prodVec ψ ψ φ φ
  simp only [inner_self_eq_norm_sq_to_K] at h
  norm_cast at h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp (by rw [h, mul_pow])

/-- The product of two unit vectors is a unit vector. -/
lemma norm_prodVec_eq_one {ψ : 𝓗[α]} {φ : 𝓗[β]} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    ‖prodVec ψ φ‖ = 1 := by
  rw [norm_prodVec, hψ, hφ, one_mul]

lemma prodVec_sub_left (ψ ψ' : 𝓗[α]) (φ : 𝓗[β]) :
    prodVec (ψ - ψ') φ = prodVec ψ φ - prodVec ψ' φ := by
  ext p
  exact sub_mul _ _ _

lemma prodVec_sub_right (ψ : 𝓗[α]) (φ φ' : 𝓗[β]) :
    prodVec ψ (φ - φ') = prodVec ψ φ - prodVec ψ φ' := by
  ext p
  exact mul_sub _ _ _

lemma prodVec_smul_left (r : ℝ) (ψ : 𝓗[α]) (φ : 𝓗[β]) :
    prodVec (r • ψ) φ = r • prodVec ψ φ := by
  ext p
  simp [prodVec_val, ← Complex.coe_smul, mul_assoc]

lemma prodVec_smul_right (r : ℝ) (ψ : 𝓗[α]) (φ : 𝓗[β]) :
    prodVec ψ (r • φ) = r • prodVec ψ φ := by
  ext p
  simp [prodVec_val, ← Complex.coe_smul, mul_left_comm]

/-- `(A ⊗ 1) (ψ ⊗ φ) = A ψ ⊗ φ`. -/
lemma onFst_prodVec (A : 𝓗[α] →ₗ[ℂ] 𝓗[α]) (ψ : 𝓗[α]) (φ : 𝓗[β]) :
    onFst A (prodVec ψ φ) = prodVec (A ψ) φ := by
  ext p
  simp only [onFst_val, prodVec_val, val_apply A ψ, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- `(1 ⊗ B) (ψ ⊗ φ) = ψ ⊗ B φ`. -/
lemma onSnd_prodVec (B : 𝓗[β] →ₗ[ℂ] 𝓗[β]) (ψ : 𝓗[α]) (φ : 𝓗[β]) :
    onSnd B (prodVec ψ φ) = prodVec ψ (B φ) := by
  ext p
  simp only [onSnd_val, prodVec_val, val_apply B φ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-!

## B. Observables on one coordinate

-/

/-- An observable of the first coordinate as an observable of `𝓗[α × β]`. -/
noncomputable def onFstObservable (a : Observable (𝓗[α] →L[ℂ] 𝓗[α])) :
    Observable (𝓗[α × β] →L[ℂ] 𝓗[α × β]) :=
  ⟨LinearMap.toContinuousLinearMap (onFst (a : 𝓗[α] →L[ℂ] 𝓗[α]).toLinearMap),
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (onFst_isSymmetric (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp a.2))⟩

/-- An observable of the second coordinate as an observable of `𝓗[α × β]`. -/
noncomputable def onSndObservable (b : Observable (𝓗[β] →L[ℂ] 𝓗[β])) :
    Observable (𝓗[α × β] →L[ℂ] 𝓗[α × β]) :=
  ⟨LinearMap.toContinuousLinearMap (onSnd (b : 𝓗[β] →L[ℂ] 𝓗[β]).toLinearMap),
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (onSnd_isSymmetric (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp b.2))⟩

/-!

## C. Statistics of the first coordinate

-/

variable {ψ : 𝓗[α]} {φ : 𝓗[β]} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)

/-- The mean of the first coordinate is that of `ψ`. -/
lemma expectation_onFstObservable (a : Observable (𝓗[α] →L[ℂ] 𝓗[α])) :
    (ofVec (norm_prodVec_eq_one hψ hφ))⟨onFstObservable a⟩ = (ofVec hψ)⟨a⟩ := by
  apply Complex.ofReal_injective
  rw [← apply_observable_eq_expectation, ← apply_observable_eq_expectation, ofVec_apply,
    ofVec_apply]
  change ⟪prodVec ψ φ, onFst _ (prodVec ψ φ)⟫_ℂ = _
  rw [onFst_prodVec, inner_prodVec, inner_self_eq_norm_sq_to_K, hφ]
  rw [RCLike.ofReal_one, one_pow, mul_one]
  rfl

/-- The fluctuation of the first coordinate is that of `ψ`, tensored with `φ`. -/
lemma fluctuation_onFstObservable (a : Observable (𝓗[α] →L[ℂ] 𝓗[α])) :
    (onFstObservable (β := β) a : 𝓗[α × β] →L[ℂ] 𝓗[α × β]) (prodVec ψ φ) -
        (ofVec (norm_prodVec_eq_one hψ hφ))⟨onFstObservable a⟩ • prodVec ψ φ =
      prodVec ((a : 𝓗[α] →L[ℂ] 𝓗[α]) ψ - (ofVec hψ)⟨a⟩ • ψ) φ := by
  rw [expectation_onFstObservable hψ hφ, prodVec_sub_left, prodVec_smul_left]
  exact congrArg (· - _) (onFst_prodVec _ ψ φ)

lemma variance_onFstObservable (a : Observable (𝓗[α] →L[ℂ] 𝓗[α])) :
    variance (ofVec (norm_prodVec_eq_one hψ hφ)) (onFstObservable a) = variance (ofVec hψ) a := by
  rw [variance_ofVec, variance_ofVec, fluctuation_onFstObservable hψ hφ, norm_prodVec, hφ, mul_one]

lemma covariance_onFstObservable (a b : Observable (𝓗[α] →L[ℂ] 𝓗[α])) :
    covariance (ofVec (norm_prodVec_eq_one hψ hφ)) (onFstObservable a) (onFstObservable b) =
      covariance (ofVec hψ) a b := by
  rw [covariance_eq_re_apply_centered_mul, covariance_eq_re_apply_centered_mul,
    apply_centered_mul_centered_ofVec, apply_centered_mul_centered_ofVec,
    fluctuation_onFstObservable hψ hφ, fluctuation_onFstObservable hψ hφ, inner_prodVec,
    inner_self_eq_norm_sq_to_K, hφ]
  simp

lemma centeredGramDefect_onFstObservable (a b : Observable (𝓗[α] →L[ℂ] 𝓗[α])) :
    centeredGramDefect (ofVec (norm_prodVec_eq_one hψ hφ)) (onFstObservable a)
      (onFstObservable b) = centeredGramDefect (ofVec hψ) a b := by
  rw [centeredGramDefect_ofVec, centeredGramDefect_ofVec, fluctuation_onFstObservable hψ hφ,
    fluctuation_onFstObservable hψ hφ, inner_prodVec, inner_self_eq_norm_sq_to_K, norm_prodVec,
    norm_prodVec, hφ]
  simp

/-!

## D. Statistics of the second coordinate

-/

/-- The mean of the second coordinate is that of `φ`. -/
lemma expectation_onSndObservable (b : Observable (𝓗[β] →L[ℂ] 𝓗[β])) :
    (ofVec (norm_prodVec_eq_one hψ hφ))⟨onSndObservable b⟩ = (ofVec hφ)⟨b⟩ := by
  apply Complex.ofReal_injective
  rw [← apply_observable_eq_expectation, ← apply_observable_eq_expectation, ofVec_apply,
    ofVec_apply]
  change ⟪prodVec ψ φ, onSnd _ (prodVec ψ φ)⟫_ℂ = _
  rw [onSnd_prodVec, inner_prodVec, inner_self_eq_norm_sq_to_K, hψ, RCLike.ofReal_one, one_pow,
    one_mul]
  rfl

/-- The fluctuation of the second coordinate is `ψ` tensored with that of `φ`. -/
lemma fluctuation_onSndObservable (b : Observable (𝓗[β] →L[ℂ] 𝓗[β])) :
    (onSndObservable (α := α) b : 𝓗[α × β] →L[ℂ] 𝓗[α × β]) (prodVec ψ φ) -
        (ofVec (norm_prodVec_eq_one hψ hφ))⟨onSndObservable b⟩ • prodVec ψ φ =
      prodVec ψ ((b : 𝓗[β] →L[ℂ] 𝓗[β]) φ - (ofVec hφ)⟨b⟩ • φ) := by
  rw [expectation_onSndObservable hψ hφ, prodVec_sub_right, prodVec_smul_right]
  exact congrArg (· - _) (onSnd_prodVec _ ψ φ)

lemma variance_onSndObservable (b : Observable (𝓗[β] →L[ℂ] 𝓗[β])) :
    variance (ofVec (norm_prodVec_eq_one hψ hφ)) (onSndObservable b) = variance (ofVec hφ) b := by
  rw [variance_ofVec, variance_ofVec, fluctuation_onSndObservable hψ hφ, norm_prodVec, hψ, one_mul]

lemma covariance_onSndObservable (a b : Observable (𝓗[β] →L[ℂ] 𝓗[β])) :
    covariance (ofVec (norm_prodVec_eq_one hψ hφ)) (onSndObservable a) (onSndObservable b) =
      covariance (ofVec hφ) a b := by
  rw [covariance_eq_re_apply_centered_mul, covariance_eq_re_apply_centered_mul,
    apply_centered_mul_centered_ofVec, apply_centered_mul_centered_ofVec,
    fluctuation_onSndObservable hψ hφ, fluctuation_onSndObservable hψ hφ, inner_prodVec,
    inner_self_eq_norm_sq_to_K, hψ]
  simp

lemma centeredGramDefect_onSndObservable (a b : Observable (𝓗[β] →L[ℂ] 𝓗[β])) :
    centeredGramDefect (ofVec (norm_prodVec_eq_one hψ hφ)) (onSndObservable a)
      (onSndObservable b) = centeredGramDefect (ofVec hφ) a b := by
  rw [centeredGramDefect_ofVec, centeredGramDefect_ofVec, fluctuation_onSndObservable hψ hφ,
    fluctuation_onSndObservable hψ hφ, inner_prodVec, inner_self_eq_norm_sq_to_K, norm_prodVec,
    norm_prodVec, hψ]
  simp

end FiniteHilbertSpace

end QuantumMechanics
