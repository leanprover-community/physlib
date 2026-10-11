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

Beyond product states, minimum uncertainty on one coordinate is read slice by slice. If `Ψ` has
minimum uncertainty for two observables of the first coordinate, their fluctuation vectors are
linearly dependent, and so are those of every nonzero slice `a ↦ Ψ (a, b)`: each slice has minimum
uncertainty. The mean of a third observable is the average over the slices, weighted by their
squared norms, so any bound on the minimum uncertainty vectors of the coordinate holds for `Ψ`.

## ii. Key results

- `prodVec` : the product vector `ψ ⊗ φ`, of norm `‖ψ‖ ‖φ‖` by `norm_prodVec`.
- `onFst_prodVec`, `onSnd_prodVec` : `(A ⊗ 1) (ψ ⊗ φ) = A ψ ⊗ φ` and `(1 ⊗ B) (ψ ⊗ φ) = ψ ⊗ B φ`.
- `onFstObservable`, `onSndObservable` : an observable acting on one coordinate.
- `variance_onFstObservable`, `covariance_onFstObservable`,
  `centeredGramDefect_onFstObservable` : the statistics of the first coordinate.
- `variance_onSndObservable`, `covariance_onSndObservable`,
  `centeredGramDefect_onSndObservable` : the statistics of the second coordinate.
- `covariance_onFstObservable_onSndObservable` : the two coordinates are uncorrelated.
- `abs_expectation_le_of_slices` : minimum uncertainty passes to the slices.
- `abs_expectation_onFstObservable_le`, `abs_expectation_onSndObservable_le` : a bound on the
  minimum uncertainty vectors of one coordinate holds on `𝓗[α × β]`.

## iii. Table of contents

- A. Product vectors
- B. Observables on one coordinate
- C. Statistics of the first coordinate
- D. Statistics of the second coordinate
- E. Different coordinates are uncorrelated
- F. Minimum uncertainty on one coordinate

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

/-!

## E. Different coordinates are uncorrelated

-/

/-- The fluctuation vector of an observable is orthogonal to the state. -/
lemma inner_fluctuation {γ : Type*} [Fintype γ] [DecidableEq γ] {χ : 𝓗[γ]} (hχ : ‖χ‖ = 1)
    (c : Observable (𝓗[γ] →L[ℂ] 𝓗[γ])) :
    ⟪χ, (c : 𝓗[γ] →L[ℂ] 𝓗[γ]) χ - (ofVec hχ)⟨c⟩ • χ⟫_ℂ = 0 := by
  have h := apply_observable_eq_expectation (ofVec hχ) c
  rw [ofVec_apply] at h
  rw [inner_sub_right, ← Complex.coe_smul, inner_smul_right, inner_self_eq_norm_sq_to_K, hχ,
    ← h]
  simp

/-- In a product state, an observable of the first coordinate and one of the second are
uncorrelated. -/
lemma covariance_onFstObservable_onSndObservable (a : Observable (𝓗[α] →L[ℂ] 𝓗[α]))
    (b : Observable (𝓗[β] →L[ℂ] 𝓗[β])) :
    covariance (ofVec (norm_prodVec_eq_one hψ hφ)) (onFstObservable a) (onSndObservable b) = 0 := by
  rw [covariance_eq_re_apply_centered_mul, apply_centered_mul_centered_ofVec,
    fluctuation_onFstObservable hψ hφ, fluctuation_onSndObservable hψ hφ, inner_prodVec,
    inner_fluctuation hφ, mul_zero, Complex.zero_re]

/-!

## F. Minimum uncertainty on one coordinate

-/

section MinUncertainty

variable {γ ι R : Type*} [Fintype γ] [DecidableEq γ] [Fintype ι] [DecidableEq ι] [Fintype R]

/-- The slice `a ↦ Ψ (a, b)` of a vector of `𝓗[α × β]` at the second coordinate `b`. -/
noncomputable def fstSlice (b : β) : 𝓗[α × β] →ₗ[ℂ] 𝓗[α] where
  toFun Ψ := ⟨WithLp.toLp 2 fun a => Ψ.val (a, b)⟩
  map_add' Ψ Φ := by ext a; simp
  map_smul' c Ψ := by ext a; simp

/-- The slice `b ↦ Ψ (a, b)` of a vector of `𝓗[α × β]` at the first coordinate `a`. -/
noncomputable def sndSlice (a : α) : 𝓗[α × β] →ₗ[ℂ] 𝓗[β] where
  toFun Ψ := ⟨WithLp.toLp 2 fun b => Ψ.val (a, b)⟩
  map_add' Ψ Φ := by ext b; simp
  map_smul' c Ψ := by ext b; simp

lemma fstSlice_onFst (A : 𝓗[α] →ₗ[ℂ] 𝓗[α]) (b : β) (Ψ : 𝓗[α × β]) :
    fstSlice b (onFst A Ψ) = A (fstSlice b Ψ) := by
  ext a
  exact (val_apply A (fstSlice b Ψ) a).symm

lemma sndSlice_onSnd (B : 𝓗[β] →ₗ[ℂ] 𝓗[β]) (a : α) (Ψ : 𝓗[α × β]) :
    sndSlice a (onSnd B Ψ) = B (sndSlice a Ψ) := by
  ext b
  exact (val_apply B (sndSlice a Ψ) b).symm

/-- The inner product of `𝓗[γ]` in components. -/
private lemma inner_eq_sum' (ψ φ : 𝓗[γ]) : ⟪ψ, φ⟫_ℂ = ∑ c, (starRingEnd ℂ) (ψ.val c) * φ.val c := by
  rw [inner_eq_val, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun c _ => by rw [RCLike.inner_apply, mul_comm]

/-- The inner product of `𝓗[α × β]` is the sum of the inner products of the slices. -/
lemma inner_eq_sum_fstSlice (Ψ Φ : 𝓗[α × β]) :
    ⟪Ψ, Φ⟫_ℂ = ∑ b, ⟪fstSlice b Ψ, fstSlice b Φ⟫_ℂ := by
  simp only [inner_eq_sum', Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- The inner product of `𝓗[α × β]` is the sum of the inner products of the slices. -/
lemma inner_eq_sum_sndSlice (Ψ Φ : 𝓗[α × β]) :
    ⟪Ψ, Φ⟫_ℂ = ∑ a, ⟪sndSlice a Ψ, sndSlice a Φ⟫_ℂ := by
  simp only [inner_eq_sum', Fintype.sum_prod_type]
  rfl

/-- In a unit vector, the expectation is `re ⟨ψ|a|ψ⟩`. -/
private lemma expectation_ofVec_eq_re {u : 𝓗[γ]} (hu : ‖u‖ = 1)
    (a : Observable (𝓗[γ] →L[ℂ] 𝓗[γ])) :
    (ofVec hu)⟨a⟩ = (⟪u, (a : 𝓗[γ] →L[ℂ] 𝓗[γ]) u⟫_ℂ).re := by
  rw [← Complex.ofReal_re ((ofVec hu)⟨a⟩), ← apply_observable_eq_expectation, ofVec_apply]
  rfl

/-- Linearly dependent vectors have no Cauchy–Schwarz defect. -/
private lemma norm_sq_mul_norm_sq_eq {x y : 𝓗[γ]} {p q : ℂ} (hpq : p ≠ 0 ∨ q ≠ 0)
    (h : p • x + q • y = 0) : ‖x‖ ^ 2 * ‖y‖ ^ 2 = ‖⟪x, y⟫_ℂ‖ ^ 2 := by
  rw [← mul_pow]
  rcases hpq with hp | hq
  · have hx : x = (-(p⁻¹ * q)) • y := by
      rw [neg_smul, mul_smul, ← smul_neg, neg_eq_of_add_eq_zero_left h, inv_smul_smul₀ hp]
    have h3 : y = 0 ∨ ∃ r : ℂ, x = r • y := Or.inr ⟨_, hx⟩
    have e : ‖⟪y, x⟫_ℂ‖ = ‖y‖ * ‖x‖ := ((norm_inner_eq_norm_tfae ℂ y x).out 3 1).mp h3
    rw [norm_inner_symm, e, mul_comm]
  · have hy : y = (-(q⁻¹ * p)) • x := by
      rw [neg_smul, mul_smul, ← smul_neg, neg_eq_of_add_eq_zero_right h, inv_smul_smul₀ hq]
    have h3 : x = 0 ∨ ∃ r : ℂ, y = r • x := Or.inr ⟨_, hy⟩
    have e : ‖⟪x, y⟫_ℂ‖ = ‖x‖ * ‖y‖ := ((norm_inner_eq_norm_tfae ℂ x y).out 3 1).mp h3
    rw [e]

/-- Without Cauchy–Schwarz defect, two vectors are linearly dependent. -/
private lemma exists_smul_add_smul_eq_zero {x y : 𝓗[γ]}
    (h : ‖x‖ ^ 2 * ‖y‖ ^ 2 - ‖⟪x, y⟫_ℂ‖ ^ 2 = 0) :
    ∃ p q : ℂ, (p ≠ 0 ∨ q ≠ 0) ∧ p • x + q • y = 0 := by
  rw [sub_eq_zero, ← mul_pow] at h
  have h' := ((pow_left_inj₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h).symm
  rcases ((norm_inner_eq_norm_tfae ℂ x y).out 1 3).mp h' with hx | ⟨r, hr⟩
  · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hx]⟩
  · exact ⟨r, -1, Or.inr (by norm_num), by rw [hr]; simp⟩

/-- If `p (a - m₁) u + q (b - m₂) u = 0` for some centers `m₁`, `m₂`, then the unit vector `u`
has minimum uncertainty for `a` and `b`: the centers are forced to be the means. -/
lemma centeredGramDefect_ofVec_eq_zero_of_smul_add_smul {u : 𝓗[γ]} (hu : ‖u‖ = 1)
    {a b : Observable (𝓗[γ] →L[ℂ] 𝓗[γ])} {p q m₁ m₂ : ℂ} (hpq : p ≠ 0 ∨ q ≠ 0)
    (h : p • ((a : 𝓗[γ] →L[ℂ] 𝓗[γ]) u - m₁ • u) + q • ((b : 𝓗[γ] →L[ℂ] 𝓗[γ]) u - m₂ • u) = 0) :
    centeredGramDefect (ofVec hu) a b = 0 := by
  set x := (a : 𝓗[γ] →L[ℂ] 𝓗[γ]) u - (ofVec hu)⟨a⟩ • u
  set y := (b : 𝓗[γ] →L[ℂ] 𝓗[γ]) u - (ofVec hu)⟨b⟩ • u
  set κ := p * (m₁ - (ofVec hu)⟨a⟩) + q * (m₂ - (ofVec hu)⟨b⟩)
  have hκ : p • x + q • y = κ • u := by
    simp only [x, y, κ, ← Complex.coe_smul]
    linear_combination (norm := module) h
  have hκ0 : κ = 0 := by
    have h1 := congrArg (fun z => ⟪u, z⟫_ℂ) hκ
    simp only [inner_add_right, inner_smul_right, x, y, inner_fluctuation hu,
      inner_self_eq_norm_sq_to_K, hu] at h1
    simpa using h1.symm
  rw [hκ0, zero_smul] at hκ
  rw [centeredGramDefect_ofVec, norm_sq_mul_norm_sq_eq hpq hκ, sub_self]

/-- A slice of a relation `p (a - m₁) w + q (b - m₂) w = 0` moves no faster than the bound `v` of
the minimum uncertainty vectors, weighted by its squared norm. -/
private lemma abs_re_inner_le {a b c : Observable (𝓗[γ] →L[ℂ] 𝓗[γ])} {v : ℝ}
    (hP : ∀ (u : 𝓗[γ]) (hu : ‖u‖ = 1), centeredGramDefect (ofVec hu) a b = 0 →
      |(ofVec hu)⟨c⟩| ≤ v)
    {w : 𝓗[γ]} {p q m₁ m₂ : ℂ} (hpq : p ≠ 0 ∨ q ≠ 0)
    (h : p • ((a : 𝓗[γ] →L[ℂ] 𝓗[γ]) w - m₁ • w) + q • ((b : 𝓗[γ] →L[ℂ] 𝓗[γ]) w - m₂ • w) = 0) :
    |(⟪w, (c : 𝓗[γ] →L[ℂ] 𝓗[γ]) w⟫_ℂ).re| ≤ ‖w‖ ^ 2 * v := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
  set u := (‖w‖ : ℂ)⁻¹ • w
  have hu : ‖u‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
  have hrel : p • ((a : 𝓗[γ] →L[ℂ] 𝓗[γ]) u - m₁ • u) +
      q • ((b : 𝓗[γ] →L[ℂ] 𝓗[γ]) u - m₂ • u) = 0 := by
    simp only [u, map_smul]
    linear_combination (norm := module) (‖w‖ : ℂ)⁻¹ • h
  have hc := hP u hu (centeredGramDefect_ofVec_eq_zero_of_smul_add_smul hu hpq hrel)
  have he : (⟪w, (c : 𝓗[γ] →L[ℂ] 𝓗[γ]) w⟫_ℂ).re = ‖w‖ ^ 2 * (ofVec hu)⟨c⟩ := by
    rw [expectation_ofVec_eq_re hu]
    simp only [u, map_smul, inner_smul_left, inner_smul_right, map_inv₀, Complex.conj_ofReal]
    rw [← mul_assoc, ← mul_inv, ← sq, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
      Complex.re_ofReal_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)),
      one_mul]
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left hc (sq_nonneg _)

/-- **Minimum uncertainty passes to the slices.** Let the linear maps `s r : 𝓗[ι] → 𝓗[γ]` split
the inner product, `⟪Ψ, Φ⟫ = ∑ r, ⟪s r Ψ, s r Φ⟫`, and carry `a'`, `b'`, `c'` to `a`, `b`, `c`. If
every unit vector of minimum uncertainty for `a`, `b` has `|⟨c⟩| ≤ v`, then every unit vector of
minimum uncertainty for `a'`, `b'` has `|⟨c'⟩| ≤ v`: each nonzero slice has minimum uncertainty,
and `⟨c'⟩` is the average of the slices weighted by their squared norms. -/
lemma abs_expectation_le_of_slices (s : R → 𝓗[ι] →ₗ[ℂ] 𝓗[γ])
    (hs : ∀ Ψ Φ, ⟪Ψ, Φ⟫_ℂ = ∑ r, ⟪s r Ψ, s r Φ⟫_ℂ)
    {a b c : Observable (𝓗[γ] →L[ℂ] 𝓗[γ])} {a' b' c' : Observable (𝓗[ι] →L[ℂ] 𝓗[ι])}
    (ha : ∀ r Ψ, s r ((a' : 𝓗[ι] →L[ℂ] 𝓗[ι]) Ψ) = (a : 𝓗[γ] →L[ℂ] 𝓗[γ]) (s r Ψ))
    (hb : ∀ r Ψ, s r ((b' : 𝓗[ι] →L[ℂ] 𝓗[ι]) Ψ) = (b : 𝓗[γ] →L[ℂ] 𝓗[γ]) (s r Ψ))
    (hc : ∀ r Ψ, s r ((c' : 𝓗[ι] →L[ℂ] 𝓗[ι]) Ψ) = (c : 𝓗[γ] →L[ℂ] 𝓗[γ]) (s r Ψ)) {v : ℝ}
    (hP : ∀ (u : 𝓗[γ]) (hu : ‖u‖ = 1), centeredGramDefect (ofVec hu) a b = 0 →
      |(ofVec hu)⟨c⟩| ≤ v)
    {Ψ : 𝓗[ι]} (hΨ : ‖Ψ‖ = 1) (h0 : centeredGramDefect (ofVec hΨ) a' b' = 0) :
    |(ofVec hΨ)⟨c'⟩| ≤ v := by
  rw [centeredGramDefect_ofVec] at h0
  obtain ⟨p, q, hpq, hrel⟩ := exists_smul_add_smul_eq_zero h0
  have hr (r : R) : p • ((a : 𝓗[γ] →L[ℂ] 𝓗[γ]) (s r Ψ) - ((ofVec hΨ)⟨a'⟩ : ℂ) • s r Ψ) +
      q • ((b : 𝓗[γ] →L[ℂ] 𝓗[γ]) (s r Ψ) - ((ofVec hΨ)⟨b'⟩ : ℂ) • s r Ψ) = 0 := by
    have := congrArg (s r) hrel
    simpa only [map_add, map_smul, map_sub, ha, hb, map_zero, ← Complex.coe_smul] using this
  have hsum : (ofVec hΨ)⟨c'⟩ = ∑ r, (⟪s r Ψ, (c : 𝓗[γ] →L[ℂ] 𝓗[γ]) (s r Ψ)⟫_ℂ).re := by
    rw [expectation_ofVec_eq_re, hs, Complex.re_sum]
    simp only [hc]
  have hnorm : ∑ r, ‖s r Ψ‖ ^ 2 = 1 := by
    simp only [@norm_sq_eq_re_inner ℂ]
    rw [← map_sum, ← hs, ← @norm_sq_eq_re_inner ℂ, hΨ, one_pow]
  calc |(ofVec hΨ)⟨c'⟩| ≤ ∑ r, ‖s r Ψ‖ ^ 2 * v := by
        rw [hsum]
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun r _ => abs_re_inner_le hP hpq (hr r))
    _ = v := by rw [← Finset.sum_mul, hnorm, one_mul]

/-- A bound on the minimum uncertainty vectors of the first coordinate holds for the minimum
uncertainty vectors of `𝓗[α × β]`, product vectors or not. -/
lemma abs_expectation_onFstObservable_le {a b c : Observable (𝓗[α] →L[ℂ] 𝓗[α])} {v : ℝ}
    (hP : ∀ (u : 𝓗[α]) (hu : ‖u‖ = 1), centeredGramDefect (ofVec hu) a b = 0 →
      |(ofVec hu)⟨c⟩| ≤ v)
    {Ψ : 𝓗[α × β]} (hΨ : ‖Ψ‖ = 1)
    (h0 : centeredGramDefect (ofVec hΨ) (onFstObservable a) (onFstObservable b) = 0) :
    |(ofVec hΨ)⟨onFstObservable c⟩| ≤ v :=
  abs_expectation_le_of_slices fstSlice inner_eq_sum_fstSlice (fun _ _ => fstSlice_onFst _ _ _)
    (fun _ _ => fstSlice_onFst _ _ _) (fun _ _ => fstSlice_onFst _ _ _) hP hΨ h0

/-- A bound on the minimum uncertainty vectors of the second coordinate holds for the minimum
uncertainty vectors of `𝓗[α × β]`. -/
lemma abs_expectation_onSndObservable_le {a b c : Observable (𝓗[β] →L[ℂ] 𝓗[β])} {v : ℝ}
    (hP : ∀ (u : 𝓗[β]) (hu : ‖u‖ = 1), centeredGramDefect (ofVec hu) a b = 0 →
      |(ofVec hu)⟨c⟩| ≤ v)
    {Ψ : 𝓗[α × β]} (hΨ : ‖Ψ‖ = 1)
    (h0 : centeredGramDefect (ofVec hΨ) (onSndObservable a) (onSndObservable b) = 0) :
    |(ofVec hΨ)⟨onSndObservable c⟩| ≤ v :=
  abs_expectation_le_of_slices sndSlice inner_eq_sum_sndSlice (fun _ _ => sndSlice_onSnd _ _ _)
    (fun _ _ => sndSlice_onSnd _ _ _) (fun _ _ => sndSlice_onSnd _ _ _) hP hΨ h0

end MinUncertainty

end FiniteHilbertSpace

end QuantumMechanics
