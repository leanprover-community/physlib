/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem, Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Statistics
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Lie
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.GNS

/-!

# Uncertainty relations

## i. Overview

A state gives the sesquilinear form `(x, y) ↦ ω(x⋆ y)`, which is the inner product of the GNS
vectors of `x` and `y`. Cauchy–Schwarz for it, applied to centered observables, gives the
Robertson–Schrödinger relation, and from it the Robertson relation `|ω⟨⁅a, b⁆⟩| ≤ σ_a σ_b` and the
bound on the covariance.

## ii. Key results

- `UnitalPositiveLinearMap.gns_cauchy_schwarz` : Cauchy–Schwarz for a state.
- `UnitalPositiveLinearMap.robertson_schrodinger` : **the Robertson–Schrödinger uncertainty
  relation.**
- `UnitalPositiveLinearMap.robertson` : **the Robertson uncertainty relation.**
- `UnitalPositiveLinearMap.covariance_cauchy_schwarz` : `|cov(a, b)| ≤ σ_a σ_b`.

## iii. Table of contents

- A. Cauchy–Schwarz
- B. Uncertainty relations
- C. Equality in the uncertainty relations
- D. Normalized variance bounds

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped ComplexOrder InnerProductSpace
open ContinuousLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped selfAdjoint

namespace UnitalPositiveLinearMap

omit [PartialOrder A] [StarOrderedRing A] in
/-- A real multiple of `1` commutes with everything: the algebraic fact making `commutator`
insensitive to shifting by a constant. -/
lemma smul_one_comm (r : ℝ) (x : A) : (r • (1 : A)) * x = x * (r • (1 : A)) := by
  rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

/-- The commutator only sees fluctuations, not means: centering `a` and `b` changes nothing about
how badly they fail to commute, since scalar multiples of `1` commute with everything and so
contribute nothing to `ab - ba`. -/
lemma bracket_centered (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    ⁅centered ω a, centered ω b⁆ = ⁅a, b⁆ := by
  apply Subtype.ext
  simp only [selfAdjoint.coe_bracket]
  congr 1
  show (centered ω a : A) * centered ω b - (centered ω b : A) * centered ω a =
      (a : A) * b - (b : A) * a
  simp only [centered, LinearMap.centered, AddSubgroup.coe_sub, selfAdjoint.val_smul,
    selfAdjoint.val_one, mul_sub, sub_mul]
  rw [smul_one_comm ((expectation ω).toLinearMap b) (a : A),
    smul_one_comm ((expectation ω).toLinearMap a) (b : A),
    smul_one_comm ((expectation ω).toLinearMap a)
      ((expectation ω).toLinearMap b • (1 : A))]
  abel

/-- The expectation of a raw product of two fluctuations splits into a real symmetric part
(covariance) and an imaginary antisymmetric part (the commutator's expectation). This is what
turns the Cauchy–Schwarz bound below into simultaneous control on covariance and commutator. -/
lemma apply_centered_mul_centered (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    ω ((centered ω a : A) * centered ω b) =
      (covariance ω a b : ℂ) + Complex.I * (ω⟨⁅a, b⁆⟩ : ℂ) := by
  set z := ω ((centered ω a : A) * centered ω b) with hz
  have hstar : ω ((centered ω b : A) * centered ω a) = star z := by
    rw [hz, apply_mul_comm_eq_star]
  have hsub : ω ((centered ω a : A) * centered ω b - (centered ω b : A) * centered ω a) =
      (2 * z.im : ℝ) * Complex.I := by
    rw [map_sub, hstar, ← hz, Complex.star_def, Complex.sub_conj]
  have hcomm : (ω⟨⁅a, b⁆⟩ : ℂ) = (z.im : ℂ) := by
    rw [← bracket_centered ω a b, ← apply_observable_eq_expectation, selfAdjoint.coe_bracket,
      map_smul, hsub, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    push_cast
    ring
  have hcov : covariance ω a b = z.re := by
    rw [covariance_eq_re_apply_centered_mul, hz]
  rw [hcomm, hcov, mul_comm, Complex.re_add_im]

/-! ## A. Cauchy–Schwarz -/

/-- `⟪π_ω(x) Ω_ω, π_ω(y) Ω_ω⟫ = ω(x⋆ y)`. -/
lemma inner_gnsRep_gnsCyclicVector_gnsRep_gnsCyclicVector (ω : 𝓢[ℂ, A]) (x y : A) :
    ⟪ω.gnsRep x ω.gnsCyclicVector, ω.gnsRep y ω.gnsCyclicVector⟫_ℂ = ω (star x * y) := by
  rw [← ω.inner_gnsCyclicVector_gnsRep_gnsCyclicVector (star x * y), map_mul,
    mul_apply_eq_comp, map_star ω.gnsRep, star_eq_adjoint, adjoint_inner_right]

/-- **Cauchy–Schwarz for a state**: `|ω(x⋆ y)|² ≤ ω(x⋆ x) ω(y⋆ y)`. -/
lemma gns_cauchy_schwarz (ω : 𝓢[ℂ, A]) (x y : A) :
    ‖ω (star x * y)‖ * ‖ω (star y * x)‖ ≤
      (ω (star x * x)).re * (ω (star y * y)).re := by
  have h := inner_mul_inner_self_le (𝕜 := ℂ)
    (ω.gnsRep x ω.gnsCyclicVector) (ω.gnsRep y ω.gnsCyclicVector)
  rwa [inner_gnsRep_gnsCyclicVector_gnsRep_gnsCyclicVector,
    inner_gnsRep_gnsCyclicVector_gnsRep_gnsCyclicVector,
    inner_gnsRep_gnsCyclicVector_gnsRep_gnsCyclicVector,
    inner_gnsRep_gnsCyclicVector_gnsRep_gnsCyclicVector] at h

/-- No state can correlate two fluctuations more strongly than the product of their spreads
allows — the GNS-Cauchy–Schwarz seed of every uncertainty relation below, before splitting the
left side via `apply_centered_mul_centered`. -/
lemma centered_gns_cauchy_schwarz (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    ‖ω ((centered ω a : A) * centered ω b)‖ *
        ‖ω ((centered ω b : A) * centered ω a)‖ ≤
      variance ω a * variance ω b := by
  rw [variance_eq_re_apply_centered_mul_self, variance_eq_re_apply_centered_mul_self]
  simpa only [(centered ω a).property.star_eq, (centered ω b).property.star_eq] using
    gns_cauchy_schwarz ω (centered ω a : A) (centered ω b : A)

/-- The squared-magnitude form of `centered_gns_cauchy_schwarz`, ready to be split via
`apply_centered_mul_centered` into `robertson_schrodinger`. -/
lemma centered_cauchy_schwarz (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    Complex.normSq (ω ((centered ω a : A) * centered ω b)) ≤
      variance ω a * variance ω b := by
  calc
    Complex.normSq (ω ((centered ω a : A) * centered ω b)) =
        ‖ω ((centered ω a : A) * centered ω b)‖ *
          ‖ω ((centered ω b : A) * centered ω a)‖ := by
      rw [apply_mul_comm_eq_star]
      simp [Complex.normSq_eq_norm_sq, pow_two]
    _ ≤ _ := centered_gns_cauchy_schwarz ω a b

/-! ## B. Uncertainty relations -/

/-- **The Robertson–Schrödinger uncertainty relation**, bounding the squared covariance plus the
squared expectation of the commutator by the product of the variances. -/
lemma robertson_schrodinger (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    covariance ω a b ^ 2 + ω⟨⁅a, b⁆⟩ ^ 2 ≤
      variance ω a * variance ω b := by
  have h := centered_cauchy_schwarz ω a b
  rw [apply_centered_mul_centered, Complex.normSq_apply] at h
  simpa [pow_two] using h

/-- Two observables cannot be more correlated than the product of their uncertainties allows —
the familiar `|correlation| ≤ σ_a · σ_b`, from dropping the commutator term in
`robertson_schrodinger`. -/
lemma covariance_cauchy_schwarz (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    covariance ω a b ^ 2 ≤ variance ω a * variance ω b := by
  nlinarith [robertson_schrodinger ω a b, sq_nonneg (ω⟨⁅a, b⁆⟩)]

/-- Heisenberg's uncertainty relation: observables that fail to commute cannot both be measured
with arbitrary precision. For position and momentum, `⁅x, p⁆ = iℏ` gives `ΔxΔp ≥ ℏ/2`. Obtained
from `robertson_schrodinger` by dropping the covariance term. -/
lemma robertson (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    ω⟨⁅a, b⁆⟩ ^ 2 ≤ variance ω a * variance ω b := by
  nlinarith [robertson_schrodinger ω a b, sq_nonneg (covariance ω a b)]

/-! ## C. Equality in the uncertainty relations -/

/-- The Cauchy–Schwarz defect of two centered observables, the slack in the Robertson–Schrödinger
relation. -/
noncomputable def centeredGramDefect (ω : 𝓢[ℂ, A]) (a b : Observable A) : ℝ :=
  variance ω a * variance ω b -
    Complex.normSq (ω ((centered ω a : A) * centered ω b))

/-- Positivity of the state makes the centered Gram defect nonnegative. -/
lemma centeredGramDefect_nonneg (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    0 ≤ centeredGramDefect ω a b :=
  sub_nonneg.mpr (centered_cauchy_schwarz ω a b)

/-- The squared centered pairing consists of squared covariance and squared
expectation of the observable Lie bracket. -/
lemma normSq_centered_pairing (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    Complex.normSq (ω ((centered ω a : A) * centered ω b)) =
      covariance ω a b ^ 2 + ω⟨⁅a, b⁆⟩ ^ 2 := by
  rw [apply_centered_mul_centered, Complex.normSq_apply]
  simp [pow_two]

/-- The slack in the Robertson relation is the Cauchy–Schwarz defect plus the squared covariance. -/
lemma robertson_gap_decomposition (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    variance ω a * variance ω b - ω⟨⁅a, b⁆⟩ ^ 2 =
      centeredGramDefect ω a b + covariance ω a b ^ 2 := by
  unfold centeredGramDefect
  rw [normSq_centered_pairing]
  ring

/-- Robertson–Schrödinger saturates exactly when the centered Gram defect vanishes. -/
lemma robertson_schrodinger_eq_iff_gram_zero (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    covariance ω a b ^ 2 + ω⟨⁅a, b⁆⟩ ^ 2 = variance ω a * variance ω b ↔
      centeredGramDefect ω a b = 0 := by
  unfold centeredGramDefect
  rw [normSq_centered_pairing]
  constructor <;> intro h <;> linarith

/-- Robertson saturates exactly when Cauchy–Schwarz saturates for the centered
pairing and the covariance is zero. Includes zero-variance cases without division. -/
lemma robertson_eq_iff_gram_zero_and_covariance_zero (ω : 𝓢[ℂ, A])
    (a b : Observable A) :
    ω⟨⁅a, b⁆⟩ ^ 2 = variance ω a * variance ω b ↔
      centeredGramDefect ω a b = 0 ∧ covariance ω a b = 0 := by
  have hgap := robertson_gap_decomposition ω a b
  have hgram := centeredGramDefect_nonneg ω a b
  have hcov := sq_nonneg (covariance ω a b)
  constructor
  · intro h
    have hc : covariance ω a b = 0 := by nlinarith
    exact ⟨by nlinarith, hc⟩
  · rintro ⟨hg, hc⟩
    rw [hg, hc] at hgap
    nlinarith

/-! ## D. Normalized variance bounds -/

/-- A raw commutator expectation of magnitude one yields the normalized variance
product bound for arbitrary states, with no extra positivity hypotheses. -/
lemma normalized_variance_product (ω : 𝓢[ℂ, A]) (a b : Observable A)
    (hnorm : ω⟨⁅a, b⁆⟩ ^ 2 = (1 : ℝ) / 4) :
    1 ≤ 4 * variance ω a * variance ω b := by
  have h := robertson ω a b
  rw [hnorm] at h
  nlinarith

/-- Normalization itself forces both variances to be positive. -/
lemma variances_pos_of_normalized_pairing (ω : 𝓢[ℂ, A]) (a b : Observable A)
    (hnorm : ω⟨⁅a, b⁆⟩ ^ 2 = (1 : ℝ) / 4) :
    0 < variance ω a ∧ 0 < variance ω b := by
  have h := normalized_variance_product ω a b hnorm
  have ha := variance_nonneg ω a
  have hb := variance_nonneg ω b
  constructor <;> by_contra! hn <;> nlinarith

end UnitalPositiveLinearMap

end ProbabilisticTheory
