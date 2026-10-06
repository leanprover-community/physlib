/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem, Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Statistics
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Lie
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.GNS
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.PosDef

/-!

# Uncertainty relations

Cauchy–Schwarz for states and the Robertson and Robertson–Schrödinger uncertainty relations.

## i. Overview

A state gives the sesquilinear form `(x, y) ↦ ω(x⋆ y)`, which is the inner product of the GNS
vectors of `x` and `y`. Cauchy–Schwarz for it, applied to centered observables, gives the
Robertson–Schrödinger relation, and from it the Robertson relation `|ω⟨⁅a, b⁆⟩| ≤ σ_a σ_b` and the
bound on the covariance.

For a family of observables `a : ι → Observable A`, the covariance matrix `Σ` and the matrix `Ω`
of expectations of brackets give the matrix `Σ + iΩ` of GNS inner products of the centered
observables. It is a Gram matrix, and with its transpose `Σ − iΩ` it gives Robertson's relation
for several observables, `|det Ω| ≤ det Σ`.

## ii. Key results

- `UnitalPositiveLinearMap.gns_cauchy_schwarz` : Cauchy–Schwarz for a state.
- `UnitalPositiveLinearMap.robertson_schrodinger` : **the Robertson–Schrödinger uncertainty
  relation.**
- `UnitalPositiveLinearMap.robertson` : **the Robertson uncertainty relation.**
- `UnitalPositiveLinearMap.covariance_cauchy_schwarz` : `|cov(a, b)| ≤ σ_a σ_b`.
- `Matrix.PosDef.norm_det_le_re_det` : `‖det B‖ ≤ det A` when `A ± B` are positive semidefinite.
- `UnitalPositiveLinearMap.robertson_det` : **Robertson's uncertainty relation for several
  observables**, `|det Ω| ≤ det Σ`.

## iii. Table of contents

- A. Cauchy–Schwarz
- B. Uncertainty relations
- C. Equality in the uncertainty relations
- D. Normalized variance bounds
- E. A determinant bound for positive matrices
- F. Several observables

## iv. References

* None.

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

/-! ## E. A determinant bound for positive matrices -/

namespace Matrix

open scoped ComplexOrder
open Unitary Filter Topology

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix `T` with `T A Tᴴ = 1` for a positive definite `A`: the inverse square roots of the
eigenvalues of `A` times the adjoint of its eigenvector unitary. -/
noncomputable def PosDef.normalizer {A : Matrix n n ℂ} (hA : A.PosDef) : Matrix n n ℂ :=
  diagonal (fun i => ((Real.sqrt (hA.1.eigenvalues i))⁻¹ : ℂ)) *
    star (hA.1.eigenvectorUnitary : Matrix n n ℂ)

lemma PosDef.normalizer_mul_mul_conjTranspose {A : Matrix n n ℂ} (hA : A.PosDef) :
    hA.normalizer * A * hA.normalizerᴴ = 1 := by
  set U : Matrix n n ℂ := (hA.1.eigenvectorUnitary : Matrix n n ℂ)
  set α := hA.1.eigenvalues
  set D : Matrix n n ℂ := diagonal fun i => ((Real.sqrt (α i))⁻¹ : ℂ)
  have hUU : star U * U = 1 := coe_star_mul_self _
  have hAU : A = U * diagonal (fun i => (α i : ℂ)) * star U := by
    conv_lhs => rw [hA.1.spectral_theorem, conjStarAlgAut_apply]
    rfl
  have hDD : D * diagonal (fun i => (α i : ℂ)) * D = 1 := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    have hs : (Real.sqrt (α i) : ℂ) ^ 2 = α i := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (hA.eigenvalues_pos i).le]
    have hne : (Real.sqrt (α i) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (hA.eigenvalues_pos i)).ne'
    rw [← hs]
    field_simp
  have hT : hA.normalizer = D * star U := rfl
  have hTH : hA.normalizerᴴ = U * D := by
    simp [hT, D, conjTranspose_mul, diagonal_conjTranspose, Pi.star_def, star_eq_conjTranspose]
  rw [hTH, hT]
  rw [hAU]
  calc D * star U * (U * diagonal (fun i => (α i : ℂ)) * star U) * (U * D)
      = D * (star U * U) * diagonal (fun i => (α i : ℂ)) * (star U * U) * D := by
        simp only [mul_assoc]
    _ = 1 := by rw [hUU, mul_one, mul_one, hDD]

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
`‖det B‖ ≤ re (det A)`: conjugating by the normalizer of `A` puts `B` between `−1` and `1`. -/
lemma PosDef.norm_det_le_re_det {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.IsHermitian)
    (h₁ : (A - B).PosSemidef) (h₂ : (A + B).PosSemidef) : ‖B.det‖ ≤ (A.det).re := by
  set T := hA.normalizer
  have hT := hA.normalizer_mul_mul_conjTranspose
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
    refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => ?_
    rw [RCLike.norm_ofReal]
    exact hK.abs_eigenvalues_le_one hm hp i
  have hdetA : A.det = ((∏ i, hA.1.eigenvalues i : ℝ) : ℂ) := by
    rw [hA.1.det_eq_prod_eigenvalues]
    push_cast
    rfl
  have hprod : 0 < ∏ i, hA.1.eigenvalues i := Finset.prod_pos fun i _ => hA.eigenvalues_pos i
  have hBK : B.det = K.det * A.det := by
    have h := congrArg det hT
    rw [det_mul, det_mul, det_one] at h
    simp only [K, det_mul]
    linear_combination (-B.det) * h
  rw [hBK, norm_mul, hdetA, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hprod]
  nlinarith [norm_nonneg K.det]

omit [Fintype n] in
lemma map_ofReal_add_smul_one (S : Matrix n n ℝ) (ε : ℝ) :
    (S + ε • 1).map ((↑) : ℝ → ℂ) = S.map ((↑) : ℝ → ℂ) + (ε : ℂ) • 1 := by
  ext i j
  by_cases h : i = j <;> simp [h]

/-- For real `S` and `W`, if `S − iW` and `S + iW` are positive semidefinite then
`|det W| ≤ det S`. -/
lemma abs_det_le_det_of_posSemidef {S W : Matrix n n ℝ}
    (h₁ : (S.map ((↑) : ℝ → ℂ) - Complex.I • W.map ((↑) : ℝ → ℂ)).PosSemidef)
    (h₂ : (S.map ((↑) : ℝ → ℂ) + Complex.I • W.map ((↑) : ℝ → ℂ)).PosSemidef) :
    |W.det| ≤ S.det := by
  have hS : (S.map ((↑) : ℝ → ℂ)).PosSemidef := by
    have h := (h₁.add h₂).smul (Complex.zero_le_real.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2))
    convert h using 1
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    push_cast
    ring
  have hB : (Complex.I • W.map ((↑) : ℝ → ℂ)).IsHermitian := by
    rw [show Complex.I • W.map ((↑) : ℝ → ℂ) =
      S.map ((↑) : ℝ → ℂ) - (S.map ((↑) : ℝ → ℂ) - Complex.I • W.map ((↑) : ℝ → ℂ)) by abel]
    exact hS.1.sub h₁.1
  have key : ∀ ε : ℝ, 0 < ε → |W.det| ≤ (S + ε • 1).det := by
    intro ε hε
    have hε1 : ((ε : ℂ) • (1 : Matrix n n ℂ)).PosSemidef :=
      PosSemidef.one.smul (Complex.zero_le_real.mpr hε.le)
    have hA : ((S + ε • 1).map ((↑) : ℝ → ℂ)).PosDef := by
      rw [map_ofReal_add_smul_one]
      exact PosDef.posSemidef_add hS (PosDef.one.smul (Complex.zero_lt_real.mpr hε))
    have h₁' : ((S + ε • 1).map ((↑) : ℝ → ℂ) - Complex.I • W.map ((↑) : ℝ → ℂ)).PosSemidef := by
      rw [map_ofReal_add_smul_one, add_sub_right_comm]
      exact h₁.add hε1
    have h₂' : ((S + ε • 1).map ((↑) : ℝ → ℂ) + Complex.I • W.map ((↑) : ℝ → ℂ)).PosSemidef := by
      rw [map_ofReal_add_smul_one, add_right_comm]
      exact h₂.add hε1
    have h := hA.norm_det_le_re_det hB h₁' h₂'
    have hW : (W.map ((↑) : ℝ → ℂ)).det = (W.det : ℂ) := (RingHom.map_det Complex.ofRealHom W).symm
    have hSε : ((S + ε • 1).map ((↑) : ℝ → ℂ)).det = ((S + ε • 1).det : ℂ) :=
      (RingHom.map_det Complex.ofRealHom _).symm
    rwa [det_smul, hW, hSε, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re] at h
  have hlim : Tendsto (fun ε : ℝ => (S + ε • (1 : Matrix n n ℝ)).det) (𝓝[>] 0) (𝓝 S.det) := by
    have hc : Continuous fun ε : ℝ => (S + ε • (1 : Matrix n n ℝ)).det :=
      (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)

end Matrix

/-! ## F. Several observables -/

namespace ProbabilisticTheory

open scoped ComplexOrder InnerProductSpace selfAdjoint
open Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*}

namespace UnitalPositiveLinearMap

/-- The covariance matrix `Σ_jk = cov(a_j, a_k)` of a family of observables. -/
noncomputable def covarianceMatrix (ω : 𝓢[ℂ, A]) (a : ι → Observable A) : Matrix ι ι ℝ :=
  of fun j k => covariance ω (a j) (a k)

/-- The matrix `Ω_jk = ω⟨⁅a_j, a_k⁆⟩` of expectations of brackets of a family of observables. -/
noncomputable def bracketMatrix (ω : 𝓢[ℂ, A]) (a : ι → Observable A) : Matrix ι ι ℝ :=
  of fun j k => ω⟨⁅a j, a k⁆⟩

/-- The GNS vectors of the centered observables. -/
noncomputable def centeredGNSVector (ω : 𝓢[ℂ, A]) (a : Observable A) :=
  ω.gnsRep (centered ω a : A) ω.gnsCyclicVector

/-- `Σ + iΩ` is the Gram matrix of the GNS vectors of the centered observables. -/
lemma gram_centeredGNSVector (ω : 𝓢[ℂ, A]) (a : ι → Observable A) :
    gram ℂ (fun j => centeredGNSVector ω (a j)) =
      (covarianceMatrix ω a).map ((↑) : ℝ → ℂ) +
        Complex.I • (bracketMatrix ω a).map ((↑) : ℝ → ℂ) := by
  ext j k
  rw [gram, of_apply, centeredGNSVector, centeredGNSVector,
    inner_gnsRep_gnsCyclicVector_gnsRep_gnsCyclicVector, (centered ω (a j)).property.star_eq,
    apply_centered_mul_centered]
  simp [covarianceMatrix, bracketMatrix]

/-- `Σ − iΩ` is the transpose of the Gram matrix. -/
lemma transpose_gram_centeredGNSVector (ω : 𝓢[ℂ, A]) (a : ι → Observable A) :
    (gram ℂ (fun j => centeredGNSVector ω (a j)))ᵀ =
      (covarianceMatrix ω a).map ((↑) : ℝ → ℂ) -
        Complex.I • (bracketMatrix ω a).map ((↑) : ℝ → ℂ) := by
  ext j k
  rw [transpose_apply, gram, of_apply, ← inner_conj_symm, centeredGNSVector, centeredGNSVector,
    inner_gnsRep_gnsCyclicVector_gnsRep_gnsCyclicVector, (centered ω (a j)).property.star_eq,
    apply_centered_mul_centered]
  simp [covarianceMatrix, bracketMatrix, sub_eq_add_neg]

/-- **Robertson's uncertainty relation for several observables**: for every state and every
finite family of observables, `|det Ω| ≤ det Σ`. -/
theorem robertson_det [Fintype ι] [DecidableEq ι] (ω : 𝓢[ℂ, A]) (a : ι → Observable A) :
    |(bracketMatrix ω a).det| ≤ (covarianceMatrix ω a).det := by
  have hG := posSemidef_gram ℂ fun j => centeredGNSVector ω (a j)
  exact abs_det_le_det_of_posSemidef
    (by rw [← transpose_gram_centeredGNSVector]; exact hG.transpose)
    (by rw [← gram_centeredGNSVector]; exact hG)

end UnitalPositiveLinearMap

end ProbabilisticTheory
