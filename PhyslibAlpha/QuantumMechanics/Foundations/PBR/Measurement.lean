/-
Copyright (c) 2026 Brent Yee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brent Yee
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.OrthonormalMeasurement
public import PhyslibAlpha.QuantumMechanics.Foundations.PBR.Phases
public import PhyslibAlpha.QuantumMechanics.Foundations.PBR.QubitFrame
public import PhyslibAlpha.QuantumMechanics.HilbertSpaces.FiniteTarget.ProductState

/-!
# The PBR measurement

The entangled measurement on `n` copies used in the Pusey–Barrett–Rudolph (PBR) theorem.

## i. Overview

Let `F` be a qubit frame of two unit vectors `ψ 0`, `ψ 1`, with frame vectors `e 0`, `e 1` and
amplitudes `c`, `s`, and let `ω z` be unit phases indexed by `z : Fin n → Fin 2`. The product
frame vectors `E z = e (z 0) ⊗ ⋯ ⊗ e (z (n - 1))` (the vectors `piProdVec fun i => e (z i)`)
are orthonormal, and so are the measurement vectors
`b x = 2^{-n/2} ∑ z, conj (ω z) * walsh x z • E z`. If `∑ z, ω z * ∏ i, ![c, s] (z i) = 0`,
then `b x` is orthogonal to the product vector `Ψ x = ψ (x 0) ⊗ ⋯ ⊗ ψ (x (n - 1))`. Moreover
the components of every product vector `Ψ y` in the vectors `b x` have total squared norm one
(Parseval's identity), so `Ψ y` lies in the span of the vectors `b x`. The measurement
`Measurement.ofOrthonormal` in the orthonormal family `b` is therefore a measurement on `n`
copies whose outcome `x` has probability zero in the vector state of `Ψ x`.

## ii. Key results

- `PBR.QubitFrame.measurementVec` : the measurement vectors `b x`.
- `PBR.QubitFrame.orthonormal_measurementVec` : the measurement vectors are orthonormal.
- `PBR.QubitFrame.inner_measurementVec_piProdVec_self` : `b x` is orthogonal to `Ψ x`.
- `PBR.QubitFrame.sum_norm_sq_inner_measurementVec` : `∑ x, ‖⟪b x, Ψ y⟫_ℂ‖ ^ 2 = 1`.
- `PBR.exists_measurement` : the PBR measurement.

## iii. Table of contents

- A. The product frame vectors
- B. The measurement vectors
  - B.1. Definition
  - B.2. Orthonormality
  - B.3. Inner products with product vectors
- C. The PBR measurement

## iv. References

- M. F. Pusey, J. Barrett and T. Rudolph, *On the reality of the quantum state*,
  Nature Phys. 8, 475–478 (2012), arXiv:1111.3328. [ref: Pusey:2011de]

-/

@[expose] public section

noncomputable section

namespace QuantumMechanics.PBR

open InnerProductSpace ProbabilisticTheory UnitalPositiveLinearMap FiniteHilbertSpace

/-!
## A. The product frame vectors

-/

namespace QubitFrame

variable {d : Type*} [Fintype d] [DecidableEq d] {ψ : Fin 2 → 𝓗[d]} {n : ℕ}

/-- The product frame vector `E z = e (z 0) ⊗ ⋯ ⊗ e (z (n - 1))` on `n` copies. -/
def frameVec (F : QubitFrame ψ) (z : Fin n → Fin 2) : 𝓗[Fin n → d] :=
  piProdVec fun i => F.e (z i)

variable (F : QubitFrame ψ)

/-- The product frame vectors are orthonormal. -/
lemma inner_frameVec_frameVec (z z' : Fin n → Fin 2) :
    ⟪F.frameVec z, F.frameVec z'⟫_ℂ = if z = z' then 1 else 0 := by
  simp only [frameVec, inner_piProdVec, orthonormal_iff_ite.1 F.orthonormal_e,
    Finset.prod_boole, Finset.mem_univ, true_implies, funext_iff]

/-- The components of a product vector of the `ψ b` in the product frame. -/
lemma inner_frameVec_piProdVec (z x : Fin n → Fin 2) :
    ⟪F.frameVec z, piProdVec fun i => ψ (x i)⟫_ℂ =
      (∏ i, F.phase (x i)) * walsh z x * ∏ i, ![(F.c : ℂ), (F.s : ℂ)] (z i) := by
  simp only [frameVec, inner_piProdVec, F.inner_e_state, Finset.prod_mul_distrib, walsh_eq]

/-- Parseval's identity: the components of each product vector of the `ψ b` in the product frame
have total squared norm one, so the product vector lies in the span of the product frame. -/
lemma sum_norm_sq_inner_frameVec_piProdVec (y : Fin n → Fin 2) :
    ∑ z : Fin n → Fin 2, ‖⟪F.frameVec z, piProdVec fun i => ψ (y i)⟫_ℂ‖ ^ 2 = 1 := by
  simp only [frameVec, inner_piProdVec, norm_prod, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun i j => ‖⟪F.e j, ψ (y i)⟫_ℂ‖ ^ 2)]
  exact Finset.prod_eq_one fun i _ => F.sum_norm_sq_inner_e_state (y i)

/-!
## B. The measurement vectors

### B.1. Definition

-/

/-- The PBR measurement vector `b x = (√(2 ^ n))⁻¹ ∑ z, conj (ω z) * walsh x z • E z`. It is a
unit vector when the phases `ω z` have unit norm, see `orthonormal_measurementVec`. -/
def measurementVec (ω : (Fin n → Fin 2) → ℂ) (x : Fin n → Fin 2) : 𝓗[Fin n → d] :=
  ∑ z, ((Real.sqrt (2 ^ n))⁻¹ * starRingEnd ℂ (ω z) * walsh x z) • F.frameVec z

variable {ω : (Fin n → Fin 2) → ℂ}

/-- The inner product with a measurement vector is the corresponding combination of inner
products with the product frame vectors. -/
lemma inner_measurementVec (x : Fin n → Fin 2) (φ : 𝓗[Fin n → d]) :
    ⟪F.measurementVec ω x, φ⟫_ℂ =
      ∑ z, (Real.sqrt (2 ^ n))⁻¹ * ω z * walsh x z * ⟪F.frameVec z, φ⟫_ℂ := by
  rw [measurementVec, sum_inner]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [inner_smul_left, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_conj, conj_walsh]

/-!
### B.2. Orthonormality

-/

/-- The components of a measurement vector in the product frame. -/
lemma inner_frameVec_measurementVec (z y : Fin n → Fin 2) :
    ⟪F.frameVec z, F.measurementVec ω y⟫_ℂ =
      (Real.sqrt (2 ^ n))⁻¹ * starRingEnd ℂ (ω z) * walsh y z := by
  simp only [measurementVec, inner_sum, inner_smul_right, F.inner_frameVec_frameVec, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The PBR measurement vectors of unit phases are orthonormal. -/
lemma orthonormal_measurementVec (hω : ∀ z, ‖ω z‖ = 1) :
    Orthonormal ℂ (F.measurementVec ω) := by
  refine orthonormal_iff_ite.2 fun x y => ?_
  have hω' : ∀ z, ω z * starRingEnd ℂ (ω z) = 1 := fun z => by
    rw [Complex.mul_conj', hω]
    simp
  -- the Gram matrix of the `b x` is that of the orthonormal rescaled Walsh vectors
  rw [← orthonormal_iff_ite.1 orthonormal_walshVec x y, inner_measurementVec]
  simp only [inner_frameVec_measurementVec, PiLp.inner_apply, walshVec_apply, RCLike.inner_apply,
    map_mul, Complex.conj_ofReal, conj_walsh]
  refine Finset.sum_congr rfl fun z _ => ?_
  linear_combination
    ((((Real.sqrt (2 ^ n))⁻¹ : ℝ) : ℂ) ^ 2 * walsh x z * walsh y z) * hω' z

/-!
### B.3. Inner products with product vectors

-/

/-- If `∑ z, ω z * ∏ i, ![c, s] (z i) = 0`, the measurement vector `b x` is orthogonal to the
product vector `Ψ x = ψ (x 0) ⊗ ⋯ ⊗ ψ (x (n - 1))`. -/
lemma inner_measurementVec_piProdVec_self
    (hsum : ∑ z, ω z * ∏ i, ![(F.c : ℂ), (F.s : ℂ)] (z i) = 0) (x : Fin n → Fin 2) :
    ⟪F.measurementVec ω x, piProdVec fun i => ψ (x i)⟫_ℂ = 0 := by
  rw [inner_measurementVec]
  simp_rw [inner_frameVec_piProdVec]
  calc _ = ∑ z, ((Real.sqrt (2 ^ n))⁻¹ * ∏ i, F.phase (x i)) *
        (ω z * ∏ i, ![(F.c : ℂ), (F.s : ℂ)] (z i)) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [walsh_comm z x]
        linear_combination ((((Real.sqrt (2 ^ n))⁻¹ : ℝ) : ℂ) * (∏ i, F.phase (x i)) * ω z *
          ∏ i, ![(F.c : ℂ), (F.s : ℂ)] (z i)) * walsh_mul_self x z
    _ = 0 := by rw [← Finset.mul_sum, hsum, mul_zero]

/-- Parseval's identity for the PBR measurement: the components of every product vector
`Ψ y = ψ (y 0) ⊗ ⋯ ⊗ ψ (y (n - 1))` in the measurement vectors have total squared norm one, so
`Ψ y` lies in the span of the measurement vectors. -/
lemma sum_norm_sq_inner_measurementVec (hω : ∀ z, ‖ω z‖ = 1) (y : Fin n → Fin 2) :
    ∑ x, ‖⟪F.measurementVec ω x, piProdVec fun i => ψ (y i)⟫_ℂ‖ ^ 2 = 1 := by
  simp_rw [inner_measurementVec]
  calc _ = ∑ x : Fin n → Fin 2, ‖∑ z, (ω z * ⟪F.frameVec z, piProdVec fun i => ψ (y i)⟫_ℂ) *
        ((Real.sqrt (2 ^ n))⁻¹ * walsh x z)‖ ^ 2 :=
        Finset.sum_congr rfl fun x _ =>
          congrArg (‖·‖ ^ 2) (Finset.sum_congr rfl fun z _ => by ring)
    _ = ∑ z, ‖ω z * ⟪F.frameVec z, piProdVec fun i => ψ (y i)⟫_ℂ‖ ^ 2 :=
        sum_norm_sq_sum_mul_inv_sqrt_mul_walsh n _
    _ = 1 := by
        simp_rw [norm_mul, hω, one_mul]
        exact F.sum_norm_sq_inner_frameVec_piProdVec y

end QubitFrame

/-!
## C. The PBR measurement

-/

/-- The PBR measurement: for two unit vectors with different vector states there is a number of
copies `n` and a measurement on `n` copies whose outcome `x` has probability zero in the vector
state of the product vector `ψ (x 0) ⊗ ⋯ ⊗ ψ (x (n - 1))`. -/
lemma exists_measurement {d : Type*} [Fintype d] [DecidableEq d] (ψ : Fin 2 → 𝓗[d])
    (hψ : ∀ b, ‖ψ b‖ = 1) (h : ofVec (𝕜 := ℂ) (hψ 0) ≠ ofVec (𝕜 := ℂ) (hψ 1)) :
    ∃ (n : ℕ) (M : Measurement (Fin n → Fin 2)
        (Observable (𝓗[Fin n → d] →L[ℂ] 𝓗[Fin n → d]))), ∀ x : Fin n → Fin 2,
      (ofVec (norm_piProdVec_eq_one fun i => hψ (x i)))⟨M {x} (measurableSet_singleton x)⟩ =
        0 := by
  obtain ⟨F⟩ := exists_qubitFrame ψ hψ (norm_inner_lt_one_of_ofVec_ne (hψ 0) (hψ 1) h)
  obtain ⟨n, hn⟩ := exists_two_mul_pow_le F.c_pos F.s_pos
  obtain ⟨ω, hω, hsum⟩ := exists_phases F.c_pos F.s_pos.le F.s_le_c hn
  refine ⟨n, Measurement.ofOrthonormal (F.orthonormal_measurementVec hω) 0, fun x => ?_⟩
  -- the outcome `x` has probability `‖⟪b x, Ψ x⟫_ℂ‖ ^ 2 = 0`, plus `1 - 1` if `x = 0`
  rw [Measurement.expectation_ofOrthonormal_singleton,
    F.inner_measurementVec_piProdVec_self hsum, norm_zero, zero_pow two_ne_zero, zero_add,
    F.sum_norm_sq_inner_measurementVec hω, sub_self, ite_self]

end QuantumMechanics.PBR
