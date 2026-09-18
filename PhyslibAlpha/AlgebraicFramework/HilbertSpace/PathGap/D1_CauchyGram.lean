/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Complex.Norm

/-!
# D1 — Cauchy–Schwarz via the Gram defect

Purely algebraic kernel: for two vectors `x, y` in a complex
Hilbert space, the determinant of the Hermitian Gram matrix

`gramDefectC x y = ‖x‖² ‖y‖² − |⟨x,y⟩|²`

is never negative. That is, word for word, the Cauchy–Schwarz
inequality. Writing `⟨x,y⟩` in real and imaginary parts gives
the Robertson–Schrödinger inequality (`D2_Robertson.lean`)
as an algebraic consequence, not an additional postulate.
-/

@[expose] public section

noncomputable section

namespace ObstruccionGramUnificada

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Squared dispersion of a centered vector. -/
def varianceC (x : H) : ℝ := ‖x‖ ^ 2

/-- Determinant of the Hermitian Gram matrix of two vectors. -/
def gramDefectC (x y : H) : ℝ :=
  varianceC x * varianceC y - ‖@inner ℂ H _ x y‖ ^ 2

/-- The universal obstruction: the Gram determinant is never
negative. This IS the Cauchy–Schwarz inequality, rewritten as
positivity of a 2×2 determinant. -/
theorem gramDefectC_nonneg (x y : H) : 0 ≤ gramDefectC x y := by
  have hxy : ‖@inner ℂ H _ x y‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm x y
  have hleft : 0 ≤ ‖x‖ * ‖y‖ - ‖@inner ℂ H _ x y‖ := sub_nonneg.mpr hxy
  have hright : 0 ≤ ‖x‖ * ‖y‖ + ‖@inner ℂ H _ x y‖ :=
    add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  calc
    0 ≤ (‖x‖ * ‖y‖ - ‖@inner ℂ H _ x y‖) *
        (‖x‖ * ‖y‖ + ‖@inner ℂ H _ x y‖) := mul_nonneg hleft hright
    _ = gramDefectC x y := by simp [gramDefectC, varianceC, pow_two]; ring

/-- Saturating Cauchy–Schwarz amounts to zeroing
the Gram determinant, not the dispersions. -/
theorem gramDefectC_eq_zero_iff (x y : H) :
    gramDefectC x y = 0 ↔ ‖@inner ℂ H _ x y‖ = ‖x‖ * ‖y‖ := by
  have hxy : ‖@inner ℂ H _ x y‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm x y
  have hi : 0 ≤ ‖@inner ℂ H _ x y‖ := norm_nonneg _
  have hp : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  constructor
  · intro hzero
    simp only [gramDefectC, varianceC, pow_two] at hzero
    nlinarith
  · intro heq
    unfold gramDefectC varianceC
    rw [heq]
    ring

/-- Symmetric part of the inner product of the fluctuations. -/
def covarianceC (x y : H) : ℝ := (@inner ℂ H _ x y).re

/-- Real antisymmetric coordinate: for operator fluctuations
this is the real coordinate of the commutator expectation. -/
def commutatorCoordinateC (x y : H) : ℝ := 2 * (@inner ℂ H _ x y).im

/-- Robertson–Schrödinger is exactly Gram positivity
written in real and imaginary coordinates. -/
theorem robertsonSchrodinger_from_gram (x y : H) :
    covarianceC x y ^ 2 + (commutatorCoordinateC x y / 2) ^ 2 ≤
      varianceC x * varianceC y := by
  have hgram := gramDefectC_nonneg x y
  have hnorm :
      ‖@inner ℂ H _ x y‖ ^ 2 =
        (@inner ℂ H _ x y).re ^ 2 + (@inner ℂ H _ x y).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hbase : ‖@inner ℂ H _ x y‖ ^ 2 ≤ varianceC x * varianceC y :=
    sub_nonneg.mp hgram
  rw [hnorm] at hbase
  simpa [covarianceC, commutatorCoordinateC] using hbase

/-- Abstract Robertson–Schrödinger saturation. -/
def RSSaturated (x y : H) : Prop :=
  covarianceC x y ^ 2 + (commutatorCoordinateC x y / 2) ^ 2 =
    varianceC x * varianceC y

/-- Robertson–Schrödinger saturation is exactly
zero Gram defect. -/
theorem robertsonSchrodinger_saturated_iff_gram_zero (x y : H) :
    RSSaturated x y ↔ gramDefectC x y = 0 := by
  have hnorm :
      ‖@inner ℂ H _ x y‖ ^ 2 =
        (@inner ℂ H _ x y).re ^ 2 + (@inner ℂ H _ x y).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  simp only [RSSaturated, covarianceC, commutatorCoordinateC, gramDefectC]
  rw [show (2 * (@inner ℂ H _ x y).im / 2) ^ 2 =
      (@inner ℂ H _ x y).im ^ 2 by ring]
  rw [← hnorm]
  constructor <;> intro h <;> nlinarith

end ObstruccionGramUnificada
