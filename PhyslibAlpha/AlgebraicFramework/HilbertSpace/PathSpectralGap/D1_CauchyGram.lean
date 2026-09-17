/-
Copyright (c) 2026 Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Complex.Norm

@[expose] public section

/-!
# D1 — Cauchy–Schwarz vía el defecto de Gram

Núcleo puramente algebraico: para dos vectores `x, y` de un espacio de
Hilbert complejo, el determinante de la matriz de Gram hermitiana

`gramDefectC x y = ‖x‖² ‖y‖² − |⟨x,y⟩|²`

nunca es negativo. Esa es, palabra por palabra, la desigualdad de
Cauchy–Schwarz. Escribiendo `⟨x,y⟩` en sus partes real e imaginaria se
obtiene de inmediato la desigualdad de Robertson–Schrödinger (`D2_Robertson.lean`)
como consecuencia algebraica, no como postulado adicional.
-/

noncomputable section

namespace ObstruccionGramUnificada

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Cuadrado de la dispersión representada por un vector centrado. -/
def varianceC (x : H) : ℝ := ‖x‖ ^ 2

/-- Determinante de la matriz de Gram hermitiana de dos vectores. -/
def gramDefectC (x y : H) : ℝ :=
  varianceC x * varianceC y - ‖@inner ℂ H _ x y‖ ^ 2

/-- La obstrucción universal: el determinante de Gram nunca es negativo.
Esto ES la desigualdad de Cauchy–Schwarz, reescrita como positividad de un
determinante 2×2. -/
theorem gramDefectC_nonneg (x y : H) : 0 ≤ gramDefectC x y := by
  have hxy : ‖@inner ℂ H _ x y‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm x y
  have hleft : 0 ≤ ‖x‖ * ‖y‖ - ‖@inner ℂ H _ x y‖ := sub_nonneg.mpr hxy
  have hright : 0 ≤ ‖x‖ * ‖y‖ + ‖@inner ℂ H _ x y‖ :=
    add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  calc
    0 ≤ (‖x‖ * ‖y‖ - ‖@inner ℂ H _ x y‖) *
        (‖x‖ * ‖y‖ + ‖@inner ℂ H _ x y‖) := mul_nonneg hleft hright
    _ = gramDefectC x y := by simp [gramDefectC, varianceC, pow_two]; ring

/-- Saturar Cauchy–Schwarz equivale a anular, no las dispersiones, sino el
determinante de Gram. -/
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

/-- Parte simétrica del producto interno de las fluctuaciones. -/
def covarianceC (x y : H) : ℝ := (@inner ℂ H _ x y).re

/-- Coordenada antisimétrica real: para fluctuaciones operatoriales es la
coordenada real de la esperanza del conmutador. -/
def commutatorCoordinateC (x y : H) : ℝ := 2 * (@inner ℂ H _ x y).im

/-- Robertson–Schrödinger es exactamente la positividad de Gram escrita en
coordenadas real e imaginaria. -/
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

/-- Saturación Robertson–Schrödinger abstracta. -/
def RSSaturated (x y : H) : Prop :=
  covarianceC x y ^ 2 + (commutatorCoordinateC x y / 2) ^ 2 =
    varianceC x * varianceC y

/-- La saturación Robertson–Schrödinger es exactamente defecto de Gram cero. -/
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
