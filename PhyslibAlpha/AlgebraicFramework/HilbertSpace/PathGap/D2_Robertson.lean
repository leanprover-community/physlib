/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathGap.D1_CauchyGram
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.IntervalCases

/-!
# D2 — The Robertson inequality (1929)

Abstract formalization of Robertson's (1929) inequality for a pair
of conjugate observables evaluated in a normalized Hilbert-space
state. Two forms are included: the classical linear form
(`Evaluacion`, with `|⟨[A,B]⟩|/2 ≤ σ_A σ_B`) and the quadratic
Robertson–Schrödinger form (`EvaluacionSchrodinger`, with
covariance).

Key point: the hypothesis `cota_cuadratica` required by
`EvaluacionSchrodinger` is **not postulated** — at the end of
this file (`ObstruccionGramUnificada.evaluacionSchrodingerDeGram`)
we prove that every pair of Hilbert-space vectors automatically
yields a valid `EvaluacionSchrodinger`, with the bound derived
from `D1_CauchyGram.gramDefectC_nonneg`. Cauchy–Schwarz ⇒ Gram ⇒
Robertson–Schrödinger, as a theorem, not an additional axiom.

Five elementary arithmetic lemmas (`Blindaje` / Shielding) used
later for cosine bounds and the Niven theorem (`D7_Niven.lean`)
are also included here.
-/

@[expose] public section

namespace Robertson1929

universe u

/-- Exact evaluation of Robertson's (1929) theorem for two conjugate
observables in a normalized Hilbert-space state. `sigmaA`, `sigmaB`
are the standard deviations; `mediaConmutador` is `⟨ψ,[A,B]ψ⟩`. -/
structure Evaluacion (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  /-- The normalized state in which the observables are evaluated. -/
  estado : H
  normalizado : ‖estado‖ = 1
  /-- Standard deviation of the first observable. -/
  sigmaA : ℝ
  /-- Standard deviation of the second observable. -/
  sigmaB : ℝ
  /-- Expectation value of the commutator. -/
  mediaConmutador : ℂ
  sigmaA_nonneg : 0 ≤ sigmaA
  sigmaB_nonneg : 0 ≤ sigmaB
  cota : ‖mediaConmutador‖ / 2 ≤ sigmaA * sigmaB

/-- Exact saturation of the Robertson bound for the given evaluation. -/
def Saturada {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (R : Evaluacion H) : Prop :=
  R.sigmaA * R.sigmaB = ‖R.mediaConmutador‖ / 2

/-- Maximal-tension evaluation: the normalized state realizes the
commutator norm, so Robertson's right-hand side is the tightest
among all normalized states. -/
structure MaximaTension (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] extends Evaluacion H where
  /-- Norm of the commutator realized by the maximal-tension state. -/
  normaConmutador : ℝ
  normaConmutador_nonneg : 0 ≤ normaConmutador
  realiza_norma :
    ‖toEvaluacion.mediaConmutador‖ = normaConmutador

/-- At maximal tension, Robertson yields the bound evaluated at the
commutator norm. -/
theorem MaximaTension.cota_por_norma
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (R : MaximaTension H) :
    R.normaConmutador / 2 ≤ R.sigmaA * R.sigmaB := by
  rw [← R.realiza_norma]
  exact R.cota

/-! ## Robertson–Schrödinger anchor: quadratic form -/

/-- Quadratic Robertson–Schrödinger evaluation: the dispersion product
dominates the quadratic floor composed of covariance and commutator. -/
structure EvaluacionSchrodinger where
  /-- Standard deviation of the first observable. -/
  sigmaA : ℝ
  /-- Standard deviation of the second observable. -/
  sigmaB : ℝ
  /-- Symmetric covariance contribution. -/
  covarianza : ℝ
  /-- Commutator contribution. -/
  conmutador : ℝ
  sigmaA_nonneg : 0 ≤ sigmaA
  sigmaB_nonneg : 0 ≤ sigmaB
  cota_cuadratica : covarianza ^ 2 + conmutador ^ 2 ≤ sigmaA ^ 2 * sigmaB ^ 2

/-- Robertson–Schrödinger floor: square root of the quadratic term. -/
noncomputable def pisoSchrodinger (S : EvaluacionSchrodinger) : ℝ :=
  Real.sqrt (S.covarianza ^ 2 + S.conmutador ^ 2)

/-- Exact Robertson–Schrödinger saturation. -/
def SaturadaSchrodinger (S : EvaluacionSchrodinger) : Prop :=
  S.sigmaA ^ 2 * S.sigmaB ^ 2 = S.covarianza ^ 2 + S.conmutador ^ 2

theorem saturadaSchrodinger_iff (S : EvaluacionSchrodinger) :
    SaturadaSchrodinger S ↔
      S.sigmaA ^ 2 * S.sigmaB ^ 2 =
        S.covarianza ^ 2 + S.conmutador ^ 2 := by
  rfl

/-- The Robertson–Schrödinger floor is positive iff the covariance or
the commutator is nonzero. -/
theorem pisoSchrodinger_pos_iff (S : EvaluacionSchrodinger) :
    0 < pisoSchrodinger S ↔ S.covarianza ≠ 0 ∨ S.conmutador ≠ 0 := by
  rw [pisoSchrodinger, Real.sqrt_pos]
  constructor
  · intro h
    by_contra hz
    push Not at hz
    simp [hz.1, hz.2] at h
  · rintro (hcov | hcomm)
    · nlinarith [sq_pos_of_ne_zero hcov, sq_nonneg S.conmutador]
    · nlinarith [sq_nonneg S.covarianza, sq_pos_of_ne_zero hcomm]

/-- The quadratic Robertson–Schrödinger bound implies the linear bound
on the nonnegative dispersion product. -/
theorem pisoSchrodinger_le_producto (S : EvaluacionSchrodinger) :
    pisoSchrodinger S ≤ S.sigmaA * S.sigmaB := by
  have hsum : 0 ≤ S.covarianza ^ 2 + S.conmutador ^ 2 := by positivity
  have hprod_nonneg : 0 ≤ S.sigmaA * S.sigmaB :=
    mul_nonneg S.sigmaA_nonneg S.sigmaB_nonneg
  have hsqrt_sq :
      pisoSchrodinger S ^ 2 = S.covarianza ^ 2 + S.conmutador ^ 2 := by
    simpa [pisoSchrodinger] using Real.sq_sqrt hsum
  have hprod_sq :
      S.sigmaA ^ 2 * S.sigmaB ^ 2 = (S.sigmaA * S.sigmaB) ^ 2 := by
    ring
  have hcota := S.cota_cuadratica
  rw [hprod_sq] at hcota
  nlinarith

/-- Clean anchor form: Robertson–Schrödinger yields a linear bound and
does not allow asserting the bound and its negation simultaneously. -/
theorem anclaSchrodinger_limpia (S : EvaluacionSchrodinger) :
    pisoSchrodinger S ≤ S.sigmaA * S.sigmaB ∧
    ¬ (pisoSchrodinger S ≤ S.sigmaA * S.sigmaB ∧
      ¬ pisoSchrodinger S ≤ S.sigmaA * S.sigmaB) := by
  refine ⟨pisoSchrodinger_le_producto S, ?_⟩
  intro h
  exact h.2 h.1

end Robertson1929

/-! ## Five elementary arithmetic lemmas (`Blindaje` / Shielding)

Used later by the Niven theorem (`D7_Niven.lean`): R3 bounds the
cosine for `d ≥ 5`; R5 is the arithmetic observation that a strictly
positive bound prevents either factor from vanishing. -/

open Real Finset

namespace Blindaje

/-- Term-by-term identity, exact over ℚ. -/
theorem R1b_termino (k : ℕ) (hk : 1 ≤ k) :
    (1 : ℚ) / k ^ 2 - 1 / (k * (k + 1)) = 1 / (k ^ 2 * (k + 1)) := by
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Exact telescoping: `Σ_{k=2..N} 1/(k(k+1)) = 1/2 − 1/(N+1)`. -/
theorem R1a_telescopio (N : ℕ) (hN : 2 ≤ N) :
    ∑ k ∈ Icc 2 N, (1 : ℚ) / (k * (k + 1)) = 1 / 2 - 1 / (N + 1) := by
  induction N with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · omega
      · simp
        norm_num
    · rw [Finset.sum_Icc_succ_top (by omega), ih h]
      have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
      have hn2 : ((n : ℚ) + 1 + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

theorem R1d_modo_positivo (k : ℕ) (hk : 2 ≤ k) :
    (0 : ℚ) < 1 / (k ^ 2 * (k + 1)) := by
  have : (0 : ℚ) < k := by exact_mod_cast (by omega : 0 < k)
  positivity

/-- If `(3+√5)/8 = 3/4` then `√5 = 3`, then `5 = 9`: absurd. -/
theorem R2_cinco_no_es_nueve : (3 + Real.sqrt 5) / 8 ≠ 3 / 4 := by
  intro h
  have h3 : Real.sqrt 5 = 3 := by linarith
  have h5 : (5 : ℝ) = 9 := by
    have := Real.sq_sqrt (by norm_num : (5:ℝ) ≥ 0)
    rw [h3] at this
    linarith [this]
  norm_num at h5

/-- Cosine ceiling: for `d ≥ 5`, `cos²(π/(d+1)) < (d−1)/4`. -/
theorem R3_techo_coseno (d : ℕ) (hd : 5 ≤ d) :
    Real.cos (π / (d + 1)) ^ 2 < (d - 1 : ℝ) / 4 := by
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hx_pos : 0 < π / ((d : ℝ) + 1) := by positivity
  have hd5 : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hcos_lt : Real.cos (π / (d + 1)) < 1 := by
    have hy : π / ((d : ℝ) + 1) ≤ π := by
      rw [div_le_iff₀ hd1]
      nlinarith [Real.pi_pos]
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hy hx_pos
    simpa using h
  have hcos_nonneg : 0 ≤ Real.cos (π / ((d : ℝ) + 1)) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · nlinarith [Real.pi_pos]
    · rw [div_le_iff₀ hd1]
      nlinarith [Real.pi_pos]
  have hcos_le : Real.cos (π / (d + 1)) ^ 2 < 1 := by
    nlinarith [hcos_nonneg, hcos_lt]
  have hfloor : (1 : ℝ) ≤ ((d : ℝ) - 1) / 4 := by
    have : (5 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  linarith

theorem R4a_siete_fracciones :
    (3 : ℚ) / 2 < ∑ k ∈ Finset.range 7, (1 : ℚ) / (k + 1) ^ 2 := by
  norm_num [Finset.sum_range_succ]

theorem R4_pi_mayor_que_tres : (3 : ℝ) < π := Real.pi_gt_three

/-- Arithmetic obstruction: if the bound `c` is strictly positive and
`c ≤ α·β`, then neither factor can vanish. -/
theorem R5_obstruccion_aritmetica (var_A var_B cota_robertson : ℝ)
    (h_robertson : cota_robertson ≤ var_A * var_B)
    (h_cota_positiva : 0 < cota_robertson) :
    var_A ≠ 0 ∧ var_B ≠ 0 := by
  constructor
  · intro hA
    rw [hA, zero_mul] at h_robertson
    linarith
  · intro hB
    rw [hB, mul_zero] at h_robertson
    linarith

end Blindaje

/-! ## Bridge closure: Cauchy–Schwarz ⇒ Robertson–Schrödinger -/

noncomputable section

namespace ObstruccionGramUnificada

/-- Bridge to `Robertson1929`: any pair of vectors in a complex Hilbert
space yields an `EvaluacionSchrodinger` whose quadratic bound is not
postulated — it is derived from the nonneg Gram defect
(`gramDefectC_nonneg`). The `cota_cuadratica` hypothesis required by
`Robertson1929.EvaluacionSchrodinger` is proved here. -/
def evaluacionSchrodingerDeGram {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (x y : H) :
    Robertson1929.EvaluacionSchrodinger where
  sigmaA := ‖x‖
  sigmaB := ‖y‖
  covarianza := covarianceC x y
  conmutador := commutatorCoordinateC x y / 2
  sigmaA_nonneg := norm_nonneg x
  sigmaB_nonneg := norm_nonneg y
  cota_cuadratica := by
    have h := robertsonSchrodinger_from_gram x y
    simpa [varianceC] using h

/-- The Robertson–Schrödinger floor of the Gram-constructed evaluation
is dominated by the norm product: the same conclusion as
`Robertson1929.pisoSchrodinger_le_producto`, instantiated on an
evaluation that is now a theorem, not an assumption. -/
theorem pisoSchrodinger_evaluacionSchrodingerDeGram_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x y : H) :
    Robertson1929.pisoSchrodinger (evaluacionSchrodingerDeGram x y) ≤ ‖x‖ * ‖y‖ := by
  have h := Robertson1929.pisoSchrodinger_le_producto (evaluacionSchrodingerDeGram x y)
  simpa [evaluacionSchrodingerDeGram] using h

end ObstruccionGramUnificada
