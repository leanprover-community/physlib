/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Physlib.SpaceAndTime.Space.Norm.Regularized
public import Physlib.SpaceAndTime.Space.Integrals.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
/-!

# The Hardy inequality

## i. Overview

For `d ≥ 3` and a Schwartz map `ψ` on `Space d`, the function `|ψ|²/‖x‖²` is integrable and
`∫ |ψ|²/‖x‖² ≤ (2/(d-2))² ∑ᵢ ∫ |∂ᵢψ|²`.

In quantum mechanics this bounds the Coulomb potential `1/‖x‖` by the kinetic energy, which is
the analytic input for the essential self-adjointness of the hydrogen Hamiltonian.

The proof uses the vector field `x/(‖x‖² + ε²)`, which is smooth of temperate growth. Integration
by parts against `ψ̄ ψ` relates its divergence `d/s - 2‖x‖²/s²` (with `s = ‖x‖² + ε²`) to the
derivatives of `ψ`, and a pointwise estimate `2ab ≤ ta² + b²/t` gives the inequality with
`‖x‖² + ε²` in place of `‖x‖²`. The limit `ε → 0` follows from Fatou's lemma.

## ii. Key results

- `Space.add_conj_integral_mul_deriv` : for real `g` of temperate growth,
  `z + conj z = -∫ (∂ᵢ g) |ψ|²` with `z = ∫ g ψ̄ ∂ᵢψ`.
- `Space.hardy_inequality_regularized` : the inequality with `‖x‖² + ε²`.
- `Space.hardy_inequality` : the Hardy inequality for `d ≥ 3`.

## iii. Table of contents

- A. The basic identity
- B. The regularized vector field
- C. The Hardy inequality

## iv. References

- M. Reed, B. Simon, *Methods of Modern Mathematical Physics II*, Section X.2.
- E. H. Lieb, M. Loss, *Analysis*, Section 2.20 (sharp Hardy constant).

-/

@[expose] public section

namespace Space

noncomputable section

open SchwartzMap Complex MeasureTheory

variable {d : ℕ}

/-!

## A. The basic identity

-/

/-- Identity behind the Hardy inequality: for real `g` of temperate growth,
`z + conj z = -∫ (∂ᵢ g) |ψ|²` with `z = ∫ g ψ̄ ∂ᵢψ`. -/
lemma add_conj_integral_mul_deriv (i : Fin d) {g : Space d → ℂ}
    (hg : g.HasTemperateGrowth) (hreal : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (ψ : 𝓢(Space d, ℂ)) :
    (∫ x, g x * (starRingEnd ℂ) (ψ x) * ∂[i] ψ x) +
      (starRingEnd ℂ) (∫ x, g x * (starRingEnd ℂ) (ψ x) * ∂[i] ψ x) =
      -∫ x, ∂[i] g x * ((‖ψ x‖ ^ 2 : ℝ) : ℂ) := by
  have hG : (fun x => g x * (starRingEnd ℂ) (ψ x)).HasTemperateGrowth :=
    hg.mul ψ.hasTemperateGrowth.conj
  have h1 := integral_mul_deriv_schwartzMap i hG ψ
  have hdG : ∀ x, ∂[i] (fun x => g x * (starRingEnd ℂ) (ψ x)) x =
      ∂[i] g x * (starRingEnd ℂ) (ψ x) + g x * (starRingEnd ℂ) (∂[i] ψ x) := by
    intro x
    have hc : DifferentiableAt ℝ (fun x => (starRingEnd ℂ) (ψ x)) x := by fun_prop
    rw [show (fun x => g x * (starRingEnd ℂ) (ψ x)) = g • fun x => (starRingEnd ℂ) (ψ x) from rfl,
      deriv_smul (hg.1.differentiable (by simp) x) hc, deriv_conj ψ.differentiableAt,
      smul_eq_mul, smul_eq_mul]
    ring
  have hdψ : (fun x => (starRingEnd ℂ) (∂[i] ψ x)).HasTemperateGrowth :=
    (SchwartzMap.hasTemperateGrowth
      (SchwartzMap.evalCLM ℝ (Space d) ℂ (basis i) (SchwartzMap.fderivCLM ℝ (Space d) ℂ ψ))).conj
  have hint1 : Integrable (fun x => ∂[i] g x * (starRingEnd ℂ) (ψ x) * ψ x) volume :=
    ((deriv_hasTemperateGrowth i hg).mul ψ.hasTemperateGrowth.conj).integrable_mul_schwartzMap ψ
  have hint2 : Integrable (fun x => g x * (starRingEnd ℂ) (∂[i] ψ x) * ψ x) volume :=
    (hg.mul hdψ).integrable_mul_schwartzMap ψ
  simp_rw [hdG, add_mul] at h1
  rw [integral_add hint1 hint2, neg_add] at h1
  have e1 : ∫ x, ∂[i] g x * (starRingEnd ℂ) (ψ x) * ψ x =
      ∫ x, ∂[i] g x * ((‖ψ x‖ ^ 2 : ℝ) : ℂ) := by
    congr 1 with x
    simp [mul_assoc, conj_mul']
  have e2 : ∫ x, g x * (starRingEnd ℂ) (∂[i] ψ x) * ψ x =
      ∫ x, (starRingEnd ℂ) (g x * (starRingEnd ℂ) (ψ x) * ∂[i] ψ x) := by
    congr 1 with x
    simp only [map_mul, hreal, conj_conj]
    ring
  rw [← integral_conj, h1, e1, e2]
  ring

/-!

## B. The regularized vector field

-/

lemma deriv_hardyField {ε : ℝ} (hε : ε ≠ 0) (i : Fin d) (x : Space d) :
    ∂[i] (fun x : Space d => x i * (‖x‖ ^ 2 + ε ^ 2)⁻¹) x =
      (‖x‖ ^ 2 + ε ^ 2)⁻¹ - 2 * x i ^ 2 * ((‖x‖ ^ 2 + ε ^ 2) ^ 2)⁻¹ := by
  set u := Units.mk0 ε hε
  have hf : (fun x : Space d => x i * (‖x‖ ^ 2 + ε ^ 2)⁻¹) =
      (fun x : Space d => x i) * normRegularizedPow d u (-2) := by
    funext y
    simp only [Pi.mul_apply, normRegularizedPow_neg_two, u, Units.val_mk0]
  have hc : HasFDerivAt (fun x : Space d => x i) (fderiv ℝ (fun x : Space d => x i) x) x :=
    (eval_differentiable i x).hasFDerivAt
  have hn : HasFDerivAt (normRegularizedPow d u (-2))
      (fderiv ℝ (normRegularizedPow d u (-2)) x) x :=
    ((normRegularizedPow_hasTemperateGrowth d u (-2)).1.differentiable (by simp) x).hasFDerivAt
  rw [hf, Space.deriv_eq, (hc.mul hn).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [← Space.deriv_eq, ← Space.deriv_eq, deriv_component_same, deriv_normRegularizedPow]
  have hq : 0 ≤ ‖x‖ ^ 2 + ε ^ 2 := by positivity
  simp only [normRegularizedPow, u, Units.val_mk0]
  rw [show ((-2 : ℝ) - 2) / 2 = -2 by norm_num, show (-2 : ℝ) / 2 = -1 by norm_num,
    Real.rpow_neg_one, Real.rpow_neg hq, Real.rpow_two]
  ring

lemma sum_deriv_hardyField {ε : ℝ} (hε : ε ≠ 0) (x : Space d) :
    ∑ i, ∂[i] (fun x : Space d => x i * (‖x‖ ^ 2 + ε ^ 2)⁻¹) x =
      d * (‖x‖ ^ 2 + ε ^ 2)⁻¹ - 2 * ‖x‖ ^ 2 * ((‖x‖ ^ 2 + ε ^ 2) ^ 2)⁻¹ := by
  simp only [deriv_hardyField hε]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← norm_sq_eq]


/-!

## C. The Hardy inequality

-/

/-- Bound for a single component of the regularized Hardy field. -/
lemma hardy_component_le {ε : ℝ} (hε : ε ≠ 0) (i : Fin d) (ψ : 𝓢(Space d, ℂ)) {t : ℝ}
    (ht : 0 < t) :
    ∫ x, ∂[i] (fun x : Space d => x i * (‖x‖ ^ 2 + ε ^ 2)⁻¹) x * ‖ψ x‖ ^ 2 ≤
      t * (∫ x, (x i * (‖x‖ ^ 2 + ε ^ 2)⁻¹) ^ 2 * ‖ψ x‖ ^ 2) +
        t⁻¹ * ∫ x, ‖∂[i] ψ x‖ ^ 2 := by
  have hgR : (fun x : Space d => x i * (‖x‖ ^ 2 + ε ^ 2)⁻¹).HasTemperateGrowth := by
    fun_prop (disch := exact hε)
  set g : Space d → ℝ := fun x => x i * (‖x‖ ^ 2 + ε ^ 2)⁻¹ with hg_def
  have hgC : (fun x => (g x : ℂ)).HasTemperateGrowth := by fun_prop
  have hid := add_conj_integral_mul_deriv i hgC (fun x => conj_ofReal _) ψ
  set z := ∫ x, ((g x : ℝ) : ℂ) * (starRingEnd ℂ) (ψ x) * ∂[i] ψ x with hz_def
  have hderiv : ∀ x, ∂[i] (fun x => ((g x : ℝ) : ℂ)) x = ((∂[i] g x : ℝ) : ℂ) :=
    fun x => deriv_ofReal (hgR.1.differentiable (by simp) x)
  have hint : ∫ x, ∂[i] (fun x => ((g x : ℝ) : ℂ)) x * ((‖ψ x‖ ^ 2 : ℝ) : ℂ) =
      ((∫ x, ∂[i] g x * ‖ψ x‖ ^ 2 : ℝ) : ℂ) := by
    simp [← integral_complex_ofReal, hderiv]
  rw [hint, Complex.add_conj] at hid
  have hz : ∫ x, ∂[i] g x * ‖ψ x‖ ^ 2 = -(2 * z.re) := by
    have h2 : ((∫ x, ∂[i] g x * ‖ψ x‖ ^ 2 : ℝ) : ℂ) = ((-(2 * z.re) : ℝ) : ℂ) := by
      push_cast at hid ⊢
      linear_combination hid
    exact_mod_cast h2
  rw [hz]
  -- integrability of the right-hand side
  set F : 𝓢(Space d, ℂ) := SchwartzMap.smulLeftCLM ℂ (fun x => ((g x : ℝ) : ℂ)) ψ with hF_def
  have hFx : ∀ x, ‖F x‖ ^ 2 = g x ^ 2 * ‖ψ x‖ ^ 2 := by
    intro x
    rw [hF_def, SchwartzMap.smulLeftCLM_apply_apply hgC, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs]
  have hiA : Integrable (fun x => g x ^ 2 * ‖ψ x‖ ^ 2) volume := by
    simpa only [hFx] using (F.memLp ((2 : ℕ) : ENNReal) volume).integrable_norm_pow two_ne_zero
  have hiB : Integrable (fun x => ‖∂[i] ψ x‖ ^ 2) volume :=
    (SchwartzMap.memLp (SchwartzMap.evalCLM ℝ (Space d) ℂ (basis i)
      (SchwartzMap.fderivCLM ℝ (Space d) ℂ ψ)) ((2 : ℕ) : ENNReal) volume).integrable_norm_pow
      two_ne_zero
  have hle : -(2 * z.re) ≤ ∫ x, (t * (g x ^ 2 * ‖ψ x‖ ^ 2) + t⁻¹ * ‖∂[i] ψ x‖ ^ 2) := by
    calc -(2 * z.re) ≤ 2 * ‖z‖ := by linarith [neg_abs_le z.re, Complex.abs_re_le_norm z]
      _ ≤ 2 * ∫ x, ‖((g x : ℝ) : ℂ) * (starRingEnd ℂ) (ψ x) * ∂[i] ψ x‖ := by
          gcongr
          exact norm_integral_le_integral_norm _
      _ = ∫ x, 2 * ‖((g x : ℝ) : ℂ) * (starRingEnd ℂ) (ψ x) * ∂[i] ψ x‖ :=
          (integral_const_mul _ _).symm
      _ ≤ ∫ x, (t * (g x ^ 2 * ‖ψ x‖ ^ 2) + t⁻¹ * ‖∂[i] ψ x‖ ^ 2) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
            ((hiA.const_mul t).add (hiB.const_mul t⁻¹)) (Filter.Eventually.of_forall fun x => ?_)
          dsimp only
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj]
          have := two_mul_le_add_mul_sq (a := |g x| * ‖ψ x‖) (b := ‖∂[i] ψ x‖) ht
          rw [mul_pow, sq_abs] at this
          linarith
  rw [integral_add (hiA.const_mul t) (hiB.const_mul t⁻¹), integral_const_mul,
    integral_const_mul] at hle
  simpa only [hg_def] using hle


lemma sum_sq_hardyField (ε : ℝ) (x : Space d) :
    ∑ i, (x i * (‖x‖ ^ 2 + ε ^ 2)⁻¹) ^ 2 = ‖x‖ ^ 2 * ((‖x‖ ^ 2 + ε ^ 2)⁻¹) ^ 2 := by
  simp [mul_pow, ← Finset.sum_mul, norm_sq_eq]

/-- **Regularized Hardy inequality** for `d ≥ 3`. -/
lemma hardy_inequality_regularized {ε : ℝ} (hε : ε ≠ 0) (hd : 3 ≤ d) (ψ : 𝓢(Space d, ℂ)) :
    ∫ x, (‖x‖ ^ 2 + ε ^ 2)⁻¹ * ‖ψ x‖ ^ 2 ≤
      4 / ((d : ℝ) - 2) ^ 2 * ∑ i, ∫ x, ‖∂[i] ψ x‖ ^ 2 := by
  have hd' : (0 : ℝ) < (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set t : ℝ := ((d : ℝ) - 2) / 2 with ht_def
  have ht : 0 < t := by positivity
  -- integrability of the pieces
  have hgR : ∀ i : Fin d, (fun x : Space d => x i * (‖x‖ ^ 2 + ε ^ 2)⁻¹).HasTemperateGrowth :=
    fun i => by fun_prop (disch := exact hε)
  have hI1 : ∀ i : Fin d, Integrable
      (fun x => ∂[i] (fun x : Space d => x i * (‖x‖ ^ 2 + ε ^ 2)⁻¹) x * ‖ψ x‖ ^ 2) volume :=
    fun i => (deriv_hasTemperateGrowth i (hgR i)).integrable_mul_norm_sq_schwartzMap ψ
  have hI2 : ∀ i : Fin d, Integrable
      (fun x => (x i * (‖x‖ ^ 2 + ε ^ 2)⁻¹) ^ 2 * ‖ψ x‖ ^ 2) volume :=
    fun i => ((hgR i).pow 2).integrable_mul_norm_sq_schwartzMap ψ
  have hIC : Integrable (fun x => (‖x‖ ^ 2 + ε ^ 2)⁻¹ * ‖ψ x‖ ^ 2) volume :=
    (inv_norm_sq_add_sq_hasTemperateGrowth hε).integrable_mul_norm_sq_schwartzMap ψ
  have hIA := integrable_finsetSum Finset.univ (fun i _ => hI1 i)
  have hIB := integrable_finsetSum Finset.univ (fun i _ => hI2 i)
  -- summed component bounds
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hardy_component_le hε i ψ ht)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← integral_finsetSum _ (fun i _ => hI1 i), ← integral_finsetSum _ (fun i _ => hI2 i)] at hsum
  set K := ∑ i, ∫ x, ‖∂[i] ψ x‖ ^ 2
  -- pointwise comparison
  have hpt : ∀ x : Space d, t * ((‖x‖ ^ 2 + ε ^ 2)⁻¹ * ‖ψ x‖ ^ 2) ≤
      (∑ i, ∂[i] (fun x : Space d => x i * (‖x‖ ^ 2 + ε ^ 2)⁻¹) x * ‖ψ x‖ ^ 2) -
        t * ∑ i, (x i * (‖x‖ ^ 2 + ε ^ 2)⁻¹) ^ 2 * ‖ψ x‖ ^ 2 := by
    intro x
    rw [← Finset.sum_mul, ← Finset.sum_mul, sum_deriv_hardyField hε, sum_sq_hardyField,
      ← inv_pow]
    set u := (‖x‖ ^ 2 + ε ^ 2)⁻¹ with hu
    set m := ‖ψ x‖ ^ 2
    have hs : 0 < ‖x‖ ^ 2 + ε ^ 2 := by positivity
    have hu0 : 0 < u := inv_pos.mpr hs
    have hρ : ‖x‖ ^ 2 * u ≤ 1 := by
      rw [hu, ← div_eq_mul_inv, div_le_one hs]
      nlinarith [sq_nonneg ε]
    have hρu : ‖x‖ ^ 2 * u ^ 2 ≤ u := by nlinarith
    have hm : 0 ≤ m := by positivity
    have key := mul_le_mul_of_nonneg_left hρu (by positivity : 0 ≤ (2 + t) * m)
    rw [ht_def] at key ⊢
    nlinarith [key, hm, hu0]
  have hint : ∫ x, t * ((‖x‖ ^ 2 + ε ^ 2)⁻¹ * ‖ψ x‖ ^ 2) ≤
      ∫ x, ((∑ i, ∂[i] (fun x : Space d => x i * (‖x‖ ^ 2 + ε ^ 2)⁻¹) x * ‖ψ x‖ ^ 2) -
        t * ∑ i, (x i * (‖x‖ ^ 2 + ε ^ 2)⁻¹) ^ 2 * ‖ψ x‖ ^ 2) :=
    integral_mono (hIC.const_mul t) (hIA.sub (hIB.const_mul t)) hpt
  rw [integral_sub hIA (hIB.const_mul _), integral_const_mul, integral_const_mul] at hint
  have h3 : t * ∫ x, (‖x‖ ^ 2 + ε ^ 2)⁻¹ * ‖ψ x‖ ^ 2 ≤ t⁻¹ * K := by linarith
  rw [← le_div_iff₀' ht] at h3
  calc ∫ x, (‖x‖ ^ 2 + ε ^ 2)⁻¹ * ‖ψ x‖ ^ 2 ≤ t⁻¹ * K / t := h3
    _ = 4 / ((d : ℝ) - 2) ^ 2 * K := by
      rw [ht_def]
      field_simp
      ring

open Filter Topology in
/-- **Hardy inequality** for `d ≥ 3`: `∫ |ψ|²/‖x‖² ≤ (2/(d-2))² ∑ᵢ ‖∂ᵢ ψ‖²`, together with the
integrability of `|ψ|²/‖x‖²`. -/
lemma hardy_inequality (hd : 3 ≤ d) (ψ : 𝓢(Space d, ℂ)) :
    Integrable (fun x => (‖x‖ ^ 2)⁻¹ * ‖ψ x‖ ^ 2) volume ∧
      ∫ x, (‖x‖ ^ 2)⁻¹ * ‖ψ x‖ ^ 2 ≤
        4 / ((d : ℝ) - 2) ^ 2 * ∑ i, ∫ x, ‖∂[i] ψ x‖ ^ 2 := by
  set C := 4 / ((d : ℝ) - 2) ^ 2 * ∑ i, ∫ x, ‖∂[i] ψ x‖ ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  have hε : ∀ n : ℕ, (1 / ((n : ℝ) + 1)) ≠ 0 := fun n => by positivity
  set F : ℕ → Space d → ENNReal := fun n x =>
    ENNReal.ofReal ((‖x‖ ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2)⁻¹ * ‖ψ x‖ ^ 2) with hF
  have hFm : ∀ n, Measurable (F n) := fun n => by fun_prop
  have hFb : ∀ n, ∫⁻ x, F n x ≤ ENNReal.ofReal C := by
    intro n
    have hI : Integrable (fun x => (‖x‖ ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2)⁻¹ * ‖ψ x‖ ^ 2) volume :=
      (inv_norm_sq_add_sq_hasTemperateGrowth (hε n)).integrable_mul_norm_sq_schwartzMap ψ
    show ∫⁻ x, ENNReal.ofReal ((‖x‖ ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2)⁻¹ * ‖ψ x‖ ^ 2) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun x => by positivity)]
    exact ENNReal.ofReal_le_ofReal (hardy_inequality_regularized (hε n) hd ψ)
  have hpt : ∀ x, ENNReal.ofReal ((‖x‖ ^ 2)⁻¹ * ‖ψ x‖ ^ 2) ≤ liminf (fun n => F n x) atTop := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp
    · have hx2 : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
      have h0 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
        rwa [zero_pow two_ne_zero] at this
      have ht : Tendsto (fun n => F n x) atTop
          (𝓝 (ENNReal.ofReal ((‖x‖ ^ 2)⁻¹ * ‖ψ x‖ ^ 2))) := by
        refine ENNReal.tendsto_ofReal (Tendsto.mul_const _ (Tendsto.inv₀ ?_ hx2))
        simpa using (tendsto_const_nhds (x := ‖x‖ ^ 2)).add h0
      exact ht.liminf_eq.ge
  have hlin : ∫⁻ x, ENNReal.ofReal ((‖x‖ ^ 2)⁻¹ * ‖ψ x‖ ^ 2) ≤ ENNReal.ofReal C :=
    calc _ ≤ ∫⁻ x, liminf (fun n => F n x) atTop := lintegral_mono hpt
      _ ≤ liminf (fun n => ∫⁻ x, F n x) atTop := lintegral_liminf_le hFm
      _ ≤ ENNReal.ofReal C := liminf_le_of_frequently_le' (Frequently.of_forall hFb)
  have hmeas : Measurable (fun x : Space d => (‖x‖ ^ 2)⁻¹ * ‖ψ x‖ ^ 2) := by fun_prop
  have hint : Integrable (fun x => (‖x‖ ^ 2)⁻¹ * ‖ψ x‖ ^ 2) volume :=
    ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (ae_of_all _ fun x => by positivity)).mpr (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => by positivity)
    hmeas.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hC0 hlin

end

end Space
