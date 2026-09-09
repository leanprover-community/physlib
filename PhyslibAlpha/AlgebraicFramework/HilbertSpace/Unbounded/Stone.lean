/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.SpectralIntegral.Construction
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.SpectralIntegral.SpecTheorem
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.StoneUnitaryGroup
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The scalar analytic kernel for Stone's theorem

This file contains estimates for the multiplier `exp (I * t r)`.  They are independent of a
particular operator or representation.  In particular, the derivative is taken in the real
parameter `t` with values in `ℂ`; the strong Hilbert-space theorem lifts this scalar statement
through the spectral integral, while the operator-algebra packaging lives in `Unbounded.Stone`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology InnerProductSpace Function

namespace QuantumMechanics.WOTSpectralMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma expFunction_hasDerivAt (r : ℝ) :
    HasDerivAt (fun t : ℝ => expFunction t r) (Complex.I * (r : ℂ)) 0 := by
  have harg : HasDerivAt (fun t : ℝ => t • ((r : ℂ) * Complex.I))
      ((r : ℂ) * Complex.I) 0 := by
      have h := HasDerivAt.smul_const (𝕜 := ℝ) (F := ℂ)
        (hasDerivAt_id' (𝕜 := ℝ) (0 : ℝ)) ((r : ℂ) * Complex.I)
      simpa only [one_smul] using h
  have harg' : HasDerivAt (fun t : ℝ => ((t * r : ℝ) : ℂ) * Complex.I)
      ((r : ℂ) * Complex.I) 0 := by
    convert harg using 1
    · funext t
      rw [Complex.real_smul]
      push_cast
      ring
  have hexp := _root_.Complex.hasDerivAt_exp (0 : ℂ)
  have hcomp := hexp.scomp_of_eq 0 harg' (by simp)
  have hfun : (fun t : ℝ => expFunction t r) =
      Complex.exp ∘ (fun t : ℝ => ((t * r : ℝ) : ℂ) * Complex.I) := by
    funext t
    unfold expFunction
    rfl
  have hcomp' : HasDerivAt (fun t : ℝ => expFunction t r)
      (((r : ℂ) * Complex.I) • (Complex.exp 0)) 0 :=
    hcomp.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun t => congrFun hfun t))
  convert hcomp' using 1
  rw [Complex.exp_zero, smul_eq_mul, mul_one]
  ring

lemma expFunction_slope_tendsto (r : ℝ) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (expFunction t r - expFunction 0 r))
      (𝓝[≠] (0 : ℝ)) (𝓝 (Complex.I * (r : ℂ))) := by
  simpa only [zero_add] using (expFunction_hasDerivAt r).tendsto_slope_zero

lemma expFunction_sub_one_norm_le (t r : ℝ) (ht : |t * r| ≤ 1) :
    ‖expFunction t r - 1‖ ≤ 2 * |t * r| := by
  unfold expFunction
  have harg : ‖((t * r : ℝ) : ℂ) * Complex.I‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using ht
  simpa [Complex.norm_real, Real.norm_eq_abs] using
    (Complex.norm_exp_sub_one_le harg)

@[nolint unusedArguments]
lemma expFunction_slope_norm_le {t r : ℝ} (ht : t ≠ 0) (_htsmall : |t| ≤ 1) :
    ‖t⁻¹ • (expFunction t r - 1)‖ ≤ 2 * |r| := by
  have ht' : 0 < |t| := abs_pos.mpr ht
  by_cases hsmall : |t * r| ≤ 1
  · have hmain := expFunction_sub_one_norm_le t r hsmall
    rw [norm_smul, Real.norm_eq_abs, abs_inv]
    have htr : |t * r| = |t| * |r| := by rw [abs_mul]
    rw [htr] at hmain
    calc
      |t|⁻¹ * ‖expFunction t r - 1‖ ≤ |t|⁻¹ * (2 * (|t| * |r|)) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = 2 * |r| := by field_simp
  · have hlarge : 1 < |t * r| := lt_of_not_ge hsmall
    have htwo : ‖expFunction t r - 1‖ ≤ 2 := by
      calc
        ‖expFunction t r - 1‖ ≤ ‖expFunction t r‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [expFunction_modulus]; norm_num
    rw [norm_smul, Real.norm_eq_abs, abs_inv]
    have htr : |t * r| = |t| * |r| := by rw [abs_mul]
    rw [htr] at hlarge
    have hle : |t|⁻¹ ≤ |r| := by
      rw [← one_div]
      apply (div_le_iff₀ ht').2
      rw [mul_comm] at hlarge
      exact le_of_lt hlarge
    calc
      |t|⁻¹ * ‖expFunction t r - 1‖ ≤ |t|⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left htwo (by positivity)
      _ ≤ |r| * 2 := mul_le_mul_of_nonneg_right hle (by positivity)
      _ = 2 * |r| := by ring

lemma expFunction_slope_sub_derivative_norm_le {t r : ℝ} (ht : t ≠ 0)
    (htsmall : |t| ≤ 1) :
    ‖t⁻¹ • (expFunction t r - 1) - Complex.I * (r : ℂ)‖ ≤ 3 * |r| := by
  calc
    ‖t⁻¹ • (expFunction t r - 1) - Complex.I * (r : ℂ)‖ ≤
        ‖t⁻¹ • (expFunction t r - 1)‖ + ‖Complex.I * (r : ℂ)‖ := norm_sub_le _ _
    _ ≤ 2 * |r| + |r| := by
      gcongr
      · exact expFunction_slope_norm_le ht htsmall
      · simp [Complex.norm_real]
    _ = 3 * |r| := by ring

/-- The difference quotient `t⁻¹(exp(itr) - 1)` of `expFunction`. -/
def expSlope (t r : ℝ) : ℂ :=
  t⁻¹ • (expFunction t r - 1)

lemma expSlope_measurable (t : ℝ) : Measurable (expSlope t) := by
  unfold expSlope
  exact (measurable_const : Measurable (fun _ : ℝ => (t⁻¹ : ℝ))).smul
    ((expFunction_measurable t).sub measurable_const)

lemma expSlope_tendsto (r : ℝ) :
    Filter.Tendsto (fun t : ℝ => expSlope t r) (𝓝[≠] (0 : ℝ))
      (𝓝 (Complex.I * (r : ℂ))) := by
  simpa [expSlope, expFunction] using expFunction_slope_tendsto r

lemma expSlope_sub_derivative_measurable (t : ℝ) :
    Measurable (fun r : ℝ => expSlope t r - Complex.I * (r : ℂ)) := by
  exact (expSlope_measurable t).sub
    (measurable_const.mul Complex.measurable_ofReal)

lemma expSlope_sub_derivative_norm_le {t r : ℝ} (ht : t ≠ 0)
    (htsmall : |t| ≤ 1) :
    ‖expSlope t r - Complex.I * (r : ℂ)‖ ≤ 3 * |r| := by
  exact expFunction_slope_sub_derivative_norm_le ht htsmall

lemma vectorMeasure_expSlope_sub_derivative_tendsto
    {μ : MeasureTheory.VectorMeasure ℝ ℂ} (hxi : μ.Integrable id) :
    Filter.Tendsto
      (fun t : ℝ => ∫ᵛ r, expSlope t r - Complex.I * (r : ℂ) ∂[
        ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); μ])
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  let ν : Measure ℝ := μ.variation
  have hnorm : Integrable (fun r : ℝ => |r|) ν := by
    simpa [ν, Real.norm_eq_abs] using hxi.norm
  have hbound : Integrable (fun r : ℝ => 3 * |r|) ν := by
    simpa only [smul_eq_mul] using hnorm.const_mul 3
  have hmeas : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      AEStronglyMeasurable (fun r : ℝ => expSlope t r - Complex.I * (r : ℂ)) ν := by
    filter_upwards [] with t
    exact (expSlope_sub_derivative_measurable t).aestronglyMeasurable
  have hdom : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      ∀ᵐ r : ℝ ∂ν, ‖expSlope t r - Complex.I * (r : ℂ)‖ ≤ 3 * |r| := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1)] with t ht htnz
    filter_upwards [] with r
    have htsmall : |t| ≤ 1 := by
      rw [abs_le]
      exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    exact expSlope_sub_derivative_norm_le htnz
      htsmall
  have hlim : ∀ᵐ r : ℝ ∂ν,
      Filter.Tendsto (fun t : ℝ => expSlope t r - Complex.I * (r : ℂ))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    filter_upwards [] with r
    simpa using (expSlope_tendsto r).sub
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℝ => Complex.I * (r : ℂ)) (𝓝[≠] (0 : ℝ))
        (𝓝 (Complex.I * (r : ℂ))))
  simpa using
    (MeasureTheory.VectorMeasure.tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (B := ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ))
      (fun r : ℝ => 3 * |r|) hmeas hdom hbound hlim)

lemma maximalSpectralIntegral_inner_eq_complexWeakIntegral
    (μS : WOTSpectralMeasure ℝ H) (x : H)
    (hx : x ∈ (maximalSpectralIntegral μS).domain) (y : H)
    (hfi : (μS.scalarMeasure x y).Integrable id) :
    ⟪y, (maximalSpectralIntegral μS) ⟨x, hx⟩⟫_ℂ =
      μS.complexWeakIntegral (fun r : ℝ => (r : ℂ)) x y := by
  have hmax := maximalSpectralIntegral_weak_truncation_reconstruction μS x hx y
  have hlim := truncationIntegral_inner_tendsto_complexWeakIntegral μS x y hfi
  exact tendsto_nhds_unique hmax hlim

lemma expIntegral_inner_slope_tendsto_complexWeakIntegral
    (μS : WOTSpectralMeasure ℝ H) (x y : H)
    (hfi : (μS.scalarMeasure x y).Integrable id) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ •
        (⟪y, expIntegral μS t x⟫_ℂ - ⟪y, x⟫_ℂ))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (μS.complexWeakIntegral (fun r : ℝ => Complex.I * (r : ℂ)) x y)) := by
  let ν := μS.scalarMeasure x y
  let := scalarMeasure_isFiniteVariation μS x y
  have hreal : ν.Integrable id := hfi
  have hone : ν.Integrable (fun _ : ℝ => (1 : ℂ)) := by
    exact MeasureTheory.integrable_const 1
  have habs : ν.Integrable (fun r : ℝ => |r|) := by
    simpa only [Function.id_def, Real.norm_eq_abs] using hreal.norm
  have hcomplex : ν.Integrable (fun r : ℝ => (r : ℂ)) := hreal.ofReal
  have htarget : ν.Integrable (fun r : ℝ => Complex.I * (r : ℂ)) := by
    exact hcomplex.const_mul Complex.I
  have hzero :
      μS.complexWeakIntegral (fun r : ℝ => Complex.I * (r : ℂ)) x y =
        ∫ᵛ r, Complex.I * (r : ℂ) ∂[
          ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν] := rfl
  rw [hzero]
  have hDCT := vectorMeasure_expSlope_sub_derivative_tendsto (μ := ν) hreal
  have hquot : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      t⁻¹ • (⟪y, expIntegral μS t x⟫_ℂ - ⟪y, x⟫_ℂ) -
          ∫ᵛ r, Complex.I * (r : ℂ) ∂[
            ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν] =
        ∫ᵛ r, expSlope t r - Complex.I * (r : ℂ) ∂[
          ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν] := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1)] with t ht htnz
    have htsmall : |t| ≤ 1 := by
      rw [abs_le]
      exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hslope : ν.Integrable (expSlope t) := by
      apply Integrable.mono' (habs.const_mul (2 : ℝ))
      · exact (expSlope_measurable t).aestronglyMeasurable
      · filter_upwards [] with r
        simpa [expSlope, norm_smul, Real.norm_eq_abs] using
          (expFunction_slope_norm_le (r := r) htnz htsmall)
    have hexpint : ν.Integrable (expFunction t) := by
      apply Integrable.of_bound (expFunction_measurable t).aestronglyMeasurable 1
      filter_upwards [] with r
      rw [expFunction_modulus]
    have hExp := boundedIntegral_inner μS (expFunction_measurable t)
      (expFunction_bounded t) x y (scalarMeasure_isFiniteVariation μS x y)
    have hOne := boundedIntegral_inner μS (f := fun _ : ℝ => (1 : ℂ)) measurable_const
      (⟨(1 : ℝ), fun _ => by norm_num⟩) x y
        (scalarMeasure_isFiniteVariation μS x y)
    have hExp' : ⟪y, expIntegral μS t x⟫_ℂ =
        ∫ᵛ r, expFunction t r ∂[
          ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν] := by
      exact hExp
    have hOne' : ⟪y, x⟫_ℂ =
        ∫ᵛ r, (1 : ℂ) ∂[
          ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν] := by
      rw [← hOne]
      simp [boundedIntegral_const]
    rw [hExp', hOne']
    have hExpSmul := MeasureTheory.VectorMeasure.integral_smul
      (expFunction t) ν (ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ)) t⁻¹
    have hOneSmul := MeasureTheory.VectorMeasure.integral_smul
      (fun _ : ℝ => (1 : ℂ)) ν
      (ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ)) t⁻¹
    have hExpS : ν.Integrable (fun r : ℝ => t⁻¹ • expFunction t r) :=
      hexpint.smul t⁻¹
    have hOneS : ν.Integrable (fun _ : ℝ => t⁻¹ • (1 : ℂ)) :=
      hone.smul t⁻¹
    have hExpSmul' :
        (∫ᵛ r, t⁻¹ • expFunction t r ∂[
          ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν]) =
          t⁻¹ • ∫ᵛ r, expFunction t r ∂[
            ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν] := by
      simpa only [Pi.smul_apply] using hExpSmul
    have hOneSmul' :
        (∫ᵛ r, t⁻¹ • (1 : ℂ) ∂[
          ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν]) =
          t⁻¹ • ∫ᵛ r, (1 : ℂ) ∂[
            ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν] := by
      simpa only [Pi.smul_apply] using hOneSmul
    have hsubInt :
        (∫ᵛ r, t⁻¹ • expFunction t r ∂[
          ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν]) -
          ∫ᵛ r, t⁻¹ • (1 : ℂ) ∂[
            ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν] =
        ∫ᵛ r, (t⁻¹ • expFunction t r - t⁻¹ • (1 : ℂ)) ∂[
          ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν] := by
      simpa only [Pi.sub_apply] using
        (MeasureTheory.VectorMeasure.integral_sub hExpS hOneS).symm
    have hfinalInt :
        (∫ᵛ r, (t⁻¹ • expFunction t r - t⁻¹ • (1 : ℂ)) ∂[
          ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν]) -
          ∫ᵛ r, Complex.I * (r : ℂ) ∂[
            ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν] =
        ∫ᵛ r, (t⁻¹ • expFunction t r - t⁻¹ • (1 : ℂ)) -
            Complex.I * (r : ℂ) ∂[
          ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν] := by
      simpa only [Pi.sub_apply] using
        (MeasureTheory.VectorMeasure.integral_sub (hExpS.sub hOneS) htarget).symm
    calc
      t⁻¹ • (∫ᵛ r, expFunction t r ∂[
          ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν] -
          ∫ᵛ r, (1 : ℂ) ∂[
            ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν]) -
          ∫ᵛ r, Complex.I * (r : ℂ) ∂[
            ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν] =
        (t⁻¹ • ∫ᵛ r, expFunction t r ∂[
          ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν] -
          t⁻¹ • ∫ᵛ r, (1 : ℂ) ∂[
            ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν]) -
          ∫ᵛ r, Complex.I * (r : ℂ) ∂[
            ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν] := by rw [smul_sub]
      _ = (∫ᵛ r, t⁻¹ • expFunction t r ∂[
          ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν] -
          ∫ᵛ r, t⁻¹ • (1 : ℂ) ∂[
            ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν]) -
          ∫ᵛ r, Complex.I * (r : ℂ) ∂[
            ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν] := by
        rw [hExpSmul', hOneSmul']
      _ = (∫ᵛ r, (t⁻¹ • expFunction t r - t⁻¹ • (1 : ℂ)) ∂[
          ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν]) -
          ∫ᵛ r, Complex.I * (r : ℂ) ∂[
            ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν] := by
        exact congrArg (fun z : ℂ => z -
          ∫ᵛ r, Complex.I * (r : ℂ) ∂[
            ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν]) hsubInt
      _ = ∫ᵛ r, expSlope t r - Complex.I * (r : ℂ) ∂[
          ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν] := by
        rw [hfinalInt]
        congr 1
        funext r
        simp [expSlope]
        ring
  have hdiff_tendsto : Filter.Tendsto
      (fun t : ℝ =>
        t⁻¹ • (⟪y, expIntegral μS t x⟫_ℂ - ⟪y, x⟫_ℂ) -
          ∫ᵛ r, Complex.I * (r : ℂ) ∂[
            ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν])
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    exact hDCT.congr' (hquot.mono fun _ h => h.symm)
  have hadd := hdiff_tendsto.add (tendsto_const_nhds :
    Filter.Tendsto (fun _ : ℝ => ∫ᵛ r, Complex.I * (r : ℂ) ∂[
      ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν])
      (𝓝[≠] (0 : ℝ)) (𝓝 (∫ᵛ r, Complex.I * (r : ℂ) ∂[
        ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν])))
  simpa [sub_add_cancel] using hadd

lemma boundedIntegral_sub_maximal_norm_sq
    (μS : WOTSpectralMeasure ℝ H) {g : ℝ → ℂ} (hg : Measurable g)
    (hgb : ∃ C : ℝ, ∀ r, ‖g r‖ ≤ C)
    (x : H) (hx : x ∈ (maximalSpectralIntegral μS).domain) :
    ENNReal.ofReal (‖boundedIntegral μS g hg hgb x -
      Complex.I • (maximalSpectralIntegral μS) ⟨x, hx⟩‖ ^ 2) =
      ∫⁻ r, ENNReal.ofReal (‖g r - Complex.I * (r : ℂ)‖ ^ 2)
        ∂μS.diagonalMeasure x := by
  rcases hgb with ⟨C, hC⟩
  have hC0 : 0 ≤ C := by
    exact (norm_nonneg (g 0)).trans (hC 0)
  let μ := μS.diagonalMeasure x
  have hdom : Integrable (fun r : ℝ => r ^ 2) μ := by
    exact hx
  have hbound : Integrable (fun r : ℝ => 2 * C ^ 2 + 2 * r ^ 2) μ := by
    have hconst : Integrable (fun _ : ℝ => 2 * C ^ 2) μ :=
      MeasureTheory.integrable_const _
    exact hconst.add (hdom.const_mul 2)
  have hfin : (∫⁻ r, ENNReal.ofReal (2 * C ^ 2 + 2 * r ^ 2) ∂μ) ≠ ⊤ :=
    (hbound.lintegral_lt_top).ne
  let F : ℕ → ℝ → ENNReal := fun n r =>
    ENNReal.ofReal (‖g r - Complex.I * truncationFunction n r‖ ^ 2)
  let F₀ : ℝ → ENNReal := fun r =>
    ENNReal.ofReal (‖g r - Complex.I * (r : ℂ)‖ ^ 2)
  have hFmeas : ∀ n, Measurable (F n) := by
    intro n
    exact ENNReal.continuous_ofReal.measurable.comp
      ((hg.sub ((measurable_const.mul (truncationFunction_measurable n)))).norm.pow_const 2)
  have hFbound : ∀ n, ∀ᵐ r ∂μ, F n r ≤
      ENNReal.ofReal (2 * C ^ 2 + 2 * r ^ 2) := by
    intro n
    filter_upwards [] with r
    dsimp [F]
    apply ENNReal.ofReal_le_ofReal
    have htrunc : ‖truncationFunction n r‖ ≤ |r| := by
      by_cases hr : r ∈ spectralCutoffSet n
      · change r ∈ Set.Icc (-(n : ℝ)) (n : ℝ) at hr
        rw [truncationFunction, indicator_of_mem hr, Complex.norm_real, Real.norm_eq_abs]
      · change r ∉ Set.Icc (-(n : ℝ)) (n : ℝ) at hr
        simp [truncationFunction, hr]
    have hnorm : ‖g r - Complex.I * truncationFunction n r‖ ≤ C + |r| := by
      calc
        _ ≤ ‖g r‖ + ‖Complex.I * truncationFunction n r‖ := norm_sub_le _ _
        _ = ‖g r‖ + ‖truncationFunction n r‖ := by simp
        _ ≤ C + |r| := add_le_add (hC r) htrunc
    have hsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
    nlinarith [sq_nonneg (C - |r|), sq_abs r]
  have hFlim : ∀ᵐ r ∂μ, Filter.Tendsto (fun n : ℕ => F n r)
      Filter.atTop (𝓝 (F₀ r)) := by
    filter_upwards [] with r
    have htrunc := truncationFunction_tendsto r
    have hdiff : Filter.Tendsto
        (fun n : ℕ => g r - Complex.I * truncationFunction n r)
        Filter.atTop (𝓝 (g r - Complex.I * (r : ℂ))) := by
      exact tendsto_const_nhds.sub (tendsto_const_nhds.mul htrunc)
    have hnorm : Filter.Tendsto
        (fun n : ℕ => ‖g r - Complex.I * truncationFunction n r‖ ^ 2)
        Filter.atTop (𝓝 (‖g r - Complex.I * (r : ℂ)‖ ^ 2)) :=
      (continuous_norm.pow 2).continuousAt.tendsto.comp hdiff
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hnorm
  have hlin : Filter.Tendsto (fun n : ℕ => ∫⁻ r, F n r ∂μ)
      Filter.atTop (𝓝 (∫⁻ r, F₀ r ∂μ)) :=
    MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence
      (fun r : ℝ => ENNReal.ofReal (2 * C ^ 2 + 2 * r ^ 2))
      (by filter_upwards [] with n; exact hFmeas n)
      (by filter_upwards [] with n; exact hFbound n) hfin hFlim
  have hvec : Filter.Tendsto
      (fun n : ℕ => boundedIntegral μS g hg ⟨C, hC⟩ x -
        Complex.I • truncationIntegral μS n x)
      Filter.atTop (𝓝 (boundedIntegral μS g hg ⟨C, hC⟩ x -
        Complex.I • (maximalSpectralIntegral μS) ⟨x, hx⟩)) := by
    have htr := truncationLimit_tendsto μS (⟨x, hx⟩ : spectralSquareMomentSubmodule μS)
    have hsub := (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => boundedIntegral μS g hg ⟨C, hC⟩ x)
        Filter.atTop (𝓝 (boundedIntegral μS g hg ⟨C, hC⟩ x))).sub
      (htr.const_smul Complex.I)
    simpa [maximalSpectralIntegral, truncationLimit] using hsub
  have hnorm : Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal (‖boundedIntegral μS g hg ⟨C, hC⟩ x -
        Complex.I • truncationIntegral μS n x‖ ^ 2))
      Filter.atTop (𝓝 (ENNReal.ofReal (‖boundedIntegral μS g hg ⟨C, hC⟩ x -
        Complex.I • (maximalSpectralIntegral μS) ⟨x, hx⟩‖ ^ 2))) := by
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((continuous_norm.pow 2).continuousAt.tendsto.comp hvec)
  have hnormsq : ∀ n : ℕ,
      ENNReal.ofReal (‖boundedIntegral μS g hg ⟨C, hC⟩ x -
        Complex.I • truncationIntegral μS n x‖ ^ 2) =
      ∫⁻ r, F n r ∂μ := by
    intro n
    let gn : ℝ → ℂ := fun r => Complex.I * truncationFunction n r
    have hgn : Measurable gn := by
      exact measurable_const.mul (truncationFunction_measurable n)
    have hgnbound : ∀ r, ‖gn r‖ ≤ (n : ℝ) := by
      intro r
      dsimp [gn]
      rw [norm_mul, Complex.norm_I, one_mul]
      by_cases hr : r ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
      · rw [truncationFunction, indicator_of_mem hr, Complex.norm_real, Real.norm_eq_abs]
        exact abs_le.mpr hr
      · simp [truncationFunction, hr]
    have hgnb : ∃ K : ℝ, ∀ r, ‖gn r‖ ≤ K := ⟨n, hgnbound⟩
    have hdifff : Measurable (g - gn) := hg.sub hgn
    have hdiffb : ∃ K : ℝ, ∀ r, ‖(g - gn) r‖ ≤ K := by
      refine ⟨C + n, fun r => ?_⟩
      exact (norm_sub_le _ _).trans
        (add_le_add (hC r) (hgnbound r))
    have hsubop := boundedIntegral_sub μS hg hgn ⟨C, hC⟩ hgnb
    have hsmul := boundedIntegral_smul μS Complex.I
      (truncationFunction_measurable n) (truncationFunction_bounded n)
    have hsmulx : boundedIntegral μS gn hgn hgnb x =
        Complex.I • truncationIntegral μS n x := by
      have h := congrArg (fun A : H →WOT[ℂ] H => A x) hsmul
      simpa [gn, truncationIntegral] using h
    have hdiffEq : boundedIntegral μS (g - gn) hdifff hdiffb x =
        boundedIntegral μS g hg ⟨C, hC⟩ x -
          Complex.I • truncationIntegral μS n x := by
      have h := congrArg (fun A : H →WOT[ℂ] H => A x) hsubop
      have h' : boundedIntegral μS (g - gn) hdifff hdiffb x =
          boundedIntegral μS g hg ⟨C, hC⟩ x -
            boundedIntegral μS gn hgn hgnb x := by
        simpa using h
      rw [hsmulx] at h'
      exact h'
    have hnorm0 := boundedIntegral_norm_sq μS hdifff hdiffb x
    rw [← hdiffEq]
    simpa [F, μ, gn] using hnorm0
  have hlin' : Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal (‖boundedIntegral μS g hg ⟨C, hC⟩ x -
        Complex.I • truncationIntegral μS n x‖ ^ 2))
      Filter.atTop (𝓝 (∫⁻ r, F₀ r ∂μ)) := by
    apply hlin.congr'
    filter_upwards [] with n
    rw [hnormsq n]
  exact tendsto_nhds_unique hnorm hlin'

lemma expIntegral_slope_eq_boundedIntegral
    (μS : WOTSpectralMeasure ℝ H) (t : ℝ) (x : H)
    (hgb : ∃ C : ℝ, ∀ r, ‖expSlope t r‖ ≤ C) :
    t⁻¹ • (expIntegral μS t x - x) =
      boundedIntegral μS (expSlope t) (expSlope_measurable t) hgb x := by
  have hdiffb : ∃ C : ℝ, ∀ r, ‖(expFunction t - (fun _ : ℝ => (1 : ℂ))) r‖ ≤ C := by
    refine ⟨2, fun r => ?_⟩
    calc
      ‖(expFunction t - (fun _ : ℝ => (1 : ℂ))) r‖ =
          ‖expFunction t r - 1‖ := by rfl
      _ ≤ ‖expFunction t r‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [expFunction_modulus]; norm_num
  have hdiff := boundedIntegral_sub μS (f := expFunction t)
    (g := fun _ : ℝ => (1 : ℂ)) (expFunction_measurable t) measurable_const
    (expFunction_bounded t) (⟨1, fun _ => by norm_num⟩)
  have hscale := boundedIntegral_smul μS (t⁻¹ : ℂ)
    ((expFunction_measurable t).sub measurable_const) hdiffb
  have hscale' : boundedIntegral μS (expSlope t) (expSlope_measurable t) hgb x =
      (t⁻¹ : ℂ) •
        boundedIntegral μS (expFunction t - (fun _ : ℝ => (1 : ℂ)))
          ((expFunction_measurable t).sub measurable_const) hdiffb x := by
    have hfun : (fun r : ℝ => expSlope t r) =
        (fun r : ℝ => (t⁻¹ : ℂ) * (expFunction t r - (1 : ℂ))) := by
      funext r
      simp [expSlope]
    have h := congrArg (fun A : H →WOT[ℂ] H => A x) hscale
    simpa [hfun, expSlope, smul_eq_mul] using h
  have hdiff' : boundedIntegral μS (expFunction t - (fun _ : ℝ => (1 : ℂ)))
        ((expFunction_measurable t).sub measurable_const) hdiffb x =
      expIntegral μS t x - x := by
    have h := congrArg (fun A : H →WOT[ℂ] H => A x) hdiff
    simpa [expIntegral, boundedIntegral_const] using h
  rw [hscale', hdiff']
  rw [← Complex.ofReal_inv]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) (E := H) t⁻¹
    (expIntegral μS t x - x)

lemma expIntegral_strong_slope_tendsto
    (μS : WOTSpectralMeasure ℝ H) (x : H)
    (hx : x ∈ (maximalSpectralIntegral μS).domain) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (expIntegral μS t x - x))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (Complex.I • (maximalSpectralIntegral μS) ⟨x, hx⟩)) := by
  have hqeq : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      t⁻¹ • (expIntegral μS t x - x) =
        boundedIntegral μS (expSlope t) (expSlope_measurable t)
          (by
            refine ⟨2 * |t|⁻¹, fun r => ?_⟩
            rw [expSlope, norm_smul, Real.norm_eq_abs, abs_inv]
            calc
              |t|⁻¹ * ‖expFunction t r - 1‖ ≤ |t|⁻¹ * 2 :=
                mul_le_mul_of_nonneg_left
                  (by
                    calc
                      ‖expFunction t r - 1‖ ≤ ‖expFunction t r‖ + ‖(1 : ℂ)‖ :=
                        norm_sub_le _ _
                      _ = 2 := by rw [expFunction_modulus]; norm_num)
                  (by positivity)
              _ = 2 * |t|⁻¹ := by ring)
          x := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1)] with t ht htnz
    let hgb : ∃ C : ℝ, ∀ r, ‖expSlope t r‖ ≤ C := by
      refine ⟨2 * |t|⁻¹, fun r => ?_⟩
      rw [expSlope, norm_smul, Real.norm_eq_abs, abs_inv]
      calc
        |t|⁻¹ * ‖expFunction t r - 1‖ ≤ |t|⁻¹ * 2 :=
          mul_le_mul_of_nonneg_left
            (by
              calc
                ‖expFunction t r - 1‖ ≤ ‖expFunction t r‖ + ‖(1 : ℂ)‖ :=
                  norm_sub_le _ _
                _ = 2 := by rw [expFunction_modulus]; norm_num)
            (by positivity)
        _ = 2 * |t|⁻¹ := by ring
    have hdiffb : ∃ C : ℝ, ∀ r, ‖(expFunction t - (fun _ : ℝ => (1 : ℂ))) r‖ ≤ C := by
      refine ⟨2, fun r => ?_⟩
      calc
        ‖(expFunction t - (fun _ : ℝ => (1 : ℂ))) r‖ =
            ‖expFunction t r - 1‖ := by rfl
        _ ≤ ‖expFunction t r‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [expFunction_modulus]; norm_num
    have hdiff := boundedIntegral_sub μS (f := expFunction t)
      (g := fun _ : ℝ => (1 : ℂ)) (expFunction_measurable t) measurable_const
      (expFunction_bounded t) (⟨1, fun _ => by norm_num⟩)
    have hscale := boundedIntegral_smul μS (t⁻¹ : ℂ)
      ((expFunction_measurable t).sub measurable_const) hdiffb
    have hscale' : boundedIntegral μS (expSlope t) (expSlope_measurable t) hgb x =
        (t⁻¹ : ℂ) •
          boundedIntegral μS (expFunction t - (fun _ : ℝ => (1 : ℂ)))
            ((expFunction_measurable t).sub measurable_const) hdiffb x := by
      have hfun : (fun r : ℝ => expSlope t r) =
          (fun r : ℝ => (t⁻¹ : ℂ) *
            (expFunction t r - (1 : ℂ))) := by
        funext r
        simp [expSlope]
      have h := congrArg (fun A : H →WOT[ℂ] H => A x) hscale
      simpa [hfun, expSlope, smul_eq_mul] using h
    have hdiff' : boundedIntegral μS (expFunction t - (fun _ : ℝ => (1 : ℂ)))
          ((expFunction_measurable t).sub measurable_const) hdiffb x =
        expIntegral μS t x - x := by
      have h := congrArg (fun A : H →WOT[ℂ] H => A x) hdiff
      simpa [expIntegral, boundedIntegral_const] using h
    rw [hscale', hdiff']
    rw [← Complex.ofReal_inv]
    exact RCLike.real_smul_eq_coe_smul (K := ℂ) (E := H) t⁻¹
      (expIntegral μS t x - x)
  have hnormsq : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      ENNReal.ofReal (‖t⁻¹ • (expIntegral μS t x - x) -
        Complex.I • (maximalSpectralIntegral μS) ⟨x, hx⟩‖ ^ 2) =
        ∫⁻ r, ENNReal.ofReal (‖expSlope t r - Complex.I * (r : ℂ)‖ ^ 2)
          ∂μS.diagonalMeasure x := by
    filter_upwards [hqeq] with t hq
    rw [hq]
    exact boundedIntegral_sub_maximal_norm_sq μS
      (expSlope_measurable t)
      (by
        refine ⟨2 * |t|⁻¹, fun r => ?_⟩
        rw [expSlope, norm_smul, Real.norm_eq_abs, abs_inv]
        calc
          |t|⁻¹ * ‖expFunction t r - 1‖ ≤ |t|⁻¹ * 2 :=
            mul_le_mul_of_nonneg_left
              (by
                calc
                  ‖expFunction t r - 1‖ ≤ ‖expFunction t r‖ + ‖(1 : ℂ)‖ :=
                    norm_sub_le _ _
                  _ = 2 := by rw [expFunction_modulus]; norm_num)
              (by positivity)
          _ = 2 * |t|⁻¹ := by ring)
      x hx
  let μ := μS.diagonalMeasure x
  let G : ℝ → ℝ → ENNReal := fun t r =>
    ENNReal.ofReal (‖expSlope t r - Complex.I * (r : ℂ)‖ ^ 2)
  let G₀ : ℝ → ENNReal := fun _ => 0
  have hdom : Integrable (fun r : ℝ => r ^ 2) μ := hx
  have hbound : Integrable (fun r : ℝ => 9 * r ^ 2) μ := hdom.const_mul 9
  have hfin : (∫⁻ r, ENNReal.ofReal (9 * r ^ 2) ∂μ) ≠ ⊤ :=
    (hbound.lintegral_lt_top).ne
  have hGmeas : ∀ t : ℝ, Measurable (G t) := by
    intro t
    exact ENNReal.continuous_ofReal.measurable.comp
      ((expSlope_sub_derivative_measurable t).norm.pow_const 2)
  have hGbound : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), ∀ᵐ r ∂μ, G t r ≤
      ENNReal.ofReal (9 * r ^ 2) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1)] with t ht htnz
    filter_upwards [] with r
    dsimp [G]
    apply ENNReal.ofReal_le_ofReal
    have htsmall : |t| ≤ 1 := by
      rw [abs_le]
      exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hpoint := expFunction_slope_sub_derivative_norm_le
      (r := r) htnz htsmall
    have hpoint' : ‖expSlope t r - Complex.I * (r : ℂ)‖ ≤ 3 * |r| := by
      simpa [expSlope] using hpoint
    have hsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hpoint'
    nlinarith [sq_abs r]
  have hGlim : ∀ᵐ r ∂μ, Filter.Tendsto (fun t : ℝ => G t r)
      (𝓝[≠] (0 : ℝ)) (𝓝 (G₀ r)) := by
    filter_upwards [] with r
    have hdiff : Filter.Tendsto
        (fun t : ℝ => expSlope t r - Complex.I * (r : ℂ))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      simpa using (expSlope_tendsto r).sub
        (tendsto_const_nhds : Filter.Tendsto
          (fun _ : ℝ => Complex.I * (r : ℂ)) (𝓝[≠] (0 : ℝ))
          (𝓝 (Complex.I * (r : ℂ))))
    have hnorm : Filter.Tendsto
        (fun t : ℝ => ‖expSlope t r - Complex.I * (r : ℂ)‖ ^ 2)
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 ^ 2)) := by
        simpa [Function.comp_def] using
          ((continuous_norm.pow 2).continuousAt.tendsto.comp hdiff)
    simpa [G, G₀, Function.comp_def] using
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hnorm)
  have hGint : Filter.Tendsto (fun t : ℝ => ∫⁻ r, G t r ∂μ)
      (𝓝[≠] (0 : ℝ)) (𝓝 (∫⁻ r, G₀ r ∂μ)) :=
    MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence
      (fun r : ℝ => ENNReal.ofReal (9 * r ^ 2))
      (by filter_upwards [] with t; exact hGmeas t)
      (by filter_upwards [hGbound] with t ht; exact ht) hfin hGlim
  have henergy : Filter.Tendsto
      (fun t : ℝ => ENNReal.ofReal (‖t⁻¹ • (expIntegral μS t x - x) -
        Complex.I • (maximalSpectralIntegral μS) ⟨x, hx⟩‖ ^ 2))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have hGint' : Filter.Tendsto (fun t : ℝ => ∫⁻ r, G t r ∂μ)
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      simpa [G₀, μ] using hGint
    exact hGint'.congr' (hnormsq.mono fun _ h => h.symm)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hevent := henergy.eventually
    (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hεsq))
  filter_upwards [hevent] with t ht
  have ht' : ENNReal.ofReal
      (‖t⁻¹ • (expIntegral μS t x - x) -
        Complex.I • (maximalSpectralIntegral μS) ⟨x, hx⟩‖ ^ 2) <
      ENNReal.ofReal (ε ^ 2) := by
    simpa using ht
  have hsq : ‖t⁻¹ • (expIntegral μS t x - x) -
      Complex.I • (maximalSpectralIntegral μS) ⟨x, hx⟩‖ ^ 2 < ε ^ 2 := by
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp ht'
  have hnormlt : ‖t⁻¹ • (expIntegral μS t x - x) -
      Complex.I • (maximalSpectralIntegral μS) ⟨x, hx⟩‖ < ε :=
    (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hε)).mp hsq
  simpa [dist_eq_norm] using hnormlt

end QuantumMechanics.WOTSpectralMeasure

end
