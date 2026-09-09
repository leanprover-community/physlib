/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Existence.CandidateGenerator
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Existence.GenericGardingKernel
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.AnalyticVector.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Analytic Gårding vectors for the candidate Stone generator (Milestone 1′)

`STONE_GENERATOR_EXISTENCE_PLAN.md`'s revised Milestone 1: instead of a compactly-supported bump
(which can never be real-analytic, so its Gårding vectors cannot be analytic vectors of the
generator), mollify against the normalized heat kernel

`gaussianKernel ε t := (π * ε)⁻¹ᐟ² * Real.exp (-(t ^ 2) / ε)` (`ε > 0`),

whose Gårding vectors `analyticGardingVector ε ψ := ∫ t, gaussianKernel ε t • U t ψ` are meant to
be simultaneously (a) genuine analytic vectors of `stoneCandidateGenerator` (fed to the ported
Nelson's theorem, Milestone 3′) and (b) dense as `ε → 0` (the heat kernel is an approximate
identity).

**(b) is fully proved** (`analyticGardingVector_tendsto`), via a scaling change of variables
`t = √ε x` that rewrites the `ε`-dependent Gaussian as a *fixed* kernel (`standardGaussianKernel`)
with all the `ε`-dependence pushed into `U (√ε x) ψ`'s argument — turning the approximate-identity
limit into ordinary dominated convergence instead of an explicit Gaussian-tail estimate.

**(a) is partially proved**: the commutation identity
`stoneCandidateGenerator_analyticGardingVector` (one derivative) is fully proved via
differentiation under the integral sign, and domain membership
(`analyticGardingVector_mem_stoneCandidateDomain`) is derived from it rather than assumed. The full
`IsAnalyticVector` conclusion (`LinearPMap.IsAnalyticVector`, from the landed Nelson port,
`AnalyticVector/Basic.lean`) needs the same argument iterated to every derivative order plus a
factorial-type `L¹` growth bound on the kernel's iterated derivatives — see
`GaussianKernelGrowth.lean` and `STONE_GENERATOR_EXISTENCE_PLAN.md`'s status log.

## Main definitions

- `gaussianKernel` : the normalized heat kernel on `ℝ`.
- `analyticGardingVector` : its Gårding vector, `∫ t, gaussianKernel ε t • U t ψ`.
- `analyticGardingVector_tendsto` : it tends to `ψ` as `ε → 0⁺`.
- `stoneCandidateGenerator_analyticGardingVector` : the one-derivative commutation identity.
- `analyticGardingVector_mem_stoneCandidateDomain` : membership, derived from the above.
-/

@[expose] public section

namespace QuantumMechanics

noncomputable section

open scoped InnerProductSpace Topology
open MeasureTheory Filter Real

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U : ℝ → H →L[ℂ] H} (hU0 : U 0 = 1) (hUmul : ∀ s t, U (s + t) = U s * U t)
  (hUunit : ∀ t, U t ∈ unitary (H →L[ℂ] H)) (hUcont : ∀ ξ : H, Continuous (fun t : ℝ => U t ξ))

/-- The normalized heat kernel: a Gaussian of variance `ε / 2`, normalized to integrate to `1`.
Unlike a compactly-supported bump, this is real-analytic in `t` for every fixed `ε > 0` — the
whole point of switching kernels for Milestone 1′. -/
def gaussianKernel (ε t : ℝ) : ℝ := (Real.pi * ε) ^ (-(1 : ℝ) / 2) * Real.exp (-(t ^ 2) / ε)

theorem gaussianKernel_pos {ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 < gaussianKernel ε t := by
  unfold gaussianKernel
  have hbase : (0 : ℝ) < Real.pi * ε := by positivity
  positivity

theorem gaussianKernel_integral {ε : ℝ} (hε : 0 < ε) :
    ∫ t : ℝ, gaussianKernel ε t = 1 := by
  unfold gaussianKernel
  rw [MeasureTheory.integral_const_mul]
  have hrw : (fun t : ℝ => Real.exp (-(t ^ 2) / ε)) = fun t : ℝ => Real.exp (-(1 / ε) * t ^ 2) := by
    funext t; ring_nf
  rw [hrw, integral_gaussian (1 / ε)]
  rw [show Real.pi / (1 / ε) = Real.pi * ε by field_simp]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity : (0:ℝ) < Real.pi * ε)]
  norm_num

/-- The heat kernel is integrable against any bounded continuous function, in particular against
`t ↦ U t ψ` (bounded because `U t` is unitary, `‖U t ψ‖ = ‖ψ‖`). -/
theorem gaussianKernel_smul_integrable (hUunit : ∀ t, U t ∈ unitary (H →L[ℂ] H))
    (hUcont : ∀ ξ : H, Continuous (fun t : ℝ => U t ξ))
    {ε : ℝ} (hε : 0 < ε) (ψ : H) :
    Integrable (fun t : ℝ => (gaussianKernel ε t : ℂ) • U t ψ) := by
  have hexp_int : Integrable (fun t : ℝ => Real.exp (-(t ^ 2) / ε)) := by
    have heq : (fun t : ℝ => Real.exp (-(t ^ 2) / ε)) =
                fun t : ℝ => Real.exp (-(1 / ε) * t ^ 2) := by
      funext t; ring_nf
    rw [heq]
    exact integrable_exp_neg_mul_sq (by positivity)
  have hkernel_int : Integrable (gaussianKernel ε) := by
    unfold gaussianKernel
    exact hexp_int.const_mul _
  have hg_int : Integrable (fun t : ℝ => gaussianKernel ε t * ‖ψ‖) := hkernel_int.mul_const _
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (gaussianKernel ε t : ℂ) • U t ψ) volume := by
    have hcont1 : Continuous (fun t : ℝ => (gaussianKernel ε t : ℂ)) := by
      unfold gaussianKernel; fun_prop
    exact (hcont1.smul (hUcont ψ)).aestronglyMeasurable
  refine Integrable.mono' hg_int hmeas (ae_of_all _ fun t => le_of_eq ?_)
  rw [norm_smul, Complex.norm_of_nonneg (gaussianKernel_pos hε t).le,
    ContinuousLinearMap.norm_map_of_mem_unitary (hUunit t)]

variable (U) in
/-- The Gårding vector of `ψ` mollified against the heat kernel of width `ε`. -/
def analyticGardingVector (ε : ℝ) (ψ : H) : H := ∫ t : ℝ, (gaussianKernel ε t : ℂ) • U t ψ

/-- The standard (`ε = 1`, unnormalized-width) Gaussian: `gaussianKernel ε` rescaled by
`t = √ε x` becomes a copy of this *fixed* kernel, independent of `ε`. Rewriting
`analyticGardingVector` through it (`analyticGardingVector_eq_standardGaussian`) turns the
`ε → 0⁺` approximate-identity limit into an ordinary dominated-convergence argument with a single,
`ε`-independent dominating function — avoiding an explicit Gaussian-tail estimate entirely. -/
private def standardGaussianKernel (x : ℝ) : ℝ := Real.pi ^ (-(1 : ℝ) / 2) * Real.exp (-(x ^ 2))

private theorem standardGaussianKernel_pos (x : ℝ) : 0 < standardGaussianKernel x := by
  unfold standardGaussianKernel; positivity

private theorem standardGaussianKernel_eq_gaussianKernel_one :
    standardGaussianKernel = gaussianKernel 1 := by
  funext t; unfold standardGaussianKernel gaussianKernel; norm_num

private theorem standardGaussianKernel_integral : ∫ x : ℝ, standardGaussianKernel x = 1 := by
  rw [standardGaussianKernel_eq_gaussianKernel_one]; exact gaussianKernel_integral one_pos

private theorem standardGaussianKernel_integrable : Integrable standardGaussianKernel := by
  rw [standardGaussianKernel_eq_gaussianKernel_one]
  have hexp : Integrable (fun t : ℝ => Real.exp (-(t ^ 2) / (1 : ℝ))) := by
    have heq : (fun t : ℝ => Real.exp (-(t ^ 2) / (1 : ℝ))) =
                fun t : ℝ => Real.exp (-(1 : ℝ) * t ^ 2) := by
      funext t; ring_nf
    rw [heq]; exact integrable_exp_neg_mul_sq one_pos
  unfold gaussianKernel; exact hexp.const_mul _

/-- The rescaling identity at the level of the kernel itself: `√ε · gaussianKernel ε (√ε x) =
standardGaussianKernel x`, i.e. the `ε`-dependence exactly cancels once the extra `√ε` from the
change-of-variables Jacobian is absorbed. -/
private theorem gaussianKernel_scale_eq_standardGaussianKernel {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    Real.sqrt ε * gaussianKernel ε (Real.sqrt ε * x) = standardGaussianKernel x := by
  unfold gaussianKernel standardGaussianKernel
  have hsq : -(Real.sqrt ε * x) ^ 2 / ε = -(x ^ 2) := by
    rw [neg_div, neg_inj, mul_pow, Real.sq_sqrt hε.le]
    field_simp
  have hkey : Real.sqrt ε * (Real.pi * ε) ^ (-(1 : ℝ) / 2) = Real.pi ^ (-(1 : ℝ) / 2) := by
    rw [Real.mul_rpow Real.pi_pos.le hε.le, Real.sqrt_eq_rpow, mul_comm (Real.pi ^ (-(1 : ℝ) / 2)),
      ← mul_assoc, ← Real.rpow_add hε, show (1 : ℝ) / 2 + -(1 : ℝ) / 2 = 0 by ring,
      Real.rpow_zero, one_mul]
  rw [hsq, ← mul_assoc, hkey]

omit [CompleteSpace H] in
/-- `analyticGardingVector` rewritten via `t = √ε x`: the `ε`-dependent Gaussian becomes the fixed
`standardGaussianKernel`, with all of the `ε`-dependence pushed into the orbit's argument
`√ε x → 0`. This is the substitution suggested to replace an explicit Gaussian-tail estimate with
ordinary dominated convergence. -/
private theorem analyticGardingVector_eq_standardGaussian {ε : ℝ} (hε : 0 < ε) (ψ : H) :
    analyticGardingVector U ε ψ =
      ∫ x : ℝ, (standardGaussianKernel x : ℂ) • U (Real.sqrt ε * x) ψ := by
  have hsq_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  unfold analyticGardingVector
  have step1 : (∫ x : ℝ, (standardGaussianKernel x : ℂ) • U (Real.sqrt ε * x) ψ) =
      (Real.sqrt ε : ℂ) •
        ∫ x : ℝ, (gaussianKernel ε (Real.sqrt ε * x) : ℂ) • U (Real.sqrt ε * x) ψ := by
    rw [← MeasureTheory.integral_smul]
    congr 1
    funext x
    rw [← gaussianKernel_scale_eq_standardGaussianKernel hε x]
    push_cast
    rw [smul_smul]
  rw [step1, MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => (gaussianKernel ε t : ℂ) • U t ψ) (Real.sqrt ε),
    abs_of_pos (inv_pos.mpr hsq_pos)]
  have hcast := RCLike.real_smul_eq_coe_smul (K := ℂ) (E := H) (Real.sqrt ε)⁻¹
    (∫ y : ℝ, (gaussianKernel ε y : ℂ) • U y ψ)
  rw [hcast, smul_smul]
  simp [hsq_pos.ne']

include hUunit in
/-- The heat kernel is an approximate identity: `analyticGardingVector ε ψ → ψ` as `ε → 0⁺`.
Rewritten via `analyticGardingVector_eq_standardGaussian` into a fixed-kernel integral whose only
`ε`-dependence is in `U (√ε x) ψ`'s argument, this becomes ordinary dominated convergence: for each
fixed `x`, `√ε x → 0` so `U (√ε x) ψ → U 0 ψ = ψ` by continuity, dominated by the `ε`-independent
bound `standardGaussianKernel x * ‖ψ‖` (using unitarity, `‖U t ψ‖ = ‖ψ‖`). -/
theorem analyticGardingVector_tendsto (hU0 : U 0 = 1)
    (hUcont : ∀ ξ : H, Continuous (fun t : ℝ => U t ξ)) (ψ : H) :
    Tendsto (fun ε : ℝ => analyticGardingVector U ε ψ) (𝓝[>] (0 : ℝ)) (𝓝 ψ) := by
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hrw : (fun ε : ℝ => ∫ x : ℝ, (standardGaussianKernel x : ℂ) • U (Real.sqrt ε * x) ψ) =ᶠ[
      𝓝[>] (0 : ℝ)] fun ε : ℝ => analyticGardingVector U ε ψ :=
    hev.mono (fun ε hε => (analyticGardingVector_eq_standardGaussian hε ψ).symm)
  refine Tendsto.congr' hrw ?_
  have hbound_int : Integrable (fun x : ℝ => standardGaussianKernel x * ‖ψ‖) :=
    standardGaussianKernel_integrable.mul_const _
  have hmeas : ∀ ε : ℝ, AEStronglyMeasurable
      (fun x : ℝ => (standardGaussianKernel x : ℂ) • U (Real.sqrt ε * x) ψ) volume := by
    intro ε
    have h1 : Continuous (fun x : ℝ => (standardGaussianKernel x : ℂ)) := by
      unfold standardGaussianKernel; fun_prop
    have h2 : Continuous (fun x : ℝ => U (Real.sqrt ε * x) ψ) :=
      (hUcont ψ).comp (continuous_const.mul continuous_id)
    exact (h1.smul h2).aestronglyMeasurable
  have hbound : ∀ ε x : ℝ, ‖(standardGaussianKernel x : ℂ) • U (Real.sqrt ε * x) ψ‖ ≤
      standardGaussianKernel x * ‖ψ‖ := by
    intro ε x
    rw [norm_smul, Complex.norm_of_nonneg (standardGaussianKernel_pos x).le,
      ContinuousLinearMap.norm_map_of_mem_unitary (hUunit _)]
  have hlim : ∀ x : ℝ, Tendsto (fun ε : ℝ => (standardGaussianKernel x : ℂ) • U (Real.sqrt ε * x) ψ)
      (𝓝[>] (0 : ℝ)) (𝓝 ((standardGaussianKernel x : ℂ) • ψ)) := by
    intro x
    have hsq : Tendsto (fun ε : ℝ => Real.sqrt ε * x) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      have h0 : Tendsto (fun ε : ℝ => Real.sqrt ε) (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
        (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa using h0.mul_const x
    have hUlim : Tendsto (fun ε : ℝ => U (Real.sqrt ε * x) ψ) (𝓝[>] (0 : ℝ)) (𝓝 (U 0 ψ)) :=
      ((hUcont ψ).tendsto 0).comp hsq
    rw [hU0, one_apply_eq_self] at hUlim
    exact hUlim.const_smul _
  have key := tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε x : ℝ => (standardGaussianKernel x : ℂ) • U (Real.sqrt ε * x) ψ)
    (f := fun x : ℝ => (standardGaussianKernel x : ℂ) • ψ)
    (fun x : ℝ => standardGaussianKernel x * ‖ψ‖)
    (Filter.Eventually.of_forall (fun ε => hmeas ε))
    (Filter.Eventually.of_forall (fun ε => ae_of_all _ (fun x => hbound ε x)))
    hbound_int
    (ae_of_all _ hlim)
  have hval : (∫ x : ℝ, (standardGaussianKernel x : ℂ)) = (1 : ℂ) := by
    rw [integral_complex_ofReal, standardGaussianKernel_integral, Complex.ofReal_one]
  rw [integral_smul_const, hval, one_smul] at key
  exact key

/-! ## Towards `analyticGardingVector_isAnalyticVector`

The classical Gårding-vector commutation identity `A (gardingVector f ψ) = -gardingVector f' ψ`
(up to the `-i` convention) is proved in two stages: first a purely algebraic translation identity
(no calculus, just `U`'s group law and translation-invariance of Lebesgue measure — proved below,
`analyticGardingVector_translate`), then a genuine differentiation-under-the-integral-sign step
(stated but not yet proved, `stoneCandidateGenerator_analyticGardingVector` below) that turns the
translation identity's `s`-dependence into a derivative of the smooth kernel. -/

include hUmul in
/-- Translating the orbit: `U s` applied to a Gårding vector is again a Gårding vector, but of the
kernel shifted by `s`. This is the algebraic heart of the commutation identity — everything here is
just `U`'s group law (`hUmul`) plus translation-invariance of the Lebesgue integral
(`MeasureTheory.integral_add_right_eq_self`); no differentiability of `t ↦ U t ψ` is needed, which
is the whole point: it lets the derivative be taken on the smooth kernel instead. -/
theorem analyticGardingVector_translate (hUunit : ∀ t, U t ∈ unitary (H →L[ℂ] H))
    (hUcont : ∀ ξ : H, Continuous (fun t : ℝ => U t ξ)) {ε : ℝ} (hε : 0 < ε) (ψ : H) (s : ℝ) :
    U s (analyticGardingVector U ε ψ) = ∫ u : ℝ, (gaussianKernel ε (u - s) : ℂ) • U u ψ := by
  unfold analyticGardingVector
  rw [← ContinuousLinearMap.integral_comp_comm (U s)
    (gaussianKernel_smul_integrable hUunit hUcont hε ψ)]
  have hpt : ∀ t : ℝ, U s ((gaussianKernel ε t : ℂ) • U t ψ) =
      (gaussianKernel ε t : ℂ) • U (t + s) ψ := by
    intro t
    rw [ContinuousLinearMap.map_smul]
    congr 1
    rw [← mul_apply_eq_comp, ← hUmul s t, add_comm s t]
  simp_rw [hpt]
  rw [← MeasureTheory.integral_add_right_eq_self
    (fun u : ℝ => (gaussianKernel ε (u - s) : ℂ) • U u ψ) s]
  simp only [add_sub_cancel_right]

/-- Explicit `HasDerivAt` for the heat kernel: `gaussianKernel ε` is differentiable everywhere,
with derivative `gaussianKernel ε t * (-(2 * t) / ε)` (the usual `d/dt exp(-t²/ε) = (-2t/ε)
exp(-t²/ε)` computation, scaled by the front normalization constant). -/
private theorem gaussianKernel_hasDerivAt {ε : ℝ} (_hε : 0 < ε) (t : ℝ) :
    HasDerivAt (gaussianKernel ε) (gaussianKernel ε t * (-(2 * t) / ε)) t := by
  unfold gaussianKernel
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have hquad : HasDerivAt (fun t : ℝ => -(t ^ 2) / ε) (-(2 * t) / ε) t := by
    simpa [div_eq_mul_inv] using hpow.neg.div_const ε
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(t ^ 2) / ε))
      (Real.exp (-(t ^ 2) / ε) * (-(2 * t) / ε)) t := hquad.exp
  have hker := hexp.const_mul ((Real.pi * ε) ^ (-(1 : ℝ) / 2))
  exact hker.congr_deriv (by ring)

/-- Corollary of `gaussianKernel_hasDerivAt` as a `deriv` equation. -/
private theorem gaussianKernel_deriv {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    deriv (gaussianKernel ε) t = gaussianKernel ε t * (-(2 * t) / ε) :=
  (gaussianKernel_hasDerivAt hε t).deriv

/-- `deriv (gaussianKernel ε)` is continuous. -/
private theorem gaussianKernel_deriv_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (deriv (gaussianKernel ε)) := by
  have heq : deriv (gaussianKernel ε) = fun t => gaussianKernel ε t * (-(2 * t) / ε) :=
    funext (gaussianKernel_deriv hε)
  rw [heq]
  have hcont : Continuous (gaussianKernel ε) := by unfold gaussianKernel; fun_prop
  fun_prop

/-- A uniform Gaussian-type envelope, over a bounded shift `x` with `x ^ 2 ≤ 1`, dominating
`|deriv (gaussianKernel ε) (u - x)|`: the shifted derivative-of-Gaussian is bounded by a constant
times `(|u| + 1) * exp (-(u ^ 2) / (2 * ε))`, which decays fast enough in `u` to be integrable
(`gaussianKernel_deriv_bound_integrable` below). -/
private theorem gaussianKernel_deriv_shift_bound {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : x ^ 2 ≤ 1)
    (u : ℝ) :
    |deriv (gaussianKernel ε) (u - x)| ≤
      (2 * (Real.pi * ε) ^ (-(1 : ℝ) / 2) * Real.exp (1 / ε) / ε) *
        ((|u| + 1) * Real.exp (-(u ^ 2) / (2 * ε))) := by
  set t := u - x with ht
  rw [gaussianKernel_deriv hε t, abs_mul, abs_of_pos (gaussianKernel_pos hε t)]
  have habs_div : |(-(2 * t)) / ε| = 2 * |t| / ε := by
    rw [abs_div, abs_neg, abs_mul, abs_of_pos hε, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  rw [habs_div]
  have hsq : u ^ 2 / 2 - 1 ≤ t ^ 2 := by nlinarith [sq_nonneg (u - 2 * x), hx]
  have hexp_le : Real.exp (-(t ^ 2) / ε) ≤ Real.exp (1 / ε) * Real.exp (-(u ^ 2) / (2 * ε)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [div_add_div _ _ (ne_of_gt hε) (by positivity : (2 : ℝ) * ε ≠ 0),
      div_le_div_iff₀ hε (by positivity : (0 : ℝ) < ε * (2 * ε))]
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg ε)]
  have hCpos : (0 : ℝ) < (Real.pi * ε) ^ (-(1 : ℝ) / 2) := by positivity
  have htu : |t| ≤ |u| + 1 := by
    have h1 : |t| ≤ |u| + |x| := by
      have h0 := abs_add_le u (-x)
      simpa [ht, sub_eq_add_neg] using h0
    have h2 : |x| ≤ 1 := by nlinarith [sq_abs x, hx]
    linarith
  have hstep1 : (Real.pi * ε) ^ (-(1 : ℝ) / 2) * Real.exp (-(t ^ 2) / ε) * (2 * |t| / ε) ≤
      (Real.pi * ε) ^ (-(1 : ℝ) / 2) * (Real.exp (1 / ε) * Real.exp (-(u ^ 2) / (2 * ε))) *
        (2 * (|u| + 1) / ε) := by
    gcongr
  calc gaussianKernel ε t * (2 * |t| / ε)
      = (Real.pi * ε) ^ (-(1 : ℝ) / 2) * Real.exp (-(t ^ 2) / ε) * (2 * |t| / ε) := by
        rfl
    _ ≤ (Real.pi * ε) ^ (-(1 : ℝ) / 2) * (Real.exp (1 / ε) * Real.exp (-(u ^ 2) / (2 * ε))) *
        (2 * (|u| + 1) / ε) := hstep1
    _ = (2 * (Real.pi * ε) ^ (-(1 : ℝ) / 2) * Real.exp (1 / ε) / ε) *
        ((|u| + 1) * Real.exp (-(u ^ 2) / (2 * ε))) := by ring

/-- The `L¹` domination bound is itself integrable in `u`: it is `const * ((|u|+1) *
Gaussian(u))`, and `|u| * Gaussian(u)` and `Gaussian(u)` are each classically integrable
(`integrable_mul_exp_neg_mul_sq`, `integrable_exp_neg_mul_sq`). -/
private theorem gaussianKernel_deriv_bound_integrable {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    Integrable (fun u : ℝ => c * ((|u| + 1) * Real.exp (-(u ^ 2) / (2 * ε)))) := by
  have hb : (0 : ℝ) < 1 / (2 * ε) := by positivity
  have h1 : Integrable (fun u : ℝ => u * Real.exp (-(1 / (2 * ε)) * u ^ 2)) :=
    integrable_mul_exp_neg_mul_sq hb
  have h1' : Integrable (fun u : ℝ => |u| * Real.exp (-(1 / (2 * ε)) * u ^ 2)) := by
    have := h1.abs
    simpa [abs_mul, abs_of_nonneg (Real.exp_pos _).le] using this
  have h2 : Integrable (fun u : ℝ => Real.exp (-(1 / (2 * ε)) * u ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have hsum : Integrable (fun u : ℝ => |u| * Real.exp (-(1 / (2 * ε)) * u ^ 2) +
      Real.exp (-(1 / (2 * ε)) * u ^ 2)) := h1'.add h2
  have heq : (fun u : ℝ => c * ((|u| + 1) * Real.exp (-(u ^ 2) / (2 * ε)))) =
      fun u : ℝ => c * (|u| * Real.exp (-(1 / (2 * ε)) * u ^ 2) +
        Real.exp (-(1 / (2 * ε)) * u ^ 2)) := by
    funext u; rw [show -(u ^ 2) / (2 * ε) = -(1 / (2 * ε)) * u ^ 2 by ring]; ring
  rw [heq]
  exact hsum.const_mul c

include hUmul in
/-- The heart of the commutation identity, factored out so it can feed both the domain-membership
fact (`analyticGardingVector_mem_stoneCandidateDomain`) and the generator's actual value
(`stoneCandidateGenerator_analyticGardingVector`) without proving the same
differentiation-under-the-integral argument twice: the orbit `s ↦ U s (analyticGardingVector U ε ψ)`
literally has a derivative at `0`, namely `∫ u, -(deriv (gaussianKernel ε) u) • U u ψ` — this alone
already witnesses `analyticGardingVector U ε ψ ∈ stoneCandidateDomain` (whose defining predicate is
exactly "the orbit is differentiable at `0`"), which is why `hmem` should never need to be an
independent hypothesis: it's precisely the byproduct of this computation, not extra data. Proved by
differentiating `analyticGardingVector_translate`'s RHS in `s` at `s = 0` via
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` (`Analysis/Calculus/ParametricIntegral.lean`),
using `gaussianKernel_deriv_shift_bound` as the domination bound. -/
private theorem analyticGardingVector_hasDerivAt
    (hUunit : ∀ t, U t ∈ unitary (H →L[ℂ] H))
    (hUcont : ∀ ξ : H, Continuous (fun t : ℝ => U t ξ)) {ε : ℝ} (hε : 0 < ε) (ψ : H) :
    HasDerivAt (fun s : ℝ => U s (analyticGardingVector U ε ψ))
      (∫ u : ℝ, ((-(deriv (gaussianKernel ε) u) : ℝ) : ℂ) • U u ψ) 0 := by
  have hgvEq : gardingVectorAt U (gaussianKernel ε) ψ = analyticGardingVector U ε ψ := rfl
  rw [← hgvEq]
  have hgk_cont : Continuous (gaussianKernel ε) := by unfold gaussianKernel; fun_prop
  have hgk'_cont : Continuous (deriv (gaussianKernel ε)) := gaussianKernel_deriv_continuous hε
  set c : ℝ := 2 * (Real.pi * ε) ^ (-(1 : ℝ) / 2) * Real.exp (1 / ε) / ε * ‖ψ‖ with hc
  refine gardingVectorAt_hasDerivAt hUmul hUunit hUcont (gaussianKernel ε)
    (deriv (gaussianKernel ε))
    hgk_cont hgk'_cont
    (fun t => (gaussianKernel_hasDerivAt hε t).congr_deriv (gaussianKernel_deriv hε t).symm) ψ
    (gaussianKernel_smul_integrable hUunit hUcont hε ψ)
    (fun u => c * ((|u| + 1) * Real.exp (-(u ^ 2) / (2 * ε))))
    (gaussianKernel_deriv_bound_integrable hε c) (fun u x hx => ?_)
  have hx2 : x ^ 2 ≤ 1 := by
    have := Metric.mem_ball.mp hx
    rw [Real.dist_eq, sub_zero] at this
    nlinarith [abs_nonneg x, sq_abs x, this]
  calc |deriv (gaussianKernel ε) (u - x)| * ‖ψ‖
      ≤ (2 * (Real.pi * ε) ^ (-(1 : ℝ) / 2) * Real.exp (1 / ε) / ε) *
          ((|u| + 1) * Real.exp (-(u ^ 2) / (2 * ε))) * ‖ψ‖ :=
        mul_le_mul_of_nonneg_right (gaussianKernel_deriv_shift_bound hε hx2 u) (norm_nonneg ψ)
    _ = c * ((|u| + 1) * Real.exp (-(u ^ 2) / (2 * ε))) := by rw [hc]; ring

/-- The Gaussian construction doesn't just *use* domain membership, it *proves* it: this is exactly
the content of `analyticGardingVector_hasDerivAt`, since `stoneCandidateDomain`'s membership
predicate is precisely "the orbit is differentiable at `0`". No `hmem` hypothesis needed anywhere —
smoothing against the heat kernel constructs a domain vector, it doesn't merely happen to land in
one that was assumed to exist. -/
theorem analyticGardingVector_mem_stoneCandidateDomain (hUunit : ∀ t, U t ∈ unitary (H →L[ℂ] H))
    (hUcont : ∀ ξ : H, Continuous (fun t : ℝ => U t ξ)) {ε : ℝ} (hε : 0 < ε) (ψ : H) :
    analyticGardingVector U ε ψ ∈ (stoneCandidateGenerator (U := U) hUmul).domain :=
  ⟨_, analyticGardingVector_hasDerivAt hUmul hUunit hUcont hε ψ⟩

/-- The commutation identity itself: applying the candidate generator to a Gårding vector smears
the *derivative* of the kernel instead. Membership in the generator's domain is derived, not
assumed (`analyticGardingVector_mem_stoneCandidateDomain`), and the value follows from
`analyticGardingVector_hasDerivAt` by uniqueness of `HasDerivAt`. -/
theorem stoneCandidateGenerator_analyticGardingVector (hUunit : ∀ t, U t ∈ unitary (H →L[ℂ] H))
    (hUcont : ∀ ξ : H, Continuous (fun t : ℝ => U t ξ)) {ε : ℝ} (hε : 0 < ε) (ψ : H) :
    stoneCandidateGenerator (U := U) hUmul
        ⟨analyticGardingVector U ε ψ, analyticGardingVector_mem_stoneCandidateDomain hUmul
          hUunit hUcont hε ψ⟩ =
      (Complex.I : ℂ) • ∫ u : ℝ, ((deriv (gaussianKernel ε) u : ℝ) : ℂ) • U u ψ := by
  set hmem := analyticGardingVector_mem_stoneCandidateDomain hUmul hUunit hUcont hε ψ
  have hspec := stoneCandidateDeriv_spec (U := U) hUmul
    (ψ := ⟨analyticGardingVector U ε ψ, hmem⟩)
  have hderiv_eq := hspec.unique (analyticGardingVector_hasDerivAt hUmul hUunit hUcont hε ψ)
  refine (stoneCandidateGenerator_apply (U := U) hUmul ⟨analyticGardingVector U ε ψ, hmem⟩).trans ?_
  show (-Complex.I) • stoneCandidateDeriv hUmul
      (⟨analyticGardingVector U ε ψ, hmem⟩ : stoneCandidateDomain (U := U) hUmul) =
      Complex.I • ∫ u : ℝ, ((deriv (gaussianKernel ε) u : ℝ) : ℂ) • U u ψ
  rw [hderiv_eq]
  have hneg : (∫ u : ℝ, ((-(deriv (gaussianKernel ε) u) : ℝ) : ℂ) • U u ψ) =
      -(∫ u : ℝ, ((deriv (gaussianKernel ε) u : ℝ) : ℂ) • U u ψ) := by
    rw [← MeasureTheory.integral_neg]
    congr 1
    funext u
    push_cast
    rw [neg_smul]
  rw [hneg, smul_neg, neg_smul, neg_neg]

/-! ## Milestone 2 of Track A: assembling the full `IsAnalyticVector` witness

`stoneCandidateGenerator_analyticGardingVector` proves the *single-derivative* commutation
identity. The generalization to every derivative order (needed for the full `IsAnalyticVector`
witness) is assembled in `IteratedKernelGrowth.lean` and `GardingVectorWitness.lean`,
which live downstream of this file (they need `GaussianKernelGrowth.lean`'s growth bound, which
itself imports this file) — see `analyticGardingVector_isAnalyticVector` there. -/

end

end QuantumMechanics
