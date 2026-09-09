/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Existence.GaussianKernelGrowth
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Existence.GenericGardingKernel

/-!
# Pointwise (not just `L¹`) growth of the heat kernel's iterated derivatives

Milestone 2 of Track A (`STONE_GENERATOR_EXISTENCE_PLAN.md`): `gardingVectorAt_hasDerivAt`
(`GenericGardingKernel.lean`) needs, for `k := iteratedDeriv n (gaussianKernel ε)`, a **local
pointwise** domination bound on `k' = iteratedDeriv (n+1) (gaussianKernel ε)` near a shift `x` in
a bounded neighborhood of `0` — materially different from `GaussianKernelGrowth.lean`'s *global*
`L¹`-norm bound on `iteratedDeriv n (gaussianKernel ε)` itself. This file supplies that pointwise
bound, via a simple coefficient-sum estimate on Hermite polynomials (weaker than, and much easier
than, the `L¹` growth-rate estimate already proved) combined with
`gaussianKernel_iteratedDeriv_eq`'s closed form.

## Main results

- `hermite_aeval_le_poly_growth` : `|Hₙ(y)| ≤ Cₙ (1+|y|)ⁿ` for an explicit `n`-dependent constant.
- `gaussianKernel_iteratedDeriv_shift_bound` : the local domination bound needed by
  `gardingVectorAt_hasDerivAt`, generalizing `gaussianKernel_deriv_shift_bound` to every order.
-/

@[expose] public section

namespace QuantumMechanics

noncomputable section

open MeasureTheory Polynomial

/-- **A simple pointwise coefficient-sum bound** on Hermite polynomials: `|Hₙ(y)| ≤ Cₙ (1+|y|)ⁿ`,
where `Cₙ` is the sum of the absolute values of `Hₙ`'s coefficients. Much weaker than (and much
easier to prove than) `hermite_gaussian_L1_bound`'s weighted `L¹` growth rate, but exactly the
*pointwise* statement `gardingVectorAt_hasDerivAt`'s local domination hypothesis needs. -/
theorem hermite_aeval_le_poly_growth (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, |aeval y (hermite n)| ≤ C * (1 + |y|) ^ n := by
  set C : ℝ := ∑ i ∈ Finset.range (n + 1), |((hermite n).coeff i : ℝ)| with hC_def
  have hC_nonneg : 0 ≤ C := Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨C, hC_nonneg, fun y => ?_⟩
  have hsum : aeval y (hermite n) =
      ∑ i ∈ Finset.range ((hermite n).natDegree + 1), ((hermite n).coeff i : ℝ) * y ^ i := by
    rw [aeval_eq_sum_range]
    simp [zsmul_eq_mul]
  rw [natDegree_hermite] at hsum
  rw [hsum]
  calc |∑ i ∈ Finset.range (n + 1), ((hermite n).coeff i : ℝ) * y ^ i|
      ≤ ∑ i ∈ Finset.range (n + 1), |((hermite n).coeff i : ℝ) * y ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (n + 1), |((hermite n).coeff i : ℝ)| * |y| ^ i := by
        simp [abs_mul, abs_pow]
    _ ≤ ∑ i ∈ Finset.range (n + 1), |((hermite n).coeff i : ℝ)| * (1 + |y|) ^ n := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 : |y| ≤ 1 + |y| := by linarith [abs_nonneg y]
        have h2 : |y| ^ i ≤ (1 + |y|) ^ i := pow_le_pow_left₀ (abs_nonneg y) h1 i
        have h3 : (1 + |y|) ^ i ≤ (1 + |y|) ^ n :=
          pow_le_pow_right₀ (by linarith [abs_nonneg y]) hi'
        exact mul_le_mul_of_nonneg_left (h2.trans h3) (abs_nonneg _)
    _ = C * (1 + |y|) ^ n := by rw [← Finset.sum_mul]

/-- **The local pointwise domination bound**, generalizing `gaussianKernel_deriv_shift_bound`
(order `1`) to every order: for `x` in the closed unit ball, `iteratedDeriv (n+1) (gaussianKernel
ε) (u - x)` is dominated by a constant (depending on `n`, `ε`, but not `x` or `u`) times a
polynomial-times-Gaussian envelope in `u`. Proved from `gaussianKernel_iteratedDeriv_eq`'s closed
form and `hermite_aeval_le_poly_growth`, using `(u-x)² ≥ u²/2 - 1` for `x² ≤ 1` (the same
inequality `gaussianKernel_deriv_shift_bound` uses) to push the shift onto a Gaussian-tail loss of
a fixed multiplicative factor `exp(1/ε)`. -/
theorem gaussianKernel_iteratedDeriv_shift_bound (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {x : ℝ}, x ^ 2 ≤ 1 → ∀ u : ℝ,
      |iteratedDeriv (n + 1) (gaussianKernel ε) (u - x)| ≤
        D * ((1 + |u|) ^ (n + 1) * Real.exp (-(u ^ 2) / (2 * ε))) := by
  set c : ℝ := Real.sqrt (2 / ε) with hc_def
  have hc_pos : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc_sq : c ^ 2 = 2 / ε := Real.sq_sqrt (by positivity)
  set K : ℝ := (Real.pi * ε) ^ (-(1 : ℝ) / 2) with hK_def
  have hK_pos : 0 < K := by rw [hK_def]; positivity
  obtain ⟨Cn, hCn_nonneg, hCn⟩ := hermite_aeval_le_poly_growth (n + 1)
  set D : ℝ := K * c ^ (n + 1) * Cn * (1 + c) ^ (n + 1) * Real.exp (1 / ε) with hD_def
  refine ⟨D, by positivity, fun {x} hx u => ?_⟩
  rw [gaussianKernel_iteratedDeriv_eq hε (n + 1) (u - x)]
  have hval : |K * (c ^ (n + 1) * ((-1 : ℝ) ^ (n + 1) *
      aeval (c * (u - x)) (hermite (n + 1)) * Real.exp (-((c * (u - x)) ^ 2 / 2))))| =
      K * c ^ (n + 1) * (|aeval (c * (u - x)) (hermite (n + 1))| *
        Real.exp (-((c * (u - x)) ^ 2 / 2))) := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hK_pos, abs_of_pos (pow_pos hc_pos (n + 1)),
      abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (Real.exp_pos _), mul_assoc]
  rw [hval]
  have hshift_arg : 1 + |c * (u - x)| ≤ (1 + c) * (1 + |u|) := by
    have h1 : |c * (u - x)| ≤ c * (|u| + 1) := by
      rw [abs_mul, abs_of_pos hc_pos]
      have h2 : |u - x| ≤ |u| + 1 := by
        have h3 : |u - x| ≤ |u| + |x| := by
          have := abs_add_le u (-x)
          simpa [sub_eq_add_neg] using this
        have h4 : |x| ≤ 1 := by nlinarith [sq_abs x, hx]
        linarith
      exact mul_le_mul_of_nonneg_left h2 hc_pos.le
    nlinarith [abs_nonneg u, h1]
  have hpoly_bound : |aeval (c * (u - x)) (hermite (n + 1))| ≤
      Cn * ((1 + c) * (1 + |u|)) ^ (n + 1) := by
    calc |aeval (c * (u - x)) (hermite (n + 1))|
        ≤ Cn * (1 + |c * (u - x)|) ^ (n + 1) := hCn _
      _ ≤ Cn * ((1 + c) * (1 + |u|)) ^ (n + 1) := by
          gcongr
  have hexp_bound : Real.exp (-((c * (u - x)) ^ 2 / 2)) ≤
      Real.exp (1 / ε) * Real.exp (-(u ^ 2) / (2 * ε)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsq : u ^ 2 / 2 - 1 ≤ (u - x) ^ 2 := by nlinarith [sq_nonneg (u - 2 * x), hx]
    have hkey : (c * (u - x)) ^ 2 = c ^ 2 * (u - x) ^ 2 := by ring
    have heq1 : -((c * (u - x)) ^ 2 / 2) = -((u - x) ^ 2) / ε := by
      rw [hkey, hc_sq]; field_simp
    have heq2 : (1 : ℝ) / ε + -u ^ 2 / (2 * ε) = (1 - u ^ 2 / 2) / ε := by field_simp; ring
    rw [heq1, heq2]
    gcongr
    linarith [hsq]
  calc K * c ^ (n + 1) * (|aeval (c * (u - x)) (hermite (n + 1))| *
      Real.exp (-((c * (u - x)) ^ 2 / 2)))
      ≤ K * c ^ (n + 1) * ((Cn * ((1 + c) * (1 + |u|)) ^ (n + 1)) *
          (Real.exp (1 / ε) * Real.exp (-(u ^ 2) / (2 * ε)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ K * c ^ (n + 1))
        apply mul_le_mul hpoly_bound hexp_bound (Real.exp_pos _).le
        positivity
    _ = D * ((1 + |u|) ^ (n + 1) * Real.exp (-(u ^ 2) / (2 * ε))) := by
        rw [hD_def, mul_pow]; ring

/-- `|u|^n` times a Gaussian weight is integrable — the `abs`-of-argument variant of
`integrable_pow_mul_exp_neg_mul_sq`, obtained via `Integrable.abs` since `|u^n * exp(-cu²)| =
|u|^n * exp(-cu²)`. -/
theorem integrable_abs_pow_mul_exp_neg_mul_sq (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ => |u| ^ n * Real.exp (-(c * u ^ 2))) := by
  have h := integrable_pow_mul_exp_neg_mul_sq n hc
  have habs := h.abs
  have heq : (fun u : ℝ => |u ^ n * Real.exp (-(c * u ^ 2))|) =
      fun u : ℝ => |u| ^ n * Real.exp (-(c * u ^ 2)) := by
    funext u; rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  rwa [heq] at habs

/-- **The integrability of the domination bound's envelope** `(1+|u|)ⁿ · exp(-cu²)`, via the
binomial theorem reducing to `integrable_abs_pow_mul_exp_neg_mul_sq` term by term — exactly the
integrability fact `gardingVectorAt_hasDerivAt` needs for its `bound_int` hypothesis, feeding
`gaussianKernel_iteratedDeriv_shift_bound`. -/
theorem integrable_one_add_abs_pow_mul_exp_neg_mul_sq (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ => (1 + |u|) ^ n * Real.exp (-(c * u ^ 2))) := by
  have heq : (fun u : ℝ => (1 + |u|) ^ n * Real.exp (-(c * u ^ 2))) =
      fun u : ℝ => (∑ m ∈ Finset.range (n + 1),
        |u| ^ m * (1 : ℝ) ^ (n - m) * n.choose m) * Real.exp (-(c * u ^ 2)) := by
    funext u
    rw [add_comm (1 : ℝ) |u|, add_pow]
  rw [heq]
  have heq2 : (fun u : ℝ => (∑ m ∈ Finset.range (n + 1),
      |u| ^ m * (1 : ℝ) ^ (n - m) * n.choose m) * Real.exp (-(c * u ^ 2))) =
      fun u : ℝ => ∑ m ∈ Finset.range (n + 1),
        (n.choose m : ℝ) * (|u| ^ m * Real.exp (-(c * u ^ 2))) := by
    funext u
    rw [Finset.sum_mul]
    congr 1
    funext m
    ring
  rw [heq2]
  apply integrable_finsetSum
  intro m _
  exact (integrable_abs_pow_mul_exp_neg_mul_sq m hc).const_mul _

/-- `gaussianKernel ε` is smooth to every order (used to get `Continuous`/`Differentiable` facts
about its iterated derivatives via the generic `ContDiff.continuous_iteratedDeriv`/
`ContDiff.differentiable_iteratedDeriv`). -/
theorem gaussianKernel_contDiff {ε : ℝ} (_hε : 0 < ε) : ContDiff ℝ (⊤ : ℕ∞) (gaussianKernel ε) := by
  unfold gaussianKernel
  fun_prop

/-- `iteratedDeriv n (gaussianKernel ε)` is continuous, for every `n`. -/
theorem gaussianKernel_iteratedDeriv_continuous (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (iteratedDeriv n (gaussianKernel ε)) :=
  ContDiff.continuous_iteratedDeriv' n
    ((gaussianKernel_contDiff hε).of_le (by exact_mod_cast le_top))

/-- The successor identity `HasDerivAt (iteratedDeriv n (gaussianKernel ε)) (iteratedDeriv (n+1)
(gaussianKernel ε) t) t`, connecting consecutive orders — exactly the `hk_deriv` hypothesis
`gardingVectorAt_hasDerivAt` needs when instantiated at `k := iteratedDeriv n (gaussianKernel
ε)`. -/
theorem gaussianKernel_iteratedDeriv_hasDerivAt (n : ℕ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (iteratedDeriv n (gaussianKernel ε))
      (iteratedDeriv (n + 1) (gaussianKernel ε) t) t := by
  have hdiff : DifferentiableAt ℝ (iteratedDeriv n (gaussianKernel ε)) t := by
    have h := ContDiff.differentiable_iteratedDeriv' n
      ((gaussianKernel_contDiff hε).of_le (by exact_mod_cast le_top))
    exact h.differentiableAt
  have heq : deriv (iteratedDeriv n (gaussianKernel ε)) t =
      iteratedDeriv (n + 1) (gaussianKernel ε) t := by
    rw [iteratedDeriv_succ]
  rw [← heq]
  exact hdiff.hasDerivAt

/-- `iteratedDeriv n (gaussianKernel ε)` is integrable against `t ↦ U t ψ`, exactly like
`gaussianKernel_smul_integrable` at order `0`: bounded by `|iteratedDeriv n (gaussianKernel ε) t| ·
‖ψ‖` via unitarity, and `Integrable (iteratedDeriv n (gaussianKernel ε))` itself is
`gaussianKernel_iteratedDeriv_L1_bound`'s first component. -/
theorem gaussianKernel_iteratedDeriv_smul_integrable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {U : ℝ → H →L[ℂ] H}
    (hUunit : ∀ t, U t ∈ unitary (H →L[ℂ] H)) (hUcont : ∀ ξ : H, Continuous (fun t : ℝ => U t ξ))
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) (ψ : H) :
    Integrable (fun t : ℝ => ((iteratedDeriv n (gaussianKernel ε) t : ℝ) : ℂ) • U t ψ) := by
  obtain ⟨C, hC, hall⟩ := gaussianKernel_iteratedDeriv_L1_bound (ε := ε) hε
  have hkernel_int : Integrable (iteratedDeriv n (gaussianKernel ε)) := (hall n).1
  have hg_int : Integrable (fun t : ℝ => |iteratedDeriv n (gaussianKernel ε) t| * ‖ψ‖) :=
    hkernel_int.abs.mul_const _
  have hmeas : AEStronglyMeasurable (fun t : ℝ =>
      ((iteratedDeriv n (gaussianKernel ε) t : ℝ) : ℂ) • U t ψ) volume := by
    have hcont0 : Continuous (iteratedDeriv n (gaussianKernel ε)) :=
      gaussianKernel_iteratedDeriv_continuous n hε
    have hcont1 : Continuous (fun t : ℝ => ((iteratedDeriv n (gaussianKernel ε) t : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hcont0
    exact (hcont1.smul (hUcont ψ)).aestronglyMeasurable
  refine Integrable.mono' hg_int hmeas (ae_of_all _ fun t => le_of_eq ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    ContinuousLinearMap.norm_map_of_mem_unitary (hUunit t)]

/-- **The generalized single-derivative commutation identity, at every order `n`.** Instantiating
`gardingVectorAt_hasDerivAt` at `k := iteratedDeriv n (gaussianKernel ε)` — the whole point of
`GenericGardingKernel.lean`'s abstraction — using `gaussianKernel_iteratedDeriv_hasDerivAt` for the
derivative identity and `gaussianKernel_iteratedDeriv_shift_bound` (turned into an integrable
domination function via `integrable_one_add_abs_pow_mul_exp_neg_mul_sq`) for the local domination
hypothesis. This is the engine `analyticGardingVector_isAnalyticVector` (Milestone 2 of Track A)
needs, applied for every `n` to build the `IteratesSeq` witness. -/
theorem gardingVectorAt_iteratedKernel_hasDerivAt {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {U : ℝ → H →L[ℂ] H}
    (hUmul : ∀ s t, U (s + t) = U s * U t) (hUunit : ∀ t, U t ∈ unitary (H →L[ℂ] H))
    (hUcont : ∀ ξ : H, Continuous (fun t : ℝ => U t ξ)) (n : ℕ) {ε : ℝ} (hε : 0 < ε) (ψ : H) :
    HasDerivAt (fun s : ℝ => U s (gardingVectorAt U (iteratedDeriv n (gaussianKernel ε)) ψ))
      (∫ u : ℝ, ((-(iteratedDeriv (n + 1) (gaussianKernel ε) u) : ℝ) : ℂ) • U u ψ) 0 := by
  obtain ⟨D, hD_nonneg, hD⟩ := gaussianKernel_iteratedDeriv_shift_bound n hε
  have hbound_int : Integrable (fun u : ℝ =>
      D * ‖ψ‖ * ((1 + |u|) ^ (n + 1) * Real.exp (-(u ^ 2) / (2 * ε)))) := by
    have hbase : Integrable (fun u : ℝ =>
        (1 + |u|) ^ (n + 1) * Real.exp (-(u ^ 2) / (2 * ε))) := by
      have heq : (fun u : ℝ => (1 + |u|) ^ (n + 1) * Real.exp (-(u ^ 2) / (2 * ε))) =
          fun u : ℝ => (1 + |u|) ^ (n + 1) * Real.exp (-(1 / (2 * ε) * u ^ 2)) := by
        funext u; rw [show -(u ^ 2) / (2 * ε) = -(1 / (2 * ε) * u ^ 2) by ring]
      rw [heq]
      exact integrable_one_add_abs_pow_mul_exp_neg_mul_sq (n + 1) (c := 1 / (2 * ε)) (by positivity)
    exact hbase.const_mul _
  exact gardingVectorAt_hasDerivAt hUmul hUunit hUcont (iteratedDeriv n (gaussianKernel ε))
    (iteratedDeriv (n + 1) (gaussianKernel ε)) (gaussianKernel_iteratedDeriv_continuous n hε)
    (gaussianKernel_iteratedDeriv_continuous (n + 1) hε)
    (gaussianKernel_iteratedDeriv_hasDerivAt n hε) ψ
    (gaussianKernel_iteratedDeriv_smul_integrable hUunit hUcont n hε ψ)
    (fun u => D * ‖ψ‖ * ((1 + |u|) ^ (n + 1) * Real.exp (-(u ^ 2) / (2 * ε))))
    hbound_int (fun u x hx => by
      have hx2 : x ^ 2 ≤ 1 := by
        have hxb := Metric.mem_ball.mp hx
        rw [Real.dist_eq, sub_zero] at hxb
        nlinarith [abs_nonneg x, sq_abs x, hxb]
      have := hD hx2 u
      calc |iteratedDeriv (n + 1) (gaussianKernel ε) (u - x)| * ‖ψ‖
          ≤ (D * ((1 + |u|) ^ (n + 1) * Real.exp (-(u ^ 2) / (2 * ε)))) * ‖ψ‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg ψ)
        _ = D * ‖ψ‖ * ((1 + |u|) ^ (n + 1) * Real.exp (-(u ^ 2) / (2 * ε))) := by ring)

end

end QuantumMechanics
