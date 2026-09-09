/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Existence.IteratedKernelGrowth
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.AnalyticVector.Basic

/-!
# The full `IsAnalyticVector` witness for Gårding vectors (Milestone 2 of Track A, completed)

The capstone of `STONE_GENERATOR_EXISTENCE_PLAN.md`'s Milestone 1′: `analyticGardingVector U ε ψ`
is a genuine `LinearPMap.IsAnalyticVector` of `stoneCandidateGenerator`, for *every* strongly
continuous one-parameter unitary group `U` and every `ψ`. Combined with the ported Nelson's
analytic-vector theorem (`AnalyticVector/Nelson.lean`), this is the existence direction of Stone's
theorem via Gårding vectors, entirely avoiding the classical Bochner/spectral-measure route.

## The assembly

Write `Gₙ := gardingVectorAt U (iteratedDeriv n (gaussianKernel ε)) ψ` (so `G₀ =
analyticGardingVector U ε ψ`, `rfl`). `gardingVectorAt_iteratedKernel_hasDerivAt`
(`IteratedKernelGrowth.lean`) gives, for
every `n`: `Gₙ ∈ (stoneCandidateGenerator hUmul).domain` and
`stoneCandidateGenerator hUmul Gₙ = I • Gₙ₊₁` (the same argument as
`stoneCandidateGenerator_analyticGardingVector`, one order at a time). Since `T` is linear on its
domain, `v n := Iⁿ • ⟨Gₙ, _⟩` then satisfies the `IteratesSeq` recursion exactly (the factor of `I`
at each step is absorbed by the extra power of `I` on the left): `T (v n) = Iⁿ • (T Gₙ) = Iⁿ • (I •
Gₙ₊₁) = Iⁿ⁺¹ • Gₙ₊₁ = v (n+1)`. Since `|I| = 1`, `‖(v n : H)‖ = ‖Gₙ‖`, bounded via
`gaussianKernel_iteratedDeriv_L1_bound` and unitarity by `‖ψ‖ · C^(n+1) · √(n!)`. Choosing `t`
small enough that `C·t < 1` turns the majorant series into a genuine geometric series (dominating
the `1/√(n!) ≤ 1` factor crudely, which is all that is needed for the analytic-vector radius, even
though the true series is far better than geometric) — summable, completing the witness.
-/

@[expose] public section

namespace QuantumMechanics

noncomputable section

open scoped InnerProductSpace
open MeasureTheory LinearPMap

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U : ℝ → H →L[ℂ] H} (hUmul : ∀ s t, U (s + t) = U s * U t)

include hUmul in
/-- Domain membership of the `n`-th iterated-kernel Gårding vector, derived (not assumed) from the
differentiability of its orbit — the same pattern as
`analyticGardingVector_mem_stoneCandidateDomain`, one order at a time. -/
theorem gardingVectorAt_iteratedKernel_mem_stoneCandidateDomain
    (hUunit : ∀ t, U t ∈ unitary (H →L[ℂ] H)) (hUcont : ∀ ξ : H, Continuous (fun t : ℝ => U t ξ))
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) (ψ : H) :
    gardingVectorAt U (iteratedDeriv n (gaussianKernel ε)) ψ ∈
      (stoneCandidateGenerator (U := U) hUmul).domain :=
  ⟨_, gardingVectorAt_iteratedKernel_hasDerivAt hUmul hUunit hUcont n hε ψ⟩

include hUmul in
/-- The commutation identity at every order: applying `stoneCandidateGenerator` to `Gₙ` gives (up
to the factor `I`) `Gₙ₊₁`. Exactly `stoneCandidateGenerator_analyticGardingVector`'s proof, one
order at a time. -/
theorem stoneCandidateGenerator_gardingVectorAt_iteratedKernel
    (hUunit : ∀ t, U t ∈ unitary (H →L[ℂ] H)) (hUcont : ∀ ξ : H, Continuous (fun t : ℝ => U t ξ))
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) (ψ : H) :
    stoneCandidateGenerator (U := U) hUmul
        ⟨gardingVectorAt U (iteratedDeriv n (gaussianKernel ε)) ψ,
          gardingVectorAt_iteratedKernel_mem_stoneCandidateDomain hUmul hUunit hUcont n hε ψ⟩ =
      (Complex.I : ℂ) • gardingVectorAt U (iteratedDeriv (n + 1) (gaussianKernel ε)) ψ := by
  set hmem := gardingVectorAt_iteratedKernel_mem_stoneCandidateDomain hUmul hUunit hUcont n hε ψ
  have hspec := stoneCandidateDeriv_spec (U := U) hUmul
    (ψ := ⟨gardingVectorAt U (iteratedDeriv n (gaussianKernel ε)) ψ, hmem⟩)
  have hderiv_eq := hspec.unique
    (gardingVectorAt_iteratedKernel_hasDerivAt hUmul hUunit hUcont n hε ψ)
  refine (stoneCandidateGenerator_apply (U := U) hUmul
    ⟨gardingVectorAt U (iteratedDeriv n (gaussianKernel ε)) ψ, hmem⟩).trans ?_
  show (-Complex.I) • stoneCandidateDeriv hUmul
      (⟨gardingVectorAt U (iteratedDeriv n (gaussianKernel ε)) ψ, hmem⟩ :
        stoneCandidateDomain (U := U) hUmul) =
      Complex.I • gardingVectorAt U (iteratedDeriv (n + 1) (gaussianKernel ε)) ψ
  rw [hderiv_eq]
  have hneg : (∫ u : ℝ, ((-(iteratedDeriv (n + 1) (gaussianKernel ε) u) : ℝ) : ℂ) • U u ψ) =
      -(gardingVectorAt U (iteratedDeriv (n + 1) (gaussianKernel ε)) ψ) := by
    unfold gardingVectorAt
    rw [← MeasureTheory.integral_neg]
    congr 1
    funext u
    push_cast
    rw [neg_smul]
  rw [hneg, smul_neg, neg_smul, neg_neg]

include hUmul in
/-- **The full analytic-vector witness.** `analyticGardingVector U ε ψ` is a genuine
`LinearPMap.IsAnalyticVector` of `stoneCandidateGenerator`, for every strongly continuous
one-parameter unitary group `U` and every `ψ` — Milestone 1′ of
`STONE_GENERATOR_EXISTENCE_PLAN.md`, completed. -/
theorem analyticGardingVector_isAnalyticVector (hUunit : ∀ t, U t ∈ unitary (H →L[ℂ] H))
    (hUcont : ∀ ξ : H, Continuous (fun t : ℝ => U t ξ)) {ε : ℝ} (hε : 0 < ε) (ψ : H) :
    (stoneCandidateGenerator (U := U) hUmul).IsAnalyticVector (analyticGardingVector U ε ψ) := by
  set T := stoneCandidateGenerator (U := U) hUmul with hT_def
  set G : ℕ → H := fun n => gardingVectorAt U (iteratedDeriv n (gaussianKernel ε)) ψ with hG_def
  set hmem : ∀ n, G n ∈ T.domain := fun n =>
    gardingVectorAt_iteratedKernel_mem_stoneCandidateDomain hUmul hUunit hUcont n hε ψ with hmem_def
  set v : ℕ → T.domain := fun n => (Complex.I : ℂ) ^ n • (⟨G n, hmem n⟩ : T.domain) with hv_def
  have hGval : ∀ n, T ⟨G n, hmem n⟩ = (Complex.I : ℂ) • G (n + 1) :=
    fun n => stoneCandidateGenerator_gardingVectorAt_iteratedKernel hUmul hUunit hUcont n hε ψ
  have hv_coe : ∀ n, (v n : H) = (Complex.I : ℂ) ^ n • G n := fun n => by
    rw [hv_def]; simp
  have hG0 : G 0 = analyticGardingVector U ε ψ := by
    rw [hG_def]; simp [gardingVectorAt, analyticGardingVector]
  have hiter : IteratesSeq T (analyticGardingVector U ε ψ) v := by
    constructor
    · rw [hv_coe, pow_zero, one_smul, hG0]
    · intro n
      show (v (n + 1) : H) = T (v n)
      have hTv : T (v n) = (Complex.I : ℂ) ^ n • T ⟨G n, hmem n⟩ := by
        rw [hv_def]
        exact LinearPMap.map_smul T ((Complex.I : ℂ) ^ n) ⟨G n, hmem n⟩
      rw [hTv, hGval n, smul_smul, hv_coe, pow_succ]
  refine ⟨v, hiter, ?_⟩
  obtain ⟨C, hC_pos, hC⟩ := gaussianKernel_iteratedDeriv_L1_bound (ε := ε) hε
  set t : ℝ := 1 / (2 * (C + 1)) with ht_def
  have ht_pos : 0 < t := by rw [ht_def]; positivity
  have hCt : C * t < 1 := by
    have heq : C * t = C / (2 * (C + 1)) := by rw [ht_def]; ring
    rw [heq, div_lt_one (by positivity)]
    linarith
  refine ⟨t, ht_pos, ?_⟩
  have hGnorm : ∀ n, ‖G n‖ ≤ ‖ψ‖ * (C ^ (n + 1) * Real.sqrt n.factorial) := by
    intro n
    obtain ⟨hint, hbound⟩ := hC n
    have hnorm_le : ‖G n‖ ≤ ∫ u : ℝ, |iteratedDeriv n (gaussianKernel ε) u| * ‖ψ‖ := by
      rw [hG_def]
      unfold gardingVectorAt
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      refine integral_congr_ae (ae_of_all _ fun u => ?_)
      show ‖((iteratedDeriv n (gaussianKernel ε) u : ℝ) : ℂ) • U u ψ‖ =
        |iteratedDeriv n (gaussianKernel ε) u| * ‖ψ‖
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        ContinuousLinearMap.norm_map_of_mem_unitary (hUunit u)]
    calc ‖G n‖ ≤ ∫ u : ℝ, |iteratedDeriv n (gaussianKernel ε) u| * ‖ψ‖ := hnorm_le
      _ = (∫ u : ℝ, |iteratedDeriv n (gaussianKernel ε) u|) * ‖ψ‖ :=
          MeasureTheory.integral_mul_const _ _
      _ ≤ (C ^ (n + 1) * Real.sqrt n.factorial) * ‖ψ‖ :=
          mul_le_mul_of_nonneg_right hbound (norm_nonneg ψ)
      _ = ‖ψ‖ * (C ^ (n + 1) * Real.sqrt n.factorial) := by ring
  have hv_norm : ∀ n, ‖(v n : H)‖ = ‖G n‖ := fun n => by
    rw [hv_coe, norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
  have hterm_le : ∀ n, ‖(v n : H)‖ * t ^ n / n.factorial ≤ (‖ψ‖ * C) * (C * t) ^ n := by
    intro n
    have hnfact_pos : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    have hsqrt_le : Real.sqrt n.factorial ≤ n.factorial := by
      have h1 : (1 : ℝ) ≤ (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
      calc Real.sqrt (n.factorial : ℝ) ≤ Real.sqrt ((n.factorial : ℝ) * n.factorial) := by
            apply Real.sqrt_le_sqrt; nlinarith
        _ = n.factorial := by rw [← sq]; exact Real.sqrt_sq (by positivity)
    have hGn_le : ‖G n‖ ≤ ‖ψ‖ * (C ^ (n + 1) * n.factorial) := by
      calc ‖G n‖ ≤ ‖ψ‖ * (C ^ (n + 1) * Real.sqrt n.factorial) := hGnorm n
        _ ≤ ‖ψ‖ * (C ^ (n + 1) * n.factorial) := by gcongr
    rw [hv_norm, div_le_iff₀ hnfact_pos]
    calc ‖G n‖ * t ^ n ≤ (‖ψ‖ * (C ^ (n + 1) * n.factorial)) * t ^ n :=
          mul_le_mul_of_nonneg_right hGn_le (by positivity)
      _ = (‖ψ‖ * C) * (C * t) ^ n * n.factorial := by rw [mul_pow, pow_succ]; ring
  apply Summable.of_nonneg_of_le (fun n => by positivity) hterm_le
  exact Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) hCt)

end

end QuantumMechanics

