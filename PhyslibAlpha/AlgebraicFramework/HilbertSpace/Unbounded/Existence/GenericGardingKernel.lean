/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Existence.CandidateGenerator
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Group.Integral

/-!
# The Gårding-vector commutation identity for a generic smooth kernel

Milestone 2 of Track A (`STONE_GENERATOR_EXISTENCE_PLAN.md`): `GardingVectors.lean` proves
the single-derivative commutation identity `stoneCandidateGenerator_analyticGardingVector` for the
*specific* kernel `gaussianKernel ε`, via a differentiation-under-the-integral-sign argument
(`analyticGardingVector_hasDerivAt`) whose proof only ever uses four structural facts about the
kernel: it is continuous, it has an everywhere-defined derivative, that derivative is dominated
locally (near a shift `x` in a bounded neighborhood of `0`) by an integrable function, and the
kernel itself is integrable against `t ↦ U t ψ`. This file factors that argument out to apply to
*any* kernel `k` satisfying those four properties, so that assembling the full
`IsAnalyticVector` witness (which needs the *same* argument applied to `k := iteratedDeriv n
(gaussianKernel ε)` at every order `n`) does not need to re-derive
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`'s application from scratch at each order — only
the four hypotheses need to be checked for `iteratedDeriv n (gaussianKernel ε)`, which is genuine
new work (`GaussianKernelGrowth.lean`'s companion file) but is now decoupled from this
differentiation-under-the-integral machinery itself.

## Main results

- `gardingVectorAt` : the Gårding vector of `ψ` against a generic kernel `k`.
- `gardingVectorAt_translate` : the algebraic translation identity, for any `k`.
- `gardingVectorAt_hasDerivAt` : the differentiation-under-the-integral commutation identity, for
  any kernel `k` satisfying the four structural hypotheses above.
-/

@[expose] public section

namespace QuantumMechanics

noncomputable section

open scoped InnerProductSpace Topology
open MeasureTheory Filter

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U : ℝ → H →L[ℂ] H} (hUmul : ∀ s t, U (s + t) = U s * U t)

variable (U) in
/-- The Gårding vector of `ψ` against a generic (real-valued) kernel `k`, generalizing
`analyticGardingVector U ε ψ = gardingVectorAt U (gaussianKernel ε) ψ`. -/
def gardingVectorAt (k : ℝ → ℝ) (ψ : H) : H := ∫ t : ℝ, (k t : ℂ) • U t ψ

include hUmul in
/-- The algebraic translation identity for a generic kernel: `U s` applied to `gardingVectorAt k ψ`
is again a Gårding vector, of the kernel `k` shifted by `s`. Exactly
`analyticGardingVector_translate`'s proof with `gaussianKernel ε` replaced by an arbitrary `k`
(nothing in that proof used any special property of the Gaussian). -/
theorem gardingVectorAt_translate (k : ℝ → ℝ) (ψ : H)
    (hk_integrable : Integrable (fun t : ℝ => (k t : ℂ) • U t ψ)) (s : ℝ) :
    U s (gardingVectorAt U k ψ) = ∫ u : ℝ, (k (u - s) : ℂ) • U u ψ := by
  unfold gardingVectorAt
  rw [← ContinuousLinearMap.integral_comp_comm (U s) hk_integrable]
  have hpt : ∀ t : ℝ, U s ((k t : ℂ) • U t ψ) = (k t : ℂ) • U (t + s) ψ := by
    intro t
    rw [ContinuousLinearMap.map_smul]
    congr 1
    rw [← mul_apply_eq_comp, ← hUmul s t, add_comm s t]
  simp_rw [hpt]
  rw [← integral_add_right_eq_self (fun u : ℝ => (k (u - s) : ℂ) • U u ψ) s]
  simp only [add_sub_cancel_right]

include hUmul in
/-- **The generic commutation-identity engine.** If a kernel `k` is continuous, has an everywhere
`HasDerivAt` derivative `k'` which is itself continuous, is integrable against `t ↦ U t ψ`, and
`k'` is dominated near a shift `x ∈ (-1,1)` by a fixed integrable function of `u`, then the orbit
`s ↦ U s (gardingVectorAt U k ψ)` is differentiable at `0` with derivative
`∫ u, -k' u • U u ψ` — exactly `analyticGardingVector_hasDerivAt`'s conclusion, with `gaussianKernel
ε` replaced by `k` throughout. The proof is verbatim the same differentiation-under-the-integral
argument (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`), so this lemma need only be proved
once. -/
theorem gardingVectorAt_hasDerivAt (hUunit : ∀ t, U t ∈ unitary (H →L[ℂ] H))
    (hUcont : ∀ ξ : H, Continuous (fun t : ℝ => U t ξ)) (k k' : ℝ → ℝ)
    (hk_cont : Continuous k) (hk'_cont : Continuous k') (hk_deriv : ∀ t, HasDerivAt k (k' t) t)
    (ψ : H) (hk_integrable : Integrable (fun t : ℝ => (k t : ℂ) • U t ψ))
    (bound : ℝ → ℝ) (hbound_int : Integrable bound)
    (hbound : ∀ u : ℝ, ∀ x ∈ Metric.ball (0 : ℝ) 1, |k' (u - x)| * ‖ψ‖ ≤ bound u) :
    HasDerivAt (fun s : ℝ => U s (gardingVectorAt U k ψ))
      (∫ u : ℝ, ((-(k' u) : ℝ) : ℂ) • U u ψ) 0 := by
  -- The orbit function, rewritten via the translation identity.
  have horbit : (fun s : ℝ => U s (gardingVectorAt U k ψ)) =
      fun s : ℝ => ∫ u : ℝ, (k (u - s) : ℂ) • U u ψ :=
    funext (gardingVectorAt_translate hUmul k ψ hk_integrable)
  -- Per-point derivative in `s`, for every `u`, at every `s`.
  have hpt_deriv : ∀ u s : ℝ, HasDerivAt (fun s : ℝ => (k (u - s) : ℂ) • U u ψ)
      (((-(k' (u - s)) : ℝ) : ℂ) • U u ψ) s := by
    intro u s
    have hf1 := hk_deriv (u - s)
    have hcomp : HasDerivAt (fun s : ℝ => u - s) (-1 : ℝ) s := (hasDerivAt_id s).const_sub u
    have hg : HasDerivAt (fun s : ℝ => k (u - s)) (k' (u - s) * (-1)) s := hf1.comp s hcomp
    have hgcs := hg.ofReal_comp.smul_const (U u ψ)
    have heq : ((-(k' (u - s)) : ℝ) : ℂ) • U u ψ = ((k' (u - s) * (-1) : ℝ) : ℂ) • U u ψ := by
      congr 1; push_cast; ring
    rw [heq]; exact hgcs
  -- Continuity facts feeding measurability.
  have hFmeas : ∀ s : ℝ, Continuous (fun u : ℝ => (k (u - s) : ℂ) • U u ψ) := by
    intro s
    have h1 : Continuous (fun u : ℝ => (k (u - s) : ℂ)) := by fun_prop
    exact h1.smul (hUcont ψ)
  have hF'meas : Continuous (fun u : ℝ => ((-(k' u) : ℝ) : ℂ) • U u ψ) := by
    have h1 : Continuous (fun u : ℝ => ((-(k' u) : ℝ) : ℂ)) := by fun_prop
    exact h1.smul (hUcont ψ)
  -- Assemble via the dominated-derivative theorem.
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s u : ℝ => (k (u - s) : ℂ) • U u ψ)
    (F' := fun s u : ℝ => ((-(k' (u - s)) : ℝ) : ℂ) • U u ψ)
    (x₀ := (0 : ℝ)) (bound := bound)
    (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall (fun s => (hFmeas s).aestronglyMeasurable))
    (by simpa using hk_integrable)
    (by simpa using hF'meas.aestronglyMeasurable)
    (ae_of_all _ (fun u => fun x hx => by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        ContinuousLinearMap.norm_map_of_mem_unitary (hUunit u)]
      exact hbound u x hx))
    hbound_int
    (ae_of_all _ (fun u => fun x _ => hpt_deriv u x))
  rw [← horbit] at hderiv
  simpa only [sub_zero] using hderiv

end

end QuantumMechanics
