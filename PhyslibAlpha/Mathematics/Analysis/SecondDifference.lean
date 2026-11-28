/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# The symmetric second difference

The symmetric second difference of a real profile, and its Taylor limits: at a fixed centre for
`C^2` profiles, and along refinements whose sampled sites move.

## i. Overview

The symmetric second difference `(φ (x + h) - 2 φ x + φ (x - h)) / h^2` is the standard finite
difference approximation of the second derivative. For a `C^2` profile it tends to the second
derivative at the centre as the step tends to zero, which is Taylor's theorem at order two. The same
limit holds along any refinement whose sites tend to the centre and whose steps tend to zero, with
no relation between the rate of the site and the spacing: the Lagrange remainder form of Taylor's
theorem is applied at each moving centre, and continuity of the second derivative closes the limit.

These statements are pure analysis; the sampled residual of the AQUAL discrete action is the
application that motivates them.

## ii. Key results

- `secondDifference` : the symmetric second difference of a profile.
- `secondDifference_tendsto` : the `C^2` Taylor limit at a fixed centre.
- `secondDifference_tendsto_of_tendsto_site` : the limit along refinements with moving sites.

## iii. Table of contents

- A. The symmetric second difference
- B. The Taylor limits

## iv. References

* None.

-/

@[expose] public section

/-! ## A. The symmetric second difference -/

/-- The symmetric second difference of a profile. -/
noncomputable def secondDifference (φ : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (φ (x + h) - 2 * φ x + φ (x - h)) / h ^ 2

/-! ## B. The Taylor limits -/

private lemma taylorWithinEval_two (f : ℝ → ℝ) (x y : ℝ) :
    taylorWithinEval f 2 Set.univ x y =
      f x + (y - x) * deriv f x + (1 / 2) * (y - x) ^ 2 * deriv (deriv f) x := by
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp [iteratedDerivWithin_succ]

private lemma taylorWithinEval_one_eq (φ : ℝ → ℝ) (x₀ y : ℝ)
    (hφ : DifferentiableAt ℝ φ x₀) (hxy : x₀ ≠ y) :
    taylorWithinEval φ 1 (Set.uIcc x₀ y) x₀ y = φ x₀ + (y - x₀) * deriv φ x₀ := by
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, pow_zero, pow_one,
    iteratedDerivWithin_zero, iteratedDerivWithin_one]
  rw [hφ.derivWithin]
  · ring
  · exact (uniqueDiffOn_uIcc hxy).uniqueDiffWithinAt Set.left_mem_uIcc

private lemma secondDifference_eq_lagrange (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (x h : ℝ) (hh : h ≠ 0) :
    ∃ ξ η : ℝ, ξ ∈ Set.uIoo x (x + h) ∧ η ∈ Set.uIoo x (x - h) ∧
      secondDifference φ x h =
        (deriv (deriv φ) ξ + deriv (deriv φ) η) / 2 := by
  have hxp : x ≠ x + h := by intro hc; exact hh (by linarith)
  have hxm : x ≠ x - h := by intro hc; exact hh (by linarith)
  have hφ2 : ContDiffOn ℝ ((1 : ℕ) + 1) φ (Set.uIcc x (x + h)) := hφ.contDiffOn
  have hφ2' : ContDiffOn ℝ ((1 : ℕ) + 1) φ (Set.uIcc x (x - h)) := hφ.contDiffOn
  obtain ⟨ξ, hξ, hξeq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := φ) (x := x + h) (x₀ := x) (n := 1) hxp hφ2
  obtain ⟨η, hη, hηeq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := φ) (x := x - h) (x₀ := x) (n := 1) hxm hφ2'
  refine ⟨ξ, η, hξ, hη, ?_⟩
  have hφd : DifferentiableAt ℝ φ x := hφ.differentiable (by norm_num) x
  have htp := taylorWithinEval_one_eq φ x (x + h) hφd hxp
  have htm := taylorWithinEval_one_eq φ x (x - h) hφd hxm
  have hξ' : φ (x + h) = φ x + h * deriv φ x + deriv (deriv φ) ξ * h ^ 2 / 2 := by
    rw [htp] at hξeq
    have hξeq' : φ (x + h) - (φ x + h * deriv φ x) = deriv (deriv φ) ξ * h ^ 2 / 2 := by
      simpa [iteratedDeriv_succ, iteratedDeriv_one, Nat.factorial] using hξeq
    linarith
  have hη' : φ (x - h) = φ x - h * deriv φ x + deriv (deriv φ) η * h ^ 2 / 2 := by
    rw [htm] at hηeq
    have hηeq' : φ (x - h) - (φ x + (x - h - x) * deriv φ x)
        = deriv (deriv φ) η * h ^ 2 / 2 := by
      simpa [iteratedDeriv_succ, iteratedDeriv_one, Nat.factorial] using hηeq
    have hsub : x - h - x = -h := by ring
    rw [hsub] at hηeq'
    linarith
  rw [secondDifference, hξ', hη']
  field_simp [hh]
  ring

/-- The symmetric second difference of a `C^2` profile tends to the second
derivative at the centre.  This is Taylor's theorem at order two. -/
lemma secondDifference_tendsto (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) (x : ℝ) :
    Filter.Tendsto (fun h : ℝ => secondDifference φ x h)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (deriv (deriv φ) x)) := by
  let r : ℝ → ℝ := fun y => φ y - taylorWithinEval φ 2 Set.univ x y
  have ht : Filter.Tendsto (fun y : ℝ => ((y - x) ^ 2)⁻¹ • r y) (nhds x) (nhds 0) := by
    have h := taylor_tendsto (s := Set.univ) convex_univ (Set.mem_univ x) (n := 2)
      hφ.contDiffOn
    simpa [r] using h
  have hplus0 : Filter.Tendsto (fun h : ℝ => x + h) (nhds 0) (nhds x) := by
    have hc : Continuous fun h : ℝ => x + h := continuous_const.add continuous_id
    simpa using hc.tendsto (0 : ℝ)
  have hplus : Filter.Tendsto (fun h : ℝ => x + h)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds x) :=
    hplus0.mono_left nhdsWithin_le_nhds
  have hminus0 : Filter.Tendsto (fun h : ℝ => x - h) (nhds 0) (nhds x) := by
    have hc : Continuous fun h : ℝ => x - h := continuous_const.sub continuous_id
    simpa using hc.tendsto (0 : ℝ)
  have hminus : Filter.Tendsto (fun h : ℝ => x - h)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds x) :=
    hminus0.mono_left nhdsWithin_le_nhds
  have hp : Filter.Tendsto (fun h : ℝ => r (x + h) / h ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    have h := ht.comp hplus
    convert h using 1
    ext h
    simp only [Function.comp_apply]
    ring_nf
  have hm : Filter.Tendsto (fun h : ℝ => r (x - h) / h ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    have h := ht.comp hminus
    convert h using 1
    ext h
    simp only [Function.comp_apply]
    ring_nf
  have hsum : Filter.Tendsto (fun h : ℝ => (r (x + h) + r (x - h)) / h ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    have h := hp.add hm
    convert h using 1
    · ext h
      ring_nf
    · simp
  have htarget : Filter.Tendsto
      (fun h : ℝ => deriv (deriv φ) x + (r (x + h) + r (x - h)) / h ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (deriv (deriv φ) x)) := by
    simpa [Pi.add_apply] using (tendsto_const_nhds (x := deriv (deriv φ) x)).add hsum
  have hsd : ∀ᶠ h in nhdsWithin (0 : ℝ) ({0}ᶜ),
      secondDifference φ x h = deriv (deriv φ) x + (r (x + h) + r (x - h)) / h ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [r]
    rw [secondDifference, taylorWithinEval_two φ x (x + h), taylorWithinEval_two φ x (x - h)]
    have hh0 : h ≠ 0 := by simpa using hh
    field_simp [hh0]
    ring
  exact htarget.congr' (hsd.mono fun h hh => hh.symm)

/-- The symmetric second difference of a `C^2` profile tends to the second
derivative at the centre, along any refinement whose sampled sites tend to the
centre.  The proof uses Taylor's theorem with the Lagrange remainder at each
moving centre, so no relation between the rate of the site and the spacing is
needed. -/
lemma secondDifference_tendsto_of_tendsto_site (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    {ι : Type*} {l : Filter ι} {x : ℝ} (h : ι → ℝ) (i : ι → ℕ)
    (hh : ∀ k, h k ≠ 0)
    (hh0 : Filter.Tendsto h l (nhdsWithin (0 : ℝ) ({0}ᶜ)))
    (hx : Filter.Tendsto (fun k => (i k : ℝ) * h k) l (nhds x)) :
    Filter.Tendsto (fun k => secondDifference φ ((i k : ℝ) * h k) (h k))
      l (nhds (deriv (deriv φ) x)) := by
  let xk : ι → ℝ := fun k => (i k : ℝ) * h k
  have hx' : Filter.Tendsto xk l (nhds x) := hx
  classical
  choose ξ η hξ hη heq using fun k =>
    secondDifference_eq_lagrange φ hφ (xk k) (h k) (hh k)
  have hξclose : ∀ k, |ξ k - xk k| ≤ |h k| := by
    intro k
    have hmem : ξ k ∈ Set.uIcc (xk k) (xk k + h k) := Set.Ioo_subset_Icc_self (hξ k)
    simpa using Set.abs_sub_left_of_mem_uIcc hmem
  have hηclose : ∀ k, |η k - xk k| ≤ |h k| := by
    intro k
    have hmem : η k ∈ Set.uIcc (xk k) (xk k - h k) := Set.Ioo_subset_Icc_self (hη k)
    simpa using Set.abs_sub_left_of_mem_uIcc hmem
  have hhab : Filter.Tendsto (fun k => |h k|) l (nhds 0) := by
    simpa [Function.comp_def, abs_zero] using
      (continuous_abs.tendsto 0).comp (hh0.mono_right nhdsWithin_le_nhds)
  have hξt : Filter.Tendsto ξ l (nhds x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (f := fun k => ‖ξ k - x‖)
      (g := fun k => |h k| + |xk k - x|) (fun k => abs_nonneg _) (fun k => ?_) ?_
    · rw [Real.norm_eq_abs]
      calc |ξ k - x| = |(ξ k - xk k) + (xk k - x)| := by ring_nf
        _ ≤ |ξ k - xk k| + |xk k - x| := abs_add_le _ _
        _ ≤ |h k| + |xk k - x| := add_le_add (hξclose k) le_rfl
    · have h2 : Filter.Tendsto (fun k => |xk k - x|) l (nhds 0) := by
        simpa using (hx'.sub_const x).abs
      simpa using hhab.add h2
  have hηt : Filter.Tendsto η l (nhds x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (f := fun k => ‖η k - x‖)
      (g := fun k => |h k| + |xk k - x|) (fun k => abs_nonneg _) (fun k => ?_) ?_
    · rw [Real.norm_eq_abs]
      calc |η k - x| = |(η k - xk k) + (xk k - x)| := by ring_nf
        _ ≤ |η k - xk k| + |xk k - x| := abs_add_le _ _
        _ ≤ |h k| + |xk k - x| := add_le_add (hηclose k) le_rfl
    · have h2 : Filter.Tendsto (fun k => |xk k - x|) l (nhds 0) := by
        simpa using (hx'.sub_const x).abs
      simpa using hhab.add h2
  have hcont2 : Continuous (deriv (deriv φ)) := by
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using
      hφ.continuous_iteratedDeriv 2 (by norm_num)
  have hξlim : Filter.Tendsto (fun k => deriv (deriv φ) (ξ k)) l
      (nhds (deriv (deriv φ) x)) := hcont2.tendsto x |> fun h => h.comp hξt
  have hηlim : Filter.Tendsto (fun k => deriv (deriv φ) (η k)) l
      (nhds (deriv (deriv φ) x)) := hcont2.tendsto x |> fun h => h.comp hηt
  have hhalf := (hξlim.add hηlim).div_const 2
  have hhalf' : Filter.Tendsto
      (fun k => (deriv (deriv φ) (ξ k) + deriv (deriv φ) (η k)) / 2)
      l (nhds (deriv (deriv φ) x)) := by
    convert hhalf using 1
    ring_nf
  refine hhalf'.congr' (Filter.Eventually.of_forall fun k => ?_)
  exact (heq k).symm
