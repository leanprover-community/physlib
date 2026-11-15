/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Distribution.ExpTwist
public import Mathlib.Analysis.Distribution.TestFunction

/-!

# Exponential twists on test functions

Conjugating a continuous linear operator on test functions by the exponential twist moves its
values by `O (|a|)` in every derivative.

## i. Overview

The twist `x ↦ exp (a ℓ x)` multiplies a test function. The derivatives of a test function are
bounded continuous functions, and `iterDerivCLM` makes them a continuous linear map. A
distribution of finite order is bounded on a fixed compact set by finitely many of these norms.
Together with the estimates for the twist this gives the convergence
`T (M_a C M_{-a} φ) → T (C φ)` for a continuous linear `C` with values in a fixed ball.

## ii. Key results

- `ExpTwist.twistCLM` : the multiplication by the twist as a map of test functions.
- `ExpTwist.iterDerivCLM` : the `k`-th derivative as a continuous linear map to bounded functions.
- `ExpTwist.tendsto_twistCLM` : the twisted test function tends to the test function.
- `ExpTwist.exists_bound_of_tsupport_subset` : a distribution has finite order on a compact set.
- `ExpTwist.tendsto_distribution_twist` : the conjugation limit.

## iii. Table of contents

- A. Test functions and their derivatives
- B. Estimates for the twist
- C. The conjugation limit

## iv. References

None.

## A. Test functions and their derivatives

- `ExpTwist.twistCLM` : the multiplication by the twist.
- `ExpTwist.iterDerivCLM` : the `k`-th derivative as a continuous linear map.

## B. Estimates for the twist

- `ExpTwist.dnorm_twistCLM_sub_le` : the derivatives of `M_a φ - φ`.
- `ExpTwist.tendsto_twistCLM` : convergence in the test function topology.
- `ExpTwist.exists_bound_of_tsupport_subset` : finite order on a compact set.

## C. The conjugation limit

- `ExpTwist.tendsto_distribution_twist` : the conjugation limit.
-/

@[expose] public section

noncomputable section

open scoped Distributions ContDiff BoundedContinuousFunction
open TopologicalSpace

namespace ExpTwist

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ℓ : E →L[ℝ] ℝ)

/-- Multiplication of a test function by the twist. -/
def twistCLM (a : ℝ) : 𝓓((⊤ : Opens E), ℝ) →L[ℝ] 𝓓((⊤ : Opens E), ℝ) :=
  TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) (contDiff_twist ℓ a)

lemma twistCLM_apply (a : ℝ) (φ : 𝓓((⊤ : Opens E), ℝ)) (x : E) :
    twistCLM ℓ a φ x = φ x * twist ℓ a x := rfl

variable (E) in
/-- The `k`-th derivative of a test function as a bounded continuous function. -/
def iterDerivCLM (k : ℕ) : 𝓓((⊤ : Opens E), ℝ) →L[ℝ] (E →ᵇ (E [×k]→L[ℝ] ℝ)) :=
  haveI : IsTopologicalAddGroup (E →ᵇ (E [×k]→L[ℝ] ℝ)) := by
    convert (inferInstance : NormedAddCommGroup
      (E →ᵇ (E [×k]→L[ℝ] ℝ))).toSeminormedAddCommGroup.toIsTopologicalAddGroup
  haveI : LocallyConvexSpace ℝ (E →ᵇ (E [×k]→L[ℝ] ℝ)) := by
    convert (NormedSpace.toLocallyConvexSpace (E := E →ᵇ (E [×k]→L[ℝ] ℝ)))
  TestFunction.limitCLM ℝ (Ω := (⊤ : Opens E)) (F := ℝ) (n := ⊤)
    (V := E →ᵇ (E [×k]→L[ℝ] ℝ))
    (fun φ => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤
      (K := ⟨tsupport φ, φ.hasCompactSupport⟩) k
      (ContDiffMapSupportedIn.of_support_subset φ.contDiff subset_closure))
    (fun K _ => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (K := K) k)
    (fun K _ f => by
      refine DFunLike.ext _ _ fun x => ?_
      simp
      rfl)

lemma iterDerivCLM_apply (k : ℕ) (φ : 𝓓((⊤ : Opens E), ℝ)) (x : E) :
    iterDerivCLM E k φ x = iteratedFDeriv ℝ k φ x := by
  simp [iterDerivCLM]
  rfl

lemma norm_iteratedFDeriv_le_iterDerivCLM (k : ℕ) (φ : 𝓓((⊤ : Opens E), ℝ)) (x : E) :
    ‖iteratedFDeriv ℝ k φ x‖ ≤ ‖iterDerivCLM E k φ‖ := by
  rw [← iterDerivCLM_apply]
  exact BoundedContinuousFunction.norm_coe_le_norm _ _

lemma norm_iterDerivCLM_le (k : ℕ) (φ : 𝓓((⊤ : Opens E), ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖iteratedFDeriv ℝ k φ x‖ ≤ C) : ‖iterDerivCLM E k φ‖ ≤ C := by
  refine (BoundedContinuousFunction.norm_le hC).2 fun x => ?_
  rw [iterDerivCLM_apply]
  exact h x


/-- The constant in the twist estimate. -/
def twistConst (R : ℝ) (k : ℕ) : ℝ :=
  2 ^ k * ((1 + R) * (1 + ‖ℓ‖) ^ (k + 1) * Real.exp (‖ℓ‖ * R))

lemma dnorm_twistCLM_sub_le {a R : ℝ} (hR : 0 ≤ R) (ha : |a| ≤ 1) (φ : 𝓓((⊤ : Opens E), ℝ))
    (hs : tsupport φ ⊆ Metric.closedBall 0 R) (k : ℕ) :
    ‖iterDerivCLM E k (twistCLM ℓ a φ - φ)‖ ≤
      |a| * twistConst ℓ R k * ∑ j ∈ Finset.range (k + 1), ‖iterDerivCLM E j φ‖ := by
  set S := ∑ j ∈ Finset.range (k + 1), ‖iterDerivCLM E j φ‖ with hSdef
  have hS : ∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j φ y‖ ≤ S := fun j hj y =>
    (norm_iteratedFDeriv_le_iterDerivCLM j φ y).trans
      (Finset.single_le_sum (f := fun j => ‖iterDerivCLM E j φ‖) (fun _ _ => by positivity)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hc : 0 ≤ |a| * twistConst ℓ R k * S := by
    unfold twistConst; positivity
  refine norm_iterDerivCLM_le k _ hc fun x => ?_
  have hfun : ⇑(twistCLM ℓ a φ - φ) = fun y => twist ℓ a y * φ y - φ y := by
    funext y
    simp [twistCLM_apply, mul_comm]
  rw [hfun]
  have := norm_iteratedFDeriv_twist_mul_sub_le ℓ hR ha φ φ.contDiff hs k hS x
  convert this using 1
  unfold twistConst
  ring


lemma tendsto_twistCLM (φ : 𝓓((⊤ : Opens E), ℝ)) :
    Filter.Tendsto (fun a : ℝ => twistCLM ℓ a φ) (nhds 0) (nhds φ) := by
  obtain ⟨R₀, hR₀⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : E)
  set R := max R₀ 0 with hRdef
  have hR : 0 ≤ R := le_max_right _ _
  have hs : tsupport φ ⊆ Metric.closedBall 0 R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  set K : Compacts E := ⟨tsupport φ, φ.hasCompactSupport⟩ with hK
  have hKΩ : (K : Set E) ⊆ ((⊤ : Opens E) : Set E) := fun _ _ => trivial
  set φK : 𝓓_{K}(E, ℝ) := ContDiffMapSupportedIn.of_support_subset φ.contDiff subset_closure
  let U : ℝ → 𝓓_{K}(E, ℝ) := fun a =>
    ContDiffMapSupportedIn.bilinLeftCLM (𝕜 := ℝ) (n := ⊤) (K := K) (ContinuousLinearMap.mul ℝ ℝ)
      (contDiff_twist ℓ a) φK
  have hU : ∀ a, twistCLM ℓ a φ = TestFunction.ofSupportedIn hKΩ (U a) := fun a => by
    ext x; rfl
  have hφ : φ = TestFunction.ofSupportedIn hKΩ φK := by ext x; rfl
  have hT : Filter.Tendsto U (nhds 0) (nhds φK) := by
    rw [(ContDiffMapSupportedIn.withSeminorms ℝ E ℝ ⊤ K).tendsto_nhds]
    intro i
    have hnorm : ∀ a, (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K i) (U a - φK) =
        ‖iterDerivCLM E i (twistCLM ℓ a φ - φ)‖ := fun a => by
      rw [ContDiffMapSupportedIn.seminorm_apply]
      congr 1
    have hfn : (fun a : ℝ => (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K i) (U a - φK)) =
        fun a => ‖iterDerivCLM E i (twistCLM ℓ a φ - φ)‖ := funext hnorm
    have hlim : Filter.Tendsto (fun a : ℝ => |a| * twistConst ℓ R i *
        ∑ j ∈ Finset.range (i + 1), ‖iterDerivCLM E j φ‖) (nhds 0) (nhds 0) := by
      have : Continuous fun a : ℝ => |a| * twistConst ℓ R i *
          ∑ j ∈ Finset.range (i + 1), ‖iterDerivCLM E j φ‖ := by fun_prop
      simpa using this.tendsto 0
    have key : Filter.Tendsto (fun a : ℝ => (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K i)
        (U a - φK)) (nhds 0) (nhds 0) := by
      rw [hfn]
      refine squeeze_zero' (Filter.Eventually.of_forall fun a => by positivity) ?_ hlim
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with a ha
      exact dnorm_twistCLM_sub_le ℓ hR (by simpa using ha.out.le) φ hs i
    intro ε hε
    exact key.eventually (gt_mem_nhds hε)
  have h2 : Filter.Tendsto (fun a => TestFunction.ofSupportedIn hKΩ (U a)) (nhds 0)
      (nhds (TestFunction.ofSupportedIn hKΩ φK)) :=
    ((TestFunction.continuous_ofSupportedIn hKΩ).tendsto φK).comp hT
  rw [← hφ] at h2
  have e1 : (fun a : ℝ => twistCLM ℓ a φ) = fun a => TestFunction.ofSupportedIn hKΩ (U a) :=
    funext hU
  rw [e1]
  exact h2


/-- **Finite order.** A distribution is bounded on test functions supported in a compact set by
finitely many sup norms of derivatives. -/
lemma exists_bound_of_tsupport_subset (T : 𝓓((⊤ : Opens E), ℝ) →L[ℝ] ℝ) (K : Compacts E) :
    ∃ (N : ℕ) (c : ℝ), 0 ≤ c ∧ ∀ w : 𝓓((⊤ : Opens E), ℝ), tsupport w ⊆ K →
      |T w| ≤ c * ∑ k ∈ Finset.range (N + 1), ‖iterDerivCLM E k w‖ := by
  have hKΩ : (K : Set E) ⊆ ((⊤ : Opens E) : Set E) := fun _ _ => trivial
  let Ψ : 𝓓_{K}(E, ℝ) →L[ℝ] ℝ := T.comp (TestFunction.ofSupportedInCLM ℝ hKΩ)
  let q : Seminorm ℝ 𝓓_{K}(E, ℝ) := (normSeminorm ℝ ℝ).comp Ψ.toLinearMap
  have hq : Continuous q := continuous_norm.comp Ψ.continuous
  obtain ⟨s, C, hC0, hC⟩ :=
    Seminorm.bound_of_continuous (ContDiffMapSupportedIn.withSeminorms ℝ E ℝ ⊤ K) q hq
  refine ⟨s.sup id, C, C.coe_nonneg, fun w hw => ?_⟩
  let wK : 𝓓_{K}(E, ℝ) := ContDiffMapSupportedIn.of_support_subset w.contDiff
    (subset_closure.trans hw)
  have hw' : TestFunction.ofSupportedIn hKΩ wK = w := by ext x; rfl
  have h1 : |T w| ≤ C * (s.sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) wK := by
    have := hC wK
    have h3 : q wK = |T w| := by simp [q, Ψ, hw']
    rw [← h3]
    refine this.trans ?_
    rw [smul_apply, NNReal.smul_def, smul_eq_mul]
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ C.coe_nonneg)
  refine Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => by positivity) fun k hk => ?_
  have hk' : k ≤ s.sup id := Finset.le_sup (f := id) hk
  have heq : ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K k wK = ‖iterDerivCLM E k w‖ := by
    rw [ContDiffMapSupportedIn.seminorm_apply]
    congr 1
  rw [heq]
  exact Finset.single_le_sum (f := fun k => ‖iterDerivCLM E k w‖) (fun _ _ => by positivity)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hk'))


variable (E) in
/-- The sum of the sup norms of the derivatives up to the order `N`. -/
def dsum (N : ℕ) (w : 𝓓((⊤ : Opens E), ℝ)) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), ‖iterDerivCLM E k w‖

lemma dsum_nonneg (N : ℕ) (w : 𝓓((⊤ : Opens E), ℝ)) : 0 ≤ dsum E N w :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma dsum_add_le (N : ℕ) (v w : 𝓓((⊤ : Opens E), ℝ)) :
    dsum E N (v + w) ≤ dsum E N v + dsum E N w := by
  unfold dsum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [map_add]
  exact norm_add_le (iterDerivCLM E k v) (iterDerivCLM E k w)

lemma dsum_neg (N : ℕ) (w : 𝓓((⊤ : Opens E), ℝ)) : dsum E N (-w) = dsum E N w := by
  unfold dsum
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_neg]
  exact norm_neg (iterDerivCLM E k w)

lemma dsum_twistCLM_sub_le {a R : ℝ} (hR : 0 ≤ R) (ha : |a| ≤ 1) (N : ℕ)
    (φ : 𝓓((⊤ : Opens E), ℝ)) (hs : tsupport φ ⊆ Metric.closedBall 0 R) :
    dsum E N (twistCLM ℓ a φ - φ) ≤
      |a| * (∑ k ∈ Finset.range (N + 1), twistConst ℓ R k) * dsum E N φ := by
  unfold dsum
  calc ∑ k ∈ Finset.range (N + 1), ‖iterDerivCLM E k (twistCLM ℓ a φ - φ)‖
      ≤ ∑ k ∈ Finset.range (N + 1),
          |a| * twistConst ℓ R k * ∑ j ∈ Finset.range (N + 1), ‖iterDerivCLM E j φ‖ := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkN : k ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        refine (dnorm_twistCLM_sub_le ℓ hR ha φ hs k).trans ?_
        have htc : 0 ≤ |a| * twistConst ℓ R k := by unfold twistConst; positivity
        refine mul_le_mul_of_nonneg_left ?_ htc
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (Nat.succ_le_succ hkN)) fun _ _ _ => by positivity
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]


lemma tsupport_twistCLM_subset (a : ℝ) (g : 𝓓((⊤ : Opens E), ℝ)) :
    tsupport ⇑(twistCLM ℓ a g) ⊆ tsupport g :=
  tsupport_mul_subset_left (f := ⇑g) (g := twist ℓ a)

/-- **Conjugation by the twist.** For a continuous linear `C` with values supported in a ball and
a distribution `T`, the twisted values `T (M_a C M_{-a} φ)` converge to `T (C φ)`. -/
lemma tendsto_distribution_twist [ProperSpace E] (T : 𝓓((⊤ : Opens E), ℝ) →L[ℝ] ℝ)
    (C : 𝓓((⊤ : Opens E), ℝ) →L[ℝ] 𝓓((⊤ : Opens E), ℝ)) (φ : 𝓓((⊤ : Opens E), ℝ)) {R : ℝ}
    (hR : 0 ≤ R) (hC : ∀ g, tsupport ⇑(C g) ⊆ Metric.closedBall 0 R) :
    Filter.Tendsto (fun a : ℝ => T (twistCLM ℓ a (C (twistCLM ℓ (-a) φ)))) (nhds 0)
      (nhds (T (C φ))) := by
  obtain ⟨N, c, hc0, hc⟩ := exists_bound_of_tsupport_subset T
    ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R⟩
  set γ := ∑ k ∈ Finset.range (N + 1), twistConst ℓ R k with hγ
  have hγ0 : 0 ≤ γ := Finset.sum_nonneg fun k _ => by unfold twistConst; positivity
  -- convergence of the derivatives of `C (M_{-a} φ)`
  have h1 : Filter.Tendsto (fun a : ℝ => twistCLM ℓ (-a) φ) (nhds 0) (nhds φ) := by
    have hneg : Filter.Tendsto (fun a : ℝ => -a) (nhds 0) (nhds 0) := by
      simpa using (continuous_neg (G := ℝ)).tendsto (0 : ℝ)
    exact (tendsto_twistCLM ℓ φ).comp hneg
  have h2 : Filter.Tendsto (fun a : ℝ => dsum E N (C (twistCLM ℓ (-a) φ) - C φ)) (nhds 0)
      (nhds 0) := by
    unfold dsum
    have : ∀ k, Filter.Tendsto (fun a : ℝ => ‖iterDerivCLM E k (C (twistCLM ℓ (-a) φ) - C φ)‖)
        (nhds 0) (nhds 0) := fun k => by
      have hk := ((iterDerivCLM E k).comp C).continuous.tendsto φ
      have hk2 := hk.comp h1
      have key : Filter.Tendsto (fun a : ℝ => ‖iterDerivCLM E k (C (twistCLM ℓ (-a) φ)) -
          iterDerivCLM E k (C φ)‖) (nhds 0) (nhds 0) := by
        have := hk2
        rw [tendsto_iff_dist_tendsto_zero] at this
        refine this.congr fun a => ?_
        exact dist_eq_norm (iterDerivCLM E k (C (twistCLM ℓ (-a) φ))) (iterDerivCLM E k (C φ))
      simpa [map_sub] using key
    simpa using tendsto_finsetSum _ fun k _ => this k
  have hsupp : ∀ a, tsupport ⇑(twistCLM ℓ a (C (twistCLM ℓ (-a) φ)) - C φ) ⊆
      Metric.closedBall 0 R := fun a =>
    (tsupport_sub _ _).trans (Set.union_subset
      ((tsupport_twistCLM_subset ℓ a _).trans (hC _)) (hC _))
  have hsupp' : ∀ a, tsupport ⇑(C (twistCLM ℓ (-a) φ) - C φ) ⊆ Metric.closedBall 0 R := fun a =>
    (tsupport_sub _ _).trans (Set.union_subset (hC _) (hC _))
  have hbound : ∀ᶠ a in nhds (0 : ℝ), |T (twistCLM ℓ a (C (twistCLM ℓ (-a) φ))) - T (C φ)| ≤
      c * (|a| * γ * dsum E N (C (twistCLM ℓ (-a) φ) - C φ) +
        dsum E N (C (twistCLM ℓ (-a) φ) - C φ) + |a| * γ * dsum E N (C φ)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with a ha
    have ha1 : |a| ≤ 1 := by simpa using ha.out.le
    set u := C (twistCLM ℓ (-a) φ) with hu
    set v := u - C φ with hv
    have hw : twistCLM ℓ a u - C φ = (twistCLM ℓ a v - v) + v + (twistCLM ℓ a (C φ) - C φ) := by
      simp only [hv, map_sub]; abel
    have hT : T (twistCLM ℓ a u) - T (C φ) = T (twistCLM ℓ a u - C φ) := (map_sub T _ _).symm
    rw [hT]
    have hsw : tsupport ⇑(twistCLM ℓ a u - C φ) ⊆ Metric.closedBall 0 R := hsupp a
    refine (hc _ hsw).trans (mul_le_mul_of_nonneg_left ?_ hc0)
    have hA := dsum_twistCLM_sub_le ℓ hR ha1 N v (hsupp' a)
    have hB := dsum_twistCLM_sub_le ℓ hR ha1 N (C φ) (hC φ)
    rw [← hγ] at hA hB
    rw [hw]
    refine (dsum_add_le _ _ _).trans ?_
    have := dsum_add_le N (twistCLM ℓ a v - v) v
    linarith [dsum_add_le N (twistCLM ℓ a v - v + v) (twistCLM ℓ a (C φ) - C φ)]
  have habs : Filter.Tendsto (fun a : ℝ => |a| * γ) (nhds 0) (nhds 0) := by
    have : Continuous fun a : ℝ => |a| * γ := by fun_prop
    simpa using this.tendsto 0
  have hlim : Filter.Tendsto (fun a : ℝ => c * (|a| * γ * dsum E N (C (twistCLM ℓ (-a) φ) - C φ) +
        dsum E N (C (twistCLM ℓ (-a) φ) - C φ) + |a| * γ * dsum E N (C φ))) (nhds 0) (nhds 0) := by
    have := ((habs.mul h2).add h2).add (habs.mul_const (dsum E N (C φ)))
    simpa using this.const_mul c
  have hz : Filter.Tendsto (fun a : ℝ => T (twistCLM ℓ a (C (twistCLM ℓ (-a) φ))) - T (C φ))
      (nhds 0) (nhds 0) :=
    squeeze_zero_norm' (hbound.mono fun a ha => by simpa using ha) hlim
  simpa using hz.add_const (T (C φ))

end ExpTwist
