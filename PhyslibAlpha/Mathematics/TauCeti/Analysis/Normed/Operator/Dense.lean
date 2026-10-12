/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Extending bounded-operator convergence from dense subsets

This file records two standard density arguments for uniformly bounded families of continuous linear
maps between seminormed spaces.

## i. Overview

This file records two standard density arguments for uniformly bounded families of continuous
linear maps between seminormed spaces. Pointwise convergence on a dense subset extends to
pointwise convergence everywhere, and uniform Cauchy convergence on a parameter set does likewise.
Both rest on the same estimate
`ContinuousLinearMap.norm_sub_apply_le_of_norm_le`, which moves the point at which a
difference of two uniformly bounded operators is evaluated to a nearby point of the dense subset.

## ii. Key results

This file proves the statement described in the overview.

## iii. Table of contents

- A. Development

## iv. References

* Standard material; the statements and proofs are original to this formalization.
-/

public section

/-! ## A. Development -/

namespace ContinuousLinearMap

open Filter

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]


/-- Comparing two continuous linear maps of norm at most `K` at `x` costs at most `2 K ‖x - y‖`
more than comparing them at `y`. This is the shared estimate of the two density arguments below:
`y` is chosen in the dense subset, close to the arbitrary vector `x`. -/
lemma norm_sub_apply_le_of_norm_le {T S : X →L[𝕜] Y} {K : ℝ}
    (hT : ‖T‖ ≤ K) (hS : ‖S‖ ≤ K)
    (x y : X) : ‖T x - S x‖ ≤ ‖T y - S y‖ + 2 * K * ‖x - y‖ := by
  have hbound : ‖T - S‖ ≤ 2 * K := (norm_sub_le T S).trans (by linarith)
  calc
    ‖T x - S x‖ ≤ ‖T y - S y‖ + ‖(T - S) (x - y)‖ := by
      simpa only [map_sub, sub_apply] using
        norm_le_norm_add_norm_sub' ((T - S) x) ((T - S) y)
    _ ≤ ‖T y - S y‖ + 2 * K * ‖x - y‖ :=
      add_le_add le_rfl ((T - S).le_of_opNorm_le_of_le hbound le_rfl)

/-- A uniformly bounded family of continuous linear maps that converges pointwise on a dense
subset converges pointwise everywhere. -/
lemma tendsto_apply_of_dense {ι : Type*} {l : Filter ι} {D : Set X}
    (hD : Dense D) {f : ι → X →L[𝕜] Y} {g : X →L[𝕜] Y} {C : ℝ}
    (hbound : ∀ᶠ i in l, ‖f i‖ ≤ C)
    (htendsto : ∀ x ∈ D, Tendsto (fun i => f i x) l (nhds (g x))) (x : X) :
    Tendsto (fun i => f i x) l (nhds (g x)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let K : ℝ := |C| + ‖g‖ + 1
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hC_le : C ≤ K := by
    dsimp only [K]
    linarith [le_abs_self C, norm_nonneg g]
  have hg_le : ‖g‖ ≤ K := by
    dsimp only [K]
    linarith [abs_nonneg C]
  obtain ⟨y, hyD, hxy⟩ := hD.exists_dist_lt x (by positivity : 0 < epsilon / (3 * K))
  have hxy_norm : 2 * K * ‖x - y‖ < 2 * epsilon / 3 := by
    have : ‖x - y‖ < epsilon / (3 * K) := by simpa only [dist_eq_norm] using hxy
    calc
      2 * K * ‖x - y‖ < 2 * K * (epsilon / (3 * K)) :=
        mul_lt_mul_of_pos_left this (by positivity)
      _ = 2 * epsilon / 3 := by field_simp
  have hy := (Metric.tendsto_nhds.mp (htendsto y hyD)) (epsilon / 3) (by positivity)
  filter_upwards [hbound, hy] with i hi hiy
  rw [dist_eq_norm] at hiy ⊢
  have hmain := norm_sub_apply_le_of_norm_le (hi.trans hC_le) hg_le x y
  linarith

/-- A uniformly bounded family of continuous linear maps that is uniformly Cauchy on a parameter
set at every vector in a dense subset is uniformly Cauchy there at every vector. -/
lemma uniformCauchySeqOn_apply_of_dense {ι Z : Type*} {p : Filter ι}
    {D : Set X}
    (hD : Dense D) {f : ι → Z → X →L[𝕜] Y} {s : Set Z} {C : ℝ}
    (hbound : ∀ᶠ i in p, ∀ z ∈ s, ‖f i z‖ ≤ C)
    (hcauchy : ∀ x ∈ D, UniformCauchySeqOn (fun i z => f i z x) p s) (x : X) :
    UniformCauchySeqOn (fun i z => f i z x) p s := by
  intro u hu
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_uniformity_dist.mp hu
  let K : ℝ := |C| + 1
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hC_le : C ≤ K := by
    dsimp only [K]
    linarith [le_abs_self C]
  obtain ⟨y, hyD, hxy⟩ := hD.exists_dist_lt x (by positivity : 0 < epsilon / (3 * K))
  have hxy_norm : 2 * K * ‖x - y‖ < 2 * epsilon / 3 := by
    have : ‖x - y‖ < epsilon / (3 * K) := by simpa only [dist_eq_norm] using hxy
    calc
      2 * K * ‖x - y‖ < 2 * K * (epsilon / (3 * K)) :=
        mul_lt_mul_of_pos_left this (by positivity)
      _ = 2 * epsilon / 3 := by field_simp
  have hmiddle := hcauchy y hyD { q : Y × Y | dist q.1 q.2 < epsilon / 3 }
    (Metric.dist_mem_uniformity (by positivity))
  filter_upwards [hbound.prod_inl p, hbound.prod_inr p, hmiddle] with m hi hj hm z hz
  refine hball ?_
  rw [dist_eq_norm]
  have hmain := norm_sub_apply_le_of_norm_le ((hi z hz).trans hC_le)
    ((hj z hz).trans hC_le) x y
  have hmid : ‖f m.1 z y - f m.2 z y‖ < epsilon / 3 := by
    simpa only [dist_eq_norm] using hm z hz
  linarith


end ContinuousLinearMap
