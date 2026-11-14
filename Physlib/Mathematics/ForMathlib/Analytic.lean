/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

-- `Uniqueness` imports this module privately; the auxiliary analyticity lemmas need its public API.
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.InnerProductSpace.PiL2
/-!

# Analyticity and dense non-vanishing sets

Analytic coordinate functions and density of the non-vanishing set of an analytic function.

## i. Overview

By the identity principle, an analytic function on a connected normed space which vanishes on a
non-empty open set vanishes everywhere. Hence an analytic function which is non-zero at one point
is non-zero on a dense set.

The coordinate functionals on Euclidean space are registered with `fun_prop` to automate proofs of
analyticity for polynomial expressions in the coordinates. Combined with the density lemma, this
shows that the non-vanishing set of such an expression is dense whenever it is non-zero at some
point. Applications include domains in phase space used in proofs of Liouville integrability.

## ii. Key results

- `AnalyticOnNhd.dense_setOf_ne_zero` : a function analytic on a connected space and non-zero at
  some point is non-zero on a dense set.
- `analyticAt_euclideanSpace_apply` : coordinate functionals on Euclidean space are analytic.

## iii. Table of contents

- A. Density of the non-vanishing set
- B. Analyticity of coordinate functionals

## iv. References

The density proof uses the identity principle in `Mathlib.Analysis.Analytic.Uniqueness`.
-/

@[expose] public section

open Filter Topology

/-!

## A. Density of the non-vanishing set

-/

/-- A function analytic on a connected space, and non-zero at some point, is non-zero on a dense
set. -/
lemma AnalyticOnNhd.dense_setOf_ne_zero {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [PreconnectedSpace E] {f : E → F} (hf : AnalyticOnNhd 𝕜 f Set.univ) {x₀ : E}
    (hx₀ : f x₀ ≠ 0) : Dense {x | f x ≠ 0} := by
  rw [dense_iff_inter_open]
  rintro W hW ⟨z, hz⟩
  by_contra h
  have hzero : f =ᶠ[𝓝 z] 0 := by
    filter_upwards [hW.mem_nhds hz] with y hy
    by_contra hne
    exact h ⟨y, hy, hne⟩
  exact hx₀ (congrFun (hf.eq_of_eventuallyEq analyticOnNhd_const hzero) x₀)

/-!

## B. Analyticity of coordinate functionals

-/

/-- The coordinate functionals on Euclidean space are analytic. -/
@[fun_prop]
lemma analyticAt_euclideanSpace_apply {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] (i : ι)
    (z : EuclideanSpace 𝕜 ι) : AnalyticAt 𝕜 (fun x : EuclideanSpace 𝕜 ι => x i) z :=
  (EuclideanSpace.proj (𝕜 := 𝕜) i).analyticAt z
