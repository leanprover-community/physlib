/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.Existence.GardingVectorWitness
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.AnalyticVector.Nelson

/-!

# Stone's theorem: existence of the generator

## i. Overview

The Gårding vectors of a strongly continuous unitary group are analytic vectors of its candidate
generator and are dense. By Nelson's theorem the candidate generator is essentially self-adjoint.

## ii. Key results

- `stoneCandidateGenerator_denseAnalyticVectors` : the analytic vectors of the candidate generator
  are dense.
- `stoneCandidateGenerator_isEssentiallySelfAdjoint` : **Stone's theorem, existence**: the candidate
  generator is essentially self-adjoint.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace QuantumMechanics

noncomputable section

open scoped InnerProductSpace Topology
open LinearPMap

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U : ℝ → H →L[ℂ] H} (hUmul : ∀ s t, U (s + t) = U s * U t)

include hUmul in
/-- **The analytic vectors of the candidate generator are dense**: every vector is a limit of
Gårding vectors. -/
lemma stoneCandidateGenerator_denseAnalyticVectors (hU0 : U 0 = 1)
    (hUunit : ∀ t, U t ∈ unitary (H →L[ℂ] H)) (hUcont : ∀ ξ : H, Continuous (fun t : ℝ => U t ξ)) :
    (Submodule.span ℂ
      {x : H | (stoneCandidateGenerator (U := U) hUmul).IsAnalyticVector x}).topologicalClosure =
      (⊤ : Submodule ℂ H) := by
  rw [Submodule.eq_top_iff']
  intro ψ
  apply Submodule.closure_subset_topologicalClosure_span
  refine mem_closure_of_tendsto
    (analyticGardingVector_tendsto (U := U) (hUunit := hUunit) hU0 hUcont ψ) ?_
  have hev : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), (0 : ℝ) < ε := self_mem_nhdsWithin
  filter_upwards [hev] with ε hε
  exact analyticGardingVector_isAnalyticVector hUmul hUunit hUcont hε ψ

include hUmul in
/-- **Stone's theorem, existence.** The candidate generator of a strongly continuous unitary group
is essentially self-adjoint. -/
lemma stoneCandidateGenerator_isEssentiallySelfAdjoint (hU0 : U 0 = 1)
    (hUunit : ∀ t, U t ∈ unitary (H →L[ℂ] H)) (hUcont : ∀ ξ : H, Continuous (fun t : ℝ => U t ξ)) :
    (stoneCandidateGenerator (U := U) hUmul).IsEssentiallySelfAdjoint :=
  LinearPMap.IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors
    (stoneCandidateGenerator_isSymmetric (U := U) hU0 hUmul hUunit)
    (stoneCandidateGenerator_denseAnalyticVectors hUmul hU0 hUunit hUcont)

end

end QuantumMechanics

end ProbabilisticTheory
