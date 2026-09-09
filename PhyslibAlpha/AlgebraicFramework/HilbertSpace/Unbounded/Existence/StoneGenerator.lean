/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Existence.GardingVectorWitness
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.AnalyticVector.Nelson

/-!
# Stone's theorem, existence direction: every strongly continuous unitary group has a
self-adjoint generator

The capstone of Track A (`STONE_GENERATOR_EXISTENCE_PLAN.md`): for *any* strongly continuous
one-parameter unitary group `U` on a Hilbert space `H` — no spectral measure, no boundedness, no
prior structure assumed — the candidate generator `stoneCandidateGenerator hUmul` is essentially
self-adjoint, i.e. its closure is a genuine self-adjoint (unbounded) operator. This is the classical
"hard" direction of Stone's theorem, proved here entirely via **Gårding vectors + Nelson's
analytic-vector theorem**, avoiding the usual Bochner/spectral-integral route.

## The last step

Nelson's theorem (`IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors`) needs a symmetric
operator with a *dense* set of analytic vectors. `stoneCandidateGenerator_isSymmetric`
(`CandidateGenerator.lean`) gives symmetry. Density follows from combining this Track's two main
results: `analyticGardingVector_isAnalyticVector` (every Gårding vector `analyticGardingVector U ε
ψ` is an analytic vector) and `analyticGardingVector_tendsto` (`analyticGardingVector U ε ψ → ψ` as
`ε → 0⁺`, for *every* `ψ`) — so every vector in `H` is a limit of analytic vectors, hence lies in
the closure of their span, hence that closure is all of `H`.
-/

@[expose] public section

namespace QuantumMechanics

noncomputable section

open scoped InnerProductSpace Topology
open LinearPMap

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U : ℝ → H →L[ℂ] H} (hUmul : ∀ s t, U (s + t) = U s * U t)

include hUmul in
/-- **Density of analytic vectors.** Every `ψ : H` is a limit of Gårding vectors
`analyticGardingVector U ε ψ` as `ε → 0⁺` (`analyticGardingVector_tendsto`), each of which is an
analytic vector of `stoneCandidateGenerator` (`analyticGardingVector_isAnalyticVector`); hence
`ψ` lies in the closure of the analytic vectors, and since this holds for every `ψ`, the span of
the analytic vectors is dense. -/
theorem stoneCandidateGenerator_denseAnalyticVectors (hU0 : U 0 = 1)
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
/-- **Stone's theorem, existence direction.** Every strongly continuous one-parameter unitary
group `U` on a Hilbert space has an essentially self-adjoint generator: the closure of
`stoneCandidateGenerator hUmul` is a genuine self-adjoint (generally unbounded) operator. Proved
via Nelson's analytic-vector theorem, fed by density of Gårding vectors
(`stoneCandidateGenerator_denseAnalyticVectors`) — the culmination of Track A. -/
theorem stoneCandidateGenerator_isEssentiallySelfAdjoint (hU0 : U 0 = 1)
    (hUunit : ∀ t, U t ∈ unitary (H →L[ℂ] H)) (hUcont : ∀ ξ : H, Continuous (fun t : ℝ => U t ξ)) :
    (stoneCandidateGenerator (U := U) hUmul).IsEssentiallySelfAdjoint :=
  LinearPMap.IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors
    (stoneCandidateGenerator_isSymmetric (U := U) hU0 hUmul hUunit)
    (stoneCandidateGenerator_denseAnalyticVectors hUmul hU0 hUunit hUcont)

end

end QuantumMechanics
