/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.Existence.GeneratorInvariance
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.Existence.StoneGenerator
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.CayleySpectralData.SpecTheorem
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.Flow.StoneInvariance

/-!

# Stone's theorem: reconstruction of the group

Stone's theorem, reconstruction: a unitary group is exp(i t T) for its generator.

## i. Overview

Let `T` be the candidate generator of a strongly continuous unitary group `U`, and `V t = exp(i t
T)` the unitary group of the spectral measure of its closure. For `x` in the domain of `T`, the
orbits `U t x` and `V t x` solve the same equation `w' = i T w` with the same initial value. Since
`T` is symmetric, `‖U t x - V t x‖²` has zero derivative, so the orbits agree. The domain is dense,
so `U = V`.

## ii. Key results

- `stoneReconstructionUnitaryGroup` : the group `exp(i t T)` of the generator.
- `stoneCandidateGenerator_domain_dense` : the domain of the candidate generator is dense.
- `stoneCandidateGenerator_reconstruction` : **Stone's theorem, reconstruction**: `U t = exp(i t
  T)`.

## iii. Table of contents

- A. The reconstructed unitary group
- B. Uniqueness for the evolution equation
- C. Reconstruction of the group

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace QuantumMechanics

noncomputable section

open scoped InnerProductSpace Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U : ℝ → H →L[ℂ] H} (hU0 : U 0 = 1) (hUmul : ∀ s t, U (s + t) = U s * U t)
  (hUunit : ∀ t, U t ∈ unitary (H →L[ℂ] H)) (hUcont : ∀ ξ : H, Continuous (fun t : ℝ => U t ξ))

/-!

## A. The reconstructed unitary group

-/

include hU0 hUmul hUunit hUcont in
/-- The Cayley-transform spectral measure for `stoneCandidateGenerator hUmul`'s essential
self-adjoint closure. -/
noncomputable def stoneReconstructionSpectralMeasure : WOTSpectralMeasure ℝ H :=
  cayleyRealSpectralMeasure (stoneCandidateGenerator (U := U) hUmul).closure
    (stoneCandidateGenerator_isEssentiallySelfAdjoint hUmul hU0 hUunit hUcont)

include hU0 hUmul hUunit hUcont in
/-- The domain-aware spectral theorem for `stoneCandidateGenerator hUmul`'s closure, built via the
Cayley transform from this Track's essential self-adjointness result. -/
lemma stoneReconstructionData :
    DomainAwareSelfAdjointSpectralTheorem (stoneCandidateGenerator (U := U) hUmul).closure
      (stoneReconstructionSpectralMeasure hU0 hUmul hUunit hUcont) :=
  unboundedSpectralTheorem_of_essentiallySelfAdjoint (stoneCandidateGenerator (U := U) hUmul)
    (stoneCandidateGenerator_isEssentiallySelfAdjoint hUmul hU0 hUunit hUcont)

include hU0 hUmul hUunit hUcont in
/-- The unitary group `exp(i t T)` of the closure of the candidate generator. -/
noncomputable def stoneReconstructionUnitaryGroup (t : ℝ) : H →L[ℂ] H :=
  ContinuousLinearMapWOT.toCLM ((stoneReconstructionData hU0 hUmul hUunit hUcont).expUnitaryGroup t)

/-!

## B. Uniqueness for the evolution equation

-/

section Uniqueness

variable {T : H →ₗ.[ℂ] H}

omit [CompleteSpace H] in
/-- Two curves through the same starting point, both solving `w' = i • T w` while remaining in
`T`'s domain, coincide everywhere: the standard Schrödinger-equation uniqueness argument, using
only that `T` is symmetric (so `⟪w, T w⟫` is real, killing the cross terms in `d/dt‖w‖²`). -/
lemma hasDerivAt_generator_unique {y z : ℝ → H} (hTsym : T.IsSymmetric)
    (hy_mem : ∀ t, y t ∈ T.domain) (hz_mem : ∀ t, z t ∈ T.domain)
    (hy_deriv : ∀ t, HasDerivAt y (Complex.I • T ⟨y t, hy_mem t⟩) t)
    (hz_deriv : ∀ t, HasDerivAt z (Complex.I • T ⟨z t, hz_mem t⟩) t)
    (h0 : y 0 = z 0) : ∀ t, y t = z t := by
  set w : ℝ → H := fun t => y t - z t with hw_def
  have hw_mem : ∀ t, w t ∈ T.domain := fun t =>
    T.domain.sub_mem (hy_mem t) (hz_mem t)
  have hw_val : ∀ t, ((⟨w t, hw_mem t⟩ : T.domain) : H) = (⟨y t, hy_mem t⟩ : T.domain) -
      (⟨z t, hz_mem t⟩ : T.domain) := fun t => rfl
  have hw_apply : ∀ t, T ⟨w t, hw_mem t⟩ = T ⟨y t, hy_mem t⟩ - T ⟨z t, hz_mem t⟩ := by
    intro t
    have := T.map_sub ⟨y t, hy_mem t⟩ ⟨z t, hz_mem t⟩
    rwa [show (⟨y t, hy_mem t⟩ : T.domain) - ⟨z t, hz_mem t⟩ = ⟨w t, hw_mem t⟩ from rfl] at this
  have hw_deriv : ∀ t, HasDerivAt w (Complex.I • T ⟨w t, hw_mem t⟩) t := by
    intro t
    have hsub := (hy_deriv t).sub (hz_deriv t)
    rw [hw_apply t, smul_sub]
    exact hsub
  set g : ℝ → ℂ := fun t => ⟪w t, w t⟫_ℂ with hg_def
  have hg_deriv : ∀ t, HasDerivAt g 0 t := by
    intro t
    have hprod := (hw_deriv t).inner ℂ (hw_deriv t)
    have hval : ⟪w t, Complex.I • T ⟨w t, hw_mem t⟩⟫_ℂ +
        ⟪Complex.I • T ⟨w t, hw_mem t⟩, w t⟫_ℂ = 0 := by
      rw [inner_smul_left, inner_smul_right]
      have hreal_t := LinearPMap.isSymmetric_iff_inner_map_self_real.mp hTsym ⟨w t, hw_mem t⟩
      have hswap : ⟪(w t : H), T ⟨w t, hw_mem t⟩⟫_ℂ = ⟪T ⟨w t, hw_mem t⟩, (w t : H)⟫_ℂ := by
        rw [← inner_conj_symm (w t : H) (T ⟨w t, hw_mem t⟩), hreal_t]
      rw [hswap]
      have hconjI : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I
      rw [hconjI]
      ring
    rwa [hval] at hprod
  have hg_const : ∀ t, g t = g 0 := fun t =>
    is_const_of_deriv_eq_zero (fun t => (hg_deriv t).differentiableAt)
      (fun t => (hg_deriv t).deriv) t 0
  have hg0 : g 0 = 0 := by
    show ⟪w 0, w 0⟫_ℂ = 0
    have : w 0 = 0 := by rw [hw_def]; simp [h0]
    rw [this]; simp
  intro t
  have hgt0 : g t = 0 := (hg_const t).trans hg0
  have hw0 : w t = 0 := inner_self_eq_zero.mp hgt0
  exact sub_eq_zero.mp hw0

end Uniqueness

/-!

## C. Reconstruction of the group

-/

include hU0 hUmul hUunit hUcont in
/-- **Stone's theorem, reconstruction direction.** `U` agrees with the concrete unitary group
`stoneReconstructionUnitaryGroup` on every vector in `stoneCandidateGenerator hUmul`'s domain. -/
lemma stoneCandidateGenerator_reconstruction_of_mem_domain
    (x : (stoneCandidateGenerator (U := U) hUmul).domain) (t : ℝ) :
    U t (x : H) = stoneReconstructionUnitaryGroup hU0 hUmul hUunit hUcont t (x : H) := by
  have hle := (stoneCandidateGenerator (U := U) hUmul).le_closure
  have hTsym : (stoneCandidateGenerator (U := U) hUmul).closure.IsSymmetric :=
    LinearPMap.IsSelfAdjoint.isSymmetric (LinearPMap.isEssentiallySelfAdjoint_def.mp
      (stoneCandidateGenerator_isEssentiallySelfAdjoint hUmul hU0 hUunit hUcont))
  have hx_dom : (x : H) ∈ (stoneCandidateGenerator (U := U) hUmul).closure.domain :=
    hle.1 x.property
  set D := stoneReconstructionData (U := U) hU0 hUmul hUunit hUcont with hD_def
  set x' : (stoneCandidateGenerator (U := U) hUmul).closure.domain := ⟨(x : H), hx_dom⟩
    with hx'_def
  -- The `U`-side orbit and its everywhere-derivative, transported from `X` to `X.closure`.
  have hUorbit_mem : ∀ t, U t (x : H) ∈ (stoneCandidateGenerator (U := U) hUmul).closure.domain :=
    fun t => hle.1 (stoneCandidateDomain_translate_mem hUmul x t)
  have hUorbit_deriv : ∀ t, HasDerivAt (fun r : ℝ => U r (x : H))
      (Complex.I • (stoneCandidateGenerator (U := U) hUmul).closure
        ⟨U t (x : H), hUorbit_mem t⟩) t := by
    intro t
    have hraw := stoneCandidateGenerator_hasDerivAt hUmul x t
    have heq : (stoneCandidateGenerator (U := U) hUmul).closure ⟨U t (x : H), hUorbit_mem t⟩ =
        stoneCandidateGenerator (U := U) hUmul
          ⟨U t (x : H), stoneCandidateDomain_translate_mem hUmul x t⟩ :=
      (LinearPMap.apply_comp_inclusion hle
        ⟨U t (x : H), stoneCandidateDomain_translate_mem hUmul x t⟩).symm
    rw [heq, stoneCandidateGenerator_translate hUmul x t]
    exact hraw
  -- The `V`-side orbit and its everywhere-derivative.
  have hVorbit_mem : ∀ t, D.expUnitaryGroup t (x : H) ∈
      (stoneCandidateGenerator (U := U) hUmul).closure.domain :=
    fun t => D.expUnitaryGroup_translate_mem x' t
  have hVorbit_deriv : ∀ t, HasDerivAt (fun r : ℝ => D.expUnitaryGroup r (x : H))
      (Complex.I • (stoneCandidateGenerator (U := U) hUmul).closure
        ⟨D.expUnitaryGroup t (x : H), hVorbit_mem t⟩) t := by
    intro t
    have hraw : HasDerivAt (fun r : ℝ => D.expUnitaryGroup r (x : H))
        (D.expUnitaryGroup t (Complex.I • (stoneCandidateGenerator (U := U) hUmul).closure x')) t :=
      D.expUnitaryGroup_hasDerivAt x' t
    have hcomm : D.expUnitaryGroup t ((stoneCandidateGenerator (U := U) hUmul).closure x') =
        (stoneCandidateGenerator (U := U) hUmul).closure
          ⟨D.expUnitaryGroup t (x : H), hVorbit_mem t⟩ :=
      (D.expUnitaryGroup_translate x' t).symm
    have hscalar : D.expUnitaryGroup t
        (Complex.I • (stoneCandidateGenerator (U := U) hUmul).closure x') =
        Complex.I • D.expUnitaryGroup t
          ((stoneCandidateGenerator (U := U) hUmul).closure x') := map_smul _ _ _
    rw [hscalar, hcomm] at hraw
    exact hraw
  have h0 : U 0 (x : H) = D.expUnitaryGroup 0 (x : H) := by
    rw [hU0]
    simp [D.expUnitaryGroup_zero]
  have hVt := hasDerivAt_generator_unique hTsym hUorbit_mem hVorbit_mem
    hUorbit_deriv hVorbit_deriv h0 t
  show U t (x : H) = ContinuousLinearMapWOT.toCLM (D.expUnitaryGroup t) (x : H)
  rw [hVt]
  rfl

include hU0 hUunit hUcont in
/-- The domain of the candidate generator is dense. -/
lemma stoneCandidateGenerator_domain_dense :
    Dense ((stoneCandidateGenerator (U := U) hUmul).domain : Set H) := by
  have hsub : {x : H | (stoneCandidateGenerator (U := U) hUmul).IsAnalyticVector x} ⊆
      ((stoneCandidateGenerator (U := U) hUmul).domain : Set H) := by
    rintro x ⟨v, ⟨hv0, -⟩, -⟩
    rw [← hv0]
    exact (v 0).property
  have hspan_le : Submodule.span ℂ
      {x : H | (stoneCandidateGenerator (U := U) hUmul).IsAnalyticVector x} ≤
      (stoneCandidateGenerator (U := U) hUmul).domain :=
    Submodule.span_le.mpr hsub
  have hmono := Submodule.topologicalClosure_mono hspan_le
  rw [stoneCandidateGenerator_denseAnalyticVectors hUmul hU0 hUunit hUcont] at hmono
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr (top_le_iff.mp hmono)

include hU0 hUmul hUunit hUcont in
/-- **Stone's theorem.** A strongly continuous unitary group is `exp(i t T)` for the closure `T` of
its candidate generator. -/
lemma stoneCandidateGenerator_reconstruction (x : H) (t : ℝ) :
    U t x = stoneReconstructionUnitaryGroup hU0 hUmul hUunit hUcont t x := by
  have hdense := stoneCandidateGenerator_domain_dense hU0 hUmul hUunit hUcont
  have heq : Set.EqOn (fun ξ : H => U t ξ)
      (fun ξ : H => stoneReconstructionUnitaryGroup hU0 hUmul hUunit hUcont t ξ)
      ((stoneCandidateGenerator (U := U) hUmul).domain : Set H) := by
    intro ξ hξ
    exact stoneCandidateGenerator_reconstruction_of_mem_domain hU0 hUmul hUunit hUcont ⟨ξ, hξ⟩ t
  have hext := Continuous.ext_on hdense (U t).continuous
    (stoneReconstructionUnitaryGroup hU0 hUmul hUunit hUcont t).continuous heq
  exact congrFun hext x

end
end QuantumMechanics

end ProbabilisticTheory
