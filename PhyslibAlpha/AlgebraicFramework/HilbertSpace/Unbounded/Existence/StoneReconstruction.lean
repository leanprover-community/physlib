/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Existence.GeneratorInvariance
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Existence.StoneGenerator
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.CayleySpectralData.SpecTheorem
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Flow.StoneInvariance

/-!
# Stone's theorem, reconstruction direction: `U t = exp(-it Hgen)`

The second half of Stone's theorem, completing `StoneGenerator.lean`'s existence result:
the strongly continuous unitary group `U` a candidate generator `T := stoneCandidateGenerator
hUmul` was built from is *recovered* from that generator's essential self-adjoint closure via the
Cayley-transform spectral integral (`unboundedSpectralTheorem_of_essentiallySelfAdjoint`,
`CayleySpectralData/SpecTheorem.lean`) and its associated unitary group
(`WOTSpectralMeasure.expUnitaryGroup`, `StoneUnitaryGroup.lean`).

## Strategy

For `V t := ContinuousLinearMapWOT.toCLM (D.expUnitaryGroup t)`, both `t ↦ U t x` and
`t ↦ V t x` satisfy the same "Schrödinger equation" `w'(t) = i • T.closure (w t)` for `x` in the
(dense) domain of `T := stoneCandidateGenerator hUmul`:

- the `U`-side derivative relation is `GeneratorInvariance.stoneCandidateGenerator_hasDerivAt`;
- the `V`-side one combines `Flow.Stone`'s `expUnitaryGroup_hasDerivAt` with this Track's own
  `Flow.StoneInvariance.expUnitaryGroup_translate`.

Given that, `g(t) := ⟪U t x - V t x, U t x - V t x⟫_ℂ` has zero derivative everywhere (using that
`T.closure` is self-adjoint, hence symmetric, so `⟪w, T.closure w⟫` is always real and the two
cross terms of the product rule cancel exactly), hence is the constant `g(0) = 0`, hence `U t x =
V t x` for every `t`. Density of `T`'s domain (already established in
`StoneGenerator.lean`, since the analytic vectors used there are a subset of it) then
extends this identity from the domain to all of `H`, using continuity of both `U t` and `V t`.

## Main definitions

- `stoneReconstructionSpectralMeasure`, `stoneReconstructionData` : the Cayley-transform spectral
  measure and domain-aware spectral theorem for `stoneCandidateGenerator hUmul`'s closure.
- `stoneReconstructionUnitaryGroup` : the resulting concrete `exp(itT)`, as a genuine
  `H →L[ℂ] H`-valued function of `t`.
- `stoneCandidateGenerator_reconstruction` : `U t = stoneReconstructionUnitaryGroup t` for every
  `t` — the reconstruction theorem itself.
-/

@[expose] public section

namespace QuantumMechanics

noncomputable section

open scoped InnerProductSpace Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U : ℝ → H →L[ℂ] H} (hU0 : U 0 = 1) (hUmul : ∀ s t, U (s + t) = U s * U t)
  (hUunit : ∀ t, U t ∈ unitary (H →L[ℂ] H)) (hUcont : ∀ ξ : H, Continuous (fun t : ℝ => U t ξ))

include hU0 hUmul hUunit hUcont in
/-- The Cayley-transform spectral measure for `stoneCandidateGenerator hUmul`'s essential
self-adjoint closure. -/
noncomputable def stoneReconstructionSpectralMeasure : WOTSpectralMeasure ℝ H :=
  cayleyRealSpectralMeasure (stoneCandidateGenerator (U := U) hUmul).closure
    (stoneCandidateGenerator_isEssentiallySelfAdjoint hUmul hU0 hUunit hUcont)

include hU0 hUmul hUunit hUcont in
/-- The domain-aware spectral theorem for `stoneCandidateGenerator hUmul`'s closure, built via the
Cayley transform from this Track's essential self-adjointness result. -/
theorem stoneReconstructionData :
    DomainAwareSelfAdjointSpectralTheorem (stoneCandidateGenerator (U := U) hUmul).closure
      (stoneReconstructionSpectralMeasure hU0 hUmul hUunit hUcont) :=
  unboundedSpectralTheorem_of_essentiallySelfAdjoint (stoneCandidateGenerator (U := U) hUmul)
    (stoneCandidateGenerator_isEssentiallySelfAdjoint hUmul hU0 hUunit hUcont)

include hU0 hUmul hUunit hUcont in
/-- The concrete unitary group `exp(itT)` reconstructed from `T`'s spectral measure, as a genuine
`H →L[ℂ] H`-valued function of `t`. -/
noncomputable def stoneReconstructionUnitaryGroup (t : ℝ) : H →L[ℂ] H :=
  ContinuousLinearMapWOT.toCLM ((stoneReconstructionData hU0 hUmul hUunit hUcont).expUnitaryGroup t)

section Uniqueness

variable {T : H →ₗ.[ℂ] H}

omit [CompleteSpace H] in
/-- Two curves through the same starting point, both solving `w' = i • T w` while remaining in
`T`'s domain, coincide everywhere: the standard Schrödinger-equation uniqueness argument, using
only that `T` is symmetric (so `⟪w, T w⟫` is real, killing the cross terms in `d/dt‖w‖²`). -/
theorem hasDerivAt_generator_unique {y z : ℝ → H} (hTsym : T.IsSymmetric)
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

include hU0 hUmul hUunit hUcont in
/-- **Stone's theorem, reconstruction direction.** `U` agrees with the concrete unitary group
`stoneReconstructionUnitaryGroup` on every vector in `stoneCandidateGenerator hUmul`'s domain. -/
theorem stoneCandidateGenerator_reconstruction_of_mem_domain
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
/-- `stoneCandidateGenerator hUmul`'s domain is dense: every analytic vector lies in it (an
analytic vector's iterate sequence starts at the vector itself, so `v 0 = x` with
`v 0 : T.domain`), so the domain, a submodule, contains the span of the analytic vectors; density
of that span's topological closure (`stoneCandidateGenerator_denseAnalyticVectors`) then forces
the domain's own topological closure to be everything too, by monotonicity. -/
theorem stoneCandidateGenerator_domain_dense :
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
/-- **Stone's theorem, in full: existence and reconstruction.** Every strongly continuous
one-parameter unitary group `U` on a Hilbert space equals `exp(itHgen)` for its own essentially
self-adjoint generator `Hgen := stoneCandidateGenerator hUmul`, reconstructed via the Cayley
transform's spectral integral (`stoneReconstructionUnitaryGroup`) — for *every* vector, not just
those in `Hgen`'s domain: `stoneCandidateGenerator_reconstruction_of_mem_domain` extended from the
(dense, `stoneCandidateGenerator_domain_dense`) domain to all of `H` by continuity of both sides. -/
theorem stoneCandidateGenerator_reconstruction (x : H) (t : ℝ) :
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
