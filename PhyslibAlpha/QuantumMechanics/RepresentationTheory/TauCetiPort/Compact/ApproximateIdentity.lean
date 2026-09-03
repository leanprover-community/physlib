/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Order.Filter.SmallSets
public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Compact.Convolution
public import Mathlib.Topology.UrysohnsLemma

/-!
# Approximate identities on a compact group

Convolution against a continuous kernel smooths an `L²` class into a continuous function
(`TauCeti.convolutionCLM`). This file supplies the kernels that make that smoothing harmless: for
every neighbourhood `U` of the identity there is a **mollifying kernel** supported in `U`, and
convolving a continuous function against a kernel supported in a small enough neighbourhood
changes it by as little as one likes in the uniform norm.

A mollifying kernel is bundled as `TauCeti.IsMollifier U k`: the kernel is nonnegative, invariant
under inversion, has unit mass for normalized Haar measure, and vanishes off `U`. Inversion
invariance of a nonnegative kernel is the symmetry `k g⁻¹ = conj (k g)`, so `convolutionOperator k`
is self-adjoint (`TauCeti.IsMollifier.isSelfAdjoint_convolutionOperator`); this is one of the two
hypotheses of the spectral theorem for compact self-adjoint operators, the other, compactness,
being no concern of this file.

## Main definitions

* `TauCeti.IsMollifier`: `k` is a nonnegative, inversion-invariant, unit-mass continuous kernel
  vanishing outside `U`.

## Main statements

* `TauCeti.exists_mem_nhds_one_norm_sub_le`: uniform continuity of a continuous function on a
  compact group, in the form `‖f (z⁻¹ * x) - f x‖ ≤ ε` for `z` near `1`, uniformly in `x`.
* `TauCeti.exists_isMollifier`: mollifying kernels exist supported in any neighbourhood of `1`.
* `TauCeti.IsMollifier.norm_convolutionCLM_toLp_sub_le`: the uniform estimate
  `‖k * f - f‖ ≤ ε` for a kernel supported where `f` varies by at most `ε`.
* `TauCeti.exists_isMollifier_norm_convolutionCLM_toLp_sub_le`: **the approximate identity.** For
  every continuous `f`, every `ε > 0` and every neighbourhood `U` of `1` there is a mollifying
  kernel supported in `U` with `‖k * f - f‖ ≤ ε`.
* `TauCeti.tendsto_convolutionCLM_toLp`: the same statement as convergence of a net of kernels
  whose supports shrink to `1`.
* `TauCeti.exists_isMollifier_tendsto_convolutionCLM_toLp`: **the approximate identity as a single
  family.** One mollifying kernel for each neighbourhood of `1`, whose convolutions converge
  uniformly to `f` as the neighbourhood shrinks, simultaneously for every continuous `f`.

## Implementation notes

Uniform continuity is obtained from the same currying trick that builds the kernel sections in
`TauCeti/RepresentationTheory/Compact/Convolution.lean`: the left translates `z ↦ (x ↦ f (z⁻¹ * x))`
assemble into a *continuous* map `G → C(G, 𝕜)` for the uniform norm, and continuity at `z = 1` is
exactly the uniform estimate. No uniform structure on `G` is mentioned.

The kernels themselves come from Urysohn's lemma, in the form that asks for a regular, locally
compact space: a compact topological group is both whether or not it is Hausdorff, so the
construction needs no `T2Space G`, and the mollifier results below do not assume it. A bump at the
identity supported in a *symmetric* neighbourhood is made inversion invariant by adding its
composition with inversion, and then normalized by its mass, which is positive because Haar measure
is positive on nonempty open sets.

Kernels take values in `𝕜` rather than in `ℝ` because that is what `convolutionCLM` consumes;
nonnegativity is stated with the scoped `ComplexOrder` instance on an `RCLike` field, for which
`0 ≤ z` means `z` is real and nonnegative.

## References

This is `approx_identity_exists` from Layer 5 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), the last input to the
uniform density of the matrix coefficients in `C(G)` that the roadmap's non-circular route to the
Peter-Weyl theorem requires.

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC (2016), Chapter 5.
* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 2.
-/

public section

open Filter MeasureTheory Set
open scoped ComplexOrder Topology

namespace TauCeti

section CompactGroup

variable {𝕜 E G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-! ### Uniform continuity on a compact group -/

/-- The left translates `z ↦ (x ↦ f (z⁻¹ * x))` of a continuous function on a compact group,
as a continuous map into `C(G, E)` with the uniform norm. -/
private noncomputable def leftTranslateCM (f : C(G, E)) : C(G, C(G, E)) :=
  ContinuousMap.curry
    (f.comp ⟨fun p : G × G => p.1⁻¹ * p.2, continuous_fst.inv.mul continuous_snd⟩)

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem leftTranslateCM_apply (f : C(G, E)) (z x : G) :
    leftTranslateCM f z x = f (z⁻¹ * x) :=
  (rfl)

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem leftTranslateCM_one (f : C(G, E)) : leftTranslateCM f 1 = f := by
  ext x
  rw [leftTranslateCM_apply, inv_one, one_mul]

omit [MeasurableSpace G] [BorelSpace G] in
/-- **Uniform continuity of a continuous function on a compact group.** For every `ε > 0` there is
a neighbourhood `V` of the identity such that translating the argument by any `z ∈ V` moves the
value of `f` by at most `ε`, *uniformly* in the argument.

The uniform structure of `G` is not mentioned: the statement is continuity at `z = 1` of the map
sending `z` to the left translate of `f` by `z`, which is continuous into `C(G, E)` for the
uniform norm because `G` is compact. -/
theorem exists_mem_nhds_one_norm_sub_le (f : C(G, E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ V ∈ 𝓝 (1 : G), ∀ z ∈ V, ∀ x : G, ‖f (z⁻¹ * x) - f x‖ ≤ ε := by
  have htendsto : Tendsto (leftTranslateCM (E := E) (G := G) f) (𝓝 1) (𝓝 f) := by
    simpa only [leftTranslateCM_one] using (leftTranslateCM f).continuous.tendsto 1
  refine ⟨leftTranslateCM f ⁻¹' Metric.closedBall f ε,
    htendsto (Metric.closedBall_mem_nhds f hε), fun z hz x => ?_⟩
  have hz' : ‖leftTranslateCM f z - f‖ ≤ ε := by
    simpa only [mem_preimage, Metric.mem_closedBall, dist_eq_norm] using hz
  calc ‖f (z⁻¹ * x) - f x‖
      = ‖(leftTranslateCM f z - f) x‖ := by rw [ContinuousMap.sub_apply, leftTranslateCM_apply]
    _ ≤ ‖leftTranslateCM f z - f‖ := (leftTranslateCM f z - f).norm_coe_le_norm x
    _ ≤ ε := hz'

/-! ### Mollifying kernels -/

/-- A **mollifying kernel supported in `U`**: a continuous kernel on a compact group which is
nonnegative, invariant under inversion, of unit mass for normalized Haar measure, and zero outside
`U`.

Nonnegativity is taken in the scoped `ComplexOrder` order of the `RCLike` field `𝕜`, so it says in
particular that `k` is real-valued. Together with inversion invariance it gives the symmetry
`k g⁻¹ = conj (k g)` that makes `convolutionOperator k` self-adjoint. -/
structure IsMollifier (U : Set G) (k : C(G, 𝕜)) : Prop where
  /-- A mollifying kernel is nonnegative, hence real-valued. -/
  nonneg : ∀ g, 0 ≤ k g
  /-- A mollifying kernel is invariant under inversion. -/
  inv_apply : ∀ g, k g⁻¹ = k g
  /-- A mollifying kernel has unit mass for normalized Haar measure. -/
  integral_eq_one : ∫ g, k g ∂(haarProb G) = 1
  /-- A mollifying kernel supported in `U` vanishes outside `U`. -/
  eq_zero_of_notMem : ∀ g ∉ U, k g = 0

namespace IsMollifier

variable {U U' : Set G} {k : C(G, 𝕜)}

/-- Enlarging the neighbourhood a kernel is supported in. -/
theorem mono (h : IsMollifier U k) (hUU' : U ⊆ U') : IsMollifier U' k :=
  { h with eq_zero_of_notMem := fun g hg => h.eq_zero_of_notMem g fun hg' => hg (hUU' hg') }

/-- A mollifying kernel is its own norm: it takes nonnegative real values. -/
theorem apply_eq_norm (h : IsMollifier U k) (g : G) : k g = (‖k g‖ : 𝕜) :=
  (RCLike.norm_of_nonneg' (h.nonneg g)).symm

/-- A mollifying kernel is symmetric in the sense required for self-adjointness of the associated
convolution operator: inversion invariance and real-valuedness combine to `k g⁻¹ = conj (k g)`. -/
theorem inv_apply_eq_conj (h : IsMollifier U k) (g : G) : k g⁻¹ = (starRingEnd 𝕜) (k g) := by
  rw [h.inv_apply]
  exact (RCLike.conj_eq_iff_im.2 (RCLike.nonneg_iff.1 (h.nonneg g)).2).symm

/-- **The convolution operator of a mollifying kernel is self-adjoint.** This is one of the two
hypotheses of the spectral theorem for compact self-adjoint operators; compactness of
`convolutionOperator k` is a separate matter, not established here. -/
theorem isSelfAdjoint_convolutionOperator (h : IsMollifier U k) :
    IsSelfAdjoint (convolutionOperator k) :=
  _root_.TauCeti.isSelfAdjoint_convolutionOperator k h.inv_apply_eq_conj

/-- A mollifying kernel has unit `L¹` norm. -/
theorem integral_norm_eq_one (h : IsMollifier U k) : ∫ g, ‖k g‖ ∂(haarProb G) = 1 := by
  have hcast : ((∫ g, ‖k g‖ ∂(haarProb G) : ℝ) : 𝕜) = 1 := by
    rw [← integral_ofReal, ← h.integral_eq_one]
    exact integral_congr_ae (Eventually.of_forall fun g => (h.apply_eq_norm g).symm)
  exact_mod_cast hcast

end IsMollifier

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- **A symmetric open neighbourhood of the identity carries a symmetric bump.** If `W` is open,
contains `1`, and is closed under inversion, then some continuous real function is nonnegative,
invariant under inversion, vanishes off `W`, and is positive at `1`. -/
private theorem exists_symmetric_bump [LocallyCompactSpace G] {W : Set G} (hWopen : IsOpen W)
    (hW1 : (1 : G) ∈ W) (hWsymm : ∀ g ∈ W, g⁻¹ ∈ W) :
    ∃ ψ : C(G, ℝ), (∀ g, 0 ≤ ψ g) ∧ (∀ g, ψ g⁻¹ = ψ g) ∧ (∀ g ∉ W, ψ g = 0) ∧ 0 < ψ 1 := by
  obtain ⟨φ, hφ1, hφ0, -, hφIcc⟩ :=
    exists_continuous_one_zero_of_isCompact (X := G) isCompact_singleton hWopen.isClosed_compl
      (disjoint_compl_right_iff_subset.2 (singleton_subset_iff.2 hW1))
  -- symmetrize the Urysohn bump by adding its composition with inversion
  refine ⟨φ + φ.comp ⟨Inv.inv, continuous_inv⟩, fun g => ?_, fun g => ?_, fun g hg => ?_, ?_⟩
  · simpa only [ContinuousMap.add_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk] using
      add_nonneg (hφIcc g).1 (hφIcc g⁻¹).1
  · simp only [ContinuousMap.add_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk, inv_inv]
    exact add_comm _ _
  · have hg' : g⁻¹ ∉ W := fun hc => hg (by simpa using hWsymm _ hc)
    simp only [ContinuousMap.add_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      hφ0 hg, hφ0 hg', Pi.zero_apply, add_zero]
  · simp only [ContinuousMap.add_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk, inv_one,
      hφ1 rfl]
    norm_num

variable (𝕜) in
/-- **Mollifying kernels exist, supported in any prescribed neighbourhood of the identity.**

The kernel is built from a Urysohn bump at the identity supported in a symmetric open
neighbourhood, made inversion invariant by adding its composition with inversion, and normalized by
its mass, which is positive because Haar measure is positive on nonempty open sets. -/
theorem exists_isMollifier {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ k : C(G, 𝕜), IsMollifier U k := by
  obtain ⟨V, hVU, hVopen, hV1⟩ := mem_nhds_iff.1 hU
  -- A symmetric open neighbourhood of `1` inside `U`.
  set W : Set G := V ∩ V⁻¹
  have hWopen : IsOpen W := hVopen.inter hVopen.inv
  have hW1 : (1 : G) ∈ W := ⟨hV1, by simpa using hV1⟩
  have hWU : W ⊆ U := inter_subset_left.trans hVU
  have hWsymm : ∀ g : G, g ∈ W → g⁻¹ ∈ W := by
    rintro g ⟨h1, h2⟩
    exact ⟨by simpa using h2, by simpa using h1⟩
  obtain ⟨ψ, hψ_nonneg, hψ_inv, hψ_zero, hψ_one⟩ := exists_symmetric_bump hWopen hW1 hWsymm
  -- Its mass is positive, so it can be normalized.
  have hψ_int : Integrable ψ (haarProb G) := integrable_continuousMap G ψ
  have hmass : 0 < ∫ g, ψ g ∂(haarProb G) := by
    refine (integral_pos_iff_support_of_nonneg hψ_nonneg hψ_int).2 ?_
    exact ψ.continuous.isOpen_support.measure_pos _
      ⟨1, by simp [Function.mem_support, hψ_one.ne']⟩
  set c : ℝ := ∫ g, ψ g ∂(haarProb G) with hcdef
  refine ⟨⟨fun g => ((c⁻¹ * ψ g : ℝ) : 𝕜),
    RCLike.continuous_ofReal.comp (continuous_const.mul ψ.continuous)⟩, ?_, ?_, ?_, ?_⟩
  · exact fun g => RCLike.ofReal_nonneg.2 (mul_nonneg (inv_nonneg.2 hmass.le) (hψ_nonneg g))
  · exact fun g => by simp only [ContinuousMap.coe_mk, hψ_inv]
  · simp only [ContinuousMap.coe_mk]
    rw [integral_ofReal, integral_const_mul, ← hcdef, inv_mul_cancel₀ hmass.ne',
      RCLike.ofReal_one]
  · exact fun g hg => by
      simp only [ContinuousMap.coe_mk, hψ_zero g fun hc => hg (hWU hc), mul_zero,
        RCLike.ofReal_zero]

/-! ### Approximate-identity estimates -/

/-- **The approximate-identity estimate.** If a mollifying kernel is supported where `f` varies by
at most `ε`, then convolving `f` against it changes `f` by at most `ε` in the uniform norm. -/
theorem IsMollifier.norm_convolutionCLM_toLp_sub_le {U : Set G} {k : C(G, 𝕜)}
    (h : IsMollifier U k) (f : C(G, 𝕜)) {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ z ∈ U, ∀ x : G, ‖f (z⁻¹ * x) - f x‖ ≤ ε) :
    ‖convolutionCLM k (ContinuousMap.toLp 2 (haarProb G) 𝕜 f) - f‖ ≤ ε := by
  refine (ContinuousMap.norm_le _ hε).2 fun x => ?_
  have hval : (convolutionCLM k (ContinuousMap.toLp 2 (haarProb G) 𝕜 f) - f) x
      = ∫ z, k z * (f (z⁻¹ * x) - f x) ∂(haarProb G) := by
    rw [ContinuousMap.sub_apply]
    exact convolutionCLM_toLp_sub_apply k f h.integral_eq_one x
  have hbound : ∀ z : G, ‖k z * (f (z⁻¹ * x) - f x)‖ ≤ ‖k z‖ * ε := by
    intro z
    by_cases hz : z ∈ U
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hf z hz x) (norm_nonneg _)
    · simp [h.eq_zero_of_notMem z hz]
  rw [hval]
  calc ‖∫ z, k z * (f (z⁻¹ * x) - f x) ∂(haarProb G)‖
      ≤ ∫ z, ‖k z‖ * ε ∂(haarProb G) :=
        norm_integral_le_of_norm_le ((integrable_continuousMap G k).norm.mul_const ε)
          (Eventually.of_forall hbound)
    _ = ε := by rw [integral_mul_const, h.integral_norm_eq_one, one_mul]

variable (𝕜) in
/-- **Approximate identities exist on a compact group.** For every continuous `f`, every `ε > 0`
and every neighbourhood `U` of the identity there is a mollifying kernel supported in `U` whose
convolution with `f` is uniformly within `ε` of `f`.

This is the input to the uniform density of the matrix coefficients in `C(G)`: a continuous
function is approximated by convolutions, and convolutions are decomposed spectrally into finitely
many matrix coefficients. -/
theorem exists_isMollifier_norm_convolutionCLM_toLp_sub_le (f : C(G, 𝕜)) {ε : ℝ}
    (hε : 0 < ε) {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ k : C(G, 𝕜), IsMollifier U k ∧
      ‖convolutionCLM k (ContinuousMap.toLp 2 (haarProb G) 𝕜 f) - f‖ ≤ ε := by
  obtain ⟨V, hV, hfV⟩ := exists_mem_nhds_one_norm_sub_le f hε
  obtain ⟨k, hk⟩ := exists_isMollifier 𝕜 (Filter.inter_mem hU hV)
  exact ⟨k, hk.mono inter_subset_left,
    hk.norm_convolutionCLM_toLp_sub_le f hε.le fun z hz => hfV z hz.2⟩

variable (𝕜) in
/-- **The mollifying convolution operators are jointly nondegenerate.** No nonzero continuous
function is annihilated by every mollifying convolution operator, because convolving against a
kernel supported near the identity moves a function by less than its own norm.

This is why the Peter-Weyl argument can start: together with the self-adjointness above, and with
compactness of `convolutionOperator k` established elsewhere, it supplies a *nonzero* operator to
feed to the spectral theorem. Nonvanishing and self-adjointness are what is proved here;
compactness is not. -/
theorem exists_isMollifier_convolutionOperator_toLp_ne_zero {f : C(G, 𝕜)} (hf : f ≠ 0)
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ k : C(G, 𝕜), IsMollifier U k ∧
      convolutionOperator k (ContinuousMap.toLp 2 (haarProb G) 𝕜 f) ≠ 0 := by
  have hfpos : 0 < ‖f‖ := norm_pos_iff.2 hf
  obtain ⟨k, hk, hle⟩ :=
    exists_isMollifier_norm_convolutionCLM_toLp_sub_le 𝕜 f (half_pos hfpos) hU
  refine ⟨k, hk, fun hzero => absurd hle (not_le.2 ?_)⟩
  rw [convolutionOperator_apply] at hzero
  have hconv : convolutionCLM k (ContinuousMap.toLp 2 (haarProb G) 𝕜 f) = 0 :=
    ContinuousMap.toLp_injective (haarProb G) (by rw [hzero, map_zero])
  rw [hconv, zero_sub, norm_neg]
  exact half_lt_self hfpos

/-- **The approximate identity as a net.** If the kernels `k i` are eventually mollifying kernels
whose supporting neighbourhoods `U i` eventually shrink inside every neighbourhood of the identity,
then `k i * f` converges uniformly to `f` for every continuous `f`. -/
theorem tendsto_convolutionCLM_toLp {ι : Type*} {l : Filter ι} {U : ι → Set G} {k : ι → C(G, 𝕜)}
    (hk : ∀ᶠ i in l, IsMollifier (U i) (k i)) (hU : ∀ V ∈ 𝓝 (1 : G), ∀ᶠ i in l, U i ⊆ V)
    (f : C(G, 𝕜)) :
    Tendsto (fun i => convolutionCLM (k i) (ContinuousMap.toLp 2 (haarProb G) 𝕜 f)) l (𝓝 f) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨V, hV, hfV⟩ := exists_mem_nhds_one_norm_sub_le f (half_pos hε)
  filter_upwards [hk, hU V hV] with i hki hi
  rw [dist_eq_norm]
  exact ((hki.mono hi).norm_convolutionCLM_toLp_sub_le f (half_pos hε).le hfV).trans_lt
    (half_lt_self hε)

variable (𝕜 G) in
/-- **The approximate identity itself: a single family of mollifying kernels that works for every
function.** There is a kernel `k U` for each neighbourhood `U` of the identity, mollifying and
supported in `U`, such that for *every* continuous `f` the convolutions `k U * f` converge
uniformly to `f` as `U` shrinks to the identity.

The index filter is the one of `TauCeti.comap_val_smallSets_neBot` at `𝓝 1`, which is nontrivial,
so the convergence has content. Unlike
`TauCeti.exists_isMollifier_norm_convolutionCLM_toLp_sub_le`, where the kernel may depend on the
function being approximated, the family here is chosen once and for all. -/
theorem exists_isMollifier_tendsto_convolutionCLM_toLp :
    ∃ k : {U : Set G // U ∈ 𝓝 (1 : G)} → C(G, 𝕜), (∀ U, IsMollifier U.1 (k U)) ∧
      ∀ f : C(G, 𝕜),
        Tendsto (fun U => convolutionCLM (k U) (ContinuousMap.toLp 2 (haarProb G) 𝕜 f))
          (comap Subtype.val (𝓝 (1 : G)).smallSets) (𝓝 f) := by
  choose k hk using fun U : {U : Set G // U ∈ 𝓝 (1 : G)} => exists_isMollifier 𝕜 U.2
  refine ⟨k, hk, fun f => tendsto_convolutionCLM_toLp (Eventually.of_forall hk) ?_ f⟩
  exact fun V hV => (eventually_smallSets_subset.2 hV).comap Subtype.val

end CompactGroup

end TauCeti
