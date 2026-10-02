/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Measurement.Basic
public import PhyslibAlpha.Mathematics.Probability.Kernel.Factorization

/-!
# Post-processing of measurements

## i. Overview

A measurement `M` is a post-processing of a measurement `N` when `M` can be simulated by performing
`N` and processing its outcome classically: `M = N ∘ K` for a normal channel `K` between the
classical systems of outcomes. Thus `M ≤ₚ N` means that `N` is at least as informative as `M`.
Normal classical channels are Markov kernels, so the processing is a random relabeling of the
outcome; relabeling along a measurable map is the deterministic case. In every normal state, the
Born law of `M` is the Born law of `N` composed with the kernel.

## ii. Key results

- `Measurement.IsPostprocessing` : the information preorder on measurements.
- `Measurement.isPostprocessing_iff_kernel` : post-processing through a Markov kernel.
- `Measurement.mapOutcome` : deterministic relabeling of measurement outcomes.
- `Measurement.IsPostprocessing.probabilityLaw_eq` : the Born law of a post-processing is the
  Born law of the original measurement composed with a Markov kernel.

## iii. Table of contents

- A. Post-processing
- B. Relabeling outcomes
- C. Born laws

-/

@[expose] public section

namespace ProbabilisticTheory

namespace Measurement

open MeasureTheory ProbabilityTheory UnitalPositiveLinearMap BoundedMeasurable

universe u v w z

variable {Ω : Type v} {Ω' : Type w} {Ω'' : Type z} {E : Type u}
  [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω''] [OrderUnitSpace E]

/-! ## A. Post-processing -/

/-- `M` is a post-processing of `N`: `M = N ∘ K` for a normal channel `K` between the classical
systems of outcomes. -/
def IsPostprocessing (M : Measurement Ω E) (N : Measurement Ω' E) : Prop :=
  ∃ K : Channel (BoundedMeasurable Ω) (BoundedMeasurable Ω'), K.IsNormal ∧
    M.toChannel = N.toChannel.comp K

/-- The information preorder on measurements. -/
scoped infix:50 " ≤ₚ " => IsPostprocessing

/-- Every measurement is a post-processing of itself. -/
lemma postprocessing_refl (M : Measurement Ω E) : M ≤ₚ M :=
  ⟨.id ℝ _, isNormal_id, (comp_id _).symm⟩

/-- Post-processing is transitive. -/
lemma postprocessing_trans {M : Measurement Ω E} {N : Measurement Ω' E}
    {P : Measurement Ω'' E} (hMN : M ≤ₚ N) (hNP : N ≤ₚ P) : M ≤ₚ P := by
  obtain ⟨K, hK, hMN⟩ := hMN
  obtain ⟨L, hL, hNP⟩ := hNP
  exact ⟨L.comp K, UnitalPositiveLinearMap.IsNormal.comp hK hL, by rw [hMN, hNP, comp_assoc]⟩

/-- Post-processing is post-processing through a Markov kernel. -/
lemma isPostprocessing_iff_kernel {M : Measurement Ω E} {N : Measurement Ω' E} :
    M ≤ₚ N ↔ ∃ (κ : Kernel Ω' Ω) (_ : IsMarkovKernel κ),
      M.toChannel = N.toChannel.comp (ofKernel κ) :=
  ⟨fun ⟨K, hK, h⟩ => ⟨toKernel K hK, inferInstance, by rw [ofKernel_toKernel, h]⟩,
    fun ⟨κ, _, h⟩ => ⟨ofKernel κ, isNormal_ofKernel κ, h⟩⟩

/-- Two measurements are post-processing equivalent when each is a post-processing of the other. -/
def PostprocessEquiv (M : Measurement Ω E) (N : Measurement Ω' E) : Prop :=
  M ≤ₚ N ∧ N ≤ₚ M

lemma postprocessEquiv_refl (M : Measurement Ω E) : PostprocessEquiv M M :=
  ⟨postprocessing_refl M, postprocessing_refl M⟩

lemma postprocessEquiv_symm {M : Measurement Ω E} {N : Measurement Ω' E}
    (h : PostprocessEquiv M N) : PostprocessEquiv N M :=
  h.symm

lemma postprocessEquiv_trans {M : Measurement Ω E} {N : Measurement Ω' E}
    {P : Measurement Ω'' E} (hMN : PostprocessEquiv M N) (hNP : PostprocessEquiv N P) :
    PostprocessEquiv M P :=
  ⟨postprocessing_trans hMN.1 hNP.1, postprocessing_trans hNP.2 hMN.2⟩

/-! ## B. Relabeling outcomes -/

/-- Relabel the outcomes of a measurement along a measurable map. -/
def mapOutcome (N : Measurement Ω' E) (f : Ω' → Ω) (hf : Measurable f) : Measurement Ω E where
  toChannel := N.toChannel.comp (comap f hf)
  isNormal := UnitalPositiveLinearMap.IsNormal.comp (isNormal_comap f hf) N.isNormal

@[simp, nolint simpNF]
lemma coe_mapOutcome_apply (N : Measurement Ω' E) (f : Ω' → Ω) (hf : Measurable f)
    (s : Set Ω) (hs : MeasurableSet s) : (N.mapOutcome f hf s hs : E) = N (f ⁻¹' s) (hf hs) :=
  congrArg N.toChannel (BoundedMeasurable.ext fun _ => rfl)

/-- Measurable relabeling is deterministic post-processing. -/
lemma mapOutcome_isPostprocessing (N : Measurement Ω' E) (f : Ω' → Ω) (hf : Measurable f) :
    N.mapOutcome f hf ≤ₚ N :=
  ⟨comap f hf, isNormal_comap f hf, rfl⟩

/-! ## C. Born laws -/

/-- The Born law of a post-processing through `K` is the Born law of the original measurement
composed with the kernel of `K`. -/
lemma probabilityLaw_comp {M : Measurement Ω E} {N : Measurement Ω' E}
    {K : Channel (BoundedMeasurable Ω) (BoundedMeasurable Ω')} (hK : K.IsNormal)
    (h : M.toChannel = N.toChannel.comp K) (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal) :
    (M.probabilityLaw ω hω : Measure Ω) = toKernel K hK ∘ₘ N.probabilityLaw ω hω := by
  change _ = toKernel K hK ∘ₘ (toMeasure (ω.comp N.toChannel) (N.isNormal_comp hω) : Measure Ω')
  rw [← toMeasure_comp K hK _ (N.isNormal_comp hω)]
  unfold probabilityLaw
  congr 2
  rw [h, comp_assoc]

/-- The Born law of a post-processing is the Born law of the original measurement composed with a
Markov kernel, the same for every state. -/
lemma IsPostprocessing.probabilityLaw_eq {M : Measurement Ω E} {N : Measurement Ω' E}
    (h : M ≤ₚ N) : ∃ (κ : Kernel Ω' Ω) (_ : IsMarkovKernel κ), ∀ (ω : 𝓢[ℝ, E])
      (hω : ω.IsNormal), (M.probabilityLaw ω hω : Measure Ω) = κ ∘ₘ N.probabilityLaw ω hω :=
  let ⟨K, hK, hMN⟩ := h
  ⟨toKernel K hK, inferInstance, probabilityLaw_comp hK hMN⟩

/-- Relabeling outcomes pushes each Born law forward along the relabeling map. -/
lemma probabilityLaw_mapOutcome (N : Measurement Ω' E) (f : Ω' → Ω) (hf : Measurable f)
    (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal) :
    (N.mapOutcome f hf).probabilityLaw ω hω = (N.probabilityLaw ω hω).map f :=
  ProbabilityMeasure.toMeasure_injective <| Measure.ext fun s hs => by
    rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply hf hs, probabilityLaw_apply _ _ _ s hs,
      probabilityLaw_apply _ _ _ _ (hf hs), coe_mapOutcome_apply]

end Measurement

end ProbabilisticTheory
