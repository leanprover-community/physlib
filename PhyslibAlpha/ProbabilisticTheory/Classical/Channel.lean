/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Classical.NormalStates
public import PhyslibAlpha.ProbabilisticTheory.Channel.Normal
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Classical channels

Normal channels between classical systems of observables are exactly Markov kernels.

## i. Overview

A channel between two classical systems sends observables of the target system `Ω` to observables
of the source system `Ω'`. At each outcome `x` of `Ω'` it gives a normal state of `Ω` when it is
normal, that is a probability distribution over `Ω`. So a normal classical channel is exactly a
Markov kernel from `Ω'` to `Ω`: the observable `f` is sent to its average `x ↦ ∫ f d(κ x)`.
Relabeling outcomes along a measurable map is the deterministic case.

In a normal state of `Ω'`, the channel turns the outcome distribution into its composite with the
kernel.

## ii. Key results

- `BoundedMeasurable.comap` : relabeling outcomes along a measurable map.
- `BoundedMeasurable.ofKernel` : the channel of a Markov kernel.
- `BoundedMeasurable.toKernel` : the Markov kernel of a normal channel.
- `BoundedMeasurable.kernelEquiv` : **normal classical channels are Markov kernels**.
- `BoundedMeasurable.toMeasure_comp` : a normal channel acts on outcome distributions by composing
  with its kernel.

## iii. Table of contents

- A. Relabeling outcomes
- B. The channel of a Markov kernel
- C. The Markov kernel of a normal channel
- D. The correspondence

## iv. References

* None.

-/

@[expose] public section

namespace BoundedMeasurable
open ProbabilisticTheory

open UnitalPositiveLinearMap MeasureTheory ProbabilityTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-! ## A. Relabeling outcomes -/

/-- Relabeling outcomes along a measurable map `g : Ω' → Ω`: the observable `f` of `Ω` becomes
the observable `f ∘ g` of `Ω'`. -/
def comap (g : Ω' → Ω) (hg : Measurable g) : Channel (BoundedMeasurable Ω) (BoundedMeasurable Ω') :=
  ofLinearMap ⟨⟨fun f => mk (f ∘ g) (f.measurable.comp hg) (f.exists_bound.imp fun _ hC x =>
    hC (g x)), fun _ _ => rfl⟩, fun _ _ => rfl⟩ (fun _ hf => le_def.2 fun x => le_def.1 hf (g x))
    rfl

@[simp] lemma comap_apply (g : Ω' → Ω) (hg : Measurable g) (f : BoundedMeasurable Ω) (x : Ω') :
    comap g hg f x = f (g x) := rfl

lemma isNormal_comap (g : Ω' → Ω) (hg : Measurable g) : (comap g hg).IsNormal :=
  fun _ _ _ hf => isLUB_range_iff.2 fun x => isLUB_range_iff.1 hf (g x)

/-! ## B. The channel of a Markov kernel -/

section Kernel

variable (κ : Kernel Ω' Ω) [IsMarkovKernel κ]

/-- The average `x ↦ ∫ f d(κ x)` of an observable `f` against a Markov kernel. -/
noncomputable def kernelAverage (f : BoundedMeasurable Ω) : BoundedMeasurable Ω' :=
  mk (fun x => ∫ y, f y ∂(κ x)) f.measurable.stronglyMeasurable.integral_kernel.measurable
    (f.exists_bound.imp fun _ hC x => abs_apply_le (ofMeasure ⟨κ x, inferInstance⟩) hC)

@[simp] lemma kernelAverage_apply (f : BoundedMeasurable Ω) (x : Ω') :
    kernelAverage κ f x = ∫ y, f y ∂(κ x) := rfl

/-- The channel of a Markov kernel `κ` from `Ω'` to `Ω`: the observable `f` becomes its average
`x ↦ ∫ f d(κ x)`. -/
noncomputable def ofKernel : Channel (BoundedMeasurable Ω) (BoundedMeasurable Ω') :=
  ofLinearMap
    { toFun := kernelAverage κ
      map_add' f g := ext fun x => map_add (ofMeasure ⟨κ x, inferInstance⟩) f g
      map_smul' c f := ext fun x => map_smul (ofMeasure ⟨κ x, inferInstance⟩) c f }
    (fun _ hf => le_def.2 fun x => map_nonneg (ofMeasure ⟨κ x, inferInstance⟩) hf)
    (ext fun x => map_one (ofMeasure ⟨κ x, inferInstance⟩))

@[simp] lemma ofKernel_apply (f : BoundedMeasurable Ω) (x : Ω') :
    ofKernel κ f x = ∫ y, f y ∂(κ x) := rfl

lemma isNormal_ofKernel : (ofKernel κ).IsNormal :=
  fun f g hf hg => isLUB_range_iff.2 fun x =>
    isNormal_ofMeasure ⟨κ x, inferInstance⟩ f g hf hg

end Kernel

/-! ## C. The Markov kernel of a normal channel -/

section Normal

variable (K : Channel (BoundedMeasurable Ω) (BoundedMeasurable Ω')) (hK : K.IsNormal)
include hK

lemma isNormal_eval_comp (x : Ω') : ((eval x).comp K).IsNormal :=
  UnitalPositiveLinearMap.IsNormal.comp hK (isNormal_eval x)

/-- The Markov kernel of a normal channel: at `x`, the outcome distribution of the state
`f ↦ K f x`. -/
noncomputable def toKernel : Kernel Ω' Ω where
  toFun x := toMeasure ((eval x).comp K) (isNormal_eval_comp K hK x)
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs => by
    simp only [toMeasure_apply _ _ hs]
    exact ENNReal.measurable_ofReal.comp (K (indicator s hs)).measurable

lemma toKernel_apply {s : Set Ω} (hs : MeasurableSet s) (x : Ω') :
    toKernel K hK x s = ENNReal.ofReal (K (indicator s hs) x) :=
  toMeasure_apply _ _ hs

instance : IsMarkovKernel (toKernel K hK) :=
  ⟨fun x => (toMeasure ((eval x).comp K) (isNormal_eval_comp K hK x)).2⟩

/-- A normal channel acts on outcome distributions by composing with its kernel. -/
lemma toMeasure_comp (σ : 𝓢[ℝ, BoundedMeasurable Ω']) (hσ : σ.IsNormal) :
    (toMeasure (σ.comp K) (UnitalPositiveLinearMap.IsNormal.comp hK hσ) : Measure Ω) =
      toKernel K hK ∘ₘ toMeasure σ hσ := by
  ext s hs
  have h0 : 0 ≤ K (indicator s hs) := K.map_nonneg (indicator_nonneg s hs)
  rw [Measure.bind_apply hs (toKernel K hK).aemeasurable, toMeasure_apply _ _ hs]
  simp only [toKernel_apply K hK hs]
  rw [← ofReal_integral_eq_lintegral_ofReal ((K (indicator s hs)).integrable _)
    (.of_forall (le_def.1 h0))]
  exact congrArg ENNReal.ofReal (congrFun (congrArg DFunLike.coe
    (ofMeasure_toMeasure σ hσ)) (K (indicator s hs))).symm

end Normal

/-! ## D. The correspondence -/

lemma ofKernel_toKernel (K : Channel (BoundedMeasurable Ω) (BoundedMeasurable Ω'))
    (hK : K.IsNormal) :
    ofKernel (toKernel K hK) = K :=
  UnitalPositiveLinearMap.ext fun f => ext fun x =>
    congrFun (congrArg DFunLike.coe (ofMeasure_toMeasure _ (isNormal_eval_comp K hK x))) f

lemma toKernel_ofKernel (κ : Kernel Ω' Ω) [IsMarkovKernel κ] :
    toKernel (ofKernel κ) (isNormal_ofKernel κ) = κ := by
  ext x s hs
  rw [toKernel_apply _ _ hs, ofKernel_apply]
  simp only [BoundedMeasurable.indicator_apply]
  rw [integral_indicator_one hs, ofReal_measureReal]

/-- **Normal classical channels are Markov kernels.** -/
noncomputable def kernelEquiv :
    {K : Channel (BoundedMeasurable Ω) (BoundedMeasurable Ω') // K.IsNormal} ≃
      {κ : Kernel Ω' Ω // IsMarkovKernel κ} where
  toFun K := ⟨toKernel K.1 K.2, inferInstance⟩
  invFun κ := have := κ.2; ⟨ofKernel κ.1, isNormal_ofKernel κ.1⟩
  left_inv K := Subtype.ext (ofKernel_toKernel K.1 K.2)
  right_inv κ := by have := κ.2; exact Subtype.ext (toKernel_ofKernel κ.1)

end BoundedMeasurable

