/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ClassicalMechanics.Observables.NormalState
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Normal classical channels

The normal channels between classical systems are the Markov kernels between their
configuration spaces.

## i. Overview

A Markov kernel `κ` from `Ω'` to `Ω` gives each configuration `x` of the second system a
probability distribution `κ x` of configurations of the first. It turns an observable `f` of the
first system into its average `x ↦ ∫ f d(κ x)`, an observable of the second. This channel is
normal because each average is.

Conversely a normal channel `K` turns each Dirac state of the second system into a normal state
`f ↦ K f x` of the first. Its probability distribution depends measurably on `x`, so these
distributions form a Markov kernel. The two constructions are inverse.

## ii. Key results

- `ProbabilisticTheory.ClassicalChannel` : channels between classical systems.
- `ProbabilisticTheory.Classical.ofKernel` : the channel of a Markov kernel.
- `ProbabilisticTheory.Classical.toKernel` : the Markov kernel of a normal channel.
- `ProbabilisticTheory.Classical.kernelEquiv` : normal channels are Markov kernels.

## iii. Table of contents

- A. Channels of Markov kernels
- B. Markov kernels of normal channels
- C. Normal channels are Markov kernels

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

/-- A channel from the bounded measurable observables on `Ω` to those on `Ω'`. -/
abbrev ClassicalChannel (Ω Ω' : Type*) [MeasurableSpace Ω] [MeasurableSpace Ω'] :=
  Channel (ofCStarAlgebra (Classical.measurableAlgebra Ω))
    (ofCStarAlgebra (Classical.measurableAlgebra Ω'))

namespace Classical

open MeasureTheory ProbabilityTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-! ## A. Channels of Markov kernels -/

/-- The average `x ↦ ∫ f d(κ x)` of an observable against a Markov kernel. -/
noncomputable def kernelAverage (κ : Kernel Ω' Ω) [IsMarkovKernel κ] (f : ClassicalObservable Ω) :
    ClassicalObservable Ω' :=
  ofFun (fun x ↦ ∫ y, toFun f y ∂(κ x))
    (measurable_toFun f).stronglyMeasurable.integral_kernel.measurable
    ⟨‖(f : measurableAlgebra Ω)‖, fun x ↦ by
      simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const (μ := κ x) (f := toFun f)
        (.of_forall fun y ↦ by simpa [Real.norm_eq_abs] using abs_toFun_le_norm f y)⟩

/-- The channel of a Markov kernel `κ` turns each observable into its average against `κ`. -/
noncomputable def ofKernel (κ : Kernel Ω' Ω) [IsMarkovKernel κ] : ClassicalChannel Ω Ω' :=
  .ofLinearMap
    { toFun := kernelAverage κ
      map_add' f g := toFun_injective <| funext fun x ↦ map_add (ofMeasure ⟨κ x, inferInstance⟩) f g
      map_smul' c f := toFun_injective <| funext fun x ↦ by
        rw [RingHom.id_apply, map_smul]
        exact map_smul (ofMeasure ⟨κ x, inferInstance⟩) c f }
    (fun _ hf ↦ toFun_le_toFun_iff.mp fun x ↦ map_nonneg (ofMeasure ⟨κ x, inferInstance⟩) hf)
    (toFun_injective <| funext fun x ↦ map_one (ofMeasure ⟨κ x, inferInstance⟩))

@[simp]
lemma toFun_ofKernel (κ : Kernel Ω' Ω) [IsMarkovKernel κ] (f : ClassicalObservable Ω) (x : Ω') :
    toFun (ofKernel κ f) x = ∫ y, toFun f y ∂(κ x) := rfl

/-- The channel of a Markov kernel is normal. -/
lemma isNormal_ofKernel (κ : Kernel Ω' Ω) [IsMarkovKernel κ] : (ofKernel κ).IsNormal :=
  fun f g hf hg ↦ isLUB_range_iff.mpr fun x ↦ isNormal_ofMeasure ⟨κ x, inferInstance⟩ f g hf hg

/-! ## B. Markov kernels of normal channels -/

variable (K : ClassicalChannel Ω Ω') (hK : K.IsNormal)

include hK in
/-- A normal channel turns each Dirac state into a normal state. -/
lemma isNormal_dirac_comap (x : Ω') : ((dirac x).comap K).IsNormal :=
  hK.comp (isNormal_dirac x)

/-- The Markov kernel of a normal channel `K` gives at `x` the probability distribution of the
state `f ↦ K f x`. -/
noncomputable def toKernel : Kernel Ω' Ω where
  toFun x := toMeasure ((dirac x).comap K) (isNormal_dirac_comap K hK x)
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs ↦ by
    simp only [toMeasure_apply _ _ hs]
    exact ENNReal.measurable_ofReal.comp (measurable_toFun (K (indicator s hs)))

lemma toKernel_apply {s : Set Ω} (hs : MeasurableSet s) (x : Ω') :
    toKernel K hK x s = ENNReal.ofReal (toFun (K (indicator s hs)) x) :=
  toMeasure_apply _ (isNormal_dirac_comap K hK x) hs

instance : IsMarkovKernel (toKernel K hK) :=
  ⟨fun x ↦ (toMeasure ((dirac x).comap K) (isNormal_dirac_comap K hK x)).2⟩

/-! ## C. Normal channels are Markov kernels -/

/-- A normal channel is the channel of its Markov kernel. -/
lemma ofKernel_toKernel : ofKernel (toKernel K hK) = K :=
  Channel.ext fun f ↦ toFun_injective <| funext fun x ↦ DFunLike.congr_fun (congrArg Subtype.val
    (normalStateEquiv.symm_apply_apply ⟨(dirac x).comap K, isNormal_dirac_comap K hK x⟩)) f

/-- A Markov kernel is the kernel of its channel. -/
lemma toKernel_ofKernel (κ : Kernel Ω' Ω) [IsMarkovKernel κ] :
    toKernel (ofKernel κ) (isNormal_ofKernel κ) = κ := by
  ext x s hs
  rw [toKernel_apply _ _ hs, toFun_ofKernel, toFun_indicator, integral_indicator_one hs,
    ofReal_measureReal]

/-- The normal channels between two classical systems are the Markov kernels between their
configuration spaces. -/
noncomputable def kernelEquiv :
    {K : ClassicalChannel Ω Ω' // K.IsNormal} ≃ {κ : Kernel Ω' Ω // IsMarkovKernel κ} where
  toFun K := ⟨toKernel K.1 K.2, inferInstance⟩
  invFun κ := have := κ.2; ⟨ofKernel κ.1, isNormal_ofKernel κ.1⟩
  left_inv K := Subtype.ext (ofKernel_toKernel K.1 K.2)
  right_inv κ := have := κ.2; Subtype.ext (toKernel_ofKernel κ.1)

end Classical

end ProbabilisticTheory
