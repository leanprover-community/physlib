/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Classical.NormalState
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Normal classical channels

The normal channels between classical systems are the Markov kernels between their
configuration spaces.

## i. Overview

A Markov kernel `κ` from `Y` to `X` gives each configuration `x` of the second system a
probability distribution `κ x` of configurations of the first. It turns an observable `f` of the
first system into its average `x ↦ ∫ f d(κ x)`, an observable of the second. This channel is
normal because each average is.

Conversely a normal channel `K` turns each Dirac state of the second system into a normal state
`f ↦ K f x` of the first. Its probability distribution depends measurably on `x`, so these
distributions form a Markov kernel. The two constructions are inverse.

A measurable map `φ : Y → X` moves every configuration with certainty. Its Koopman channel turns
an observable `f` into `f ∘ φ` and is the channel of the deterministic Markov kernel of `φ`.

## ii. Key results

- `ProbabilisticTheory.Classical.ofKernel` : the channel of a Markov kernel.
- `ProbabilisticTheory.Classical.toKernel` : the Markov kernel of a normal channel.
- `ProbabilisticTheory.Classical.kernelEquiv` : normal channels are Markov kernels.
- `ProbabilisticTheory.Classical.koopman` : the channel of a measurable map of configurations.

## iii. Table of contents

- A. Channels of Markov kernels
- B. Markov kernels of normal channels
- C. Normal channels are Markov kernels
- D. Koopman channels

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory.Classical

open MeasureTheory ProbabilityTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-! ## A. Channels of Markov kernels -/

/-- The average `x ↦ ∫ f d(κ x)` of an observable against a Markov kernel. -/
noncomputable def average (κ : Kernel Y X) [IsMarkovKernel κ] (f : Observables (measurable X)) :
    Observables (measurable Y) :=
  ofFun (fun x ↦ ∫ y, f y ∂(κ x))
    (measurable_coe f).stronglyMeasurable.integral_kernel.measurable
    (have ⟨C, hC⟩ := exists_abs_le f
    ⟨C, fun x ↦ by
      simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const (μ := κ x) (f := f)
        (.of_forall fun y ↦ by simpa [Real.norm_eq_abs] using hC y)⟩)

/-- The channel of a Markov kernel `κ` turns each observable into its average against `κ`. -/
noncomputable def ofKernel (κ : Kernel Y X) [IsMarkovKernel κ] :
    Channel (measurable X) (measurable Y) :=
  .ofLinearMap
    { toFun := average κ
      map_add' f g := DFunLike.ext _ _ fun x ↦ map_add (ofDistribution (κ x)) f g
      map_smul' c f := DFunLike.ext _ _ fun x ↦ by
        rw [RingHom.id_apply, smul_apply]
        exact map_smul (ofDistribution (κ x)) c f }
    (fun _ hf ↦ le_def.mpr fun x ↦ map_nonneg (ofDistribution (κ x)) hf)
    (DFunLike.ext _ _ fun x ↦ map_one (ofDistribution (κ x)))

@[simp]
lemma ofKernel_apply (κ : Kernel Y X) [IsMarkovKernel κ]
    (f : Observables (measurable X)) (x : Y) :
    ofKernel κ f x = ∫ y, f y ∂(κ x) := rfl

/-- The channel of a Markov kernel is normal. -/
lemma isNormal_ofKernel (κ : Kernel Y X) [IsMarkovKernel κ] : (ofKernel κ).IsNormal :=
  fun f g hf hg ↦ isLUB_range_of_apply fun x ↦ isNormal_ofDistribution (κ x) f g hf hg

/-! ## B. Markov kernels of normal channels -/

variable (K : Channel (measurable X) (measurable Y)) (hK : K.IsNormal)

include hK in
/-- A normal channel turns each Dirac state into a normal state. -/
lemma isNormal_dirac_comap (x : Y) : ((dirac _ x).comap K).IsNormal :=
  hK.comp (isNormal_dirac x)

/-- The Markov kernel of a normal channel `K` gives at `x` the probability distribution of the
state `f ↦ K f x`. -/
noncomputable def toKernel : Kernel Y X where
  toFun x := distribution ((dirac _ x).comap K) (isNormal_dirac_comap K hK x)
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs ↦ by
    simp only [distribution_apply _ _ ⟨s, hs⟩]
    exact ENNReal.measurable_ofReal.comp (measurable_coe (K (indicator ⟨s, hs⟩)))

lemma toKernel_apply (s : Event X) (x : Y) :
    toKernel K hK x s = ENNReal.ofReal (K (indicator s) x) :=
  distribution_apply _ (isNormal_dirac_comap K hK x) s

instance : IsMarkovKernel (toKernel K hK) :=
  ⟨fun x ↦ inferInstanceAs <|
    IsProbabilityMeasure (distribution ((dirac _ x).comap K) (isNormal_dirac_comap K hK x))⟩

/-! ## C. Normal channels are Markov kernels -/

/-- A normal channel is the channel of its Markov kernel. -/
lemma ofKernel_toKernel : ofKernel (toKernel K hK) = K :=
  Channel.ext fun f ↦ DFunLike.ext _ _ fun x ↦
    DFunLike.congr_fun (ofDistribution_distribution _ (isNormal_dirac_comap K hK x)) f

/-- A Markov kernel is the kernel of its channel. -/
lemma toKernel_ofKernel (κ : Kernel Y X) [IsMarkovKernel κ] :
    toKernel (ofKernel κ) (isNormal_ofKernel κ) = κ := by
  ext x s hs
  rw [toKernel_apply _ _ ⟨s, hs⟩, ofKernel_apply, coe_indicator, integral_indicator_one hs,
    ofReal_measureReal]

/-- The normal channels between two classical systems are the Markov kernels between their
configuration spaces. -/
noncomputable def kernelEquiv : {K : Channel (measurable X) (measurable Y) // K.IsNormal} ≃
    {κ : Kernel Y X // IsMarkovKernel κ} where
  toFun K := ⟨toKernel K.1 K.2, inferInstance⟩
  invFun κ := have := κ.2; ⟨ofKernel κ.1, isNormal_ofKernel κ.1⟩
  left_inv K := Subtype.ext (ofKernel_toKernel K.1 K.2)
  right_inv κ := have := κ.2; Subtype.ext (toKernel_ofKernel κ.1)

/-! ## D. Koopman channels -/

/-- The Koopman channel of a measurable map `φ` of configurations turns `f` into `f ∘ φ`. -/
noncomputable def koopman (φ : Y → X) (hφ : Measurable φ) : Channel (measurable X) (measurable Y) :=
  .ofLinearMap
    { toFun f := ofFun (f ∘ φ) ((measurable_coe f).comp hφ)
        (have ⟨C, hC⟩ := exists_abs_le f
        ⟨C, fun x ↦ hC (φ x)⟩)
      map_add' _ _ := DFunLike.coe_injective rfl
      map_smul' c f := DFunLike.ext _ _ fun x ↦ by
        rw [RingHom.id_apply, smul_apply]; exact smul_apply c f (φ x) }
    (fun _ hf ↦ le_def.mpr fun x ↦ le_def.mp hf (φ x))
    (DFunLike.coe_injective rfl)

@[simp]
lemma coe_koopman (φ : Y → X) (hφ : Measurable φ)
    (f : Observables (measurable X)) :
    ⇑(koopman φ hφ f) = f ∘ φ := rfl

/-- The Koopman channel of `φ` is the channel of the deterministic Markov kernel of `φ`. -/
lemma ofKernel_deterministic (φ : Y → X) (hφ : Measurable φ) :
    ofKernel (Kernel.deterministic φ hφ) = koopman φ hφ :=
  Channel.ext fun f ↦ DFunLike.ext _ _ fun x ↦ by
    rw [ofKernel_apply, Kernel.deterministic_apply,
      integral_dirac' _ _ (measurable_coe f).stronglyMeasurable, coe_koopman, Function.comp_apply]

end ProbabilisticTheory.Classical
