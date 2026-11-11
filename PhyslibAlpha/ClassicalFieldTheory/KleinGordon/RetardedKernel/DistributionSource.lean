/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.RetardedKernel.Convolution
public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.RetardedKernel.PointSource
public import PhyslibAlpha.Mathematics.Distribution.ExpTwistCLM

/-!

# The boundary value formula for compactly supported distributional sources

The retarded response of a compactly supported distribution is the limit of the responses to its
damped advanced solutions.

## i. Overview

By transposition the retarded response of a compactly supported distribution `T` against a test
function `φ` is `T` applied to the cut off advanced solution of `φ`
(`retardedDistribution_apply`). For `ε > 0` the cut off advanced solution is replaced by
`x ↦ χ x * Re ⟨φ̂ translated by x, resolvent at 2π w + i ε⟩`. This is the cut off damped kernel
centred at `x`, the boundary value pairing of the kernel for the translate of `φ`. It equals the
conjugate `M_ε C M_{-ε} φ` of the cut off advanced solution `C` by the multiplication with
`exp (ε t)`. Finite order of `T` and the estimates for the twist give that the pairings converge
to the response for every compactly supported distribution.

## ii. Key results

- `timeCLM` : the time coordinate.
- `kernel_twist` : the kernel applied to a twisted test function is the damped kernel.
- `twisted_apply_fourier` : the twisted cut off advanced solution is the cut off resolvent
  pairing of the translate.
- `tendsto_distribution_boundary_value` : the boundary value formula for compactly supported
  distributions.

## iii. Table of contents

- A. The twist in time
- B. The damped kernel centred at a point
- C. Compactly supported distributions

## iv. References

None.

## A. The twist in time

- `timeCLM` : the time coordinate.
- `slice_twist` : the slices of a twisted test function.
- `kernel_twist` : the kernel applied to a twisted test function is the damped kernel.

## B. The damped kernel centred at a point

- `realAdvancedCutoff_eq` : the cut off advanced solution through the point source.
- `twisted_apply` : the twisted cut off advanced solution is the damped kernel at the translate.
- `twisted_apply_fourier` : the same as a resolvent pairing.

## C. Compactly supported distributions

- `tendsto_distribution_boundary_value` : the boundary value formula.
-/

@[expose] public section

noncomputable section

open scoped SchwartzMap Distributions ContDiff FourierTransform
open TopologicalSpace SchwartzMap PoincareGroup KleinGordon.Solution KleinGordon.Spacetime
  MeasureTheory TestFunction TimeSlice CausalRelation LocalOperator Minkowski GreenOperator
  Distribution

namespace KleinGordon
variable {d : ℕ}

/-- The time coordinate as a continuous linear functional. -/
def timeCLM (d : ℕ) : SpaceTime d →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (Space d)).comp (coordinates d : SpaceTime d →L[ℝ] ℝ × Space d)

lemma timeCLM_symm (s : ℝ) (x : Space d) : timeCLM d ((coordinates d).symm (s, x)) = s := by
  simp [timeCLM]

lemma slice_twist (ε : ℝ) (ψ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) (s : ℝ) :
    slice ℂ (sourceEquiv ℂ (TestFunction.postcompCLM Complex.ofRealCLM
      (ExpTwist.twistCLM (timeCLM d) (-ε) ψ))) s =
      (Real.exp (-(ε * s)) : ℂ) • slice ℂ (sourceEquiv ℂ
        (TestFunction.postcompCLM Complex.ofRealCLM ψ)) s := by
  ext x
  simp only [slice_apply, smul_apply, smul_eq_mul]
  show (((ExpTwist.twistCLM (timeCLM d) (-ε) ψ) ((coordinates d).symm (s, x)) : ℝ) : ℂ) =
    ((Real.exp (-(ε * s)) : ℝ) : ℂ) * ((ψ ((coordinates d).symm (s, x)) : ℝ) : ℂ)
  rw [ExpTwist.twistCLM_apply, ExpTwist.twist, timeCLM_symm]
  push_cast
  ring_nf

/-- The kernel at the origin applied to a twisted test function is the damped kernel. -/
lemma kernel_twist (m ε : ℝ) (ψ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    retardedPointSource m (0 : SpaceTime d) (ExpTwist.twistCLM (timeCLM d) (-ε) ψ) =
      (dampedKernel (m ^ 2) ε
        (sourceEquiv ℂ (TestFunction.postcompCLM Complex.ofRealCLM ψ))).re := by
  rw [retardedPointSource_zero_eq]
  congr 1
  unfold dampedKernel
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [slice_twist, map_smul]
  simp

lemma realAdvancedCutoff_eq (m : ℝ) (χ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ))
    (g : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) (p : SpaceTime d) :
    realAdvancedCutoff m χ g p = χ p * retardedPointSource m p g := by
  obtain ⟨f, rfl⟩ := (testFieldEquiv ℝ (d := d)).surjective g
  rw [realAdvancedCutoff_apply]
  rfl

lemma tsupport_realAdvancedCutoff_subset (m : ℝ) (χ g : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    tsupport ⇑(realAdvancedCutoff m χ g) ⊆ tsupport χ := by
  have : ⇑(realAdvancedCutoff m χ g) = fun p => χ p * retardedPointSource m p g :=
    funext (realAdvancedCutoff_eq m χ g)
  rw [this]
  exact tsupport_mul_subset_left (f := ⇑χ) (g := fun p => retardedPointSource m p g)

lemma precompTranslationCLM_twistCLM (a : ℝ) (p : SpaceTime d)
    (g : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    precompTranslationCLM p (ExpTwist.twistCLM (timeCLM d) a g) =
      Real.exp (a * timeCLM d p) • ExpTwist.twistCLM (timeCLM d) a (precompTranslationCLM p g) := by
  ext x
  simp only [precompTranslationCLM_apply, ExpTwist.twistCLM_apply, ExpTwist.twist, map_add,
    smul_apply, smul_eq_mul]
  rw [mul_add, Real.exp_add]
  ring

/-- **The twisted advanced response is the damped kernel centred at `p`.** -/
lemma twisted_apply (m ε : ℝ) (χ φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) (p : SpaceTime d) :
    ExpTwist.twistCLM (timeCLM d) ε (realAdvancedCutoff m χ
        (ExpTwist.twistCLM (timeCLM d) (-ε) φ)) p =
      χ p * (dampedKernel (m ^ 2) ε
        (sourceEquiv ℂ
          (TestFunction.postcompCLM Complex.ofRealCLM (precompTranslationCLM p φ)))).re := by
  rw [ExpTwist.twistCLM_apply, realAdvancedCutoff_eq, retardedPointSource_eq_kernel_translate,
    precompTranslationCLM_twistCLM, map_smul, ← kernel_twist, smul_eq_mul]
  simp only [ExpTwist.twist]
  have : Real.exp (-ε * timeCLM d p) * Real.exp (ε * timeCLM d p) = 1 := by
    rw [← Real.exp_add]; simp
  calc _ = χ p * (retardedPointSource m (0 : SpaceTime d)
        (ExpTwist.twistCLM (timeCLM d) (- ε) (precompTranslationCLM p φ)) *
        (Real.exp (-ε * timeCLM d p) * Real.exp (ε * timeCLM d p))) := by ring
    _ = _ := by rw [this, mul_one]

/-- For `ε > 0` the twisted advanced response is the cut off resolvent pairing of the translate. -/
lemma twisted_apply_fourier (m : ℝ) {ε : ℝ} (hε : 0 < ε) (χ φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ))
    (p : SpaceTime d) :
    ExpTwist.twistCLM (timeCLM d) ε (realAdvancedCutoff m χ
        (ExpTwist.twistCLM (timeCLM d) (-ε) φ)) p =
      χ p * (fourierPairing (m ^ 2) ε (ofTestFunction (precompTranslationCLM p φ))).re := by
  rw [twisted_apply, fourierPairing_ofTestFunction hε]

lemma splitSource_translate (p : SpaceTime d) (φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    ⇑(splitSource d (ofTestFunction (precompTranslationCLM p φ))) =
      fun v => splitSource d (ofTestFunction φ) (v + (splitEquiv d).symm p) := by
  funext v
  simp [splitSource_apply, ofTestFunction_apply, precompTranslationCLM_apply]

/-- **The pairing of a translate in Fourier variables.** The resolvent pairing of the translate of
`φ` by `p` is the integral of the phase `𝐞 ⟨p, ζ⟩` times the transform of `φ` times the
resolvent. -/
lemma fourierPairing_translate (μ ε : ℝ) (p : SpaceTime d)
    (φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    fourierPairing μ ε (ofTestFunction (precompTranslationCLM p φ)) =
      ∫ ζ : SplitSpace d, (𝐞 (inner ℝ ((splitEquiv d).symm p) ζ) : ℂ) *
        (𝓕 (splitSource d (ofTestFunction φ)) ζ * splitResolvent μ ε ζ) := by
  unfold fourierPairing
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  show 𝓕 (splitSource d (ofTestFunction (precompTranslationCLM p φ))) ζ * splitResolvent μ ε ζ = _
  rw [SchwartzMap.fourier_coe, splitSource_translate, Fourier.fourier_comp_add_right,
    SchwartzMap.fourier_coe]
  simp only [Circle.smul_def, smul_eq_mul]
  ring

/-- **The twisted advanced response in Fourier variables.** For `ε > 0` it is
`x ↦ χ x * Re ∫ 𝐞 ⟨x, ζ⟩ φ̂ (ζ) / (ω_ξ² - (2π w + i ε)²) dζ`. -/
lemma twisted_apply_phase (m : ℝ) {ε : ℝ} (hε : 0 < ε) (χ φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ))
    (p : SpaceTime d) :
    ExpTwist.twistCLM (timeCLM d) ε (realAdvancedCutoff m χ
        (ExpTwist.twistCLM (timeCLM d) (-ε) φ)) p =
      χ p * (∫ ζ : SplitSpace d, (𝐞 (inner ℝ ((splitEquiv d).symm p) ζ) : ℂ) *
        (𝓕 (splitSource d (ofTestFunction φ)) ζ * splitResolvent (m ^ 2) ε ζ)).re := by
  rw [twisted_apply_fourier m hε, fourierPairing_translate]

/-- **The boundary value formula for compactly supported distributional sources.** -/
lemma tendsto_distribution_boundary_value (m : ℝ) (T : compactDistributions (SpaceTime d) ℝ)
    (f : TestField d ℝ) :
    Filter.Tendsto (fun ε : ℝ => T.val (ExpTwist.twistCLM (timeCLM d) ε
      (realAdvancedCutoff m (compactCutoff (compactDistributionBound T))
        (ExpTwist.twistCLM (timeCLM d) (-ε) (testFieldEquiv ℝ f)))))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (retardedDistribution m T (testFieldEquiv ℝ f))) := by
  set χ := compactCutoff (compactDistributionBound T)
  obtain ⟨R₀, hR₀⟩ := χ.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : SpaceTime d)
  have hR : 0 ≤ max R₀ 0 := le_max_right _ _
  have hC : ∀ g, tsupport ⇑(realAdvancedCutoff m χ g) ⊆ Metric.closedBall 0 (max R₀ 0) :=
    fun g => (tsupport_realAdvancedCutoff_subset m χ g).trans
      (hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _)))
  have := ExpTwist.tendsto_distribution_twist (timeCLM d)
    (T.val : 𝓓((⊤ : Opens (SpaceTime d)), ℝ) →L[ℝ] ℝ) (realAdvancedCutoff m χ)
    (testFieldEquiv ℝ f) hR hC
  rw [retardedDistribution_apply]
  exact this.mono_left nhdsWithin_le_nhds

end KleinGordon
