/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.Covariance.CausalKernel
public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.RetardedKernel.Convolution
public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.RetardedKernel.FourierForm

/-!

# Lorentz covariance of the causal kernel on the Fourier side

The Fourier transform of the causal propagator kernel is invariant under orthochronous Lorentz
transformations acting on the frequencies by the inverse transpose. It is odd under the others.

## i. Overview

The covariance of the causal kernel is proved on test functions (`causalKernel_actDist`). Density
carries it to the tempered extension. The Fourier transform of a tempered functional `T` is
`g ↦ T (𝓕 g)`. For a Lorentz transformation `Λ` the transform of `g ∘ (Λ⁻¹)ᵀ` is `𝓕 g ∘ Λ`
because `|det Λ| = 1`. So a functional with `T (φ ∘ Λ) = c * T φ` has a transform with
`T̂ (g ∘ (Λ⁻¹)ᵀ) = c * T̂ g`. No second Fourier theory enters. The transport is one lemma about
any tempered functional.

## ii. Key results

- `lorentzSplit` : a Lorentz transformation on the split space.
- `freqAct` : the induced action on Schwartz functions of the frequency by `(Λ⁻¹)ᵀ`.
- `fourierDist` : the Fourier transform of a tempered functional.
- `fourierDist_freqAct` : covariance of a functional transports to its transform.
- `temperedCausal` : the tempered causal propagator kernel.
- `fourierDist_temperedCausal_freqAct` : the transform of the causal kernel is invariant under
  orthochronous transformations.
- `fourierDist_temperedCausal_freqAct_of_not` : it changes sign under the others.

## iii. Table of contents

- A. The action on frequencies
- B. Transport of covariance
- C. The tempered causal kernel
- D. The causal kernel on the Fourier side

## iv. References

None.

## A. The action on frequencies

- `lorentzSplit` : a Lorentz transformation on the split space.
- `abs_det_lorentzSplit` : its determinant has absolute value one.
- `freqAct` : the induced action on Schwartz functions of the frequency.
- `fourier_freqAct` : the transform of the transformed function.

## B. Transport of covariance

- `fourierDist` : the Fourier transform of a tempered functional.
- `fourierDist_freqAct` : covariance of a functional transports to its transform.

## C. The tempered causal kernel

- `temperedCausal` : the tempered causal propagator kernel.
- `temperedCausal_comp` : its covariance on Schwartz functions.

## D. The causal kernel on the Fourier side

- `fourierDist_temperedCausal_freqAct` : invariance under orthochronous transformations.
- `fourierDist_temperedCausal_freqAct_of_not` : sign change under the others.
-/

@[expose] public section

noncomputable section

open scoped SchwartzMap FourierTransform Distributions
open SchwartzMap MeasureTheory TopologicalSpace KleinGordon.Spacetime KleinGordon.Solution
  PoincareGroup

namespace KleinGordon

variable {d : ℕ}

/-- A Lorentz transformation as a linear equivalence of the split space. -/
def lorentzSplit (Λ : LorentzGroup d) : SplitSpace d ≃L[ℝ] SplitSpace d :=
  (splitEquiv d).trans ((lorentzCLE Λ).trans (splitEquiv d).symm)

lemma lorentzSplit_apply (Λ : LorentzGroup d) (ξ : SplitSpace d) :
    lorentzSplit Λ ξ = (splitEquiv d).symm (lorentzCLE Λ (splitEquiv d ξ)) := rfl

/-- The determinant of a Lorentz transformation of the split space has absolute value one. -/
lemma abs_det_lorentzSplit (Λ : LorentzGroup d) :
    |LinearMap.det (lorentzSplit Λ : SplitSpace d →ₗ[ℝ] SplitSpace d)| = 1 := by
  have h := LinearMap.det_conj (lorentzCLE Λ : SpaceTime d →ₗ[ℝ] SpaceTime d)
    (splitEquiv d).symm.toLinearEquiv
  rw [← abs_det_lorentzCLE Λ, ← h]
  rfl

/-- **The action on frequencies.** A Lorentz transformation acts on Schwartz functions of the
frequency by the inverse transpose. -/
def freqAct (Λ : LorentzGroup d) : 𝓢(SplitSpace d, ℂ) →L[ℂ] 𝓢(SplitSpace d, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Fourier.invTranspose (lorentzSplit Λ))

lemma freqAct_apply (Λ : LorentzGroup d) (g : 𝓢(SplitSpace d, ℂ)) (ξ : SplitSpace d) :
    freqAct Λ g ξ = g (Fourier.invTranspose (lorentzSplit Λ) ξ) := rfl

/-- **The transform of the transformed function.** -/
lemma fourier_freqAct (Λ : LorentzGroup d) (g : 𝓢(SplitSpace d, ℂ)) (ξ : SplitSpace d) :
    𝓕 (freqAct Λ g) ξ = 𝓕 g (lorentzSplit Λ ξ) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  have h := Fourier.fourier_comp_invTranspose (lorentzSplit Λ) (⇑g) ξ
  rw [abs_det_lorentzSplit, one_smul] at h
  exact h

/-- The real or imaginary part of a complex Schwartz function of the split space as a real
Schwartz function of spacetime. -/
def partSource (part : ℂ →L[ℝ] ℝ) : 𝓢(SplitSpace d, ℂ) →L[ℝ] 𝓢(SpaceTime d, ℝ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (splitEquiv d).symm ∘L
    SchwartzMap.postcompCLM part

lemma partSource_apply (part : ℂ →L[ℝ] ℝ) (h : 𝓢(SplitSpace d, ℂ)) (x : SpaceTime d) :
    partSource part h x = part (h ((splitEquiv d).symm x)) := rfl

/-- **The Fourier transform of a tempered functional.** It sends `g` to the functional applied to
the real and the imaginary part of `𝓕 g`. -/
def fourierDist (T : 𝓢(SpaceTime d, ℝ) →L[ℝ] ℝ) (g : 𝓢(SplitSpace d, ℂ)) : ℂ :=
  ⟨T (partSource Complex.reCLM (𝓕 g)), T (partSource Complex.imCLM (𝓕 g))⟩

lemma partSource_lorentz (part : ℂ →L[ℝ] ℝ) (Λ : LorentzGroup d) (h : 𝓢(SplitSpace d, ℂ)) :
    partSource part (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (lorentzSplit Λ) h) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (lorentzCLE Λ) (partSource part h) := by
  ext x
  simp [partSource_apply, lorentzSplit_apply]

/-- **Covariance of a functional transports to its transform.** If `T (φ ∘ Λ) = c * T φ` then
the transform of `T` at `g ∘ (Λ⁻¹)ᵀ` is `c` times its value at `g`. -/
lemma fourierDist_freqAct (T : 𝓢(SpaceTime d, ℝ) →L[ℝ] ℝ) (Λ : LorentzGroup d) (c : ℝ)
    (hT : ∀ φ : 𝓢(SpaceTime d, ℝ),
      T (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (lorentzCLE Λ) φ) = c * T φ)
    (g : 𝓢(SplitSpace d, ℂ)) : fourierDist T (freqAct Λ g) = c * fourierDist T g := by
  have h : 𝓕 (freqAct Λ g) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (lorentzSplit Λ) (𝓕 g) := by
    ext ξ
    exact fourier_freqAct Λ g ξ
  apply Complex.ext
  · simp [fourierDist, h, partSource_lorentz, hT]
  · simp [fourierDist, h, partSource_lorentz, hT]

/-- The advanced kernel as a tempered functional: the retarded one reflected through the origin. -/
def temperedAdvanced (d : ℕ) (m : ℝ) : 𝓢(SpaceTime d, ℝ) →L[ℝ] ℝ :=
  (temperedKernel d m).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (ContinuousLinearEquiv.neg ℝ))

/-- **The tempered causal propagator kernel.** -/
def temperedCausal (d : ℕ) (m : ℝ) : 𝓢(SpaceTime d, ℝ) →L[ℝ] ℝ :=
  temperedKernel d m - temperedAdvanced d m

lemma compCLM_neg_ofTestFunction (φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (ContinuousLinearEquiv.neg ℝ)
      (ofTestFunction φ) = ofTestFunction (actTestFunction (pointReflection 0)⁻¹ φ) := by
  ext x
  simp [ofTestFunction_apply, pointReflection_smul]

lemma temperedAdvanced_ofTestFunction (m : ℝ) (φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    temperedAdvanced d m (ofTestFunction φ) = advancedPointSource m (0 : SpaceTime d) φ := by
  have h := retardedPointSource_actDist_of_not (m := m) (not_isOrthochronous_pointReflection 0)
    (0 : SpaceTime d)
  have h0 : pointReflection (0 : SpaceTime d) • (0 : SpaceTime d) = 0 := by
    rw [pointReflection_smul, sub_zero]
  rw [h0] at h
  rw [temperedAdvanced, ContinuousLinearMap.comp_apply, compCLM_neg_ofTestFunction,
    temperedKernel_apply, ← actDist_apply, h]

lemma temperedCausal_ofTestFunction (m : ℝ) (φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    temperedCausal d m (ofTestFunction φ) = causalKernel m φ := by
  rw [temperedCausal, sub_apply, temperedKernel_apply,
    temperedAdvanced_ofTestFunction]
  rfl

lemma compCLM_lorentz_ofTestFunction (Λ : LorentzGroup d)
    (φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (lorentzCLE Λ) (ofTestFunction φ) =
      ofTestFunction (actTestFunction (⟨0, Λ⟩ : PoincareGroup d)⁻¹ φ) := by
  ext x
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ofTestFunction_apply, actTestFunction_apply, inv_inv, smul_def, add_zero]
  rfl

/-- **Covariance of the tempered causal kernel.** If the causal kernel on test functions picks up
the factor `c` under `Λ` then so does its tempered extension on Schwartz functions. -/
lemma temperedCausal_comp (m : ℝ) (Λ : LorentzGroup d) (c : ℝ)
    (h : ∀ φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ),
      causalKernel m (actTestFunction (⟨0, Λ⟩ : PoincareGroup d)⁻¹ φ) = c * causalKernel m φ)
    (φ : 𝓢(SpaceTime d, ℝ)) :
    temperedCausal d m (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (lorentzCLE Λ) φ) =
      c * temperedCausal d m φ := by
  have key : (temperedCausal d m).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (lorentzCLE Λ)) =
      c • temperedCausal d m := by
    refine tempered_ext d fun ψ => ?_
    simp only [ContinuousLinearMap.comp_apply, compCLM_lorentz_ofTestFunction,
      temperedCausal_ofTestFunction, smul_apply, smul_eq_mul]
    exact h ψ
  exact congrArg (fun T : 𝓢(SpaceTime d, ℝ) →L[ℝ] ℝ => T φ) key

/-- **The causal kernel on the Fourier side is Lorentz invariant.** Its transform is unchanged
when an orthochronous Lorentz transformation acts on the frequencies by the inverse transpose. -/
lemma fourierDist_temperedCausal_freqAct (m : ℝ) {Λ : LorentzGroup d}
    (hΛ : LorentzGroup.IsOrthochronous Λ) (g : 𝓢(SplitSpace d, ℂ)) :
    fourierDist (temperedCausal d m) (freqAct Λ g) = fourierDist (temperedCausal d m) g := by
  have h := causalKernel_actDist m (g := (⟨0, Λ⟩ : PoincareGroup d)) hΛ rfl
  have htest : ∀ ψ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ),
      causalKernel m (actTestFunction (⟨0, Λ⟩ : PoincareGroup d)⁻¹ ψ) = 1 * causalKernel m ψ :=
    fun ψ => by rw [← actDist_apply, h, one_mul]
  have := fourierDist_freqAct (temperedCausal d m) Λ 1 (temperedCausal_comp m Λ 1 htest) g
  simpa using this

/-- **The causal kernel on the Fourier side is odd under time reversal.** Its transform changes
sign when a non-orthochronous Lorentz transformation acts on the frequencies. -/
lemma fourierDist_temperedCausal_freqAct_of_not (m : ℝ) {Λ : LorentzGroup d}
    (hΛ : ¬ LorentzGroup.IsOrthochronous Λ) (g : 𝓢(SplitSpace d, ℂ)) :
    fourierDist (temperedCausal d m) (freqAct Λ g) = -fourierDist (temperedCausal d m) g := by
  have h := causalKernel_actDist_of_not m (g := (⟨0, Λ⟩ : PoincareGroup d)) hΛ rfl
  have htest : ∀ ψ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ),
      causalKernel m (actTestFunction (⟨0, Λ⟩ : PoincareGroup d)⁻¹ ψ) = (-1) * causalKernel m ψ :=
    fun ψ => by rw [← actDist_apply, h, neg_mul, one_mul]; rfl
  have := fourierDist_freqAct (temperedCausal d m) Λ (-1) (temperedCausal_comp m Λ (-1) htest) g
  simpa using this

end KleinGordon
