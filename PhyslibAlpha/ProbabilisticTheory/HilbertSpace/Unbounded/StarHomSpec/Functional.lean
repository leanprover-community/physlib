/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.StarHomSpec.SpectralMeasure
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.SpectralIntegral.Construction
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.BoundedIntegralAlgebra

/-!

# The functional calculus of a representation of continuous functions

The bounded integral against the spectral measure of a ⋆-homomorphism `Φ` is `Φ`.

## i. Overview

The spectral measure of a unital ⋆-homomorphism `Φ : C(X, ℂ) → B(H)` reconstructs `Φ` on real
continuous functions. Since the bounded integral against a spectral measure is linear, it
reconstructs `Φ` on all complex continuous functions: `∫ f dE = Φ f`.

## ii. Key results

- `starHomSpectralMeasure_boundedIntegral_real` : the integral of a real continuous function.
- `starHomSpectralMeasure_boundedIntegral` : the integral of a complex continuous function is
  `Φ f`.

## iii. Table of contents

- A. Real and imaginary parts
- B. The diagonal measure
- C. The integral of a continuous function

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open MeasureTheory Set Topology
open scoped ComplexOrder CStarAlgebra InnerProductSpace

namespace QuantumMechanics

section StarHomFunctional

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [CompactSpace X] (Φ : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))

/-! ## A. Real and imaginary parts -/

/-- The real part of a continuous complex function on a compact space, as a compactly supported
continuous real function. -/
def reCompact (f : C(X, ℂ)) : CompactlySupportedContinuousMap X ℝ :=
  ⟨⟨fun z => (f z).re, by fun_prop⟩, HasCompactSupport.of_compactSpace _⟩

/-- The imaginary part of a continuous complex function on a compact space, as a compactly
supported continuous real function. -/
def imCompact (f : C(X, ℂ)) : CompactlySupportedContinuousMap X ℝ :=
  ⟨⟨fun z => (f z).im, by fun_prop⟩, HasCompactSupport.of_compactSpace _⟩

omit [T2Space X] [BorelSpace X] [MeasurableSpace X] in
lemma realToComplex_reCompact_add_I_smul (f : C(X, ℂ)) :
    realToComplex (reCompact f) + Complex.I • realToComplex (imCompact f) = f := by
  ext z
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, realToComplex_apply, reCompact,
    imCompact, smul_eq_mul]
  change ((f z).re : ℂ) + Complex.I * ((f z).im : ℂ) = f z
  conv_rhs => rw [← Complex.re_add_im (f z)]
  ring

/-! ## B. The diagonal measure -/

/-- The diagonal measure `S ↦ ‖E(S) x‖²` of the spectral measure of `Φ` is the Riesz measure of
the vector state of `x`. -/
lemma starHomSpectralMeasure_diagonalMeasure (x : H) :
    (starHomSpectralMeasure Φ).diagonalMeasure x = starHomScalarMeasure Φ x := by
  apply Measure.ext
  intro S hS
  rw [WOTSpectralMeasure.diagonalMeasure_apply _ x S hS]
  have h : ⟪x, (starHomSpectralMeasure Φ S) x⟫_ℂ = ((starHomScalarMeasure Φ x).real S : ℂ) :=
    starHomSpectralOperator_inner_self Φ hS x
  rw [h, Complex.ofReal_re, ofReal_measureReal]

/-- The integral of a real continuous function against the Riesz measure of the vector state of
`x` is the expectation of its operator. -/
lemma integral_starHomScalarMeasure_real (u : CompactlySupportedContinuousMap X ℝ) (x : H) :
    ∫ z, (u z : ℂ) ∂starHomScalarMeasure Φ x = ⟪x, starHomRealOperator Φ u x⟫_ℂ := by
  rw [integral_complex_ofReal, starHomScalarMeasure_integral_complex]
  exact ((starHomRealOperator_isSelfAdjoint Φ u).isSymmetric x x)

/-- The vector state of `x` in the representation `Φ` is integration against its Riesz measure:
`⟪x, Φ f x⟫ = ∫ f dμₓ` for every continuous `f`. -/
lemma integral_starHomScalarMeasure (f : C(X, ℂ)) (x : H) :
    ∫ z, f z ∂starHomScalarMeasure Φ x = ⟪x, Φ f x⟫_ℂ := by
  set μ := starHomScalarMeasure Φ x
  have hint : ∀ u : CompactlySupportedContinuousMap X ℝ, Integrable (fun z => (u z : ℂ)) μ :=
    fun u => by
      refine Integrable.of_bound (by fun_prop) ‖u.toContinuousMap‖ (Filter.Eventually.of_forall
        fun z => ?_)
      simpa using u.toContinuousMap.norm_coe_le_norm z
  have hfun : (fun z => f z) = fun z => (reCompact f z : ℂ) + Complex.I * (imCompact f z : ℂ) := by
    funext z
    have := congrArg (fun g : C(X, ℂ) => g z) (realToComplex_reCompact_add_I_smul f)
    simpa [smul_eq_mul] using this.symm
  have hΦ : Φ f = starHomRealOperator Φ (reCompact f) +
      Complex.I • starHomRealOperator Φ (imCompact f) := by
    conv_lhs => rw [← realToComplex_reCompact_add_I_smul f]
    simp [starHomRealOperator]
  rw [hfun, integral_add (hint _) ((hint _).const_mul Complex.I), integral_const_mul,
    integral_starHomScalarMeasure_real, integral_starHomScalarMeasure_real, hΦ]
  simp [inner_add_right, inner_smul_right]

/-! ## C. The integral of a continuous function -/

section WithNonempty

variable [Nonempty X]

omit [T2Space X] [BorelSpace X] [Nonempty X] [MeasurableSpace X] in
lemma boundedIntegral_bound_of_continuous (f : C(X, ℂ)) : ∃ C, ∀ z, ‖f z‖ ≤ C :=
  ⟨‖f‖, fun z => f.norm_coe_le_norm z⟩

/-- The bounded integral of a real continuous function against the spectral measure of `Φ` is
`Φ` of that function. -/
lemma starHomSpectralMeasure_boundedIntegral_real (u : CompactlySupportedContinuousMap X ℝ) :
    ContinuousLinearMapWOT.toCLM
      (WOTSpectralMeasure.boundedIntegral (starHomSpectralMeasure Φ)
        (fun z => (u z : ℂ)) (by fun_prop) ⟨‖u.toContinuousMap‖, fun z => by
          simpa using u.toContinuousMap.norm_coe_le_norm z⟩) = starHomRealOperator Φ u := by
  ext x
  apply ext_inner_left ℂ
  intro y
  have hfin : IsFiniteMeasure ((starHomSpectralMeasure Φ).scalarMeasure x y).variation := by
    rw [starHomSpectralMeasure_scalarMeasure]
    exact polarizedStarHomScalarMeasure_isFiniteMeasure Φ x y
  have h := WOTSpectralMeasure.boundedIntegral_inner (starHomSpectralMeasure Φ)
    (f := fun z => (u z : ℂ)) (by fun_prop) ⟨‖u.toContinuousMap‖, fun z => by
      simpa using u.toContinuousMap.norm_coe_le_norm z⟩ x y hfin
  have h2 := starHomSpectralMeasure_reconstruction Φ u x y
  unfold WOTSpectralMeasure.complexWeakIntegral at h2
  exact h.trans h2

/-- **The spectral measure of `Φ` reconstructs `Φ`**: the bounded integral of a continuous
function `f` against `starHomSpectralMeasure Φ` is `Φ f`. -/
lemma starHomSpectralMeasure_boundedIntegral (f : C(X, ℂ)) :
    ContinuousLinearMapWOT.toCLM
      (WOTSpectralMeasure.boundedIntegral (starHomSpectralMeasure Φ) f f.continuous.measurable
        (boundedIntegral_bound_of_continuous f)) = Φ f := by
  set P := starHomSpectralMeasure Φ
  let u : X → ℂ := fun z => (reCompact f z : ℂ)
  let v : X → ℂ := fun z => (imCompact f z : ℂ)
  let w : X → ℂ := fun z => Complex.I * v z
  have hu : Measurable u := by fun_prop
  have hv : Measurable v := by fun_prop
  have hw : Measurable w := measurable_const.mul hv
  have hbu : ∃ C, ∀ z, ‖u z‖ ≤ C :=
    ⟨‖(reCompact f).toContinuousMap‖, fun z => by
      simpa [u] using (reCompact f).toContinuousMap.norm_coe_le_norm z⟩
  have hbv : ∃ C, ∀ z, ‖v z‖ ≤ C :=
    ⟨‖(imCompact f).toContinuousMap‖, fun z => by
      simpa [v] using (imCompact f).toContinuousMap.norm_coe_le_norm z⟩
  have hbw : ∃ C, ∀ z, ‖w z‖ ≤ C := by
    obtain ⟨C, hC⟩ := hbv
    exact ⟨‖Complex.I‖ * C, fun z => by
      change ‖Complex.I * v z‖ ≤ _
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC z) (norm_nonneg _)⟩
  have hfun : ∀ z, f z = (u + w) z := fun z => by
    have := congrArg (fun g : C(X, ℂ) => g z) (realToComplex_reCompact_add_I_smul f)
    simpa [u, w, v, smul_eq_mul] using this.symm
  have hcongr := WOTSpectralMeasure.boundedIntegral_congr P f.continuous.measurable (hu.add hw)
    (boundedIntegral_bound_of_continuous f) (by
      obtain ⟨C₁, h₁⟩ := hbu
      obtain ⟨C₂, h₂⟩ := hbw
      exact ⟨C₁ + C₂, fun z => (norm_add_le _ _).trans (add_le_add (h₁ z) (h₂ z))⟩) hfun
  have hsum := WOTSpectralMeasure.boundedIntegral_add P hu hw hbu hbw
  have hsmul := WOTSpectralMeasure.boundedIntegral_smul P Complex.I hv hbv
  have hre := starHomSpectralMeasure_boundedIntegral_real Φ (reCompact f)
  have him := starHomSpectralMeasure_boundedIntegral_real Φ (imCompact f)
  have hΦ : Φ f = starHomRealOperator Φ (reCompact f) +
      Complex.I • starHomRealOperator Φ (imCompact f) := by
    conv_lhs => rw [← realToComplex_reCompact_add_I_smul f]
    simp [starHomRealOperator]
  rw [hcongr, hsum, hΦ, ← hre, ← him]
  have hw' : P.boundedIntegral w hw hbw = Complex.I • P.boundedIntegral v hv hbv := hsmul
  rw [hw']
  rfl

/-- **Change of spectral variable**: integrating a bounded measurable function `g` against the
pushforward of the spectral measure of `Φ` along a measurable map `f` is integrating `g ∘ f`
against the spectral measure itself. -/
lemma starHomSpectralMeasure_boundedIntegral_map {β : Type*} [MeasurableSpace β] [Nonempty β]
    {f : X → β} (hf : Measurable f) {g : β → ℂ} (hg : Measurable g)
    (hbg : ∃ C, ∀ b, ‖g b‖ ≤ C) :
    WOTSpectralMeasure.boundedIntegral ((starHomSpectralMeasure Φ).map f hf) g hg hbg =
      WOTSpectralMeasure.boundedIntegral (starHomSpectralMeasure Φ) (g ∘ f) (hg.comp hf)
        (by obtain ⟨C, hC⟩ := hbg; exact ⟨C, fun z => hC (f z)⟩) := by
  set P := starHomSpectralMeasure Φ
  apply ContinuousLinearMapWOT.toCLM_injective
  ext x
  apply ext_inner_left ℂ
  intro y
  have hfin : IsFiniteMeasure (P.scalarMeasure x y).variation := by
    rw [starHomSpectralMeasure_scalarMeasure]
    exact polarizedStarHomScalarMeasure_isFiniteMeasure Φ x y
  have hfin' : IsFiniteMeasure ((P.map f hf).scalarMeasure x y).variation := by
    rw [WOTSpectralMeasure.scalarMeasure_map]
    exact isFiniteMeasure_of_le _ VectorMeasure.variation_map_le
  obtain ⟨C, hC⟩ := hbg
  have hgi : (P.scalarMeasure x y).Integrable (g ∘ f) := by
    refine Integrable.of_bound ((hg.comp hf).aestronglyMeasurable) C ?_
    exact Filter.Eventually.of_forall fun z => hC (f z)
  have h1 := WOTSpectralMeasure.boundedIntegral_inner (P.map f hf) hg ⟨C, hC⟩ x y hfin'
  have h2 := WOTSpectralMeasure.boundedIntegral_inner P (hg.comp hf)
    ⟨C, fun z => hC (f z)⟩ x y hfin
  have h3 := WOTSpectralMeasure.complexWeakIntegral_map P f hf g x y hg.aestronglyMeasurable hgi
  unfold WOTSpectralMeasure.complexWeakIntegral at h3
  exact h1.trans (h3.trans h2.symm)

end WithNonempty

end StarHomFunctional

end QuantumMechanics

end ProbabilisticTheory

end
