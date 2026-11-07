/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.GreenOperators
public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.TemperedSlice
public import PhyslibAlpha.Mathematics.Distribution.CompactSupport

/-!

# Distributional sources

Compactly supported distributions have retarded and advanced responses.

## i. Overview

Compactly supported distributions have retarded and advanced responses. The point source is a
corollary.

## ii. Key results

- `retardedPointSource` : The retarded native point-source distribution obtained by transposing
  advanced evaluation.
- `advancedPointSource` : The advanced native point-source distribution obtained by transposing
  retarded evaluation.
- `realRetardedCutoff` : The continuous cut off real retarded response on native smooth tests.
- `realAdvancedCutoff` : The continuous cut off real advanced response on native smooth tests.
- `retardedLocalizedResponse` : Transposing the cut off advanced test map gives a retarded response
  on all distributions.
- `advancedLocalizedResponse` : Transposing the cut off retarded test map gives an advanced response
  on all distributions.
- `retardedCompactResponse` : The retarded response of a compactly supported distribution.
- `advancedCompactResponse` : The advanced response of a compactly supported distribution.

## iii. Table of contents

- A. Causal Klein–Gordon responses to a Dirac source
- B. The retarded point source through the spatial Fourier multiplier
- C. Distributional Klein–Gordon Green operators in every dimension

## iv. References

None.

## A. Causal Klein–Gordon responses to a Dirac source

- `retardedPointSource` : The retarded native point-source distribution obtained by transposing
  advanced evaluation.
- `advancedPointSource` : The advanced native point-source distribution obtained by transposing
  retarded evaluation.

Lemmas: `nativeTestDerivative_coe`, `nativeTestOperator_equiv`,
`distributionOperator_retardedPointSource`, `distributionOperator_advancedPointSource`,
`retardedPointSource_vanishes`, `advancedPointSource_vanishes`,
`dsupport_retardedPointSource_subset`, `dsupport_advancedPointSource_subset`.

## B. The retarded point source through the spatial Fourier multiplier

Lemmas: `retardedPointSource_apply`.

## C. Distributional Klein–Gordon Green operators in every dimension

- `realRetardedCutoff` : The continuous cut off real retarded response on native smooth tests.
- `realAdvancedCutoff` : The continuous cut off real advanced response on native smooth tests.
- `retardedLocalizedResponse` : Transposing the cut off advanced test map gives a retarded response
  on all distributions.
- `advancedLocalizedResponse` : Transposing the cut off retarded test map gives an advanced response
  on all distributions.
- `retardedCompactResponse` : The retarded response of a compactly supported distribution.
- `advancedCompactResponse` : The advanced response of a compactly supported distribution.
- `compactDistributionOperator` : The field operator restricts to an endomorphism of compactly
  supported distributions.

Lemmas: `realRetardedCutoff_apply`, `realAdvancedCutoff_apply`, `retardedLocalizedResponse_solves`,
`advancedLocalizedResponse_solves`, `retardedLocalizedResponse_vanishes`,
`advancedLocalizedResponse_vanishes`, `retardedDistribution_eq_zero`,
`advancedDistribution_eq_zero`, `retardedDistribution_unique`, `advancedDistribution_unique` and
more.

-/

@[expose] public section

noncomputable section

open scoped Distributions
open CausalRelation Distribution LocalOperator Minkowski TestFunction TimeSlice WaveEquation
    TopologicalSpace Topology GreenOperator
open Minkowski (DistributionField)

namespace KleinGordon.Spacetime

section
variable {d : ℕ}

lemma nativeTestDerivative_coe (μ : Fin 1 ⊕ Fin d)
    (φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (Lorentz.Vector.basis μ) φ : SpaceTime d → ℝ) =
      SpaceTime.deriv μ φ := by
  funext p
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
  exact (φ.contDiff.differentiable (by simp) p).lineDeriv_eq_fderiv

lemma nativeTestOperator_equiv (m : ℝ) (f : TestField d ℝ) :
    testOperator m (testFieldEquiv ℝ f) =
      testFieldEquiv ℝ ((equation m).compactOperator f) := by
  ext p
  change (testOperator m (testFieldEquiv ℝ f)) p =
    (KleinGordon.Spacetime.operator m f.val : SpaceTime d → ℝ) p
  change (testOperator m (testFieldEquiv ℝ f)) p =
    (smoothWaveOperator f.val : SpaceTime d → ℝ) p + m ^ 2 * f.val.val p
  rw [smoothWaveOperator_coe]
  simp only [testOperator, testWaveOperator, add_apply, sum_apply,
    smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [nativeTestDerivative_coe]
  rfl

/-- The retarded native point-source distribution obtained by transposing advanced evaluation. -/
def retardedPointSource (m : ℝ) (p : SpaceTime d) : Distribution (⊤ : Opens (SpaceTime d)) ℝ ⊤ where
  toFun := realAdvancedEvaluation m p
  map_add' := map_add (realAdvancedEvaluation m p)
  map_smul' := map_smul (realAdvancedEvaluation m p)
  cont := (realAdvancedEvaluation m p).continuous

/-- The advanced native point-source distribution obtained by transposing retarded evaluation. -/
def advancedPointSource (m : ℝ) (p : SpaceTime d) : Distribution (⊤ : Opens (SpaceTime d)) ℝ ⊤ where
  toFun := realRetardedEvaluation m p
  map_add' := map_add (realRetardedEvaluation m p)
  map_smul' := map_smul (realRetardedEvaluation m p)
  cont := (realRetardedEvaluation m p).continuous

/-- The retarded point-source distribution solves the weak equation with source `δₚ`. -/
lemma distributionOperator_retardedPointSource (m : ℝ) (p : SpaceTime d) :
    distributionOperator m (retardedPointSource m p) = Distribution.delta p := by
  ext φ
  rw [distributionOperator_apply]
  let f := (testFieldEquiv ℝ).symm φ
  have he : φ = testFieldEquiv ℝ f := ((testFieldEquiv ℝ).apply_symm_apply φ).symm
  change realAdvancedEvaluation m p (testOperator m φ) = φ p
  rw [he, nativeTestOperator_equiv, realAdvancedEvaluation_apply,
    (realAdvancedGreenOperator m).comp_operator]
  rfl

/-- The advanced point-source distribution solves the weak equation with source `δₚ`. -/
lemma distributionOperator_advancedPointSource (m : ℝ) (p : SpaceTime d) :
    distributionOperator m (advancedPointSource m p) = Distribution.delta p := by
  ext φ
  rw [distributionOperator_apply]
  let f := (testFieldEquiv ℝ).symm φ
  have he : φ = testFieldEquiv ℝ f := ((testFieldEquiv ℝ).apply_symm_apply φ).symm
  change realRetardedEvaluation m p (testOperator m φ) = φ p
  rw [he, nativeTestOperator_equiv, realRetardedEvaluation_apply,
    (realRetardedGreenOperator m).comp_operator]
  rfl

/-- The retarded point-source response annihilates all tests outside the source event's future. -/
lemma retardedPointSource_vanishes (m : ℝ) (p : SpaceTime d) :
    Distribution.IsVanishingOn (retardedPointSource m p)
      ((causalRelation d).causalFuture {p})ᶜ := by
  intro φ hφ
  let f := (testFieldEquiv ℝ).symm φ
  have he : φ = testFieldEquiv ℝ f := ((testFieldEquiv ℝ).apply_symm_apply φ).symm
  change realAdvancedEvaluation m p φ = 0
  rw [he, realAdvancedEvaluation_apply]
  apply image_eq_zero_of_notMem_tsupport
  intro hp
  obtain ⟨q, hq, hpq⟩ := (realAdvancedGreenOperator m).support f hp
  have hqφ : q ∈ tsupport φ := by rw [he]; exact hq
  exact (hφ hqφ) ⟨p, rfl, hpq⟩

/-- The advanced point-source response annihilates all tests outside the source event's past. -/
lemma advancedPointSource_vanishes (m : ℝ) (p : SpaceTime d) :
    Distribution.IsVanishingOn (advancedPointSource m p)
      ((causalRelation d).causalPast {p})ᶜ := by
  intro φ hφ
  let f := (testFieldEquiv ℝ).symm φ
  have he : φ = testFieldEquiv ℝ f := ((testFieldEquiv ℝ).apply_symm_apply φ).symm
  change realRetardedEvaluation m p φ = 0
  rw [he, realRetardedEvaluation_apply]
  apply image_eq_zero_of_notMem_tsupport
  intro hp
  obtain ⟨q, hq, hqp⟩ := (realRetardedGreenOperator m).support f hp
  have hqφ : q ∈ tsupport φ := by rw [he]; exact hq
  exact (hφ hqφ) ⟨p, rfl, hqp⟩

/-- Native distributional support of the retarded fundamental solution is causal. -/
lemma dsupport_retardedPointSource_subset (m : ℝ) (p : SpaceTime d) :
    Distribution.dsupport (retardedPointSource m p) ⊆ (causalRelation d).causalFuture {p} :=
  Set.sInter_subset_of_mem ⟨retardedPointSource_vanishes m p,
    isClosed_causalFuture isCompact_singleton⟩

/-- Native distributional support of the advanced fundamental solution is causal. -/
lemma dsupport_advancedPointSource_subset (m : ℝ) (p : SpaceTime d) :
    Distribution.dsupport (advancedPointSource m p) ⊆ (causalRelation d).causalPast {p} :=
  Set.sInter_subset_of_mem ⟨advancedPointSource_vanishes m p,
    isClosed_causalPast isCompact_singleton⟩

/-- **The retarded fundamental solution as propagated Dirac distributions.** Tested against a
real test function `φ` the retarded point source at the event `p` is the real part of the time
integral of the Fourier multiplier `sincPropagator (s - t₀)` applied to the Dirac distribution at
the position `y₀` of `p`, paired with the spatial slice of `φ` at the time `s`. -/
lemma retardedPointSource_apply (m : ℝ) (p : SpaceTime d)
    (φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    retardedPointSource m p φ =
      (∫ s in Set.Ioi (coordinates d p).1,
        sineEvolutionTempered ℂ (s - (coordinates d p).1) (m ^ 2)
          (TemperedDistribution.delta (coordinates d p).2)
          (slice ℂ (sourceEquiv ℂ (TestFunction.postcompCLM Complex.ofRealCLM φ)) s)).re := by
  change (advancedResponse ℂ (m ^ 2) (TestFunction.postcompCLM Complex.ofRealCLM φ) p).re = _
  rw [advancedResponse, advancedSolution_eq_dirac (sq_nonneg m)]

/-- The continuous cut off real retarded response on native smooth tests. -/
def realRetardedCutoff (m : ℝ) (χ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    𝓓((⊤ : Opens (SpaceTime d)), ℝ) →L[ℝ] 𝓓((⊤ : Opens (SpaceTime d)), ℝ) :=
  (TestFunction.postcompCLM Complex.reCLM).comp
    ((precompLinearEquivCLM (coordinates d)).comp
      ((cutoffSolution ℂ (sq_nonneg m)
          (precompLinearEquivCLM (coordinates d).symm χ)).comp
        ((precompLinearEquivCLM (coordinates d).symm).comp
          (TestFunction.postcompCLM Complex.ofRealCLM))))

/-- The continuous cut off real advanced response on native smooth tests. -/
def realAdvancedCutoff (m : ℝ) (χ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    𝓓((⊤ : Opens (SpaceTime d)), ℝ) →L[ℝ] 𝓓((⊤ : Opens (SpaceTime d)), ℝ) :=
  (TestFunction.postcompCLM Complex.reCLM).comp
    ((precompLinearEquivCLM (coordinates d)).comp
      ((cutoffAdvancedSolution ℂ (sq_nonneg m)
          (precompLinearEquivCLM (coordinates d).symm χ)).comp
        ((precompLinearEquivCLM (coordinates d).symm).comp
          (TestFunction.postcompCLM Complex.ofRealCLM))))

lemma realRetardedCutoff_apply (m : ℝ) (χ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ))
    (f : TestField d ℝ) (p : SpaceTime d) :
    realRetardedCutoff m χ (testFieldEquiv ℝ f) p =
      χ p * ((realRetardedGreenOperator m).toLinearMap f).val p := by
  have h : realRetardedCutoff m χ (testFieldEquiv ℝ f) p =
      (χ ((coordinates d).symm (coordinates d p)) • retardedResponse ℂ (m ^ 2)
        (TestFunction.postcompCLM Complex.ofRealCLM (testFieldEquiv ℝ f)) p).re := rfl
  rw [h, ContinuousLinearEquiv.symm_apply_apply, Complex.smul_re, smul_eq_mul]
  rfl

lemma realAdvancedCutoff_apply (m : ℝ) (χ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ))
    (f : TestField d ℝ) (p : SpaceTime d) :
    realAdvancedCutoff m χ (testFieldEquiv ℝ f) p =
      χ p * ((realAdvancedGreenOperator m).toLinearMap f).val p := by
  have h : realAdvancedCutoff m χ (testFieldEquiv ℝ f) p =
      (χ ((coordinates d).symm (coordinates d p)) • advancedResponse ℂ (m ^ 2)
        (TestFunction.postcompCLM Complex.ofRealCLM (testFieldEquiv ℝ f)) p).re := by
    change (cutoffAdvancedSolution ℂ (sq_nonneg m)
      (precompLinearEquivCLM (coordinates d).symm χ)
      (precompLinearEquivCLM (coordinates d).symm
        (TestFunction.postcompCLM Complex.ofRealCLM (testFieldEquiv ℝ f))) (coordinates d p)).re = _
    rw [cutoffAdvancedSolution_apply]
    rfl
  rw [h, ContinuousLinearEquiv.symm_apply_apply, Complex.smul_re, smul_eq_mul]
  rfl
end

section
variable {d : ℕ}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Transposing the cut off advanced test map gives a retarded response on all distributions. -/
def retardedLocalizedResponse (m : ℝ) (χ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    DistributionField d V →L[ℝ] DistributionField d V :=
  (realAdvancedCutoff m χ).precompCompactConvergenceCLM V

/-- Transposing the cut off retarded test map gives an advanced response on all distributions. -/
def advancedLocalizedResponse (m : ℝ) (χ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    DistributionField d V →L[ℝ] DistributionField d V :=
  (realRetardedCutoff m χ).precompCompactConvergenceCLM V

lemma retardedLocalizedResponse_solves (m : ℝ) (χ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ))
    (T : DistributionField d V) :
    distributionOperator m (retardedLocalizedResponse m χ T) =
      multiplyDistribution χ χ.contDiff T := by
  ext φ
  rw [distributionOperator_apply]
  change T (realAdvancedCutoff m χ (testOperator m φ)) =
    T (smoothWeightTest χ χ.contDiff φ)
  apply congrArg T
  let f := (testFieldEquiv ℝ).symm φ
  have he : φ = testFieldEquiv ℝ f := ((testFieldEquiv ℝ).apply_symm_apply φ).symm
  rw [he, nativeTestOperator_equiv]
  ext p
  rw [realAdvancedCutoff_apply]
  change χ p * _ = χ p * _
  rw [(realAdvancedGreenOperator m).comp_operator]
  rfl

lemma advancedLocalizedResponse_solves (m : ℝ) (χ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ))
    (T : DistributionField d V) :
    distributionOperator m (advancedLocalizedResponse m χ T) =
      multiplyDistribution χ χ.contDiff T := by
  ext φ
  rw [distributionOperator_apply]
  change T (realRetardedCutoff m χ (testOperator m φ)) =
    T (smoothWeightTest χ χ.contDiff φ)
  apply congrArg T
  let f := (testFieldEquiv ℝ).symm φ
  have he : φ = testFieldEquiv ℝ f := ((testFieldEquiv ℝ).apply_symm_apply φ).symm
  rw [he, nativeTestOperator_equiv]
  ext p
  rw [realRetardedCutoff_apply]
  change χ p * _ = χ p * _
  rw [(realRetardedGreenOperator m).comp_operator]
  rfl

/-- Retarded propagation respects every distributional source support bound. -/
lemma retardedLocalizedResponse_vanishes (m : ℝ) (χ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ))
    (T : DistributionField d V) (K : Set (SpaceTime d))
    (hT : Distribution.IsVanishingOn T Kᶜ) :
    Distribution.IsVanishingOn (retardedLocalizedResponse m χ T)
      ((causalRelation d).causalFuture K)ᶜ := by
  intro φ hφ
  change T (realAdvancedCutoff m χ φ) = 0
  apply hT
  let f := (testFieldEquiv ℝ).symm φ
  have he : φ = testFieldEquiv ℝ f := ((testFieldEquiv ℝ).apply_symm_apply φ).symm
  rw [he]
  intro q hq hqK
  have hn : q ∉ tsupport (((realAdvancedGreenOperator m).toLinearMap f).val) := by
    intro hu
    obtain ⟨r, hr, hqr⟩ := (realAdvancedGreenOperator m).support f hu
    exact hφ (by rw [he]; exact hr) ⟨q, hqK, hqr⟩
  have hc : q ∉ tsupport (realAdvancedCutoff m χ (testFieldEquiv ℝ f) : SpaceTime d → ℝ) := by
    apply notMem_tsupport_iff_eventuallyEq.mpr
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
    change ((realAdvancedGreenOperator m).toLinearMap f).val y = 0 at hy
    change realAdvancedCutoff m χ (testFieldEquiv ℝ f) y = 0
    rw [realAdvancedCutoff_apply, hy, mul_zero]
  exact hc hq

/-- Advanced propagation respects every distributional source support bound. -/
lemma advancedLocalizedResponse_vanishes (m : ℝ) (χ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ))
    (T : DistributionField d V) (K : Set (SpaceTime d))
    (hT : Distribution.IsVanishingOn T Kᶜ) :
    Distribution.IsVanishingOn (advancedLocalizedResponse m χ T)
      ((causalRelation d).causalPast K)ᶜ := by
  intro φ hφ
  change T (realRetardedCutoff m χ φ) = 0
  apply hT
  let f := (testFieldEquiv ℝ).symm φ
  have he : φ = testFieldEquiv ℝ f := ((testFieldEquiv ℝ).apply_symm_apply φ).symm
  rw [he]
  intro q hq hqK
  have hn : q ∉ tsupport (((realRetardedGreenOperator m).toLinearMap f).val) := by
    intro hu
    obtain ⟨r, hr, hrq⟩ := (realRetardedGreenOperator m).support f hu
    exact hφ (by rw [he]; exact hr) ⟨q, hqK, hrq⟩
  have hc : q ∉ tsupport (realRetardedCutoff m χ (testFieldEquiv ℝ f) : SpaceTime d → ℝ) := by
    apply notMem_tsupport_iff_eventuallyEq.mpr
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
    change ((realRetardedGreenOperator m).toLinearMap f).val y = 0 at hy
    change realRetardedCutoff m χ (testFieldEquiv ℝ f) y = 0
    rw [realRetardedCutoff_apply, hy, mul_zero]
  exact hc hq

/-- A weak homogeneous field with future support in a compact causal future vanishes. -/
lemma retardedDistribution_eq_zero (m : ℝ) (K : Set (SpaceTime d)) (hK : IsCompact K)
    (T : DistributionField d V)
    (hT : Distribution.IsVanishingOn T ((causalRelation d).causalFuture K)ᶜ)
    (hzero : distributionOperator m T = 0) : T = 0 := by
  apply distribution_eq_zero_of_retarded (testFieldEquiv ℝ) (fun _ => rfl)
    (realAdvancedGreenOperator m)
    (Minkowski.smoothFutureLocalization (equation m))
    (hasCompactCausalDiamonds d) K hK T hT
  intro f
  have h := congrArg (fun D : DistributionField d V => D (testFieldEquiv ℝ f)) hzero
  change distributionOperator m T (testFieldEquiv ℝ f) = 0 at h
  rw [distributionOperator_apply, nativeTestOperator_equiv] at h
  exact h

/-- A weak homogeneous field with past support in a compact causal past vanishes. -/
lemma advancedDistribution_eq_zero (m : ℝ) (K : Set (SpaceTime d)) (hK : IsCompact K)
    (T : DistributionField d V)
    (hT : Distribution.IsVanishingOn T ((causalRelation d).causalPast K)ᶜ)
    (hzero : distributionOperator m T = 0) : T = 0 := by
  apply distribution_eq_zero_of_retarded (C := (causalRelation d).reverse)
    (testFieldEquiv ℝ) (fun _ => rfl) (realGreenOperators m).reverse.advanced
    (Minkowski.smoothPastLocalization (equation m))
    (HasCompactCausalDiamonds.reverse _
      (hasCompactCausalDiamonds d)) K hK T hT
  intro f
  have h := congrArg (fun D : DistributionField d V => D (testFieldEquiv ℝ f)) hzero
  change distributionOperator m T (testFieldEquiv ℝ f) = 0 at h
  rw [distributionOperator_apply, nativeTestOperator_equiv] at h
  exact h

/-- The same source and retarded support determine a unique distributional solution. -/
lemma retardedDistribution_unique (m : ℝ) (K : Set (SpaceTime d)) (hK : IsCompact K)
    (u v : DistributionField d V)
    (hu : Distribution.IsVanishingOn u ((causalRelation d).causalFuture K)ᶜ)
    (hv : Distribution.IsVanishingOn v ((causalRelation d).causalFuture K)ᶜ)
    (hsource : distributionOperator m u =
      distributionOperator m v) : u = v := by
  apply sub_eq_zero.mp
  apply retardedDistribution_eq_zero m K hK (u - v)
  · intro φ hφ
    change u φ - v φ = 0
    rw [hu φ hφ, hv φ hφ, sub_self]
  · exact (map_sub _ u v).trans (sub_eq_zero.mpr hsource)

/-- The same source and advanced support determine a unique distributional solution. -/
lemma advancedDistribution_unique (m : ℝ) (K : Set (SpaceTime d)) (hK : IsCompact K)
    (u v : DistributionField d V)
    (hu : Distribution.IsVanishingOn u ((causalRelation d).causalPast K)ᶜ)
    (hv : Distribution.IsVanishingOn v ((causalRelation d).causalPast K)ᶜ)
    (hsource : distributionOperator m u =
      distributionOperator m v) : u = v := by
  apply sub_eq_zero.mp
  apply advancedDistribution_eq_zero m K hK (u - v)
  · intro φ hφ
    change u φ - v φ = 0
    rw [hu φ hφ, hv φ hφ, sub_self]
  · exact (map_sub _ u v).trans (sub_eq_zero.mpr hsource)

/-- The retarded response of a compactly supported distribution. -/
def retardedCompactResponse (m : ℝ) (T : compactDistributions (SpaceTime d) V) :
    DistributionField d V :=
  retardedLocalizedResponse m (compactCutoff (compactDistributionBound T)) T.val

/-- The advanced response of a compactly supported distribution. -/
def advancedCompactResponse (m : ℝ) (T : compactDistributions (SpaceTime d) V) :
    DistributionField d V :=
  advancedLocalizedResponse m (compactCutoff (compactDistributionBound T)) T.val

/-- The retarded response solves the equation for the source itself. -/
lemma retardedCompactResponse_solves (m : ℝ) (T : compactDistributions (SpaceTime d) V) :
    distributionOperator m (retardedCompactResponse m T) = T.val := by
  rw [retardedCompactResponse, retardedLocalizedResponse_solves]
  exact multiplyDistribution_eq_self _ _ _ _ (compactDistributionBound_vanishes T)
    (fun p hp => compactCutoff_one_near _ hp)

/-- The advanced response solves the equation for the source itself. -/
lemma advancedCompactResponse_solves (m : ℝ) (T : compactDistributions (SpaceTime d) V) :
    distributionOperator m (advancedCompactResponse m T) = T.val := by
  rw [advancedCompactResponse, advancedLocalizedResponse_solves]
  exact multiplyDistribution_eq_self _ _ _ _ (compactDistributionBound_vanishes T)
    (fun p hp => compactCutoff_one_near _ hp)

/-- The retarded response is supported in the causal future of the source's compact bound. -/
lemma retardedCompactResponse_vanishes (m : ℝ) (T : compactDistributions (SpaceTime d) V) :
    Distribution.IsVanishingOn (retardedCompactResponse m T)
      ((causalRelation d).causalFuture (compactDistributionBound T))ᶜ :=
  retardedLocalizedResponse_vanishes m _ T.val _ (compactDistributionBound_vanishes T)

/-- The advanced response is supported in the causal past of the source's compact bound. -/
lemma advancedCompactResponse_vanishes (m : ℝ) (T : compactDistributions (SpaceTime d) V) :
    Distribution.IsVanishingOn (advancedCompactResponse m T)
      ((causalRelation d).causalPast (compactDistributionBound T))ᶜ :=
  advancedLocalizedResponse_vanishes m _ T.val _ (compactDistributionBound_vanishes T)

/-- Any distributional solution with future support is the retarded response. -/
lemma retardedCompactResponse_unique (m : ℝ) (T : compactDistributions (SpaceTime d) V)
    (u : DistributionField d V) (K : Set (SpaceTime d)) (hK : IsCompact K)
    (hu : Distribution.IsVanishingOn u ((causalRelation d).causalFuture K)ᶜ)
    (hsource : distributionOperator m u = T.val) :
    u = retardedCompactResponse m T := by
  apply retardedDistribution_unique m (K ∪ compactDistributionBound T)
    (hK.union (compactDistributionBound T).isCompact)
  · exact hu.mono (Set.compl_subset_compl.mpr
      ((causalRelation d).causalFuture_mono Set.subset_union_left))
  · exact (retardedCompactResponse_vanishes m T).mono (Set.compl_subset_compl.mpr
      ((causalRelation d).causalFuture_mono Set.subset_union_right))
  · rw [hsource, retardedCompactResponse_solves]

/-- Any distributional solution with past support is the advanced response. -/
lemma advancedCompactResponse_unique (m : ℝ) (T : compactDistributions (SpaceTime d) V)
    (u : DistributionField d V) (K : Set (SpaceTime d)) (hK : IsCompact K)
    (hu : Distribution.IsVanishingOn u ((causalRelation d).causalPast K)ᶜ)
    (hsource : distributionOperator m u = T.val) :
    u = advancedCompactResponse m T := by
  apply advancedDistribution_unique m (K ∪ compactDistributionBound T)
    (hK.union (compactDistributionBound T).isCompact)
  · exact hu.mono (Set.compl_subset_compl.mpr
      ((causalRelation d).causalPast_mono Set.subset_union_left))
  · exact (advancedCompactResponse_vanishes m T).mono (Set.compl_subset_compl.mpr
      ((causalRelation d).causalPast_mono Set.subset_union_right))
  · rw [hsource, advancedCompactResponse_solves]

/-- The massive weak operator preserves every source annihilation bound. -/
lemma distributionOperator_vanishes (m : ℝ) (T : DistributionField d V) (K : Set (SpaceTime d))
    (hT : Distribution.IsVanishingOn T Kᶜ) :
    Distribution.IsVanishingOn (distributionOperator m T) Kᶜ := by
  intro φ hφ
  rw [distributionOperator_apply]
  apply hT
  let f := (testFieldEquiv ℝ).symm φ
  have he : φ = testFieldEquiv ℝ f := ((testFieldEquiv ℝ).apply_symm_apply φ).symm
  have hφ' : tsupport (f.val.val : SpaceTime d → ℝ) ⊆ Kᶜ := by
    rw [he] at hφ
    exact hφ
  rw [he, nativeTestOperator_equiv]
  change tsupport (((equation m).compactOperator f).val.val) ⊆ Kᶜ
  exact ((equation m).support_operator f.val).trans hφ'

/-- The field operator restricts to an endomorphism of compactly supported distributions. -/
def compactDistributionOperator (m : ℝ) :
    compactDistributions (SpaceTime d) V →ₗ[ℝ] compactDistributions (SpaceTime d) V where
  toFun T := ⟨distributionOperator m T.val,
    ⟨compactDistributionBound T, (compactDistributionBound T).isCompact,
    distributionOperator_vanishes m T.val _ (compactDistributionBound_vanishes T)⟩⟩
  map_add' T S := Subtype.ext (map_add (distributionOperator m) T.val S.val)
  map_smul' a T := Subtype.ext (map_smul (distributionOperator m) a T.val)

/-- The retarded response inverts the field operator on compactly supported distributions. -/
lemma retardedCompactResponse_operator (m : ℝ) (T : compactDistributions (SpaceTime d) V) :
    retardedCompactResponse m (compactDistributionOperator m T) = T.val := by
  symm
  apply retardedCompactResponse_unique m _ T.val (compactDistributionBound T)
    (compactDistributionBound T).isCompact
  · exact (compactDistributionBound_vanishes T).mono (Set.compl_subset_compl.mpr
      (causalRelation d).subset_causalFuture)
  · rfl

/-- The advanced response inverts the field operator on compactly supported distributions. -/
lemma advancedCompactResponse_operator (m : ℝ) (T : compactDistributions (SpaceTime d) V) :
    advancedCompactResponse m (compactDistributionOperator m T) = T.val := by
  symm
  apply advancedCompactResponse_unique m _ T.val (compactDistributionBound T)
    (compactDistributionBound T).isCompact
  · exact (compactDistributionBound_vanishes T).mono (Set.compl_subset_compl.mpr
      (causalRelation d).subset_causalPast)
  · rfl
end

end KleinGordon.Spacetime
