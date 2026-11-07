/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Distribution.TimeSliceSmooth
public import PhyslibAlpha.Mathematics.Fourier.Inversion
public import PhyslibAlpha.Mathematics.Fourier.SchwartzDecay

/-!

# The space and time Fourier transform of a test function

A test function on time and space is transformed in the space variable and then in the time
variable.

## i. Overview

The spatial transform of the slices of a test function is a smooth function of the time with
compact support. It is therefore a Schwartz function of the time. Its transform in the time is the
spacetime transform in the split variables. Fourier inversion in the time recovers the spatial
transform. The Schwartz seminorms and the integral over the frequency decay faster than every
power of the wave vector.

## ii. Key results

- `TimeSlice.spaceFourier` : the spatial transform of the slices.
- `TimeSlice.timeFourier` : the transform in the time of the spatial transform.
- `TimeSlice.spaceFourier_eq_integral` : Fourier inversion in the time.
- `TimeSlice.exists_integral_norm_timeFourier_le` : decay of the integral over the frequency.

## iii. Table of contents

- A. The transforms
- B. Properties of the time transform
- C. Decay in the wave vector

## iv. References

None.

## A. The transforms

- `TimeSlice.spaceFourier` : the spatial transform of the slices.
- `TimeSlice.spaceFourierSchwartz` : the spatial transform as a Schwartz function of the time.
- `TimeSlice.timeFourier` : the transform in the time of the spatial transform.
- `TimeSlice.spaceFourier_eq_integral` : Fourier inversion in the time.
- `TimeSlice.timeFourier_eq_integral` : the time transform as an integral.

## B. Properties of the time transform

- `TimeSlice.continuous_timeFourier` : joint continuity.
- `TimeSlice.timeFourier_reflect` : reflecting the source reflects the frequency.
- `TimeSlice.integrable_timeFourier` : integrability in the frequency.

## C. Decay in the wave vector

- `TimeSlice.exists_seminorm_spaceFourier_le` : decay of the Schwartz seminorms.
- `TimeSlice.exists_integral_norm_timeFourier_le` : decay of the integral over the frequency.
-/

@[expose] public section

noncomputable section

open scoped SchwartzMap FourierTransform ContDiff Distributions
open MeasureTheory TestFunction TopologicalSpace

namespace TimeSlice

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]

/-- The spatial transform of the slices of `ψ` at the frequency `ξ` as a function of the time. -/
def spaceFourier (ψ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) (ξ : E) (s : ℝ) : ℂ := 𝓕 (slice ℂ ψ s) ξ

lemma hasCompactSupport_spaceFourier (ψ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) (ξ : E) :
    HasCompactSupport (spaceFourier ψ ξ) :=
  HasCompactSupport.intro (isCompact_timeSupport ℂ ψ) fun s hs => by
    simp [spaceFourier, slice_eq_zero_of_notMem ℂ ψ hs]

lemma contDiff_spaceFourier (ψ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) (ξ : E) :
    ContDiff ℝ ∞ (spaceFourier ψ ξ) :=
  contDiff_infty.2 fun n => contDiff_fourier_slice ℂ ξ n ψ

/-- The spatial transform of a test function is a Schwartz function of the time. -/
def spaceFourierSchwartz (ψ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) (ξ : E) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_spaceFourier ψ ξ).toSchwartzMap (contDiff_spaceFourier ψ ξ)

/-- The transform in the time of the spatial transform. -/
def timeFourier (ψ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) (w : ℝ) (ξ : E) : ℂ :=
  𝓕 (spaceFourierSchwartz ψ ξ) w

/-- **Fourier inversion in the time.** The spatial transform of a slice is the inverse transform
in the time of `timeFourier`. -/
lemma spaceFourier_eq_integral (ψ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) (ξ : E) (s : ℝ) :
    spaceFourier ψ ξ s = ∫ w : ℝ, (𝐞 (s * w) : ℂ) • timeFourier ψ w ξ := by
  simp only [timeFourier]
  exact (SchwartzMap.integral_char_smul_fourier (spaceFourierSchwartz ψ ξ) s).symm

/-- The transform in the time as an integral. -/
lemma timeFourier_eq_integral (χ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) (v : ℝ) (ξ : E) :
    timeFourier χ v ξ = ∫ s : ℝ, (𝐞 (-(s * v)) : ℂ) • spaceFourier χ ξ s := by
  simp only [timeFourier, SchwartzMap.fourier_coe, Real.fourier_eq, Circle.smul_def,
    RCLike.inner_apply, conj_trivial, mul_comm]
  rfl

/-- The transformed test function is jointly continuous in the frequency and the wave vector. -/
lemma continuous_timeFourier (χ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) :
    Continuous fun p : ℝ × E => timeFourier χ p.1 p.2 := by
  have hT : IsCompact (Prod.fst '' tsupport χ) := isCompact_timeSupport ℂ χ
  have hcont : Continuous (Function.uncurry fun (p : ℝ × E) (s : ℝ) =>
      (𝐞 (-(s * p.1)) : ℂ) • spaceFourier χ p.2 s) := by
    have h1 : Continuous fun q : (ℝ × E) × ℝ => (𝐞 (-(q.2 * q.1.1)) : ℂ) :=
      continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        ((continuous_snd.mul (continuous_fst.comp continuous_fst)).neg))
    have h2 : Continuous fun q : (ℝ × E) × ℝ => spaceFourier χ q.1.2 q.2 :=
      (continuous_fourier_slice ℂ χ).comp (continuous_snd.prodMk (continuous_snd.comp
        continuous_fst))
    exact h1.smul h2
  have h := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun (p : ℝ × E) (s : ℝ) => (𝐞 (-(s * p.1)) : ℂ) • spaceFourier χ p.2 s) hcont hT
  refine h.congr fun p => ?_
  rw [timeFourier_eq_integral]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero (s := Prod.fst '' tsupport χ)
    (f := fun s : ℝ => (𝐞 (-(s * p.1)) : ℂ) • spaceFourier χ p.2 s) fun s hs => ?_)
  simp [spaceFourier, slice_eq_zero_of_notMem ℂ χ hs]

/-- Reflecting the source in the time reflects the frequency. -/
lemma timeFourier_reflect (ψ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) (w : ℝ) (ξ : E) :
    timeFourier (reflect ℂ ψ) w ξ = timeFourier ψ (-w) ξ := by
  have hsf : ∀ s, spaceFourier (reflect ℂ ψ) ξ s = spaceFourier ψ ξ (-s) := fun s => by
    simp [spaceFourier, slice_reflect]
  rw [timeFourier_eq_integral, timeFourier_eq_integral]
  simp_rw [hsf]
  rw [← integral_neg_eq_self (fun s : ℝ => (𝐞 (-(s * -w)) : ℂ) • spaceFourier ψ ξ s)]
  simp

lemma integrable_timeFourier (χ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) (ξ : E) :
    Integrable fun w : ℝ => timeFourier χ w ξ :=
  (𝓕 (spaceFourierSchwartz χ ξ)).integrable

/-- The Schwartz seminorms of the spatial transform of a test function decay in the frequency. -/
lemma exists_seminorm_spaceFourier_le (ψ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) (N k p : ℕ) :
    ∃ B : ℝ, ∀ ξ : E, SchwartzMap.seminorm ℂ k p (spaceFourierSchwartz ψ ξ) ≤
      B * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
  obtain ⟨K, hK⟩ := exists_iteratedDeriv_fourier_slice_bound ℂ ψ p N
  obtain ⟨R, hR⟩ := (isCompact_timeSupport ℂ ψ).isBounded.exists_norm_le
  set T : Set ℝ := Prod.fst '' tsupport ψ with hT
  have hTc : IsCompact T := isCompact_timeSupport ℂ ψ
  refine ⟨max R 0 ^ k * max K 0, fun ξ => ?_⟩
  have hpos : 0 ≤ (1 + ‖ξ‖) ^ (-(N : ℝ)) := by positivity
  refine SchwartzMap.seminorm_le_bound ℂ k p _ (by positivity) fun s => ?_
  have hd : ‖iteratedFDeriv ℝ p (spaceFourierSchwartz ψ ξ) s‖ =
      ‖iteratedDeriv p (spaceFourier ψ ξ) s‖ :=
    norm_iteratedFDeriv_eq_norm_iteratedDeriv
  by_cases hs : s ∈ T
  · have h1 : ‖s‖ ≤ max R 0 := (hR s hs).trans (le_max_left _ _)
    have h2 : ‖iteratedDeriv p (fun r => 𝓕 (slice ℂ ψ r) ξ) s‖ ≤
        K * (1 + ‖ξ‖) ^ (-(N : ℝ)) := hK ξ s
    rw [hd]
    calc ‖s‖ ^ k * ‖iteratedDeriv p (spaceFourier ψ ξ) s‖
        ≤ max R 0 ^ k * (max K 0 * (1 + ‖ξ‖) ^ (-(N : ℝ))) := by
          gcongr
          exact h2.trans (by gcongr; exact le_max_left _ _)
      _ = _ := by ring
  · have hsupp : tsupport (spaceFourier ψ ξ) ⊆ T :=
      closure_minimal (fun r hr => by
        by_contra hrT
        exact hr (by simp [spaceFourier, slice_eq_zero_of_notMem ℂ ψ hrT])) hTc.isClosed
    have h0 : iteratedFDeriv ℝ p (spaceFourierSchwartz ψ ξ) s = 0 := by
      by_contra h
      exact hs (hsupp (support_iteratedFDeriv_subset (𝕜 := ℝ) (n := p)
        (Function.mem_support.2 h)))
    rw [h0]
    simp only [norm_zero, mul_zero]
    positivity

/-- The integral over the frequency of the transformed test function decays in `ξ`. -/
lemma exists_integral_norm_timeFourier_le (ψ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : E, ∫ w : ℝ, ‖timeFourier ψ w ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
  obtain ⟨S, C₀, hC₀, hS⟩ := SchwartzMap.exists_integral_norm_fourier_le (E := ℝ) ℂ
  choose B hB using fun i : ℕ × ℕ => exists_seminorm_spaceFourier_le ψ N i.1 i.2
  set T : ℝ := ∑ i ∈ S, max (B i) 0 with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => le_max_right _ _
  refine ⟨C₀ * T, mul_nonneg hC₀ hT0, fun ξ => ?_⟩
  have hpos : 0 ≤ (1 + ‖ξ‖) ^ (-(N : ℝ)) := by positivity
  have h1 : (S.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (spaceFourierSchwartz ψ ξ) ≤
      T * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
    refine Seminorm.finset_sup_apply_le (mul_nonneg hT0 hpos) fun i hi => ?_
    calc _ ≤ B i * (1 + ‖ξ‖) ^ (-(N : ℝ)) := hB i ξ
      _ ≤ max (B i) 0 * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by gcongr; exact le_max_left _ _
      _ ≤ T * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
        gcongr
        exact Finset.single_le_sum (f := fun i => max (B i) 0) (fun j _ => le_max_right _ _) hi
  calc ∫ w : ℝ, ‖timeFourier ψ w ξ‖ ≤ C₀ * (S.sup (schwartzSeminormFamily ℂ ℝ ℂ))
        (spaceFourierSchwartz ψ ξ) := hS _
    _ ≤ C₀ * (T * (1 + ‖ξ‖) ^ (-(N : ℝ))) := by gcongr
    _ = _ := by ring

end TimeSlice
