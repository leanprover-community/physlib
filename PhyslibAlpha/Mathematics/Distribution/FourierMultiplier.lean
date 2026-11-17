/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Data.Nat.Choose.Multinomial

/-!

# Fourier multipliers on Schwartz functions

Sums and commutation of Fourier multipliers and their derivatives in a parameter.

## i. Overview

Sums and commutation of Fourier multipliers and their derivatives in a parameter. Compositions with
bounded smooth functions have temperate growth.

## ii. Key results

- `continuous_multiplierFamily_apply` : The evolution of fixed Schwartz data is jointly continuous
  in time and position, for every multiplier family that is jointly continuous and locally dominated
  against the Fourier transform of the data.
- `hasTemperateGrowth_comp_of_bounded` : Composition of a smooth function with bounded derivatives
  on `[0, ∞)` with a nonnegative function of temperate growth has temperate growth.
- `functional_fourier` : A continuous linear functional commutes with the Fourier transform of a
  Schwartz function.
- `hasDerivAt_multiplierFamily` : Differentiation in time of a family of Fourier multipliers, under
  the Fourier integral.

## iii. Table of contents

- A. The Klein–Gordon propagation multiplier
- B. The free Klein–Gordon evolution and its group law
- C. The free Klein–Gordon evolution as a one-parameter group
- D. The homogeneous Klein–Gordon evolution of Schwartz data
- E. Finite propagation speed for the homogeneous Klein–Gordon evolution
- F. The retarded solution as a tempered distribution in space

## iv. References

None.

## A. The Klein–Gordon propagation multiplier

Lemmas: `hasTemperateGrowth_comp_of_bounded`.

## B. The free Klein–Gordon evolution and its group law

Lemmas: `fourierMultiplierCLM_add`.

## C. The free Klein–Gordon evolution as a one-parameter group

Lemmas: `multiplier_comm`.

## D. The homogeneous Klein–Gordon evolution of Schwartz data

Lemmas: `multiplier_apply_eq`, `hasDerivAt_multiplierFamily`, `lineDeriv_fourierMultiplier`,
`continuous_multiplierFamily_apply`.

## E. Finite propagation speed for the homogeneous Klein–Gordon evolution

Lemmas: `hasLineDerivAt_lineDerivOp`, `functional_fourier`, `integrable_fourier_integrand`.

## F. The retarded solution as a tempered distribution in space

Lemmas: `fourier_smul_fourierInv_of_even`.

-/

@[expose] public section

noncomputable section

open scoped ContDiff SchwartzMap FourierTransform LineDeriv
open Function Set TopologicalSpace Topology MeasureTheory
universe u

namespace FourierMultiplier

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Composition of a smooth function with bounded derivatives on `[0, ∞)` with a nonnegative
function of temperate growth has temperate growth. -/
lemma hasTemperateGrowth_comp_of_bounded {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {C : ℝ}
    (hC : ∀ n : ℕ, ∀ y : ℝ, 0 ≤ y → |iteratedDeriv n g y| ≤ C) {q : E → ℝ}
    (hq : q.HasTemperateGrowth) (hq0 : ∀ ξ, 0 ≤ q ξ) : (fun ξ => g (q ξ)).HasTemperateGrowth := by
  refine HasTemperateGrowth.comp' (g := g) (f := q) (t := Ici 0)
    (fun y ⟨ξ, hξ⟩ => hξ ▸ hq0 ξ) (uniqueDiffOn_Ici 0) hg.contDiffOn ?_ hq
  intro N
  refine ⟨0, max C 0, le_max_right _ _, fun n _ y hy => ?_⟩
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0)
      (hg.contDiffAt.of_le (by exact_mod_cast le_top)) hy, Real.norm_eq_abs]
  rw [pow_zero, mul_one]
  exact (hC n y hy).trans (le_max_left _ _)
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]

omit [CompleteSpace F] in
lemma fourierMultiplierCLM_add {g₁ g₂ : E → ℂ} (h₁ : g₁.HasTemperateGrowth)
    (h₂ : g₂.HasTemperateGrowth) (f : 𝓢(E, F)) :
    SchwartzMap.fourierMultiplierCLM F (g₁ + g₂) f =
      SchwartzMap.fourierMultiplierCLM F g₁ f + SchwartzMap.fourierMultiplierCLM F g₂ f := by
  have := congrArg (fun T => T f) (SchwartzMap.fourierMultiplierCLM_sum (𝕜 := ℂ) F
    (g := ![g₁, g₂]) (s := Finset.univ) (by intro i _; fin_cases i <;> simpa))
  have e : (g₁ + g₂) = fun x => g₁ x + g₂ x := rfl
  rw [e]
  simpa [Fin.sum_univ_two] using this

lemma multiplier_comm {g₁ g₂ : E → ℂ} (h₁ : g₁.HasTemperateGrowth) (h₂ : g₂.HasTemperateGrowth)
    (f : 𝓢(E, F)) :
    SchwartzMap.fourierMultiplierCLM F g₁ (SchwartzMap.fourierMultiplierCLM F g₂ f) =
      SchwartzMap.fourierMultiplierCLM F g₂ (SchwartzMap.fourierMultiplierCLM F g₁ f) := by
  rw [SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply h₁ h₂,
    SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply h₂ h₁, mul_comm]
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]

omit [CompleteSpace F] in
/-- The pointwise Fourier integral of a Fourier multiplier with temperate growth. -/
lemma multiplier_apply_eq {g : E → ℂ} (hg : g.HasTemperateGrowth) (a : 𝓢(E, F)) (x : E) :
    SchwartzMap.fourierMultiplierCLM F g a x =
      ∫ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) • (g ξ • 𝓕 a ξ) := by
  simp only [SchwartzMap.fourierMultiplierCLM_apply]
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  simp [SchwartzMap.smulLeftCLM_apply_apply hg, Circle.smul_def]

omit [CompleteSpace F] in
/-- Differentiation in time of a family of Fourier multipliers, under the Fourier integral. -/
lemma hasDerivAt_multiplierFamily (a : 𝓢(E, F)) (x : E) (gfam gfam' : ℝ → E → ℂ)
    (hg : ∀ r, (gfam r).HasTemperateGrowth) (hg' : ∀ r, (gfam' r).HasTemperateGrowth)
    (hd : ∀ ξ r, HasDerivAt (fun r' => gfam r' ξ) (gfam' r ξ) r) (τ : ℝ)
    (B : E → ℝ) (hB : MeasureTheory.Integrable B MeasureTheory.volume)
    (hb : ∀ ξ r, r ∈ Metric.ball τ 1 → ‖gfam' r ξ‖ * ‖𝓕 a ξ‖ ≤ B ξ) :
    HasDerivAt (fun r => SchwartzMap.fourierMultiplierCLM F (gfam r) a x)
      (SchwartzMap.fourierMultiplierCLM F (gfam' τ) a x) τ := by
  have hchar : Continuous fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_id.inner continuous_const))
  have hnorm : ∀ (ξ : E) (v : F), ‖(𝐞 (inner ℝ ξ x) : ℂ) • v‖ = ‖v‖ := fun ξ v => by
    rw [norm_smul, Circle.norm_coe, one_mul]
  have hmeas : ∀ (h : E → ℂ), Continuous h → MeasureTheory.AEStronglyMeasurable
      (fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) • (h ξ • 𝓕 a ξ)) MeasureTheory.volume :=
    fun h hh => (hchar.smul (hh.smul (𝓕 a).continuous)).aestronglyMeasurable
  have hint : ∀ (h : E → ℂ), h.HasTemperateGrowth → MeasureTheory.Integrable
      (fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) • (h ξ • 𝓕 a ξ)) MeasureTheory.volume := by
    intro h hh
    have := (SchwartzMap.smulLeftCLM F h (𝓕 a)).integrable (μ := MeasureTheory.volume)
    refine this.norm.mono' ((hmeas h hh.1.continuous)) (Filter.Eventually.of_forall fun ξ => ?_)
    rw [hnorm]
    simp [SchwartzMap.smulLeftCLM_apply_apply hh]
  simp_rw [multiplier_apply_eq (hg _) a x]
  rw [multiplier_apply_eq (hg' τ) a x]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r ξ => (𝐞 (inner ℝ ξ x) : ℂ) • (gfam r ξ • 𝓕 a ξ))
    (F' := fun r ξ => (𝐞 (inner ℝ ξ x) : ℂ) • (gfam' r ξ • 𝓕 a ξ))
    (bound := B) (Metric.ball_mem_nhds τ one_pos)
    (Filter.Eventually.of_forall fun r => hmeas _ (hg r).1.continuous) (hint _ (hg τ))
    (hmeas _ (hg' τ).1.continuous) ?_ hB ?_).2
  · refine Filter.Eventually.of_forall fun ξ r hr => ?_
    rw [hnorm, norm_smul]
    exact hb ξ r hr
  · exact Filter.Eventually.of_forall fun ξ r _ =>
      ((hd ξ r).smul_const (𝓕 a ξ)).const_smul _

open LineDeriv in
/-- Directional derivatives of Schwartz functions commute with Fourier multipliers. -/
lemma lineDeriv_fourierMultiplier {g : E → ℂ} (hg : g.HasTemperateGrowth) (m : E)
    (f : 𝓢(E, F)) :
    ∂_{m} (SchwartzMap.fourierMultiplierCLM F g f) =
      SchwartzMap.fourierMultiplierCLM F g (∂_{m} f) := by
  rw [SchwartzMap.lineDeriv_eq_fourierMultiplierCLM, SchwartzMap.lineDeriv_eq_fourierMultiplierCLM,
    map_smul]
  congr 1
  have hi : (fun ξ : E => (inner ℝ ξ m : ℝ)).HasTemperateGrowth :=
    Function.hasTemperateGrowth_inner_left m
  have e : ∀ h : 𝓢(E, F), SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) F (fun ξ : E => inner ℝ ξ m) h =
      SchwartzMap.fourierMultiplierCLM (𝕜 := ℂ) F (fun ξ : E => ((inner ℝ ξ m : ℝ) : ℂ)) h :=
    fun h => (SchwartzMap.fourierMultiplierCLM_ofReal ℂ hi h).symm
  rw [e, e]
  exact (multiplier_comm F hg
    (g₂ := fun ξ : E => ((inner ℝ ξ m : ℝ) : ℂ)) (Complex.hasTemperateGrowth_ofReal.comp hi) f).symm

omit [CompleteSpace F] in
/-- The evolution of fixed Schwartz data is jointly continuous in time and position, for every
multiplier family that is jointly continuous and locally dominated against the Fourier transform of
the data. -/
lemma continuous_multiplierFamily_apply (a : 𝓢(E, F)) (g : ℝ → E → ℂ)
    (hg : Continuous fun p : ℝ × E => g p.1 p.2) (hgt : ∀ r, (g r).HasTemperateGrowth)
    (hb : ∀ R : ℝ, ∃ q : E → ℝ, MeasureTheory.Integrable q MeasureTheory.volume ∧
      ∀ r ξ, |r| ≤ R → ‖g r ξ‖ * ‖𝓕 a ξ‖ ≤ q ξ) :
    Continuous fun p : ℝ × E => SchwartzMap.fourierMultiplierCLM F (g p.1) a p.2 := by
  simp_rw [multiplier_apply_eq (hgt _) a]
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨q, hq, hqb⟩ := hb (|p₀.1| + 1)
  refine MeasureTheory.continuousAt_of_dominated (bound := q) ?_ ?_ hq ?_
  · refine Filter.Eventually.of_forall fun p => Continuous.aestronglyMeasurable ?_
    have h2 : Continuous fun ξ : E => g p.1 ξ := hg.comp (continuous_const.prodMk continuous_id)
    have hc : Continuous fun ξ : E => (𝐞 (inner ℝ ξ p.2) : ℂ) :=
      continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (continuous_id.inner continuous_const))
    exact hc.smul (h2.smul (𝓕 a).continuous)
  · have : ∀ᶠ p in nhds p₀, |p.1| < |p₀.1| + 1 :=
      (continuous_fst.abs.continuousAt.eventually (gt_mem_nhds (by linarith)))
    filter_upwards [this] with p hp
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [norm_smul, Circle.norm_coe, one_mul, norm_smul]
    exact hqb _ _ hp.le
  · refine Filter.Eventually.of_forall fun ξ => ?_
    have h2 : Continuous fun p : ℝ × E => g p.1 ξ :=
      (hg.comp (continuous_id.prodMk continuous_const)).comp continuous_fst
    have hc : Continuous fun p : ℝ × E => (𝐞 (inner ℝ ξ p.2) : ℂ) :=
      continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (continuous_const.inner continuous_snd))
    exact (hc.smul (h2.smul continuous_const)).continuousAt
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma hasLineDerivAt_lineDerivOp (f : 𝓢(E, ℂ)) (m x : E) :
    HasLineDerivAt ℝ (⇑f) (∂_{m} f x) x m := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  exact (f.differentiableAt.hasFDerivAt).hasLineDerivAt m
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A continuous linear functional commutes with the Fourier transform of a Schwartz function. -/
lemma functional_fourier (ℓ : F →L[ℂ] ℂ) (g : 𝓢(E, F)) (ξ : E) :
    ℓ (𝓕 g ξ) = 𝓕 (SchwartzMap.postcompCLM (𝕜 := ℂ) (E := E) ℓ g) ξ := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq, SchwartzMap.fourier_coe, Real.fourier_eq]
  have hint : MeasureTheory.Integrable (fun x : E => 𝐞 (-inner ℝ x ξ) • g x)
      MeasureTheory.volume := by
    refine (g.integrable (μ := MeasureTheory.volume)).norm.mono'
      ((Real.continuous_fourierChar.comp
        ((continuous_id.inner continuous_const).neg)).smul g.continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
  have := ContinuousLinearMap.integral_comp_comm (ℓ.restrictScalars ℝ) hint
  have e : ∀ v, (SchwartzMap.postcompCLM (𝕜 := ℂ) (E := E) ℓ g) v = ℓ (g v) := fun _ => rfl
  simp only [ContinuousLinearMap.coe_restrictScalars', Circle.smul_def, map_smul, e] at this ⊢
  exact this.symm

omit [CompleteSpace F] in
/-- The Fourier integrand of a multiplier applied to Schwartz data is integrable. -/
lemma integrable_fourier_integrand {g : E → ℂ} (hg : g.HasTemperateGrowth) (a : 𝓢(E, F)) (x : E) :
    MeasureTheory.Integrable (fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) • (g ξ • 𝓕 a ξ))
      MeasureTheory.volume := by
  have hchar : Continuous fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_id.inner continuous_const))
  have := (SchwartzMap.smulLeftCLM F g (𝓕 a)).integrable (μ := MeasureTheory.volume)
  refine this.norm.mono' (hchar.smul (hg.1.continuous.smul (𝓕 a).continuous)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [norm_smul, Circle.norm_coe, one_mul]
  simp [SchwartzMap.smulLeftCLM_apply_apply hg]
end

section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]

/-- An even multiplier acts the same on a function and on its transpose. -/
lemma fourier_smul_fourierInv_of_even {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (m : E → ℂ) (hm : ∀ x, m (-x) = m x) (g : E → G) (y : E) :
    𝓕 (fun x => m x • 𝓕⁻ g x) y = 𝓕⁻ (fun x => m x • 𝓕 g x) y := by
  have h : (fun x => m x • 𝓕⁻ g x) = (fun x => m x • 𝓕 g x) ∘ (LinearIsometryEquiv.neg ℝ (E :=
    E)) := by
    funext x
    simp only [Function.comp_apply, LinearIsometryEquiv.coe_neg, hm,
      Real.fourierInv_eq_fourier_neg]
  rw [h, Real.fourier_comp_linearIsometry, Real.fourierInv_eq_fourier_neg]
  rfl
end

end FourierMultiplier
