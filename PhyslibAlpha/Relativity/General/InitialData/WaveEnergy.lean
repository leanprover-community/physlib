/-
Copyright (c) 2026 Alex Vergara Gil.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!

# Energy for the one-dimensional wave equation

## i. Overview

This file starts the energy-method layer for the one-dimensional wave Cauchy
problem.  It defines the conserved energy

  E(t) = 1/2 ∫₀ᴸ (u_t(t,x)² + u_x(t,x)²) dx

and proves its time derivative, differentiating under the interval integral.
The next step is the integration-by-parts identity that makes this derivative
zero for a solution of `u_tt = u_xx` with homogeneous Dirichlet data.


## ii. Key results

- `waveEnergy`
- `hasDerivAt_waveEnergy`
- `waveEnergy_eq_initial`
- `WaveSolutionOn` : the regularity used by the energy method.
- `WaveSolutionOn.sub` : the difference of two regular solutions is a regular solution.
- `wave_unique_of_same_data`

## iii. Table of contents

- A. The one-dimensional wave energy
- B. Zero data and conservation
- C. Uniqueness for the one-dimensional problem

## iv. References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, §2.4. [ref: Evans2010PDE]
-/
@[expose] public section

/-! ## A. The one-dimensional wave energy -/

open scoped Interval Topology
open MeasureTheory

namespace GeneralRelativity

/-- The energy density `u_t² + u_x²` of a one-dimensional wave field. -/
noncomputable def waveEnergyIntegrand (ut ux : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  ut t x ^ 2 + ux t x ^ 2

/-- The energy on the interval `[0, L]`. -/
noncomputable def waveEnergy (ut ux : ℝ → ℝ → ℝ) (L t : ℝ) : ℝ :=
  (1 / 2) * ∫ x in (0 : ℝ)..L, waveEnergyIntegrand ut ux t x

/-- The time derivative of the energy density. -/
noncomputable def waveEnergyDerivIntegrand
    (ut ux utt uxt : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  2 * ut t x * utt t x + 2 * ux t x * uxt t x

lemma continuous_waveEnergyIntegrand_section
    (ut ux : ℝ → ℝ → ℝ) (hut : Continuous (Function.uncurry ut))
    (hux : Continuous (Function.uncurry ux)) (t : ℝ) :
    Continuous (fun x : ℝ => waveEnergyIntegrand ut ux t x) := by
  have h1 : Continuous (fun x : ℝ => ut t x) :=
    hut.comp (continuous_const.prodMk continuous_id)
  have h2 : Continuous (fun x : ℝ => ux t x) :=
    hux.comp (continuous_const.prodMk continuous_id)
  unfold waveEnergyIntegrand
  exact (h1.pow 2).add (h2.pow 2)

lemma continuous_waveEnergyDerivIntegrand_section
    (ut ux utt uxt : ℝ → ℝ → ℝ)
    (hut : Continuous (Function.uncurry ut))
    (hux : Continuous (Function.uncurry ux))
    (hutt : Continuous (Function.uncurry utt))
    (huxt : Continuous (Function.uncurry uxt)) (t : ℝ) :
    Continuous (fun x : ℝ => waveEnergyDerivIntegrand ut ux utt uxt t x) := by
  have h_ut : Continuous (fun x : ℝ => ut t x) :=
    hut.comp (continuous_const.prodMk continuous_id)
  have h_ux : Continuous (fun x : ℝ => ux t x) :=
    hux.comp (continuous_const.prodMk continuous_id)
  have h_utt : Continuous (fun x : ℝ => utt t x) :=
    hutt.comp (continuous_const.prodMk continuous_id)
  have h_uxt : Continuous (fun x : ℝ => uxt t x) :=
    huxt.comp (continuous_const.prodMk continuous_id)
  unfold waveEnergyDerivIntegrand
  exact ((continuous_const.mul h_ut).mul h_utt).add
    ((continuous_const.mul h_ux).mul h_uxt)

lemma hasDerivAt_waveEnergyIntegrand (ut ux utt uxt : ℝ → ℝ → ℝ)
    (hut : ∀ t x, HasDerivAt (fun t : ℝ => ut t x) (utt t x) t)
    (hux : ∀ t x, HasDerivAt (fun t : ℝ => ux t x) (uxt t x) t) (t x : ℝ) :
    HasDerivAt (fun t : ℝ => waveEnergyIntegrand ut ux t x)
      (waveEnergyDerivIntegrand ut ux utt uxt t x) t := by
  unfold waveEnergyIntegrand waveEnergyDerivIntegrand
  have h1 : HasDerivAt (fun t : ℝ => ut t x ^ 2) (2 * ut t x * utt t x) t := by
    have h := (hut t x).mul (hut t x)
    convert h using 1
    · funext y
      simp [pow_two]
    · ring
  have h2 : HasDerivAt (fun t : ℝ => ux t x ^ 2) (2 * ux t x * uxt t x) t := by
    have h := (hux t x).mul (hux t x)
    convert h using 1
    · funext y
      simp [pow_two]
    · ring
  exact h1.add h2

/-- Differentiation of the wave energy under the interval integral.  The bound
`M` is a global bound on the differentiated energy density; it is a regularity
hypothesis, not a physical assumption. -/
lemma hasDerivAt_waveEnergy (ut ux utt uxt : ℝ → ℝ → ℝ) (L t M : ℝ)
    (hut : ∀ s x, HasDerivAt (fun s : ℝ => ut s x) (utt s x) s)
    (hux : ∀ s x, HasDerivAt (fun s : ℝ => ux s x) (uxt s x) s)
    (hut_cont : Continuous (Function.uncurry ut))
    (hux_cont : Continuous (Function.uncurry ux))
    (hutt_cont : Continuous (Function.uncurry utt))
    (huxt_cont : Continuous (Function.uncurry uxt))
    (hbound : ∀ s x, ‖waveEnergyDerivIntegrand ut ux utt uxt s x‖ ≤ M) :
    HasDerivAt (waveEnergy ut ux L)
      ((1 / 2) * ∫ x in (0 : ℝ)..L,
        waveEnergyDerivIntegrand ut ux utt uxt t x) t := by
  have hF_meas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun x : ℝ => waveEnergyIntegrand ut ux s x)
        (volume.restrict (Ι (0 : ℝ) L)) := by
    filter_upwards with s
    exact (continuous_waveEnergyIntegrand_section ut ux hut_cont hux_cont s).aestronglyMeasurable
  have hF_int : IntervalIntegrable (fun x : ℝ => waveEnergyIntegrand ut ux t x)
      volume (0 : ℝ) L :=
    (continuous_waveEnergyIntegrand_section ut ux hut_cont hux_cont t).intervalIntegrable _ _
  have hF'_meas : AEStronglyMeasurable
      (fun x : ℝ => waveEnergyDerivIntegrand ut ux utt uxt t x)
      (volume.restrict (Ι (0 : ℝ) L)) :=
    (continuous_waveEnergyDerivIntegrand_section ut ux utt uxt
      hut_cont hux_cont hutt_cont huxt_cont t).aestronglyMeasurable
  have hbound_ae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι (0 : ℝ) L →
      ∀ s : ℝ, s ∈ (Set.univ : Set ℝ) →
        ‖waveEnergyDerivIntegrand ut ux utt uxt s x‖ ≤ (fun _ : ℝ => M) x := by
    filter_upwards with x hx s hs
    exact hbound s x
  have hbound_int : IntervalIntegrable (fun _ : ℝ => M) volume (0 : ℝ) L :=
    (continuous_const : Continuous (fun _ : ℝ => M)).intervalIntegrable (0 : ℝ) L
  have h_diff : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι (0 : ℝ) L →
      ∀ s : ℝ, s ∈ (Set.univ : Set ℝ) →
        HasDerivAt (fun s : ℝ => waveEnergyIntegrand ut ux s x)
          (waveEnergyDerivIntegrand ut ux utt uxt s x) s := by
    filter_upwards with x hx s hs
    exact hasDerivAt_waveEnergyIntegrand ut ux utt uxt hut hux s x
  have h := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => waveEnergyIntegrand ut ux s x)
    (F' := fun s x => waveEnergyDerivIntegrand ut ux utt uxt s x)
    (x₀ := t) (s := Set.univ) (a := (0 : ℝ)) (b := L)
    (by simp) hF_meas hF_int hF'_meas hbound_ae hbound_int h_diff).2
  convert h.const_mul (1 / 2 : ℝ) using 1
  funext y
  simp [waveEnergy]

/-! ## B. Zero data and conservation -/

/-- The differentiated energy density integrates to zero for a wave solution with
homogeneous Dirichlet data.  This is the integration-by-parts step of the energy
method; `hwave` and `hmixed` are the wave equation and the symmetry of the mixed
partial derivatives, respectively. -/
lemma waveEnergyDerivIntegral_eq_zero
    (ut ux utt uxt utx uxx : ℝ → ℝ → ℝ) (L t : ℝ)
    (hwave : ∀ x, utt t x = uxx t x)
    (hmixed : ∀ x, uxt t x = utx t x)
    (hut_x : ∀ x, HasDerivAt (fun x : ℝ => ut t x) (utx t x) x)
    (hux_x : ∀ x, HasDerivAt (fun x : ℝ => ux t x) (uxx t x) x)
    (hut_cont : Continuous (fun x : ℝ => ut t x))
    (hux_cont : Continuous (fun x : ℝ => ux t x))
    (hutx_cont : Continuous (fun x : ℝ => utx t x))
    (huxx_cont : Continuous (fun x : ℝ => uxx t x))
    (hbc0 : ut t 0 = 0) (hbcL : ut t L = 0) :
    (∫ x in (0 : ℝ)..L, waveEnergyDerivIntegrand ut ux utt uxt t x) = 0 := by
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => ux t x) (v := fun x : ℝ => ut t x)
    (u' := fun x : ℝ => uxx t x) (v' := fun x : ℝ => utx t x)
    (fun x _ => hux_x x) (fun x _ => hut_x x)
    (huxx_cont.intervalIntegrable (0 : ℝ) L)
    (hutx_cont.intervalIntegrable (0 : ℝ) L)
  have h1int : IntervalIntegrable (fun x : ℝ => ut t x * uxx t x) volume (0 : ℝ) L :=
    (hut_cont.mul huxx_cont).intervalIntegrable (0 : ℝ) L
  have h2int : IntervalIntegrable (fun x : ℝ => ux t x * utx t x) volume (0 : ℝ) L :=
    (hux_cont.mul hutx_cont).intervalIntegrable (0 : ℝ) L
  have hfactor : (fun x : ℝ => waveEnergyDerivIntegrand ut ux utt uxt t x) =
      fun x : ℝ => 2 * (ut t x * utt t x + ux t x * uxt t x) := by
    funext x
    unfold waveEnergyDerivIntegrand
    ring
  calc
    (∫ x in (0 : ℝ)..L, waveEnergyDerivIntegrand ut ux utt uxt t x)
        = 2 * ∫ x in (0 : ℝ)..L,
            (ut t x * utt t x + ux t x * uxt t x) := by
          rw [hfactor, intervalIntegral.integral_const_mul]
    _ = 2 * ∫ x in (0 : ℝ)..L,
            (ut t x * uxx t x + ux t x * utx t x) := by
          simp_rw [hwave, hmixed]
    _ = 2 * ((∫ x in (0 : ℝ)..L, ut t x * uxx t x) +
            ∫ x in (0 : ℝ)..L, ux t x * utx t x) := by
          rw [intervalIntegral.integral_add h1int h2int]
    _ = 2 * ((∫ x in (0 : ℝ)..L, ut t x * uxx t x) +
            (ux t L * ut t L - ux t 0 * ut t 0 -
              ∫ x in (0 : ℝ)..L, uxx t x * ut t x)) := by
          rw [hIBP]
    _ = 0 := by
          rw [hbc0, hbcL]
          simp only [mul_zero, sub_zero, zero_sub]
          have hcomm : (∫ x in (0 : ℝ)..L, uxx t x * ut t x) =
              ∫ x in (0 : ℝ)..L, ut t x * uxx t x := by
            congr 1
            funext x
            ring
          rw [hcomm]
          ring

/-- Combined form: the energy has zero time derivative. -/
lemma hasDerivAt_waveEnergy_zero
    (ut ux utt uxt utx uxx : ℝ → ℝ → ℝ) (L t M : ℝ)
    (hut : ∀ s x, HasDerivAt (fun s : ℝ => ut s x) (utt s x) s)
    (hux : ∀ s x, HasDerivAt (fun s : ℝ => ux s x) (uxt s x) s)
    (hut_x : ∀ s x, HasDerivAt (fun x : ℝ => ut s x) (utx s x) x)
    (hux_x : ∀ s x, HasDerivAt (fun x : ℝ => ux s x) (uxx s x) x)
    (hut_cont : Continuous (Function.uncurry ut))
    (hux_cont : Continuous (Function.uncurry ux))
    (hutt_cont : Continuous (Function.uncurry utt))
    (huxt_cont : Continuous (Function.uncurry uxt))
    (hutx_cont : Continuous (Function.uncurry utx))
    (huxx_cont : Continuous (Function.uncurry uxx))
    (hbound : ∀ s x, ‖waveEnergyDerivIntegrand ut ux utt uxt s x‖ ≤ M)
    (hwave : ∀ s x, utt s x = uxx s x)
    (hmixed : ∀ s x, uxt s x = utx s x)
    (hbc0 : ∀ s, ut s 0 = 0) (hbcL : ∀ s, ut s L = 0) :
    HasDerivAt (waveEnergy ut ux L) 0 t := by
  have h := hasDerivAt_waveEnergy ut ux utt uxt L t M hut hux
    hut_cont hux_cont hutt_cont huxt_cont hbound
  have hsec_ut : Continuous (fun x : ℝ => ut t x) :=
    hut_cont.comp (continuous_const.prodMk continuous_id)
  have hsec_ux : Continuous (fun x : ℝ => ux t x) :=
    hux_cont.comp (continuous_const.prodMk continuous_id)
  have hsec_utx : Continuous (fun x : ℝ => utx t x) :=
    hutx_cont.comp (continuous_const.prodMk continuous_id)
  have hsec_uxx : Continuous (fun x : ℝ => uxx t x) :=
    huxx_cont.comp (continuous_const.prodMk continuous_id)
  have hz := waveEnergyDerivIntegral_eq_zero ut ux utt uxt utx uxx L t
    (hwave t) (hmixed t) (hut_x t) (hux_x t)
    hsec_ut hsec_ux hsec_utx hsec_uxx (hbc0 t) (hbcL t)
  rw [hz] at h
  simpa using h

/-- Energy conservation for the one-dimensional wave equation under the stated
regularity and homogeneous Dirichlet hypotheses. -/
lemma waveEnergy_eq_initial
    (ut ux utt uxt utx uxx : ℝ → ℝ → ℝ) (L M : ℝ)
    (hut : ∀ s x, HasDerivAt (fun s : ℝ => ut s x) (utt s x) s)
    (hux : ∀ s x, HasDerivAt (fun s : ℝ => ux s x) (uxt s x) s)
    (hut_x : ∀ s x, HasDerivAt (fun x : ℝ => ut s x) (utx s x) x)
    (hux_x : ∀ s x, HasDerivAt (fun x : ℝ => ux s x) (uxx s x) x)
    (hut_cont : Continuous (Function.uncurry ut))
    (hux_cont : Continuous (Function.uncurry ux))
    (hutt_cont : Continuous (Function.uncurry utt))
    (huxt_cont : Continuous (Function.uncurry uxt))
    (hutx_cont : Continuous (Function.uncurry utx))
    (huxx_cont : Continuous (Function.uncurry uxx))
    (hbound : ∀ s x, ‖waveEnergyDerivIntegrand ut ux utt uxt s x‖ ≤ M)
    (hwave : ∀ s x, utt s x = uxx s x)
    (hmixed : ∀ s x, uxt s x = utx s x)
    (hbc0 : ∀ s, ut s 0 = 0) (hbcL : ∀ s, ut s L = 0) :
    ∀ t, waveEnergy ut ux L t = waveEnergy ut ux L 0 := by
  have hzero : ∀ s, HasDerivAt (waveEnergy ut ux L) 0 s := fun s =>
    hasDerivAt_waveEnergy_zero ut ux utt uxt utx uxx L s M hut hux hut_x hux_x
      hut_cont hux_cont hutt_cont huxt_cont hutx_cont huxx_cont hbound hwave hmixed hbc0 hbcL
  have hderiv : ∀ s, deriv (waveEnergy ut ux L) s = 0 := fun s => (hzero s).deriv
  intro t
  exact (is_const_of_deriv_eq_zero (fun s => (hzero s).differentiableAt) hderiv 0 t).symm

/-- The energy at time zero vanishes when both initial data vanish. -/
lemma waveEnergy_eq_zero_initial (ut ux : ℝ → ℝ → ℝ) (L : ℝ)
    (hut0 : ∀ x, ut 0 x = 0) (hux0 : ∀ x, ux 0 x = 0) :
    waveEnergy ut ux L 0 = 0 := by
  unfold waveEnergy waveEnergyIntegrand
  simp [hut0, hux0]

/-- If the energy vanishes, then both first derivatives vanish pointwise on the
half-open interval.  This is the step from the integral identity to pointwise
information, using continuity and the positivity of the interval measure. -/
lemma eq_zero_of_waveEnergy_eq_zero (ut ux : ℝ → ℝ → ℝ) {L t : ℝ}
    (hut_cont : Continuous (fun x : ℝ => ut t x))
    (hux_cont : Continuous (fun x : ℝ => ux t x))
    (hL : 0 < L) (hE : waveEnergy ut ux L t = 0) :
    ∀ x ∈ Set.Ioc 0 L, ut t x = 0 ∧ ux t x = 0 := by
  have hInt : (∫ x in (0 : ℝ)..L, waveEnergyIntegrand ut ux t x) = 0 := by
    have h := hE
    unfold waveEnergy at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have hcont : Continuous (fun x : ℝ => waveEnergyIntegrand ut ux t x) := by
    unfold waveEnergyIntegrand
    exact (hut_cont.pow 2).add (hux_cont.pow 2)
  have hfi : IntervalIntegrable (fun x : ℝ => waveEnergyIntegrand ut ux t x)
      volume (0 : ℝ) L :=
    hcont.intervalIntegrable (0 : ℝ) L
  have hnonneg : ∀ x, 0 ≤ waveEnergyIntegrand ut ux t x := by
    intro x
    unfold waveEnergyIntegrand
    nlinarith [sq_nonneg (ut t x), sq_nonneg (ux t x)]
  have hAE : (fun x : ℝ => waveEnergyIntegrand ut ux t x) =ᵐ[
      volume.restrict (Set.Ioc 0 L)] 0 :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae (le_of_lt hL)
      (Filter.Eventually.of_forall hnonneg) hfi).mp hInt
  have hEq : Set.EqOn (fun x : ℝ => waveEnergyIntegrand ut ux t x) 0 (Set.Ioc 0 L) :=
    Measure.eqOn_Ioc_of_ae_eq (μ := volume) hAE hcont.continuousOn continuousOn_const
  intro x hx
  have hx0 : waveEnergyIntegrand ut ux t x = 0 := hEq hx
  unfold waveEnergyIntegrand at hx0
  constructor
  · have h1 : ut t x ^ 2 = 0 := by
      nlinarith [sq_nonneg (ut t x), sq_nonneg (ux t x)]
    exact sq_eq_zero_iff.mp h1
  · have h2 : ux t x ^ 2 = 0 := by
      nlinarith [sq_nonneg (ut t x), sq_nonneg (ux t x)]
    exact sq_eq_zero_iff.mp h2

/-- If the time derivative vanishes at every time, the field is constant in
time at that spatial point. -/
lemma u_eq_initial_of_ut_zero (u ut : ℝ → ℝ → ℝ) (x : ℝ)
    (hu_t : ∀ s, HasDerivAt (fun s : ℝ => u s x) (ut s x) s)
    (hut0 : ∀ s, ut s x = 0) :
    ∀ t, u t x = u 0 x := by
  have hderiv : ∀ s, deriv (fun s : ℝ => u s x) s = 0 := by
    intro s
    rw [(hu_t s).deriv, hut0 s]
  exact fun t => is_const_of_deriv_eq_zero
    (fun s => (hu_t s).differentiableAt) hderiv t 0

/-- Interior zero-data uniqueness for the one-dimensional wave equation, proved
by the energy method.  The hypotheses bundle the differentiability, continuity,
mixed-partial symmetry and homogeneous Dirichlet data used by the energy
identity; these are regularity assumptions, not additional physical premises. -/
lemma wave_zero_of_zero_data (u ut ux utt uxt utx uxx : ℝ → ℝ → ℝ)
    (L M : ℝ) (hL : 0 < L)
    (hu_t : ∀ s x, HasDerivAt (fun s : ℝ => u s x) (ut s x) s)
    (hut : ∀ s x, HasDerivAt (fun s : ℝ => ut s x) (utt s x) s)
    (hux : ∀ s x, HasDerivAt (fun s : ℝ => ux s x) (uxt s x) s)
    (hut_x : ∀ s x, HasDerivAt (fun x : ℝ => ut s x) (utx s x) x)
    (hux_x : ∀ s x, HasDerivAt (fun x : ℝ => ux s x) (uxx s x) x)
    (hut_cont : Continuous (Function.uncurry ut))
    (hux_cont : Continuous (Function.uncurry ux))
    (hutt_cont : Continuous (Function.uncurry utt))
    (huxt_cont : Continuous (Function.uncurry uxt))
    (hutx_cont : Continuous (Function.uncurry utx))
    (huxx_cont : Continuous (Function.uncurry uxx))
    (hbound : ∀ s x, ‖waveEnergyDerivIntegrand ut ux utt uxt s x‖ ≤ M)
    (hwave : ∀ s x, utt s x = uxx s x)
    (hmixed : ∀ s x, uxt s x = utx s x)
    (hbc0 : ∀ s, ut s 0 = 0) (hbcL : ∀ s, ut s L = 0)
    (hinit : ∀ x, u 0 x = 0) (hvel : ∀ x, ut 0 x = 0)
    (hux0 : ∀ x, ux 0 x = 0) :
    ∀ t x, x ∈ Set.Ioo 0 L → u t x = 0 := by
  intro t x hx
  have hE0 : waveEnergy ut ux L 0 = 0 :=
    waveEnergy_eq_zero_initial ut ux L hvel hux0
  have hEconst : ∀ s, waveEnergy ut ux L s = waveEnergy ut ux L 0 :=
    waveEnergy_eq_initial ut ux utt uxt utx uxx L M hut hux hut_x hux_x
      hut_cont hux_cont hutt_cont huxt_cont hutx_cont huxx_cont hbound hwave hmixed hbc0 hbcL
  have hsec_ut : ∀ s, Continuous (fun x : ℝ => ut s x) := fun s =>
    hut_cont.comp (continuous_const.prodMk continuous_id)
  have hsec_ux : ∀ s, Continuous (fun x : ℝ => ux s x) := fun s =>
    hux_cont.comp (continuous_const.prodMk continuous_id)
  have hzero : ∀ s, ut s x = 0 := by
    intro s
    have hEs : waveEnergy ut ux L s = 0 := by rw [hEconst s, hE0]
    exact (eq_zero_of_waveEnergy_eq_zero ut ux (hsec_ut s) (hsec_ux s) hL hEs
      x ⟨hx.1, le_of_lt hx.2⟩).1
  have hconst := u_eq_initial_of_ut_zero u ut x (fun s => hu_t s x) hzero t
  rw [hconst, hinit x]

/-- Zero-data uniqueness on the closed interval.  The interior is covered by
the energy argument; the endpoints follow from the homogeneous Dirichlet
boundary values. -/
lemma wave_zero_of_zero_data_Icc
    (u ut ux utt uxt utx uxx : ℝ → ℝ → ℝ)
    (L M : ℝ) (hL : 0 < L)
    (hu_t : ∀ s x, HasDerivAt (fun s : ℝ => u s x) (ut s x) s)
    (hut : ∀ s x, HasDerivAt (fun s : ℝ => ut s x) (utt s x) s)
    (hux : ∀ s x, HasDerivAt (fun s : ℝ => ux s x) (uxt s x) s)
    (hut_x : ∀ s x, HasDerivAt (fun x : ℝ => ut s x) (utx s x) x)
    (hux_x : ∀ s x, HasDerivAt (fun x : ℝ => ux s x) (uxx s x) x)
    (hut_cont : Continuous (Function.uncurry ut))
    (hux_cont : Continuous (Function.uncurry ux))
    (hutt_cont : Continuous (Function.uncurry utt))
    (huxt_cont : Continuous (Function.uncurry uxt))
    (hutx_cont : Continuous (Function.uncurry utx))
    (huxx_cont : Continuous (Function.uncurry uxx))
    (hbound : ∀ s x, ‖waveEnergyDerivIntegrand ut ux utt uxt s x‖ ≤ M)
    (hwave : ∀ s x, utt s x = uxx s x)
    (hmixed : ∀ s x, uxt s x = utx s x)
    (hbc0 : ∀ s, ut s 0 = 0) (hbcL : ∀ s, ut s L = 0)
    (hinit : ∀ x, u 0 x = 0) (hvel : ∀ x, ut 0 x = 0)
    (hux0 : ∀ x, ux 0 x = 0)
    (hdir0 : ∀ s, u s 0 = 0) (hdirL : ∀ s, u s L = 0) :
    ∀ t x, x ∈ Set.Icc 0 L → u t x = 0 := by
  intro t x hx
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · have hx0' : x = 0 := hx0.symm
    rw [hx0']
    exact hdir0 t
  rcases eq_or_lt_of_le hx.2 with hxL | hxL
  · rw [hxL]
    exact hdirL t
  · exact wave_zero_of_zero_data u ut ux utt uxt utx uxx L M hL
      hu_t hut hux hut_x hux_x hut_cont hux_cont hutt_cont huxt_cont hutx_cont
      huxx_cont hbound hwave hmixed hbc0 hbcL hinit hvel hux0 t x ⟨hx0, hxL⟩

/-! ## C. Uniqueness for the one-dimensional problem -/

/-- A regular solution of the one-dimensional wave equation on `[0, L]`, with
the derivative fields and the differentiated homogeneous Dirichlet condition
used by the energy method.  The bound `M` is a regularity bound on the
differentiated energy density. -/
structure WaveSolutionOn
    (u ut ux utt uxt utx uxx : ℝ → ℝ → ℝ) (L M : ℝ) : Prop where
  hu_t : ∀ s x, HasDerivAt (fun s : ℝ => u s x) (ut s x) s
  hut : ∀ s x, HasDerivAt (fun s : ℝ => ut s x) (utt s x) s
  hux : ∀ s x, HasDerivAt (fun s : ℝ => ux s x) (uxt s x) s
  hut_x : ∀ s x, HasDerivAt (fun x : ℝ => ut s x) (utx s x) x
  hux_x : ∀ s x, HasDerivAt (fun x : ℝ => ux s x) (uxx s x) x
  hut_cont : Continuous (Function.uncurry ut)
  hux_cont : Continuous (Function.uncurry ux)
  hutt_cont : Continuous (Function.uncurry utt)
  huxt_cont : Continuous (Function.uncurry uxt)
  hutx_cont : Continuous (Function.uncurry utx)
  huxx_cont : Continuous (Function.uncurry uxx)
  hbound : ∀ s x, ‖waveEnergyDerivIntegrand ut ux utt uxt s x‖ ≤ M
  hwave : ∀ s x, utt s x = uxx s x
  hmixed : ∀ s x, uxt s x = utx s x
  hbc0 : ∀ s, ut s 0 = 0
  hbcL : ∀ s, ut s L = 0

/-- The difference of two regular solutions is a regular solution of the same
problem, with the difference of the derivative fields and the difference bound
`Mw` on the differentiated energy density. -/
lemma WaveSolutionOn.sub
    (u ut ux utt uxt utx uxx v vt vx vtt vxt vtx vxx : ℝ → ℝ → ℝ) (L Mu Mv Mw : ℝ)
    (S : WaveSolutionOn u ut ux utt uxt utx uxx L Mu)
    (T : WaveSolutionOn v vt vx vtt vxt vtx vxx L Mv)
    (hboundw : ∀ s x, ‖waveEnergyDerivIntegrand
      (fun s x => ut s x - vt s x)
      (fun s x => ux s x - vx s x)
      (fun s x => utt s x - vtt s x)
      (fun s x => uxt s x - vxt s x) s x‖ ≤ Mw) :
    WaveSolutionOn
      (fun s x => u s x - v s x) (fun s x => ut s x - vt s x)
      (fun s x => ux s x - vx s x) (fun s x => utt s x - vtt s x)
      (fun s x => uxt s x - vxt s x) (fun s x => utx s x - vtx s x)
      (fun s x => uxx s x - vxx s x) L Mw := by
  refine {
    hu_t := ?_
    hut := ?_
    hux := ?_
    hut_x := ?_
    hux_x := ?_
    hut_cont := ?_
    hux_cont := ?_
    hutt_cont := ?_
    huxt_cont := ?_
    hutx_cont := ?_
    huxx_cont := ?_
    hbound := ?_
    hwave := ?_
    hmixed := ?_
    hbc0 := ?_
    hbcL := ?_ }
  · intro s x
    convert (S.hu_t s x).sub (T.hu_t s x) using 1
  · intro s x
    convert (S.hut s x).sub (T.hut s x) using 1
  · intro s x
    convert (S.hux s x).sub (T.hux s x) using 1
  · intro s x
    convert (S.hut_x s x).sub (T.hut_x s x) using 1
  · intro s x
    convert (S.hux_x s x).sub (T.hux_x s x) using 1
  · convert S.hut_cont.sub T.hut_cont using 1
    funext p
    simp [Function.uncurry, Pi.sub_apply]
  · convert S.hux_cont.sub T.hux_cont using 1
    funext p
    simp [Function.uncurry, Pi.sub_apply]
  · convert S.hutt_cont.sub T.hutt_cont using 1
    funext p
    simp [Function.uncurry, Pi.sub_apply]
  · convert S.huxt_cont.sub T.huxt_cont using 1
    funext p
    simp [Function.uncurry, Pi.sub_apply]
  · convert S.hutx_cont.sub T.hutx_cont using 1
    funext p
    simp [Function.uncurry, Pi.sub_apply]
  · convert S.huxx_cont.sub T.huxx_cont using 1
    funext p
    simp [Function.uncurry, Pi.sub_apply]
  · exact hboundw
  · intro s x
    simp [(S.hwave s x), (T.hwave s x)]
  · intro s x
    simp [(S.hmixed s x), (T.hmixed s x)]
  · intro s
    simp [(S.hbc0 s), (T.hbc0 s)]
  · intro s
    simp [(S.hbcL s), (T.hbcL s)]

/-- **General-data uniqueness for the 1D wave Cauchy problem.**  Two regular
solutions with the same initial position, velocity and spatial derivative, and
the same Dirichlet boundary values, agree on the closed interval. -/
lemma wave_unique_of_same_data
    (u ut ux utt uxt utx uxx v vt vx vtt vxt vtx vxx : ℝ → ℝ → ℝ)
    (L Mu Mv Mw : ℝ) (hL : 0 < L)
    (S : WaveSolutionOn u ut ux utt uxt utx uxx L Mu)
    (T : WaveSolutionOn v vt vx vtt vxt vtx vxx L Mv)
    (hboundw : ∀ s x, ‖waveEnergyDerivIntegrand
      (fun s x => ut s x - vt s x)
      (fun s x => ux s x - vx s x)
      (fun s x => utt s x - vtt s x)
      (fun s x => uxt s x - vxt s x) s x‖ ≤ Mw)
    (hinit : ∀ x, u 0 x = v 0 x)
    (hvel : ∀ x, ut 0 x = vt 0 x)
    (hux0 : ∀ x, ux 0 x = vx 0 x)
    (hbd0 : ∀ s, u s 0 = v s 0) (hbdL : ∀ s, u s L = v s L) :
    ∀ t x, x ∈ Set.Icc 0 L → u t x = v t x := by
  let w : ℝ → ℝ → ℝ := fun s x => u s x - v s x
  let wt : ℝ → ℝ → ℝ := fun s x => ut s x - vt s x
  let wx : ℝ → ℝ → ℝ := fun s x => ux s x - vx s x
  let wtt : ℝ → ℝ → ℝ := fun s x => utt s x - vtt s x
  let wxt : ℝ → ℝ → ℝ := fun s x => uxt s x - vxt s x
  let wtx : ℝ → ℝ → ℝ := fun s x => utx s x - vtx s x
  let wxx : ℝ → ℝ → ℝ := fun s x => uxx s x - vxx s x

  have hW : WaveSolutionOn w wt wx wtt wxt wtx wxx L Mw :=
    WaveSolutionOn.sub u ut ux utt uxt utx uxx v vt vx vtt vxt vtx vxx L Mu Mv Mw S T hboundw
  have hinitw : ∀ x, w 0 x = 0 := by
    intro x
    simp [w, hinit x]
  have hvelw : ∀ x, wt 0 x = 0 := by
    intro x
    simp [wt, hvel x]
  have hux0w : ∀ x, wx 0 x = 0 := by
    intro x
    simp [wx, hux0 x]
  have hbd0w : ∀ s, w s 0 = 0 := by
    intro s
    simp [w, hbd0 s]
  have hbdLw : ∀ s, w s L = 0 := by
    intro s
    simp [w, hbdL s]

  have hzero := wave_zero_of_zero_data_Icc w wt wx wtt wxt wtx wxx L Mw hL
    hW.hu_t hW.hut hW.hux hW.hut_x hW.hux_x
    hW.hut_cont hW.hux_cont hW.hutt_cont hW.huxt_cont hW.hutx_cont hW.huxx_cont
    hW.hbound hW.hwave hW.hmixed hW.hbc0 hW.hbcL hinitw hvelw hux0w hbd0w hbdLw
  intro t x hx
  have h := hzero t x hx
  simpa [w] using sub_eq_zero.mp h

end GeneralRelativity
