/-
Copyright (c) 2026 Alex Vergara Gil.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.InitialData.SpaceChart
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!

# Energy and energy conservation for the three-dimensional wave equation

## i. Overview

This file defines the energy

  E(t) = 1/2 ∫_box (u_t(t,x)^2 + ∑ i, (∂ᵢu(t,x))^2) dx

for a field on a spatial box in `Fin 3 → ℝ`, proves its derivative by
differentiating under the box integral, identifies that derivative with the
divergence of the flux `u_t ∇u`, and applies the box divergence theorem.  The
divergence identity is an explicit hypothesis in Section B and is derived from
`u_tt = Δu` and the mixed-partial symmetry in Section C.

## ii. Key results

- `waveEnergy3D` : the energy integral of a wave in three space dimensions.
- `hasDerivAt_waveEnergy3D` : its time derivative, the divergence of the energy
  flux.
- `waveEnergy3D_eq_initial_of_divergence` : conservation when the flux
  divergence vanishes, by the divergence theorem.
- `waveFlux3D` : the energy flux `u_t ∇u`.
- `waveEnergy3D_eq_initial_of_wave` : conservation for a solution of the
  three-dimensional wave equation.
- `waveEnergy3DIntegrand_nonneg` : the energy density is nonnegative.
- `WaveSolution3D` : the regularity and boundary data used by the energy method.
- `WaveSolution3D.sub` : the difference of two regular solutions is a regular solution.
- `wave_unique3D_of_same_data` : uniqueness for the 3D wave Cauchy problem.

## iii. Table of contents

- A. The three-dimensional wave energy
- B. Conservation from a divergence identity
- C. The wave energy of a solution
- D. Uniqueness for the three-dimensional problem

## iv. References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, §2.4. [ref: Evans2010PDE]
-/
@[expose] public section

open MeasureTheory BoxIntegral
open scoped Topology

namespace GeneralRelativity

/-! ## A. The three-dimensional wave energy -/

/-- The energy density `u_t² + ∑ᵢ (∂ᵢu)²` on a spatial box. -/
noncomputable def waveEnergy3DIntegrand
    (ut : SpaceChart → ℝ) (grad : SpaceChart → SpaceChart) (x : SpaceChart) : ℝ :=
  ut x ^ 2 + ∑ i : Fin 3, grad x i ^ 2

/-- The energy on a spatial box. -/
noncomputable def waveEnergy3D
    (ut : ℝ → SpaceChart → ℝ) (grad : ℝ → SpaceChart → SpaceChart)
    (I : Box (Fin 3)) (t : ℝ) : ℝ :=
  (1 / 2) * ∫ x in Box.Icc I, waveEnergy3DIntegrand (ut t) (grad t) x

/-- The time derivative of the energy density. -/
noncomputable def waveEnergy3DDerivIntegrand
    (ut utt : ℝ → SpaceChart → ℝ) (grad gradt : ℝ → SpaceChart → SpaceChart)
    (t : ℝ) (x : SpaceChart) : ℝ :=
  2 * ut t x * utt t x + ∑ i : Fin 3, 2 * (grad t x i * gradt t x i)

lemma continuous_waveEnergy3DIntegrand_section
    (ut : ℝ → SpaceChart → ℝ) (grad : ℝ → SpaceChart → SpaceChart)
    (hut : Continuous (Function.uncurry ut))
    (hgrad : Continuous (Function.uncurry grad)) (t : ℝ) :
    Continuous (fun x : SpaceChart => waveEnergy3DIntegrand (ut t) (grad t) x) := by
  have h1 : Continuous (fun x : SpaceChart => ut t x) :=
    hut.comp (continuous_const.prodMk continuous_id)
  have h2 : Continuous (fun x : SpaceChart => grad t x) :=
    hgrad.comp (continuous_const.prodMk continuous_id)
  unfold waveEnergy3DIntegrand
  exact (h1.pow 2).add
    (continuous_finsetSum Finset.univ fun i _ =>
      ((continuous_apply i).comp h2).pow 2)

lemma continuous_waveEnergy3DDerivIntegrand_section
    (ut utt : ℝ → SpaceChart → ℝ) (grad gradt : ℝ → SpaceChart → SpaceChart)
    (hut : Continuous (Function.uncurry ut))
    (hutt : Continuous (Function.uncurry utt))
    (hgrad : Continuous (Function.uncurry grad))
    (hgradt : Continuous (Function.uncurry gradt)) (t : ℝ) :
    Continuous (fun x : SpaceChart => waveEnergy3DDerivIntegrand ut utt grad gradt t x) := by
  have h1 : Continuous (fun x : SpaceChart => ut t x) :=
    hut.comp (continuous_const.prodMk continuous_id)
  have h2 : Continuous (fun x : SpaceChart => utt t x) :=
    hutt.comp (continuous_const.prodMk continuous_id)
  have h3 : Continuous (fun x : SpaceChart => grad t x) :=
    hgrad.comp (continuous_const.prodMk continuous_id)
  have h4 : Continuous (fun x : SpaceChart => gradt t x) :=
    hgradt.comp (continuous_const.prodMk continuous_id)
  unfold waveEnergy3DDerivIntegrand
  refine ((continuous_const.mul h1).mul h2).add ?_
  exact continuous_finsetSum Finset.univ fun i _ =>
    continuous_const.mul (((continuous_apply i).comp h3).mul ((continuous_apply i).comp h4))

lemma hasDerivAt_waveEnergy3DIntegrand
    (ut utt : ℝ → SpaceChart → ℝ) (grad gradt : ℝ → SpaceChart → SpaceChart)
    (hut : ∀ t x, HasDerivAt (fun s : ℝ => ut s x) (utt t x) t)
    (hgrad : ∀ t x, HasDerivAt (fun s : ℝ => grad s x) (gradt t x) t)
    (t : ℝ) (x : SpaceChart) :
    HasDerivAt (fun s : ℝ => waveEnergy3DIntegrand (ut s) (grad s) x)
      (waveEnergy3DDerivIntegrand ut utt grad gradt t x) t := by
  unfold waveEnergy3DIntegrand waveEnergy3DDerivIntegrand
  have h1 : HasDerivAt (fun s : ℝ => ut s x ^ 2) (2 * ut t x * utt t x) t := by
    have h := (hut t x).mul (hut t x)
    convert h using 1
    · funext y
      simp [pow_two]
    · ring
  have h2 : HasDerivAt (fun s : ℝ => ∑ i : Fin 3, grad s x i ^ 2)
      (∑ i : Fin 3, 2 * (grad t x i * gradt t x i)) t := by
    refine HasDerivAt.fun_sum ?_
    intro i _
    have hdi : HasDerivAt (fun s : ℝ => grad s x i) (gradt t x i) t := by
      have hcomp := (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt t (hgrad t x)
      simpa [Function.comp_def, ContinuousLinearMap.proj_apply] using hcomp
    have hp := hdi.mul hdi
    convert hp using 1
    · funext y
      simp [pow_two]
    · ring
  exact h1.add h2

/-- Differentiation of the 3D wave energy under the box integral.  The bound
`M` is a global bound on the differentiated energy density. -/
lemma hasDerivAt_waveEnergy3D
    (ut utt : ℝ → SpaceChart → ℝ) (grad gradt : ℝ → SpaceChart → SpaceChart)
    (I : Box (Fin 3)) (t M : ℝ)
    (hut : ∀ s x, HasDerivAt (fun s : ℝ => ut s x) (utt s x) s)
    (hgrad : ∀ s x, HasDerivAt (fun s : ℝ => grad s x) (gradt s x) s)
    (hut_cont : Continuous (Function.uncurry ut))
    (hgrad_cont : Continuous (Function.uncurry grad))
    (hutt_cont : Continuous (Function.uncurry utt))
    (hgradt_cont : Continuous (Function.uncurry gradt))
    (hbound : ∀ s x, ‖waveEnergy3DDerivIntegrand ut utt grad gradt s x‖ ≤ M) :
    HasDerivAt (waveEnergy3D ut grad I)
      ((1 / 2) * ∫ x in Box.Icc I,
        waveEnergy3DDerivIntegrand ut utt grad gradt t x) t := by
  have hF_meas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun x : SpaceChart => waveEnergy3DIntegrand (ut s) (grad s) x)
        (volume.restrict (Box.Icc I)) := by
    filter_upwards with s
    exact (continuous_waveEnergy3DIntegrand_section ut grad hut_cont hgrad_cont s)
      |>.aestronglyMeasurable
  have hF_int : Integrable
      (fun x : SpaceChart => waveEnergy3DIntegrand (ut t) (grad t) x)
      (volume.restrict (Box.Icc I)) :=
    (continuous_waveEnergy3DIntegrand_section ut grad hut_cont hgrad_cont t)
      |>.continuousOn.integrableOn_compact I.isCompact_Icc
  have hF'_meas : AEStronglyMeasurable
      (fun x : SpaceChart => waveEnergy3DDerivIntegrand ut utt grad gradt t x)
      (volume.restrict (Box.Icc I)) :=
    (continuous_waveEnergy3DDerivIntegrand_section ut utt grad gradt
      hut_cont hutt_cont hgrad_cont hgradt_cont t)
      |>.aestronglyMeasurable
  have hbound_ae : ∀ᵐ x ∂(volume.restrict (Box.Icc I)),
      ∀ s : ℝ, s ∈ (Set.univ : Set ℝ) →
        ‖waveEnergy3DDerivIntegrand ut utt grad gradt s x‖ ≤ (fun _ : SpaceChart => M) x := by
    filter_upwards with x s hs
    exact hbound s x
  have hbound_int : Integrable (fun _ : SpaceChart => M) (volume.restrict (Box.Icc I)) :=
    integrableOn_const (μ := volume) (s := Box.Icc I) (C := M)
      I.isCompact_Icc.measure_lt_top.ne (by finiteness)
  have h_diff : ∀ᵐ x ∂(volume.restrict (Box.Icc I)),
      ∀ s : ℝ, s ∈ (Set.univ : Set ℝ) →
        HasDerivAt (fun s : ℝ => waveEnergy3DIntegrand (ut s) (grad s) x)
          (waveEnergy3DDerivIntegrand ut utt grad gradt s x) s := by
    filter_upwards with x s hs
    exact hasDerivAt_waveEnergy3DIntegrand
      (ut := ut) (utt := utt) (grad := grad) (gradt := gradt) hut hgrad s x
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => waveEnergy3DIntegrand (ut s) (grad s) x)
    (F' := fun s x => waveEnergy3DDerivIntegrand ut utt grad gradt s x)
    (x₀ := t) (s := Set.univ) (bound := fun _ : SpaceChart => M)
    (by simp) hF_meas hF_int hF'_meas hbound_ae hbound_int h_diff).2
  convert h.const_mul (1 / 2 : ℝ) using 1
  funext y
  simp [waveEnergy3D]

/-! ## B. Conservation from a divergence identity -/

/-- **3D energy conservation from a divergence identity.**  If the
differentiated energy density is twice the divergence of `F`, and `F` has zero
normal flux on every face, then the box energy is constant in time.  The
divergence identity is an explicit hypothesis, not a consequence claimed here. -/
lemma waveEnergy3D_eq_initial_of_divergence
    (ut utt : ℝ → SpaceChart → ℝ) (grad gradt : ℝ → SpaceChart → SpaceChart)
    (F : ℝ → SpaceChart → SpaceChart) (F' : ℝ → SpaceChart → SpaceChart →L[ℝ] SpaceChart)
    (I : Box (Fin 3)) (M : ℝ)
    (hut : ∀ s x, HasDerivAt (fun s : ℝ => ut s x) (utt s x) s)
    (hgrad : ∀ s x, HasDerivAt (fun s : ℝ => grad s x) (gradt s x) s)
    (hut_cont : Continuous (Function.uncurry ut))
    (hgrad_cont : Continuous (Function.uncurry grad))
    (hutt_cont : Continuous (Function.uncurry utt))
    (hgradt_cont : Continuous (Function.uncurry gradt))
    (hbound : ∀ s x, ‖waveEnergy3DDerivIntegrand ut utt grad gradt s x‖ ≤ M)
    (hF_cont : ∀ s, ContinuousOn (F s) (Box.Icc I))
    (hF_deriv : ∀ s, ∀ x ∈ Box.Ioo I, HasFDerivAt (F s) (F' s x) x)
    (hdiv_int : ∀ s, IntegrableOn
      (fun x => ∑ i, F' s x (Pi.single i 1) i) (Box.Icc I))
    (hface_upper : ∀ (s : ℝ) (i : Fin 3),
      (∫ x in Box.Icc (I.face i), F s (i.insertNth (I.upper i) x) i) = 0)
    (hface_lower : ∀ (s : ℝ) (i : Fin 3),
      (∫ x in Box.Icc (I.face i), F s (i.insertNth (I.lower i) x) i) = 0)
    (hdiv : ∀ s x,
      (∑ i, F' s x (Pi.single i 1) i) =
        (1 / 2) * waveEnergy3DDerivIntegrand ut utt grad gradt s x) :
    ∀ t, waveEnergy3D ut grad I t = waveEnergy3D ut grad I 0 := by
  have hzero : ∀ s, HasDerivAt (waveEnergy3D ut grad I) 0 s := by
    intro s
    have hderiv := hasDerivAt_waveEnergy3D ut utt grad gradt I s M
      hut hgrad hut_cont hgrad_cont hutt_cont hgradt_cont hbound
    have hdivzero := integral_divergence_box_eq_zero I (F s) (F' s)
      (hF_cont s) (hF_deriv s) (hdiv_int s) (hface_upper s) (hface_lower s)
    have hEq : (∫ x in Box.Icc I, ∑ i, F' s x (Pi.single i 1) i) =
        ∫ x in Box.Icc I, (1 / 2) * waveEnergy3DDerivIntegrand ut utt grad gradt s x := by
      congr 1
      funext x
      exact hdiv s x
    rw [hEq, integral_const_mul] at hdivzero
    have hIntZero :
        (∫ x in Box.Icc I, waveEnergy3DDerivIntegrand ut utt grad gradt s x) = 0 := by
      nlinarith
    rw [hIntZero] at hderiv
    simpa using hderiv
  have hderiv : ∀ s, deriv (waveEnergy3D ut grad I) s = 0 := fun s => (hzero s).deriv
  intro t
  exact (is_const_of_deriv_eq_zero (fun s => (hzero s).differentiableAt) hderiv 0 t).symm

/-! ## C. The wave energy of a solution -/

/-- The energy flux `F = u_t ∇u`. -/
noncomputable def waveFlux3D
    (ut : ℝ → SpaceChart → ℝ) (grad : ℝ → SpaceChart → SpaceChart)
    (t : ℝ) (x : SpaceChart) : SpaceChart :=
  ut t x • grad t x

/-- A derivative of the energy flux, built from the spatial derivatives of
`u_t` and `∇u`. -/
noncomputable def waveFlux3DDeriv
    (ut : ℝ → SpaceChart → ℝ) (grad : ℝ → SpaceChart → SpaceChart)
    (Dut : ℝ → SpaceChart → SpaceChart →L[ℝ] ℝ)
    (Dgrad : ℝ → SpaceChart → SpaceChart →L[ℝ] SpaceChart)
    (t : ℝ) (x : SpaceChart) : SpaceChart →L[ℝ] SpaceChart :=
  (ut t x) • Dgrad t x + (Dut t x).smulRight (grad t x)

lemma hasFDerivAt_waveFlux3D
    (ut : ℝ → SpaceChart → ℝ) (grad : ℝ → SpaceChart → SpaceChart)
    (Dut : ℝ → SpaceChart → SpaceChart →L[ℝ] ℝ)
    (Dgrad : ℝ → SpaceChart → SpaceChart →L[ℝ] SpaceChart)
    (t : ℝ) (x : SpaceChart)
    (hut : HasFDerivAt (ut t) (Dut t x) x)
    (hgrad : HasFDerivAt (grad t) (Dgrad t x) x) :
    HasFDerivAt (waveFlux3D ut grad t) (waveFlux3DDeriv ut grad Dut Dgrad t x) x := by
  simpa [waveFlux3D, waveFlux3DDeriv] using hut.smul hgrad

/-- **3D wave energy conservation.**  Under the wave equation
`u_tt = Δu`, mixed-partial symmetry, homogeneous Dirichlet data and the stated
regularity, the box energy is constant in time. -/
lemma waveEnergy3D_eq_initial_of_wave
    (ut utt : ℝ → SpaceChart → ℝ) (grad gradt : ℝ → SpaceChart → SpaceChart)
    (Dut : ℝ → SpaceChart → SpaceChart →L[ℝ] ℝ)
    (Dgrad : ℝ → SpaceChart → SpaceChart →L[ℝ] SpaceChart)
    (lap : ℝ → SpaceChart → ℝ) (I : Box (Fin 3)) (M : ℝ)
    (hut : ∀ s x, HasDerivAt (fun s : ℝ => ut s x) (utt s x) s)
    (hgrad : ∀ s x, HasDerivAt (fun s : ℝ => grad s x) (gradt s x) s)
    (hut_cont : Continuous (Function.uncurry ut))
    (hgrad_cont : Continuous (Function.uncurry grad))
    (hutt_cont : Continuous (Function.uncurry utt))
    (hgradt_cont : Continuous (Function.uncurry gradt))
    (hbound : ∀ s x, ‖waveEnergy3DDerivIntegrand ut utt grad gradt s x‖ ≤ M)
    (hut_spatial : ∀ t x, HasFDerivAt (ut t) (Dut t x) x)
    (hgrad_spatial : ∀ t x, HasFDerivAt (grad t) (Dgrad t x) x)
    (hlap : ∀ t x, (∑ i : Fin 3, Dgrad t x (Pi.single i 1) i) = lap t x)
    (hgradut : ∀ (t : ℝ) (x : SpaceChart) (i : Fin 3),
      Dut t x (Pi.single i 1) = gradt t x i)
    (hwave : ∀ t x, utt t x = lap t x)
    (hdiv_int : ∀ s, IntegrableOn
      (fun x => ∑ i, waveFlux3DDeriv ut grad Dut Dgrad s x (Pi.single i 1) i)
      (Box.Icc I))
    (hut_face_upper : ∀ (s : ℝ) (i : Fin 3) (y : Fin 2 → ℝ),
      ut s (i.insertNth (I.upper i) y) = 0)
    (hut_face_lower : ∀ (s : ℝ) (i : Fin 3) (y : Fin 2 → ℝ),
      ut s (i.insertNth (I.lower i) y) = 0) :
    ∀ t, waveEnergy3D ut grad I t = waveEnergy3D ut grad I 0 := by
  have hF_cont : ∀ s, ContinuousOn (waveFlux3D ut grad s) (Box.Icc I) := by
    intro s
    have h1 : Continuous (fun x : SpaceChart => ut s x) :=
      hut_cont.comp (continuous_const.prodMk continuous_id)
    have h2 : Continuous (fun x : SpaceChart => grad s x) :=
      hgrad_cont.comp (continuous_const.prodMk continuous_id)
    exact (h1.smul h2).continuousOn
  have hF_deriv : ∀ s, ∀ x ∈ Box.Ioo I,
      HasFDerivAt (waveFlux3D ut grad s) (waveFlux3DDeriv ut grad Dut Dgrad s x) x := by
    intro s x hx
    exact hasFDerivAt_waveFlux3D ut grad Dut Dgrad s x
      (hut_spatial s x) (hgrad_spatial s x)
  have hface_upper : ∀ (s : ℝ) (i : Fin 3),
      (∫ y in Box.Icc (I.face i), waveFlux3D ut grad s (i.insertNth (I.upper i) y) i) = 0 := by
    intro s i
    simp [waveFlux3D, hut_face_upper s i]
  have hface_lower : ∀ (s : ℝ) (i : Fin 3),
      (∫ y in Box.Icc (I.face i), waveFlux3D ut grad s (i.insertNth (I.lower i) y) i) = 0 := by
    intro s i
    simp [waveFlux3D, hut_face_lower s i]
  have hdiv : ∀ s x,
      (∑ i : Fin 3, waveFlux3DDeriv ut grad Dut Dgrad s x (Pi.single i 1) i) =
        (1 / 2) * waveEnergy3DDerivIntegrand ut utt grad gradt s x := by
    intro s x
    have hleft : (∑ i : Fin 3, ut s x * (Dgrad s x (Pi.single i 1) i)) =
        ut s x * lap s x := by
      rw [← Finset.mul_sum, hlap s x]
    have hsum1 : (∑ i : Fin 3, gradt s x i * grad s x i) =
        ∑ i : Fin 3, grad s x i * gradt s x i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hsum3 : (∑ i : Fin 3, 2 * (grad s x i * gradt s x i)) =
        2 * ∑ i : Fin 3, grad s x i * gradt s x i := by
      rw [Finset.mul_sum]
    simp [waveFlux3DDeriv, waveEnergy3DDerivIntegrand, hgradut s x,
      Finset.sum_add_distrib, hleft, hwave s x, hsum1]
    rw [hsum3]
    ring
  exact waveEnergy3D_eq_initial_of_divergence ut utt grad gradt
    (waveFlux3D ut grad) (waveFlux3DDeriv ut grad Dut Dgrad) I M
    hut hgrad hut_cont hgrad_cont hutt_cont hgradt_cont hbound
    hF_cont hF_deriv hdiv_int hface_upper hface_lower hdiv

/-- The 3D energy density is nonnegative. -/
lemma waveEnergy3DIntegrand_nonneg
    (ut : SpaceChart → ℝ) (grad : SpaceChart → SpaceChart) (x : SpaceChart) :
    0 ≤ waveEnergy3DIntegrand ut grad x := by
  unfold waveEnergy3DIntegrand
  exact add_nonneg (sq_nonneg (ut x))
    (Finset.sum_nonneg fun i _ => sq_nonneg (grad x i))

/-- **Zero box energy gives zero pointwise data.**  If the energy on a box
vanishes, then both `u_t` and `∇u` vanish at every interior point. -/
lemma eq_zero_of_waveEnergy3D_eq_zero
    (ut : ℝ → SpaceChart → ℝ) (grad : ℝ → SpaceChart → SpaceChart)
    {I : Box (Fin 3)} {t : ℝ}
    (hut_cont : Continuous (Function.uncurry ut))
    (hgrad_cont : Continuous (Function.uncurry grad))
    (hE : waveEnergy3D ut grad I t = 0) :
    ∀ x ∈ Box.Ioo I, ut t x = 0 ∧ grad t x = 0 := by
  have hInt :
      (∫ x in Box.Icc I, waveEnergy3DIntegrand (ut t) (grad t) x) = 0 := by
    have h := hE
    unfold waveEnergy3D at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have hcont : Continuous
      (fun x : SpaceChart => waveEnergy3DIntegrand (ut t) (grad t) x) :=
    continuous_waveEnergy3DIntegrand_section ut grad hut_cont hgrad_cont t
  have hIntble : Integrable
      (fun x : SpaceChart => waveEnergy3DIntegrand (ut t) (grad t) x)
      (volume.restrict (Box.Icc I)) :=
    hcont.continuousOn.integrableOn_compact I.isCompact_Icc
  have hnonneg : ∀ x : SpaceChart,
      0 ≤ waveEnergy3DIntegrand (ut t) (grad t) x :=
    fun x => waveEnergy3DIntegrand_nonneg (ut t) (grad t) x
  have hAE : (fun x : SpaceChart => waveEnergy3DIntegrand (ut t) (grad t) x)
      =ᵐ[volume.restrict (Box.Icc I)] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hIntble).mp hInt
  have hAEIoo : (fun x : SpaceChart => waveEnergy3DIntegrand (ut t) (grad t) x)
      =ᵐ[volume.restrict (Box.Ioo I)] 0 :=
    ae_restrict_of_ae_restrict_of_subset I.Ioo_subset_Icc hAE
  have hIoo_open : IsOpen (Box.Ioo I) := by
    change IsOpen (Set.univ.pi fun i : Fin 3 =>
      Set.Ioo (I.lower i) (I.upper i))
    exact isOpen_set_pi Set.finite_univ fun i (_ : i ∈ Set.univ) => isOpen_Ioo
  have hEqOn : Set.EqOn (fun x : SpaceChart =>
      waveEnergy3DIntegrand (ut t) (grad t) x) 0 (Box.Ioo I) :=
    Measure.eqOn_open_of_ae_eq hAEIoo hIoo_open hcont.continuousOn
      continuousOn_const
  intro x hx
  have hx0 : waveEnergy3DIntegrand (ut t) (grad t) x = 0 := hEqOn hx
  have hsum_nonneg : 0 ≤ ∑ i : Fin 3, grad t x i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (grad t x i)
  have hsq : ut t x ^ 2 = 0 := by
    unfold waveEnergy3DIntegrand at hx0
    nlinarith [sq_nonneg (ut t x), hsum_nonneg]
  have hgsum : (∑ i : Fin 3, grad t x i ^ 2) = 0 := by
    unfold waveEnergy3DIntegrand at hx0
    nlinarith [sq_nonneg (ut t x), hsum_nonneg]
  constructor
  · exact sq_eq_zero_iff.mp hsq
  · funext i
    have hi : grad t x i ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (grad t x j))).mp hgsum i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hi

/-- The energy at time zero vanishes when the initial velocity and the initial
spatial gradient vanish. -/
lemma waveEnergy3D_eq_zero_initial
    (ut : ℝ → SpaceChart → ℝ) (grad : ℝ → SpaceChart → SpaceChart) (I : Box (Fin 3))
    (hut0 : ∀ x, ut 0 x = 0) (hgrad0 : ∀ x i, grad 0 x i = 0) :
    waveEnergy3D ut grad I 0 = 0 := by
  unfold waveEnergy3D waveEnergy3DIntegrand
  simp [hut0, hgrad0]

/-! ## D. Uniqueness for the three-dimensional problem -/

/-- A regular solution of the 3D linear wave equation on a spatial box, with the
derivative fields and boundary conditions used by the energy method.  `M` bounds
the differentiated energy density. -/
structure WaveSolution3D
    (u ut : ℝ → SpaceChart → ℝ) (grad : ℝ → SpaceChart → SpaceChart)
    (utt : ℝ → SpaceChart → ℝ) (gradt : ℝ → SpaceChart → SpaceChart)
    (Dut : ℝ → SpaceChart → SpaceChart →L[ℝ] ℝ)
    (Dgrad : ℝ → SpaceChart → SpaceChart →L[ℝ] SpaceChart)
    (lap : ℝ → SpaceChart → ℝ) (I : Box (Fin 3)) (M : ℝ) : Prop where
  hu_t : ∀ s x, HasDerivAt (fun s : ℝ => u s x) (ut s x) s
  hu_face_upper : ∀ (s : ℝ) (i : Fin 3) (y : Fin 2 → ℝ),
    u s (i.insertNth (I.upper i) y) = 0
  hu_face_lower : ∀ (s : ℝ) (i : Fin 3) (y : Fin 2 → ℝ),
    u s (i.insertNth (I.lower i) y) = 0
  hut : ∀ s x, HasDerivAt (fun s : ℝ => ut s x) (utt s x) s
  hgrad : ∀ s x, HasDerivAt (fun s : ℝ => grad s x) (gradt s x) s
  hut_cont : Continuous (Function.uncurry ut)
  hgrad_cont : Continuous (Function.uncurry grad)
  hutt_cont : Continuous (Function.uncurry utt)
  hgradt_cont : Continuous (Function.uncurry gradt)
  hbound : ∀ s x, ‖waveEnergy3DDerivIntegrand ut utt grad gradt s x‖ ≤ M
  hut_spatial : ∀ t x, HasFDerivAt (ut t) (Dut t x) x
  hgrad_spatial : ∀ t x, HasFDerivAt (grad t) (Dgrad t x) x
  hlap : ∀ t x, (∑ i : Fin 3, Dgrad t x (Pi.single i 1) i) = lap t x
  hgradut : ∀ (t : ℝ) (x : SpaceChart) (i : Fin 3),
    Dut t x (Pi.single i 1) = gradt t x i
  hwave : ∀ t x, utt t x = lap t x
  hdiv_int : ∀ s, IntegrableOn
    (fun x => ∑ i, waveFlux3DDeriv ut grad Dut Dgrad s x (Pi.single i 1) i)
    (Box.Icc I)
  hut_face_upper : ∀ (s : ℝ) (i : Fin 3) (y : Fin 2 → ℝ),
    ut s (i.insertNth (I.upper i) y) = 0
  hut_face_lower : ∀ (s : ℝ) (i : Fin 3) (y : Fin 2 → ℝ),
    ut s (i.insertNth (I.lower i) y) = 0

/-- If the time derivative vanishes at every time, the field is constant in
time at that spatial point. -/
lemma u_eq_initial_of_ut_zero3D (u ut : ℝ → SpaceChart → ℝ) (x : SpaceChart)
    (hu_t : ∀ s, HasDerivAt (fun s : ℝ => u s x) (ut s x) s)
    (hut0 : ∀ s, ut s x = 0) :
    ∀ t, u t x = u 0 x := by
  have hderiv : ∀ s, deriv (fun s : ℝ => u s x) s = 0 := by
    intro s
    rw [(hu_t s).deriv, hut0 s]
  exact fun t => is_const_of_deriv_eq_zero
    (fun s => (hu_t s).differentiableAt) hderiv t 0

/-- A point of the closed box that is not interior lies on a face. -/
lemma exists_coord_eq_bound_of_mem_Icc_not_mem_Ioo
    {I : Box (Fin 3)} {x : SpaceChart}
    (hx : x ∈ Box.Icc I) (hxnot : x ∉ Box.Ioo I) :
    ∃ i : Fin 3, x i = I.lower i ∨ x i = I.upper i := by
  by_contra h
  apply hxnot
  change x ∈ Set.pi Set.univ
    (fun i : Fin 3 => Set.Ioo (I.lower i) (I.upper i))
  intro i _
  have hx' : x ∈ Box.Icc I := hx
  rw [Box.Icc_eq_pi] at hx'
  have hxi : I.lower i ≤ x i ∧ x i ≤ I.upper i :=
    hx' i (Set.mem_univ i)
  constructor
  · exact lt_of_le_of_ne hxi.1 (fun heq => h ⟨i, Or.inl heq.symm⟩)
  · exact lt_of_le_of_ne hxi.2 (fun heq => h ⟨i, Or.inr heq⟩)

/-- **Zero-data uniqueness in 3D.**  A regular wave solution with zero initial
position, velocity and gradient, and homogeneous Dirichlet data for the field,
vanishes on the closed box. -/
lemma wave_zero_of_zero_data3D
    (u ut : ℝ → SpaceChart → ℝ) (grad : ℝ → SpaceChart → SpaceChart)
    (utt : ℝ → SpaceChart → ℝ) (gradt : ℝ → SpaceChart → SpaceChart)
    (Dut : ℝ → SpaceChart → SpaceChart →L[ℝ] ℝ)
    (Dgrad : ℝ → SpaceChart → SpaceChart →L[ℝ] SpaceChart)
    (lap : ℝ → SpaceChart → ℝ) (I : Box (Fin 3)) (M : ℝ)
    (S : WaveSolution3D u ut grad utt gradt Dut Dgrad lap I M)
    (hinit : ∀ x, u 0 x = 0)
    (hvel : ∀ x, ut 0 x = 0)
    (hgrad0 : ∀ x i, grad 0 x i = 0) :
    ∀ t x, x ∈ Box.Icc I → u t x = 0 := by
  have hEconst : ∀ t, waveEnergy3D ut grad I t = waveEnergy3D ut grad I 0 :=
    waveEnergy3D_eq_initial_of_wave ut utt grad gradt Dut Dgrad lap I M
      S.hut S.hgrad S.hut_cont S.hgrad_cont S.hutt_cont S.hgradt_cont S.hbound
      S.hut_spatial S.hgrad_spatial S.hlap S.hgradut S.hwave S.hdiv_int
      S.hut_face_upper S.hut_face_lower
  have hE0 : waveEnergy3D ut grad I 0 = 0 :=
    waveEnergy3D_eq_zero_initial ut grad I hvel hgrad0
  have hzero_ut : ∀ t x, x ∈ Box.Ioo I → ut t x = 0 := by
    intro t x hx
    have hEt : waveEnergy3D ut grad I t = 0 := by
      rw [hEconst t, hE0]
    exact (eq_zero_of_waveEnergy3D_eq_zero ut grad
      S.hut_cont S.hgrad_cont hEt x hx).1
  intro t x hx
  by_cases hxIoo : x ∈ Box.Ioo I
  · have hconst := u_eq_initial_of_ut_zero3D u ut x
      (fun s => S.hu_t s x) (fun s => hzero_ut s x hxIoo) t
    rw [hconst, hinit x]
  · obtain ⟨i, hi | hi⟩ :=
      exists_coord_eq_bound_of_mem_Icc_not_mem_Ioo hx hxIoo
    · have hrepr : i.insertNth (I.lower i) (i.removeNth x) = x := by
        rw [← hi]
        exact Fin.insertNth_self_removeNth i x
      rw [← hrepr]
      exact S.hu_face_lower t i (i.removeNth x)
    · have hrepr : i.insertNth (I.upper i) (i.removeNth x) = x := by
        rw [← hi]
        exact Fin.insertNth_self_removeNth i x
      rw [← hrepr]
      exact S.hu_face_upper t i (i.removeNth x)

/-- The difference of two regular 3D solutions is a regular solution of the same
problem, with the difference of the derivative fields and the difference bound
`Mw` on the differentiated energy density. -/
lemma WaveSolution3D.sub
    (u v : ℝ → SpaceChart → ℝ) (ut vt : ℝ → SpaceChart → ℝ)
    (grad vgrad : ℝ → SpaceChart → SpaceChart)
    (utt vtt : ℝ → SpaceChart → ℝ) (gradt vgradt : ℝ → SpaceChart → SpaceChart)
    (Dut vDut : ℝ → SpaceChart → SpaceChart →L[ℝ] ℝ)
    (Dgrad vDgrad : ℝ → SpaceChart → SpaceChart →L[ℝ] SpaceChart)
    (lap vlap : ℝ → SpaceChart → ℝ) (I : Box (Fin 3)) (M N Mw : ℝ)
    (S : WaveSolution3D u ut grad utt gradt Dut Dgrad lap I M)
    (T : WaveSolution3D v vt vgrad vtt vgradt vDut vDgrad vlap I N)
    (hboundw : ∀ s x,
      ‖waveEnergy3DDerivIntegrand
        (fun s x => ut s x - vt s x)
        (fun s x => utt s x - vtt s x)
        (fun s x => grad s x - vgrad s x)
        (fun s x => gradt s x - vgradt s x) s x‖ ≤ Mw)
    (hdivw : ∀ s, IntegrableOn
      (fun x => ∑ i : Fin 3,
        waveFlux3DDeriv
          (fun s x => ut s x - vt s x)
          (fun s x => grad s x - vgrad s x)
          (fun s x => Dut s x - vDut s x)
          (fun s x => Dgrad s x - vDgrad s x)
          s x (Pi.single i 1) i) (Box.Icc I)) :
    WaveSolution3D
      (fun s x => u s x - v s x) (fun s x => ut s x - vt s x)
      (fun s x => grad s x - vgrad s x) (fun s x => utt s x - vtt s x)
      (fun s x => gradt s x - vgradt s x)
      (fun s x => Dut s x - vDut s x) (fun s x => Dgrad s x - vDgrad s x)
      (fun s x => lap s x - vlap s x) I Mw := by
  refine {
    hu_t := ?_
    hu_face_upper := ?_
    hu_face_lower := ?_
    hut := ?_
    hgrad := ?_
    hut_cont := ?_
    hgrad_cont := ?_
    hutt_cont := ?_
    hgradt_cont := ?_
    hbound := ?_
    hut_spatial := ?_
    hgrad_spatial := ?_
    hlap := ?_
    hgradut := ?_
    hwave := ?_
    hdiv_int := ?_
    hut_face_upper := ?_
    hut_face_lower := ?_ }
  · intro s x
    convert (S.hu_t s x).sub (T.hu_t s x) using 1
  · intro s i y
    simp [(S.hu_face_upper s i y), (T.hu_face_upper s i y)]
  · intro s i y
    simp [(S.hu_face_lower s i y), (T.hu_face_lower s i y)]
  · intro s x
    convert (S.hut s x).sub (T.hut s x) using 1
  · intro s x
    convert (S.hgrad s x).sub (T.hgrad s x) using 1
  · convert S.hut_cont.sub T.hut_cont using 1
    funext p
    simp [Function.uncurry, Pi.sub_apply]
  · convert S.hgrad_cont.sub T.hgrad_cont using 1
    funext p
    simp [Function.uncurry, Pi.sub_apply]
  · convert S.hutt_cont.sub T.hutt_cont using 1
    funext p
    simp [Function.uncurry, Pi.sub_apply]
  · convert S.hgradt_cont.sub T.hgradt_cont using 1
    funext p
    simp [Function.uncurry, Pi.sub_apply]
  · simpa using hboundw
  · intro t x
    convert (S.hut_spatial t x).sub (T.hut_spatial t x) using 1
  · intro t x
    convert (S.hgrad_spatial t x).sub (T.hgrad_spatial t x) using 1
  · intro t x
    have h1 := S.hlap t x
    have h2 := T.hlap t x
    change (∑ i : Fin 3,
      (Dgrad t x (Pi.single i 1) i - vDgrad t x (Pi.single i 1) i)) =
        lap t x - vlap t x
    rw [Finset.sum_sub_distrib, h1, h2]
  · intro t x i
    have h1 := S.hgradut t x i
    have h2 := T.hgradut t x i
    change Dut t x (Pi.single i 1) - vDut t x (Pi.single i 1) =
      gradt t x i - vgradt t x i
    rw [h1, h2]
  · intro t x
    simp [(S.hwave t x), (T.hwave t x)]
  · simpa using hdivw
  · intro s i y
    simp [(S.hut_face_upper s i y), (T.hut_face_upper s i y)]
  · intro s i y
    simp [(S.hut_face_lower s i y), (T.hut_face_lower s i y)]

/-- **General-data uniqueness in 3D.**  Two regular wave solutions with the same
initial position, velocity and spatial gradient, and the same homogeneous
Dirichlet data, agree on the closed box.  The proof applies the zero-data theorem
to their difference. -/
lemma wave_unique3D_of_same_data
    (u v : ℝ → SpaceChart → ℝ) (ut vt : ℝ → SpaceChart → ℝ)
    (grad vgrad : ℝ → SpaceChart → SpaceChart)
    (utt vtt : ℝ → SpaceChart → ℝ) (gradt vgradt : ℝ → SpaceChart → SpaceChart)
    (Dut vDut : ℝ → SpaceChart → SpaceChart →L[ℝ] ℝ)
    (Dgrad vDgrad : ℝ → SpaceChart → SpaceChart →L[ℝ] SpaceChart)
    (lap vlap : ℝ → SpaceChart → ℝ) (I : Box (Fin 3)) (M N Mw : ℝ)
    (S : WaveSolution3D u ut grad utt gradt Dut Dgrad lap I M)
    (T : WaveSolution3D v vt vgrad vtt vgradt vDut vDgrad vlap I N)
    (hboundw : ∀ s x,
      ‖waveEnergy3DDerivIntegrand
        (fun s x => ut s x - vt s x)
        (fun s x => utt s x - vtt s x)
        (fun s x => grad s x - vgrad s x)
        (fun s x => gradt s x - vgradt s x) s x‖ ≤ Mw)
    (hdivw : ∀ s, IntegrableOn
      (fun x => ∑ i : Fin 3,
        waveFlux3DDeriv
          (fun s x => ut s x - vt s x)
          (fun s x => grad s x - vgrad s x)
          (fun s x => Dut s x - vDut s x)
          (fun s x => Dgrad s x - vDgrad s x)
          s x (Pi.single i 1) i) (Box.Icc I))
    (hinit : ∀ x, u 0 x = v 0 x)
    (hvel : ∀ x, ut 0 x = vt 0 x)
    (hgrad0 : ∀ x i, grad 0 x i = vgrad 0 x i) :
    ∀ t x, x ∈ Box.Icc I → u t x = v t x := by
  let w : ℝ → SpaceChart → ℝ := fun s x => u s x - v s x
  let wt : ℝ → SpaceChart → ℝ := fun s x => ut s x - vt s x
  let wgrad : ℝ → SpaceChart → SpaceChart := fun s x => grad s x - vgrad s x

  have hW : WaveSolution3D w wt wgrad
      (fun s x => utt s x - vtt s x) (fun s x => gradt s x - vgradt s x)
      (fun s x => Dut s x - vDut s x) (fun s x => Dgrad s x - vDgrad s x)
      (fun s x => lap s x - vlap s x) I Mw :=
    WaveSolution3D.sub u v ut vt grad vgrad utt vtt gradt vgradt Dut vDut Dgrad vDgrad
      lap vlap I M N Mw S T hboundw hdivw
  have hzero := wave_zero_of_zero_data3D w wt wgrad
    (fun s x => utt s x - vtt s x) (fun s x => gradt s x - vgradt s x)
    (fun s x => Dut s x - vDut s x) (fun s x => Dgrad s x - vDgrad s x)
    (fun s x => lap s x - vlap s x) I Mw hW
    (by intro x; simp [w, hinit x])
    (by intro x; simp [wt, hvel x])
    (by intro x i; simp [wgrad, hgrad0 x i])
  intro t x hx
  have h := hzero t x hx
  simpa [w] using sub_eq_zero.mp h

end GeneralRelativity
