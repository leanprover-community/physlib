/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/

module

public import PhyslibAlpha.Relativity.General.InitialData.WaveEnergy3DConservation
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!

# Energy conservation for the 3D linear wave equation

## i. Overview

This file instantiates the conditional 3D energy theorem with the physical flux
`F = u_t ∇u`.  The divergence identity

  div F = u_t Δu + ∇u · ∇u_t

is proved from the coordinate derivatives, the wave equation `u_tt = Δu`, and
the mixed-partial symmetry `∇u_t = (∇u)_t`.  Homogeneous Dirichlet data makes
the normal flux vanish on every face.


## ii. Key results

- `waveFlux3D`
- `waveEnergy3D_eq_initial_of_wave`
- `waveEnergy3DIntegrand_nonneg`

## iii. Table of contents

- A. The wave energy on a wave

## iv. References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, §2.4.
-/
@[expose] public section

/-! ## A. The wave energy on a wave -/

open MeasureTheory BoxIntegral
open scoped Topology

namespace GeneralRelativity

/-- The energy flux `F = u_t ∇u`. -/
noncomputable def waveFlux3D
    (ut : ℝ → Space3 → ℝ) (grad : ℝ → Space3 → Space3)
    (t : ℝ) (x : Space3) : Space3 :=
  ut t x • grad t x

/-- A derivative of the energy flux, built from the spatial derivatives of
`u_t` and `∇u`. -/
noncomputable def waveFlux3DDeriv
    (ut : ℝ → Space3 → ℝ) (grad : ℝ → Space3 → Space3)
    (Dut : ℝ → Space3 → Space3 →L[ℝ] ℝ)
    (Dgrad : ℝ → Space3 → Space3 →L[ℝ] Space3)
    (t : ℝ) (x : Space3) : Space3 →L[ℝ] Space3 :=
  (ut t x) • Dgrad t x + (Dut t x).smulRight (grad t x)

lemma hasFDerivAt_waveFlux3D
    (ut : ℝ → Space3 → ℝ) (grad : ℝ → Space3 → Space3)
    (Dut : ℝ → Space3 → Space3 →L[ℝ] ℝ)
    (Dgrad : ℝ → Space3 → Space3 →L[ℝ] Space3)
    (t : ℝ) (x : Space3)
    (hut : HasFDerivAt (ut t) (Dut t x) x)
    (hgrad : HasFDerivAt (grad t) (Dgrad t x) x) :
    HasFDerivAt (waveFlux3D ut grad t) (waveFlux3DDeriv ut grad Dut Dgrad t x) x := by
  simpa [waveFlux3D, waveFlux3DDeriv] using hut.smul hgrad

/-- **3D wave energy conservation.**  Under the wave equation
`u_tt = Δu`, mixed-partial symmetry, homogeneous Dirichlet data and the stated
regularity, the box energy is constant in time. -/
lemma waveEnergy3D_eq_initial_of_wave
    (ut utt : ℝ → Space3 → ℝ) (grad gradt : ℝ → Space3 → Space3)
    (Dut : ℝ → Space3 → Space3 →L[ℝ] ℝ)
    (Dgrad : ℝ → Space3 → Space3 →L[ℝ] Space3)
    (lap : ℝ → Space3 → ℝ) (I : Box (Fin 3)) (M : ℝ)
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
    (hgradut : ∀ (t : ℝ) (x : Space3) (i : Fin 3),
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
    have h1 : Continuous (fun x : Space3 => ut s x) :=
      hut_cont.comp (continuous_const.prodMk continuous_id)
    have h2 : Continuous (fun x : Space3 => grad s x) :=
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
    (ut : Space3 → ℝ) (grad : Space3 → Space3) (x : Space3) :
    0 ≤ waveEnergy3DIntegrand ut grad x := by
  unfold waveEnergy3DIntegrand
  exact add_nonneg (sq_nonneg (ut x))
    (Finset.sum_nonneg fun i _ => sq_nonneg (grad x i))

/-- **Zero box energy gives zero pointwise data.**  If the energy on a box
vanishes, then both `u_t` and `∇u` vanish at every interior point. -/
lemma eq_zero_of_waveEnergy3D_eq_zero
    (ut : ℝ → Space3 → ℝ) (grad : ℝ → Space3 → Space3)
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
      (fun x : Space3 => waveEnergy3DIntegrand (ut t) (grad t) x) :=
    continuous_waveEnergy3DIntegrand_section ut grad hut_cont hgrad_cont t
  have hIntble : Integrable
      (fun x : Space3 => waveEnergy3DIntegrand (ut t) (grad t) x)
      (volume.restrict (Box.Icc I)) :=
    hcont.continuousOn.integrableOn_compact I.isCompact_Icc
  have hnonneg : ∀ x : Space3,
      0 ≤ waveEnergy3DIntegrand (ut t) (grad t) x :=
    fun x => waveEnergy3DIntegrand_nonneg (ut t) (grad t) x
  have hAE : (fun x : Space3 => waveEnergy3DIntegrand (ut t) (grad t) x)
      =ᵐ[volume.restrict (Box.Icc I)] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hIntble).mp hInt
  have hAEIoo : (fun x : Space3 => waveEnergy3DIntegrand (ut t) (grad t) x)
      =ᵐ[volume.restrict (Box.Ioo I)] 0 :=
    ae_restrict_of_ae_restrict_of_subset I.Ioo_subset_Icc hAE
  have hIoo_open : IsOpen (Box.Ioo I) := by
    change IsOpen (Set.univ.pi fun i : Fin 3 =>
      Set.Ioo (I.lower i) (I.upper i))
    exact isOpen_set_pi Set.finite_univ fun i (_ : i ∈ Set.univ) => isOpen_Ioo
  have hEqOn : Set.EqOn (fun x : Space3 =>
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
    (ut : ℝ → Space3 → ℝ) (grad : ℝ → Space3 → Space3) (I : Box (Fin 3))
    (hut0 : ∀ x, ut 0 x = 0) (hgrad0 : ∀ x i, grad 0 x i = 0) :
    waveEnergy3D ut grad I 0 = 0 := by
  unfold waveEnergy3D waveEnergy3DIntegrand
  simp [hut0, hgrad0]

end GeneralRelativity
