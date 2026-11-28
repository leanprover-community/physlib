/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/

module

public import PhyslibAlpha.Relativity.General.InitialData.WaveEnergy3D

/-!

# Energy conservation for the 3D wave equation

## i. Overview

This file combines the differentiated 3D energy with the box divergence
theorem.  The theorem below is deliberately conditional: it assumes that the
energy derivative is twice the divergence of an explicit vector field and that
the normal flux vanishes.  The next analytic step is to derive the divergence
identity from `u_tt = Δu`; it is not assumed silently.


## ii. Key results

- `waveEnergy3D_eq_initial_of_divergence`

## iii. Table of contents

- A. Conservation of the three-dimensional wave energy

## iv. References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, §2.4. [ref: Evans2010PDE]
-/
@[expose] public section

/-! ## A. Conservation of the three-dimensional wave energy -/

open MeasureTheory BoxIntegral

namespace GeneralRelativity

/-- **3D energy conservation from a divergence identity.**  If the
differentiated energy density is twice the divergence of `F`, and `F` has zero
normal flux on every face, then the box energy is constant in time.  The
divergence identity is an explicit hypothesis, not a consequence claimed here. -/
lemma waveEnergy3D_eq_initial_of_divergence
    (ut utt : ℝ → Space3 → ℝ) (grad gradt : ℝ → Space3 → Space3)
    (F : ℝ → Space3 → Space3) (F' : ℝ → Space3 → Space3 →L[ℝ] Space3)
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

end GeneralRelativity
