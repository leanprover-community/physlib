/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/

module

public import PhyslibAlpha.Relativity.General.InitialData.Divergence3D
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!

# Energy for the three-dimensional wave equation

## i. Overview

This file defines the energy

  E(t) = 1/2 ∫_box (u_t(t,x)^2 + ∑ i, (∂ᵢu(t,x))^2) dx

for a field on a spatial box in `Fin 3 → ℝ`, and proves its derivative by
differentiating under the box integral.  The remaining wave-specific step is to
identify this derivative with the divergence of `u_t ∇u` and apply the box
divergence theorem.


## ii. Key results

- `waveEnergy3D`
- `hasDerivAt_waveEnergy3D`

## iii. Table of contents

- A. The three-dimensional wave energy

## iv. References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, §2.4. [ref: Evans2010PDE]
-/
@[expose] public section

/-! ## A. The three-dimensional wave energy -/

open MeasureTheory BoxIntegral
open scoped Topology

namespace GeneralRelativity

/-- The energy density `u_t² + ∑ᵢ (∂ᵢu)²` on a spatial box. -/
noncomputable def waveEnergy3DIntegrand
    (ut : Space3 → ℝ) (grad : Space3 → Space3) (x : Space3) : ℝ :=
  ut x ^ 2 + ∑ i : Fin 3, grad x i ^ 2

/-- The energy on a spatial box. -/
noncomputable def waveEnergy3D
    (ut : ℝ → Space3 → ℝ) (grad : ℝ → Space3 → Space3)
    (I : Box (Fin 3)) (t : ℝ) : ℝ :=
  (1 / 2) * ∫ x in Box.Icc I, waveEnergy3DIntegrand (ut t) (grad t) x

/-- The time derivative of the energy density. -/
noncomputable def waveEnergy3DDerivIntegrand
    (ut utt : ℝ → Space3 → ℝ) (grad gradt : ℝ → Space3 → Space3)
    (t : ℝ) (x : Space3) : ℝ :=
  2 * ut t x * utt t x + ∑ i : Fin 3, 2 * (grad t x i * gradt t x i)

lemma continuous_waveEnergy3DIntegrand_section
    (ut : ℝ → Space3 → ℝ) (grad : ℝ → Space3 → Space3)
    (hut : Continuous (Function.uncurry ut))
    (hgrad : Continuous (Function.uncurry grad)) (t : ℝ) :
    Continuous (fun x : Space3 => waveEnergy3DIntegrand (ut t) (grad t) x) := by
  have h1 : Continuous (fun x : Space3 => ut t x) :=
    hut.comp (continuous_const.prodMk continuous_id)
  have h2 : Continuous (fun x : Space3 => grad t x) :=
    hgrad.comp (continuous_const.prodMk continuous_id)
  unfold waveEnergy3DIntegrand
  exact (h1.pow 2).add
    (continuous_finsetSum Finset.univ fun i _ =>
      ((continuous_apply i).comp h2).pow 2)

lemma continuous_waveEnergy3DDerivIntegrand_section
    (ut utt : ℝ → Space3 → ℝ) (grad gradt : ℝ → Space3 → Space3)
    (hut : Continuous (Function.uncurry ut))
    (hutt : Continuous (Function.uncurry utt))
    (hgrad : Continuous (Function.uncurry grad))
    (hgradt : Continuous (Function.uncurry gradt)) (t : ℝ) :
    Continuous (fun x : Space3 => waveEnergy3DDerivIntegrand ut utt grad gradt t x) := by
  have h1 : Continuous (fun x : Space3 => ut t x) :=
    hut.comp (continuous_const.prodMk continuous_id)
  have h2 : Continuous (fun x : Space3 => utt t x) :=
    hutt.comp (continuous_const.prodMk continuous_id)
  have h3 : Continuous (fun x : Space3 => grad t x) :=
    hgrad.comp (continuous_const.prodMk continuous_id)
  have h4 : Continuous (fun x : Space3 => gradt t x) :=
    hgradt.comp (continuous_const.prodMk continuous_id)
  unfold waveEnergy3DDerivIntegrand
  refine ((continuous_const.mul h1).mul h2).add ?_
  exact continuous_finsetSum Finset.univ fun i _ =>
    continuous_const.mul (((continuous_apply i).comp h3).mul ((continuous_apply i).comp h4))

lemma hasDerivAt_waveEnergy3DIntegrand
    (ut utt : ℝ → Space3 → ℝ) (grad gradt : ℝ → Space3 → Space3)
    (hut : ∀ t x, HasDerivAt (fun s : ℝ => ut s x) (utt t x) t)
    (hgrad : ∀ t x, HasDerivAt (fun s : ℝ => grad s x) (gradt t x) t)
    (t : ℝ) (x : Space3) :
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
    (ut utt : ℝ → Space3 → ℝ) (grad gradt : ℝ → Space3 → Space3)
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
      AEStronglyMeasurable (fun x : Space3 => waveEnergy3DIntegrand (ut s) (grad s) x)
        (volume.restrict (Box.Icc I)) := by
    filter_upwards with s
    exact (continuous_waveEnergy3DIntegrand_section ut grad hut_cont hgrad_cont s)
      |>.aestronglyMeasurable
  have hF_int : Integrable
      (fun x : Space3 => waveEnergy3DIntegrand (ut t) (grad t) x)
      (volume.restrict (Box.Icc I)) :=
    (continuous_waveEnergy3DIntegrand_section ut grad hut_cont hgrad_cont t)
      |>.continuousOn.integrableOn_compact I.isCompact_Icc
  have hF'_meas : AEStronglyMeasurable
      (fun x : Space3 => waveEnergy3DDerivIntegrand ut utt grad gradt t x)
      (volume.restrict (Box.Icc I)) :=
    (continuous_waveEnergy3DDerivIntegrand_section ut utt grad gradt
      hut_cont hutt_cont hgrad_cont hgradt_cont t)
      |>.aestronglyMeasurable
  have hbound_ae : ∀ᵐ x ∂(volume.restrict (Box.Icc I)),
      ∀ s : ℝ, s ∈ (Set.univ : Set ℝ) →
        ‖waveEnergy3DDerivIntegrand ut utt grad gradt s x‖ ≤ (fun _ : Space3 => M) x := by
    filter_upwards with x s hs
    exact hbound s x
  have hbound_int : Integrable (fun _ : Space3 => M) (volume.restrict (Box.Icc I)) :=
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
    (x₀ := t) (s := Set.univ) (bound := fun _ : Space3 => M)
    (by simp) hF_meas hF_int hF'_meas hbound_ae hbound_int h_diff).2
  convert h.const_mul (1 / 2 : ℝ) using 1
  funext y
  simp [waveEnergy3D]

end GeneralRelativity
