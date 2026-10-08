/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.MaxCurrentVariances
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
/-!

# The long chain limit of `C_Nava`

## i. Overview

In the maximal current state, `C_Nava` depends only on the number of sites `N`. As the chain
grows, `θ = π / (N + 1) → 0`, `(N + 1) sin θ → π` and `cos θ → 1`, so the closed form of
`C_Nava²` tends to `2 (π² / 6 - 1) = π² / 3 - 2`. Every long enough chain has
`C_Nava` close to `C_∞ = √(π² / 3 - 2) ≈ 1.1357`, which is strictly larger than one: the
uncertainty relation stays strict in the long chain limit.

## ii. Key results

- `cNavaSqForm` : the closed form of `C_Nava²` as a function of `n = N + 1`.
- `CNava_sq_eq_cNavaSqForm` : `C_Nava² = cNavaSqForm (N + 1)` for `N ≥ 2`.
- `tendsto_cNavaSqForm` : `cNavaSqForm n → π² / 3 - 2` as `n → ∞`.
- `tendsto_CNava` : `C_Nava → √(π² / 3 - 2)` along any family of chains with `N → ∞`.
- `one_lt_sqrt_pi_sq_div_three_sub_two` : `1 < √(π² / 3 - 2)`.

## iii. Table of contents

- A. The limit of the closed form
- B. The limit of `C_Nava`

## iv. References

* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]
-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open Filter Topology

/-!

## A. The limit of the closed form

-/

/-- The closed form of `C_Nava²` as a function of `n = N + 1`, written with `sinc`. -/
noncomputable def cNavaSqForm (n : ℝ) : ℝ :=
  2 * (1 - 2 / n) / Real.cos (Real.pi / n) ^ 2 *
    ((Real.pi ^ 2 * Real.sinc (Real.pi / n) ^ 2 + 2 * Real.sin (Real.pi / n) ^ 2) / 6 - 1)

/-- The closed form tends to `π² / 3 - 2` as `n → ∞`. -/
lemma tendsto_cNavaSqForm :
    Tendsto cNavaSqForm atTop (𝓝 (Real.pi ^ 2 / 3 - 2)) := by
  have hθ : Tendsto (fun n : ℝ => Real.pi / n) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop Real.pi
  have hratio : Tendsto (fun n : ℝ => 1 - 2 / n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_id.const_div_atTop (2 : ℝ))
  have hcos : Tendsto (fun n : ℝ => Real.cos (Real.pi / n) ^ 2) atTop (𝓝 1) := by
    simpa using (Real.continuous_cos.continuousAt.tendsto.comp hθ).pow 2
  have hsinc : Tendsto (fun n : ℝ => Real.sinc (Real.pi / n) ^ 2) atTop (𝓝 1) := by
    simpa using (Real.continuous_sinc.continuousAt.tendsto.comp hθ).pow 2
  have hsin : Tendsto (fun n : ℝ => Real.sin (Real.pi / n) ^ 2) atTop (𝓝 0) := by
    simpa using (Real.continuous_sin.continuousAt.tendsto.comp hθ).pow 2
  have h := (((tendsto_const_nhds (x := (2 : ℝ))).mul hratio).div hcos one_ne_zero).mul
    ((((tendsto_const_nhds (x := Real.pi ^ 2)).mul hsinc).add
      ((tendsto_const_nhds (x := (2 : ℝ))).mul hsin)).div_const 6 |>.sub_const 1)
  rw [show Real.pi ^ 2 / 3 - 2 = 2 * 1 / 1 * ((Real.pi ^ 2 * 1 + 2 * 0) / 6 - 1) by ring]
  exact h.congr fun n => by simp only [cNavaSqForm, Pi.div_apply]

/-- For `N ≥ 2`, `C_Nava²` is the closed form at `n = N + 1`. -/
lemma CNava_sq_eq_cNavaSqForm (T : TightBindingChain) (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    T.CNava ^ 2 = cNavaSqForm (T.N + 1) := by
  have hn : (T.N : ℝ) + 1 ≠ 0 := by positivity
  rw [T.CNava_sq_eq ht hN, cNavaSqForm, Real.sinc_of_ne_zero (div_ne_zero Real.pi_ne_zero hn)]
  field_simp
  ring

/-!

## B. The limit of `C_Nava`

-/

/-- **The long chain limit.** Along any family of chains whose number of sites tends to infinity,
the constant `C_Nava` of the maximal current state tends to `√(π² / 3 - 2)`. -/
theorem tendsto_CNava {ι : Type*} {l : Filter ι} (T : ι → TightBindingChain)
    (ht : ∀ i, (T i).t ≠ 0) (hN : Tendsto (fun i => (T i).N) l atTop) :
    Tendsto (fun i => (T i).CNava) l (𝓝 √(Real.pi ^ 2 / 3 - 2)) := by
  have hn : Tendsto (fun i => ((T i).N : ℝ) + 1) l atTop :=
    tendsto_atTop_add_const_right l 1 (tendsto_natCast_atTop_atTop.comp hN)
  refine ((Real.continuous_sqrt.tendsto _).comp (tendsto_cNavaSqForm.comp hn)).congr' ?_
  filter_upwards [hN.eventually_ge_atTop 2] with i hi
  rw [Function.comp_apply, Function.comp_apply, ← CNava_sq_eq_cNavaSqForm (T i) (ht i) hi,
    Real.sqrt_sq (by unfold CNava; positivity)]

/-- The limit `√(π² / 3 - 2)` is strictly larger than one, since `π > 3`. -/
lemma one_lt_sqrt_pi_sq_div_three_sub_two : 1 < √(Real.pi ^ 2 / 3 - 2) := by
  rw [Real.lt_sqrt zero_le_one]
  nlinarith [Real.pi_gt_three]

end TightBindingChain
end CondensedMatter
