/-
Copyright (c) 2026 Alex Vergara Gil.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/

module

public import PhyslibAlpha.Relativity.General.InitialData.WaveEnergy

/-!

# General-data uniqueness for the one-dimensional wave equation

## i. Overview

The energy argument proves uniqueness for zero data.  Two solutions with the
same Cauchy data have a difference with zero data, so the zero-data theorem
applies.  This file bundles the regularity needed for that argument and proves
the resulting general-data uniqueness theorem.


## ii. Key results

- `WaveSolutionOn`
- `WaveSolutionOn.sub` : the difference of two regular solutions is a regular solution.
- `wave_unique_of_same_data`

## iii. Table of contents

- A. Uniqueness for the one-dimensional problem

## iv. References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, §2.4. [ref: Evans2010PDE]
-/
@[expose] public section

/-! ## A. Uniqueness for the one-dimensional problem -/

open scoped Interval Topology
open MeasureTheory

namespace GeneralRelativity

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
