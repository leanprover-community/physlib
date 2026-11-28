/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/

module

public import PhyslibAlpha.Relativity.General.Linearized.LinearizedChristoffel
public import PhyslibAlpha.Relativity.General.Linearized.LinearizedRiemann
public import PhyslibAlpha.Relativity.General.Linearized.LinearizedRicci
public import PhyslibAlpha.Relativity.General.Linearized.LinearizedEinstein
public import PhyslibAlpha.Relativity.General.Linearized.MinkowskiDalembertian
public import PhyslibAlpha.Relativity.General.Linearized.LorenzGauge
public import PhyslibAlpha.Relativity.General.Linearized.TTWave
public import PhyslibAlpha.Relativity.General.InitialData.WaveUniqueness3D

/-!

# Linearized Einstein equations in wave gauge

## i. Overview

The linearized-gravity module proves that, in Lorenz gauge, the linearized
Einstein tensor is `-(1/2) □ h̄`.  This file records the resulting wave-gauge
interface explicitly: a perturbation is a linearized vacuum solution when it is
`C²`, satisfies the gauge condition near the point, and solves the component
wave equations `□ h̄_{ij} = 0`.  Perturbations are bundled as the
`MetricPerturbation`, whose symmetry is part of the structure.

This is the coordinate-level starting point for the linearized Einstein layer;
it is not a manifold-level derivation of the linearized equations.

## ii. Key results

- `WaveGaugePerturbation` : the wave-gauge form of the linearized vacuum
  equations at a point.
- `ttWave_waveGauge` : the transverse-traceless plane wave is a wave-gauge
  perturbation.
- `linearizedEinstein_eq_zero_of_waveGauge` : a wave-gauge perturbation solves
  the linearized vacuum equations `G^{(1)}_{ij} = 0`.

## iii. Table of contents

- A. Wave-gauge perturbations

## iv. References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019,
  Ch. 7. [ref: Carroll1997]
* R. M. Wald, *General Relativity*, University of Chicago Press, 1984, Ch. 7.
  [ref: wald_1984_general_relativity]

-/

@[expose] public section

open scoped Topology

namespace GeneralRelativity

namespace Linearized

/-! ## A. Wave-gauge perturbations -/

/-- A metric perturbation satisfying the wave-gauge form of the linearized
vacuum equations at a point. -/
structure WaveGaugePerturbation (P : MetricPerturbation) (x : Fin 4 → ℝ) : Prop where
  /-- Every component is `C²` at the point. -/
  smooth : P.IsC2At x
  /-- The Lorenz gauge condition holds on a neighborhood. -/
  gauge : ∀ᶠ y in nhds x, ∀ k : Fin 4, IsLorenzGauge P y k
  /-- The trace-reversed perturbation solves the component wave equations. -/
  wave : ∀ i j : Fin 4, minkowskiDalembertian (fun y => P.traceReversed.h y i j) x = 0

/-- A component of a plane-wave profile `f(t-z)` is `C²` when `f` is. -/
private lemma contDiffAt_waveProfile
    (c : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x : Fin 4 → ℝ) :
    ContDiffAt ℝ 2 (fun y : Fin 4 → ℝ => c * f (y 0 - y 3)) x := by
  have hlin : ContDiff ℝ 2 (fun y : Fin 4 → ℝ => y 0 - y 3) :=
    (contDiff_pi.mp (contDiff_id (𝕜 := ℝ) (E := Fin 4 → ℝ)) 0).sub
      (contDiff_pi.mp (contDiff_id (𝕜 := ℝ) (E := Fin 4 → ℝ)) 3)
  exact contDiffAt_const.mul ((hf.comp hlin).contDiffAt)

/-- The transverse-traceless plane wave has `C²` components. -/
lemma ttWave_isC2At
    (hPlus hCross : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x : Fin 4 → ℝ) :
    (ttWave hPlus hCross f).IsC2At x := fun i j => by
  fin_cases i <;> fin_cases j <;> simp only [ttWave] <;> norm_num
  all_goals first
    | exact contDiffAt_const
    | exact contDiffAt_waveProfile hPlus f hf x
    | exact (contDiffAt_waveProfile hPlus f hf x).neg
    | exact contDiffAt_waveProfile hCross f hf x

/-- The transverse-traceless plane wave is a wave-gauge perturbation. -/
lemma ttWave_waveGauge
    (hPlus hCross : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x : Fin 4 → ℝ) :
    WaveGaugePerturbation (ttWave hPlus hCross f) x := by
  have hlz : ∀ᶠ y in nhds x, ∀ k : Fin 4,
      IsLorenzGauge (ttWave hPlus hCross f) y k :=
    Filter.Eventually.of_forall fun y k => ttWave_lorenz_gauge hPlus hCross f y k
  refine { smooth := ttWave_isC2At hPlus hCross f hf x, gauge := hlz, wave := ?_ }
  intro i j
  have hG := ttWave_linearizedEinstein_zero hPlus hCross f hf x i j
  rw [linearizedEinstein_lorenz_gauge (ttWave hPlus hCross f) x
    (ttWave_isC2At hPlus hCross f hf x) hlz i j] at hG
  linarith

/-- A wave-gauge perturbation is a linearized vacuum solution:
`G^{(1)}_{ij} = 0`. -/
lemma linearizedEinstein_eq_zero_of_waveGauge
    (P : MetricPerturbation) (x : Fin 4 → ℝ)
    (S : WaveGaugePerturbation P x) (i j : Fin 4) :
    linearizedEinstein P x i j = 0 := by
  rw [linearizedEinstein_lorenz_gauge P x S.smooth S.gauge i j]
  simp [S.wave i j]

end Linearized

end GeneralRelativity