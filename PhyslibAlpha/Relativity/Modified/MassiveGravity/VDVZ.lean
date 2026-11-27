/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import PhyslibAlpha.Relativity.Metrics.MetricTrace
public import PhyslibAlpha.Relativity.Metrics.Minkowski
public import PhyslibAlpha.Relativity.Modified.MassiveGravity.Basic
import Mathlib.Tactic.Ring

/-!

# The van Dam–Veltman–Zakharov (vDVZ) discontinuity

Propagator coupling discontinuity `4/3` for static sources and `3/4` light-deflection suppression in
the massless limit of Fierz–Pauli massive gravity.

## i. Overview

In the massless limit `m → 0` of Fierz–Pauli massive gravity, the helicity-0 mode remains coupled
to the trace of the stress-energy tensor with coefficient `1/3` instead of the General Relativity
factor `1/2`, producing the van Dam–Veltman–Zakharov (vDVZ) discontinuity between
`massivePropagatorCoupling` and `grPropagatorCoupling`.

## ii. Key results

- `staticSource` : static point-mass stress-energy tensor.
- `grPropagatorCoupling`, `massivePropagatorCoupling` : massless GR and massive spin-2 propagator
  residues using `MassiveGravityTheory` and `metricTrace minkowski`.
- `vdvz_static_ratio`, `vdvz_light_deflection_ratio` : static `4/3` enhancement and `3/4`
  light-bending discontinuity.

## iii. Table of contents

- A. The vDVZ propagator discontinuity

## iv. References

* Markus Fierz and Wolfgang Pauli, *On Relativistic Wave Equations for Particles of Arbitrary Spin
  in an Electromagnetic Field*, *Proceedings of the Royal Society of London. Series A* 173, pp.
  211-232 (1939), Sec. 2-3. [ref: FierzPauli1939]
* D. G. Boulware and S. Deser, *Can Gravitation Have a Finite Range?*, *Physical Review D* 6, pp.
  3368-3382 (1972), Sec. II. [ref: BoulwareDeser1972]
* H. van Dam and M. J. G. Veltman, *Massive and Massless Yang-Mills and Gravitational Fields*,
  *Nuclear Physics B* 22, pp. 397-411 (1970), Sec. 2-3. [ref: vanDamVeltman1970]
* V. I. Zakharov, *Linearized Gravitation Theory and the Graviton Mass*, *JETP Letters* 12, pp.
  312-314 (1970). [ref: Zakharov1970]
* Kurt Hinterbichler, *Theoretical Aspects of Massive Gravity*, *Reviews of Modern Physics* 84, pp.
  671-710 (2012), Sec. II.D (https://arxiv.org/pdf/1105.3735#page=6). [ref: Hinterbichler2012]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace MassiveGravity

/-!

## A. The vDVZ propagator discontinuity

Comparing the tensor structures of the massless spin-2 and `m → 0` massive Fierz–Pauli one-graviton
exchange amplitudes exhibits the discontinuous `4/3` static coupling and `3/4` light deflection.

-/

/-- Massless General Relativity spin-2 propagator residue contracted between two conserved
stress-energy tensors `T₁, T₂`: `T₁_{ab} T₂^{ab} - ½ T₁ T₂`. -/
noncomputable def grPropagatorCoupling (T1 T2 : Tensor2 4) : ℝ :=
  MassiveGravityTheory.generalRelativity.propagatorCoupling T1 T2

/-- Massive Fierz–Pauli spin-2 propagator residue in the `m → 0` limit contracted between two
conserved stress-energy tensors `T₁, T₂`, for a massive-gravity model `M` with trace coefficient
`M.c = 1/3`: `T₁_{ab} T₂^{ab} - ⅓ T₁ T₂`. -/
noncomputable def massivePropagatorCoupling (M : MassiveGravityTheory) (T1 T2 : Tensor2 4) : ℝ :=
  M.propagatorCoupling T1 T2

/-- Stress-energy tensor of a static non-relativistic mass density `ρ`: `T_{00} = ρ`, all other
components zero. -/
def staticSource (ρ : ℝ) : Tensor2 4 :=
  fun i j => if i = 0 ∧ j = 0 then ρ else 0

/-- The vDVZ static discontinuity: for two static non-relativistic sources `ρ₁, ρ₂`, the massive
graviton exchange amplitude is `4/3` times the massless General Relativity amplitude. -/
lemma vdvz_static_ratio (M : MassiveGravityTheory) (hM : M.c = 1 / 3) (ρ1 ρ2 : ℝ) :
    massivePropagatorCoupling M (staticSource ρ1) (staticSource ρ2) =
      (4 / 3) * grPropagatorCoupling (staticSource ρ1) (staticSource ρ2) := by
  simp only [massivePropagatorCoupling, grPropagatorCoupling,
    MassiveGravityTheory.propagatorCoupling, MassiveGravityTheory.generalRelativity, hM,
    metricTrace_minkowski, staticSource, Fin.sum_univ_four, minkowskiMetric4_apply]
  norm_num
  ring

/-- The vDVZ light-deflection discontinuity: for a null electromagnetic/light probe `Tlight`
(`metricTrace minkowski Tlight = 0`), after calibrating the massive gravitational coupling by `3/4`
to reproduce Newton's law for static masses, the effective coupling to light is strictly `3/4` of
the General Relativity coupling. -/
lemma vdvz_light_deflection_ratio (M : MassiveGravityTheory) (hM : M.c = 1 / 3)
    (Tmass Tlight : Tensor2 4) (hnull : metricTrace minkowski Tlight = 0) :
    (3 / 4) * massivePropagatorCoupling M Tmass Tlight =
      (3 / 4) * grPropagatorCoupling Tmass Tlight := by
  simp only [massivePropagatorCoupling, grPropagatorCoupling,
    MassiveGravityTheory.propagatorCoupling, MassiveGravityTheory.generalRelativity, hM, hnull]
  ring

end MassiveGravity

end Modified

end GeneralRelativity
