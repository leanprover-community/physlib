/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import PhyslibAlpha.Relativity.Metrics.MetricTrace
public import PhyslibAlpha.Relativity.Metrics.Minkowski
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Fierz–Pauli massive gravity and ghost freedom

Fierz–Pauli Lorentz-invariant quadratic mass term, Boulware–Deser ghost-free tuning `α = -1`,
and on-shell tracelessness of massive spin-2 perturbations.

## i. Overview

Giving the graviton a non-zero mass `m > 0` on a Minkowski reference background `η` requires a
quadratic potential built from `h_{ab} h^{ab}` and `h² = (η^{ab} h_{ab})²`. Only the
Fierz–Pauli tuning `α = -1` eliminates the sixth Boulware–Deser ghost degree of freedom and forces
`h = 0` on shell for `m ≠ 0`.

## ii. Key results

- `FierzPauliTheory` : massive spin-2 theory parameterized by mass `m` and tuning `α`.
- `hTraceEta`, `hContractionSq`, `fierzPauliLagrangian`, `fpMassTensor` : mass invariants and
  variation tensor.
- `fpMassTensor_trace`, `fpMassTensor_trace_tuned`, `longitudinal_time_ghost_free_iff`,
  `fp_traceless_of_zero_trace_source` : ghost-free tuning `α = -1` and tracelessness.

## iii. Table of contents

- A. Fierz–Pauli mass term and ghost-free trace constraint

## iv. References

* Markus Fierz and Wolfgang Pauli, *On Relativistic Wave Equations for Particles of Arbitrary Spin
  in an Electromagnetic Field*, *Proceedings of the Royal Society of London. Series A* (1939).
  [ref: FierzPauli1939]
* D. G. Boulware and S. Deser, *Can Gravitation Have a Finite Range?*, *Physical Review D* (1972).
  [ref: BoulwareDeser1972]
* Kurt Hinterbichler, *Theoretical Aspects of Massive Gravity*, *Reviews of Modern Physics* (2012)
  (https://arxiv.org/abs/1105.3735). [ref: Hinterbichler2012]

-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace MassiveGravity

/-!

## A. Fierz–Pauli mass term and ghost-free trace constraint

-/

/-- Fierz–Pauli linearized massive gravity parameterized by graviton mass `m` and mass-term
mixing parameter `α` (ghost-free at `α = -1`). -/
structure FierzPauliTheory where
  /-- Graviton mass parameter `m`. -/
  m : ℝ
  /-- Relative coefficient `α` of `(η^{ab} h_{ab})²`. -/
  α : ℝ

/-- Minkowski trace `h = η^{ab} h_{ab}` of a rank-2 perturbation `h : Tensor2 4`. -/
def hTraceEta (h : Tensor2 4) : ℝ :=
  ∑ a : Fin 4, minkowskiMetric4 a a * h a a

/-- Full Minkowski quadratic contraction `h_{ab} h^{ab} = ∑_{a,b} η^{aa} η^{bb} (h_{ab})²`. -/
def hContractionSq (h : Tensor2 4) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, minkowskiMetric4 a a * minkowskiMetric4 b b * h a b * h a b

/-- General Lorentz-invariant quadratic graviton mass Lagrangian density
`ℒ_mass(α) = -(m² / 4) (h_{ab} h^{ab} + α h²)`. The Fierz–Pauli tuning is `α = -1`. -/
noncomputable def fierzPauliLagrangian (m α : ℝ) (h : Tensor2 4) : ℝ :=
  -(m ^ 2 / 4) * (hContractionSq h + α * hTraceEta h ^ 2)

/-- Mass-term contribution to the linearized field equations:
`M_{ij}(α) = (m² / 2) (h_{ij} + α η_{ij} h)`. -/
noncomputable def fpMassTensor (m α : ℝ) (h : Tensor2 4) : Tensor2 4 :=
  fun i j => (m ^ 2 / 2) * (h i j + α * minkowskiMetric4 i j * hTraceEta h)

/-- Minkowski trace of the general mass tensor:
`η^{ij} M_{ij}(α) = (m² / 2) (1 + 4 α) h`. -/
lemma fpMassTensor_trace (m α : ℝ) (h : Tensor2 4) :
    (∑ i : Fin 4, minkowskiMetric4 i i * fpMassTensor m α h i i) =
      (m ^ 2 / 2) * (1 + 4 * α) * hTraceEta h := by
  unfold fpMassTensor hTraceEta
  simp only [Fin.sum_univ_four, minkowskiMetric4_apply]
  norm_num
  ring

/-- At the Fierz–Pauli ghost-free point `α = -1`, the trace of the mass tensor is
`-(3 / 2) m² h`. -/
lemma fpMassTensor_trace_tuned (m : ℝ) (h : Tensor2 4) :
    (∑ i : Fin 4, minkowskiMetric4 i i * fpMassTensor m (-1) h i i)
      = -(3 / 2) * m ^ 2 * hTraceEta h := by
  rw [fpMassTensor_trace]
  ring

/-- Longitudinal kinetic-mass decoupling criterion: for a 1D plane-wave longitudinal mode
`h_{00} = ϕ''`, all other components `0`, the quadratic mass combination `h_{ab} h^{ab} + α h²`
vanishes (preventing a fourth-order time-derivative Boulware–Deser ghost) if and only if
`α = -1`. -/
lemma longitudinal_time_ghost_free_iff (α ϕdd : ℝ) (hϕ : ϕdd ≠ 0) :
    hContractionSq (fun i j => if i = 0 ∧ j = 0 then ϕdd else 0)
      + α * hTraceEta (fun i j => if i = 0 ∧ j = 0 then ϕdd else 0) ^ 2 = 0 ↔ α = -1 := by
  unfold hContractionSq hTraceEta
  simp only [Fin.sum_univ_four, minkowskiMetric4_apply]
  norm_num
  constructor
  · intro h
    have h2 : ϕdd ^ 2 ≠ 0 := pow_ne_zero 2 hϕ
    have hfac : (1 + α) * ϕdd ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp hfac with h1 | h2'
    · linarith
    · exact False.elim (h2 h2')
  · intro h
    subst h
    ring

/-- On shell in vacuum (where the divergence constraint forces the trace of the mass tensor to
vanish), any non-zero Fierz–Pauli mass `m ≠ 0` at `α = -1` forces the metric perturbation to be
traceless (`h = 0`). -/
lemma fp_traceless_of_zero_trace_source (m : ℝ) (hm : m ≠ 0) (h : Tensor2 4)
    (htr : (∑ i : Fin 4, minkowskiMetric4 i i * fpMassTensor m (-1) h i i) = 0) :
    hTraceEta h = 0 := by
  rw [fpMassTensor_trace_tuned] at htr
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  have hfac : (-(3 / 2 : ℝ) * m ^ 2) * hTraceEta h = 0 := by linarith
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exfalso; apply hm2; linarith
  · exact h2

/-- `hTraceEta` coincides with `metricTrace minkowski`. -/
lemma hTraceEta_eq_metricTrace (h : Tensor2 4) :
    hTraceEta h = metricTrace minkowski h := by
  rw [metricTrace_diag minkowski h (fun _ _ hij => minkowski_ginv_offdiag hij)]
  simp [hTraceEta, minkowski]

/-- Fierz–Pauli quadratic graviton mass Lagrangian evaluated for a `FierzPauliTheory`. -/
noncomputable def FierzPauliTheory.lagrangian (T : FierzPauliTheory) (h : Tensor2 4) : ℝ :=
  fierzPauliLagrangian T.m T.α h

/-- Fierz–Pauli mass-term variation tensor evaluated for a `FierzPauliTheory`. -/
noncomputable def FierzPauliTheory.massTensor (T : FierzPauliTheory) (h : Tensor2 4) : Tensor2 4 :=
  fpMassTensor T.m T.α h

end MassiveGravity

end Modified

end GeneralRelativity
