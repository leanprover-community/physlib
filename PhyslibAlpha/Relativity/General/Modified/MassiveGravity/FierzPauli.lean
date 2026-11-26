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
and on-shell tracelessness of massive spin-2 perturbations packaged on `FierzPauliTheory`.

## i. Overview

Giving a spin-2 graviton a non-zero mass `m > 0` on a Minkowski reference background `η` requires
adding a Lorentz-invariant quadratic mass term built from `h_{ab} h^{ab}` and `h² = (η^{ab}
h_{ab})²`. On `T : FierzPauliTheory`, for a generic mixing coefficient `T.α ≠ -1`, the
longitudinal Stueckelberg mode `h_{00} = ϕ''` retains a non-zero `-(m²/4)(1 + α) (ϕ'')²`
mass-induced fourth-order time derivative—the linearized precursor of the pathological sixth
Boulware–Deser ghost degree of freedom. Only the Fierz–Pauli tuning `T.α = -1` cancels this
longitudinal ghost contribution and forces the five healthy massive polarizations via the on-shell
tracelessness constraint `h = 0` for `m ≠ 0`.

## ii. Key results

- `FierzPauliTheory`, `FierzPauliTheory.ghostFree` : massive spin-2 theory parameterized by mass
  `m` and tuning `α`, and its ghost-free specialization `α = -1`.
- `hContractionSq`, `FierzPauliTheory.lagrangian`, `FierzPauliTheory.massTensor` : mass
  invariants and variation tensor contracted against `metricTrace minkowski`.
- `FierzPauliTheory.massTensor_trace`, `FierzPauliTheory.massTensor_trace_tuned`,
  `FierzPauliTheory.longitudinal_time_ghost_free_iff`,
  `FierzPauliTheory.traceless_of_zero_trace_source` : ghost-free tuning `α = -1` and
  tracelessness.

## iii. Table of contents

- A. Fierz–Pauli mass term and ghost-free trace constraint

## iv. References

* Markus Fierz and Wolfgang Pauli, *On Relativistic Wave Equations for Particles of Arbitrary Spin
  in an Electromagnetic Field*, *Proceedings of the Royal Society of London. Series A* 173, pp.
  211-232 (1939), Sec. 2-3. [ref: FierzPauli1939]
* D. G. Boulware and S. Deser, *Can Gravitation Have a Finite Range?*, *Physical Review D* 6, pp.
  3368-3382 (1972), Sec. II. [ref: BoulwareDeser1972]
* Kurt Hinterbichler, *Theoretical Aspects of Massive Gravity*, *Reviews of Modern Physics* 84, pp.
  671-710 (2012), Sec. II-III (https://arxiv.org/pdf/1105.3735#page=4). [ref: Hinterbichler2012]
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

/-- The ghost-free Fierz–Pauli tuning `α = -1` at graviton mass `m`. -/
def FierzPauliTheory.ghostFree (m : ℝ) : FierzPauliTheory := ⟨m, -1⟩

/-- Full Minkowski quadratic contraction `h_{ab} h^{ab} = ∑_{a,b} η^{aa} η^{bb} (h_{ab})²`. -/
def hContractionSq (h : Tensor2 4) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, minkowskiMetric4 a a * minkowskiMetric4 b b * h a b * h a b

/-- General Lorentz-invariant quadratic graviton mass Lagrangian density
`ℒ_mass(α) = -(m² / 4) (h_{ab} h^{ab} + α h²)` evaluated for a `FierzPauliTheory`. -/
noncomputable def FierzPauliTheory.lagrangian (T : FierzPauliTheory) (h : Tensor2 4) : ℝ :=
  -(T.m ^ 2 / 4) * (hContractionSq h + T.α * metricTrace minkowski h ^ 2)

/-- Mass-term contribution to the linearized field equations for a `FierzPauliTheory`:
`M_{ij}(α) = (m² / 2) (h_{ij} + α η_{ij} h)`. -/
noncomputable def FierzPauliTheory.massTensor (T : FierzPauliTheory) (h : Tensor2 4) :
    Tensor2 4 :=
  fun i j => (T.m ^ 2 / 2) * (h i j + T.α * minkowskiMetric4 i j * metricTrace minkowski h)

/-- Minkowski trace of the general mass tensor:
`η^{ij} M_{ij}(α) = (m² / 2) (1 + 4 α) h`. -/
lemma FierzPauliTheory.massTensor_trace (T : FierzPauliTheory) (h : Tensor2 4) :
    (∑ i : Fin 4, minkowskiMetric4 i i * T.massTensor h i i) =
      (T.m ^ 2 / 2) * (1 + 4 * T.α) * metricTrace minkowski h := by
  simp only [massTensor, metricTrace_minkowski, Fin.sum_univ_four, minkowskiMetric4_apply]
  norm_num
  ring

/-- At the Fierz–Pauli ghost-free point `T.α = -1`, the trace of the mass tensor is
`-(3 / 2) m² h`. -/
lemma FierzPauliTheory.massTensor_trace_tuned (T : FierzPauliTheory) (hα : T.α = -1)
    (h : Tensor2 4) :
    (∑ i : Fin 4, minkowskiMetric4 i i * T.massTensor h i i) =
      -(3 / 2) * T.m ^ 2 * metricTrace minkowski h := by
  rw [T.massTensor_trace, hα]
  ring

/-- Ghost cancellation on a longitudinal plane wave: for a 1D mode `h_{00} = ϕ''` with all other
components zero and `T.m ≠ 0`, the quadratic mass Lagrangian vanishes (eliminating the sixth
scalar ghost degree of freedom) if and only if `T.α = -1`. -/
lemma FierzPauliTheory.longitudinal_time_ghost_free_iff (T : FierzPauliTheory) (hm : T.m ≠ 0)
    (ϕdd : ℝ) (hϕ : ϕdd ≠ 0) :
    T.lagrangian (fun i j => if i = 0 ∧ j = 0 then ϕdd else 0) = 0 ↔ T.α = -1 := by
  have ht : metricTrace minkowski (fun i j => if i = 0 ∧ j = 0 then ϕdd else 0) = -ϕdd := by
    simp [metricTrace, minkowski, Fin.sum_univ_four]
  have hc : hContractionSq (fun i j => if i = 0 ∧ j = 0 then ϕdd else 0) = ϕdd ^ 2 := by
    simp [hContractionSq, Fin.sum_univ_four]
    ring
  simp only [lagrangian, hc, ht]
  constructor
  · intro h
    have hfac : -(T.m ^ 2 / 4) * ϕdd ^ 2 * (1 + T.α) = 0 := by
      calc -(T.m ^ 2 / 4) * ϕdd ^ 2 * (1 + T.α)
          = -(T.m ^ 2 / 4) * (ϕdd ^ 2 + T.α * (-ϕdd) ^ 2) := by ring
        _ = 0 := h
    have hm2 : T.m ^ 2 ≠ 0 := pow_ne_zero 2 hm
    have hpre : -(T.m ^ 2 / 4) * ϕdd ^ 2 ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr (div_ne_zero hm2 (by norm_num))) (pow_ne_zero 2 hϕ)
    rcases mul_eq_zero.mp hfac with h0 | h1
    · exact False.elim (hpre h0)
    · linarith
  · intro hα
    rw [hα]
    ring

/-- On shell in vacuum (where the divergence constraint forces the trace of the mass tensor to
vanish), any non-zero Fierz–Pauli mass `T.m ≠ 0` at `T.α = -1` forces the metric perturbation to
be traceless (`h = 0`). -/
lemma FierzPauliTheory.traceless_of_zero_trace_source (T : FierzPauliTheory) (hm : T.m ≠ 0)
    (hα : T.α = -1) (h : Tensor2 4)
    (htr : (∑ i : Fin 4, minkowskiMetric4 i i * T.massTensor h i i) = 0) :
    metricTrace minkowski h = 0 := by
  rw [T.massTensor_trace_tuned hα] at htr
  have hm2 : T.m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  have hfac : (-(3 / 2 : ℝ) * T.m ^ 2) * metricTrace minkowski h = 0 := by linarith
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exfalso; apply hm2; linarith
  · exact h2

end MassiveGravity

end Modified

end GeneralRelativity
