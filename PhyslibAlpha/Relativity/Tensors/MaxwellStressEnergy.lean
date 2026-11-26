/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import PhyslibAlpha.Relativity.Metrics.MetricTrace
import Mathlib.Tactic.Ring

/-!

# Electromagnetic field-strength invariant and Maxwell stress-energy

Shared 4D electromagnetic stress-energy tensor `T^{EM}_{ab}`, its quadratic field invariant
`F_{ab} F^{ab}`, and a single proof of conformal tracelessness `g^{ab} T^{EM}_{ab} = 0`.

## i. Overview

In four spacetime dimensions, classical electromagnetism has stress-energy tensor
`T^{EM}_{ab} = g^{cd} F_{ac} F_{bd} - ¼ g_{ab} F_{cd} F^{cd}` in Heaviside–Lorentz units.
Contraction with the inverse metric `g^{ab}` yields the conformal trace identity
`g^{ab} T^{EM}_{ab} = 0`, a hallmark of classical scale invariance in four dimensions that underlies
vanishing scalar curvature `S = 0` for electrovacuum solutions such as Reissner–Nordström spacetime
and the Einstein–Maxwell sector of Kaluza–Klein reduction.

## ii. Key results

- `maxwellFieldInvariant` : quadratic field-strength invariant `F_{ab} F^{ab}`.
- `maxwellStressEnergyRaw` : Heaviside–Lorentz Maxwell stress-energy tensor in 4D.
- `maxwellStressEnergyRaw_trace_zero` : conformal tracelessness `g^{ab} T^{EM}_{ab} = 0` in 4D.

## iii. Table of contents

- A. Maxwell stress-energy and conformal tracelessness

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 4 (Sec. 4.3). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 3 & Ch. 5.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 4
  (https://arxiv.org/pdf/gr-qc/9712019#page=109). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Maxwell stress-energy and conformal tracelessness

-/

/-- Electromagnetic field-strength quadratic invariant `F_{ab} F^{ab} = g^{ac} g^{bd}
F_{ab} F_{cd}`. -/
def maxwellFieldInvariant {n : ℕ} (ginv F : Tensor2 n) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, ginv a c * ginv b d * F a b * F c d

/-- Unitless Heaviside–Lorentz four-dimensional electromagnetic stress-energy tensor
`T^{EM}_{ab} = g^{cd} F_{ac} F_{bd} - ¼ g_{ab} F_{cd} F^{cd}`. -/
noncomputable def maxwellStressEnergyRaw (g ginv F : Tensor2 4) : Tensor2 4 :=
  fun a b =>
    (∑ c : Fin 4, ∑ d : Fin 4, ginv c d * F a c * F b d) -
      (1 / 4) * g a b * maxwellFieldInvariant ginv F

/-- In four spacetime dimensions (`n = 4`), `maxwellStressEnergyRaw` is identically trace-free:
`g^{ab} T^{EM}_{ab} = 0`. -/
lemma maxwellStressEnergyRaw_trace_zero (M : MetricTensor 4) (F : Tensor2 4) :
    metricTrace M (maxwellStressEnergyRaw M.g M.ginv F) = 0 := by
  simp only [metricTrace, maxwellStressEnergyRaw]
  have h1 :
      (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b *
        (∑ c : Fin 4, ∑ d : Fin 4, M.ginv c d * F a c * F b d)) =
        maxwellFieldInvariant M.ginv F := by
    simp only [maxwellFieldInvariant]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun d _ => by ring
  have h2 :
      (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b *
        ((1 / 4 : ℝ) * M.g a b * maxwellFieldInvariant M.ginv F)) =
        maxwellFieldInvariant M.ginv F := by
    have htr : (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b * M.g a b) = 4 := by
      simpa using sum_ginv_mul_g M
    have hfact :
        (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b *
          ((1 / 4 : ℝ) * M.g a b * maxwellFieldInvariant M.ginv F)) =
          (1 / 4) * (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b * M.g a b) *
            maxwellFieldInvariant M.ginv F := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [hfact, htr]
    ring
  have hsub :
      (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b *
        ((∑ c : Fin 4, ∑ d : Fin 4, M.ginv c d * F a c * F b d) -
          (1 / 4 : ℝ) * M.g a b * maxwellFieldInvariant M.ginv F)) =
        (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b *
          (∑ c : Fin 4, ∑ d : Fin 4, M.ginv c d * F a c * F b d)) -
        (∑ a : Fin 4, ∑ b : Fin 4, M.ginv a b *
          ((1 / 4 : ℝ) * M.g a b * maxwellFieldInvariant M.ginv F)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hsub, h1, h2, sub_self]

end GeneralRelativity
