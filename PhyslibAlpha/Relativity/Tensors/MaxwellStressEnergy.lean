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
`T^{EM}_{ab} = g^{cd} F_{ac} F_{bd} - ¼ g_{ab} F_{cd} F^{cd}` in Heaviside–Lorentz units
(Gaussian units include an overall `1 / (4 π)` prefactor). Contraction with the inverse metric
`g^{ab}` yields the conformal trace identity `g^{ab} T^{EM}_{ab} = 0`, a hallmark of classical
scale invariance in four dimensions that underlies vanishing scalar curvature `S = 0` for
electrovacuum solutions such as Reissner–Nordström spacetime and the Einstein–Maxwell sector of
Kaluza–Klein reduction.

## ii. Key results

- `maxwellFieldInvariant`, `metricTrace_maxwellQuad` : quadratic field-strength invariant
  `F_{ab} F^{ab}` and contraction of the quadratic term `g^{cd} F_{ac} F_{bd}`.
- `maxwellStressEnergy`, `maxwellStressEnergy_trace_zero` : Heaviside–Lorentz Maxwell stress-energy
  tensor in 4D and its conformal tracelessness `g^{ab} T^{EM}_{ab} = 0`.

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

The electromagnetic field strength contracts with the inverse metric to form the Lorentz-invariant
scalar `F_{ab} F^{ab}` and the symmetric, trace-free 4D Maxwell stress-energy tensor.

-/

/-- Electromagnetic field-strength quadratic invariant `F_{ab} F^{ab} = g^{ac} g^{bd}
F_{ab} F_{cd}`. -/
def maxwellFieldInvariant {n : ℕ} (M : MetricTensor n) (F : Tensor2 n) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, M.ginv a c * M.ginv b d * F a b * F c d

/-- Contracting the quadratic field-strength term `g^{cd} F_{ac} F_{bd}` with the inverse metric
reproduces the invariant `F_{ab} F^{ab}`. -/
lemma metricTrace_maxwellQuad {n : ℕ} (M : MetricTensor n) (F : Tensor2 n) :
    metricTrace M (fun a b => ∑ c : Fin n, ∑ d : Fin n, M.ginv c d * F a c * F b d) =
      maxwellFieldInvariant M F := by
  simp only [metricTrace, maxwellFieldInvariant]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun d _ => by ring

/-- Four-dimensional electromagnetic stress-energy tensor in Heaviside–Lorentz units:
`T^{EM}_{ab} = g^{cd} F_{ac} F_{bd} - ¼ g_{ab} F_{cd} F^{cd}` (multiply by `1 / (4 π)` for
Gaussian units). -/
noncomputable def maxwellStressEnergy (M : MetricTensor 4) (F : Tensor2 4) : Tensor2 4 :=
  fun a b =>
    (∑ c : Fin 4, ∑ d : Fin 4, M.ginv c d * F a c * F b d) -
      (1 / 4) * M.g a b * maxwellFieldInvariant M F

/-- In four spacetime dimensions (`n = 4`), `maxwellStressEnergy` is identically trace-free:
`g^{ab} T^{EM}_{ab} = 0`. -/
lemma maxwellStressEnergy_trace_zero (M : MetricTensor 4) (F : Tensor2 4) :
    metricTrace M (maxwellStressEnergy M F) = 0 := by
  have hsub := metricTrace_sub_fun M
    (fun a b => ∑ c : Fin 4, ∑ d : Fin 4, M.ginv c d * F a c * F b d)
    (fun a b => ((1 / 4) * maxwellFieldInvariant M F) * M.g a b)
  have hq := metricTrace_maxwellQuad M F
  have hm := metricTrace_mul_g M ((1 / 4) * maxwellFieldInvariant M F)
  have heq : maxwellStressEnergy M F =
      fun a b => (∑ c : Fin 4, ∑ d : Fin 4, M.ginv c d * F a c * F b d) -
        ((1 / 4) * maxwellFieldInvariant M F) * M.g a b := by
    ext a b
    simp only [maxwellStressEnergy]
    ring
  rw [heq, hsub, hq, hm]
  ring

end GeneralRelativity
