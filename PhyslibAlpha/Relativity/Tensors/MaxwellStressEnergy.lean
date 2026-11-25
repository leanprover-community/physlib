/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Physlib.Electromagnetism.Kinematics.FieldStrength
public import PhyslibAlpha.Relativity.Metrics.MetricTrace
import Mathlib.Tactic.Ring

/-!

# Electromagnetic field-strength invariant and Maxwell stress-energy

Shared 4D electromagnetic stress-energy tensor `T^{EM}_{ab}`, its quadratic field invariant
`F_{ab} F^{ab}`, a single proof of conformal tracelessness `g^{ab} T^{EM}_{ab} = 0`, and a
component bridge to Physlib's `Electromagnetism.ElectromagneticPotential.toFieldStrength`.

## i. Overview

In four spacetime dimensions, classical electromagnetism has stress-energy tensor
`T^{EM}_{ab} = g^{cd} F_{ac} F_{bd} - ¼ g_{ab} F_{cd} F^{cd}` in Heaviside–Lorentz units.
Contraction with the inverse metric `g^{ab}` yields the conformal trace identity
`g^{ab} T^{EM}_{ab} = 0`, a hallmark of classical scale invariance in four dimensions that underlies
vanishing scalar curvature `S = 0` for electrovacuum solutions such as Reissner–Nordström spacetime
and the Einstein–Maxwell sector of Kaluza–Klein reduction. In inertial Minkowski coordinates,
`F_{ab}` is expressed directly in terms of Physlib's `ElectromagneticPotential.toFieldStrength`.

## ii. Key results

- `maxwellFieldInvariant` : quadratic field-strength invariant `F_{ab} F^{ab}`.
- `maxwellStressEnergyRaw` : Heaviside–Lorentz Maxwell stress-energy tensor in 4D.
- `maxwellStressEnergyRaw_trace_zero` : conformal tracelessness `g^{ab} T^{EM}_{ab} = 0` in 4D.
- `emFieldStrengthComponents`, `emFieldStrengthComponents_antisymm` : component bridge from
  Physlib's `ElectromagneticPotential.toFieldStrength` to `Tensor2 4`.

## iii. Table of contents

- A. Maxwell stress-energy and conformal tracelessness
- B. Bridge to Physlib's `ElectromagneticPotential.toFieldStrength`

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

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

/-!

## B. Bridge to Physlib's `ElectromagneticPotential.toFieldStrength`

-/

open TensorSpecies Tensor Tensorial

/-- Extract the coordinate components `Tensor2 4` of Physlib's electromagnetic field-strength
tensor `A.toFieldStrength x` via the index equivalence `finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4`. -/
noncomputable def emFieldStrengthComponents (A : Electromagnetism.ElectromagneticPotential 3)
    (x : SpaceTime 3) : Tensor2 4 :=
  fun i j => Tensor.toScalar
    {A.toFieldStrength x | [finSumFinEquiv.symm i] [finSumFinEquiv.symm j]}ᵀ

/-- Componentwise antisymmetry of `emFieldStrengthComponents`, inherited from
`ElectromagneticPotential.toFieldStrength_eval_antisymm`. -/
lemma emFieldStrengthComponents_antisymm (A : Electromagnetism.ElectromagneticPotential 3)
    (x : SpaceTime 3) (i j : Fin 4) :
    emFieldStrengthComponents A x i j = -emFieldStrengthComponents A x j i :=
  Electromagnetism.ElectromagneticPotential.toFieldStrength_eval_antisymm A x _ _

end GeneralRelativity
