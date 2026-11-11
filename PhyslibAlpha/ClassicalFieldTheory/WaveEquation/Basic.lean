/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.SpaceAndTime.SpaceTime.Fields

/-!

# The wave operator

## i. Overview

The wave operator on smooth fields and on distributions on spacetime.

## ii. Key results

- `smoothWaveOperator` : The smooth wave operator as the Minkowski metric trace of the second
  derivative.
- `distributionWaveOperator` : The wave operator on all distributions is the metric trace of weak
  second derivatives.
- `testWaveOperator` : The transpose wave operator on native smooth compact test functions.
- `smoothFiberMap_waveOperator` : Constant fibre transformations commute with the metric-trace wave
  operator.

## iii. Table of contents

- A. The Minkowski wave equation
- B. The distributional wave operator

## iv. References

None.

## A. The Minkowski wave equation

- `smoothWaveOperator` : The smooth wave operator as the Minkowski metric trace of the second
  derivative.

Lemmas: `smoothWaveOperator_coe`, `smoothWaveOperator_support`, `smoothFiberMap_waveOperator`.

## B. The distributional wave operator

- `distributionWaveOperator` : The wave operator on all distributions is the metric trace of weak
  second derivatives.
- `testWaveOperator` : The transpose wave operator on native smooth compact test functions.

Lemmas: `distributionWaveOperator_apply`.

-/

@[expose] public section

noncomputable section

open Minkowski SpaceTime minkowskiMatrix

namespace WaveEquation

section
variable {d : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The smooth wave operator as the Minkowski metric trace of the second derivative. -/
def smoothWaveOperator : smoothFields d V →ₗ[ℝ] smoothFields d V :=
  ∑ μ : Fin 1 ⊕ Fin d, (η μ μ : ℝ) • ((smoothDerivative μ).comp (smoothDerivative μ))

lemma smoothWaveOperator_coe (u : smoothFields d V) :
    (smoothWaveOperator u : SpaceTime d → V) =
      ∑ μ : Fin 1 ⊕ Fin d, (η μ μ : ℝ) •
        (SpaceTime.deriv μ (SpaceTime.deriv μ u.val)) := by
  simp only [smoothWaveOperator, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, Submodule.coe_sum, Submodule.coe_smul, smoothDerivative_coe]

/-- Taking the metric trace does not enlarge field support. -/
lemma smoothWaveOperator_support (u : smoothFields d V) :
    tsupport (smoothWaveOperator u : SpaceTime d → V) ⊆ tsupport (u : SpaceTime d → V) := by
  rw [smoothWaveOperator_coe]
  apply smoothField_support_sum
  intro μ _
  exact (tsupport_smul_subset_right (fun _ => (η μ μ : ℝ)) _).trans
    ((smoothDerivative_support μ (smoothDerivative μ u)).trans (smoothDerivative_support μ u))

/-- Constant fibre transformations commute with the metric-trace wave operator. -/
lemma smoothFiberMap_waveOperator {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V →L[ℝ] W) (u : smoothFields d V) :
    smoothWaveOperator (smoothFiberMap L u) = smoothFiberMap L (smoothWaveOperator u) := by
  unfold smoothWaveOperator
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    map_sum, map_smul, smoothFiberMap_derivative]

/-- The wave operator on all distributions is the metric trace of weak second derivatives. -/
def distributionWaveOperator : DistributionField d V →L[ℝ] DistributionField d V :=
  ∑ μ : Fin 1 ⊕ Fin d, (η μ μ : ℝ) •
    ((Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (Lorentz.Vector.basis μ)).comp
      (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (Lorentz.Vector.basis μ)))

/-- The transpose wave operator on native smooth compact test functions. -/
def testWaveOperator :
    _root_.TestFunction (⊤ : TopologicalSpace.Opens (SpaceTime d)) ℝ ⊤ →L[ℝ]
      _root_.TestFunction (⊤ : TopologicalSpace.Opens (SpaceTime d)) ℝ ⊤ :=
  ∑ μ : Fin 1 ⊕ Fin d, (η μ μ : ℝ) •
    ((TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (Lorentz.Vector.basis μ)).comp
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (Lorentz.Vector.basis μ)))

/-- Two weak derivatives give the positive transpose wave operator on tests. -/
lemma distributionWaveOperator_apply (T : DistributionField d V)
    (φ : _root_.TestFunction (⊤ : TopologicalSpace.Opens (SpaceTime d)) ℝ ⊤) :
    distributionWaveOperator T φ = T (testWaveOperator φ) := by
  simp only [distributionWaveOperator, testWaveOperator, sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, Distribution.lineDerivCLM_apply,
    neg_neg, map_sum, map_smul]
end

end WaveEquation
