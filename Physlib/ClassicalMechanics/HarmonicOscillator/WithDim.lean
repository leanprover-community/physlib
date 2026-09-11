/-
Copyright (c) 2026 Hirotaka Monya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hirotaka Monya
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
public import Physlib.Units.WithDim.Analysis

/-!
# A. A harmonic oscillator with dimension-tagged parameters

This module applies `WithDim` to the existing harmonic-oscillator model. The mass and spring
constant themselves carry their physical dimensions, and the potential energy is assembled from
dimension-tagged quantities. Its output dimension is therefore checked by the type of the
expression rather than attached only after evaluating a numerical function.

The explicit map `toHarmonicOscillator` connects the tagged model to the existing numerical model.
The analytic results then reuse the general `WithDim` transport API and the existing numerical
potential energy. The derivative remains an ordinary continuous linear map between the tagged
coordinate spaces; a derivative whose value itself carries the quotient of output and input
dimensions remains separate follow-up work.
-/

@[expose] public section

namespace ClassicalMechanics

open Dimension InnerProductSpace

/-!
## A.1. Dimension-tagged oscillator data
-/

/-- A harmonic oscillator whose physical parameters carry their dimensions.

The spring constant has dimension `M T⁻²`, so multiplying it by a squared length produces
the energy dimension `M L² T⁻²`.
-/
structure HarmonicOscillatorWithDim where
  /-- The oscillator mass. -/
  m : WithDim M𝓭 ℝ
  /-- The spring constant, with dimension `M T⁻²`. -/
  k : WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ
  /-- The mass is positive. -/
  m_pos : 0 < m
  /-- The spring constant is positive. -/
  k_pos : 0 < k

namespace HarmonicOscillatorWithDim

/-- Forget the dimension tags on the parameters to recover the existing numerical model. -/
def toHarmonicOscillator (S : HarmonicOscillatorWithDim) : HarmonicOscillator where
  m := S.m.val
  k := S.k.val
  m_pos := by simpa using S.m_pos
  k_pos := by simpa using S.k_pos

/-- The squared norm of a length-tagged position, carrying dimension `L²`. -/
noncomputable def positionNormSq
    (x : WithDim L𝓭 (EuclideanSpace ℝ (Fin 1))) : WithDim (L𝓭 * L𝓭) ℝ :=
  ⟨⟪x.val, x.val⟫_ℝ⟩

@[simp]
lemma positionNormSq_val (x : WithDim L𝓭 (EuclideanSpace ℝ (Fin 1))) :
    (positionNormSq x).val = ⟪x.val, x.val⟫_ℝ := rfl

/-- The potential energy `1/2 k x²`, with its energy dimension checked by the tagged expression. -/
noncomputable def potentialEnergy (S : HarmonicOscillatorWithDim) :
    WithDim L𝓭 (EuclideanSpace ℝ (Fin 1)) →
      WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ := fun x =>
  (1 / (2 : ℝ)) • WithDim.cast (S.k * positionNormSq x)

/-- In numerical coordinates, the tagged potential energy is the existing oscillator potential. -/
@[simp]
lemma potentialEnergy_val (S : HarmonicOscillatorWithDim)
    (x : WithDim L𝓭 (EuclideanSpace ℝ (Fin 1))) :
    (S.potentialEnergy x).val = S.toHarmonicOscillator.potentialEnergy x.val := by
  simp [potentialEnergy, toHarmonicOscillator, positionNormSq,
    HarmonicOscillator.potentialEnergy, WithDim.cast, WithDim.withDim_hMul_val, smul_eq_mul]

/-- The typed potential energy is the explicit coordinate transport of the existing model. -/
lemma potentialEnergy_eq_transport (S : HarmonicOscillatorWithDim) :
    S.potentialEnergy =
      WithDim.transport L𝓭 (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹)
        S.toHarmonicOscillator.potentialEnergy := by
  funext x
  apply WithDim.ext
  exact S.potentialEnergy_val x

/-!
## A.2. Analytic reuse
-/

/-- The tagged potential energy is differentiable with the transported numerical derivative. -/
lemma hasFDerivAt_potentialEnergy (S : HarmonicOscillatorWithDim)
    (x : WithDim L𝓭 (EuclideanSpace ℝ (Fin 1))) :
    HasFDerivAt S.potentialEnergy
      (WithDim.transportLinearMap L𝓭 (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹)
        (fderiv ℝ S.toHarmonicOscillator.potentialEnergy x.val)) x := by
  rw [S.potentialEnergy_eq_transport]
  apply WithDim.hasFDerivAt_transport
  have hf : Differentiable ℝ S.toHarmonicOscillator.potentialEnergy := by
    unfold HarmonicOscillator.potentialEnergy
    fun_prop
  exact (hf x.val).hasFDerivAt

/-- The dimension-tagged potential energy is continuous. -/
lemma continuous_potentialEnergy (S : HarmonicOscillatorWithDim) :
    Continuous S.potentialEnergy :=
  (show Differentiable ℝ S.potentialEnergy from
    fun x => (S.hasFDerivAt_potentialEnergy x).differentiableAt).continuous

end HarmonicOscillatorWithDim

end ClassicalMechanics
