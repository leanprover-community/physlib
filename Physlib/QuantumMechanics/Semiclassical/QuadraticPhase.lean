/-
Copyright (c) 2026 Zhuoran Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhuoran Li
-/
module

public import Physlib.QuantumMechanics.Semiclassical.Basic

/-!
# Quadratic phase multipliers

Control oscillatory quadratic multipliers on the common Schwartz domain and in `L^2`.

## i. Overview

Multiplication by `exp (i a |x|^2)` preserves Schwartz maps and their Hilbert-space
norms. Its momentum product rule gives the basic shear used in free propagation. A
quadratic-weight estimate controls variation in `a` and yields norm continuity of the
propagator without assumptions on pointwise representatives of arbitrary `L^2` vectors.

## ii. Key results

- `quadraticPhaseCLM` : multiplication by a quadratic phase
- `quadraticPhaseCLM_momentum` : the momentum product rule
- `quadraticPhaseCLM_norm` : preservation of the Hilbert-space norm
- `quadraticPhaseCLM_lipschitz` : quantitative dependence on the phase parameter

## iii. Table of contents

- A. The quadratic phase
- B. Multipliers on Schwartz maps
- C. Dependence on the phase parameter

## iv. References

* None.
-/

@[expose] public section

namespace QuantumMechanics.Semiclassical

noncomputable section

open Complex Real MeasureTheory SchwartzMap ContinuousLinearMap
open SpaceDHilbertSpace
open scoped FourierTransform InnerProductSpace

variable {d : ℕ}

/-! ## A. The quadratic phase -/

/-- The oscillatory quadratic phase `exp (i a |x|^2)`. -/
def quadraticPhase (a : ℝ) (ξ : Space d) : ℂ :=
  Complex.exp ((a * ‖ξ‖ ^ 2 : ℝ) * I)

/-- A quadratic phase is a valid multiplier of Schwartz maps. -/
lemma quadraticPhase_hasTemperateGrowth (a : ℝ) :
    (quadraticPhase (d := d) a).HasTemperateGrowth := by
  exact Complex.hasTemperateGrowth_exp_mul_I.comp (by fun_prop)

/-- The phase at parameter zero is one. -/
lemma quadraticPhase_zero (ξ : Space d) : quadraticPhase 0 ξ = 1 := by
  simp [quadraticPhase]

/-- Adding phase parameters multiplies the phases. -/
lemma quadraticPhase_add (a b : ℝ) (ξ : Space d) :
    quadraticPhase (a + b) ξ = quadraticPhase a ξ * quadraticPhase b ξ := by
  simp [quadraticPhase, add_mul, Complex.exp_add]

/-- A quadratic phase has modulus one. -/
lemma quadraticPhase_norm (a : ℝ) (ξ : Space d) : ‖quadraticPhase a ξ‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

/-- The spatial derivative of the quadratic phase. -/
lemma quadraticPhase_deriv (a : ℝ) (i : Fin d) (ξ : Space d) :
    Space.deriv i (quadraticPhase a) ξ = (2 * a * ξ i * I) * quadraticPhase a ξ := by
  unfold Space.deriv quadraticPhase
  have hn := (hasStrictFDerivAt_norm_sq ξ).hasFDerivAt.const_mul a
  have he := (Complex.ofRealCLM.hasFDerivAt.comp ξ hn).mul_const I
  have hi := congrArg (fun T : Space d →L[ℝ] ℂ => T (Space.basis i)) he.cexp.fderiv
  simpa [Function.comp_def, Space.inner_basis, mul_comm, mul_left_comm, mul_assoc] using hi

/-- The derivative of the quadratic phase with respect to its real parameter. -/
lemma quadraticPhase_hasDerivAt (a : ℝ) (ξ : Space d) :
    HasDerivAt (fun b : ℝ => quadraticPhase b ξ)
      (((‖ξ‖ ^ 2 : ℝ) : ℂ) * I * quadraticPhase a ξ) a := by
  have h₁ := (hasDerivAt_id a).mul_const (‖ξ‖ ^ 2)
  have h₂ := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt a h₁).mul_const I
  convert h₂.cexp using 1 <;> simp [quadraticPhase, mul_comm]

/-! ## B. Multipliers on Schwartz maps -/

/-- Multiplication by a quadratic phase on Schwartz maps. -/
def quadraticPhaseCLM (a : ℝ) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (quadraticPhase a)

/-- The pointwise action of the quadratic-phase multiplier. -/
lemma quadraticPhaseCLM_apply (a : ℝ) (f : 𝓢(Space d, ℂ)) (ξ : Space d) :
    quadraticPhaseCLM a f ξ = quadraticPhase a ξ * f ξ := by
  exact smulLeftCLM_apply_apply (quadraticPhase_hasTemperateGrowth a) f ξ

/-- The zero-parameter multiplier is the identity. -/
@[simp]
lemma quadraticPhaseCLM_zero : quadraticPhaseCLM (d := d) 0 = .id ℂ _ := by
  ext f x
  simp [quadraticPhaseCLM_apply, quadraticPhase_zero]

/-- Quadratic-phase multipliers compose by adding their parameters. -/
lemma quadraticPhaseCLM_add (a b : ℝ) :
    quadraticPhaseCLM (d := d) (a + b) = quadraticPhaseCLM a ∘L quadraticPhaseCLM b := by
  ext f x
  simp [quadraticPhaseCLM_apply, quadraticPhase_add, mul_assoc]

/-- The product rule for momentum and a quadratic-phase multiplier. -/
lemma quadraticPhaseCLM_momentum (h a : ℝ) (i : Fin d) (f : 𝓢(Space d, ℂ)) :
    momentumCLM h i (quadraticPhaseCLM a f) =
      quadraticPhaseCLM a (momentumCLM h i f) +
        (2 * h * a : ℂ) • 𝐱 i (quadraticPhaseCLM a f) := by
  ext x
  rw [momentumCLM_apply]
  have hf : (quadraticPhaseCLM a f : Space d → ℂ) = fun x => quadraticPhase a x * f x := by
    ext x
    exact quadraticPhaseCLM_apply a f x
  rw [hf, Space.deriv]
  rw [fderiv_fun_mul ((quadraticPhase_hasTemperateGrowth a).1.differentiable
    (by simp)).differentiableAt f.differentiableAt]
  change -I * h * (quadraticPhase a x * Space.deriv i f x +
    f x * Space.deriv i (quadraticPhase a) x) = _
  simp only [quadraticPhase_deriv, add_apply, smul_apply, smul_eq_mul,
    quadraticPhaseCLM_apply, momentumCLM_apply, QuantumMechanics.positionCLM_apply]
  ring_nf
  simp [I_sq]

/-- Quadratic-phase multiplication preserves the Hilbert-space norm. -/
lemma quadraticPhaseCLM_norm (a : ℝ) (f : 𝓢(Space d, ℂ)) :
    ‖schwartzIncl volume (quadraticPhaseCLM a f)‖ = ‖schwartzIncl volume f‖ := by
  change ‖(quadraticPhaseCLM a f).toLp 2 volume‖ = ‖f.toLp 2 volume‖
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp]
  congr 1
  apply eLpNorm_congr_norm_ae (quadraticPhaseCLM a f).continuous.aestronglyMeasurable
    f.continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [quadraticPhaseCLM_apply, norm_mul, quadraticPhase_norm, one_mul]

/-! ## C. Dependence on the phase parameter -/

/-- The deviation of a quadratic phase from one is bounded by its real exponent. -/
lemma quadraticPhase_sub_one_le (a : ℝ) (ξ : Space d) :
    ‖quadraticPhase a ξ - 1‖ ≤ |a| * ‖ξ‖ ^ 2 := by
  have hb := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a * ‖ξ‖ ^ 2)
  simpa only [quadraticPhase, mul_comm I, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (sq_nonneg ‖ξ‖)] using hb

/-- A pointwise estimate for the difference of two quadratic phases. -/
lemma quadraticPhase_sub_le (a b : ℝ) (ξ : Space d) :
    ‖quadraticPhase a ξ - quadraticPhase b ξ‖ ≤ |a - b| * ‖ξ‖ ^ 2 := by
  have hab : quadraticPhase a ξ = quadraticPhase b ξ * quadraticPhase (a - b) ξ := by
    rw [← quadraticPhase_add]
    congr 1
    ring
  rw [hab, ← mul_sub_one, norm_mul, quadraticPhase_norm, one_mul]
  exact quadraticPhase_sub_one_le (a - b) ξ

/-- An `L^2` estimate for changing the phase parameter, controlled by a quadratic weight. -/
lemma quadraticPhaseCLM_sub_norm_le (a b : ℝ) (f : 𝓢(Space d, ℂ)) :
    ‖schwartzIncl volume (quadraticPhaseCLM a f) -
      schwartzIncl volume (quadraticPhaseCLM b f)‖ ≤
      |a - b| * ‖schwartzIncl volume (SchwartzMap.smulLeftCLM ℂ
        (fun ξ : Space d => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) f)‖ := by
  rw [← map_sub]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [SchwartzMap.coeFn_toLp (quadraticPhaseCLM a f - quadraticPhaseCLM b f) 2 volume,
    SchwartzMap.coeFn_toLp (SchwartzMap.smulLeftCLM ℂ
      (fun ξ : Space d => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) f) 2 volume] with ξ h₁ h₂
  change ‖((quadraticPhaseCLM a f - quadraticPhaseCLM b f).toLp 2 volume) ξ‖ ≤
    |a - b| * ‖((SchwartzMap.smulLeftCLM ℂ
      (fun ξ : Space d => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) f).toLp 2 volume) ξ‖
  rw [h₁, h₂, sub_apply, quadraticPhaseCLM_apply, quadraticPhaseCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply (g := fun ξ : Space d => ((‖ξ‖ ^ 2 : ℝ) : ℂ))
      (Complex.hasTemperateGrowth_ofReal.comp (Function.hasTemperateGrowth_norm_sq (Space d)))]
  rw [smul_eq_mul, ← sub_mul, norm_mul, norm_mul]
  calc
    _ ≤ (|a - b| * ‖ξ‖ ^ 2) * ‖f ξ‖ :=
      mul_le_mul_of_nonneg_right (quadraticPhase_sub_le a b ξ) (norm_nonneg _)
    _ = _ := by simp [mul_assoc]

/-- For a fixed Schwartz map, the phase multiplier is Lipschitz in its parameter in `L^2`. -/
lemma quadraticPhaseCLM_lipschitz (f : 𝓢(Space d, ℂ)) :
    LipschitzWith ‖schwartzIncl volume (SchwartzMap.smulLeftCLM ℂ
      (fun ξ : Space d => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) f)‖₊
      (fun a : ℝ => schwartzIncl volume (quadraticPhaseCLM a f)) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simpa only [dist_eq_norm, coe_nnnorm, Real.norm_eq_abs, mul_comm] using
    quadraticPhaseCLM_sub_norm_le a b f

end

end QuantumMechanics.Semiclassical
