/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.ConstantSliceDist
import PhysLean.SpaceAndTime.Space.Norm

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!


-/
open SchwartzMap NNReal
noncomputable section
open Distribution
variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory Real

/-!

## A. The definition of the spherical shell surface

-/

/-- The map embedding the unit sphere in `Space d.succ` into `Space d.succ`. -/
def sphericalShell (d : ℕ) : Metric.sphere (0 : Space d.succ) 1 → Space d.succ := fun x => x.1

lemma sphericalShell_injective (d : ℕ) : Function.Injective (sphericalShell d) := by
  intro x y h
  simp [sphericalShell] at h
  grind

lemma sphericalShell_continuous (d : ℕ) : Continuous (sphericalShell d) := continuous_subtype_val

lemma sphericalShell_measurableEmbedding (d : ℕ) : MeasurableEmbedding (sphericalShell d) := by
  apply Continuous.measurableEmbedding
  · exact sphericalShell_continuous d
  · exact sphericalShell_injective d

@[simp]
lemma norm_sphericalShell (d : ℕ) (x : Metric.sphere (0 : Space d.succ) 1) :
    ‖sphericalShell d x‖ = 1 := by
  simp [sphericalShell, Metric.sphere]

/-!

## B. The measure associated with the spherical shell

-/

/-- The measure on `Space d.succ` corresponding to integration around a spherical shell. -/
def sphericalShellMeasure (d : ℕ) : Measure (Space d.succ) :=
  MeasureTheory.Measure.map (sphericalShell d) (MeasureTheory.Measure.toSphere volume)

instance sphericalShellMeasure_hasTemperateGrowth (d : ℕ) :
    (sphericalShellMeasure d).HasTemperateGrowth := by
  rw [sphericalShellMeasure]
  refine { exists_integrable := ?_ }
  use 0
  simp

/-!

## C. The distribution associated with the spherical shell

-/

/-- The distribution associated with a spherical shell.
  One can roughly think of this distribution as the distribution which
  takes test functions `f (r)` to `∫ d³r f(r) ρ(r)` where `ρ(r)` is the
  mass, charge or current etc. distribution. -/
def sphericalShellDist (d : ℕ) : (Space d.succ) →d[ℝ] ℝ  :=
  SchwartzMap.integralCLM ℝ (sphericalShellMeasure d)


lemma sphericalShellDist_apply_eq_integral_sphericalShellMeasure (d : ℕ) (f : 𝓢(Space d.succ, ℝ)) :
    sphericalShellDist d f = ∫ x, f x ∂sphericalShellMeasure d := by
  rw [sphericalShellDist, SchwartzMap.integralCLM_apply]

lemma sphericalShellDist_apply_eq_integral_sphere_volume (d : ℕ) (f : 𝓢(Space d.succ, ℝ)) :
    sphericalShellDist d f =
    ∫ x, f (sphericalShell d x) ∂(MeasureTheory.Measure.toSphere volume) := by
  rw [sphericalShellDist_apply_eq_integral_sphericalShellMeasure, sphericalShellMeasure,
   MeasurableEmbedding.integral_map (sphericalShell_measurableEmbedding d)]

lemma sphericalShellDist_apply_eq_integral_radius_ioi_one (d : ℕ) (f : 𝓢(Space d.succ, ℝ)) :
    sphericalShellDist d f =
      ∫ n, (-∫ (r : ℝ) in Set.Ioi 1, _root_.deriv (fun r => f (r • n.1)) r) ∂(volume.toSphere) := by
  rw [sphericalShellDist_apply_eq_integral_sphere_volume]
  congr
  funext x
  let η' : 𝓢(ℝ, ℝ) := compCLM (g := fun a => a • (sphericalShell d x) ) ℝ (by
    apply And.intro
    · fun_prop
    · intro n'
      match n' with
      | 0 =>
        use 1, 1
        simp [norm_smul]
      | 1 =>
        use 0, 1
        intro x
        simp [fderiv_smul_const, iteratedFDeriv_succ_eq_comp_right]
      | n' + 1 + 1 =>
        use 0, 0
        intro x
        simp only [Real.norm_eq_abs, pow_zero, mul_one, norm_le_zero_iff]
        rw [iteratedFDeriv_succ_eq_comp_right]
        conv_lhs =>
          enter [2, 3, y]
          simp [fderiv_smul_const]
        rw [iteratedFDeriv_succ_const]
        rfl) (by use 1, 1; simp [norm_smul]) f
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
      (f := fun r =>  f (r • sphericalShell d x)) (m := 0)]
  · simp
  · fun_prop
  · intro x hx
    refine DifferentiableAt.hasDerivAt ?_
    have := f.differentiable
    fun_prop
  · exact (integrable ((derivCLM ℝ ℝ) η')).integrableOn
  · exact Filter.Tendsto.mono_left η'.toZeroAtInfty.zero_at_infty' atTop_le_cocompact

lemma sphericalShellDist_apply_eq_integral_radius_ioi_if (d : ℕ) (f : 𝓢(Space d.succ, ℝ)) :
    sphericalShellDist d f =
      ∫ n, (-∫ (r : ℝ) in Set.Ioi 0, (if 1 < r then 1 else 0) *
      _root_.deriv (fun r => f (r • n.1)) r) ∂(volume.toSphere) := by
  rw [sphericalShellDist_apply_eq_integral_radius_ioi_one]
  congr
  funext n
  simp only [Nat.succ_eq_add_one, ite_mul, one_mul, zero_mul, neg_inj]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  congr
  funext x
  simp [Set.indicator]
  intro h1 h2
  linarith

lemma sphericalShellDist_apply_eq_volumeIoiPow (d : ℕ) (f : 𝓢(Space d.succ, ℝ)) :
    sphericalShellDist d f =
      ∫ n, (-∫ r,  ‖r.1‖⁻¹ ^ d * (if 1 < r.1 then 1 else 0) *
      _root_.deriv (fun r => f (r • n.1)) r.1
      ∂((Measure.volumeIoiPow (Module.finrank ℝ (Space d.succ) - 1)))) ∂(volume.toSphere) := by
  rw [sphericalShellDist_apply_eq_integral_radius_ioi_if]
  congr
  funext n
  simp [Measure.volumeIoiPow]
  erw [integral_withDensity_eq_integral_smul (by fun_prop)]
  rw [← Measure.Subtype.volume_def]
  rw [← MeasureTheory.integral_subtype]
  congr
  funext r
  split_ifs
  any_goals simp
  rename_i h
  generalize  _root_.deriv (fun r => f (r • ↑n)) r.1  = a
  symm
  trans ((r.1 ^ d).toNNReal : ℝ) • ((|r.1| ^ d)⁻¹ * a)
  · rfl
  simp
  rw [max_eq_left (by positivity)]
  field_simp
  rw [abs_of_nonneg]
  positivity

lemma sphericalShellDist_apply_eq_volumeIoiPow_prod (d : ℕ) (f : 𝓢(Space d.succ, ℝ)) :
    sphericalShellDist d f = -
      ∫ r,  ‖r.2.1‖⁻¹ ^ d * (if 1 < r.2.1 then 1 else 0) *
      _root_.deriv (fun a => f (a • r.1)) r.2.1
      ∂(volume (α := Space d.succ).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (Space d.succ) - 1))) := by
  rw [MeasureTheory.integral_prod, sphericalShellDist_apply_eq_volumeIoiPow,
    MeasureTheory.integral_neg]
  /- Integrability condition -/
  convert integrable_isDistBounded_inner_grad_schwartzMap_spherical
      ((IsDistBounded.inv_pow_smul_repr_self (d.succ) (by omega)).if_norm_gt_one_const_smul 1) f
  rename_i r
  simp [norm_smul]
  rw [abs_of_nonneg (le_of_lt r.2.2)]
  split_ifs
  swap
  · simp
  rename_i hrl
  let x : Space d.succ := r.2.1 • r.1.1
  have hr := r.2.2
  simp [-Subtype.coe_prop] at hr
  have hr2 : r.2.1 ≠ 0 := by exact Ne.symm (ne_of_lt hr)
  trans (r.2.1 ^ d)⁻¹ * _root_.deriv (fun a => f (a • ‖↑x‖⁻¹ • ↑x)) ‖x‖
  · simp [x, norm_smul]
    left
    congr
    funext a
    congr
    simp [smul_smul]
    rw [abs_of_nonneg (le_of_lt hr)]
    field_simp
    simp only [one_smul]
    rw [abs_of_nonneg (le_of_lt hr)]
  rw [← grad_inner_space_unit_vector]
  rw [real_inner_comm]
  simp [inner_smul_left, x, norm_smul, abs_of_nonneg (le_of_lt hr)]
  field_simp
  ring
  exact SchwartzMap.differentiable f

lemma sphericalShellDist_apply_eq_volume_deriv_radius (d : ℕ) (f : 𝓢(Space d.succ, ℝ)) :
    sphericalShellDist d f = -
      ∫ (r : Space d.succ),  ‖r‖⁻¹ ^ d * (if 1 < ‖r‖ then 1 else 0) *
      _root_.deriv (fun a => f (a • ‖r‖⁻¹ • r))  ‖r‖ := by
  rw [sphericalShellDist_apply_eq_volumeIoiPow_prod]
  rw [← MeasureTheory.MeasurePreserving.integral_comp (f := homeomorphUnitSphereProd _)
          (MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd
          (volume (α := Space d.succ)))
          (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd (Space d.succ)))]
  congr 1
  simp only [Nat.succ_eq_add_one, homeomorphUnitSphereProd_apply_snd_coe, norm_norm, inv_pow,
    mul_ite, mul_one, mul_zero, homeomorphUnitSphereProd_apply_fst_coe, ite_mul, zero_mul]
  let f (x : Space d.succ) : ℝ :=
           if 1 < ‖↑x‖ then (‖↑x‖ ^ d)⁻¹ * _root_.deriv (fun a => f (a • ‖↑x‖⁻¹ • ↑x)) ‖↑x‖
           else 0
  conv_lhs =>
    enter [2, x]
    change f x.1
  rw [MeasureTheory.integral_subtype_comap (by simp), ← setIntegral_univ]
  simp
  rfl

open InnerProductSpace

lemma sphericalShellDist_apply_eq_integral_grad  (d : ℕ) (f : 𝓢(Space d.succ, ℝ)) :
    sphericalShellDist d f =
      - ∫ x, ⟪(if 1 < ‖x‖ then 1 else 0) • ‖x‖⁻¹ ^ d.succ • basis.repr x, Space.grad f x⟫_ℝ := by
  rw [sphericalShellDist_apply_eq_volume_deriv_radius]
  congr
  funext r
  split_ifs
  swap
  · simp
  simp
  symm
  trans ‖r‖⁻¹ ^ d * ⟪‖r‖⁻¹ • basis.repr r, Space.grad f r⟫_ℝ
  · simp only [Nat.succ_eq_add_one, inv_pow, inner_smul_left, map_inv₀, conj_trivial]
    ring_nf
  simp [real_inner_comm, ← grad_inner_space_unit_vector _ _ (SchwartzMap.differentiable f)]

end Space
