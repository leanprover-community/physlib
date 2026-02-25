/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Pietro Monticone
-/
import PhysLean.ClassicalMechanics.RigidBody.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
/-!

# The solid sphere as a rigid body

In this module we consider the solid sphere as a rigid body, and compute its mass,
center of mass and inertia tensor.

-/

open Manifold
open MeasureTheory
namespace RigidBody
open NNReal

/-- The solid sphere as a rigid body. -/
noncomputable def solidSphere (d : ℕ) (m R : ℝ≥0) : RigidBody d where
  ρ := ⟨⟨fun f => m / volume.real (Metric.closedBall (0 : Space d) R) *
      ∫ x in Metric.closedBall (0 : Space d) R, f x ∂volume,
    by
    intro f g
    simp only [ContMDiffMap.coe_add, Pi.add_apply]
    rw [integral_add]
    ring
    · exact IntegrableOn.integrable
        (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R) (by fun_prop))
    · exact IntegrableOn.integrable
        (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R) (by fun_prop))⟩, by
      intro r f
      simp only [ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [integral_const_mul]
      ring⟩

lemma solidSphere_mass {d : ℕ} (m R : ℝ≥0) (hr : R ≠ 0) : (solidSphere d.succ m R).mass = m := by
  simp only [mass, solidSphere]
  simp only [Nat.succ_eq_add_one, LinearMap.coe_mk, AddHom.coe_mk, ContMDiffMap.coeFn_mk,
    integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter, smul_eq_mul,
    mul_one]
  have h1 : (@volume (Space d.succ) measureSpaceOfInnerProductSpace).real
      (Metric.closedBall 0 R) ≠ 0 := by
    refine (measureReal_ne_zero_iff ?_).mpr ?_
    · apply Space.volume_closedBall_ne_top
    · apply Space.volume_closedBall_ne_zero
      have hr' := R.2
      have hx : R.1 ≠ 0 := by simpa using hr
      apply lt_of_le_of_ne hr' (Ne.symm hx)
  field_simp

/-- The center of mass of a solid sphere located at the origin is `0`. -/
lemma solidSphere_centerOfMass {d : ℕ} (m R : ℝ≥0) :
    (solidSphere d.succ m R).centerOfMass = 0 := by
  ext i
  simp only [Nat.succ_eq_add_one, centerOfMass, solidSphere, one_div, LinearMap.coe_mk,
    AddHom.coe_mk, ContMDiffMap.coeFn_mk, smul_eq_mul, Space.zero_apply, mul_eq_zero, inv_eq_zero,
    div_eq_zero_iff, coe_eq_zero]
  right
  right
  suffices ∫ x in Metric.closedBall (0 : Space d.succ) R, x i ∂MeasureSpace.volume
    = -∫ x in Metric.closedBall (0 : Space d.succ) R, x i ∂MeasureSpace.volume by linarith
  rw [← integral_neg]
  simp only [← integral_indicator measurableSet_closedBall, Set.indicator, Metric.mem_closedBall,
    dist_zero_right]
  rw [← integral_neg_eq_self]
  norm_num

/-!

## Helper constructions for the inertia tensor

-/

section InertiaTensorHelpers

variable {d : ℕ}

/-- A single-coordinate negation on `Space d` — negates the k-th coordinate. -/
noncomputable def Space.reflectCoord (k : Fin d) : Space d ≃ₗᵢ[ℝ] Space d where
  toLinearEquiv := {
    toFun := fun x => ⟨fun i => if i = k then -(x i) else x i⟩
    map_add' := fun x y => by ext i; simp only [Space.add_apply]; split_ifs <;> ring
    map_smul' := fun c x => by
      ext i; simp only [Space.smul_apply, RingHom.id_apply]; split_ifs <;> ring
    invFun := fun x => ⟨fun i => if i = k then -(x i) else x i⟩
    left_inv := fun x => by ext i; simp only; split_ifs <;> simp
    right_inv := fun x => by ext i; simp only; split_ifs <;> simp
  }
  norm_map' := fun x => by
    simp only [LinearEquiv.coe_mk, Space.norm_eq]; congr 1
    apply Finset.sum_congr rfl; intro i _
    show (if i = k then -(x i) else x i) ^ 2 = x i ^ 2; split_ifs <;> ring

/-- A coordinate swap on `Space d` — swaps the i-th and j-th coordinates. -/
noncomputable def Space.swapCoord (i j : Fin d) : Space d ≃ₗᵢ[ℝ] Space d where
  toLinearEquiv := {
    toFun := fun x => ⟨fun k => x (Equiv.swap i j k)⟩
    map_add' := fun x y => by ext k; simp [Space.add_apply]
    map_smul' := fun c x => by ext k; simp [Space.smul_apply]
    invFun := fun x => ⟨fun k => x (Equiv.swap i j k)⟩
    left_inv := fun x => by ext k; simp
    right_inv := fun x => by ext k; simp
  }
  norm_map' := fun x => by
    simp only [LinearEquiv.coe_mk, Space.norm_eq]; congr 1
    exact Finset.sum_equiv (Equiv.swap i j) (by simp) (by intro k _; rfl)

@[simp]
lemma Space.reflectCoord_apply (k i : Fin d) (x : Space d) :
    (Space.reflectCoord k x) i = if i = k then -(x i) else x i := by
  simp [Space.reflectCoord]

@[simp]
lemma Space.swapCoord_apply (i j k : Fin d) (x : Space d) :
    (Space.swapCoord i j x) k = x (Equiv.swap i j k) := by
  simp [Space.swapCoord]

private lemma isometry_image_closedBall (f : Space d.succ ≃ₗᵢ[ℝ] Space d.succ) (R : ℝ) :
    f '' Metric.closedBall 0 R = Metric.closedBall 0 R := by
  ext x; constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right] at hy ⊢
    rw [f.norm_map]; exact hy
  · intro hx
    refine ⟨f.symm x, ?_, by simp⟩
    simp only [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    rw [f.symm.norm_map]; exact hx

/-- The integral of x_i * x_j over the closed ball vanishes for i ≠ j,
by the reflection symmetry x_i ↦ -x_i. -/
lemma integral_coord_mul_closedBall_eq_zero {i j : Fin d.succ} (hij : i ≠ j) (R : ℝ) :
    ∫ x in Metric.closedBall (0 : Space d.succ) R, x i * x j ∂volume = 0 := by
  suffices h : ∫ x in Metric.closedBall (0 : Space d.succ) R, x i * x j ∂volume =
    -(∫ x in Metric.closedBall (0 : Space d.succ) R, x i * x j ∂volume) by linarith
  conv_lhs =>
    rw [← isometry_image_closedBall (Space.reflectCoord i) R,
        (Space.reflectCoord (d := d.succ) i).measurePreserving.setIntegral_image_emb
          (Space.reflectCoord (d := d.succ) i).toHomeomorph.measurableEmbedding]
  rw [show (fun x : Space d.succ =>
      (Space.reflectCoord i x) i * (Space.reflectCoord i x) j) =
      fun x => -(x i * x j) from by funext x; simp [hij.symm],
    integral_neg]

/-- The integral of x_i^2 over the closed ball is the same for all coordinates,
by the swap symmetry x_i ↔ x_j. -/
lemma integral_coord_sq_closedBall_eq (i j : Fin d.succ) (R : ℝ) :
    ∫ x in Metric.closedBall (0 : Space d.succ) R, x i ^ 2 ∂volume =
    ∫ x in Metric.closedBall (0 : Space d.succ) R, x j ^ 2 ∂volume := by
  conv_lhs =>
    rw [← isometry_image_closedBall (Space.swapCoord i j) R,
        (Space.swapCoord (d := d.succ) i j).measurePreserving.setIntegral_image_emb
          (Space.swapCoord (d := d.succ) i j).toHomeomorph.measurableEmbedding]
  congr 1; funext x; simp [Equiv.swap_apply_left]

open Pointwise in
/-- Integral scaling: ∫_{B(0,R)} x_0^2 = R^5 ∫_{B(0,1)} x_0^2. -/
private lemma integral_coord_sq_closedBall_scaling (R : ℝ) (hR : 0 < R) :
    ∫ x in Metric.closedBall (0 : Space 3) R, x 0 ^ 2 ∂volume =
    R ^ 5 * ∫ x in Metric.closedBall (0 : Space 3) 1, x 0 ^ 2 ∂volume := by
  have h := Measure.setIntegral_comp_smul_of_pos (μ := volume (α := Space 3))
    (fun x : Space 3 => x 0 ^ 2) (s := Metric.closedBall 0 1) hR
  rw [show R • Metric.closedBall (0 : Space 3) 1 = Metric.closedBall 0 R from by
    rw [smul_closedBall R 0 (by norm_num)]; simp [abs_of_pos hR]] at h
  rw [show (fun x : Space 3 => (R • x) 0 ^ 2) = fun x => R ^ 2 * (x 0 ^ 2) from by
    funext x; simp [Space.smul_apply]; ring] at h
  rw [integral_const_mul, Space.finrank_eq_dim, smul_eq_mul] at h
  field_simp at h; linarith

open Pointwise in
/-- Volume scaling: vol(B(0,R)) = R^3 * vol(B(0,1)). -/
private lemma vol_closedBall_scaling (R : ℝ) (hR : 0 ≤ R) :
    volume.real (Metric.closedBall (0 : Space 3) R) =
    R ^ 3 * volume.real (Metric.closedBall (0 : Space 3) 1) := by
  unfold Measure.real
  rw [show Metric.closedBall (0 : Space 3) R = R • Metric.closedBall (0 : Space 3) 1 from by
    rw [smul_closedBall R 0 (by norm_num)]; simp [abs_of_nonneg hR]]
  rw [Measure.addHaar_smul_of_nonneg _ hR, Space.finrank_eq_dim,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hR _)]

/-- The unit ball second moment: ∫_{B(0,1)} x_0^2 = vol(B(0,1)) / 5. -/
private lemma integral_coord_sq_unit_ball :
    ∫ x in Metric.closedBall (0 : Space 3) 1, x 0 ^ 2 ∂volume =
    volume.real (Metric.closedBall (0 : Space 3) 1) / 5 := by
  have vol_eq : volume.real (Metric.closedBall (0 : Space 3) 1) =
      volume.real (Metric.ball (0 : Space 3) 1) :=
    Measure.addHaar_real_closedBall_eq_addHaar_real_ball volume 0 1
  have dim3 : Module.finrank ℝ (Space 3) = 3 := Space.finrank_eq_dim
  set f : ℝ → ℝ := fun r => if r ≤ 1 then r ^ 2 else 0
  have hf_ioi : ∀ y ∈ Set.Ioi (1 : ℝ), f y = 0 := fun y hy => by
    simp only [f, show ¬(y ≤ 1) from not_le.mpr (Set.mem_Ioi.mp hy), ite_false]
  have int_icc4 : IntegrableOn (fun y : ℝ => y ^ 4) (Set.Icc 0 1) volume :=
    ContinuousOn.integrableOn_compact isCompact_Icc ((continuous_pow 4).continuousOn)
  have eq_ioc_smul : Set.EqOn (fun y : ℝ => y ^ 4)
      (fun y => y ^ (Module.finrank ℝ (Space 3) - 1) • f y) (Set.Ioc 0 1) := fun y hy => by
    change y ^ 4 = y ^ (Module.finrank ℝ (Space 3) - 1) • f y
    rw [dim3]; simp only [f, hy.2, ite_true, smul_eq_mul]; ring
  have eq_ioi_smul : Set.EqOn (fun _ : ℝ => (0 : ℝ))
      (fun y => y ^ (Module.finrank ℝ (Space 3) - 1) • f y) (Set.Ioi 1) := fun y hy => by
    change (0 : ℝ) = y ^ (Module.finrank ℝ (Space 3) - 1) • f y
    rw [dim3, hf_ioi y hy, smul_zero]
  have eq_ioc_mul : Set.EqOn (fun y : ℝ => y ^ 4)
      (fun y => y ^ (3 - 1) * f y) (Set.Ioc 0 1) := fun y hy => by
    change y ^ 4 = y ^ (3 - 1) * f y
    simp only [f, hy.2, ite_true]; ring
  have eq_ioi_mul : Set.EqOn (fun _ : ℝ => (0 : ℝ))
      (fun y => y ^ (3 - 1) * f y) (Set.Ioi 1) := fun y hy => by
    change (0 : ℝ) = y ^ (3 - 1) * f y
    rw [hf_ioi y hy, mul_zero]
  have h_int : Integrable (fun x : Space 3 => f ‖x‖) volume := by
    rw [integrable_fun_norm_addHaar (μ := volume) (E := Space 3),
      ← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact IntegrableOn.union
      ((int_icc4.mono_set Set.Ioc_subset_Icc_self).congr_fun eq_ioc_smul measurableSet_Ioc)
      (integrableOn_zero.congr_fun eq_ioi_smul measurableSet_Ioi)
  have integral_norm_sq_eq : ∫ x in Metric.closedBall (0 : Space 3) 1, ‖x‖ ^ 2 ∂volume =
      3 * volume.real (Metric.ball (0 : Space 3) 1) / 5 := by
    have key := integral_fun_norm_addHaar (μ := volume) (E := Space 3) f
    rw [dim3] at key
    rw [show ∫ x : Space 3, f ‖x‖ ∂volume =
        ∫ x in Metric.closedBall (0 : Space 3) 1, ‖x‖ ^ 2 ∂volume from by
      rw [← integral_indicator measurableSet_closedBall]; congr 1; ext x
      simp only [Set.indicator, Metric.mem_closedBall, dist_zero_right, f]] at key
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => smul_eq_mul _ _)] at key
    rw [show ∫ y in Set.Ioi (0 : ℝ), y ^ (3 - 1) * f y = 1 / 5 from by
      rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one,
        setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
          ((int_icc4.mono_set Set.Ioc_subset_Icc_self).congr_fun eq_ioc_mul measurableSet_Ioc)
          (integrableOn_zero.congr_fun eq_ioi_mul measurableSet_Ioi),
        setIntegral_congr_fun measurableSet_Ioi eq_ioi_mul.symm, integral_zero, add_zero,
        setIntegral_congr_fun measurableSet_Ioc eq_ioc_mul.symm,
        ← intervalIntegral.integral_of_le zero_le_one, integral_pow]; norm_num] at key
    simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_three] at key; linarith
  have sum_eq : ∫ x in Metric.closedBall (0 : Space 3) 1, ‖x‖ ^ 2 ∂volume =
      3 * ∫ x in Metric.closedBall (0 : Space 3) 1, x 0 ^ 2 ∂volume := by
    conv_lhs =>
      rw [setIntegral_congr_fun measurableSet_closedBall (fun x _ => Space.norm_sq_eq x)]
    rw [integral_finset_sum _ (fun i _ => (ContinuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Space 3) 1) (by fun_prop)).integrable)]
    simp_rw [integral_coord_sq_closedBall_eq _ 0 1]
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [vol_eq]; linarith [integral_norm_sq_eq, sum_eq]

/-- Key integral identity: ∫_{B(0,R)} x_0^2 dx = vol(B(0,R)) * R^2 / 5 for Space 3.
This is the fundamental second-moment integral for a uniform 3-dimensional ball. -/
lemma integral_coord_sq_closedBall_value (R : ℝ≥0) (hr : R ≠ 0) :
    ∫ x in Metric.closedBall (0 : Space 3) R, x 0 ^ 2 ∂volume =
    volume.real (Metric.closedBall (0 : Space 3) R) * (R : ℝ) ^ 2 / 5 := by
  have hR : (0 : ℝ) < R := by exact_mod_cast (show (R : ℝ) ≠ 0 by simpa using hr).symm.lt_of_le R.2
  rw [integral_coord_sq_closedBall_scaling R hR,
      vol_closedBall_scaling R hR.le,
      integral_coord_sq_unit_ball]
  ring

end InertiaTensorHelpers

/-- The moment of inertia tensor of a solid sphere through its center of mass is `2/5 m R^2 * I`. -/
lemma solidSphere_inertiaTensor (m R : ℝ≥0) (hr : R ≠ 0) :
    (solidSphere 3 m R).inertiaTensor = (2/5 * m.1 * R.1^2) • (1 : Matrix _ _ _) := by
  ext i j
  simp only [inertiaTensor, solidSphere, LinearMap.coe_mk, AddHom.coe_mk, ContMDiffMap.coeFn_mk,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true, one_mul, mul_one]
    have hvol_ne : volume.real (Metric.closedBall (0 : Space 3) (R : ℝ)) ≠ 0 := by
      refine (measureReal_ne_zero_iff ?_).mpr ?_
      · apply Space.volume_closedBall_ne_top
      · exact Space.volume_closedBall_ne_zero _ _
          (by exact_mod_cast (show (R : ℝ) ≠ 0 by simpa using hr).symm.lt_of_le R.2)
    rw [show (fun x : Space 3 => ∑ k : Fin 3, x k ^ 2 - x i * x i) =
      fun x => ∑ k : Fin 3, x k ^ 2 - x i ^ 2 from by funext x; ring]
    rw [integral_sub
      (IntegrableOn.integrable (ContinuousOn.integrableOn_compact
        (isCompact_closedBall 0 _) (by fun_prop)))
      (IntegrableOn.integrable (ContinuousOn.integrableOn_compact
        (isCompact_closedBall 0 _) (by fun_prop)))]
    rw [integral_finset_sum _ (fun k _ => IntegrableOn.integrable
      (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 _) (by fun_prop)))]
    rw [Finset.sum_eq_card_nsmul (s := Finset.univ)
      (b := ∫ x in Metric.closedBall (0 : Space 3) (R : ℝ), x 0 ^ 2 ∂volume)
      (fun k _ => integral_coord_sq_closedBall_eq k 0 _)]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [integral_coord_sq_closedBall_eq i 0, integral_coord_sq_closedBall_value R hr]
    field_simp; norm_num; ring
  · simp only [hij, ite_false, zero_mul, mul_zero]
    rw [show (fun x : Space 3 => (0 : ℝ) - x i * x j) = fun x => -(x i * x j) from
      by funext; ring]
    rw [integral_neg, integral_coord_mul_closedBall_eq_zero hij]
    simp

end RigidBody
