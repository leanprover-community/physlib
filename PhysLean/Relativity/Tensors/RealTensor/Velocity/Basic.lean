/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
/-!

# Lorentz Velocities

In this module we define Lorentz velocities to be
Lorentz vectors which have norm equal to one and which are future-directed.

-/

open TensorProduct

namespace Lorentz
open Vector

/-- A Lorentz Velocity is a Lorentz vector which has norm equal to one
  and which is future-directed. -/
def Velocity (d : ℕ := 3) : Set (Vector d) := fun v => ⟪v, v⟫ₘ = (1 : ℝ)
  ∧ 0 < v.timeComponent

namespace Velocity

variable {d : ℕ}

/-- The instance of a topological space on `Velocity d` defined as the subspace topology. -/
instance : TopologicalSpace (Velocity d) := instTopologicalSpaceSubtype

@[ext]
lemma ext {v w : Velocity d} (h : v.1 = w.1) : v = w := by
  exact SetCoe.ext h

lemma mem_iff {v : Vector d} : v ∈ Velocity d ↔ ⟪v, v⟫ₘ = (1 : ℝ) ∧ 0 < v.timeComponent := by
  rfl

@[simp]
lemma minkowskiProduct_self_eq_one (v : Velocity d) : ⟪v.1, v.1⟫ₘ = (1 : ℝ) := v.2.1

@[simp]
lemma timeComponent_pos (v : Velocity d) : 0 < v.1.timeComponent := v.2.2

@[simp]
lemma timeComponent_nonneg (v : Velocity d) : 0 ≤ v.1.timeComponent := by
  linarith [timeComponent_pos v]

@[simp]
lemma timeComponent_abs (v : Velocity d) :
    |v.1.timeComponent| = v.1.timeComponent := by
  simp

lemma norm_spatialPart_le_timeComponent (v : Velocity d) :
    ‖v.1.spatialPart‖ ≤ ‖v.1.timeComponent‖ := by
  rw [← sq_le_sq₀ (norm_nonneg v.1.spatialPart) (norm_nonneg v.1.timeComponent)]
  trans 1 + ‖v.1.spatialPart‖ ^ 2
  · linarith
  trans ⟪v.1, v.1⟫ₘ + ‖v.1.spatialPart‖ ^ 2
  · rw [minkowskiProduct_self_eq_one]
  · rw [minkowskiProduct_self_eq_timeComponent_spatialPart]
    simp

lemma norm_spatialPart_sq_eq (v : Velocity d) :
    ‖v.1.spatialPart‖ ^ 2 = (v.1 (Sum.inl 0))^2 - 1 := by
  rw [← minkowskiProduct_self_eq_one v]
  rw [minkowskiProduct_self_eq_timeComponent_spatialPart]
  simp [timeComponent]

lemma zero_le_minkowskiProduct (u v : Velocity d) :
    0 ≤ ⟪u.1, v.1⟫ₘ := by
  trans ‖u.1.timeComponent‖ * ‖v.1.timeComponent‖ - ‖u.1.spatialPart‖ * ‖v.1.spatialPart‖
  · rw [sub_nonneg]
    apply mul_le_mul
    · exact norm_spatialPart_le_timeComponent u
    · exact norm_spatialPart_le_timeComponent v
    · exact norm_nonneg v.1.spatialPart
    · exact norm_nonneg u.1.timeComponent
  rw [minkowskiProduct_eq_timeComponent_spatialPart]
  apply sub_le_sub
  · simp
  · exact real_inner_le_norm u.1.spatialPart v.1.spatialPart

lemma one_add_minkowskiProduct_ne_zero (u v : Velocity d) :
    1 + ⟪u.1, v.1⟫ₘ ≠ 0 := by
  linarith [zero_le_minkowskiProduct u v]

lemma minkowskiProduct_continuous_snd (u : Vector d) :
    Continuous fun (x : Velocity d) => ⟪u, x.1⟫ₘ := by
  fun_prop

@[fun_prop]
lemma minkowskiProduct_continuous_fst (u : Vector d) :
    Continuous fun (x : Velocity d) => ⟪x.1, u⟫ₘ := by
  have h1 : (fun (x : Velocity d) => ⟪x.1, u⟫ₘ) =
    (fun (x : Velocity d) => ⟪u, x.1⟫ₘ) := by
    ext x
    rw [minkowskiProduct_symm]
  rw [h1]
  exact minkowskiProduct_continuous_snd u

/-!

# Zero

-/

/-- The `Velocity d` which has all space components zero. -/
noncomputable def zero : Velocity d := ⟨Vector.basis (Sum.inl 0),
  by simp [mem_iff, minkowskiMatrix.inl_0_inl_0]⟩

noncomputable instance : Zero (Velocity d) := ⟨zero⟩

@[simp]
lemma zero_timeComponent : (0 : Velocity d).1.timeComponent = 1 := by
  change (Vector.basis (Sum.inl 0)).timeComponent = 1
  simp

/-- A continuous path from a velocity `u` to the zero velocity. -/
noncomputable def pathFromZero (u : Velocity d) : Path zero u where
  toFun t := ⟨(√(1 + t ^ 2 * ‖u.1.spatialPart‖ ^ 2) - u.1 (Sum.inl 0) * t) •
      zero.1 + (t : ℝ) • u.1,
    by
      rw [mem_iff]
      apply And.intro
      · let x := (√(1 + t ^ 2 * ‖u.1.spatialPart‖ ^ 2) - u.1 (Sum.inl 0) * t)
        calc _
          _ = ⟪x • zero.1 + (t : ℝ) • u.1, x • zero.1 + (t : ℝ) • u.1⟫ₘ := by rfl
          _ = x ^ 2 + (t : ℝ) ^ 2 + 2 * x * (t : ℝ) * u.1 (Sum.inl 0) := by
            simp only [zero, Fin.isValue, map_add, map_smul, ContinuousLinearMap.add_apply,
              ContinuousLinearMap.coe_smul', Pi.smul_apply, minkowskiProduct_basis_right,
              minkowskiMatrix.inl_0_inl_0, basis_apply, ↓reduceIte, mul_one, smul_eq_mul, one_mul,
              minkowskiProduct_basis_left, minkowskiProduct_self_eq_one]
            ring
        simp only [Fin.isValue, x]
        ring_nf
        rw [Real.sq_sqrt, norm_spatialPart_sq_eq]
        ring
        · apply add_nonneg
          · exact zero_le_one' ℝ
          · apply mul_nonneg
            · exact sq_nonneg _
            · exact sq_nonneg _
      · simp only [timeComponent, Fin.isValue, zero, apply_add, apply_smul, basis_apply,
        ↓reduceIte, mul_one]
        ring_nf
        refine Real.sqrt_pos_of_pos ?_
        apply add_pos_of_pos_of_nonneg
        · exact Real.zero_lt_one
        · apply mul_nonneg
          · exact sq_nonneg _
          · exact sq_nonneg _⟩
  continuous_toFun := by
    fun_prop
  source' := by
    simp
  target' := by
    ext
    simp only [Set.Icc.coe_one,
      one_pow, one_mul, Fin.isValue, mul_one, one_smul, add_eq_right, smul_eq_zero]
    left
    rw [norm_spatialPart_sq_eq]
    simp

/-!

## Topology

-/

lemma isPathConnected : IsPathConnected (@Set.univ (Velocity d)) := by
  use (zero (d := d))
  apply And.intro trivial ?_
  intro y a
  use pathFromZero (d := d) y
  exact fun _ => a

end Velocity

end Lorentz
