/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
/-!

# Lorentz Velocities

In this module we define Lorentz velocities to be
Lorentz vectors which have norm equal to one and which are future-directed.

-/

@[expose] public section

open TensorProduct

namespace Lorentz
open _root_.Lorentz.Vector

/-- A Lorentz Velocity is a Lorentz vector which has norm equal to one
  and which is future-directed. -/
def Velocity (d : ℕ := 3) : Set (Vector d) := {v | ⟪v, v⟫ₘ = (1 : ℝ)
  ∧ 0 < v.timeComponent}

namespace Velocity

variable {d : ℕ}

/-- The instance of a topological space on `Velocity d` defined as the subspace topology. -/
noncomputable instance : TopologicalSpace (Velocity d) := instTopologicalSpaceSubtype

@[ext]
lemma ext {v w : Velocity d} (h : v.1 = w.1) : v = w := by
  exact SetCoe.ext h

lemma mem_iff {v : Vector d} : v ∈ Velocity d ↔ ⟪v, v⟫ₘ = (1 : ℝ) ∧ 0 < v.timeComponent := by
  rfl

@[simp]
lemma minkowskiProduct_self_eq_one (v : Velocity d) : ⟪v.1, v.1⟫ₘ = (1 : ℝ) := (mem_iff.1 v.2).1

@[simp]
lemma timeComponent_pos (v : Velocity d) : 0 < v.1.timeComponent := (mem_iff.1 v.2).2

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

/-- The unit future four-velocity with spatial part `p` and time component
`Real.sqrt (1 + ‖p‖ ^ 2)`. The spatial part is unrestricted. -/
noncomputable def ofSpatialPart (p : EuclideanSpace ℝ (Fin d)) : Velocity d :=
  ⟨fun μ => Sum.elim (fun _ => Real.sqrt (1 + ‖p‖ ^ 2)) (fun i => p i) μ, by
    constructor
    · rw [minkowskiProduct_self_eq_sq_sub]
      have hsp : Vector.spatialPart (fun μ => Sum.elim (fun _ => Real.sqrt (1 + ‖p‖ ^ 2))
          (fun i => p i) μ : Vector d) = p := by
        ext i
        rfl
      rw [hsp]
      change (Real.sqrt (1 + ‖p‖ ^ 2)) ^ 2 - ‖p‖ ^ 2 = 1
      rw [Real.sq_sqrt (by positivity)]
      ring
    · change 0 < Real.sqrt (1 + ‖p‖ ^ 2)
      positivity⟩

@[simp]
lemma spatialPart_ofSpatialPart (p : EuclideanSpace ℝ (Fin d)) :
    (ofSpatialPart p).1.spatialPart = p := by
  ext i
  rfl

@[simp]
lemma timeComponent_ofSpatialPart (p : EuclideanSpace ℝ (Fin d)) :
    (ofSpatialPart p).1.timeComponent = Real.sqrt (1 + ‖p‖ ^ 2) := rfl

/-- A future unit four-velocity is determined by its spatial part. -/
@[simp]
lemma ofSpatialPart_spatialPart (u : Velocity d) : ofSpatialPart u.1.spatialPart = u := by
  apply Velocity.ext
  apply Vector.eq_of_apply_eq
  intro μ
  rcases μ with t | i
  · fin_cases t
    change Real.sqrt (1 + ‖u.1.spatialPart‖ ^ 2) = u.1.timeComponent
    rw [norm_spatialPart_sq_eq]
    simp only [add_sub_cancel]
    exact Real.sqrt_sq (timeComponent_nonneg u)
  · have h := congrArg (fun q : EuclideanSpace ℝ (Fin d) => q i)
      (spatialPart_ofSpatialPart u.1.spatialPart)
    exact h

/-- The spatial-coordinate parametrization of future unit four-velocities is continuous. -/
@[fun_prop]
lemma continuous_ofSpatialPart : Continuous (ofSpatialPart (d := d)) := by
  apply Continuous.subtype_mk
  apply Vector.continuous_of_apply
  intro μ
  rcases μ with t | i
  · change Continuous (fun p : EuclideanSpace ℝ (Fin d) => Real.sqrt (1 + ‖p‖ ^ 2))
    fun_prop
  · change Continuous (fun p : EuclideanSpace ℝ (Fin d) => p i)
    fun_prop

/-- A bound on the proper norm of a vector orthogonal to a unit future
four-velocity controls its spatial norm in the chosen frame. -/
lemma norm_spatialPart_le_of_orthogonal (u : Velocity d) (A : Vector d)
    {C : ℝ} (hC : 0 ≤ C) (horth : ⟪u.1, A⟫ₘ = 0) (hacc : -⟪A, A⟫ₘ ≤ C ^ 2) :
    ‖A.spatialPart‖ ≤ C * u.1.timeComponent := by
  have hunit := minkowskiProduct_self_eq_one u
  rw [Vector.minkowskiProduct_self_eq_sq_sub] at hunit
  rw [Vector.minkowskiProduct_eq_timeComponent_spatialPart, sub_eq_zero] at horth
  rw [Vector.minkowskiProduct_self_eq_sq_sub] at hacc
  have hcs := real_inner_mul_inner_self_le u.1.spatialPart A.spatialPart
  simp only [real_inner_self_eq_norm_sq] at hcs
  have horthsq := congrArg (fun x : ℝ => x ^ 2) horth
  have hacc' := mul_le_mul_of_nonneg_left hacc (sq_nonneg u.1.timeComponent)
  have hunit' := congrArg (fun x : ℝ => x * ‖A.spatialPart‖ ^ 2) hunit
  have hb : ‖A.spatialPart‖ ^ 2 ≤ C ^ 2 * u.1.timeComponent ^ 2 := by
    nlinarith [horthsq, hunit']
  apply (sq_le_sq₀ (norm_nonneg A.spatialPart)
    (mul_nonneg hC (timeComponent_nonneg u))).mp
  nlinarith [hb]

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
            simp only [zero, Fin.isValue, map_add, map_smul, _root_.add_apply,
              FunLike.coe_smul, Pi.smul_apply, minkowskiProduct_basis_right,
              minkowskiMatrix.inl_0_inl_0, basis_apply, ↓reduceIte, mul_one, smul_eq_mul, one_mul,
              minkowskiProduct_basis_left, minkowskiProduct_self_eq_one]
            ring
        simp only [Fin.isValue, x]
        ring_nf
        rw [Real.sq_sqrt, norm_spatialPart_sq_eq]
        · ring
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
    ext1
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
