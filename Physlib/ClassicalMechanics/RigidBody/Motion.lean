/-
Copyright (c) 2026 Giuseppe Sorge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuseppe Sorge
-/
module

public import Physlib.ClassicalMechanics.RigidBody.Basic
public import Physlib.SpaceAndTime.Time.MatrixDerivatives
/-!

# Rigid body motion

The static `RigidBody` records a body-fixed mass distribution. To describe a rigid body *in
motion* we record, in addition, the trajectory of its centre of mass in the inertial frame and the
body's time-dependent orientation (a rotation about the centre of mass).

From this configuration we define the velocity of the centre of mass and the body's linear
momentum. The reference point is taken to be the centre of mass, following the decomposition of
a rigid motion into a translation of the centre of mass plus a rotation about it.

## References

* Landau and Lifshitz, Mechanics, Section 32. [ref: landau_mechanics]
-/

@[expose] public section

open Time Manifold Matrix RigidBody InnerProductSpace
open Space (cmap cmap_apply)

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- A motion of a rigid body in `d`-dimensional space: the body together with the inertial-frame
trajectory of its centre of mass and its time-dependent orientation (a rotation about the centre
of mass). -/
structure RigidBodyMotion (d : ℕ) extends RigidBody d where
  /-- The position of the centre of mass in the inertial frame as a function of time. -/
  comTrajectory : Time → Space d
  /-- The orientation of the body, a rotation about the centre of mass, as a function of time. -/
  orientation : Time → Matrix.specialOrthogonalGroup (Fin d) ℝ

namespace RigidBodyMotion

/-- The orientation matrix is special orthogonal, so `R Rᵀ = 1`. -/
lemma orientation_mul_transpose {d : ℕ} (M : RigidBodyMotion d) (t : Time) :
    (M.orientation t).1 * ((M.orientation t).1)ᵀ = 1 :=
  (mem_orthogonalGroup_iff (Fin d) ℝ).mp
    (mem_specialOrthogonalGroup_iff.mp (M.orientation t).2).1

/-- The velocity of the centre of mass of a rigid body in motion, defined as the time-derivative
of its centre-of-mass trajectory. This is the velocity `V` in the Landau–Lifshitz decomposition
`v = V + Ω × r` of the velocity of a point of the body. -/
noncomputable def centerOfMassVelocity {d : ℕ} (M : RigidBodyMotion d) :
    Time → EuclideanSpace ℝ (Fin d) :=
  ∂ₜᵥ M.comTrajectory

lemma centerOfMassVelocity_eq {d : ℕ} (M : RigidBodyMotion d) :
    M.centerOfMassVelocity = ∂ₜᵥ M.comTrajectory := rfl

/-- A rigid body whose centre of mass is stationary has zero centre-of-mass velocity. -/
lemma centerOfMassVelocity_of_comTrajectory_const {d : ℕ} (M : RigidBodyMotion d) (c : Space d)
    (h : M.comTrajectory = fun _ => c) : M.centerOfMassVelocity = 0 := by
  rw [centerOfMassVelocity_eq, h]
  funext t
  exact Time.derivVec_const c

/-- The linear momentum of a rigid body in motion: the total mass times the velocity of the
centre of mass. -/
noncomputable def linearMomentum {d : ℕ} (M : RigidBodyMotion d) :
    Time → EuclideanSpace ℝ (Fin d) :=
  fun t => M.mass • M.centerOfMassVelocity t

lemma linearMomentum_eq {d : ℕ} (M : RigidBodyMotion d) :
    M.linearMomentum = fun t => M.mass • M.centerOfMassVelocity t := rfl

TODO "Define an action of the rotation and translation groups on `RigidBodyMotion`, and recover
  `displacement` as the composite of those group actions."

/-- The rigid displacement carrying the body frame into the inertial frame at time `t`: the
rotation `orientation t` about the centre of mass, followed by the translation placing the centre
of mass at `comTrajectory t`. -/
noncomputable def displacement {d : ℕ} (M : RigidBodyMotion d) (t : Time) : Space d → Space d :=
  fun y => ⟨fun k => ∑ j, (M.orientation t).val k j * (y j - M.centerOfMass j) +
    M.comTrajectory t k⟩

/-- The `k`-th coordinate of the rigid displacement applied to `y`. -/
lemma displacement_apply {d : ℕ} (M : RigidBodyMotion d) (t : Time) (y : Space d) (k : Fin d) :
    M.displacement t y k =
      (∑ j, (M.orientation t).val k j * (y j - M.centerOfMass j)) + M.comTrajectory t k := rfl

lemma displacement_contDiff {d : ℕ} (M : RigidBodyMotion d) (t : Time) :
    ContDiff ℝ ⊤ (M.displacement t) := by
  unfold displacement
  fun_prop

/-- Rotating the body-frame position of `y` relative to the centre of mass gives its
inertial-frame position relative to the moving centre of mass:
`R(t) (y − c) = displacement t y − comTrajectory t`. -/
lemma orientation_mulVec_sub_centerOfMass {d : ℕ} (M : RigidBodyMotion d) (t : Time)
    (y : Space d) :
    (M.orientation t).1 *ᵥ (fun j => y j - M.centerOfMass j)
      = fun j => M.displacement t y j - M.comTrajectory t j := by
  funext k
  show ((M.orientation t).1 *ᵥ fun j => y j - M.centerOfMass j) k
    = M.displacement t y k - M.comTrajectory t k
  rw [eq_sub_iff_add_eq, displacement_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The mass distribution of the rigid body in motion at time `t`: the pushforward of the
body-fixed mass distribution along the rigid displacement, acting on a test function `f` by
`f ↦ ρ (f ∘ displacement t)`. -/
noncomputable def massDistribution {d : ℕ} (M : RigidBodyMotion d) (t : Time) : RigidBody d where
  ρ :=
    { toFun := fun f => M.ρ (f.comp ⟨M.displacement t, (M.displacement_contDiff t).contMDiff⟩)
      map_add' := fun f g => by rw [ContMDiffMap.add_comp, map_add]
      map_smul' := fun r f => by rw [ContMDiffMap.smul_comp, map_smul, RingHom.id_apply] }

/-- The motion preserves the total mass: the mass distribution at any time `t` has the same total
mass as the body. -/
@[simp]
lemma massDistribution_mass {d : ℕ} (M : RigidBodyMotion d) (t : Time) :
    (M.massDistribution t).mass = M.mass := by
  simp only [RigidBody.mass, massDistribution, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1

/-- Evaluation commutes with finite sums of smooth functions. -/
private lemma contMDiffMap_sum_apply {d : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → C^⊤⟮𝓘(ℝ, Space d), Space d; 𝓘(ℝ, ℝ), ℝ⟯) (y : Space d) :
    (∑ j ∈ s, f j) y = ∑ j ∈ s, f j y := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha, ContMDiffMap.coe_add, Pi.add_apply, ih]

set_option backward.isDefEq.respectTransparency false in
/-- The centre of mass of the moving mass distribution tracks the prescribed trajectory: for a
body of nonzero mass, the centre of mass of `massDistribution M t` is exactly `comTrajectory t`.
This is the decisive check that `comTrajectory` and `orientation` are wired correctly in
`RigidBodyMotion`. -/
lemma massDistribution_centerOfMass {d : ℕ} (M : RigidBodyMotion d) (t : Time) (h : M.mass ≠ 0) :
    (M.massDistribution t).centerOfMass = M.comTrajectory t := by
  ext i
  have hdecomp :
      ContMDiffMap.comp (cmap (fun x => x i) (by fun_prop))
          ⟨M.displacement t, (M.displacement_contDiff t).contMDiff⟩
        = (∑ j, (M.orientation t).val i j •
              cmap (fun y => y j - M.centerOfMass j) (by fun_prop))
            + M.comTrajectory t i • (1 : C^⊤⟮𝓘(ℝ, Space d), Space d; 𝓘(ℝ, ℝ), ℝ⟯) := by
    ext y
    simp only [ContMDiffMap.comp_apply, cmap_apply, ContMDiffMap.coeFn_mk, displacement_apply,
      ContMDiffMap.coe_add, ContMDiffMap.coe_smul, ContMDiffMap.coe_one, Pi.add_apply,
      Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, contMDiffMap_sum_apply]
  have key : (M.massDistribution t).ρ (cmap (fun x => x i) (by fun_prop))
      = M.comTrajectory t i * M.mass := by
    simp only [massDistribution, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hdecomp, map_add, map_sum, map_smul, M.rho_one]
    simp only [map_smul, M.rho_coord_sub_centerOfMass h, smul_eq_mul, mul_zero,
      Finset.sum_const_zero, zero_add]
  rw [show (M.massDistribution t).centerOfMass i
      = (1 / (M.massDistribution t).mass) •
          (M.massDistribution t).ρ (cmap (fun x => x i) (by fun_prop)) from rfl,
    massDistribution_mass, key, smul_eq_mul, mul_comm, mul_one_div, mul_div_assoc, div_self h,
    mul_one]

/-- The velocity of the material point `y` of a rigid body in motion: the inertial-frame time
derivative of the trajectory `s ↦ displacement s y` of that point. -/
noncomputable def velocity {d : ℕ} (M : RigidBodyMotion d) (y : Space d) :
    Time → EuclideanSpace ℝ (Fin d) :=
  fun t => ∂ₜᵥ (fun s => M.displacement s y) t

lemma velocity_eq {d : ℕ} (M : RigidBodyMotion d) (y : Space d) (t : Time) :
    M.velocity y t = ∂ₜᵥ (fun s => M.displacement s y) t := rfl

/-- The `i`-th component of the velocity of a body point is the time derivative of the `i`-th
coordinate of its inertial-frame trajectory. -/
lemma velocity_apply {d : ℕ} (M : RigidBodyMotion d) (y : Space d) (t : Time) (i : Fin d)
    (hd : Differentiable ℝ (fun s => M.displacement s y)) :
    M.velocity y t i = ∂ₜ (fun s => M.displacement s y i) t := by
  rw [velocity_eq]
  exact derivVec_space hd t i

/-- The material point at the centre of mass moves with the centre-of-mass velocity, for any
motion: `v(centreOfMass) = V`. This is the velocity counterpart of `massDistribution_centerOfMass`.
-/
lemma velocity_centerOfMass {d : ℕ} (M : RigidBodyMotion d) :
    M.velocity M.centerOfMass = M.centerOfMassVelocity := by
  funext t
  rw [velocity_eq, centerOfMassVelocity_eq]
  congr 1
  funext s
  ext k
  rw [displacement_apply]
  simp

/-- A rigid body in pure translation (constant orientation) has every point moving with the
centre-of-mass velocity: `v = V`. -/
lemma velocity_of_orientation_const {d : ℕ} (M : RigidBodyMotion d) (y : Space d)
    (R : Matrix.specialOrthogonalGroup (Fin d) ℝ) (h : M.orientation = fun _ => R) :
    M.velocity y = M.centerOfMassVelocity := by
  funext t
  rw [velocity_eq, centerOfMassVelocity_eq]
  have hdisp : (fun s => M.displacement s y)
      = fun s => (WithLp.toLp 2 fun k => ∑ j, R.1 k j * (y j - M.centerOfMass j))
          +ᵥ M.comTrajectory s := by
    funext s
    ext k
    rw [displacement_apply, h]
    simp
  rw [hdisp]
  simp only [Time.derivVec_eq, vadd_vsub_vadd_cancel_left]

/-- The velocity of a body point decomposes as `v = Ṙ (y − c) + V`: the rate of change of the
orientation acting on the body-frame position, plus the centre-of-mass velocity. -/
lemma velocity_eq_deriv_orientation {d : ℕ} (M : RigidBodyMotion d) (y : Space d) (t : Time)
    (i : Fin d) (hR : Differentiable ℝ (fun s => (M.orientation s).1))
    (hX : Differentiable ℝ M.comTrajectory) :
    M.velocity y t i
      = (∂ₜ (fun s => (M.orientation s).1) t *ᵥ fun j => y j - M.centerOfMass j) i
        + M.centerOfMassVelocity t i := by
  have hentry : ∀ a b : Fin d, Differentiable ℝ (fun s => (M.orientation s).1 a b) := fun a b =>
    ((Matrix.entryLinearMap ℝ ℝ a b).toContinuousLinearMap).differentiable.comp hR
  have hXcoord : ∀ k : Fin d, Differentiable ℝ (fun s => M.comTrajectory s k) := fun k =>
    (Space.eval_differentiable k).comp hX
  have hd : Differentiable ℝ (fun s => M.displacement s y) := by
    have hcoord : ∀ k : Fin d, Differentiable ℝ (fun s => M.displacement s y k) := by
      intro k
      simp only [displacement_apply]
      exact (Differentiable.fun_sum
        (fun j _ => (hentry k j).mul_const (y j - M.centerOfMass j))).add (hXcoord k)
    exact Space.mk_differentiable.comp (differentiable_pi.mpr hcoord)
  have hmv : (∂ₜ (fun s => (M.orientation s).1) t *ᵥ fun j => y j - M.centerOfMass j) i
      = ∑ j, (∂ₜ (fun s => (M.orientation s).1) t) i j * (y j - M.centerOfMass j) := rfl
  rw [M.velocity_apply y t i hd]
  simp only [displacement_apply]
  rw [Time.deriv_add (fun s => ∑ j, (M.orientation s).1 i j * (y j - M.centerOfMass j))
      (fun s => M.comTrajectory s i)
      ((Differentiable.fun_sum
        fun j _ => (hentry i j).mul_const (y j - M.centerOfMass j)) t) ((hXcoord i) t),
    Time.deriv_fun_sum Finset.univ
      (fun j s => (M.orientation s).1 i j * (y j - M.centerOfMass j))
      (fun j _ => ((hentry i j).mul_const (y j - M.centerOfMass j)) t),
    Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) =>
      Time.deriv_mul_const (fun s => (M.orientation s).1 i j)
        (y j - M.centerOfMass j) ((hentry i j) t))]
  simp only [Time.deriv_matrix_apply (fun s => (M.orientation s).1) t (hR t)]
  rw [hmv, ← Time.derivVec_space hX t i, ← centerOfMassVelocity_eq]

/-- The closed form `Ṙ(t) (y − c) + V(t)` of the velocity of the body point `y` at time `t`.
Unlike `velocity` — whose junk values on non-differentiable motions need not vary continuously
with `y` — it is polynomial in `y` for any motion, so its squared speed can be bundled as the
smooth integrand of the total kinetic energy; for differentiable motions the two agree, see
`velocityClosedForm_eq_velocity`. -/
noncomputable def velocityClosedForm {d : ℕ} (M : RigidBodyMotion d) (t : Time) (y : Space d) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (∂ₜ (fun s => (M.orientation s).1) t *ᵥ fun j => y j - M.centerOfMass j)
    + M.centerOfMassVelocity t

/-- The `i`-th coordinate of the closed-form velocity. -/
lemma velocityClosedForm_apply {d : ℕ} (M : RigidBodyMotion d) (t : Time) (y : Space d)
    (i : Fin d) :
    M.velocityClosedForm t y i
      = (∂ₜ (fun s => (M.orientation s).1) t *ᵥ fun j => y j - M.centerOfMass j) i
        + M.centerOfMassVelocity t i := by
  simp only [velocityClosedForm, PiLp.add_apply]

/-- The closed-form velocity as a plain vector-valued function of the coordinates of `y`. -/
lemma velocityClosedForm_val {d : ℕ} (M : RigidBodyMotion d) (t : Time) (y : Space d) :
    (M.velocityClosedForm t y : Fin d → ℝ)
      = (∂ₜ (fun s => (M.orientation s).1) t *ᵥ fun j => y j - M.centerOfMass j)
        + (M.centerOfMassVelocity t : Fin d → ℝ) := by
  funext i
  rw [Pi.add_apply]
  exact M.velocityClosedForm_apply t y i

/-- For a differentiable motion the closed-form velocity is the honest point velocity. -/
lemma velocityClosedForm_eq_velocity {d : ℕ} (M : RigidBodyMotion d) (t : Time)
    (hR : Differentiable ℝ (fun s => (M.orientation s).1))
    (hX : Differentiable ℝ M.comTrajectory) (y : Space d) :
    M.velocityClosedForm t y = M.velocity y t := by
  ext i
  rw [velocityClosedForm_apply, ← M.velocity_eq_deriv_orientation y t i hR hX]

/-- The squared speed of a body point, in closed form, is a smooth function of the point. -/
lemma contDiff_velocityClosedForm_inner {d : ℕ} (M : RigidBodyMotion d) (t : Time) :
    ContDiff ℝ ⊤ fun y : Space d => (⟪M.velocityClosedForm t y, M.velocityClosedForm t y⟫_ℝ) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    velocityClosedForm_apply, Matrix.mulVec, dotProduct]
  fun_prop

end RigidBodyMotion
