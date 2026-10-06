/-
Copyright (c) 2026 Giuseppe Sorge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuseppe Sorge
-/
module

public import Physlib.ClassicalMechanics.RigidBody.Motion
public import Physlib.Mathematics.Modules.CrossProductMatrix
/-!

# The angular velocity of a rigid body

For a rigid body in motion the orientation `R(t) = orientation t` is a time-dependent rotation. Its
instantaneous rate of change is encoded by the *angular velocity tensor*
`Ω(t) = Ṙ(t) R(t)ᵀ`, the antisymmetric tensor `Ω` appearing in the Landau–Lifshitz decomposition
`v = V + Ω × r` of the velocity of a point of the body.

A basic consistency check is that `Ω` is skew-symmetric, `Ωᵀ = -Ω` (equivalently `Ω ∈ 𝔰𝔬(d)`); this
follows by differentiating the orthogonality identity `R Rᵀ = 1`. The general product and transpose
rules for time derivatives of matrices used for this live in
`Physlib.SpaceAndTime.Time.MatrixDerivatives`.

In three dimensions the skew-symmetric tensor `Ω` is dual to the *angular velocity vector*
`ω(t) = Ωᵛ` via the hat map (`Physlib.Mathematics.Modules.CrossProductMatrix`), with
`[ω]ₓ = Ω`; `ω` is the angular velocity proper, appearing in the decomposition `v = V + ω × r`
as an honest cross product.

The angular velocity can equally be expressed in the *body frame*: the moving coordinate system
rigidly attached to the body, with origin at the centre of mass and axes rotating with the body,
in which every material point has time-independent coordinates. The orientation `R(t)` is
precisely the rotational part of the change of frame: a point fixed at position `a` in the body
frame sits at `r = R(t) a` relative to the centre of mass in the lab frame (the inertial frame in
which the trajectories of `RigidBodyMotion` are written), and a vector with lab-frame components
`u` has body-frame components `R(t)ᵀ u`. The body frame is in general *not* inertial — it rotates
with the body, and its origin follows the (generally accelerating) centre of mass — but it is the
natural setting for the inertia tensor and Euler's equations, since the mass distribution, and
with it the inertia tensor, is time-independent in body-fixed axes.

The *body-frame angular velocity tensor* `Ω_body(t) = R(t)ᵀ Ṙ(t)` is defined directly from the
orientation, mirroring the spatial `Ω = Ṙ Rᵀ` rather than being derived from it — the two tensors
are the derivative `Ṙ` translated back to the identity from the two sides — and they are related
by conjugation, `Ω_body = Rᵀ Ω R`. The body-frame tensor is again skew-symmetric; in three
dimensions its dual is the *body-frame angular velocity vector* `ω_body = Ω_bodyᵛ`, the angular
velocity `ω` resolved along the body-fixed axes, `ω_body = Rᵀ ω`.

## References

* Landau and Lifshitz, Mechanics, Sections 31 and 32. [ref: landau_mechanics]
-/

@[expose] public section

open Time Manifold Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace RigidBodyMotion

variable {d : ℕ}

/-- The angular velocity tensor `Ω(t) = Ṙ(t) R(t)ᵀ` of a rigid body in motion, where
`R(t) = orientation t`. It is the antisymmetric tensor `Ω` in the Landau–Lifshitz decomposition
`v = V + Ω × r` of the velocity of a point of the body. -/
noncomputable def angularVelocityTensor (M : RigidBodyMotion d) (t : Time) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∂ₜ (fun s => (M.orientation s).1) t * ((M.orientation t).1)ᵀ

lemma angularVelocityTensor_eq (M : RigidBodyMotion d) (t : Time) :
    M.angularVelocityTensor t = ∂ₜ (fun s => (M.orientation s).1) t * ((M.orientation t).1)ᵀ :=
  rfl

/-- The angular velocity tensor is skew-symmetric, `Ωᵀ = -Ω`: it lies in the Lie algebra `𝔰𝔬(d)`.
This is the litmus check that `Ω = Ṙ Rᵀ` is a genuine angular-velocity tensor, and follows by
differentiating the orthogonality identity `R Rᵀ = 1`. -/
lemma angularVelocityTensor_transpose (M : RigidBodyMotion d) (t : Time)
    (hR : DifferentiableAt ℝ (fun s => (M.orientation s).1) t) :
    (M.angularVelocityTensor t)ᵀ = - M.angularVelocityTensor t := by
  have hconst : (fun s => (M.orientation s).1 * ((M.orientation s).1)ᵀ)
      = fun _ => (1 : Matrix (Fin d) (Fin d) ℝ) := by
    funext s
    exact M.orientation_mul_transpose s
  have hderiv0 : ∂ₜ (fun s => (M.orientation s).1 * ((M.orientation s).1)ᵀ) t = 0 := by
    rw [hconst]
    exact Time.deriv_const 1
  have hprod := Time.deriv_matrix_mul (fun s => (M.orientation s).1)
    (fun s => ((M.orientation s).1)ᵀ) t hR hR.matrix_transpose
  rw [Time.deriv_matrix_transpose (fun s => (M.orientation s).1) t hR, hderiv0] at hprod
  rw [angularVelocityTensor, transpose_mul, transpose_transpose]
  exact eq_neg_of_add_eq_zero_left hprod.symm

/-- A rigid body whose orientation is constant in time has zero angular velocity. -/
lemma angularVelocityTensor_of_orientation_const (M : RigidBodyMotion d)
    (R : Matrix.specialOrthogonalGroup (Fin d) ℝ) (h : M.orientation = fun _ => R) :
    M.angularVelocityTensor = 0 := by
  funext t
  have hconst : (fun s => (M.orientation s).1) = fun _ => R.1 := by
    funext s
    rw [h]
  rw [angularVelocityTensor_eq, hconst, Time.deriv_eq]
  simp

/-- The angular velocity *vector* `ω(t)` of a rigid body moving in three-dimensional space: the
vector dual to the angular velocity tensor `Ω(t)` under the hat map, `ω = Ωᵛ`. It is the angular
velocity `ω` in the Landau–Lifshitz decomposition `v = V + ω × r` of the velocity of a point of the
body, where `ω × r` is the cross product with `ω`. -/
noncomputable def angularVelocity (M : RigidBodyMotion 3) (t : Time) : Fin 3 → ℝ :=
  crossProductVee (M.angularVelocityTensor t)

lemma angularVelocity_eq (M : RigidBodyMotion 3) (t : Time) :
    M.angularVelocity t = crossProductVee (M.angularVelocityTensor t) := rfl

/-- The hat map recovers the angular velocity tensor from the angular velocity vector, `[ω]ₓ = Ω`.
This is the defining relationship between the vector and tensor forms of the angular velocity in
three dimensions; it holds because `Ω` is skew-symmetric. -/
lemma crossProductMatrix_angularVelocity (M : RigidBodyMotion 3) (t : Time)
    (hR : DifferentiableAt ℝ (fun s => (M.orientation s).1) t) :
    crossProductMatrix (M.angularVelocity t) = M.angularVelocityTensor t := by
  rw [angularVelocity_eq,
    crossProductMatrix_crossProductVee (M.angularVelocityTensor_transpose t hR)]

/-- A rigid body whose orientation is constant in time has zero angular velocity vector. -/
lemma angularVelocity_of_orientation_const (M : RigidBodyMotion 3)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (h : M.orientation = fun _ => R) :
    M.angularVelocity = 0 := by
  funext t i
  rw [angularVelocity_eq, congrFun (M.angularVelocityTensor_of_orientation_const R h) t]
  fin_cases i <;> simp [crossProductVee]

/-- The time derivative of the orientation is `Ṙ = Ω R`, recovering the orientation path from its
angular velocity tensor `Ω = Ṙ Rᵀ` via the orthogonality `Rᵀ R = 1`. -/
lemma angularVelocityTensor_mul_orientation (M : RigidBodyMotion d) (t : Time) :
    M.angularVelocityTensor t * (M.orientation t).1 = ∂ₜ (fun s => (M.orientation s).1) t := by
  rw [angularVelocityTensor_eq, mul_assoc,
    mul_eq_one_comm.mp (M.orientation_mul_transpose t), mul_one]

/-- The rotational part of the velocity of the body point `y` is the cross product of the
angular velocity with the point's position relative to the centre of mass:
`Ṙ(t) (y − c) = ω(t) × (displacement t y − comTrajectory t)`. -/
lemma deriv_orientation_mulVec_eq_angularVelocity_cross (M : RigidBodyMotion 3) (y : Space 3)
    (t : Time) (hR : DifferentiableAt ℝ (fun s => (M.orientation s).1) t) :
    ∂ₜ (fun s => (M.orientation s).1) t *ᵥ (fun j => y j - M.centerOfMass j)
      = M.angularVelocity t ⨯₃ fun j => M.displacement t y j - M.comTrajectory t j := by
  rw [← M.angularVelocityTensor_mul_orientation t, ← Matrix.mulVec_mulVec,
    M.orientation_mulVec_sub_centerOfMass t y,
    ← M.crossProductMatrix_angularVelocity t hR, Matrix.crossProductMatrix_mulVec]

/-- The Landau–Lifshitz velocity decomposition `v = V + ω × r` for a rigid body in three
dimensions: the velocity of a body point is the centre-of-mass velocity plus the cross product of
the angular velocity with the point's position relative to the centre of mass. -/
theorem velocity_eq_angularVelocity (M : RigidBodyMotion 3) (y : Space 3) (t : Time) (i : Fin 3)
    (hR : Differentiable ℝ (fun s => (M.orientation s).1)) (hX : Differentiable ℝ M.comTrajectory) :
    M.velocity y t i = M.centerOfMassVelocity t i
        + (M.angularVelocity t ⨯₃ fun j => M.displacement t y j - M.comTrajectory t j) i := by
  rw [M.velocity_eq_deriv_orientation y t i hR hX, add_comm,
    M.deriv_orientation_mulVec_eq_angularVelocity_cross y t (hR t)]

/-- The body-frame (co-rotating) angular velocity tensor `Ω_body(t) = R(t)ᵀ Ṙ(t)` of a rigid body
in motion, where `R(t) = orientation t`. -/
noncomputable def bodyAngularVelocityTensor (M : RigidBodyMotion d) (t : Time) :
    Matrix (Fin d) (Fin d) ℝ :=
  ((M.orientation t).1)ᵀ * ∂ₜ (fun s => (M.orientation s).1) t

lemma bodyAngularVelocityTensor_eq (M : RigidBodyMotion d) (t : Time) :
    M.bodyAngularVelocityTensor t = ((M.orientation t).1)ᵀ * ∂ₜ (fun s => (M.orientation s).1) t :=
  rfl

/-- The time derivative of the orientation is `Ṙ = R Ω_body`, recovering the orientation path from
its body-frame angular velocity tensor via the orthogonality `R Rᵀ = 1`. -/
lemma orientation_mul_bodyAngularVelocityTensor (M : RigidBodyMotion d) (t : Time) :
    (M.orientation t).1 * M.bodyAngularVelocityTensor t = ∂ₜ (fun s => (M.orientation s).1) t := by
  rw [bodyAngularVelocityTensor, ← mul_assoc, M.orientation_mul_transpose t, one_mul]

/-- The spatial tensor is the body-frame tensor rotated into the inertial frame,
`Ω = R Ω_body Rᵀ`. -/
lemma angularVelocityTensor_eq_orientation_conj (M : RigidBodyMotion d) (t : Time) :
    M.angularVelocityTensor t
      = (M.orientation t).1 * M.bodyAngularVelocityTensor t * ((M.orientation t).1)ᵀ := by
  rw [angularVelocityTensor_eq, ← M.orientation_mul_bodyAngularVelocityTensor t]

/-- The body-frame tensor is the spatial tensor conjugated into the body frame,
`Ω_body = Rᵀ Ω R`. -/
lemma bodyAngularVelocityTensor_eq_orientation_conj (M : RigidBodyMotion d) (t : Time) :
    M.bodyAngularVelocityTensor t
      = ((M.orientation t).1)ᵀ * M.angularVelocityTensor t * (M.orientation t).1 := by
  rw [bodyAngularVelocityTensor_eq, angularVelocityTensor_eq, ← mul_assoc, mul_assoc,
    mul_eq_one_comm.mp (M.orientation_mul_transpose t), mul_one]

/-- The body-frame angular velocity tensor is skew-symmetric, `Ω_bodyᵀ = -Ω_body`: it lies in the
Lie algebra `𝔰𝔬(d)`, inherited from the spatial tensor by conjugation. -/
lemma bodyAngularVelocityTensor_transpose (M : RigidBodyMotion d) (t : Time)
    (hR : DifferentiableAt ℝ (fun s => (M.orientation s).1) t) :
    (M.bodyAngularVelocityTensor t)ᵀ = - M.bodyAngularVelocityTensor t := by
  rw [M.bodyAngularVelocityTensor_eq_orientation_conj t, transpose_mul, transpose_mul,
    transpose_transpose, M.angularVelocityTensor_transpose t hR, neg_mul, mul_neg, ← mul_assoc]

/-- The body-frame angular velocity *vector* `ω_body(t)` of a rigid body moving in three-dimensional
space: the vector dual to the body-frame angular velocity tensor `Ω_body(t)` under the hat map,
`ω_body = Ω_bodyᵛ`. -/
noncomputable def bodyAngularVelocity (M : RigidBodyMotion 3) (t : Time) : Fin 3 → ℝ :=
  crossProductVee (M.bodyAngularVelocityTensor t)

lemma bodyAngularVelocity_eq (M : RigidBodyMotion 3) (t : Time) :
    M.bodyAngularVelocity t = crossProductVee (M.bodyAngularVelocityTensor t) := rfl

/-- The hat map recovers the body-frame angular velocity tensor from the body-frame angular
velocity vector, `[ω_body]ₓ = Ω_body`; it holds because `Ω_body` is skew-symmetric. -/
lemma crossProductMatrix_bodyAngularVelocity (M : RigidBodyMotion 3) (t : Time)
    (hR : DifferentiableAt ℝ (fun s => (M.orientation s).1) t) :
    crossProductMatrix (M.bodyAngularVelocity t) = M.bodyAngularVelocityTensor t := by
  rw [bodyAngularVelocity_eq,
    crossProductMatrix_crossProductVee (M.bodyAngularVelocityTensor_transpose t hR)]

/-- A rigid body whose orientation is constant in time has zero body-frame angular velocity
tensor. -/
lemma bodyAngularVelocityTensor_of_orientation_const (M : RigidBodyMotion d)
    (R : Matrix.specialOrthogonalGroup (Fin d) ℝ) (h : M.orientation = fun _ => R) :
    M.bodyAngularVelocityTensor = 0 := by
  funext t
  have hconst : (fun s => (M.orientation s).1) = fun _ => R.1 := by
    funext s
    rw [h]
  rw [bodyAngularVelocityTensor_eq, hconst, Time.deriv_eq]
  simp

/-- A rigid body whose orientation is constant in time has zero body-frame angular velocity
vector. -/
lemma bodyAngularVelocity_of_orientation_const (M : RigidBodyMotion 3)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (h : M.orientation = fun _ => R) :
    M.bodyAngularVelocity = 0 := by
  funext t i
  rw [bodyAngularVelocity_eq, congrFun (M.bodyAngularVelocityTensor_of_orientation_const R h) t]
  fin_cases i <;> simp [crossProductVee]

/-- The rotational velocity written through the body-frame angular velocity,
`Ṙ(t) v = R(t) (ω_body(t) × v)`: the derivative of the orientation acts as the body-frame angular
velocity `ω_body` crossed with `v`, rotated back into the inertial frame by `R`. -/
lemma deriv_orientation_mulVec_eq_orientation_bodyAngularVelocity_cross (M : RigidBodyMotion 3)
    (v : Fin 3 → ℝ) (t : Time)
    (hR : DifferentiableAt ℝ (fun s => (M.orientation s).1) t) :
    ∂ₜ (fun s => (M.orientation s).1) t *ᵥ v
      = (M.orientation t).1 *ᵥ (M.bodyAngularVelocity t ⨯₃ v) := by
  rw [← M.orientation_mul_bodyAngularVelocityTensor t, ← Matrix.mulVec_mulVec,
    ← M.crossProductMatrix_bodyAngularVelocity t hR, Matrix.crossProductMatrix_mulVec]

end RigidBodyMotion
