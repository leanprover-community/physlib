/-
Copyright (c) 2026 Giuseppe Sorge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuseppe Sorge
-/
module

public import Physlib.ClassicalMechanics.RigidBody.AngularMomentum
public import Physlib.ClassicalMechanics.RigidBody.AngularVelocity
public import Physlib.Mathematics.ForMathlib.OrthogonalMatrix
/-!

# Kinetic energy of a rigid body

For a rigid body rotating with angular velocity `ω` about its reference point the point at
position `r` has velocity `ω × r`, so its kinetic energy is `T = ½ ∫ |ω × r|² dm`. Since
`|ω × r|² = ω · (r × (ω × r))` and the angular momentum is `L = ∫ r × (ω × r) dm = I ω`, the
kinetic energy is the quadratic form `T = ½ ω · L = ½ ω · I ω` in the inertia tensor.

For a rigid body in motion the total kinetic energy is the mass integral of half the squared
speed of its points, `T = ½ ∫ ⟪v, v⟫ dm`. König's theorem splits it into the kinetic energy of
the centre of mass plus the rotational energy about the centre of mass,
`T = ½ M ⟪V, V⟫ + ½ ∫ |Ṙ (y − c)|² dm`: the cross term vanishes because the first moment of the
mass distribution about its centre of mass is zero. In three dimensions the rotational term is
`½ ∫ |ω × r|² dm`, with `ω` the angular velocity vector and `r` the position of the body point
relative to the centre of mass.

The total kinetic energy is defined with the point velocity taken in the closed form
`Ṙ(t) (y − c) + V(t)` (`velocityClosedForm`), which is polynomial in the body point and hence
smooth for any motion; for differentiable motions it agrees with the honest point velocity
`∂ₜ (displacement · y)`, recovering `T = ½ ∫ ⟪v, v⟫ dm` (`kineticEnergy_eq_integral_velocity`).

## References

* Landau and Lifshitz, Mechanics, Section 32. [ref: landau_mechanics]
-/

@[expose] public section

open Time Manifold Matrix RigidBody InnerProductSpace
open Space (cmap cmap_apply)

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace RigidBody

/-- The rotational kinetic energy of a rigid body rotating with angular velocity `ω` about its
reference point: half the contraction of `ω` with the inertia tensor, `T = ½ ω · (I ω)`. -/
noncomputable def rotationalKineticEnergy (R : RigidBody 3) (ω : Fin 3 → ℝ) : ℝ :=
  (1 / (2 : ℝ)) * (ω ⬝ᵥ R.inertiaTensor *ᵥ ω)

/-- The rotational kinetic energy is half the contraction of the angular velocity with the angular
momentum: `T = ½ ω · L`. -/
lemma rotationalKineticEnergy_eq_angularMomentum (R : RigidBody 3) (ω : Fin 3 → ℝ) :
    R.rotationalKineticEnergy ω = (1 / (2 : ℝ)) * (ω ⬝ᵥ R.angularMomentum ω) := by
  rw [rotationalKineticEnergy, angularMomentum_eq_inertiaTensor_mulVec]

set_option backward.isDefEq.respectTransparency false in
/-- The rotational kinetic energy equals the mass integral of the local rotational speed squared:
`T = ½ ∫ |ω × r|² dm`. -/
theorem rotationalKineticEnergy_eq_integral (R : RigidBody 3) (ω : Fin 3 → ℝ) :
    R.rotationalKineticEnergy ω
      = (1 / (2 : ℝ)) * R.ρ ⟨fun x => (ω ⨯₃ (x : Fin 3 → ℝ)) ⬝ᵥ (ω ⨯₃ (x : Fin 3 → ℝ)),
        ContDiff.contMDiff <| (contDiff_cross_dotProduct_cross ω).comp
          (contDiff_pi.mpr fun i => Space.eval_contDiff i)⟩ := by
  rw [rotationalKineticEnergy_eq_angularMomentum]
  congr 1
  simp_rw [dotProduct, angularMomentum, ← smul_eq_mul, ← map_smul, ← map_sum]
  congr 1
  ext x
  rw [← ContMDiffMap.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  simp only [ContMDiffMap.coeFnAddMonoidHom_apply, ContMDiffMap.coe_smul, Pi.smul_apply,
    ContMDiffMap.coeFn_mk, smul_eq_mul]
  exact dotProduct_cross_cross_self (x : Fin 3 → ℝ) ω

end RigidBody

namespace RigidBodyMotion

/-- The total kinetic energy of a rigid body in motion at time `t`: half the mass integral of the
squared speed of the body points, `T = ½ ∫ ⟪v, v⟫ dm`, with the point velocity taken in the
closed form `velocityClosedForm`. -/
noncomputable def kineticEnergy {d : ℕ} (M : RigidBodyMotion d) (t : Time) : ℝ :=
  (1 / (2 : ℝ)) * M.ρ (cmap (fun y => (⟪M.velocityClosedForm t y, M.velocityClosedForm t y⟫_ℝ))
    (M.contDiff_velocityClosedForm_inner t))

/-- For a differentiable motion the integrand of `kineticEnergy` is the squared speed of the
honest point velocity: `T = ½ ∫ ⟪v, v⟫ dm` with `v = ∂ₜ (displacement · y)`. -/
lemma kineticEnergy_eq_integral_velocity {d : ℕ} (M : RigidBodyMotion d) (t : Time)
    (hR : Differentiable ℝ (fun s => (M.orientation s).1))
    (hX : Differentiable ℝ M.comTrajectory) :
    M.kineticEnergy t = (1 / (2 : ℝ)) * M.ρ (cmap
      (fun y => (⟪M.velocity y t, M.velocity y t⟫_ℝ))
      (by
        simp only [← M.velocityClosedForm_eq_velocity t hR hX]
        exact M.contDiff_velocityClosedForm_inner t)) := by
  rw [kineticEnergy]
  congr 2
  ext y
  simp only [cmap_apply, M.velocityClosedForm_eq_velocity t hR hX]

/-- The squared-speed integrand of `kineticEnergy` splits into the squared rotational speed
`|Ṙ (y − c)|²`, a term linear in the body-frame coordinate `y − c`, and the constant squared
centre-of-mass speed `⟪V, V⟫`. -/
lemma kineticEnergy_integrand_split {d : ℕ} (M : RigidBodyMotion d) (t : Time) :
    cmap (fun y => (⟪M.velocityClosedForm t y, M.velocityClosedForm t y⟫_ℝ))
        (M.contDiff_velocityClosedForm_inner t)
      = cmap (fun y =>
            (∂ₜ (fun s => (M.orientation s).1) t *ᵥ fun j => y j - M.centerOfMass j) ⬝ᵥ
            (∂ₜ (fun s => (M.orientation s).1) t *ᵥ fun j => y j - M.centerOfMass j))
          (by simp only [dotProduct, Matrix.mulVec]; fun_prop)
        + ∑ j, (2 * (((M.centerOfMassVelocity t : Fin d → ℝ) ᵥ*
              ∂ₜ (fun s => (M.orientation s).1) t) j)) •
            cmap (fun y => y j - M.centerOfMass j) (by fun_prop)
        + (⟪M.centerOfMassVelocity t, M.centerOfMassVelocity t⟫_ℝ) •
            (1 : C^⊤⟮𝓘(ℝ, Space d), Space d; 𝓘(ℝ, ℝ), ℝ⟯) := by
  ext y
  simp only [cmap_apply, ContMDiffMap.coe_add, ContMDiffMap.coe_smul, ContMDiffMap.coe_one,
    Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ContMDiffMap.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  simp only [ContMDiffMap.coeFnAddMonoidHom_apply, ContMDiffMap.coe_smul, Pi.smul_apply,
    cmap_apply, smul_eq_mul]
  rw [show (⟪M.velocityClosedForm t y, M.velocityClosedForm t y⟫_ℝ)
        = (M.velocityClosedForm t y : Fin d → ℝ) ⬝ᵥ (M.velocityClosedForm t y : Fin d → ℝ) from
      EuclideanSpace.inner_eq_star_dotProduct _ _,
    velocityClosedForm_val,
    show (⟪M.centerOfMassVelocity t, M.centerOfMassVelocity t⟫_ℝ)
        = (M.centerOfMassVelocity t : Fin d → ℝ) ⬝ᵥ (M.centerOfMassVelocity t : Fin d → ℝ) from
      EuclideanSpace.inner_eq_star_dotProduct _ _,
    add_dotProduct, dotProduct_add, dotProduct_add,
    dotProduct_comm (∂ₜ (fun s => (M.orientation s).1) t *ᵥ fun j => y j - M.centerOfMass j)
      (M.centerOfMassVelocity t : Fin d → ℝ),
    dotProduct_mulVec (M.centerOfMassVelocity t : Fin d → ℝ)
      (∂ₜ (fun s => (M.orientation s).1) t) (fun j => y j - M.centerOfMass j)]
  simp only [dotProduct, two_mul, add_mul, Finset.sum_add_distrib]
  ring

/-- **König's theorem**, general form: the total kinetic energy of a rigid body in motion splits
into the kinetic energy of the centre of mass plus the rotational energy about the centre of
mass, `T = ½ M ⟪V, V⟫ + ½ ∫ |Ṙ (y − c)|² dm`. -/
theorem kineticEnergy_eq_translational_add_rotational {d : ℕ} (M : RigidBodyMotion d) (t : Time)
    (h : M.mass ≠ 0) :
    M.kineticEnergy t
      = (1 / (2 : ℝ)) * M.mass * (⟪M.centerOfMassVelocity t, M.centerOfMassVelocity t⟫_ℝ)
        + (1 / (2 : ℝ)) * M.ρ (cmap (fun y =>
            (∂ₜ (fun s => (M.orientation s).1) t *ᵥ fun j => y j - M.centerOfMass j) ⬝ᵥ
            (∂ₜ (fun s => (M.orientation s).1) t *ᵥ fun j => y j - M.centerOfMass j))
          (by simp only [dotProduct, Matrix.mulVec]; fun_prop)) := by
  rw [kineticEnergy, kineticEnergy_integrand_split, map_add, map_add, map_sum]
  simp only [map_smul, M.rho_coord_sub_centerOfMass h, smul_eq_mul, mul_zero,
    Finset.sum_const_zero, add_zero, M.rho_one]
  ring

/-- **König's theorem** in three dimensions: the total kinetic energy of a rigid body in motion
splits as `T = ½ M ⟪V, V⟫ + ½ ∫ |ω × r|² dm`, with `ω` the angular velocity vector and
`r = displacement − comTrajectory` the position of the body point relative to the centre of
mass. -/
theorem kineticEnergy_eq_translational_add_angularVelocity (M : RigidBodyMotion 3) (t : Time)
    (h : M.mass ≠ 0) (hR : DifferentiableAt ℝ (fun s => (M.orientation s).1) t) :
    M.kineticEnergy t
      = (1 / (2 : ℝ)) * M.mass * (⟪M.centerOfMassVelocity t, M.centerOfMassVelocity t⟫_ℝ)
        + (1 / (2 : ℝ)) * M.ρ (cmap (fun y =>
            (M.angularVelocity t ⨯₃ fun j => M.displacement t y j - M.comTrajectory t j) ⬝ᵥ
            (M.angularVelocity t ⨯₃ fun j => M.displacement t y j - M.comTrajectory t j))
          (by
            exact (contDiff_cross_dotProduct_cross (M.angularVelocity t)).comp
              (contDiff_pi.mpr fun j =>
                ((Space.eval_contDiff j).comp (M.displacement_contDiff t)).sub
                  contDiff_const))) := by
  rw [M.kineticEnergy_eq_translational_add_rotational t h]
  congr 1
  congr 2
  ext y
  simp only [cmap_apply, M.deriv_orientation_mulVec_eq_angularVelocity_cross y t hR]

/-- **König's theorem** in the body frame. The total kinetic energy `M.kineticEnergy t`, formed from
the lab-frame point velocities, splits at the centre of mass (`centerOfMass = 0`) as
`T = ½ M ⟪V, V⟫ + rotationalKineticEnergy ω_body`. The rotational energy is a frame-independent
scalar, so it is evaluated here from the *body-frame* angular velocity `ω_body`: the spatial form
`|Ṙ (y − c)|²` and the body form `|ω_body × (y − c)|²` agree because
`Ṙ (y − c) = R (ω_body × (y − c))` and `R`, being orthogonal, preserves the norm. -/
theorem kineticEnergy_eq_translational_add_bodyAngularVelocity (M : RigidBodyMotion 3) (t : Time)
    (h : M.mass ≠ 0) (hR : DifferentiableAt ℝ (fun s => (M.orientation s).1) t)
    (hc : M.centerOfMass = 0) :
    M.kineticEnergy t
      = (1 / (2 : ℝ)) * M.mass * (⟪M.centerOfMassVelocity t, M.centerOfMassVelocity t⟫_ℝ)
        + M.toRigidBody.rotationalKineticEnergy (M.bodyAngularVelocity t) := by
  rw [M.kineticEnergy_eq_translational_add_rotational t h,
    RigidBody.rotationalKineticEnergy_eq_integral]
  congr 1
  congr 2
  ext y
  have hy : (fun j => (y : Fin 3 → ℝ) j - M.centerOfMass j) = (y : Fin 3 → ℝ) := by
    simp [hc]
  simp only [cmap_apply, ContMDiffMap.coeFn_mk]
  rw [hy, M.deriv_orientation_mulVec_eq_orientation_bodyAngularVelocity_cross (y : Fin 3 → ℝ) t hR,
    Matrix.dotProduct_mulVec_orthogonal (mul_eq_one_comm.mp (M.orientation_mul_transpose t))]

end RigidBodyMotion
