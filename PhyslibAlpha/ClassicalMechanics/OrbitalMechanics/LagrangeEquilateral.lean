/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.NewtonianGravity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Lagrange's circular equilateral solution
Three positive masses form a rotating equilateral triangle in a Newtonian gravitational system.

## i. Overview

A triangle of side length `ℓ` is translated to its mass barycentre. Rotating it with angular
speed `√(G * M / ℓ ^ 3)`, where `M` is the total mass, preserves the separation of each pair.
The gravitational acceleration of each particle is therefore the centripetal acceleration
of its rotation. The rotating trajectories define particles in an arbitrary planar inertial
reference frame, and `NewtonianSystem.ofGravity` supplies the system and both Newton laws.

## ii. Key results

- `exists_lagrange_equilateral_solution` gives the three labelled particles, their equilateral
  distances, uniform circular motion about the barycentre, and Kepler's third law.

## iii. Table of contents

- A. The rotating configuration
- B. Particles in the inertial frame
- C. The Lagrange solution

## iv. References

* [ref: chenciner_fejoz_2008], §8, for the reduction of the equilateral force sum.
* R5 Lean formalization.
  https://github.com/hkjtsgmc79-boop/lagrange-three-body-lean/releases/tag/v0.5.1
-/

noncomputable section

open scoped BigOperators Classical

namespace ClassicalMechanics.LagrangeOrbit

open ReferenceFrame PointParticle Complex

/-!
## A. The rotating configuration
-/

variable (G : ℝ) (m : Fin 3 → ℝ+) (ℓ : ℝ)

/-- The squared angular speed of the equilateral relative equilibrium. -/
private def frequencySq : ℝ := G * (∑ i, (m i).val) / ℓ ^ 3

/-- The positive square root of the frequency squared for positive `G` and `ℓ`. -/
private def angularSpeed : ℝ := Real.sqrt (frequencySq G m ℓ)

private lemma frequencySq_pos (hG : 0 < G) (hℓ : 0 < ℓ) :
    0 < frequencySq G m ℓ := by
  apply div_pos (mul_pos hG _) (pow_pos hℓ _)
  exact Finset.sum_pos (fun i _ => (m i).property) Finset.univ_nonempty

/-- An equilateral triangle of side length `ℓ` with one vertex at the origin. -/
private def vertices : Fin 3 → ℂ :=
  ![0, (ℓ : ℂ), ⟨ℓ / 2, Real.sqrt 3 * ℓ / 2⟩]

private lemma vertices_distance (hℓ : 0 < ℓ) (i j : Fin 3) (hij : i ≠ j) :
    ‖vertices ℓ i - vertices ℓ j‖ = ℓ := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply (sq_eq_sq₀ (norm_nonneg _) hℓ.le).mp
  rw [Complex.sq_norm]
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  all_goals
    norm_num [vertices, Complex.normSq_apply, Matrix.cons_val_succ]
    nlinarith

/-- The mass barycentre of the initial vertices. -/
private def barycentre : ℂ :=
  (∑ i, (m i).val)⁻¹ • ∑ i, (m i).val • vertices ℓ i

/-- Rotate the mass-centred vertices uniformly about the origin. -/
private def orbit (t : ℝ) (i : Fin 3) : ℂ :=
  rotation (Circle.exp (angularSpeed G m ℓ * t)) (vertices ℓ i - barycentre m ℓ)

private lemma orbit_distance (hℓ : 0 < ℓ) (t : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    ‖orbit G m ℓ t i - orbit G m ℓ t j‖ = ℓ := by
  unfold orbit
  rw [← map_sub, LinearIsometryEquiv.norm_map, sub_sub_sub_cancel_right]
  exact vertices_distance ℓ hℓ i j hij

private lemma orbit_firstMoment (t : ℝ) : ∑ i, (m i).val • orbit G m ℓ t i = 0 := by
  have hM : 0 < ∑ i, (m i).val :=
    Finset.sum_pos (fun i _ => (m i).property) Finset.univ_nonempty
  unfold orbit
  simp_rw [← map_smul]
  rw [← map_sum, ← map_zero (rotation (Circle.exp (angularSpeed G m ℓ * t)))]
  congr 1
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, barycentre]
  rw [smul_smul, mul_inv_cancel₀ hM.ne', one_smul, sub_self]

private lemma hasDerivAt_orbit (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => orbit G m ℓ s i)
      (((angularSpeed G m ℓ : ℝ) : ℂ) * I * orbit G m ℓ t i) t := by
  let ω := angularSpeed G m ℓ
  have h : HasDerivAt (fun s : ℝ => ω * s) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  have hExp := ((h.ofReal_comp.mul_const I).cexp.mul_const (vertices ℓ i - barycentre m ℓ))
  convert hExp using 1
  · simp only [orbit, rotation_apply, Circle.coe_exp, ω]
  · simp only [orbit, rotation_apply, Circle.coe_exp, ω]
    ring

/-!
## B. Particles in the inertial frame
-/

/-- Identify the complex plane with the physical displacement vectors of the frame. -/
private def framePlane (frame : ReferenceFrame 2) [Fact frame.IsMetricConserved] :
    ℂ ≃ₗᵢ[ℝ] frame.Vector :=
  Complex.orthonormalBasisOneI.repr.trans
    ({ toLinearEquiv := Vector.dispEquiv (frame := frame) 0
       norm_map' := fun _ => rfl } : frame.Vector ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)).symm

/-- The particle following one vertex of the rotating triangle in the given frame. -/
private def particle (frame : ReferenceFrame 2) [Fact frame.IsInertial] (i : Fin 3) :
    frame.Particle where
  mass := m i
  pos t := framePlane frame (orbit G m ℓ t i)
  pos_twice_differentiable _ := by
    let L := (framePlane frame).toLinearIsometry.toContinuousLinearMap
    have hv (t : ℝ) := L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_orbit G m ℓ t i)
    refine ⟨fun t => (hv t).differentiableAt, ?_⟩
    have hderiv : deriv (fun t => framePlane frame (orbit G m ℓ t i)) =
        fun t => L (((angularSpeed G m ℓ : ℝ) : ℂ) * I * orbit G m ℓ t i) :=
      funext fun t => (hv t).deriv
    rw [hderiv]
    exact fun t => (L.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_orbit G m ℓ t i).const_mul _)).differentiableAt

/-- The particle's acceleration is centripetal with the angular speed of the rotation. -/
private lemma particle_acceleration (frame : ReferenceFrame 2) [Fact frame.IsInertial]
    (hG : 0 < G) (hℓ : 0 < ℓ) (t : ℝ) (i : Fin 3) :
    (particle G m ℓ frame i).acceleration t =
      -frequencySq G m ℓ • (particle G m ℓ frame i).pos t := by
  let L := (framePlane frame).toLinearIsometry.toContinuousLinearMap
  have hderiv : (particle G m ℓ frame i).velocity =
      fun s => L (((angularSpeed G m ℓ : ℝ) : ℂ) * I * orbit G m ℓ s i) :=
    funext fun s => (L.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_orbit G m ℓ s i)).deriv
  change deriv (particle G m ℓ frame i).velocity t = _
  rw [hderiv]
  have ha := L.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_orbit G m ℓ t i).const_mul (((angularSpeed G m ℓ : ℝ) : ℂ) * I))
  rw [show deriv (fun s => L (((angularSpeed G m ℓ : ℝ) : ℂ) * I * orbit G m ℓ s i)) t = _
    from ha.deriv]
  change framePlane frame _ = -frequencySq G m ℓ • framePlane frame (orbit G m ℓ t i)
  rw [← map_smul]
  congr 1
  rw [Complex.real_smul, Complex.ofReal_neg]
  have hw : angularSpeed G m ℓ ^ 2 = frequencySq G m ℓ :=
    Real.sq_sqrt (frequencySq_pos G m ℓ hG hℓ).le
  rw [← hw, Complex.ofReal_pow]
  linear_combination (((angularSpeed G m ℓ : ℝ) : ℂ) ^ 2 * orbit G m ℓ t i) * Complex.I_sq

private lemma particle_distance (frame : ReferenceFrame 2) [Fact frame.IsInertial]
    (hℓ : 0 < ℓ) (t : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    ‖(particle G m ℓ frame i).pos t - (particle G m ℓ frame j).pos t‖ = ℓ := by
  change ‖framePlane frame (orbit G m ℓ t i) - framePlane frame (orbit G m ℓ t j)‖ = ℓ
  rw [← map_sub, LinearIsometryEquiv.norm_map]
  exact orbit_distance G m ℓ hℓ t i j hij

private lemma particle_firstMoment (frame : ReferenceFrame 2) [Fact frame.IsInertial] (t : ℝ) :
    ∑ i, (m i).val • (particle G m ℓ frame i).pos t = 0 := by
  change ∑ i, (m i).val • framePlane frame (orbit G m ℓ t i) = 0
  simp_rw [← map_smul]
  rw [← map_sum, orbit_firstMoment, map_zero]

/-- The collection of the three rotating particles, counted with multiplicity. -/
private def particles (frame : ReferenceFrame 2) [Fact frame.IsInertial] :
    Multiset frame.Particle := Finset.univ.val.map (particle G m ℓ frame)

/-- Positive separation identifies each label with one occurrence in the particle multiset. -/
private def particleLabels (frame : ReferenceFrame 2) [Fact frame.IsInertial] (hℓ : 0 < ℓ) :
    Fin 3 ≃ particles G m ℓ frame := by
  let ps := particles G m ℓ frame
  let label (i : Fin 3) : ps :=
    ⟨particle G m ℓ frame i, ⟨0, Multiset.count_pos.mpr (by
      exact Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val i, rfl⟩)⟩⟩
  apply Equiv.ofBijective label
  apply (Fintype.bijective_iff_injective_and_card label).mpr
  refine ⟨?_, ?_⟩
  · intro i j he
    by_contra hij
    have hd := particle_distance G m ℓ frame hℓ 0 i j hij
    have hp : particle G m ℓ frame i = particle G m ℓ frame j := congrArg Sigma.fst he
    rw [hp, sub_self, norm_zero] at hd
    exact hℓ.ne' hd.symm
  · rw [Multiset.card_coe]
    change Fintype.card (Fin 3) = (Finset.univ.val.map (particle G m ℓ frame)).card
    rw [Multiset.card_map]
    exact Finset.card_univ.symm

/-- Equal separations and the zero mass first moment reduce gravity to the centripetal term. -/
private lemma particle_gravity (frame : ReferenceFrame 2) [Fact frame.IsInertial]
    (hℓ : 0 < ℓ) (t : ℝ) (i : Fin 3) :
    let ps := particles G m ℓ frame
    let target := particleLabels G m ℓ frame hℓ i
    gravityAcceleration G ps target t =
      -frequencySq G m ℓ • (particle G m ℓ frame i).pos t := by
  let ps := particles G m ℓ frame
  let e := particleLabels G m ℓ frame hℓ
  let q (j : Fin 3) := (particle G m ℓ frame j).pos t
  change gravityAcceleration G ps (e i) t = -frequencySq G m ℓ • q i
  let sources : {j : Fin 3 // j ≠ i} ≃ {j : ps // j ≠ e i} :=
    e.subtypeEquiv fun j => not_congr e.injective.eq_iff.symm
  unfold gravityAcceleration
  rw [← Fintype.sum_equiv sources
    (fun j => (G * (m j.1).val / ℓ ^ 3) • (q j.1 - q i)) _]
  · have hsum : (∑ j, (G * (m j).val / ℓ ^ 3) • (q j - q i)) =
        ∑ j : {j : Fin 3 // j ≠ i}, (G * (m j.1).val / ℓ ^ 3) • (q j.1 - q i) := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ i, sub_self, smul_zero, zero_add]
    rw [← hsum]
    have hc (j : Fin 3) : G * (m j).val / ℓ ^ 3 = (G / ℓ ^ 3) * (m j).val := by ring
    simp_rw [hc, ← smul_smul]
    rw [← Finset.smul_sum]
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    rw [show (∑ j, (m j).val • q j) = 0 from particle_firstMoment G m ℓ frame t]
    rw [zero_sub, smul_neg, smul_smul, ← neg_smul]
    congr 2
    unfold frequencySq
    ring
  · intro j
    change (G * (m j.1).val / ℓ ^ 3) • (q j.1 - q i) =
      pairGravityAcceleration G ps (e j.1) (e i) t
    simp only [pairGravityAcceleration]
    change _ = (G * (m j.1).val / ‖q j.1 - q i‖ ^ 3) • (q j.1 - q i)
    rw [particle_distance G m ℓ frame hℓ t j.1 i j.2]

/-!
## C. The Lagrange solution
-/

/-- The time for one full rotation of the triangle. -/
private def period : ℝ := 2 * Real.pi / angularSpeed G m ℓ

private lemma angularSpeed_mul_period (hG : 0 < G) (hℓ : 0 < ℓ) :
    angularSpeed G m ℓ * period G m ℓ = 2 * Real.pi := by
  unfold period
  have hω : angularSpeed G m ℓ ≠ 0 :=
    (Real.sqrt_pos.2 (frequencySq_pos G m ℓ hG hℓ)).ne'
  rw [mul_comm (angularSpeed G m ℓ), div_mul_cancel₀ _ hω]

private lemma particle_periodic (frame : ReferenceFrame 2) [Fact frame.IsInertial]
    (hG : 0 < G) (hℓ : 0 < ℓ) (i : Fin 3) :
    Function.Periodic (particle G m ℓ frame i).pos (period G m ℓ) := by
  intro t
  change framePlane frame (orbit G m ℓ (t + period G m ℓ) i) =
    framePlane frame (orbit G m ℓ t i)
  unfold orbit
  rw [mul_add, angularSpeed_mul_period G m ℓ hG hℓ, Circle.exp_add_two_pi]

private lemma period_law (hG : 0 < G) (hℓ : 0 < ℓ) :
    period G m ℓ ^ 2 * (G * ∑ i, (m i).val) = 4 * Real.pi ^ 2 * ℓ ^ 3 := by
  have hω := Real.sq_sqrt (frequencySq_pos G m ℓ hG hℓ).le
  have hf : angularSpeed G m ℓ ^ 2 * ℓ ^ 3 = G * ∑ i, (m i).val :=
    (eq_div_iff (pow_ne_zero _ hℓ.ne')).mp hω
  calc
    _ = (angularSpeed G m ℓ * period G m ℓ) ^ 2 * ℓ ^ 3 := by rw [← hf]; ring
    _ = _ := by rw [angularSpeed_mul_period G m ℓ hG hℓ]; ring

/-- The Lagrange relative equilibrium for three positive masses in a planar inertial frame.
The labelled particles move on a rigid equilateral triangle about their mass barycentre,
with a positive common period obeying Kepler's third law. -/
public lemma exists_lagrange_equilateral_solution (frame : ReferenceFrame 2) [Fact frame.IsInertial]
    (hG : 0 < G) (hℓ : 0 < ℓ) :
    ∃ (system : NewtonianSystem 2) (e : Fin 3 ≃ system.Particle) (T : ℝ),
      system.frame = frame ∧
      system.internalForces = gravityForces G system.particles ∧
      system.externalForces = 0 ∧
      (∀ i, (e i).mass = m i) ∧
      (∀ t, ∑ i, (m i).val • (e i).pos t = 0) ∧
      (∀ t i j, i ≠ j → ‖(e i).pos t - (e j).pos t‖ = ℓ) ∧
      (∀ i, Function.Periodic (e i).pos T) ∧
      (∃ plane : ℂ ≃ₗᵢ[ℝ] system.frame.Vector, ∀ t i,
        (e i).pos t = plane (rotation (Circle.exp (2 * Real.pi / T * t))
          (plane.symm ((e i).pos 0)))) ∧
      0 < T ∧ T ^ 2 * (G * ∑ i, (m i).val) = 4 * Real.pi ^ 2 * ℓ ^ 3 := by
  let e := particleLabels G m ℓ frame hℓ
  have motion (target : particles G m ℓ frame) (t : ℝ) :
      target.1.acceleration t = gravityAcceleration G (particles G m ℓ frame) target t := by
    obtain ⟨i, rfl⟩ := e.surjective target
    exact (particle_acceleration G m ℓ frame hG hℓ t i).trans
      (particle_gravity G m ℓ frame hℓ t i).symm
  have hω : 0 < angularSpeed G m ℓ := Real.sqrt_pos.2 (frequencySq_pos G m ℓ hG hℓ)
  have hT : 0 < period G m ℓ := div_pos (by positivity) hω
  refine ⟨NewtonianSystem.ofGravity G _ motion, e, period G m ℓ,
    rfl, rfl, rfl, fun _ => rfl, particle_firstMoment G m ℓ frame,
    particle_distance G m ℓ frame hℓ, particle_periodic G m ℓ frame hG hℓ, ?_,
    hT, period_law G m ℓ hG hℓ⟩
  refine ⟨framePlane frame, fun t i => ?_⟩
  have hspeed : 2 * Real.pi / period G m ℓ = angularSpeed G m ℓ :=
    (div_eq_iff hT.ne').mpr (angularSpeed_mul_period G m ℓ hG hℓ).symm
  change framePlane frame (orbit G m ℓ t i) =
    framePlane frame (rotation (Circle.exp (2 * Real.pi / period G m ℓ * t))
      ((framePlane frame).symm (framePlane frame (orbit G m ℓ 0 i))))
  rw [hspeed, LinearIsometryEquiv.symm_apply_apply]
  simp [orbit]

end ClassicalMechanics.LagrangeOrbit
