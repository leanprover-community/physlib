/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Physlib.ClassicalMechanics.EulerLagrange
public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Dynamics.Dynamics

/-!
# Lagrangian dynamics of the Hohmann transfer coast

The smooth coast satisfies the Euler–Lagrange equation for a Kepler Lagrangian on its radial range.

## i. Overview

The inverse-radius term is singular at the centre. The normed-space constructor for
`LagrangianSystem` requires a globally smooth Lagrangian. We smooth the inverse-radius term inside
half the inner orbital radius. The entire transfer ellipse stays outside this region, where the
Lagrangian is the usual kinetic term plus the gravitational parameter divided by the radius.

## ii. Key results

- `lagrangianSystem` packages the smooth extension on the planar configuration space.
- `lagrangianSystem_coord_eq` recovers the Kepler Lagrangian outside the modified region.
- `eulerLagrange_position` proves that the Euler–Lagrange covector vanishes on the smooth coast.

## iii. Table of contents

- A. The Lagrangian on the plane
- B. The Euler–Lagrange equation along the coast

## iv. References

- [ref: hohmann_jpl_orbital_mechanics] describes the Hohmann transfer coast.
-/

public noncomputable section

namespace ClassicalMechanics.HohmannTransfer

open Filter
open scoped ContDiff Manifold Topology

/-!
## A. The Lagrangian on the plane
-/

/-- The bump that smooths the inverse-radius term at the centre. -/
private def centreBump (p : Parameters) : ContDiffBump (0 : ℂ) where
  rIn := p.r₁ / 4
  rOut := p.r₁ / 2
  rIn_pos := by positivity [p.r₁_pos]
  rIn_lt_rOut := by linarith [p.r₁_pos]

/-- The squared radius with a smooth positive correction near the centre. -/
private def regularizedRadiusSq (p : Parameters) (q : ℂ) : ℝ :=
  ‖q‖ ^ 2 + centreBump p q

private lemma regularizedRadiusSq_pos (p : Parameters) (q : ℂ) :
    0 < regularizedRadiusSq p q := by
  by_cases hq : q = 0
  · subst q
    have hb : centreBump p (0 : ℂ) = 1 :=
      (centreBump p).one_of_mem_closedBall (Metric.mem_closedBall_self (centreBump p).rIn_pos.le)
    simp [regularizedRadiusSq, hb]
  · exact add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.mpr hq) 2) (centreBump p).nonneg

/-- The kinetic term plus the smooth extension of the inverse-radius term. -/
private def coastLagrangian (p : Parameters) (qv : ℂ × ℂ) : ℝ :=
  ‖qv.2‖ ^ 2 / 2 + p.mu / Real.sqrt (regularizedRadiusSq p qv.1)

private lemma contDiff_coastLagrangian (p : Parameters) : ContDiff ℝ ∞ (coastLagrangian p) := by
  have hr : ContDiff ℝ ∞ (regularizedRadiusSq p) :=
    (contDiff_norm_sq ℝ).add (centreBump p).contDiff
  have hs := hr.sqrt (fun q ↦ (regularizedRadiusSq_pos p q).ne')
  exact (((contDiff_norm_sq ℝ).comp contDiff_snd).div contDiff_const (by norm_num)).add
    (contDiff_const.div (hs.comp contDiff_fst)
      (fun qv ↦ (Real.sqrt_pos.2 (regularizedRadiusSq_pos p qv.1)).ne'))

/-- The Lagrangian system on the plane that agrees with the Kepler Lagrangian on the coast. -/
def lagrangianSystem (p : Parameters) : LagrangianSystem 𝓘(ℝ, ℂ) ⟨ℂ⟩ :=
  LagrangianSystem.ofNormedSpace (fun qv ↦ coastLagrangian p qv.2)
    ((contMDiff_iff_contDiff.mpr (contDiff_coastLagrangian p)).comp contMDiff_snd)

/-- Outside the modified region the coordinate Lagrangian is the original Kepler Lagrangian. -/
lemma lagrangianSystem_coord_eq (p : Parameters) (t₀ : Time) (t : ℝ) {q : ℂ}
    (v : ℂ) (hq : p.r₁ / 2 ≤ ‖q‖) :
    (lagrangianSystem p).coord t₀ (t, q, v) = ‖v‖ ^ 2 / 2 + p.mu / ‖q‖ := by
  have hb : centreBump p q = 0 := (centreBump p).zero_of_le_dist (by simpa [centreBump] using hq)
  change coastLagrangian p (q, v) = _
  simp [coastLagrangian, regularizedRadiusSq, hb, Real.sqrt_sq (norm_nonneg q)]

/-!
## B. The Euler–Lagrange equation along the coast
-/

private lemma hasFDerivAt_inverseRadius (μ : ℝ) {q : ℂ} (hq : q ≠ 0) :
    HasFDerivAt (fun x : ℂ ↦ μ / ‖x‖) (innerSL ℝ (gravity μ q)) q := by
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hs := (hasStrictFDerivAt_norm_sq q).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq (norm_nonneg _)] at hs
  have hd := ((hasDerivAt_inv hn).comp_hasFDerivAt q hs).const_mul μ
  convert hd using 1
  · funext x
    exact div_eq_mul_inv _ _
  · ext y
    simp only [gravity, map_smul, smul_apply, smul_eq_mul, two_smul,
      add_apply]
    field_simp
    ring

private lemma canonicalMomentum_position (p : Parameters) (t₀ : Time) (t : ℝ) :
    canonicalMomentum (lagrangianSystem p) t₀ (position p) t = innerSL ℝ (velocity p t) := by
  rw [canonicalMomentum, deriv_position]
  change fderiv ℝ (fun v : ℂ ↦ ‖v‖ ^ 2 / 2 +
    p.mu / Real.sqrt (regularizedRadiusSq p (position p t))) (velocity p t) = _
  have hk : HasFDerivAt (fun v : ℂ ↦ ‖v‖ ^ 2 / 2) (innerSL ℝ (velocity p t))
      (velocity p t) := by
    convert (hasStrictFDerivAt_norm_sq (velocity p t)).hasFDerivAt.const_mul (1 / 2 : ℝ) using 1
    · funext v
      rw [div_eq_mul_inv, one_div, mul_comm]
    · ext y
      simp only [smul_apply, smul_eq_mul]
      ring
  exact (hk.add_const _).fderiv

/-- The Hohmann transfer coast satisfies the Euler–Lagrange equation in the planar system. -/
lemma eulerLagrange_position (p : Parameters) (t₀ : Time) (t : ℝ) :
    eulerLagrange (lagrangianSystem p) t₀ (position p) t = 0 := by
  have hq : p.r₁ / 2 < ‖position p t‖ := by linarith [p.r₁_pos, (position_bounds p t).1]
  have hnear : ∀ᶠ q : ℂ in 𝓝 (position p t), p.r₁ / 2 < ‖q‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hq
  have hforce := (hasFDerivAt_inverseRadius p.mu (position_ne_zero p t)).const_add
    (‖deriv (position p) t‖ ^ 2 / 2)
  have hforce' := hforce.congr_of_eventuallyEq (by
    filter_upwards [hnear] with q hq'
    exact lagrangianSystem_coord_eq p t₀ t _ hq'.le)
  have hp : deriv (fun s ↦ innerSL ℝ (velocity p s)) t =
      innerSL ℝ (gravity p.mu (position p t)) :=
    ((innerSL ℝ (E := ℂ)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_velocity_newton p t)).deriv
  rw [eulerLagrange, funext (canonicalMomentum_position p t₀), hforce'.fderiv, hp, sub_self]

end ClassicalMechanics.HohmannTransfer
