/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Distributional.Dynamics.IsExtrema
public import Physlib.SpaceAndTime.TimeAndSpace.ConstantTimeDist

/-!

# Junctions of thin wires

## i. Overview

Let `A` be a distributional electromagnetic potential and `J` a distributional Lorentz current
density such that Maxwell's equations hold, `IsExtrema 𝓕 A J`. Taking the divergence of
Ampère's law and using Gauss's law gives the continuity equation `∂ₜ ρ + ∇ ⬝ J = 0` as an
equation of distributions.

Distributions allow currents to be carried by thin wires. A junction is modelled by finitely
many straight, semi-infinite wires leaving the origin in the directions `u k`, carrying steady
currents `I k`. The divergence of such a current density is `(∑ k, I k) δ₀`: the wires end at
the origin, where the currents must come from somewhere. If no charge accumulates, the
continuity equation forces `∑ k, I k = 0`.

This is motivated by Kirchhoff's current law, of which it is a special case: a single node with
steady currents, rather than the branch currents at every node of a lumped-element circuit.

## ii. Key results

- `Electromagnetism.DistElectromagneticPotential.continuityEquation` : the continuity equation
  for distributions.
- `Electromagnetism.DistLorentzCurrentDensity.IsWireJunction` : the current density of a
  junction of thin wires.
- `Electromagnetism.DistLorentzCurrentDensity.IsWireJunction.distSpaceDiv_currentDensity` : the
  divergence of the current density of a junction.
- `Electromagnetism.DistLorentzCurrentDensity.IsWireJunction.sum_currents_eq_zero` : the
  currents leaving a junction of thin wires sum to zero.

## iii. Table of contents

- A. Analysis on `Space`
  - A.1. Time derivatives and the divergence of distributions
  - A.2. Schwartz functions along a ray
  - A.3. Integrating test functions over time
- B. The continuity equation
- C. Junctions of thin wires
  - C.1. The current density of a junction
  - C.2. The currents at a junction sum to zero

## iv. References

* None.

-/

@[expose] public section

namespace Space

open MeasureTheory Set Filter SchwartzMap

/-!

## A. Analysis on `Space`

### A.1. Time derivatives and the divergence of distributions

-/

/-- The divergence and the time derivative of distributions commute. -/
lemma distTimeDeriv_distSpaceDiv {d} (f : (Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin d)) :
    distTimeDeriv (distSpaceDiv f) = distSpaceDiv (distTimeDeriv f) := by
  ext ε
  rw [distTimeDeriv_apply', distSpaceDiv_apply_eq_sum_distSpaceDeriv,
    distSpaceDiv_apply_eq_sum_distSpaceDeriv]
  simp [apply_fderiv_eq_distTimeDeriv, ← distTimeDeriv_commute_distSpaceDeriv]

/-!

### A.2. Schwartz functions along a ray

The ray from the origin in the direction `w` is parametrized by `s ↦ s • w`.

-/

/-- The restriction of a Schwartz function to a line through the origin is a Schwartz
function. -/
lemma exists_schwartz_eq_comp_ray {d} (χ : 𝓢(Space d, ℝ)) {w : Space d} (hw : w ≠ 0) :
    ∃ g : 𝓢(ℝ, ℝ), ∀ s : ℝ, g s = χ (s • w) := by
  let γ : ℝ →L[ℝ] Space d := (ContinuousLinearMap.id ℝ ℝ).smulRight w
  have hγ : AntilipschitzWith ‖w‖₊⁻¹ γ := γ.antilipschitz_of_bound fun s => by
    simp only [γ, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, norm_smul]
    rw [NNReal.coe_inv, coe_nnnorm, mul_comm ‖s‖, ← mul_assoc,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw), one_mul]
  exact ⟨compCLMOfAntilipschitz ℝ γ.hasTemperateGrowth hγ χ, fun s => rfl⟩

/-- The fundamental theorem of calculus along the ray in direction `w`. -/
lemma integral_Ioi_fderiv_ray {d} (ψ : 𝓢(Space d, ℝ)) {w : Space d} (hw : w ≠ 0) :
    ∫ s in Ioi (0 : ℝ), fderiv ℝ ψ (s • w) w = - ψ 0 := by
  obtain ⟨g, hg⟩ := exists_schwartz_eq_comp_ray ψ hw
  obtain ⟨g', hg'⟩ := exists_schwartz_eq_comp_ray
    (SchwartzMap.evalCLM ℝ (Space d) ℝ w (fderivCLM ℝ (Space d) ℝ ψ)) hw
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (f := g) (f' := g') (m := 0) (a := 0)
    g.continuous.continuousWithinAt (fun s _ => ?_) g'.integrable.integrableOn
    (g.tendsto_cocompact.mono_left atTop_le_cocompact)
  · simpa [hg, hg'] using h
  · have hd := (ψ.differentiableAt (x := s • w)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).smul_const w)
    rw [show (⇑g) = fun s => ψ (s • w) from funext hg, hg']
    rw [one_smul] at hd
    exact hd

lemma integral_Ioi_fderiv_ray_basis {d} (ψ : 𝓢(Space d, ℝ)) {u : EuclideanSpace ℝ (Fin d)}
    (hu : u ≠ 0) :
    ∑ i, (∫ s in Ioi (0 : ℝ), fderiv ℝ ψ (s • basis.repr.symm u) (basis i)) * u i = - ψ 0 := by
  have hw : basis.repr.symm u ≠ 0 := by simpa using hu
  have hint (i : Fin d) : Integrable fun s : ℝ =>
      fderiv ℝ ψ (s • basis.repr.symm u) (basis i) * u i := by
    obtain ⟨g, hg⟩ := exists_schwartz_eq_comp_ray
      (SchwartzMap.evalCLM ℝ (Space d) ℝ (basis i) (fderivCLM ℝ (Space d) ℝ ψ)) hw
    exact (g.integrable.mul_const (u i)).congr (Eventually.of_forall fun s => by simp [hg])
  simp only [← integral_mul_const]
  rw [← integral_finsetSum _ fun i _ => (hint i).integrableOn, ← integral_Ioi_fderiv_ray ψ hw]
  congr 1
  funext s
  rw [show fderiv ℝ ψ (s • basis.repr.symm u) (basis.repr.symm u) =
      fderiv ℝ ψ (s • basis.repr.symm u) (∑ i, u i • basis i) by rw [basis.sum_repr_symm]]
  simp [mul_comm]

/-!

### A.3. Integrating test functions over time

-/

/-- Integrating over time commutes with differentiating in space. -/
lemma timeIntegralSchwartz_fderiv_space {d} (η : 𝓢(Time × Space d, ℝ)) (i : Fin d)
    (x : Space d) :
    timeIntegralSchwartz (SchwartzMap.evalCLM ℝ (Time × Space d) ℝ (0, basis i)
      (fderivCLM ℝ (Time × Space d) ℝ η)) x = fderiv ℝ (timeIntegralSchwartz η) x (basis i) := by
  have h := congrArg (fun f => f η)
    (constantTime_distSpaceDeriv i (Physlib.Distribution.diracDelta ℝ x))
  simpa [distSpaceDeriv_apply', constantTime_apply, distDeriv_apply,
    Physlib.Distribution.fderivD_apply] using h

/-- Some test function has a non-zero time integral at the origin. -/
lemma exists_integral_time_ne_zero {d} :
    ∃ η : 𝓢(Time × Space d, ℝ), ∫ t, η (t, 0) ≠ 0 := by
  let b : ContDiffBump (0 : Time × Space d) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨b.hasCompactSupport.toSchwartzMap b.contDiff, ne_of_gt ?_⟩
  have hsupp : HasCompactSupport fun t : Time => b (t, 0) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Time) 2) fun t ht =>
      b.zero_of_le_dist (by
        rw [Metric.mem_closedBall, not_le, dist_zero_right] at ht
        simpa [b, Prod.dist_eq] using ht.le)
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
    (by fun_prop) hsupp (fun t => b.nonneg) (b.pos_of_mem_ball (by simp [b])).ne'

end Space

namespace Electromagnetism
open Space SchwartzMap

namespace DistElectromagneticPotential

/-!

## B. The continuity equation

-/

/-- The continuity equation for distributions: Maxwell's equations imply local conservation of
charge. -/
theorem continuityEquation {d} {𝓕 : FreeSpace} (A : DistElectromagneticPotential d)
    (J : DistLorentzCurrentDensity d) (h : IsExtrema 𝓕 A J) (ε : 𝓢(Time × Space d, ℝ)) :
    distTimeDeriv (J.chargeDensity 𝓕.c) ε + distSpaceDiv (J.currentDensity 𝓕.c) ε = 0 := by
  obtain ⟨hG, hA⟩ := (isExtrema_iff_vectorPotential A J).mp h
  set E := A.electricField 𝓕.c
  set V := A.vectorPotential 𝓕.c
  -- Ampère's law, differentiated in the `i`-th direction.
  have hAi (i : Fin d) : 𝓕.μ₀ * 𝓕.ε₀ * distSpaceDeriv i (distTimeDeriv E) ε i +
      (∑ x, distSpaceDeriv i (distSpaceDeriv x (distSpaceDeriv x V)) ε i
        - ∑ x, distSpaceDeriv i (distSpaceDeriv x (distSpaceDeriv i V)) ε x) +
      𝓕.μ₀ * distSpaceDeriv i (J.currentDensity 𝓕.c) ε i = 0 := by
    have := hA ((SchwartzMap.evalCLM ℝ (Time × Space d) ℝ (0, basis i))
      ((fderivCLM ℝ (Time × Space d) ℝ) ε)) i
    simp only [apply_fderiv_eq_distSpaceDeriv] at this
    simp only [PiLp.neg_apply, neg_sub_neg, Finset.sum_neg_distrib, Finset.sum_sub_distrib] at this
    linear_combination -this
  -- The curl-curl terms cancel once summed over `i`.
  have hcurl : ∑ i, (∑ x, distSpaceDeriv i (distSpaceDeriv x (distSpaceDeriv x V)) ε i
      - ∑ x, distSpaceDeriv i (distSpaceDeriv x (distSpaceDeriv i V)) ε x) = 0 := by
    rw [Finset.sum_sub_distrib, sub_eq_zero, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
    rw [distSpaceDeriv_commute]
  -- Gauss's law gives the time derivative of the charge density.
  have hρ : J.chargeDensity 𝓕.c = 𝓕.ε₀ • distSpaceDiv E := by
    ext η
    rw [_root_.smul_apply, hG, smul_eq_mul, ← mul_assoc,
      mul_one_div_cancel 𝓕.ε₀_ne_zero, one_mul]
  have hsum := Finset.sum_eq_zero (s := Finset.univ) fun i (_ : i ∈ Finset.univ) => hAi i
  rw [hρ, map_smul, _root_.smul_apply, distTimeDeriv_distSpaceDiv, smul_eq_mul,
    distSpaceDiv_apply_eq_sum_distSpaceDeriv, distSpaceDiv_apply_eq_sum_distSpaceDeriv]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hcurl] at hsum
  apply mul_left_cancel₀ 𝓕.μ₀_ne_zero
  linear_combination hsum

end DistElectromagneticPotential

namespace DistLorentzCurrentDensity

open MeasureTheory Set

/-!

## C. Junctions of thin wires

### C.1. The current density of a junction

The `k`-th wire is the ray `s ↦ s • u k`, `s > 0`. A current `I k` along it has current density
`I k` times the unit tangent times the arc-length measure on the ray; in the parameter `s` this is
`I k • u k` times the Lebesgue measure, whatever the length of `u k`. The currents are steady, so
the pairing with a test function `η` only sees its time integral.

-/

/-- The current density of `J` is that of steady currents `I k` flowing away from the origin
along thin, straight, semi-infinite wires in the directions `u k`. -/
def IsWireJunction {d} (c : SpeedOfLight) (J : DistLorentzCurrentDensity d) {ι : Type}
    [Fintype ι] (u : ι → EuclideanSpace ℝ (Fin d)) (I : ι → ℝ) : Prop :=
  ∀ η, J.currentDensity c η =
    ∑ k, (I k * ∫ s in Ioi (0 : ℝ), timeIntegralSchwartz η (basis.repr.symm (s • u k))) • u k

/-- The wires of a junction meet at the origin, where they act as a source of strength the
total current leaving along them. -/
lemma IsWireJunction.distSpaceDiv_currentDensity {d} {c : SpeedOfLight}
    {J : DistLorentzCurrentDensity d} {ι : Type} [Fintype ι] {u : ι → EuclideanSpace ℝ (Fin d)}
    {I : ι → ℝ} (hJ : J.IsWireJunction c u I) (hu : ∀ k, u k ≠ 0) (η : 𝓢(Time × Space d, ℝ)) :
    distSpaceDiv (J.currentDensity c) η = (∑ k, I k) * ∫ t, η (t, 0) := by
  have hJ' : ∀ η, J.currentDensity c η = _ := hJ
  rw [distSpaceDiv_apply_eq_sum_distSpaceDeriv]
  simp only [distSpaceDeriv_apply', PiLp.neg_apply, hJ']
  simp only [timeIntegralSchwartz_fderiv_space, map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_neg_distrib, Finset.sum_comm, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [mul_assoc, ← Finset.mul_sum, integral_Ioi_fderiv_ray_basis _ (hu k),
    timeIntegralSchwartz_apply]
  ring

/-!

### C.2. The currents at a junction sum to zero

-/

/-- If Maxwell's equations hold and no charge accumulates, the steady currents leaving a junction
of thin wires sum to zero. This is motivated by Kirchhoff's current law, of which it is the
special case of a single node. -/
lemma IsWireJunction.sum_currents_eq_zero {d} {𝓕 : FreeSpace} {J : DistLorentzCurrentDensity d}
    {ι : Type} [Fintype ι] {u : ι → EuclideanSpace ℝ (Fin d)} {I : ι → ℝ}
    (hJ : J.IsWireJunction 𝓕.c u I) (hu : ∀ k, u k ≠ 0) (A : DistElectromagneticPotential d)
    (h : DistElectromagneticPotential.IsExtrema 𝓕 A J)
    (hρ : distTimeDeriv (J.chargeDensity 𝓕.c) = 0) :
    ∑ k, I k = 0 := by
  obtain ⟨η, hη⟩ := exists_integral_time_ne_zero (d := d)
  have hcont := DistElectromagneticPotential.continuityEquation A J h η
  rw [hρ, _root_.zero_apply, zero_add, hJ.distSpaceDiv_currentDensity hu] at hcont
  exact (mul_eq_zero.mp hcont).resolve_right hη

end DistLorentzCurrentDensity
end Electromagnetism
