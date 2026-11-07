/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.RetardedSolution
public import PhyslibAlpha.Mathematics.Calculus.SmoothDistance
public import PhyslibAlpha.Relativity.Causality.LightCone

/-!

# Finite propagation speed

The weighted local energy decreases.

## i. Overview

The weighted local energy decreases. The retarded solution vanishes outside the causal future of the
source.

## ii. Key results

- `energyDensity` : The energy density `‖v‖² + ∑ᵢ ‖pᵢ‖² + μ ‖u‖²`.
- `EnergyFields` : Fields with the pointwise derivatives needed for the energy identity of the
  Klein–Gordon equation, in the basis vectors `b i`.
- `e` : The energy density of the fields.
- `e'` : The time derivative of the energy density.
- `WeightFields` : A weight for the energy: smooth, compactly supported in space uniformly in time,
  decreasing in time, with a spatial gradient bounded by its time derivative.
- `flux` : The Lie derivative of the energy flux `⟪v, pᵢ⟫` along `b i`.
- `energyDeriv` : The time derivative of the weighted energy density.
- `coneWeight` : The cone weight `N (c - τ - ψ x)` as a weight for the energy estimate.

## iii. Table of contents

- A. The weighted local energy
- B. The cone weight
- C. Finite propagation speed for the homogeneous Klein–Gordon evolution
- D. Causal support of the retarded solution

## iv. References

None.

## A. The weighted local energy

- `energyDensity` : The energy density `‖v‖² + ∑ᵢ ‖pᵢ‖² + μ ‖u‖²`.
- `EnergyFields` : Fields with the pointwise derivatives needed for the energy identity of the
  Klein–Gordon equation, in the basis vectors `b i`.
- `e` : The energy density of the fields.
- `e'` : The time derivative of the energy density.
- `WeightFields` : A weight for the energy: smooth, compactly supported in space uniformly in time,
  decreasing in time, with a spatial gradient bounded by its time derivative.
- `flux` : The Lie derivative of the energy flux `⟪v, pᵢ⟫` along `b i`.
- `energyDeriv` : The time derivative of the weighted energy density.

Lemmas: `hasDerivAt_e`, `energy_integrand_nonneg`, `continuous_e`, `continuous_e'`,
`hasLineDerivAt_flux`, `e'_eq`, `continuous_energyDeriv`, `hasCompactSupport_of_vanishing`,
`hasDerivAt_energy`, `integral_energyDeriv` and more.

## B. The cone weight

- `coneWeight` : The cone weight `N (c - τ - ψ x)` as a weight for the energy estimate.

Lemmas: `continuous_coneArg`.

## C. Finite propagation speed for the homogeneous Klein–Gordon evolution

- `evolveFields` : The evolved field of the Cauchy data `(f0, f1)` as fields for the energy
  estimate, in the orthonormal basis `stdOrthonormalBasis`.

Lemmas: `evolveU_zero_time`, `evolveV_zero_time`, `sineEvolution_apply_eq_zero`,
`functional_sineEvolution`, `sineEvolution_apply_eq_zero'`.

## D. Causal support of the retarded solution

Lemmas: `sineEvolution_slice_eq_zero`, `solution_eq_zero_of_not_mem_causalFuture`,
`tsupport_solution_subset`, `advancedSolution_eq_zero_of_not_mem_causalPast`,
`tsupport_advancedSolution_subset`.

-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace SchwartzMap LineDeriv Distributions
open Duhamel FourierMultiplier SmoothDistance TimeSlice TimeSpace MeasureTheory Real
    TopologicalSpace Topology

namespace KleinGordon

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]

/-- The energy density `‖v‖² + ∑ᵢ ‖pᵢ‖² + μ ‖u‖²`. -/
def energyDensity {ι : Type*} [Fintype ι] (μ : ℝ) (u v : ℂ) (p : ι → ℂ) : ℝ :=
  ‖v‖ ^ 2 + ∑ i, ‖p i‖ ^ 2 + μ * ‖u‖ ^ 2

/-- Fields with the pointwise derivatives needed for the energy identity of the Klein–Gordon
equation, in the basis vectors `b i`. The field is `u` with velocity `v`, the spatial derivatives
are `p i`, the time derivatives of those are `q i`, and the second spatial derivatives are `s i`. -/
structure EnergyFields {ι : Type*} [Fintype ι] (μ : ℝ) (b : ι → E) where
  /-- The field. -/
  u : ℝ → E → ℂ
  /-- The velocity. -/
  v : ℝ → E → ℂ
  /-- The derivative of the field along `b i`. -/
  p : ι → ℝ → E → ℂ
  /-- The derivative of the velocity along `b i`. -/
  q : ι → ℝ → E → ℂ
  /-- The second derivative of the field along `b i`. -/
  s : ι → ℝ → E → ℂ
  hu : ∀ τ x, HasDerivAt (fun r => u r x) (v τ x) τ
  hv : ∀ τ x, HasDerivAt (fun r => v r x) (∑ i, s i τ x - μ • u τ x) τ
  hp : ∀ i τ x, HasDerivAt (fun r => p i r x) (q i τ x) τ
  hpx : ∀ i τ x, HasLineDerivAt ℝ (p i τ) (s i τ x) x (b i)
  hvx : ∀ i τ x, HasLineDerivAt ℝ (v τ) (q i τ x) x (b i)
  cu : Continuous fun z : ℝ × E => u z.1 z.2
  cv : Continuous fun z : ℝ × E => v z.1 z.2
  cp : ∀ i, Continuous fun z : ℝ × E => p i z.1 z.2
  cq : ∀ i, Continuous fun z : ℝ × E => q i z.1 z.2
  cs : ∀ i, Continuous fun z : ℝ × E => s i z.1 z.2
end

end KleinGordon

namespace KleinGordon.EnergyFields

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] {μ : ℝ} {b : ι → E} (D : EnergyFields μ b)

/-- The energy density of the fields. -/
def e (τ : ℝ) (x : E) : ℝ :=
  energyDensity μ (D.u τ x) (D.v τ x) (fun i => D.p i τ x)

/-- The time derivative of the energy density. -/
def e' (τ : ℝ) (x : E) : ℝ :=
  2 * inner ℝ (D.v τ x) (∑ i, D.s i τ x - μ • D.u τ x) +
    ∑ i, 2 * inner ℝ (D.p i τ x) (D.q i τ x) + μ * (2 * inner ℝ (D.u τ x) (D.v τ x))

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma hasDerivAt_e (τ : ℝ) (x : E) : HasDerivAt (fun r => D.e r x) (D.e' τ x) τ := by
  unfold e e' energyDensity
  have h1 := (D.hv τ x).norm_sq
  have h2 : HasDerivAt (fun r => ∑ i, ‖D.p i r x‖ ^ 2)
      (∑ i, 2 * inner ℝ (D.p i τ x) (D.q i τ x)) τ :=
    HasDerivAt.fun_sum fun i _ => (D.hp i τ x).norm_sq
  have h3 := ((D.hu τ x).norm_sq).const_mul μ
  exact (h1.add h2).add h3
end

end KleinGordon.EnergyFields

namespace KleinGordon

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]

/-- The pointwise inequality behind the monotonicity of the weighted energy. -/
lemma energy_integrand_nonneg {ι : Type*} [Fintype ι] (m V : ℝ) (hm : 0 ≤ m)
    (wg P G : ι → ℝ) (hP : ∀ i, 0 ≤ P i) (hG : ∀ i, |G i| ≤ V * P i)
    (hgrad : ∑ i, wg i ^ 2 ≤ m ^ 2) :
    0 ≤ m * (V ^ 2 + ∑ i, P i ^ 2) + 2 * ∑ i, wg i * G i := by
  set Y : ℝ := ∑ i, |wg i| * P i with hY
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hP i)
  have hX : |∑ i, wg i * G i| ≤ V * Y := by
    calc |∑ i, wg i * G i| ≤ ∑ i, |wg i * G i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, V * (|wg i| * P i) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          calc |wg i| * |G i| ≤ |wg i| * (V * P i) := by gcongr; exact hG i
            _ = V * (|wg i| * P i) := by ring
      _ = V * Y := by rw [hY, Finset.mul_sum]
  have hCS : Y ^ 2 ≤ (∑ i, wg i ^ 2) * ∑ i, P i ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |wg i|) P
    simpa [sq_abs] using this
  have hS : 0 ≤ ∑ i, P i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hY2 : Y ^ 2 ≤ m ^ 2 * ∑ i, P i ^ 2 :=
    hCS.trans (mul_le_mul_of_nonneg_right hgrad hS)
  have hneg : -(V * Y) ≤ ∑ i, wg i * G i := (abs_le.1 hX).1
  rcases hm.eq_or_lt with hm0 | hmpos
  · subst hm0
    have : Y ^ 2 ≤ 0 := by simpa using hY2
    have hY00 : Y = 0 := by nlinarith [sq_nonneg Y]
    rw [hY00] at hneg
    nlinarith
  · have key : 2 * V * Y ≤ m * (V ^ 2 + ∑ i, P i ^ 2) := by
      have h1 : 2 * V * m * Y ≤ m ^ 2 * V ^ 2 + Y ^ 2 := by nlinarith [sq_nonneg (m * V - Y)]
      have h2 : 2 * V * m * Y ≤ m * (m * (V ^ 2 + ∑ i, P i ^ 2)) := by nlinarith
      exact le_of_mul_le_mul_left (by nlinarith) hmpos
    nlinarith

/-- A weight for the energy: smooth, compactly supported in space uniformly in time, decreasing in
time, with a spatial gradient bounded by its time derivative. -/
structure WeightFields {ι : Type*} [Fintype ι] (b : ι → E) where
  /-- The weight. -/
  w : ℝ → E → ℝ
  /-- Its time derivative. -/
  wτ : ℝ → E → ℝ
  /-- Its derivative along `b i`. -/
  wg : ι → ℝ → E → ℝ
  hw : ∀ τ x, HasDerivAt (fun r => w r x) (wτ τ x) τ
  hwx : ∀ i τ x, HasLineDerivAt ℝ (w τ) (wg i τ x) x (b i)
  cw : Continuous fun z : ℝ × E => w z.1 z.2
  cwτ : Continuous fun z : ℝ × E => wτ z.1 z.2
  cwg : ∀ i, Continuous fun z : ℝ × E => wg i z.1 z.2
  /-- The radius of the common spatial support. -/
  R : ℝ
  hR : ∀ τ x, -1 ≤ τ → R < ‖x‖ → w τ x = 0 ∧ wτ τ x = 0 ∧ ∀ i, wg i τ x = 0
  sign : ∀ τ x, wτ τ x ≤ 0
  grad : ∀ τ x, ∑ i, wg i τ x ^ 2 ≤ wτ τ x ^ 2
end

end KleinGordon

namespace KleinGordon.EnergyFields

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] {μ : ℝ} {b : ι → E} (D : EnergyFields μ b)

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma continuous_e : Continuous fun z : ℝ × E => D.e z.1 z.2 := by
  unfold e energyDensity
  have := D.cv; have := D.cu
  refine ((D.cv.norm.pow 2).add (continuous_finsetSum _ fun i _ => (D.cp i).norm.pow 2)).add
    (continuous_const.mul (D.cu.norm.pow 2))

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma continuous_e' : Continuous fun z : ℝ × E => D.e' z.1 z.2 := by
  have hin : ∀ {f g : ℝ × E → ℂ}, Continuous f → Continuous g →
      Continuous fun z => (inner ℝ (f z) (g z) : ℝ) := fun hf hg => Continuous.inner hf hg
  unfold e'
  refine ((continuous_const.mul (hin D.cv
    ((continuous_finsetSum _ fun i _ => D.cs i).sub ((continuous_const (y := μ)).smul D.cu)))).add
    (continuous_finsetSum _ fun i _ =>
      continuous_const.mul (hin (D.cp i) (D.cq i)))).add
    (continuous_const.mul (continuous_const.mul (hin D.cu D.cv)))

/-- The Lie derivative of the energy flux `⟪v, pᵢ⟫` along `b i`. -/
def flux (i : ι) (τ : ℝ) (x : E) : ℝ := inner ℝ (D.v τ x) (D.p i τ x)

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma hasLineDerivAt_flux (i : ι) (τ : ℝ) (x : E) :
    HasLineDerivAt ℝ (D.flux i τ) (inner ℝ (D.q i τ x) (D.p i τ x) + inner ℝ (D.v τ x) (D.s i τ x))
      x (b i) := by
  have h := HasDerivAt.inner ℝ (D.hvx i τ x) (D.hpx i τ x)
  unfold HasLineDerivAt flux
  simpa [add_comm] using h

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma e'_eq (τ : ℝ) (x : E) : D.e' τ x =
    2 * ∑ i, (inner ℝ (D.q i τ x) (D.p i τ x) + inner ℝ (D.v τ x) (D.s i τ x)) := by
  unfold e'
  simp only [inner_sub_right, inner_sum, inner_smul_right, Finset.sum_add_distrib,
    Finset.mul_sum, mul_add, mul_sub, real_inner_comm (D.v τ x) (D.u τ x)]
  simp only [real_inner_comm (D.q _ τ x) (D.p _ τ x)]
  ring_nf
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] {μ : ℝ} {b : ι → E} (D : EnergyFields μ b)
variable (W : WeightFields b)

/-- The time derivative of the weighted energy density. -/
def energyDeriv (τ : ℝ) (x : E) : ℝ := W.wτ τ x * D.e τ x + W.w τ x * D.e' τ x

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma continuous_energyDeriv : Continuous fun z : ℝ × E => D.energyDeriv W z.1 z.2 :=
  (W.cwτ.mul D.continuous_e).add (W.cw.mul D.continuous_e')

omit [MeasurableSpace E] [BorelSpace E] in
lemma hasCompactSupport_of_vanishing (g : E → ℝ) (hg : ∀ x, W.R < ‖x‖ → g x = 0) :
    HasCompactSupport g :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) W.R) fun x hx => hg x (by simpa using hx)

lemma hasDerivAt_energy {τ0 : ℝ} (hτ0 : 0 ≤ τ0) :
    HasDerivAt (fun τ => ∫ x, W.w τ x * D.e τ x) (∫ x, D.energyDeriv W τ0 x) τ0 := by
  have hce := D.continuous_e
  have cF' := D.continuous_energyDeriv W
  have hFd : ∀ τ x, HasDerivAt (fun r => W.w r x * D.e r x) (D.energyDeriv W τ x) τ :=
    fun τ x => (W.hw τ x).mul (D.hasDerivAt_e τ x)
  have hF'0 : ∀ τ x, -1 ≤ τ → W.R < ‖x‖ → D.energyDeriv W τ x = 0 := fun τ x hτ hx => by
    simp [energyDeriv, (W.hR τ x hτ hx).1, (W.hR τ x hτ hx).2.1]
  have hF0 : ∀ τ x, -1 ≤ τ → W.R < ‖x‖ → W.w τ x * D.e τ x = 0 := fun τ x hτ hx => by
    simp [(W.hR τ x hτ hx).1]
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := τ0 - 1) (b := τ0 + 1)).prod
    (isCompact_closedBall (0 : E) W.R)).exists_bound_of_continuousOn cF'.continuousOn
  have hcx : ∀ τ, Continuous fun x : E => W.w τ x * D.e τ x := fun τ =>
    (W.cw.mul hce).comp (continuous_const.prodMk continuous_id)
  have hcx' : ∀ τ, Continuous fun x : E => D.energyDeriv W τ x := fun τ =>
    cF'.comp (continuous_const.prodMk continuous_id)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun τ x => W.w τ x * D.e τ x) (F' := D.energyDeriv W)
    (bound := (Metric.closedBall (0 : E) W.R).indicator fun _ => max C 0)
    (Metric.ball_mem_nhds τ0 one_pos)
    (Filter.Eventually.of_forall fun τ => (hcx τ).aestronglyMeasurable)
    ((hcx τ0).integrable_of_hasCompactSupport (hasCompactSupport_of_vanishing W _ (fun x hx => hF0
      τ0 x (by linarith) hx)))
    (hcx' τ0).aestronglyMeasurable ?_ ?_ ?_).2
  · refine Filter.Eventually.of_forall fun x τ hτ => ?_
    by_cases hx : ‖x‖ ≤ W.R
    · rw [Set.indicator_of_mem (by simpa using hx)]
      have hτ' : τ ∈ Set.Icc (τ0 - 1) (τ0 + 1) := by
        have := Metric.mem_ball.1 hτ
        rw [Real.dist_eq, abs_lt] at this
        exact ⟨by linarith, by linarith⟩
      exact (hC (τ, x) ⟨hτ', by simpa using hx⟩).trans (le_max_left _ _)
    · rw [hF'0 τ x (by have := Metric.mem_ball.1 hτ; rw [Real.dist_eq, abs_lt] at this; linarith)
      (not_le.1 hx)]
      simp only [norm_zero]
      exact Set.indicator_nonneg (fun _ _ => le_max_right _ _) _
  · exact (MeasureTheory.integrableOn_const (MeasureTheory.measure_closedBall_lt_top
      (x := (0 : E)) (r := W.R)).ne).integrable_indicator measurableSet_closedBall
  · exact Filter.Eventually.of_forall fun x τ _ => hFd τ x

set_option maxHeartbeats 1600000 in
lemma integral_energyDeriv {τ0 : ℝ} (hτ0 : 0 ≤ τ0) :
    ∫ x, D.energyDeriv W τ0 x =
      ∫ x, (W.wτ τ0 x * D.e τ0 x - 2 * ∑ i, W.wg i τ0 x * D.flux i τ0 x) := by
  have hin : ∀ {f g : ℝ × E → ℂ}, Continuous f → Continuous g →
      Continuous fun z => (inner ℝ (f z) (g z) : ℝ) := fun hf hg => Continuous.inner hf hg
  have hce := D.continuous_e
  have hce' := D.continuous_e'
  have cflux : ∀ i, Continuous fun x : E => D.flux i τ0 x := fun i =>
    (hin D.cv (D.cp i)).comp (continuous_const.prodMk continuous_id)
  have cDG : ∀ i, Continuous fun x : E =>
      (inner ℝ (D.q i τ0 x) (D.p i τ0 x) + inner ℝ (D.v τ0 x) (D.s i τ0 x)) := fun i =>
    ((hin (D.cq i) (D.cp i)).add (hin D.cv (D.cs i))).comp (continuous_const.prodMk continuous_id)
  have cw0 : Continuous fun x : E => W.w τ0 x := W.cw.comp (continuous_const.prodMk continuous_id)
  have cwg0 : ∀ i, Continuous fun x : E => W.wg i τ0 x := fun i =>
    (W.cwg i).comp (continuous_const.prodMk continuous_id)
  have hI : ∀ g : E → ℝ, Continuous g → (∀ x, W.R < ‖x‖ → g x = 0) →
      MeasureTheory.Integrable g MeasureTheory.volume := fun g hg h0 =>
    hg.integrable_of_hasCompactSupport (hasCompactSupport_of_vanishing W g h0)
  have iDG : ∀ i, MeasureTheory.Integrable (fun x : E => W.w τ0 x *
      (inner ℝ (D.q i τ0 x) (D.p i τ0 x) + inner ℝ (D.v τ0 x) (D.s i τ0 x)))
      MeasureTheory.volume := fun i =>
    hI _ (cw0.mul (cDG i)) fun x hx => by simp [(W.hR τ0 x (by linarith) hx).1]
  have iWG : ∀ i, MeasureTheory.Integrable (fun x : E => W.wg i τ0 x * D.flux i τ0 x)
      MeasureTheory.volume := fun i =>
    hI _ ((cwg0 i).mul (cflux i)) fun x hx => by simp [(W.hR τ0 x (by linarith) hx).2.2 i]
  have hibp : ∀ i, ∫ x, W.w τ0 x * (inner ℝ (D.q i τ0 x) (D.p i τ0 x) +
      inner ℝ (D.v τ0 x) (D.s i τ0 x)) = -∫ x, W.wg i τ0 x * D.flux i τ0 x := by
    intro i
    have := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (μ := MeasureTheory.volume) (B := ContinuousLinearMap.mul ℝ ℝ)
      (f := fun x => W.w τ0 x) (f' := fun x => W.wg i τ0 x) (g := D.flux i τ0)
      (g' := fun x => inner ℝ (D.q i τ0 x) (D.p i τ0 x) + inner ℝ (D.v τ0 x) (D.s i τ0 x))
      (v := b i) (iWG i) (iDG i)
      (hI _ (cw0.mul (cflux i)) fun x hx => by simp [(W.hR τ0 x (by linarith) hx).1])
      (fun x _ => W.hwx i τ0 x) (fun x _ => D.hasLineDerivAt_flux i τ0 x)
    simpa using this
  have cwτ0 : Continuous fun x : E => W.wτ τ0 x := W.cwτ.comp (continuous_const.prodMk
    continuous_id)
  have ce0 : Continuous fun x : E => D.e τ0 x := hce.comp (continuous_const.prodMk continuous_id)
  have ce'0 : Continuous fun x : E => D.e' τ0 x :=
    Continuous.comp (g := fun z : ℝ × E => D.e' z.1 z.2) (f := fun x : E => (τ0, x)) hce'
      (continuous_const.prodMk continuous_id)
  have iA : MeasureTheory.Integrable (fun x : E => W.wτ τ0 x * D.e τ0 x) MeasureTheory.volume :=
    hI _ (cwτ0.mul ce0) fun x hx => by simp [(W.hR τ0 x (by linarith) hx).2.1]
  have iW : MeasureTheory.Integrable (fun x : E => W.w τ0 x * D.e' τ0 x) MeasureTheory.volume :=
    hI _ (cw0.mul ce'0) fun x hx => by simp [(W.hR τ0 x (by linarith) hx).1]
  have h1 : ∫ x, D.energyDeriv W τ0 x =
      (∫ x, W.wτ τ0 x * D.e τ0 x) + ∫ x, W.w τ0 x * D.e' τ0 x :=
    MeasureTheory.integral_add iA iW
  have h2 : ∫ x, W.w τ0 x * D.e' τ0 x = -2 * ∑ i, ∫ x, W.wg i τ0 x * D.flux i τ0 x := by
    have : ∀ x, W.w τ0 x * D.e' τ0 x = 2 * ∑ i, W.w τ0 x *
        (inner ℝ (D.q i τ0 x) (D.p i τ0 x) + inner ℝ (D.v τ0 x) (D.s i τ0 x)) := by
      intro x; rw [D.e'_eq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    simp_rw [this]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum _ fun i _ => iDG i]
    simp_rw [hibp]
    rw [Finset.sum_neg_distrib]; ring
  have h3 : ∫ x, (W.wτ τ0 x * D.e τ0 x - 2 * ∑ i, W.wg i τ0 x * D.flux i τ0 x) =
      (∫ x, W.wτ τ0 x * D.e τ0 x) - 2 * ∑ i, ∫ x, W.wg i τ0 x * D.flux i τ0 x := by
    rw [MeasureTheory.integral_sub iA
      ((MeasureTheory.integrable_finsetSum _ fun i _ => iWG i).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum _ fun i _ => iWG i]
  rw [h3, h1, h2]; ring

lemma integral_energyDeriv_nonpos (hμ : 0 ≤ μ) {τ0 : ℝ} (hτ0 : 0 ≤ τ0) : ∫ x, D.energyDeriv W τ0 x ≤
    0 := by
  rw [integral_energyDeriv D W hτ0]
  refine MeasureTheory.integral_nonpos fun x => ?_
  show W.wτ τ0 x * D.e τ0 x - 2 * ∑ i, W.wg i τ0 x * D.flux i τ0 x ≤ 0
  have hm : 0 ≤ -W.wτ τ0 x := neg_nonneg.2 (W.sign τ0 x)
  have key := energy_integrand_nonneg (-W.wτ τ0 x) ‖D.v τ0 x‖ hm
    (fun i => W.wg i τ0 x) (fun i => ‖D.p i τ0 x‖) (fun i => D.flux i τ0 x)
    (fun i => norm_nonneg _) (fun i => abs_real_inner_le_norm _ _)
    (by simpa using W.grad τ0 x)
  have hμ0 : 0 ≤ μ * ‖D.u τ0 x‖ ^ 2 := mul_nonneg hμ (sq_nonneg _)
  have he : D.e τ0 x = ‖D.v τ0 x‖ ^ 2 + ∑ i, ‖D.p i τ0 x‖ ^ 2 + μ * ‖D.u τ0 x‖ ^ 2 := rfl
  rw [he]
  nlinarith [key, mul_nonneg hm hμ0]

/-- The weighted energy is non-increasing in time, for nonnegative times. -/
lemma antitoneOn_energy (hμ : 0 ≤ μ) :
    AntitoneOn (fun τ => ∫ x, W.w τ x * D.e τ x) (Set.Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
  · intro τ hτ
    exact (D.hasDerivAt_energy W hτ).continuousAt.continuousWithinAt
  · intro τ hτ
    exact (D.hasDerivAt_energy W (interior_subset hτ)).differentiableAt.differentiableWithinAt
  · intro τ hτ
    rw [(D.hasDerivAt_energy W (by simpa using interior_subset hτ)).deriv]
    exact D.integral_energyDeriv_nonpos W hμ (by simpa using interior_subset hτ)
end

end KleinGordon.EnergyFields

namespace KleinGordon

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma continuous_coneArg (ε c : ℝ) (x₀ : E) :
    Continuous fun z : ℝ × E => c - z.1 - smoothDist ε x₀ z.2 :=
  (continuous_const.sub continuous_fst).sub ((continuous_smoothDist ε x₀).comp continuous_snd)

/-- The cone weight `N (c - τ - ψ x)` as a weight for the energy estimate. -/
def coneWeight {ε : ℝ} (hε : 0 < ε) (x₀ : E) (c : ℝ) :
    WeightFields (fun i : Fin (Module.finrank ℝ E) => stdOrthonormalBasis ℝ E i) where
  w τ x := expNegInvGlue (c - τ - smoothDist ε x₀ x)
  wτ τ x := -deriv expNegInvGlue (c - τ - smoothDist ε x₀ x)
  wg i τ x := -deriv expNegInvGlue (c - τ - smoothDist ε x₀ x) *
    (inner ℝ (x - x₀) (stdOrthonormalBasis ℝ E i) / smoothDist ε x₀ x)
  hw τ x := by
    have h1 : HasDerivAt (fun r : ℝ => c - r - smoothDist ε x₀ x) (-1) τ :=
      ((hasDerivAt_id τ).const_sub c).sub_const _ |>.congr_deriv (by simp)
    have := (hasDerivAt_expNegInvGlue (c - τ - smoothDist ε x₀ x)).comp τ h1
    exact this.congr_deriv (by ring)
  hwx i τ x := by
    have hg : HasFDerivAt (fun y : E => c - τ - smoothDist ε x₀ y)
        (-((1 / smoothDist ε x₀ x) • innerSL ℝ (x - x₀))) x :=
      ((hasFDerivAt_smoothDist hε x₀ x).const_sub (c - τ)) |>.congr_fderiv (by simp)
    have := ((hasDerivAt_expNegInvGlue (c - τ - smoothDist ε x₀ x)).comp_hasFDerivAt x
      hg).hasLineDerivAt
      (stdOrthonormalBasis ℝ E i)
    refine this.congr_deriv ?_
    simp only [smul_apply, neg_apply, innerSL_apply_apply, smul_eq_mul]
    ring
  cw := (expNegInvGlue.contDiff (n := 0)).continuous.comp (continuous_coneArg ε c x₀)
  cwτ := (continuous_deriv_expNegInvGlue.comp (continuous_coneArg ε c x₀)).neg
  cwg i := by
    have h2 : Continuous fun z : ℝ × E =>
        inner ℝ (z.2 - x₀) (stdOrthonormalBasis ℝ E i) / smoothDist ε x₀ z.2 :=
      ((continuous_snd.sub continuous_const).inner continuous_const).div
        ((continuous_smoothDist ε x₀).comp continuous_snd) fun z => (smoothDist_pos hε x₀ z.2).ne'
    exact (continuous_deriv_expNegInvGlue.comp (continuous_coneArg ε c x₀)).neg.mul h2
  R := c + 1 + ‖x₀‖
  hR τ x hτ hx := by
    have hpsi : c - τ < smoothDist ε x₀ x := by
      have h1 : ‖x‖ - ‖x₀‖ ≤ ‖x - x₀‖ := by
        have := norm_sub_norm_le x x₀
        linarith
      have h2 := norm_sub_le_smoothDist ε x₀ x
      linarith
    have hneg : c - τ - smoothDist ε x₀ x ≤ 0 := by linarith
    refine ⟨expNegInvGlue.zero_of_nonpos hneg, ?_, fun i => ?_⟩
    · simp [deriv_expNegInvGlue_of_nonpos hneg]
    · simp [deriv_expNegInvGlue_of_nonpos hneg]
  sign τ x := neg_nonpos.2 (deriv_expNegInvGlue_nonneg _)
  grad τ x := by
    set N' := deriv expNegInvGlue (c - τ - smoothDist ε x₀ x)
    have hψ := smoothDist_pos hε x₀ x
    have hsum : ∑ i : Fin (Module.finrank ℝ E),
        (inner ℝ (x - x₀) (stdOrthonormalBasis ℝ E i)) ^ 2 = ‖x - x₀‖ ^ 2 := by
      rw [← (stdOrthonormalBasis ℝ E).sum_sq_inner_right (x - x₀)]
      exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm]
    have hle : ‖x - x₀‖ ^ 2 / smoothDist ε x₀ x ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      have := norm_sub_le_smoothDist ε x₀ x
      nlinarith [norm_nonneg (x - x₀)]
    calc ∑ i, (-N' * (inner ℝ (x - x₀) (stdOrthonormalBasis ℝ E i) / smoothDist ε x₀ x)) ^ 2
        = N' ^ 2 * (‖x - x₀‖ ^ 2 / smoothDist ε x₀ x ^ 2) := by
          simp_rw [mul_pow, div_pow, neg_sq]
          rw [← Finset.mul_sum, ← Finset.sum_div, hsum]
      _ ≤ N' ^ 2 * 1 := by gcongr
      _ = (-N') ^ 2 := by ring
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]

/-- The evolved field of the Cauchy data `(f0, f1)` as fields for the energy estimate, in the
orthonormal basis `stdOrthonormalBasis`. -/
def evolveFields {μ : ℝ} (hμ : 0 ≤ μ) (f0 f1 : 𝓢(E, ℂ)) :
    EnergyFields μ (fun i : Fin (Module.finrank ℝ E) => stdOrthonormalBasis ℝ E i) where
  u τ x := evolveU μ τ f0 f1 x
  v τ x := evolveV μ τ f0 f1 x
  p i τ x := (∂_{stdOrthonormalBasis ℝ E i} (evolveU μ τ f0 f1)) x
  q i τ x := (∂_{stdOrthonormalBasis ℝ E i} (evolveV μ τ f0 f1)) x
  s i τ x := (∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E i} (evolveU μ τ f0 f1))) x
  hu τ x := hasDerivAt_evolveU hμ f0 f1 x τ
  hv τ x := by
    have h := hasDerivAt_evolveV hμ f0 f1 x τ
    convert h using 1
    rw [frequencySqOperator_eq, SchwartzMap.laplacian_eq_sum (stdOrthonormalBasis ℝ E)]
    simp only [Complex.real_smul, add_apply, neg_apply, sum_apply, smul_apply, neg_add_rev, neg_neg]
    ring
  hp i τ x := by
    simp_rw [lineDeriv_evolveU hμ]
    rw [lineDeriv_evolveV hμ]
    exact hasDerivAt_evolveU hμ _ _ x τ
  hpx i τ x := hasLineDerivAt_lineDerivOp _ _ _
  hvx i τ x := hasLineDerivAt_lineDerivOp _ _ _
  cu := continuous_evolveU_apply hμ f0 f1
  cv := continuous_evolveV_apply hμ f0 f1
  cp i := by
    simp_rw [lineDeriv_evolveU hμ]
    exact continuous_evolveU_apply hμ _ _
  cq i := by
    simp_rw [lineDeriv_evolveV hμ]
    exact continuous_evolveV_apply hμ _ _
  cs i := by
    simp_rw [lineDeriv_evolveU hμ]
    exact continuous_evolveU_apply hμ _ _

lemma evolveU_zero_time (μ : ℝ) (a b : 𝓢(E, ℂ)) : evolveU μ 0 a b = a := by
  simp [evolveU, cosEvolution_zero, sineEvolution_zero]

lemma evolveV_zero_time (μ : ℝ) (a b : 𝓢(E, ℂ)) : evolveV μ 0 a b = b := by
  simp [evolveV, cosEvolution_zero, sineEvolution_zero]

/-- **Finite propagation speed.** If the initial velocity `g` vanishes on the ball of radius
`r + δ` about `x₀` then the sine evolution over the time `r ≥ 0` vanishes at `x₀`. -/
lemma sineEvolution_apply_eq_zero {μ : ℝ} (hμ : 0 ≤ μ) (g : 𝓢(E, ℂ)) (x₀ : E) {r δ : ℝ}
    (hr : 0 ≤ r) (hδ : 0 < δ) (hg : ∀ y, g y ≠ 0 → r + δ ≤ ‖y - x₀‖) :
    sineEvolution ℂ r μ g x₀ = 0 := by
  set ε : ℝ := δ / 4 with hεdef
  have hε : 0 < ε := by positivity
  set c : ℝ := r + δ / 2 with hcdef
  set D := evolveFields hμ (0 : 𝓢(E, ℂ)) g with hD
  set W := coneWeight hε x₀ c with hW
  have hu : ∀ τ x, D.u τ x = evolveU μ τ 0 g x := fun _ _ => rfl
  have hv : ∀ τ x, D.v τ x = evolveV μ τ 0 g x := fun _ _ => rfl
  -- the initial energy vanishes
  have h0 : ∫ x, W.w 0 x * D.e 0 x = 0 := by
    refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hgx : g x = 0
    · have hv0 : D.v 0 x = 0 := by rw [hv, evolveV_zero_time]; exact hgx
      have hu0 : D.u 0 x = 0 := by rw [hu, evolveU_zero_time]; rfl
      have hp0 : ∀ i, D.p i 0 x = 0 := by
        intro i
        change (∂_{stdOrthonormalBasis ℝ E i} (evolveU μ 0 0 g)) x = 0
        rw [evolveU_zero_time]; simp
      simp [EnergyFields.e, energyDensity, hv0, hu0, hp0]
    · have hge := hg x hgx
      have : W.w 0 x = 0 := by
        change expNegInvGlue (c - 0 - smoothDist ε x₀ x) = 0
        refine expNegInvGlue.zero_of_nonpos ?_
        have := norm_sub_le_smoothDist ε x₀ x
        linarith
      simp [this]
  have hwnn : ∀ τ x, 0 ≤ W.w τ x := fun τ x => expNegInvGlue.nonneg _
  have hennn : ∀ τ x, 0 ≤ D.e τ x := fun τ x => by
    unfold EnergyFields.e energyDensity; positivity
  have hnonneg : ∀ τ, 0 ≤ ∫ x, W.w τ x * D.e τ x := fun τ =>
    MeasureTheory.integral_nonneg fun x => mul_nonneg (hwnn τ x) (hennn τ x)
  have hanti := D.antitoneOn_energy W hμ
  have hEzero : ∀ τ, 0 ≤ τ → ∫ x, W.w τ x * D.e τ x = 0 := fun τ hτ =>
    le_antisymm ((hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hτ) hτ).trans h0.le) (hnonneg τ)
  have hpt : ∀ τ, 0 ≤ τ → ∀ x, W.w τ x * D.e τ x = 0 := by
    intro τ hτ
    have hc : Continuous fun x : E => W.w τ x * D.e τ x :=
      (W.cw.mul (D.continuous_e)).comp (continuous_const.prodMk continuous_id)
    have hi : MeasureTheory.Integrable (fun x : E => W.w τ x * D.e τ x) MeasureTheory.volume :=
      hc.integrable_of_hasCompactSupport (EnergyFields.hasCompactSupport_of_vanishing W _
        fun x hx => by simp [(W.hR τ x (by linarith) hx).1])
    have := (MeasureTheory.integral_eq_zero_iff_of_nonneg
      (fun x => mul_nonneg (hwnn τ x) (hennn τ x)) hi).1 (hEzero τ hτ)
    have h := (Continuous.ae_eq_iff_eq MeasureTheory.volume hc (continuous_const (y := (0 : ℝ)))).1
      this
    exact fun x => congrFun h x
  have hwpos : ∀ τ, τ ≤ r → 0 < W.w τ x₀ := by
    intro τ hτ
    change 0 < expNegInvGlue (c - τ - smoothDist ε x₀ x₀)
    refine expNegInvGlue.pos_of_pos ?_
    have : smoothDist ε x₀ x₀ = ε := by simp [smoothDist, Real.sqrt_sq hε.le]
    rw [this, hcdef, hεdef]; linarith
  have hv0 : ∀ τ ∈ Set.Icc 0 r, D.v τ x₀ = 0 := by
    intro τ hτ
    have h1 := hpt τ hτ.1 x₀
    have h2 : D.e τ x₀ = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h (hwpos τ hτ.2).ne'
      · exact h
    have h3 : ‖D.v τ x₀‖ ^ 2 = 0 := by
      have : D.e τ x₀ = ‖D.v τ x₀‖ ^ 2 + ∑ i, ‖D.p i τ x₀‖ ^ 2 + μ * ‖D.u τ x₀‖ ^ 2 := rfl
      have hs : 0 ≤ ∑ i, ‖D.p i τ x₀‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      have hm : 0 ≤ μ * ‖D.u τ x₀‖ ^ 2 := mul_nonneg hμ (sq_nonneg _)
      nlinarith [sq_nonneg ‖D.v τ x₀‖]
    exact norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 h3)
  have hderiv : ∀ τ ∈ Set.Icc 0 r,
      HasDerivWithinAt (fun τ => D.u τ x₀) (0 : ℂ) (Set.Icc 0 r) τ := by
    intro τ hτ
    have := (D.hu τ x₀).hasDerivWithinAt (s := Set.Icc 0 r)
    rwa [hv0 τ hτ] at this
  have hconst := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun τ => D.u τ x₀)
    (f' := fun _ => (0 : ℂ)) (C := 0) hderiv (fun _ _ => by simp) (convex_Icc 0 r)
    (Set.left_mem_Icc.2 hr) (Set.right_mem_Icc.2 hr)
  have hu0 : D.u 0 x₀ = 0 := by rw [hu, evolveU_zero_time]; rfl
  have hur : D.u r x₀ = 0 := by
    have : ‖D.u r x₀ - D.u 0 x₀‖ ≤ 0 := by simpa using hconst
    rw [hu0, sub_zero] at this
    exact norm_le_zero_iff.1 this
  have : sineEvolution ℂ r μ g x₀ = D.u r x₀ := by
    rw [hu]; simp [evolveU]
  rw [this, hur]
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A continuous linear functional commutes with the sine evolution. -/
lemma functional_sineEvolution {μ : ℝ} (hμ : 0 ≤ μ) (ℓ : F →L[ℂ] ℂ) (r : ℝ) (g : 𝓢(E, F)) (x : E) :
    ℓ (sineEvolution F r μ g x) =
      sineEvolution ℂ r μ (SchwartzMap.postcompCLM (𝕜 := ℂ) (E := E) ℓ g) x := by
  rw [sineEvolution_apply_eq F r hμ, sineEvolution_apply_eq ℂ r hμ]
  simp only [Circle.smul_def]
  have hint := integrable_fourier_integrand (hasTemperateGrowth_multiplier (E := E) r hμ) g x
  have := ContinuousLinearMap.integral_comp_comm (ℓ.restrictScalars ℝ) hint
  simp only [ContinuousLinearMap.coe_restrictScalars'] at this
  rw [← this]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [map_smul, functional_fourier]

/-- **Finite propagation speed for vector-valued data.** -/
lemma sineEvolution_apply_eq_zero' {μ : ℝ} (hμ : 0 ≤ μ) (g : 𝓢(E, F)) (x₀ : E) {r δ : ℝ}
    (hr : 0 ≤ r) (hδ : 0 < δ) (hg : ∀ y, g y ≠ 0 → r + δ ≤ ‖y - x₀‖) :
    sineEvolution F r μ g x₀ = 0 := by
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ) fun ℓ => ?_
  rw [functional_sineEvolution hμ ℓ r g x₀]
  refine sineEvolution_apply_eq_zero hμ _ x₀ hr hδ fun y hy => hg y fun h0 => hy ?_
  change ℓ (g y) = 0
  simp [h0]
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (f : 𝓓((⊤ : Opens (ℝ × E)), F))

/-- Each slice of the source propagates only inside the light cone. -/
lemma sineEvolution_slice_eq_zero {μ : ℝ} (hμ : 0 ≤ μ) {s t : ℝ} (hst : s ≤ t) {x₀ : E}
    (hfut : ∀ y, (s, y) ∈ tsupport f → t - s < ‖y - x₀‖) :
    sineEvolution F (t - s) μ (slice F f s) x₀ = 0 := by
  have hA : IsCompact {y : E | (s, y) ∈ tsupport f} :=
    (isClosedEmbedding_prodMk s).isCompact_preimage f.hasCompactSupport.isCompact
  by_cases hne : {y : E | (s, y) ∈ tsupport f}.Nonempty
  · obtain ⟨y₀, hy₀, hmin⟩ := hA.exists_isMinOn hne
      ((continuous_id.sub continuous_const).norm.continuousOn : ContinuousOn (fun y : E => ‖y - x₀‖)
        _)
    have hδ : 0 < ‖y₀ - x₀‖ - (t - s) := sub_pos.2 (hfut y₀ hy₀)
    refine sineEvolution_apply_eq_zero' (r := t - s) (δ := ‖y₀ - x₀‖ - (t - s)) hμ _ x₀ (by
      linarith) hδ ?_
    intro y hy
    have hy' : (s, y) ∈ tsupport f := subset_tsupport _ (by simpa using hy)
    have := hmin hy'
    have hm : ‖y₀ - x₀‖ ≤ ‖y - x₀‖ := by simpa using this
    linarith
  · have : slice F f s = 0 := by
      ext y
      by_contra hy
      exact hne ⟨y, subset_tsupport _ (by simpa using hy)⟩
    rw [this]; simp

/-- **Causal support.** The retarded solution vanishes outside the causal future of the support of
the source. -/
lemma solution_eq_zero_of_not_mem_causalFuture {μ : ℝ} (hμ : 0 ≤ μ) {t : ℝ} {x₀ : E}
    (h : (t, x₀) ∉ causalFuture (tsupport f)) : solution F f μ t x₀ = 0 := by
  unfold solution duhamel
  refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
  rw [propagatedSlice_eq_sineEvolution F f hμ]
  refine sineEvolution_slice_eq_zero F f hμ hs ?_
  intro y hy
  by_contra hle
  exact h ⟨(s, y), hy, by simpa [norm_sub_rev] using not_lt.1 hle⟩

/-- The topological support of the retarded field lies in the source's causal future. -/
lemma tsupport_solution_subset {μ : ℝ} (hμ : 0 ≤ μ) :
    tsupport (fun p : ℝ × E => solution F f μ p.1 p.2) ⊆ causalFuture (tsupport f) := by
  apply closure_minimal _ (isClosed_causalFuture f.hasCompactSupport)
  intro p hp
  by_contra h
  exact hp (solution_eq_zero_of_not_mem_causalFuture F f hμ h)

/-- **Causal support of the advanced solution.** -/
lemma advancedSolution_eq_zero_of_not_mem_causalPast {μ : ℝ} (hμ : 0 ≤ μ) {t : ℝ} {x₀ : E}
    (h : (t, x₀) ∉ causalPast (tsupport f)) : advancedSolution F f μ t x₀ = 0 := by
  refine solution_eq_zero_of_not_mem_causalFuture F (reflect F f) hμ ?_
  rintro ⟨q, hq, hle⟩
  rw [tsupport_reflect] at hq
  refine h ⟨timeReflect q, hq, ?_⟩
  simp only [timeReflect_apply] at hle ⊢
  linarith

/-- The topological support of the advanced field lies in the source's causal past. -/
lemma tsupport_advancedSolution_subset {μ : ℝ} (hμ : 0 ≤ μ) :
    tsupport (fun p : ℝ × E => advancedSolution F f μ p.1 p.2) ⊆ causalPast (tsupport f) := by
  have he : (fun p : ℝ × E => advancedSolution F f μ p.1 p.2) =
      (fun p : ℝ × E => solution F (reflect F f) μ p.1 p.2) ∘ timeReflect := rfl
  rw [he, tsupport, Function.support_comp_eq_preimage, ← Homeomorph.preimage_closure]
  intro p hp
  obtain ⟨q, hq, hle⟩ := tsupport_solution_subset F (reflect F f) hμ hp
  rw [tsupport_reflect] at hq
  refine ⟨timeReflect q, hq, ?_⟩
  simp only [timeReflect_apply] at hle ⊢
  linarith
end

end KleinGordon
