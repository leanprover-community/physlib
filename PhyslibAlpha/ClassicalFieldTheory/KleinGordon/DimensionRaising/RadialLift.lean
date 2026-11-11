/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.DimensionRaising.SpaceSplit

/-!

# Smooth radial lifts

A smooth radial source in `d` space dimensions and its lift to `d + 2` dimensions.

## i. Overview

A radial test function is a smooth function `P` of the squared norm. Its lift to two more space
dimensions is `-(1/π) P'` of the squared norm. This is `-(1/(2π ρ)) ∂ρ` of the profile `P(ρ²)`,
written without the singular factor `1/ρ`. The integral of the lift over the plane is the original
function.

## ii. Key results

- `integral_tail_sq` : the tail integral of `u P'(u²)`.
- `integral_plane_lift` : the integral of the lifted profile over the plane.
- `radialSource` : the radial source `P(s, ‖x‖²)` as a test function.
- `liftProfile` : the lift `-(1/π) ∂_q P` of a profile to two more space dimensions.
- `radialSource_marginal` : the lifted radial source integrates to the original one.
- `hasDerivAt_solution_radialSource` : dimension raising for a smooth radial source.
- `transportSource_spaceThree` : a radial source on the Euclidean three-space is radial on
  `Space 3`.

## iii. Table of contents

- A. The tail integral
- B. The plane integral of the lift
- C. Radial sources
- D. Dimension raising

## iv. References

None.

## A. The tail integral

- `integral_tail_sq` : the tail integral of `u P'(u²)`.

## B. The plane integral of the lift

- `integral_plane_lift` : the integral of the lifted profile over the plane.

## C. Radial sources

- `radialSource` : the radial source `P(s, ‖x‖²)` as a test function.
- `liftProfile` : the lift `-(1/π) ∂_q P` of a profile to two more space dimensions.
- `radialSource_marginal` : the lifted radial source integrates to the original one.

## D. Dimension raising

- `hasDerivAt_solution_radialSource` : dimension raising for a smooth radial source.
- `transportSource_spaceThree` : a radial source on the Euclidean three-space is radial on
  `Space 3`.
-/

@[expose] public section

noncomputable section

open scoped ContDiff Distributions
open MeasureTheory Set Filter Topology RadialPlane

namespace KleinGordon

section Source

variable (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The radial source `(s, x) ↦ P (s, ‖x‖²)` built from a test function `P` of time and the squared
radius. -/
def radialSource (P : 𝓓((⊤ : TopologicalSpace.Opens (ℝ × ℝ)), ℂ)) :
    𝓓((⊤ : TopologicalSpace.Opens (ℝ × V)), ℂ) where
  toFun z := P (z.1, ‖z.2‖ ^ 2)
  contDiff' := P.contDiff.comp (contDiff_fst.prodMk ((contDiff_norm_sq ℝ).comp contDiff_snd))
  hasCompactSupport' := by
    obtain ⟨R, hR⟩ := P.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × V) (max R 0 + 1)) fun z hz => ?_
    by_contra hne
    have hmem : (z.1, ‖z.2‖ ^ 2) ∈ tsupport P := subset_tsupport _ hne
    have := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at this
    simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖z.2‖)] at this
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hz
    apply hz
    have h1 : |z.1| ≤ R := (le_max_left _ _).trans this
    have h2 : ‖z.2‖ ^ 2 ≤ R := (le_max_right _ _).trans this
    refine max_le (by rw [Real.norm_eq_abs]; linarith [le_max_left R 0]) ?_
    nlinarith [le_max_left R 0, le_max_right R 0, norm_nonneg z.2]
  tsupport_subset' := fun _ _ => trivial

lemma radialSource_apply (P : 𝓓((⊤ : TopologicalSpace.Opens (ℝ × ℝ)), ℂ)) (s : ℝ) (x : V) :
    radialSource V P (s, x) = P (s, ‖x‖ ^ 2) := rfl

end Source

/-- The tail integral of `u P'(u²)` is `-P(ρ²) / 2` for a smooth compactly supported profile. -/
lemma integral_tail_sq {P : ℝ → ℂ} (hP : ContDiff ℝ ∞ P) (hc : HasCompactSupport P) (ρ : ℝ) :
    ∫ u in Ioi ρ, u • deriv P (u ^ 2) = -(P (ρ ^ 2) / 2) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  set S : ℝ := max R 0 + 1 with hS
  have hout : ∀ u : ℝ, S < |u| → P (u ^ 2) = 0 ∧ deriv P (u ^ 2) = 0 := fun u hu => by
    have hu2 : u ^ 2 ∉ tsupport P := fun h => by
      have := hR h
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg u)]
        at this
      nlinarith [le_max_left R 0, abs_nonneg u, sq_abs u, le_abs_self u]
    exact ⟨image_eq_zero_of_notMem_tsupport hu2,
      image_eq_zero_of_notMem_tsupport fun h => hu2 (tsupport_deriv_subset h)⟩
  have hdc : Continuous (deriv P) := hP.continuous_deriv (by simp)
  have hf' : Continuous fun u : ℝ => u • deriv P (u ^ 2) :=
    continuous_id.smul (hdc.comp (continuous_pow 2))
  have hf'c : HasCompactSupport fun u : ℝ => u • deriv P (u ^ 2) :=
    HasCompactSupport.intro (isCompact_Icc (a := -S) (b := S)) fun u hu => by
      have : S < |u| := by
        by_contra h
        exact hu (Set.mem_Icc.2 (abs_le.1 (not_lt.1 h)))
      simp [(hout u this).2]
  have hderiv : ∀ x : ℝ, HasDerivAt (fun u => P (u ^ 2) / 2) (x • deriv P (x ^ 2)) x := fun x => by
    have h1 : HasDerivAt P (deriv P (x ^ 2)) (x ^ 2) :=
      (hP.differentiable (by simp) (x ^ 2)).hasDerivAt
    have h2 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h3 : HasDerivAt (fun u : ℝ => P (u ^ 2)) ((2 * x) • deriv P (x ^ 2)) x :=
      HasDerivAt.scomp (g₁ := P) (h := fun u : ℝ => u ^ 2) x h1 h2
    have h4 := h3.div_const 2
    convert h4 using 1
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  have hlim : Tendsto (fun u : ℝ => P (u ^ 2) / 2) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop S] with u hu
    have : S < |u| := lt_of_lt_of_le hu (le_abs_self u)
    simp [(hout u this).1]
  have := integral_Ioi_of_hasDerivAt_of_tendsto' (a := ρ) (fun x _ => hderiv x)
    (hf'.integrable_of_hasCompactSupport hf'c).integrableOn hlim
  rw [this]
  ring

/-- The plane integral of the lift at a given radius: the lifted profile integrates to the
original profile. -/
lemma integral_plane_lift {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    ∫ y : EuclideanSpace ℝ (Fin 2), (-(1 / Real.pi : ℝ) : ℝ) • deriv g (ρ ^ 2 + ‖y‖ ^ 2) =
      g (ρ ^ 2) := by
  set Φ : ℝ → ℂ := fun u => (-(1 / Real.pi : ℝ) : ℝ) • deriv g (u ^ 2) with hΦ
  have hdc : Continuous (deriv g) := hg.continuous_deriv (by simp)
  have hΦc : Continuous Φ := by
    simp only [hΦ]
    exact (hdc.comp (continuous_pow 2)).const_smul (-(1 / Real.pi : ℝ) : ℝ)
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  have hvan : ∀ u : ℝ, max R 0 + 1 < u → Φ u = 0 := fun u hu => by
    have hu2 : u ^ 2 ∉ tsupport g := fun h => by
      have := hR h
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg u)]
        at this
      nlinarith [le_max_left R 0, le_max_right R 0]
    have : deriv g (u ^ 2) = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hu2 (tsupport_deriv_subset h)
    simp [hΦ, this]
  have hdecay := radialDecay_of_vanishing hΦc hvan
  have hΦ' : ∀ y : EuclideanSpace ℝ (Fin 2), (-(1 / Real.pi : ℝ) : ℝ) • deriv g (ρ ^ 2 + ‖y‖ ^ 2) =
      Φ (Real.sqrt (ρ ^ 2 + ‖y‖ ^ 2)) := fun y => by
    simp only [hΦ]
    rw [Real.sq_sqrt (by positivity)]
  have hint : ∫ u in Ioi ρ, u • Φ u = -(1 / Real.pi : ℝ) • ∫ u in Ioi ρ, u • deriv g (u ^ 2) := by
    rw [← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hΦ, Complex.real_smul]
    ring
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfin : (2 * Real.pi : ℝ) • (-(1 / Real.pi : ℝ) • (-(g (ρ ^ 2) / 2))) = g (ρ ^ 2) := by
    simp only [Complex.real_smul]
    push_cast
    field_simp
  simp_rw [hΦ']
  rcases hρ.eq_or_lt with h | h
  · subst h
    have h0 := integral_plane_radial_zero Φ
    have h1 : ∀ y : EuclideanSpace ℝ (Fin 2), Φ (Real.sqrt (0 ^ 2 + ‖y‖ ^ 2)) = Φ ‖y‖ := fun y => by
      rw [zero_pow two_ne_zero, zero_add, Real.sqrt_sq (norm_nonneg _)]
    simp_rw [h1]
    rw [h0]
    rw [hint, integral_tail_sq hg hc 0, hfin]
  · have h0 := integral_plane_radial hdecay h
    rw [h0, hint, integral_tail_sq hg hc ρ, hfin]

/-- The lift of a profile to two more space dimensions: `-(1/π) ∂_q P`. -/
def liftProfile (P : 𝓓((⊤ : TopologicalSpace.Opens (ℝ × ℝ)), ℂ)) :
    𝓓((⊤ : TopologicalSpace.Opens (ℝ × ℝ)), ℂ) :=
  (-(1 / Real.pi : ℝ) : ℝ) •
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ ((0 : ℝ), (1 : ℝ))) P

lemma deriv_slice_eq (P : 𝓓((⊤ : TopologicalSpace.Opens (ℝ × ℝ)), ℂ)) (s q : ℝ) :
    deriv (fun q' : ℝ => P (s, q')) q = lineDeriv ℝ P (s, q) ((0 : ℝ), (1 : ℝ)) := by
  have hd : DifferentiableAt ℝ P (s, q) := (P.contDiff.differentiable (by simp)) _
  have h1 : HasDerivAt (fun q' : ℝ => (s, q')) ((0 : ℝ), (1 : ℝ)) q :=
    (hasDerivAt_const q s).prodMk (hasDerivAt_id q)
  have h2 := hd.hasFDerivAt.comp_hasDerivAt q h1
  exact h2.deriv.trans hd.lineDeriv_eq_fderiv.symm

lemma liftProfile_apply (P : 𝓓((⊤ : TopologicalSpace.Opens (ℝ × ℝ)), ℂ)) (s q : ℝ) :
    liftProfile P (s, q) = (-(1 / Real.pi : ℝ) : ℝ) • deriv (fun q' : ℝ => P (s, q')) q := by
  change (-(1 / Real.pi : ℝ) : ℝ) • (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ
      ((0 : ℝ), (1 : ℝ)) P) (s, q) = _
  rw [TestFunction.lineDerivCLM_apply]
  simp [deriv_slice_eq]

section Marginal

variable (E E' : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
  [FiniteDimensional ℝ E']

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The lifted radial source integrates to the original one.** The integral over the plane of the
lift `-(1/π) ∂_q P` is `P`. -/
lemma radialSource_marginal (A : WithLp 2 (E × EuclideanSpace ℝ (Fin 2)) ≃ₗᵢ[ℝ] E')
    (P : 𝓓((⊤ : TopologicalSpace.Opens (ℝ × ℝ)), ℂ)) (s : ℝ) (x : E) :
    radialSource E P (s, x) = ∫ y : EuclideanSpace ℝ (Fin 2),
      radialSource E' (liftProfile P) (s, A (WithLp.toLp 2 (x, y))) := by
  have hg : ContDiff ℝ ∞ (fun q : ℝ => P (s, q)) :=
    P.contDiff.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (fun q : ℝ => P (s, q)) :=
    TimeSlice.hasCompactSupport_slice ℂ P s
  have h := integral_plane_lift hg hc (norm_nonneg x)
  rw [radialSource_apply, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show _ = radialSource E' (liftProfile P) (s, A (WithLp.toLp 2 (x, y)))
  rw [radialSource_apply, liftProfile_apply, LinearIsometryEquiv.norm_map,
    WithLp.prod_norm_sq_eq_of_L2]
  simp

end Marginal

open TimeSlice in
/-- **Dimension raising for a smooth radial source.** The retarded solution in `d + 2` space
dimensions of the lift `-(1/π) ∂_q P` of the radial source `P(s, ‖x‖²)` is `-(1 / (2π ρ)) ∂ρ` of the
retarded solution in `d` space dimensions of `P(s, ‖x‖²)`. -/
lemma hasDerivAt_solution_radialSource {μ : ℝ} (hμ : 0 ≤ μ) (d : ℕ)
    (P : 𝓓((⊤ : TopologicalSpace.Opens (ℝ × ℝ)), ℂ)) {e : Space d} (he : ‖e‖ = 1) (t : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (fun τ : ℝ => solution ℂ (radialSource (Space d) P) μ t (τ • e))
      (-(2 * Real.pi * ρ : ℝ) • solution ℂ (radialSource (Space (d + 2)) (liftProfile P)) μ t
        ((spaceSplit d).symm (WithLp.toLp 2 (ρ • e, 0)))) ρ :=
  hasDerivAt_solution_radial_space hμ d _ _
    (fun s z z' hzz => by
      change liftProfile P (s, ‖z‖ ^ 2) = liftProfile P (s, ‖z'‖ ^ 2)
      have h : ‖z‖ = ‖z'‖ := hzz
      rw [h])
    (fun s x => radialSource_marginal (Space d) (Space (d + 2)) (spaceSplit d).symm P s x) he t hρ

lemma transportSource_spaceThree (Q : 𝓓((⊤ : TopologicalSpace.Opens (ℝ × ℝ)), ℂ)) :
    transportSource spaceThree (radialSource Eucl3 Q) = radialSource (Space 3) Q := by
  ext ⟨s, x⟩
  change radialSource Eucl3 Q (s, spaceThree x) = radialSource (Space 3) Q (s, x)
  rw [radialSource_apply, radialSource_apply, LinearIsometryEquiv.norm_map]

end KleinGordon
