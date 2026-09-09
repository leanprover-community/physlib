/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.ScalarMeasure
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.SetToL1

/-!

# The bounded weak-operator spectral integral

Builds `boundedIntegral μS f hf hbdd : H →WOT[ℂ] H`, the operator `∫ f dμS` for a bounded
measurable `f : α → ℂ`, in three stages:

1. `simpleIntegral` : the finite-sum integral of a `SimpleFunc α ℂ`,
   `∑ z ∈ f.range, z • μS (f⁻¹{z})`.
2. `boundedIntegralOfUniformApprox` : given an explicit sequence of simple functions
   converging
   *uniformly* to `f`, the norm-limit (in the underlying `H →L[ℂ] H`, then viewed weakly) of their
   simple integrals. `simpleIntegral_norm_le` gives the uniform Cauchy estimate that makes this
   limit exist.
3. `boundedIntegral` : specializing to the canonical uniform approximation supplied by
   `SimpleFunc.approxOn` on a bounded range (`exists_uniform_simple_approx`), so no approximating
   sequence needs to be supplied by hand.

This is the weak-operator-topology analogue of ordinary integration against a scalar measure
generalized to an operator-valued one; a weak PVM need not have finite variation in operator
norm, so working in the WOT type (rather than trying to make sense of a norm-limit integral
directly) is what makes this integral tractable at all. The characteristic-function case,
`simpleIntegral_piecewise_indicator`, is the bridge back from this integral to `μS` itself:
`∫ 𝟙_S dμS = μS S`.

## Main definitions

- `simpleIntegral`, `simpleIntegral_norm_sq_eq_lintegral` : the finite-sum integral, and its
  norm-square identity against `diagonalMeasure`.
- `boundedIntegral` : the canonical bounded operator integral of a bounded measurable `f`.

-/

@[expose] public section

noncomputable section

open scoped Topology InnerProductSpace Function
open ContinuousLinearMap ContinuousLinearMapWOT MeasureTheory Set

namespace QuantumMechanics

namespace WOTSpectralMeasure

variable {α : Type*} [MeasurableSpace α]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μS : WOTSpectralMeasure α H)

/-! ## A. The simple-function integral

The operator integral of a measurable simple multiplier. This is the finite-sum stage of the
bounded spectral calculus. It is defined in the weak-operator representation because a weak PVM
need not have finite variation in operator norm. -/

/-- The weak-operator integral of a complex-valued simple function. -/
noncomputable def simpleIntegral (f : SimpleFunc α ℂ) : H →WOT[ℂ] H :=
  ∑ z ∈ f.range, z • μS (f ⁻¹' {z})

lemma simpleIntegral_inner (f : SimpleFunc α ℂ) (x y : H) :
    ⟪y, simpleIntegral μS f x⟫_ℂ =
      ∑ z ∈ f.range, z * μS.scalarMeasure x y (f ⁻¹' {z}) := by
  change (innerEvaluation (H := H) x y)
      (∑ z ∈ f.range, z • μS (f ⁻¹' {z})) = _
  rw [map_sum]
  simp [innerEvaluation, ContinuousLinearMapWOT.smul_apply, inner_smul_right,
    scalarMeasure_apply]

lemma simpleIntegral_norm_sq (f : SimpleFunc α ℂ) (x : H) :
    ENNReal.ofReal (‖simpleIntegral μS f x‖ ^ 2) =
      ∑ z ∈ f.range, ENNReal.ofReal (‖z‖ ^ 2) *
        (μS.diagonalMeasure x) (f ⁻¹' {z}) := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rw [simpleIntegral]
  change ENNReal.ofReal (⟪(∑ z ∈ f.range, z • (μS (f ⁻¹' {z}))) x,
      (∑ z ∈ f.range, z • (μS (f ⁻¹' {z}))) x⟫_ℂ).re = _
  have hsum : ∀ (s : Finset ℂ),
      (∑ z ∈ s, z • (μS (f ⁻¹' {z}))) x =
        ∑ z ∈ s, z • (μS (f ⁻¹' {z})) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert z s hz ih =>
      simp only [Finset.sum_insert hz]
      rw [ContinuousLinearMapWOT.add_apply, ih]
      simp [ContinuousLinearMapWOT.smul_apply]
  rw [hsum]
  simp only [sum_inner, inner_sum]
  simp only [inner_smul_left, inner_smul_right]
  have hRHS :
      (∑ z ∈ f.range, ENNReal.ofReal (‖z‖ ^ 2) *
          (μS.diagonalMeasure x) (f ⁻¹' {z})) =
        ENNReal.ofReal (∑ z ∈ f.range,
          ‖z‖ ^ 2 * (⟪x, μS (f ⁻¹' {z}) x⟫_ℂ).re) := by
    simp_rw [μS.diagonalMeasure_apply x _ (f.measurableSet_fiber _)]
    simp_rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    intro z hz
    exact mul_nonneg (sq_nonneg _) (μS.re_inner_nonneg _ x)
  rw [hRHS]
  have hReSum : ∀ (s : Finset ℂ) (g : ℂ → ℂ),
      (∑ z ∈ s, g z).re = ∑ z ∈ s, (g z).re := by
    intro s g
    induction s using Finset.induction_on with
    | empty => simp
    | @insert z s hz ih =>
      simp only [Finset.sum_insert hz, Complex.add_re, ih]
  rw [hReSum]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.sum_eq_single z]
  · rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    rw [μS.inner_eq_inner_projection]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    norm_num [pow_two, Complex.mul_re, Complex.mul_im, RCLike.conj_re, RCLike.conj_im,
      RCLike.ofReal_re, RCLike.ofReal_im]
    have hzNorm : ‖z‖ * ‖z‖ = z.re * z.re + z.im * z.im := by
      rw [← pow_two, Complex.sq_norm, Complex.normSq_apply]
    rw [hzNorm]
    ring
  · intro w hw hwz
    have hdisj : Disjoint (f ⁻¹' ({z} : Set ℂ)) (f ⁻¹' ({w} : Set ℂ)) := by
      refine Set.disjoint_left.2 ?_
      intro a ha hb
      have haz : f a = z := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using ha
      have haw : f a = w := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hb
      exact hwz (haw.symm.trans haz)
    rw [inner_eq_zero_of_disjoint μS hdisj.symm (f.measurableSet_fiber _)
      (f.measurableSet_fiber _) x]
    simp
  · intro hznot
    exact (hznot hz).elim

lemma simpleIntegral_norm_sq_eq_lintegral (f : SimpleFunc α ℂ) (x : H) :
    ENNReal.ofReal (‖simpleIntegral μS f x‖ ^ 2) =
      ∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂μS.diagonalMeasure x := by
  rw [μS.simpleIntegral_norm_sq]
  have hfun : (fun z : α => ENNReal.ofReal (‖f z‖ ^ 2)) =
      (fun z : α => (f.map (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2))) z) := by
    funext z
    rfl
  rw [hfun]
  rw [(f.map (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2))).lintegral_eq_lintegral]
  rw [SimpleFunc.map_lintegral]

lemma simpleIntegral_norm_sq_le (f : SimpleFunc α ℂ) (x : H) {C : ℝ}
    (hC : ∀ z ∈ f.range, ‖z‖ ^ 2 ≤ C ^ 2) :
    ENNReal.ofReal (‖simpleIntegral μS f x‖ ^ 2) ≤
      ENNReal.ofReal (C ^ 2 * ‖x‖ ^ 2) := by
  rw [μS.simpleIntegral_norm_sq]
  calc
    (∑ z ∈ f.range, ENNReal.ofReal (‖z‖ ^ 2) *
        (μS.diagonalMeasure x) (f ⁻¹' {z})) ≤
        ∑ z ∈ f.range, ENNReal.ofReal (C ^ 2) *
          (μS.diagonalMeasure x) (f ⁻¹' {z}) := by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hC z hz)) _
    _ = ENNReal.ofReal (C ^ 2) *
          ∑ z ∈ f.range, (μS.diagonalMeasure x) (f ⁻¹' {z}) := by
      rw [Finset.mul_sum]
    _ = ENNReal.ofReal (C ^ 2) * (μS.diagonalMeasure x) Set.univ := by
      rw [← f.sum_range_measure_preimage_singleton]
    _ = ENNReal.ofReal (C ^ 2 * ‖x‖ ^ 2) := by
      rw [μS.diagonalMeasure_univ, ← ENNReal.ofReal_mul (sq_nonneg C)]

lemma simpleIntegral_norm_le (f : SimpleFunc α ℂ) (x : H) {C : ℝ}
    (hC : 0 ≤ C) (hCf : ∀ z ∈ f.range, ‖z‖ ≤ C) :
    ‖simpleIntegral μS f x‖ ≤ C * ‖x‖ := by
  have hsq : ∀ z ∈ f.range, ‖z‖ ^ 2 ≤ C ^ 2 := by
    intro z hz
    exact (sq_le_sq₀ (norm_nonneg z) hC).mpr (hCf z hz)
  have hENN := μS.simpleIntegral_norm_sq_le f x hsq
  have hreal : ‖simpleIntegral μS f x‖ ^ 2 ≤ C ^ 2 * ‖x‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg C) (sq_nonneg ‖x‖))).mp hENN
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  calc
    ‖simpleIntegral μS f x‖ ^ 2 ≤ C ^ 2 * ‖x‖ ^ 2 := hreal
    _ = (C * ‖x‖) ^ 2 := by ring

lemma simpleIntegral_const [Nonempty α] (c : ℂ) :
    simpleIntegral μS (SimpleFunc.const α c) = c • (1 : H →WOT[ℂ] H) := by
  apply ContinuousLinearMapWOT.ext_inner
  intro x y
  rw [simpleIntegral_inner]
  have hpre : (Function.const α c) ⁻¹' ({c} : Set ℂ) = Set.univ :=
    Set.preimage_const_of_mem (by simp)
  rw [SimpleFunc.range_const, Finset.sum_singleton, SimpleFunc.coe_const, hpre,
    scalarMeasure_apply, μS.univ]
  simp [ContinuousLinearMapWOT.one_apply, ContinuousLinearMapWOT.smul_apply,
    inner_smul_right]

/-! ## B. Uniform approximation and the limiting integral

The WOT type is a topological copy of the bounded-operator space; its underlying normed operator
is still available through `toCLM`. The finite estimate above therefore gives a norm completion
for any explicitly supplied uniformly convergent simple approximation. Keeping the approximation
sequence as an argument makes the analytic hypotheses visible at this low level.
-/

/-- The real-linear map `z ↦ z • μS(S)`, as a bounded operator, for each `z : ℂ`. -/
def spectralCLM (S : Set α) : ℂ →L[ℝ] (H →L[ℂ] H) :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight (ContinuousLinearMapWOT.toCLM (μS S))).restrictScalars ℝ

lemma spectralCLM_apply (S : Set α) (z : ℂ) :
    spectralCLM μS S z = z • ContinuousLinearMapWOT.toCLM (μS S) := by
  rfl

private lemma spectralCLM_finMeasAdditive (μ : Measure α) :
    FinMeasAdditive μ (spectralCLM μS) := by
  intro S U hS hU hμS hμU hdisj
  ext z x
  change z • (μS (S ∪ U) x) = z • (μS S x) + z • (μS U x)
  rw [μS.of_union hdisj hS hU]
  simp [smul_add]

private lemma simpleFunc_integrable_dirac (f : SimpleFunc α ℂ) [Nonempty α] :
    Integrable f (Measure.dirac (Classical.choice (inferInstance : Nonempty α))) := by
  obtain ⟨C, hC⟩ := (f.map norm).exists_forall_le
  apply Integrable.of_bound f.measurable.aestronglyMeasurable C
  filter_upwards [] with x
  exact hC x

@[nolint unusedArguments]
lemma simpleIntegral_eq_setToSimpleFunc (f : SimpleFunc α ℂ) (_μ : Measure α) :
    ContinuousLinearMapWOT.toCLM (simpleIntegral μS f) = f.setToSimpleFunc (spectralCLM μS) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [SimpleFunc.setToSimpleFunc, spectralCLM_apply]
  have hsum : ∀ (s : Finset ℂ),
      (∑ z ∈ s, z • μS (f ⁻¹' {z})) x =
        ∑ z ∈ s, z • (μS (f ⁻¹' {z}) x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert z s hz ih =>
      simp only [Finset.sum_insert hz]
      rw [ContinuousLinearMapWOT.add_apply, ih]
      simp [ContinuousLinearMapWOT.smul_apply]
  change (∑ z ∈ f.range, z • μS (f ⁻¹' {z})) x =
    (∑ z ∈ f.range, z • ContinuousLinearMapWOT.toCLM (μS (f ⁻¹' {z}))) x
  rw [hsum]
  simp

/-! The characteristic-function case is the bridge from bounded integration back to the PVM. -/

lemma simpleIntegral_piecewise_indicator {S : Set α} (hS : MeasurableSet S) :
    simpleIntegral μS
        (SimpleFunc.piecewise S hS (SimpleFunc.const α (1 : ℂ))
          (SimpleFunc.const α (0 : ℂ))) = μS S := by
  apply ContinuousLinearMapWOT.toCLM_injective
  rw [simpleIntegral_eq_setToSimpleFunc μS _ (0 : Measure α)]
  have hempty : spectralCLM μS ∅ = 0 := by
    ext z
    simp [spectralCLM, μS.empty]
  rw [SimpleFunc.setToSimpleFunc_indicator (spectralCLM μS) hempty]
  simp [spectralCLM_apply]

lemma simpleIntegral_add [Nonempty α] (f g : SimpleFunc α ℂ) :
    simpleIntegral μS (f + g) = simpleIntegral μS f + simpleIntegral μS g := by
  apply ContinuousLinearMapWOT.toCLM_injective
  let μ : Measure α := Measure.dirac (Classical.choice (inferInstance : Nonempty α))
  rw [ContinuousLinearMapWOT.toCLM_add]
  rw [simpleIntegral_eq_setToSimpleFunc μS (f + g) μ,
    simpleIntegral_eq_setToSimpleFunc μS f μ,
    simpleIntegral_eq_setToSimpleFunc μS g μ]
  exact SimpleFunc.setToSimpleFunc_add (spectralCLM μS) (spectralCLM_finMeasAdditive μS μ)
    (simpleFunc_integrable_dirac f) (simpleFunc_integrable_dirac g)

lemma simpleIntegral_neg [Nonempty α] (f : SimpleFunc α ℂ) :
    simpleIntegral μS (-f) = -simpleIntegral μS f := by
  apply ContinuousLinearMapWOT.toCLM_injective
  let μ : Measure α := Measure.dirac (Classical.choice (inferInstance : Nonempty α))
  rw [ContinuousLinearMapWOT.toCLM_neg]
  rw [simpleIntegral_eq_setToSimpleFunc μS (-f) μ,
    simpleIntegral_eq_setToSimpleFunc μS f μ]
  exact SimpleFunc.setToSimpleFunc_neg (spectralCLM μS) (spectralCLM_finMeasAdditive μS μ)
    (simpleFunc_integrable_dirac f)

lemma simpleIntegral_sub [Nonempty α] (f g : SimpleFunc α ℂ) :
    simpleIntegral μS (f - g) = simpleIntegral μS f - simpleIntegral μS g := by
  rw [sub_eq_add_neg, simpleIntegral_add, simpleIntegral_neg, sub_eq_add_neg]

lemma simpleIntegral_mul [Nonempty α] (f g : SimpleFunc α ℂ) :
    simpleIntegral μS (f * g) = simpleIntegral μS f * simpleIntegral μS g := by
  apply ContinuousLinearMapWOT.toCLM_injective
  let μ : Measure α := Measure.dirac (Classical.choice (inferInstance : Nonempty α))
  let p : SimpleFunc α (ℂ × ℂ) := f.pair g
  have hf : Integrable f μ := simpleFunc_integrable_dirac f
  have hg : Integrable g μ := simpleFunc_integrable_dirac g
  have hp : Integrable p μ := SimpleFunc.integrable_pair hf hg
  have hadd := spectralCLM_finMeasAdditive μS μ
  have hfst : ContinuousLinearMapWOT.toCLM (simpleIntegral μS f) =
      ∑ q ∈ p.range, q.1 • ContinuousLinearMapWOT.toCLM (μS (p ⁻¹' {q})) := by
    rw [simpleIntegral_eq_setToSimpleFunc μS f μ, ← SimpleFunc.map_fst_pair f g]
    rw [SimpleFunc.map_setToSimpleFunc (spectralCLM μS) hadd hp Prod.fst_zero]
    simp only [spectralCLM_apply]
  have hsnd : ContinuousLinearMapWOT.toCLM (simpleIntegral μS g) =
      ∑ q ∈ p.range, q.2 • ContinuousLinearMapWOT.toCLM (μS (p ⁻¹' {q})) := by
    rw [simpleIntegral_eq_setToSimpleFunc μS g μ, ← SimpleFunc.map_snd_pair f g]
    rw [SimpleFunc.map_setToSimpleFunc (spectralCLM μS) hadd hp Prod.snd_zero]
    simp only [spectralCLM_apply]
  have hmul : ContinuousLinearMapWOT.toCLM (simpleIntegral μS (f * g)) =
      ∑ q ∈ p.range, (q.1 * q.2) • ContinuousLinearMapWOT.toCLM (μS (p ⁻¹' {q})) := by
    rw [simpleIntegral_eq_setToSimpleFunc μS (f * g) μ, SimpleFunc.mul_eq_map₂]
    rw [SimpleFunc.map_setToSimpleFunc (spectralCLM μS) hadd hp (by simp)]
    simp only [spectralCLM_apply]
  rw [ContinuousLinearMapWOT.toCLM_mul, hfst, hsnd, hmul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.sum_eq_single q]
  · rw [smul_mul_smul_comm, ← ContinuousLinearMapWOT.toCLM_mul, μS.comp_self]
  · intro r hr hneq
    rw [smul_mul_smul_comm, ← ContinuousLinearMapWOT.toCLM_mul]
    have hdisj : Disjoint (p ⁻¹' {q}) (p ⁻¹' {r}) := by
      refine Set.disjoint_left.2 ?_
      intro a haq har
      have haq' : p a = q := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using haq
      have har' : p a = r := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using har
      exact hneq (har'.symm.trans haq')
    rw [μS.comp_of_disjoint hdisj (p.measurableSet_fiber _)
      (p.measurableSet_fiber _), ContinuousLinearMapWOT.toCLM_zero, smul_zero]
  · intro hq'
    exact (hq' hq).elim

@[nolint unusedArguments]
lemma simpleIntegral_star [Nonempty α] (f : SimpleFunc α ℂ) :
    simpleIntegral μS (star f) = star (simpleIntegral μS f) := by
  classical
  simp only [simpleIntegral, star_sum]
  refine Finset.sum_bij (fun z hz => star z) ?_ ?_ ?_ ?_
  · intro z hz
    rcases SimpleFunc.mem_range.1 hz with ⟨x, hx⟩
    apply SimpleFunc.mem_range.2
    refine ⟨x, ?_⟩
    change f x = star z
    have hx' := congrArg star hx
    change star (star (f x)) = star z at hx'
    simpa using hx'
  · intro z₁ hz₁ z₂ hz₂ h
    exact star_injective h
  · intro z hz
    rcases SimpleFunc.mem_range.1 hz with ⟨x, hx⟩
    refine ⟨star z, ?_, ?_⟩
    · apply SimpleFunc.mem_range.2
      refine ⟨x, ?_⟩
      change star (f x) = star z
      exact congrArg star hx
    · simp
  · intro z hz
    have hfiber : (⇑(star f) : α → ℂ) ⁻¹' {z} =
        (⇑f : α → ℂ) ⁻¹' {star z} := by
      ext x
      change star (f x) = z ↔ f x = star z
      constructor
      · intro h
        simpa using congrArg star h
      · intro h
        exact congrArg star h |>.trans (star_star z)
    rw [hfiber, star_smul, star_star]
    simp only [(μS.isStarProjection _).isSelfAdjoint.star_eq]

lemma simpleIntegral_toCLM_norm_le (f : SimpleFunc α ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hCf : ∀ z ∈ f.range, ‖z‖ ≤ C) :
    ‖ContinuousLinearMapWOT.toCLM (simpleIntegral μS f)‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  exact μS.simpleIntegral_norm_le f x hC hCf

lemma simpleIntegral_toCLM_diff_norm_le [Nonempty α] (f g : SimpleFunc α ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hfg : ∀ x, ‖f x - g x‖ ≤ C) :
    ‖ContinuousLinearMapWOT.toCLM (simpleIntegral μS f) -
        ContinuousLinearMapWOT.toCLM (simpleIntegral μS g)‖ ≤ C := by
  rw [← ContinuousLinearMapWOT.toCLM_sub, ← μS.simpleIntegral_sub]
  apply μS.simpleIntegral_toCLM_norm_le (f - g) hC
  intro z hz
  rcases SimpleFunc.mem_range.1 hz with ⟨x, rfl⟩
  simpa only [SimpleFunc.sub_apply] using hfg x

lemma simpleIntegral_toCLM_cauchySeq [Nonempty α] {f : α → ℂ} {s : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε) :
    CauchySeq (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  rcases hs (ε / 4) (by linarith) with ⟨N, hN⟩
  refine ⟨N, fun m hm n hn => ?_⟩
  have hmn : ∀ x, ‖s m x - s n x‖ ≤ ε / 2 := by
    intro x
    apply le_of_lt
    calc
      ‖s m x - s n x‖ ≤ ‖s m x - f x‖ + ‖s n x - f x‖ := by
        calc
          ‖s m x - s n x‖ = ‖(s m x - f x) - (s n x - f x)‖ := by ring_nf
          _ ≤ ‖s m x - f x‖ + ‖s n x - f x‖ := norm_sub_le _ _
      _ < ε / 4 + ε / 4 := add_lt_add (hN m hm x) (hN n hn x)
      _ = ε / 2 := by ring
  have hbound := μS.simpleIntegral_toCLM_diff_norm_le (s m) (s n) (by linarith) hmn
  simpa only [dist_eq_norm] using lt_of_le_of_lt hbound (by linarith)

/-- The bounded operator integral obtained from an explicit uniformly convergent simple
approximation. The limit is taken in the normed space of bounded operators and then viewed in the
WOT copy. -/
@[nolint unusedArguments]
noncomputable def boundedIntegralOfUniformApprox [Nonempty α]
    (f : α → ℂ) (s : ℕ → SimpleFunc α ℂ)
    (_hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε) :
    H →WOT[ℂ] H :=
  ContinuousLinearMapWOT.ofCLM
    (Filter.atTop.limUnder
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))))

lemma boundedIntegralOfUniformApprox_eq_limUnder
    [Nonempty α]
    (f : α → ℂ) (s : ℕ → SimpleFunc α ℂ)
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε) :
    ContinuousLinearMapWOT.toCLM (boundedIntegralOfUniformApprox μS f s hs) =
      Filter.atTop.limUnder
        (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) := by
  rfl

lemma boundedIntegralOfUniformApprox_norm_le
    [Nonempty α]
    (f : α → ℂ) (s : ℕ → SimpleFunc α ℂ)
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε)
    {C : ℝ} (hC : ∀ n x, ‖s n x‖ ≤ C) :
    ‖ContinuousLinearMapWOT.toCLM (boundedIntegralOfUniformApprox μS f s hs)‖ ≤ C := by
  have hC0 : 0 ≤ C := by
    let a₀ : α := Classical.choice (inferInstance : Nonempty α)
    exact (norm_nonneg (s 0 a₀)).trans (hC 0 a₀)
  have hseq : ∀ n,
      ‖ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))‖ ≤ C := by
    intro n
    apply simpleIntegral_toCLM_norm_le μS (s n) hC0
    intro z hz
    rcases SimpleFunc.mem_range.1 hz with ⟨x, rfl⟩
    exact hC n x
  have hlim : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hs).tendsto_limUnder
  apply (isClosed_le continuous_norm continuous_const).mem_of_tendsto hlim
  exact Filter.Eventually.of_forall hseq

lemma boundedIntegralOfUniformApprox_eq_of_uniform_approx
    [Nonempty α]
    {f : α → ℂ} {s t : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε)
    (ht : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖t n x - f x‖ < ε)
    (hst : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - t n x‖ < ε) :
    boundedIntegralOfUniformApprox μS f s hs =
      boundedIntegralOfUniformApprox μS f t ht := by
  apply ContinuousLinearMapWOT.toCLM_injective
  let S : ℕ → H →L[ℂ] H := fun n =>
    ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))
  let U : ℕ → H →L[ℂ] H := fun n =>
    ContinuousLinearMapWOT.toCLM (simpleIntegral μS (t n))
  have hdist : Filter.Tendsto (fun n => dist (S n) (U n)) Filter.atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases hst (ε / 2) (by linarith) with ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    have hnorm : ‖S n - U n‖ < ε := by
      have h := simpleIntegral_toCLM_diff_norm_le μS (s n) (t n)
        (by positivity : (0 : ℝ) ≤ ε / 2) (fun x => le_of_lt (hN n hn x))
      have h' : ‖S n - U n‖ ≤ ε / 2 := by
        simpa only [S, U, ← ContinuousLinearMapWOT.toCLM_sub] using h
      exact h'.trans_lt (by linarith)
    have hdist' : dist (S n) (U n) < ε := by
      simpa only [dist_eq_norm] using hnorm
    change dist (dist (S n) (U n)) 0 < ε
    simpa only [dist_zero_right, Real.norm_of_nonneg (dist_nonneg)] using hdist'
  have hlimS : Filter.Tendsto (fun n => S n) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs))) := by
    change Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) Filter.atTop _
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hs).tendsto_limUnder
  have hlimU : Filter.Tendsto (fun n => U n) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f t ht))) := by
    change Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (t n))) Filter.atTop _
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS ht).tendsto_limUnder
  have hlimU' : Filter.Tendsto (fun n => U n) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs))) :=
    hlimS.congr_dist hdist
  have heq : ContinuousLinearMapWOT.toCLM
      (boundedIntegralOfUniformApprox μS f s hs) =
      ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f t ht) :=
    tendsto_nhds_unique hlimU' hlimU
  exact heq

lemma boundedIntegralOfUniformApprox_eq_of_same_target
    [Nonempty α]
    {f : α → ℂ} {s t : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε)
    (ht : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖t n x - f x‖ < ε) :
    boundedIntegralOfUniformApprox μS f s hs =
      boundedIntegralOfUniformApprox μS f t ht := by
  apply boundedIntegralOfUniformApprox_eq_of_uniform_approx μS hs ht
  intro ε hε
  rcases hs (ε / 2) (by linarith) with ⟨Ns, hNs⟩
  rcases ht (ε / 2) (by linarith) with ⟨Nt, hNt⟩
  refine ⟨max Ns Nt, fun n hn x => ?_⟩
  calc
    ‖s n x - t n x‖ ≤ ‖s n x - f x‖ + ‖t n x - f x‖ := by
      calc
        ‖s n x - t n x‖ = ‖(s n x - f x) - (t n x - f x)‖ := by ring_nf
        _ ≤ ‖s n x - f x‖ + ‖t n x - f x‖ := norm_sub_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add
      (hNs n (le_trans (le_max_left _ _) hn) x)
      (hNt n (le_trans (le_max_right _ _) hn) x)
    _ = ε := by ring

/-! ## C. The canonical integral -/

lemma exists_uniform_simple_approx [Nonempty α] {f : α → ℂ} (hf : Measurable f)
    (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    ∃ s : ℕ → SimpleFunc α ℂ,
      (∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε) ∧
      ∃ C, ∀ n x, ‖s n x‖ ≤ C := by
  rcases hbdd with ⟨C, hC⟩
  let a₀ : α := Classical.choice (inferInstance : Nonempty α)
  have hC0 : 0 ≤ C := (norm_nonneg (f a₀)).trans (hC a₀)
  let K : Set ℂ := Metric.closedBall 0 C
  have hKcompact : IsCompact K := isCompact_closedBall 0 C
  let _ : TopologicalSpace.SeparableSpace K := hKcompact.isSeparable.separableSpace
  have hK0 : (0 : ℂ) ∈ K := by simp [K, hC0]
  let _ : Nonempty K := ⟨⟨0, hK0⟩⟩
  let e : ℕ → ℂ := fun k => Nat.casesOn k 0 ((↑) ∘ TopologicalSpace.denseSeq K)
  let s : ℕ → SimpleFunc α ℂ := fun n => SimpleFunc.approxOn f hf K 0 hK0 n
  refine ⟨s, ?_, ⟨C, ?_⟩⟩
  · intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    have hcover : K ⊆ ⋃ k : ℕ, Metric.ball (e k) (ε / 2) := by
      intro y hy
      have hycl : (⟨y, hy⟩ : K) ∈ closure (Set.range (TopologicalSpace.denseSeq K)) := by
        rw [(denseRange_iff_closure_range.mp (TopologicalSpace.denseRange_denseSeq K))]
        exact mem_univ _
      have hy_mem : (⟨y, hy⟩ : K) ∈ Metric.ball (⟨y, hy⟩ : K) (ε / 2) :=
        Metric.mem_ball_self hε2
      rcases (mem_closure_iff.1 hycl) _ Metric.isOpen_ball hy_mem with ⟨z, hz, hzr⟩
      rcases hzr with ⟨k, rfl⟩
      refine mem_iUnion.2 ⟨k + 1, ?_⟩
      have hz' := Metric.mem_ball.mp hz
      rw [Subtype.dist_eq] at hz'
      simpa [e, Function.comp_def, dist_comm] using hz'
    rcases hKcompact.elim_finite_subcover (fun k : ℕ => Metric.ball (e k) (ε / 2))
        (fun _ => Metric.isOpen_ball) hcover with ⟨t, ht⟩
    have ht_ne : t.Nonempty := by
      by_contra ht'
      have ht_empty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht'
      subst ht_empty
      simpa using (ht (show (0 : ℂ) ∈ K from hK0))
    let N : ℕ := t.sup id
    refine ⟨N, ?_⟩
    intro n hn x
    have hfxK : f x ∈ K := by
      rw [Metric.mem_closedBall]
      simpa [dist_eq_norm] using hC x
    rcases Set.mem_iUnion₂.1 (ht hfxK) with ⟨k, hkt, hkx⟩
    have hkn : k ≤ n := (Finset.le_sup hkt).trans hn
    have hnearest : edist (SimpleFunc.nearestPt e n (f x)) (f x) ≤ edist (e k) (f x) :=
      SimpleFunc.edist_nearestPt_le e (f x) hkn
    have hkx' : dist (e k) (f x) < ε / 2 := by
      simpa [dist_comm] using Metric.mem_ball.mp hkx
    have hdist : dist (s n x) (f x) < ε := by
      have hnearest' : edist (s n x) (f x) ≤ edist (e k) (f x) := by
        simpa [s, SimpleFunc.approxOn, e] using hnearest
      have hkxed : edist (e k) (f x) < ENNReal.ofReal ε := by
        rw [edist_dist]
        exact (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith [hkx'])
      have hlt : edist (s n x) (f x) < ENNReal.ofReal ε := hnearest'.trans_lt hkxed
      rw [edist_dist] at hlt
      exact ENNReal.ofReal_lt_ofReal_iff hε |>.mp hlt
    simpa only [dist_eq_norm] using hdist
  · intro n x
    have hx := SimpleFunc.approxOn_mem hf hK0 n x
    rw [Metric.mem_closedBall] at hx
    simpa [dist_eq_norm] using hx

/-- The weak-operator-topology integral of a bounded measurable `f : α → ℂ` against `μS`,
defined as the limit of simple-function integrals under uniform approximation. -/
noncomputable def boundedIntegral [Nonempty α] (f : α → ℂ) (hf : Measurable f)
    (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) : H →WOT[ℂ] H := by
  let s : ℕ → SimpleFunc α ℂ :=
    Classical.choose (exists_uniform_simple_approx hf hbdd)
  have hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε :=
    (Classical.choose_spec (exists_uniform_simple_approx hf hbdd)).1
  exact boundedIntegralOfUniformApprox μS f s hs

end WOTSpectralMeasure

end QuantumMechanics

end
