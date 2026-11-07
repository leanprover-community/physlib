/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Calculus.IteratedFDerivBounds
public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.DistributionSources
public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.FreeEvolution
public import PhyslibAlpha.Mathematics.Distribution.TimeSlice
public import PhyslibAlpha.Mathematics.Distribution.SchwartzDensity
public import PhyslibAlpha.Mathematics.Fourier.SchwartzDecay
public import Mathlib.Analysis.Complex.OperatorNorm
public import Mathlib.Analysis.LocallyConvex.HahnBanach

/-!

# A Schwartz bound for the retarded kernel

The retarded kernel tested against a test function is bounded by a finite number of weighted
derivative bounds of the test function. The bound does not depend on the test function.

## i. Overview

The retarded kernel at the origin applied to `ψ` is the integral over the positive times of the
sine evolution of the slice `ψ(s, ·)` evaluated at the origin. The multiplier of the sine
evolution is bounded by the time. The `L¹` norm of the Fourier transform of the slice is bounded
by Schwartz seminorms of the slice. The seminorms of the slice are bounded by weighted derivative
bounds of `ψ`. The weight in the time makes the time integral converge.

## ii. Key results

- `norm_sineEvolution_zero_le` : the sine evolution at the origin is bounded by the time and the
  `L¹` norm of the Fourier transform.
- `weighted_seminorm_slice_le` : weighted bounds of `ψ` bound the seminorms of its slices.
- `exists_norm_integral_sineEvolution_le` : the bound of the time integral.
- `exists_abs_retardedPointSource_le` : the retarded kernel applied to a test function is bounded
  by weighted derivative bounds of the test function.
- `exists_tempered_extension` : the retarded kernel extends to a continuous linear functional on
  the Schwartz space of spacetime, so it is a tempered distribution.

## iii. Table of contents

- A. The sine evolution at the origin
- B. The slices
- C. The time integral
- D. The retarded kernel
- E. The tempered extension

## iv. References

None.

## A. The sine evolution at the origin

- `norm_sineEvolution_zero_le` : the sine evolution at the origin is bounded by the time and the
  `L¹` norm of the Fourier transform.

## B. The slices

- `weighted_seminorm_slice_le` : weighted bounds of `ψ` bound the seminorms of its slices.

## C. The time integral

- `exists_norm_integral_sineEvolution_le` : the bound of the time integral.

## D. The retarded kernel

- `exists_abs_retardedPointSource_le` : the bound for the retarded kernel.

## E. The tempered extension

- `exists_tempered_extension` : the retarded kernel is a tempered distribution.
- `temperedKernel` : the retarded kernel as a tempered distribution.
- `temperedKernel_unique` : the tempered extension is unique.
-/

@[expose] public section

noncomputable section

open scoped SchwartzMap FourierTransform ContDiff Distributions
open SchwartzMap MeasureTheory TestFunction TopologicalSpace Module

namespace KleinGordon

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]

section SineEvolution

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]

omit [BorelSpace E] [MeasurableSpace E] [FiniteDimensional ℝ E] in
/-- The sine evolution at the origin is bounded by the time and the `L¹` norm of the transform. -/
lemma norm_sineEvolution_zero_le [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (r : ℝ) {μ : ℝ} (hμ : 0 ≤ μ) (g : 𝓢(E, F)) :
    ‖sineEvolution F r μ g 0‖ ≤ |r| * ∫ ξ : E, ‖𝓕 g ξ‖ := by
  rw [sineEvolution_apply_eq F r hμ g 0, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((𝓕 g).integrable.norm.const_mul _)
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Circle.norm_smul, norm_smul]
  exact mul_le_mul_of_nonneg_right (norm_multiplier_le r μ ξ) (norm_nonneg _)

end SineEvolution

section Slices

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
/-- **Weighted bounds of `ψ` bound the seminorms of its slices.** If `(1 + ‖y‖)^N` times the
derivatives of `ψ` up to the order `N` are bounded by `M`, then the seminorm `(k, p)` of the slice
at the time `s` is at most `M / (1 + |s|)^3` for `k + 3 ≤ N` and `p ≤ N`. -/
lemma weighted_seminorm_slice_le (ψ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ × E)), F)) {N k p : ℕ}
    {M : ℝ} (hM : ∀ n ≤ N, ∀ y : ℝ × E, (1 + ‖y‖) ^ N * ‖iteratedFDeriv ℝ n ψ y‖ ≤ M)
    (hk : k + 3 ≤ N) (hp : p ≤ N) (s : ℝ) :
    SchwartzMap.seminorm ℂ k p (TimeSlice.slice F ψ s) ≤ M / (1 + |s|) ^ 3 := by
  have hM0 : 0 ≤ M := le_trans (by positivity) (hM 0 (Nat.zero_le _) 0)
  refine SchwartzMap.seminorm_le_bound ℂ k p _ (by positivity) fun x => ?_
  rw [le_div_iff₀ (by positivity)]
  have h1 : ‖iteratedFDeriv ℝ p (TimeSlice.slice F ψ s) x‖ ≤ ‖iteratedFDeriv ℝ p ψ (s, x)‖ :=
    TimeSlice.norm_iteratedFDeriv_slice_le F ψ p s x
  have hy1 : |s| ≤ ‖(s, x)‖ := by simp
  have hy2 : ‖x‖ ≤ ‖(s, x)‖ := norm_snd_le (s, x)
  have hy0 : 0 ≤ ‖(s, x)‖ := norm_nonneg _
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ p (TimeSlice.slice F ψ s) x‖ * (1 + |s|) ^ 3
      ≤ (1 + ‖(s, x)‖) ^ k * ‖iteratedFDeriv ℝ p ψ (s, x)‖ * (1 + ‖(s, x)‖) ^ 3 := by
        gcongr
        linarith
    _ = (1 + ‖(s, x)‖) ^ (k + 3) * ‖iteratedFDeriv ℝ p ψ (s, x)‖ := by ring
    _ ≤ (1 + ‖(s, x)‖) ^ N * ‖iteratedFDeriv ℝ p ψ (s, x)‖ := by
        gcongr
        linarith
    _ ≤ M := hM p hp (s, x)

end Slices

section TimeIntegral

/-- **The time integral is bounded.** There are an order `N` and a constant `C` such that weighted
bounds of the derivatives of `ψ` by `M` bound the damped time integral of the sine evolution of
the slices at the origin by `C * M`. The bound does not depend on the damping `ε ≥ 0`. -/
lemma exists_norm_integral_sineEvolution_le {μ : ℝ} (hμ : 0 ≤ μ) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (ψ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ × E)), ℂ)) (M ε : ℝ),
      0 ≤ ε → (∀ n ≤ N, ∀ y : ℝ × E, (1 + ‖y‖) ^ N * ‖iteratedFDeriv ℝ n ψ y‖ ≤ M) →
      ‖∫ s in Set.Ioi (0 : ℝ), (Real.exp (-(ε * s)) : ℂ) *
        sineEvolution ℂ s μ (TimeSlice.slice ℂ ψ s) 0‖ ≤ C * M := by
  obtain ⟨S, C₀, hC₀, hS⟩ := SchwartzMap.exists_integral_norm_fourier_le (E := E) ℂ
  refine ⟨(S.sup fun i => i.1 + i.2) + 3,
    C₀ * ∫ s : ℝ, (1 + ‖s‖) ^ (-(2 : ℝ)), mul_nonneg hC₀ (integral_nonneg fun s => by positivity),
    fun ψ M ε hε hM => ?_⟩
  have hM0 : 0 ≤ M := le_trans (by positivity) (hM 0 (Nat.zero_le _) 0)
  have hint : Integrable (fun s : ℝ => (1 + ‖s‖) ^ (-(2 : ℝ))) :=
    integrable_one_add_norm (by simp)
  have hpt : ∀ s ∈ Set.Ioi (0 : ℝ), ‖(Real.exp (-(ε * s)) : ℂ) *
      sineEvolution ℂ s μ (TimeSlice.slice ℂ ψ s) 0‖ ≤
      C₀ * M * (1 + ‖s‖) ^ (-(2 : ℝ)) := fun s hs => by
    have hs0 : 0 < s := hs
    have hexp : ‖(Real.exp (-(ε * s)) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (by nlinarith)
    rw [norm_mul]
    refine le_trans (mul_le_of_le_one_left (norm_nonneg _) hexp) ?_
    have hsup : (S.sup (schwartzSeminormFamily ℂ E ℂ)) (TimeSlice.slice ℂ ψ s) ≤
        M / (1 + |s|) ^ 3 := by
      refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
      have h1 : i.1 + i.2 ≤ S.sup fun i => i.1 + i.2 :=
        Finset.le_sup (f := fun i : ℕ × ℕ => i.1 + i.2) hi
      exact weighted_seminorm_slice_le ℂ ψ hM (by omega) (by omega) s
    have h2 := (norm_sineEvolution_zero_le ℂ s hμ (TimeSlice.slice ℂ ψ s)).trans
      (mul_le_mul_of_nonneg_left (hS _) (abs_nonneg s))
    have hp3 : 0 < (1 + |s|) ^ 3 := by positivity
    have h3 : |s| * (C₀ * (S.sup (schwartzSeminormFamily ℂ E ℂ)) (TimeSlice.slice ℂ ψ s)) ≤
        |s| * (C₀ * (M / (1 + |s|) ^ 3)) := by gcongr
    have h4 : |s| * (C₀ * (M / (1 + |s|) ^ 3)) ≤ C₀ * M * (1 + ‖s‖) ^ (-(2 : ℝ)) := by
      rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two]
      have ha : 0 < 1 + |s| := by positivity
      have hs1 : |s| / (1 + |s|) ^ 3 ≤ 1 / (1 + |s|) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [abs_nonneg s, sq_nonneg (1 + |s|)]
      calc |s| * (C₀ * (M / (1 + |s|) ^ 3)) = C₀ * M * (|s| / (1 + |s|) ^ 3) := by ring
        _ ≤ C₀ * M * (1 / (1 + |s|) ^ 2) := by gcongr
        _ = _ := by rw [one_div]
    exact h2.trans (h3.trans h4)
  calc ‖∫ s in Set.Ioi (0 : ℝ), (Real.exp (-(ε * s)) : ℂ) *
        sineEvolution ℂ s μ (TimeSlice.slice ℂ ψ s) 0‖
      ≤ ∫ s in Set.Ioi (0 : ℝ), C₀ * M * (1 + ‖s‖) ^ (-(2 : ℝ)) :=
        norm_integral_le_of_norm_le (hint.const_mul _).integrableOn
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hpt))
    _ ≤ ∫ s : ℝ, C₀ * M * (1 + ‖s‖) ^ (-(2 : ℝ)) :=
        setIntegral_le_integral (hint.const_mul _)
          (Filter.Eventually.of_forall fun s => by positivity)
    _ = _ := by rw [integral_const_mul]; ring

end TimeIntegral

section Kernel

open KleinGordon.Spacetime

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Transporting a complexified spacetime test function to time-space coordinates keeps the
weighted derivative bounds up to a constant. -/
lemma exists_weighted_bound_sourceEquiv (d N : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (φ : 𝓓((⊤ : TopologicalSpace.Opens (SpaceTime d)), ℝ)) (M : ℝ),
      (∀ n ≤ N, ∀ y : SpaceTime d, (1 + ‖y‖) ^ N * ‖iteratedFDeriv ℝ n φ y‖ ≤ M) →
      ∀ n ≤ N, ∀ y : ℝ × Space d, (1 + ‖y‖) ^ N *
        ‖iteratedFDeriv ℝ n (sourceEquiv ℂ (TestFunction.postcompCLM Complex.ofRealCLM φ)) y‖ ≤
          A * M := by
  set e : SpaceTime d ≃L[ℝ] ℝ × Space d := coordinates d with he
  set A₁ : ℝ := max ‖(e : SpaceTime d →L[ℝ] ℝ × Space d)‖ 1 with hA₁
  set B₁ : ℝ := max ‖(e.symm : ℝ × Space d →L[ℝ] SpaceTime d)‖ 1 with hB₁
  have hA1 : 1 ≤ A₁ := le_max_right _ _
  have hB1 : 1 ≤ B₁ := le_max_right _ _
  refine ⟨A₁ ^ N * B₁ ^ N, by positivity, fun φ M hM n hn y => ?_⟩
  set z : SpaceTime d := e.symm y with hz
  have hφc : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := Complex.ofRealCLM.contDiff.comp φ.contDiff
  have hfun : ⇑(sourceEquiv ℂ (TestFunction.postcompCLM Complex.ofRealCLM φ)) =
      (Complex.ofRealCLM ∘ φ) ∘ (e.symm : ℝ × Space d →L[ℝ] SpaceTime d) := rfl
  have h1 := IteratedFDerivBounds.norm_iteratedFDeriv_comp_clm_le
    (e.symm : ℝ × Space d →L[ℝ] SpaceTime d) hφc n y
  have h2 : ‖iteratedFDeriv ℝ n (Complex.ofRealCLM ∘ φ) z‖ ≤ ‖iteratedFDeriv ℝ n φ z‖ := by
    have := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left (f := φ) (x := z) (N := ∞)
      (φ.contDiff.contDiffAt) (by exact_mod_cast le_top) (n := n)
    rwa [Complex.ofRealCLM_norm, one_mul] at this
  have h3 : ‖y‖ ≤ A₁ * ‖z‖ := by
    have : y = e z := by simp [hz]
    have h6 : ‖e z‖ ≤ ‖(e : SpaceTime d →L[ℝ] ℝ × Space d)‖ * ‖z‖ :=
      ContinuousLinearMap.le_opNorm (e : SpaceTime d →L[ℝ] ℝ × Space d) z
    calc ‖y‖ = ‖e z‖ := by rw [← this]
      _ ≤ ‖(e : SpaceTime d →L[ℝ] ℝ × Space d)‖ * ‖z‖ := h6
      _ ≤ A₁ * ‖z‖ := by gcongr; exact le_max_left _ _
  have h4 : (1 + ‖y‖) ≤ A₁ * (1 + ‖z‖) := by nlinarith [norm_nonneg z]
  have h5 : ‖(e.symm : ℝ × Space d →L[ℝ] SpaceTime d)‖ ^ n ≤ B₁ ^ N :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) n).trans
      (pow_le_pow_right₀ hB1 hn)
  have hM' := hM n hn z
  calc (1 + ‖y‖) ^ N * ‖iteratedFDeriv ℝ n (⇑(sourceEquiv ℂ
          (TestFunction.postcompCLM Complex.ofRealCLM φ))) y‖
      ≤ (A₁ * (1 + ‖z‖)) ^ N * (‖iteratedFDeriv ℝ n φ z‖ * B₁ ^ N) := by
        rw [hfun]
        gcongr
        exact h1.trans (by gcongr; exact h2 |>.trans le_rfl)
    _ = A₁ ^ N * B₁ ^ N * ((1 + ‖z‖) ^ N * ‖iteratedFDeriv ℝ n φ z‖) := by
        rw [mul_pow]; ring
    _ ≤ A₁ ^ N * B₁ ^ N * M := by gcongr

/-- **The retarded kernel is bounded by Schwartz-type seminorms.** There are an order `N` and a
constant `C` such that weighted derivative bounds of a test function by `M` bound the retarded
kernel applied to it by `C * M`. -/
lemma exists_abs_retardedPointSource_le (d : ℕ) (m : ℝ) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (φ : 𝓓((⊤ : TopologicalSpace.Opens (SpaceTime d)), ℝ))
      (M : ℝ), (∀ n ≤ N, ∀ y : SpaceTime d, (1 + ‖y‖) ^ N * ‖iteratedFDeriv ℝ n φ y‖ ≤ M) →
      |retardedPointSource m (0 : SpaceTime d) φ| ≤ C * M := by
  obtain ⟨N, C₀, hC₀, hC⟩ := exists_norm_integral_sineEvolution_le (E := Space d)
    (sq_nonneg m)
  obtain ⟨A, hA0, hA⟩ := exists_weighted_bound_sourceEquiv d N
  refine ⟨N, C₀ * A, mul_nonneg hC₀ hA0, fun φ M hM => ?_⟩
  have h0 : coordinates d (0 : SpaceTime d) = (0, 0) := by rw [map_zero]; rfl
  rw [retardedPointSource_apply, h0]
  refine (Complex.abs_re_le_norm _).trans ?_
  have key : ∀ ψ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ × Space d)), ℂ),
      ‖∫ s in Set.Ioi ((0, 0) : ℝ × Space d).1,
        sineEvolutionTempered ℂ (s - ((0, 0) : ℝ × Space d).1) (m ^ 2)
          (TemperedDistribution.delta ((0, 0) : ℝ × Space d).2) (TimeSlice.slice ℂ ψ s)‖ =
      ‖∫ s in Set.Ioi (0 : ℝ), sineEvolution ℂ s (m ^ 2) (TimeSlice.slice ℂ ψ s) 0‖ := by
    intro ψ
    congr 1
    simp only [sub_zero]
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ =>
      (sineEvolution_apply_eq_delta (sq_nonneg m) s _ 0).symm
  rw [key]
  calc _ ≤ C₀ * (A * M) := by
        have := hC _ (A * M) 0 le_rfl fun n hn y => hA φ M hM n hn y
        simpa using this
    _ = C₀ * A * M := by ring

/-- **Weighted bounds from Schwartz seminorms.** There is a continuous seminorm `q` on Schwartz
space such that `q` of a test function bounds its weighted derivatives of order up to `N`. -/
lemma exists_seminorm_weighted_le (d N : ℕ) :
    ∃ q : Seminorm ℝ 𝓢(SpaceTime d, ℝ), Continuous q ∧
      ∀ φ : 𝓓((⊤ : TopologicalSpace.Opens (SpaceTime d)), ℝ), ∀ n ≤ N, ∀ y : SpaceTime d,
        (1 + ‖y‖) ^ N * ‖iteratedFDeriv ℝ n φ y‖ ≤ 2 ^ (N + 1) * q (ofTestFunction φ) := by
  let S : Finset (ℕ × ℕ) := (Finset.range (N + 1)).image (fun n => (0, n)) ∪
    (Finset.range (N + 1)).image (fun n => (N, n))
  let q : Seminorm ℝ 𝓢(SpaceTime d, ℝ) := ∑ i ∈ S, schwartzSeminormFamily ℝ (SpaceTime d) ℝ i
  have hqc : Continuous q := by
    have : (q : 𝓢(SpaceTime d, ℝ) → ℝ) = fun f => ∑ i ∈ S, schwartzSeminormFamily ℝ
        (SpaceTime d) ℝ i f := by
      funext f
      exact _root_.sum_apply _ _ f
    rw [this]
    exact continuous_finsetSum _ fun i _ =>
      (schwartz_withSeminorms ℝ (SpaceTime d) ℝ).continuous_seminorm i
  have hqφ : ∀ φ : 𝓓((⊤ : TopologicalSpace.Opens (SpaceTime d)), ℝ), ∀ n ≤ N,
      ∀ y : SpaceTime d, (1 + ‖y‖) ^ N * ‖iteratedFDeriv ℝ n φ y‖ ≤
        2 ^ (N + 1) * q (ofTestFunction φ) := by
    intro φ n hn y
    set F := ofTestFunction φ with hF
    have hnonneg : ∀ i ∈ S, 0 ≤ schwartzSeminormFamily ℝ (SpaceTime d) ℝ i F :=
      fun i _ => apply_nonneg _ _
    have hle : ∀ i ∈ S, schwartzSeminormFamily ℝ (SpaceTime d) ℝ i F ≤ q F := fun i hi => by
      change _ ≤ (∑ i ∈ S, schwartzSeminormFamily ℝ (SpaceTime d) ℝ i) F
      rw [_root_.sum_apply]
      exact Finset.single_le_sum (f := fun i => schwartzSeminormFamily ℝ (SpaceTime d) ℝ i F)
        hnonneg hi
    have h0 : SchwartzMap.seminorm ℝ 0 n F ≤ q F :=
      hle (0, n) (Finset.mem_union_left _ (Finset.mem_image.2 ⟨n, Finset.mem_range.2
        (Nat.lt_succ_of_le hn), rfl⟩))
    have h1 : SchwartzMap.seminorm ℝ N n F ≤ q F :=
      hle (N, n) (Finset.mem_union_right _ (Finset.mem_image.2 ⟨n, Finset.mem_range.2
        (Nat.lt_succ_of_le hn), rfl⟩))
    have e0 : ‖y‖ ^ 0 * ‖iteratedFDeriv ℝ n (⇑φ) y‖ ≤ SchwartzMap.seminorm ℝ 0 n F :=
      SchwartzMap.le_seminorm ℝ 0 n F y
    have e1 : ‖y‖ ^ N * ‖iteratedFDeriv ℝ n (⇑φ) y‖ ≤ SchwartzMap.seminorm ℝ N n F :=
      SchwartzMap.le_seminorm ℝ N n F y
    have hq0 : 0 ≤ q F := apply_nonneg _ _
    have h2 := add_pow_le (zero_le_one' ℝ) (norm_nonneg y) N
    have hD := norm_nonneg (iteratedFDeriv ℝ n (⇑φ) y)
    calc (1 + ‖y‖) ^ N * ‖iteratedFDeriv ℝ n (⇑φ) y‖
        ≤ (2 ^ (N - 1) * (1 ^ N + ‖y‖ ^ N)) * ‖iteratedFDeriv ℝ n (⇑φ) y‖ := by gcongr
      _ = 2 ^ (N - 1) * (‖y‖ ^ 0 * ‖iteratedFDeriv ℝ n (⇑φ) y‖ +
            ‖y‖ ^ N * ‖iteratedFDeriv ℝ n (⇑φ) y‖) := by ring
      _ ≤ 2 ^ (N - 1) * (q F + q F) := by gcongr <;> linarith
      _ ≤ 2 ^ (N + 1) * q F := by
          have : (2 : ℝ) ^ (N - 1) * 2 ≤ 2 ^ (N + 1) := by
            rcases Nat.eq_zero_or_pos N with h | h
            · subst h; norm_num
            · rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
          nlinarith
  exact ⟨q, hqc, hqφ⟩

/-- **The retarded kernel is a tempered distribution.** The retarded kernel extends to a
continuous linear functional on the Schwartz space of spacetime. -/
lemma exists_tempered_extension (d : ℕ) (m : ℝ) :
    ∃ T : 𝓢(SpaceTime d, ℝ) →L[ℝ] ℝ, ∀ φ : 𝓓((⊤ : TopologicalSpace.Opens (SpaceTime d)), ℝ),
      T (ofTestFunction φ) = retardedPointSource m (0 : SpaceTime d) φ := by
  obtain ⟨N, C, hC0, hC⟩ := exists_abs_retardedPointSource_le d m
  obtain ⟨q, hqc, hqφ⟩ := exists_seminorm_weighted_le d N
  let ℓ : 𝓓((⊤ : TopologicalSpace.Opens (SpaceTime d)), ℝ) →ₗ[ℝ] ℝ :=
    ⟨⟨fun φ => retardedPointSource m (0 : SpaceTime d) φ, map_add _⟩, map_smul _⟩
  let e := LinearEquiv.ofInjective (ofTestFunction (V := SpaceTime d)) (ofTestFunction_injective)
  let f : Module.Dual ℝ (LinearMap.range (ofTestFunction (V := SpaceTime d))) :=
    ℓ ∘ₗ e.symm.toLinearMap
  let C' : NNReal := ⟨2 ^ (N + 1) * C, by positivity⟩
  let p : Seminorm ℝ 𝓢(SpaceTime d, ℝ) := C' • q
  have hpc : Continuous p := by
    have : (p : 𝓢(SpaceTime d, ℝ) → ℝ) = fun x => (C' : ℝ) * q x := rfl
    rw [this]
    exact continuous_const.mul hqc
  have hf : ∀ φ, f ⟨ofTestFunction φ, LinearMap.mem_range_self _ φ⟩ =
      retardedPointSource m (0 : SpaceTime d) φ := fun φ => by
    change ℓ (e.symm _) = _
    have : e.symm ⟨ofTestFunction φ, LinearMap.mem_range_self _ φ⟩ = φ :=
      e.symm_apply_eq.2 rfl
    rw [this]
    rfl
  have hp : ∀ x : LinearMap.range (ofTestFunction (V := SpaceTime d)), f x ≤ p x := fun x => by
    obtain ⟨x, φ, rfl⟩ := x
    rw [show (⟨ofTestFunction φ, φ, rfl⟩ : LinearMap.range (ofTestFunction (V := SpaceTime d))) =
      ⟨ofTestFunction φ, LinearMap.mem_range_self _ φ⟩ from rfl, hf]
    refine (le_abs_self _).trans ((hC φ _ (hqφ φ)).trans ?_)
    change C * (2 ^ (N + 1) * q (ofTestFunction φ)) ≤ (C' : ℝ) * q (ofTestFunction φ)
    show _ ≤ (2 ^ (N + 1) * C) * _
    nlinarith
  have : PolynormableSpace ℝ 𝓢(SpaceTime d, ℝ) :=
    (schwartz_withSeminorms ℝ (SpaceTime d) ℝ).toPolynormableSpace
  obtain ⟨T, hT, -⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm_real
    (LinearMap.range (ofTestFunction (V := SpaceTime d))) f hpc hp
  exact ⟨T, fun φ => (hT ⟨ofTestFunction φ, LinearMap.mem_range_self _ φ⟩).trans (hf φ)⟩

/-- Two tempered distributions that agree on test functions are equal. -/
lemma tempered_ext (d : ℕ) {T T' : 𝓢(SpaceTime d, ℝ) →L[ℝ] ℝ}
    (h : ∀ φ : 𝓓((⊤ : TopologicalSpace.Opens (SpaceTime d)), ℝ),
      T (ofTestFunction φ) = T' (ofTestFunction φ)) : T = T' := by
  refine DFunLike.coe_injective ?_
  refine DenseRange.equalizer (denseRange_ofTestFunction (V := SpaceTime d))
    T.continuous T'.continuous (funext fun φ => ?_)
  exact h φ

/-- The retarded kernel as a tempered distribution on spacetime. -/
def temperedKernel (d : ℕ) (m : ℝ) : 𝓢(SpaceTime d, ℝ) →L[ℝ] ℝ :=
  Classical.choose (exists_tempered_extension d m)

lemma temperedKernel_apply (d : ℕ) (m : ℝ)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (SpaceTime d)), ℝ)) :
    temperedKernel d m (ofTestFunction φ) = retardedPointSource m (0 : SpaceTime d) φ :=
  Classical.choose_spec (exists_tempered_extension d m) φ

/-- **The tempered extension is unique.** -/
lemma temperedKernel_unique (d : ℕ) (m : ℝ) {T : 𝓢(SpaceTime d, ℝ) →L[ℝ] ℝ}
    (h : ∀ φ : 𝓓((⊤ : TopologicalSpace.Opens (SpaceTime d)), ℝ),
      T (ofTestFunction φ) = retardedPointSource m (0 : SpaceTime d) φ) :
    T = temperedKernel d m :=
  tempered_ext d fun φ => (h φ).trans (temperedKernel_apply d m φ).symm

end Kernel

end KleinGordon
