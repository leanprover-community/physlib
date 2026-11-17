/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.RetardedSolution

/-!

# Smoothness of the retarded solution

## i. Overview

The retarded solution is jointly smooth in time and space.

## ii. Key results

- `solutionIntegrand` : The integrand of the retarded solution in the variables `(r, ξ)`, at the
  point `p = (t, x)`.
- `solution_eq_integral_solutionIntegrand` : A fixed propagation interval represents the solution
  when its lower source time precedes the support.
- `contDiff_solution` : The retarded Klein–Gordon solution of a smooth compactly supported source is
  smooth on spacetime.
- `integrable_solutionIntegrand` : The Fourier integrand is integrable over a bounded propagation
  interval and all frequencies.

## iii. Table of contents

- A. Smoothness of the retarded solution

## iv. References

None.

## A. Smoothness of the retarded solution

- `solutionIntegrand` : The integrand of the retarded solution in the variables `(r, ξ)`, at the
  point `p = (t, x)`.

Lemmas: `contDiff_solutionIntegrand_joint`, `contDiff_solutionIntegrand_p`,
`norm_iteratedFDeriv_solutionIntegrand_le`, `exists_char_mul_timeDeriv_bound`,
`exists_solutionIntegrand_bound`, `integrable_solutionIntegrand`,
`solution_eq_integral_solutionIntegrand`, `contDiff_integral_solutionIntegrand`,
`contDiff_solution`, `contDiff_advancedSolution`.

-/

@[expose] public section

noncomputable section

open scoped FourierTransform Distributions ContDiff Real
open Duhamel FourierIntegral ParametricIntegral TimeSlice TopologicalSpace Topology MeasureTheory
universe u

namespace KleinGordon

section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type u) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (f : 𝓓((⊤ : Opens (ℝ × E)), F))

/-- The integrand of the retarded solution in the variables `(r, ξ)`, at the point `p = (t, x)`. -/
def solutionIntegrand (μ : ℝ) (p : ℝ × E) (z : ℝ × E) : F :=
  (𝐞 (inner ℝ z.2 p.2) : ℂ) • (multiplier z.1 μ z.2 • 𝓕 (slice F f (p.1 - z.1)) z.2)

lemma contDiff_solutionIntegrand_joint {μ : ℝ} (hμ : 0 ≤ μ) :
    ContDiff ℝ ∞ fun w : (ℝ × E) × (ℝ × E) => solutionIntegrand F f μ w.1 w.2 := by
  unfold solutionIntegrand
  have hm : ContDiff ℝ ∞ fun w : (ℝ × E) × (ℝ × E) => multiplier w.2.1 μ w.2.2 :=
    (contDiff_multiplier_joint hμ).comp contDiff_snd
  have hG : ContDiff ℝ ∞ fun w : (ℝ × E) × (ℝ × E) =>
      𝓕 (slice F f (w.1.1 - w.2.1)) w.2.2 :=
    (contDiff_fourier_slice_joint_infty F f).comp
      (((contDiff_fst.comp contDiff_fst).sub (contDiff_fst.comp contDiff_snd)).prodMk
        (contDiff_snd.comp contDiff_snd))
  exact (contDiff_char_pair).smul (hm.smul hG)

lemma contDiff_solutionIntegrand_p {μ : ℝ} (hμ : 0 ≤ μ) (z : ℝ × E) :
    ContDiff ℝ ∞ fun p : ℝ × E => solutionIntegrand F f μ p z :=
  (contDiff_solutionIntegrand_joint F f hμ).comp (contDiff_id.prodMk contDiff_const)

omit [CompleteSpace F] in
/-- The Leibniz bound separates the spatial character from the time derivatives of the source. -/
lemma norm_iteratedFDeriv_solutionIntegrand_le (μ : ℝ) (k : ℕ) (p z : ℝ × E) :
    ‖iteratedFDeriv ℝ k (fun q => solutionIntegrand F f μ q z) p‖ ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (2 * π * ‖z.2‖) ^ i *
        (|z.1| * ‖iteratedDeriv (k - i) (fun s => 𝓕 (slice F f s) z.2) (p.1 - z.1)‖) := by
  have hg : ContDiff ℝ ∞ (fun s => 𝓕 (slice F f s) z.2) :=
    contDiff_infty.2 (fun n => contDiff_fourier_slice F z.2 n f)
  have ht : ContDiff ℝ ∞ (fun q : ℝ × E => 𝓕 (slice F f (q.1 - z.1)) z.2) :=
    hg.comp (contDiff_fst.sub contDiff_const)
  have hc : ContDiff ℝ ∞ (fun q : ℝ × E => (𝐞 (inner ℝ z.2 q.2) : ℂ)) :=
    contDiff_fourierChar_real.comp (contDiff_const.inner ℝ contDiff_snd)
  refine (norm_iteratedFDeriv_smul_le hc (ht.const_smul (multiplier z.1 μ z.2)) p
    (by exact_mod_cast le_top : (k : ℕ∞ω) ≤ ∞)).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  have hm : ‖iteratedFDeriv ℝ (k - i)
      (fun q : ℝ × E => multiplier z.1 μ z.2 • 𝓕 (slice F f (q.1 - z.1)) z.2) p‖ ≤
      |z.1| * ‖iteratedDeriv (k - i) (fun s => 𝓕 (slice F f s) z.2) (p.1 - z.1)‖ := by
    rw [iteratedFDeriv_const_smul_apply' (ht.of_le (show ((k - i : ℕ) : ℕ∞ω) ≤ ∞ by
      simp)).contDiffAt,
      norm_smul]
    exact mul_le_mul (norm_multiplier_le _ _ _)
      (norm_iteratedFDeriv_timeShift_le _ hg z.1 (k - i) p) (norm_nonneg _) (abs_nonneg _)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_char_le z.2 i p) (Nat.cast_nonneg _)) hm
    (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) _))

omit [CompleteSpace F] in
/-- Each Leibniz term has arbitrarily rapid frequency decay, uniformly in time. -/
lemma exists_char_mul_timeDeriv_bound (i j N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ξ : E) (s : ℝ),
      (2 * π * ‖ξ‖) ^ i * ‖iteratedDeriv j (fun r => 𝓕 (slice F f r) ξ) s‖ ≤
        C * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
  obtain ⟨K, hK⟩ := exists_iteratedDeriv_fourier_slice_bound F f j (i + N)
  refine ⟨|K| * (2 * π) ^ i, by positivity, fun ξ s => ?_⟩
  calc
    _ ≤ (2 * π * ‖ξ‖) ^ i *
        (|K| * (1 + ‖ξ‖) ^ (-((i + N : ℕ) : ℝ))) := by
      gcongr
      exact (hK ξ s).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    _ = |K| * ((2 * π * ‖ξ‖) ^ i * (1 + ‖ξ‖) ^ (-((i + N : ℕ) : ℝ))) := by ring
    _ ≤ |K| * ((2 * π) ^ i * (1 + ‖ξ‖) ^ (-(N : ℝ))) :=
      mul_le_mul_of_nonneg_left (char_pow_mul_decay_le ξ i N) (abs_nonneg _)
    _ = _ := by ring

omit [CompleteSpace F] in
/-- All parameter derivatives have rapid frequency decay on bounded propagation intervals. -/
lemma exists_solutionIntegrand_bound (μ : ℝ) (k N : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p z : ℝ × E), |z.1| ≤ R →
      ‖iteratedFDeriv ℝ k (fun q => solutionIntegrand F f μ q z) p‖ ≤
        C * (1 + ‖z.2‖) ^ (-(N : ℝ)) := by
  choose C hCnonneg hC using fun i => exists_char_mul_timeDeriv_bound F f i (k - i) N
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * |R| * C i,
    Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (hCnonneg i)), fun p z hz => ?_⟩
  refine (norm_iteratedFDeriv_solutionIntegrand_le F f μ k p z).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ = (k.choose i : ℝ) * |z.1| * ((2 * π * ‖z.2‖) ^ i *
        ‖iteratedDeriv (k - i) (fun s => 𝓕 (slice F f s) z.2) (p.1 - z.1)‖) := by ring
    _ ≤ (k.choose i : ℝ) * |R| *
        (C i * (1 + ‖z.2‖) ^ (-(N : ℝ))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hz.trans (le_abs_self R)) (Nat.cast_nonneg _)
      · exact hC i z.2 (p.1 - z.1)
      · positivity
      · positivity
    _ = _ := by ring

/-- The Fourier integrand is integrable over a bounded propagation interval and all frequencies. -/
lemma integrable_solutionIntegrand {μ : ℝ} (hμ : 0 ≤ μ) (R : ℝ) (p : ℝ × E) :
    Integrable (solutionIntegrand F f μ p)
      ((volume.restrict (Set.Ioc 0 R)).prod volume) := by
  let N := Module.finrank ℝ E + 1
  obtain ⟨C, hC0, hC⟩ := exists_solutionIntegrand_bound F f μ 0 N |R|
  refine (((integrable_one_add_norm (E := E) (r := (N : ℝ)) (by simp [N])).const_mul C).comp_snd
    (volume.restrict (Set.Ioc 0 R))).mono' ?_ ?_
  · exact ((contDiff_solutionIntegrand_joint F f hμ).continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · have hz : ∀ᵐ z : ℝ × E ∂((volume.restrict (Set.Ioc 0 R)).prod volume),
        z.1 ∈ Set.Ioc 0 R :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hz] with z hz
    simpa using hC p z (by rw [abs_of_pos hz.1]; exact hz.2.trans (le_abs_self R))

/-- A fixed propagation interval represents the solution when its lower source time precedes
the support. -/
lemma solution_eq_integral_solutionIntegrand {μ : ℝ} (hμ : 0 ≤ μ) {R : ℝ} (hR : 0 ≤ R)
    {a : ℝ} (ha : ∀ s ≤ a, s ∉ Prod.fst '' tsupport f) (p : ℝ × E) (hp : p.1 - R ≤ a) :
    solution F f μ p.1 p.2 = ∫ z : ℝ × E, solutionIntegrand F f μ p z
      ∂((volume.restrict (Set.Ioc 0 R)).prod volume) := by
  rw [solution, duhamel_eq_intervalIntegral F f _
    (fun s hs => ha s (hs.trans hp)) (sub_le_self _ hR)]
  have he := intervalIntegral.integral_comp_sub_left
    (fun s => propagatedSlice F f (fun r ξ => multiplier r μ ξ) (p.1 - s) s p.2)
    (a := 0) (b := R) p.1
  simp only [sub_zero, sub_sub_cancel] at he
  rw [← he, intervalIntegral.integral_of_le hR]
  exact integral_integral (integrable_solutionIntegrand F f hμ R p)

/-- Integrating over a fixed bounded propagation interval gives a smooth spacetime field. -/
lemma contDiff_integral_solutionIntegrand {μ : ℝ} (hμ : 0 ≤ μ) (R : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × E => ∫ z : ℝ × E, solutionIntegrand F f μ p z
      ∂((volume.restrict (Set.Ioc 0 R)).prod volume)) := by
  apply contDiff_infty.2
  intro n
  apply contDiffOn_univ.mp
  refine contDiffOn_integral _ isOpen_univ n F (solutionIntegrand F f μ)
    (fun z => (contDiff_solutionIntegrand_p F f hμ z).of_le (by simp))
    (fun k hk p => ?_) (fun k hk => ?_)
  · exact ((continuous_iteratedFDeriv_partial _ (contDiff_solutionIntegrand_joint F f hμ) k).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · let N := Module.finrank ℝ E + 1
    obtain ⟨C, hC0, hC⟩ := exists_solutionIntegrand_bound F f μ k N |R|
    refine ⟨fun z => C * (1 + ‖z.2‖) ^ (-(N : ℝ)), ?_, ?_⟩
    · exact ((integrable_one_add_norm (E := E) (r := (N : ℝ)) (by simp [N])).const_mul C).comp_snd _
    · have hz : ∀ᵐ z : ℝ × E ∂((volume.restrict (Set.Ioc 0 R)).prod volume),
          z.1 ∈ Set.Ioc 0 R :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
      filter_upwards [hz] with z hz p hp
      apply hC p z
      rw [abs_of_pos hz.1]
      exact hz.2.trans (le_abs_self R)

/-- The retarded Klein–Gordon solution of a smooth compactly supported source is smooth on
spacetime. -/
lemma contDiff_solution {μ : ℝ} (hμ : 0 ≤ μ) :
    ContDiff ℝ ∞ (fun p : ℝ × E => solution F f μ p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  obtain ⟨a, ha⟩ := exists_timeBound F f
  let R := |p.1 - a| + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hp : p.1 < a + R := by dsimp [R]; linarith [le_abs_self (p.1 - a)]
  have he : (fun q : ℝ × E => solution F f μ q.1 q.2) =ᶠ[𝓝 p]
      (fun q => ∫ z : ℝ × E, solutionIntegrand F f μ q z
        ∂((volume.restrict (Set.Ioc 0 R)).prod volume)) := by
    filter_upwards [continuous_fst.continuousAt.eventually (gt_mem_nhds hp)] with q hq
    exact solution_eq_integral_solutionIntegrand F f hμ hR ha q (by linarith)
  exact (contDiff_integral_solutionIntegrand F f hμ R).contDiffAt.congr_of_eventuallyEq he

/-- The advanced Klein–Gordon solution is smooth on spacetime. -/
lemma contDiff_advancedSolution {μ : ℝ} (hμ : 0 ≤ μ) :
    ContDiff ℝ ∞ (fun p : ℝ × E => advancedSolution F f μ p.1 p.2) :=
  (contDiff_solution F (reflect F f) hμ).comp (contDiff_fst.neg.prodMk contDiff_snd)
end

end KleinGordon
