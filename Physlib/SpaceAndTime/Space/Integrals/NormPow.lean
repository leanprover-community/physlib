/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.SpaceAndTime.Space.IsDistBounded
/-!

# Integrability of norm powers on subsets of Space

## i. Overview

This module contains results on the integrability of `x ↦ ‖x‖ᵖ` for real exponents `p` on subsets of
`Space d`.

The integrability of `x ↦ ‖x‖ᵖ` on `ball 0 b` and `(ball 0 b)ᶜ` follows from the 1d results
`integrableOn_Ioo_rpow_iff` and `integrableOn_Ioi_rpow_iff` after changing to spherical coordinates.

## ii. Key results

- `integrableOn_norm_rpow_iff_of_isBounded_nhds`: Necessary and sufficient condition for
    integrability on a set `s` which is a bounded neighborhood of the origin.
- `integrableOn_norm_rpow_of_isBounded_compl_nhds`: Integrability for all bounded sets `s`
    with `0 ∉ closure s`.
- `integrableOn_norm_rpow_of_compl_nhds`: A sufficient condition for integrability on `s`
    with `0 ∉ closure s`.
- `radial_norm_power_spherical_integral_eq_space_integral`: The spherical-coordinate integral
    identity for integer powers of the norm against a Schwartz map.

## iii. Table of contents

## iv. References

* None.
-/

@[expose] public section

namespace Space

open MeasureTheory SchwartzMap

private lemma npow_indicator_rpow_eq {n : ℕ} {s : Set ℝ} (hs : 0 ∉ s) (p : ℝ) :
    (fun r ↦ r ^ n • s.indicator (fun r ↦ r ^ p) r) = s.indicator (fun r ↦ r ^ (n + p)) := by
  ext r
  by_cases hr : r ∈ s
  · grind [Set.indicator_of_mem, smul_eq_mul, add_comm, Real.rpow_add_natCast]
  · simp [hr]

lemma radial_jacobian_zpow_mul_self
    {d p : ℕ} [NeZero d] {q : ℤ} (hp_int : (p : ℤ) = q + (d : ℤ))
    {r : ℝ} (hr : 0 < r) :
    r ^ (d - 1) * (r ^ q * r) = r ^ p := by
  have hz : r ≠ 0 := ne_of_gt hr
  calc
    r ^ (d - 1) * (r ^ q * r)
        = r ^ (d - 1: ℤ) * (r ^ q * r ^ (1 : ℤ)) := by
            rw [← zpow_natCast, zpow_one, ← Nat.cast_pred (Nat.pos_of_neZero d)]
    _ = r ^ ((d - 1: ℤ) + (q + 1)) := by
            rw [← zpow_add₀ hz q 1, ← zpow_add₀ hz (d - 1: ℤ) (q + 1)]
    _ = r ^ (p : ℤ) := by
            congr 1; omega
    _ = r ^ p := by
            rw [zpow_natCast]

private lemma radial_jacobian_zpow
    {d p : ℕ} [NeZero d] {q : ℤ} (hp_int : (p : ℤ) = q + (d : ℤ))
    (hp_pos : 0 < p) {r : ℝ} (hr : 0 < r) :
    r ^ (d - 1) * r ^ q = r ^ (p - 1) := by
  have hz : r ≠ 0 := ne_of_gt hr
  calc
    r ^ (d - 1) * r ^ q
        = r ^ ((d - 1 : ℤ) + q) := by
            rw [← Nat.cast_pred (Nat.pos_of_neZero d), ← zpow_natCast, ← zpow_add₀ hz]
    _ = r ^ ((p - 1 : ℕ) : ℤ) := by
            congr 1; omega
    _ = r ^ (p - 1) := by
            rw [zpow_natCast]

lemma radial_norm_power_spherical_integral_eq_space_integral
    {d p : ℕ} [NeZero d] {q : ℤ} (hp_int : (p : ℤ) = q + (d : ℤ))
    (hp_pos : 0 < p) (η : 𝓢(Space d, ℝ)) :
    ∫ x : Space d, η x * ‖x‖ ^ q =
      ∫ (n : ↑(Metric.sphere (0 : Space d) 1)),
        ∫ (r : Set.Ioi (0 : ℝ)),
          r.1 ^ (p - 1) * η (r.1 • n.1)
          ∂(.comap Subtype.val volume)
        ∂(volume (α := Space d).toSphere) := by
  have hf : Integrable (fun x : Space d => η x * ‖x‖ ^ q) volume :=
    IsDistBounded.integrable_space_mul (IsDistBounded.pow q (by omega)) η
  rw [integral_volume_eq_spherical_integral
    (d := d) (fun x : Space d => η x * ‖x‖ ^ q) hf]
  congr
  funext n
  congr
  funext r
  have hr : 0 < (r : ℝ) := r.2
  have hnorm := norm_smul_sphere n (le_of_lt hr)
  simp only [smul_eq_mul]
  rw [hnorm, ← radial_jacobian_zpow hp_int hp_pos hr]
  ring

/-- The function `x ↦ ‖x‖ᵖ` is integrable on `{x : Space d | 0 ≤ ‖x‖ < b}` iff `0 < d + p`. -/
lemma integrableOn_norm_rpow_ball_iff {d : ℕ} [NeZero d] {b : ℝ} (hb : 0 < b) (p : ℝ) :
    IntegrableOn (fun x : Space d ↦ ‖x‖ ^ p) (Metric.ball 0 b) ↔ 0 < d + p := by
  let f : Space d → ENNReal := (Metric.ball 0 b).indicator (fun x ↦ ‖‖x‖ ^ p‖ₑ)
  let g : ℝ → ℝ := (Set.Ioo 0 b).indicator (fun r ↦ r ^ p)
  have hfg : f =ᵐ[volume] fun x ↦ ‖g ‖x‖‖ₑ := by
    apply ae_iff.mpr
    suffices {x | f x ≠ ‖g ‖x‖‖ₑ} = if p = 0 then {0} else ∅ by by_cases p = 0 <;> simp_all
    ext x
    by_cases ‖x‖ ∈ Set.Ioo 0 b
    · simp_all [f, g]
    · by_cases x = 0 <;> simp_all [f, g, Real.zero_rpow_eq_iff]
  trans Integrable (fun x : Space d ↦ g ‖x‖)
  · refine and_congr ?_ ?_
    · refine iff_of_true ?_ ?_
      repeat exact StronglyMeasurable.aestronglyMeasurable (by measurability)
    · rw [HasFiniteIntegral, ← lintegral_indicator measurableSet_ball, lintegral_congr_ae hfg]
      rfl
  trans IntegrableOn (fun r => r ^ (d - 1 + p)) (Set.Ioo 0 b)
  · have hInter : Set.Ioo 0 b ∩ Set.Ioi 0 = Set.Ioo 0 b := by ext; grind
    simp_rw [integrable_fun_norm_addHaar, g, Space.finrank_eq_dim,
      npow_indicator_rpow_eq (Set.left_notMem_Ioo),
      _root_.MeasureTheory.integrableOn_indicator_iff measurableSet_Ioo, hInter,
      Nat.cast_pred (Nat.pos_of_neZero d)]
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hb, neg_lt_iff_pos_add']
  ring_nf

/-- The function `x ↦ ‖x‖ᵖ` is integrable on `{x : Space d | 0 < a ≤ ‖x‖}` iff `d + p < 0`. -/
lemma integrableOn_norm_rpow_ball_compl_iff {d : ℕ} [NeZero d] {a : ℝ} (ha : 0 < a) (p : ℝ) :
    IntegrableOn (fun x : Space d ↦ ‖x‖ ^ p) (Metric.ball 0 a)ᶜ ↔ d + p < 0 := by
  let f : Space d → ENNReal := (Metric.ball 0 a)ᶜ.indicator (fun x ↦ ‖‖x‖ ^ p‖ₑ)
  let g : ℝ → ℝ := (Set.Ici a).indicator (fun r ↦ r ^ p)
  have hfg : f = fun x ↦ ‖g ‖x‖‖ₑ := by ext x; by_cases ‖x‖ ∈ Set.Ici a <;> simp_all [f, g]
  trans Integrable (fun x : Space d ↦ g ‖x‖)
  · refine and_congr ?_ ?_
    · refine iff_of_true ?_ ?_
      repeat exact StronglyMeasurable.aestronglyMeasurable (by measurability)
    · dsimp [HasFiniteIntegral]
      rw [← lintegral_indicator (by measurability), lintegral_congr_ae hfg.eventuallyEq]
  trans IntegrableOn (fun r => r ^ (d - 1 + p)) (Set.Ici a)
  · have hInter : Set.Ici a ∩ Set.Ioi 0 = Set.Ici a := by ext; grind
    simp_rw [integrable_fun_norm_addHaar, g, Space.finrank_eq_dim,
      npow_indicator_rpow_eq (Set.notMem_Ici.mpr ha),
      _root_.MeasureTheory.integrableOn_indicator_iff measurableSet_Ici, hInter,
      Nat.cast_pred (Nat.pos_of_neZero d)]
  rw [integrableOn_Ici_iff_integrableOn_Ioi, integrableOn_Ioi_rpow_iff ha, lt_neg_iff_add_neg]
  ring_nf

/-- The function `x ↦ ‖x‖ᵖ` is integrable on the shell `{x : Space d | 0 < a ≤ ‖x‖ ∧ ‖x‖ < b}`. -/
lemma integrableOn_norm_rpow_shell {d : ℕ} {a : ℝ} (ha : 0 < a) (b p : ℝ) :
    IntegrableOn (fun x : Space d ↦ ‖x‖ ^ p) ((Metric.ball 0 b) ∩ (Metric.ball 0 a)ᶜ) := by
  refine ⟨StronglyMeasurable.aestronglyMeasurable (by measurability), ?_⟩
  by_cases hab : a < b
  · refine setLIntegral_lt_top_of_le_nnreal ?_ ?_
    · exact measure_inter_ne_top_of_left_ne_top measure_ball_ne_top
    · use ‖max (a ^ p) (b ^ p)‖₊
      intro x hx
      simp only [Set.mem_inter_iff, Metric.mem_ball, dist_zero_right, Set.mem_compl_iff] at hx
      rw [enorm_le_coe]
      refine abs_le_abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) p) ?_
      rw [le_sup_iff]
      by_cases hp : 0 ≤ p
      · exact Or.inr <| Real.rpow_le_rpow (norm_nonneg x) (by linarith) hp
      · exact Or.inl <| Real.rpow_le_rpow_of_nonpos ha (by linarith) (by linarith)
  · suffices (Metric.ball 0 b) ∩ (Metric.ball 0 a)ᶜ = (∅ : Set (Space d)) by simp [this]
    ext x
    have : ‖x‖ < b → ‖x‖ < a := fun _ ↦ by linarith
    simpa

/-- The function `x ↦ ‖x‖ᵖ` is integrable on a bounded neighborhood of the origin
  iff `0 < d + p`. -/
lemma integrableOn_norm_rpow_iff_of_isBounded_nhds {d : ℕ} [NeZero d] {s : Set (Space d)}
    (hs : Bornology.IsBounded s) (hs' : s ∈ nhds 0) (p : ℝ) :
    IntegrableOn (fun x : Space d ↦ ‖x‖ ^ p) s ↔ 0 < d + p := by
  obtain ⟨a, ha, ha'⟩ := Metric.eventually_nhds_iff_ball.mp hs'
  obtain ⟨b, hb, hb'⟩ := Bornology.IsBounded.subset_ball_lt hs 0 0
  constructor <;> intro h
  · exact (integrableOn_norm_rpow_ball_iff ha p).mp (IntegrableOn.mono_set h ha')
  · exact IntegrableOn.mono_set ((integrableOn_norm_rpow_ball_iff hb p).mpr h) hb'

/-- The function `x ↦ ‖x‖ᵖ` is integrable on a bounded subset with the origin in its exterior. -/
lemma integrableOn_norm_rpow_of_isBounded_compl_nhds {d : ℕ} {s : Set (Space d)}
    (hs : Bornology.IsBounded s) (hs' : sᶜ ∈ nhds 0) (p : ℝ) :
    IntegrableOn (fun x : Space d ↦ ‖x‖ ^ p) s := by
  obtain ⟨a, ha, ha'⟩ := Metric.eventually_nhds_iff_ball.mp hs'
  obtain ⟨b, hb, hb'⟩ := Bornology.IsBounded.subset_ball_lt hs 0 0
  have hsc : s ⊆ (Metric.ball 0 a)ᶜ := Set.subset_compl_comm.mp ha'
  exact IntegrableOn.mono_set (integrableOn_norm_rpow_shell ha b p) (Set.subset_inter hb' hsc)

/-- The function `x ↦ ‖x‖ᵖ` is integrable on a subset with the origin in its exterior provided
  the decay at infinity is fast enough. -/
lemma integrableOn_norm_rpow_of_compl_nhds {d : ℕ} [NeZero d] {s : Set (Space d)}
    (hs : sᶜ ∈ nhds 0) {p : ℝ} (h : d + p < 0) : IntegrableOn (fun x : Space d ↦ ‖x‖ ^ p) s := by
  obtain ⟨a, ha, ha'⟩ := Metric.eventually_nhds_iff_ball.mp hs
  have hs' : s ⊆ (Metric.ball 0 a)ᶜ := Set.subset_compl_comm.mp ha'
  exact IntegrableOn.mono_set ((integrableOn_norm_rpow_ball_compl_iff ha p).mpr h) hs'

end Space
