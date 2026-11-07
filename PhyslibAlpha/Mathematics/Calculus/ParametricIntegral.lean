/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!

# Smoothness of parametric integrals

## i. Overview

An integral of a smooth family of functions is smooth when the derivatives have an integrable bound.

## ii. Key results

- `continuous_iteratedFDeriv_partial` : The derivatives in the first variable of a jointly smooth
  function are jointly continuous.
- `norm_iteratedFDeriv_integral_le` : Uniform integrable domination bounds every derivative of a
  parametric integral.
- `contDiffOn_integral`

## iii. Table of contents

- A. Smoothness of parametric integrals

## iv. References

None.

## A. Smoothness of parametric integrals

Lemmas: `contDiffOn_integral`, `norm_iteratedFDeriv_integral_le`,
`continuous_iteratedFDeriv_partial`.

-/

@[expose] public section

noncomputable section

open scoped ContDiff
open MeasureTheory
universe u

namespace ParametricIntegral

lemma contDiffOn_integral {P α : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [MeasurableSpace α]
    (μ : Measure α)
    {U : Set P} (hU : IsOpen U) (n : ℕ) :
    ∀ (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (H : P → α → F),
    (∀ a, ContDiff ℝ n fun p => H p a) →
    (∀ k ≤ n, ∀ p, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ k (fun q => H q a) p) μ) →
    (∀ k ≤ n, ∃ b : α → ℝ, Integrable b μ ∧
      ∀ᵐ a ∂μ, ∀ p ∈ U, ‖iteratedFDeriv ℝ k (fun q => H q a) p‖ ≤ b a) →
    ContDiffOn ℝ n (fun p => ∫ a, H p a ∂μ) U := by
  induction n with
  | zero =>
    intro F _ _ _ H hs hc hb
    have hmeas : ∀ p, AEStronglyMeasurable (H p) μ := by
      intro p
      have := (continuousMultilinearCurryFin0 ℝ P F).continuous.comp_aestronglyMeasurable
        (hc 0 le_rfl p)
      simpa [Function.comp_def, iteratedFDeriv_zero_eq_comp] using this
    obtain ⟨b, hbi, hbd⟩ := hb 0 le_rfl
    refine contDiffOn_zero.2 (continuousOn_of_dominated (bound := b) (fun p _ => hmeas p)
      (fun p hp => ?_) hbi (Filter.Eventually.of_forall fun a => ?_))
    · exact hbd.mono fun a ha => by simpa using ha p hp
    · exact (hs a).continuous.continuousOn
  | succ n ih =>
    intro F _ _ _ H hs hc hb
    have hmeas : ∀ p, AEStronglyMeasurable (H p) μ := by
      intro p
      have := (continuousMultilinearCurryFin0 ℝ P F).continuous.comp_aestronglyMeasurable
        (hc 0 (Nat.zero_le _) p)
      simpa [Function.comp_def, iteratedFDeriv_zero_eq_comp] using this
    have hc' : ∀ k ≤ n, ∀ p, AEStronglyMeasurable
        (fun a => iteratedFDeriv ℝ k (fun q => fderiv ℝ (fun r => H r a) q) p) μ := by
      intro k hk p
      have := (continuousMultilinearCurryRightEquiv' ℝ k P F).continuous.comp_aestronglyMeasurable
        (hc (k + 1) (by omega) p)
      simpa [Function.comp_def, iteratedFDeriv_succ_eq_comp_right] using this
    have hb' : ∀ k ≤ n, ∃ b : α → ℝ, Integrable b μ ∧ ∀ᵐ a ∂μ, ∀ p ∈ U,
        ‖iteratedFDeriv ℝ k (fun q => fderiv ℝ (fun r => H r a) q) p‖ ≤ b a := by
      intro k hk
      obtain ⟨b, hbi, hbd⟩ := hb (k + 1) (by omega)
      exact ⟨b, hbi, hbd.mono fun a ha p hp => by rw [norm_iteratedFDeriv_fderiv]; exact ha p hp⟩
    have hs' : ∀ a, ContDiff ℝ n fun p => fderiv ℝ (fun r => H r a) p := fun a =>
      ContDiff.fderiv_right (hs a) (m := (n : WithTop ℕ∞)) (by push_cast; exact le_rfl)
    have hcd := ih (P →L[ℝ] F) (fun p a => fderiv ℝ (fun q => H q a) p) hs' hc' hb'
    obtain ⟨b0, hb0i, hb0d⟩ := hb 0 (Nat.zero_le _)
    obtain ⟨b1, hb1i, hb1d⟩ := hb 1 (by omega)
    have hd : ∀ p ∈ U, HasFDerivAt (fun p => ∫ a, H p a ∂μ)
        (∫ a, fderiv ℝ (fun q => H q a) p ∂μ) p := by
      intro p hp
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := H)
        (F' := fun p a => fderiv ℝ (fun q => H q a) p) (bound := b1) (hU.mem_nhds hp)
        (Filter.Eventually.of_forall fun x => hmeas x)
        ?_ ?_ ?_ hb1i ?_
      · refine hb0i.mono' (hmeas p) (hb0d.mono fun a ha => ?_)
        simpa using ha p hp
      · have := (continuousMultilinearCurryFin0 ℝ P (P →L[ℝ]
        F)).continuous.comp_aestronglyMeasurable
          (hc' 0 (Nat.zero_le _) p)
        simpa [Function.comp_def, iteratedFDeriv_zero_eq_comp] using this
      · exact hb1d.mono fun a ha q hq => by simpa using ha q hq
      · exact Filter.Eventually.of_forall fun a q _ =>
          (((hs a).differentiable (by simp)) q).hasFDerivAt
    push_cast
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun p hp => (hd p hp).differentiableAt.differentiableWithinAt, fun h => ?_, ?_⟩
    · exact absurd h (by simp)
    · exact hcd.congr fun p hp => (hd p hp).fderiv

/-- Uniform integrable domination bounds every derivative of a parametric integral. -/
lemma norm_iteratedFDeriv_integral_le {P α : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [MeasurableSpace α] (μ : Measure α) (n : ℕ) :
    ∀ (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (H : P → α → F) (b : ℕ → α → ℝ),
    (∀ a, ContDiff ℝ ∞ (fun p => H p a)) →
    (∀ k p, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ k (fun q => H q a) p) μ) →
    (∀ k, Integrable (b k) μ) →
    (∀ k, ∀ᵐ a ∂μ, ∀ p, ‖iteratedFDeriv ℝ k (fun q => H q a) p‖ ≤ b k a) →
    ∀ p, ‖iteratedFDeriv ℝ n (fun q => ∫ a, H q a ∂μ) p‖ ≤ ∫ a, b n a ∂μ := by
  induction n with
  | zero =>
    intro F _ _ _ H b hs hc hbi hbd p
    simpa using norm_integral_le_of_norm_le (hbi 0) ((hbd 0).mono fun a ha => by simpa using ha p)
  | succ n ih =>
    intro F _ _ _ H b hs hc hbi hbd p
    have hm : ∀ p, AEStronglyMeasurable (H p) μ := by
      intro p
      have := (continuousMultilinearCurryFin0 ℝ P F).continuous.comp_aestronglyMeasurable (hc 0 p)
      simpa [Function.comp_def, iteratedFDeriv_zero_eq_comp] using this
    have hc' : ∀ k p, AEStronglyMeasurable
        (fun a => iteratedFDeriv ℝ k (fun q => fderiv ℝ (fun r => H r a) q) p) μ := by
      intro k p
      have := (continuousMultilinearCurryRightEquiv' ℝ k P F).continuous.comp_aestronglyMeasurable
        (hc (k + 1) p)
      simpa [Function.comp_def, iteratedFDeriv_succ_eq_comp_right] using this
    have he : fderiv ℝ (fun q => ∫ a, H q a ∂μ) = fun q => ∫ a, fderiv ℝ (fun r => H r a) q ∂μ := by
      funext q
      have hd : HasFDerivAt (fun q => ∫ a, H q a ∂μ)
          (∫ a, fderiv ℝ (fun r => H r a) q ∂μ) q := by
        refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := H)
          (F' := fun q a => fderiv ℝ (fun r => H r a) q) (bound := b 1)
          (s := Set.univ) (by simp) (Filter.Eventually.of_forall (fun r => hm r)) ?_ ?_ ?_ (hbi 1)
            ?_
        · exact (hbi 0).mono' (hm q) ((hbd 0).mono fun a ha => by simpa using ha q)
        · have := (continuousMultilinearCurryFin0 ℝ P (P →L[ℝ]
          F)).continuous.comp_aestronglyMeasurable
            (hc' 0 q)
          simpa [Function.comp_def, iteratedFDeriv_zero_eq_comp] using this
        · exact (hbd 1).mono fun a ha r hr => by simpa using ha r
        · exact Filter.Eventually.of_forall fun a r hr =>
            (((hs a).differentiable (by simp)) r).hasFDerivAt
      exact hd.fderiv
    rw [← norm_iteratedFDeriv_fderiv, he]
    apply ih (P →L[ℝ] F) _ (fun k => b (k + 1))
      (fun a => (hs a).fderiv_right (m := ∞) (by simp)) hc' (fun k => hbi (k + 1))
    intro k
    exact (hbd (k + 1)).mono fun a ha q => by rw [norm_iteratedFDeriv_fderiv]; exact ha q

/-- The derivatives in the first variable of a jointly smooth function are jointly continuous. -/
lemma continuous_iteratedFDeriv_partial {P α F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup α] [NormedSpace ℝ α] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : P × α → F) (hH : ContDiff ℝ ∞ H) (k : ℕ) :
    Continuous fun z : P × α => iteratedFDeriv ℝ k (fun q => H (q, z.2)) z.1 := by
  have e : ∀ a : α, (fun q : P => H (q, a)) =
      (fun w : P × α => H (w + (0, a))) ∘ (ContinuousLinearMap.inl ℝ P α) := by
    intro a; funext q; simp
  have hd : ∀ a : α, ContDiff ℝ ∞ (fun w : P × α => H (w + (0, a))) := fun a =>
    hH.comp (ContDiff.add contDiff_id contDiff_const)
  have key : ∀ z : P × α, iteratedFDeriv ℝ k (fun q => H (q, z.2)) z.1 =
      (iteratedFDeriv ℝ k H (z.1, z.2)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ P α) := by
    intro z
    rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ (hd z.2) z.1 (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_right]
    simp
  simp_rw [key]
  have hc : Continuous fun z : P × α => iteratedFDeriv ℝ k H z :=
    hH.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin k => ContinuousLinearMap.inl ℝ P α)).continuous.comp hc

end ParametricIntegral
