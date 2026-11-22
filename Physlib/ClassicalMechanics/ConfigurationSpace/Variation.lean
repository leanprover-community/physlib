/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Physlib.ClassicalMechanics.ConfigurationSpace.Basic
public import Physlib.SpaceAndTime.Time.ManifoldCurves

/-!
# Variations of curves

Smooth variations of a curve in a configuration space fixing the endpoints.

## i. Overview

Variations probe the action of a Lagrangian system around a curve. Variations supported in a chart
test the Euler-Lagrange equations there.

## ii. Key results

- `Variation` : smooth variations fixing the endpoints.
- `Variation.contDiff_comp_vadd` : a variation of a curve in a normed space is smooth in
  coordinates.
- `Variation.exists_bump` : a bump function gives a variation of a curve in a normed space.
- `Variation.exists_chart_bump` : a bump function and a vector give a variation supported in a
  chart.

## iii. Table of contents

- A. Variations
- B. Variations in a normed space
- C. Variations supported in a chart

## iv. References

* I. Terek, Introductory Variational Calculus on Manifolds. [ref: terek_variational_manifolds]
-/

@[expose] public section

namespace ClassicalMechanics

open Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : ConfigurationSpace I)

/-!
## A. Variations
-/

variable {M} in
/-- A smooth variation of `γ` on `[t₀, t₁]` fixing `γ t₀` and `γ t₁`. -/
@[ext]
structure Variation (γ : Time → M) (t₀ t₁ : Time) where
  /-- The smooth family of curves. -/
  toFun : C^∞⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ), ℝ × Time; I, M⟯
  /-- Starts at `γ`. -/
  apply_zero : ∀ s ∈ Set.Icc 0 (t₁ -ᵥ t₀), toFun (0, s +ᵥ t₀) = γ (s +ᵥ t₀)
  /-- Fixes `γ t₀`. -/
  apply_left : ∀ s, toFun (s, t₀) = γ t₀
  /-- Fixes `γ t₁`. -/
  apply_right : ∀ s, toFun (s, t₁) = γ t₁

namespace Variation

variable {I M} in
/-- A smooth curve admits the constant variation. -/
lemma nonempty {γ : Time → M} {t₀ t₁ : Time} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) :
    Nonempty (Variation I γ t₀ t₁) :=
  ⟨⟨⟨fun p ↦ γ p.2, hγ.comp contMDiff_snd⟩, fun _ _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩⟩

/-!
## B. Variations in a normed space
-/

/-- `(s, τ) ↦ h (s, τ +ᵥ t₀)` is smooth. -/
lemma contDiff_comp_vadd {γ : Time → E} {t₀ t₁ : Time}
    (h : Variation (M := ⟨E⟩) 𝓘(ℝ, E) γ t₀ t₁) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ h.toFun (p.1, p.2 +ᵥ t₀)) := by
  have key (f : ℝ × ℝ → E) (hf : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ f) :
      ContDiff ℝ ∞ f := by
    rwa [← modelWithCornersSelf_prod (𝕜 := ℝ) (E := ℝ) (F := ℝ),
      chartedSpaceSelf_prod (H := ℝ) (H' := ℝ), contMDiff_iff_contDiff] at hf
  exact key _ (h.toFun.contMDiff.comp
    (contMDiff_fst.prodMk ((Time.contMDiff_vadd t₀ ∞).comp contMDiff_snd)))

/-- For a smooth curve `γ`, smooth `ψ` supported in `(0, t₁ -ᵥ t₀)` and `w : E`, there exists a
variation `h` of `γ` with `h (s, τ +ᵥ t₀) = γ (τ +ᵥ t₀) + s • ψ τ • w`. -/
lemma exists_bump {γ : Time → E} {t₀ t₁ : Time} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ Ioo 0 (t₁ -ᵥ t₀)) (w : E) :
    ∃ h : Variation (M := ⟨E⟩) 𝓘(ℝ, E) γ t₀ t₁,
      ∀ s τ, h.toFun (s, τ +ᵥ t₀) = γ (τ +ᵥ t₀) + s • (ψ τ • w) := by
  have hψt : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : Time ↦ ψ (t -ᵥ t₀)) :=
    (Time.contMDiff_iff_contDiff_vadd _ t₀ ∞).2 (by simpa using hψ)
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × Time ↦ γ p.2 + p.1 • (ψ (p.2 -ᵥ t₀) • w)) :=
    ContMDiff.add (hγ.comp contMDiff_snd)
      (contMDiff_fst.smul ((hψt.comp contMDiff_snd).smul contMDiff_const))
  have h0 : ψ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hs h).1.false
  have hT : ψ (t₁ -ᵥ t₀) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hs h).2.false
  refine ⟨⟨⟨fun p ↦ γ p.2 + p.1 • (ψ (p.2 -ᵥ t₀) • w), hF⟩, fun s _ ↦ ?_, fun s ↦ ?_, fun s ↦ ?_⟩,
    fun s τ ↦ ?_⟩
  · simp
  · simp [h0]
  · simp only [Time.vsub_eq_val] at hT
    simp [hT]
  · simp

/-!
## C. Variations supported in a chart
-/

section Chart

variable {I M}

/-- For `0 < ε` there is a smooth `σ` with `σ 0 = 0`, `σ' 0 = 1` and values in `[-ε, ε]`. -/
private lemma exists_contDiff_deriv_one {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : ℝ → ℝ, ContDiff ℝ ∞ σ ∧ σ 0 = 0 ∧ deriv σ 0 = 1 ∧ ∀ s, σ s ∈ Icc (-ε) ε :=
  ⟨fun s ↦ ε * Real.sin (s / ε), by fun_prop, by simp, by simp; field_simp, fun s ↦ by
    constructor <;> nlinarith [Real.neg_one_le_sin (s / ε), Real.sin_le_one (s / ε)]⟩

/-- There is a family of curves `F (s, t)`, jointly smooth in `s` and `t`, equal to `γ` for `t`
outside a closed set `Z` and to `γ` shifted in the chart at `x` by `σ s • Ψ t • w` wherever `γ t`
is in the chart. Here `σ` and `Ψ` are smooth, `Ψ` vanishes off `Z`, `w : E`, and `hZs`, `hZt` keep
`γ` and its shifts over `Z` in the chart source and target. -/
private lemma exists_contMDiff_chart_shift [I.Boundaryless] (x : M) {γ : Time → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {Z : Set Time} (hZc : IsClosed Z)
    {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) {Ψ : Time → ℝ} (hΨ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Ψ)
    (hΨ0 : ∀ t ∉ Z, Ψ t = 0) (w : E) (hZs : ∀ t ∈ Z, γ t ∈ (extChartAt I x).source)
    (hZt : ∀ t ∈ Z, ∀ s, extChartAt I x (γ t) + σ s • (Ψ t • w) ∈ (extChartAt I x).target) :
    ∃ F : ℝ × Time → M, ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞ F ∧
      (∀ s t, t ∉ Z → F (s, t) = γ t) ∧
      ∀ s t, γ t ∈ (extChartAt I x).source →
        F (s, t) = (extChartAt I x).symm (extChartAt I x (γ t) + σ s • (Ψ t • w)) := by
  classical
  refine ⟨fun p ↦ if p.2 ∈ Z then
    (extChartAt I x).symm (extChartAt I x (γ p.2) + σ p.1 • (Ψ p.2 • w)) else γ p.2,
    fun p ↦ ?_, fun s t ht ↦ by simp [ht], fun s t ht ↦ ?_⟩
  · by_cases hp : p.2 ∈ Z
    -- over `Z`, `F` is smooth near `p` as the chart shift, which agrees with `F` nearby
    · have hch : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (extChartAt I x ∘ γ) p.2 :=
        (contMDiffAt_extChartAt' (by rw [← extChartAt_source I]; exact hZs _ hp)).comp p.2
          (hγ p.2)
      refine (((contMDiffOn_extChartAt_symm x).contMDiffAt
        (extChartAt_target_mem_nhds' (hZt _ hp p.1))).comp p
        ((hch.comp p contMDiff_snd.contMDiffAt).add
          (((hσ.contMDiff.comp contMDiff_fst).contMDiffAt).smul
            (((hΨ.comp contMDiff_snd).contMDiffAt).smul
              contMDiffAt_const)))).congr_of_eventuallyEq ?_
      filter_upwards [(hγ.continuous.comp continuous_snd).continuousAt.eventually_mem
        ((isOpen_extChartAt_source x).mem_nhds (hZs _ hp))] with q hq1
      split_ifs with hq
      · rfl
      · simpa [hΨ0 _ hq] using ((extChartAt I x).left_inv hq1).symm
    -- off `Z`, `F` equals `γ` on the open complement of `Z`
    · refine ((hγ.contMDiffAt (x := p.2)).comp p contMDiff_snd.contMDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [continuous_snd.continuousAt.eventually_mem (hZc.isOpen_compl.mem_nhds hp)]
        with q hq
      exact ite_eq_right hq
  · by_cases hZ : t ∈ Z
    · simp [hZ]
    · simpa [hZ, hΨ0 _ hZ] using ((extChartAt I x).left_inv ht).symm

/-- A variation of `γ` which, in the chart at `x`, translates `γ (τ +ᵥ t₀)` by `σ s • ψ τ • w`, and
fixes `γ` off `tsupport ψ`. Here `ψ` is a bump function, `w : E`, and `σ` is smooth with `σ 0 = 0`,
`σ' 0 = 1` and values in `[-ε, ε]`, where `ε` keeps the shifts in the chart target. -/
lemma exists_chart_bump [I.Boundaryless] {γ : Time → M} {t₀ t₁ : Time} (x : M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : tsupport ψ ⊆ Ioo 0 (t₁ -ᵥ t₀))
    (hx : ∀ τ ∈ tsupport ψ, γ (τ +ᵥ t₀) ∈ (extChartAt I x).source) (w : E) {ε : ℝ} (hε : 0 < ε)
    (hNε : ∀ τ ∈ tsupport ψ, ∀ r ∈ Icc (-ε) ε,
      extChartAt I x (γ (τ +ᵥ t₀)) + r • (ψ τ • w) ∈ (extChartAt I x).target) :
    ∃ (h : Variation I γ t₀ t₁) (σ : ℝ → ℝ), ContDiff ℝ ∞ σ ∧ σ 0 = 0 ∧ deriv σ 0 = 1 ∧
      (∀ s, σ s ∈ Icc (-ε) ε) ∧ (∀ s τ, τ ∉ tsupport ψ → h.toFun (s, τ +ᵥ t₀) = γ (τ +ᵥ t₀)) ∧
      (∀ s τ, γ (τ +ᵥ t₀) ∈ (extChartAt I x).source → h.toFun (s, τ +ᵥ t₀) =
        (extChartAt I x).symm (extChartAt I x (γ (τ +ᵥ t₀)) + σ s • (ψ τ • w))) := by
  obtain ⟨σ, hσ, hσ0, hσ'0, hσε⟩ := exists_contDiff_deriv_one hε
  obtain ⟨F, hF, hnZ, hsymm⟩ := exists_contMDiff_chart_shift x hγ (Z := {t | t -ᵥ t₀ ∈ tsupport ψ})
    ((isClosed_tsupport ψ).preimage (continuous_id.vsub continuous_const)) hσ
    (Ψ := fun t ↦ ψ (t -ᵥ t₀)) ((Time.contMDiff_iff_contDiff_vadd _ t₀ ∞).2 (by simpa using hψ))
    (fun t ht ↦ image_eq_zero_of_notMem_tsupport ht) w
    (fun t ht ↦ by simpa only [vsub_vadd] using hx (t -ᵥ t₀) ht)
    fun t ht s ↦ by simpa only [vsub_vadd] using hNε (t -ᵥ t₀) ht (σ s) (hσε s)
  have h0 (t) : F (0, t) = γ t := by
    by_cases ht : γ t ∈ (extChartAt I x).source
    · simpa [hσ0, hsymm _ _ ht] using (extChartAt I x).left_inv ht
    · exact hnZ _ _ fun hZ ↦ ht (by simpa only [vsub_vadd] using hx _ hZ)
  exact ⟨⟨⟨F, hF⟩, fun s _ ↦ h0 _, fun s ↦ hnZ _ _ fun h ↦ by simpa using (hs h).1,
    fun s ↦ hnZ _ _ fun h ↦ (hs h).2.false⟩, σ, hσ, hσ0, hσ'0, hσε,
    fun s τ hτ ↦ hnZ _ _ (by simpa using hτ), fun s τ hτ ↦ by simpa using hsymm s _ hτ⟩

end Chart

end Variation

end ClassicalMechanics
