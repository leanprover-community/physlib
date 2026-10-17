/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kento Mori, Hayata Yamasaki
-/
module

public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.LownerHeinzCore

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.InnerProductSpace.StarOrder

@[expose] public section

/-!
## Wrapper（`B(ℋ)`）

このファイルは `LownerHeinzCore` の結果を、`L ℋ := ℋ →L[ℂ] ℋ`（有界線形作用素）に
**特殊化して再公開する薄い wrapper** です。

- 証明は `simpa using` による Core の特殊化のみ（重複証明は書かない）
- `B(ℋ)` 側では既存の Loewner order の ecosystem を尊重し、`spectralOrder` は導入しません
  （`spectralOrder` が必要な場合は `LownerHeinzCore.Spectral` を利用）
-/

namespace LownerHeinzTheorem

universe u v

open CFC

abbrev L (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] : Type u :=
  ℋ →L[ℂ] ℋ

variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

noncomputable instance instNontrivialL : Nontrivial (L ℋ) := inferInstance

set_option synthInstance.maxHeartbeats 40000 in
noncomputable local instance : NonnegSpectrumClass ℝ (L ℋ) := inferInstance

set_option synthInstance.maxHeartbeats 80000 in
noncomputable instance instCFCRealSelfAdjoint :
    ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint := inferInstance

noncomputable abbrev cfcR (f : ℝ → ℝ) (A : L ℋ) : L ℋ :=
  LownerHeinzCore.cfcR (𝓐 := L ℋ) f A

/-- Fixed-space operator monotonicity on the Hilbert space `ℋ`. -/
def OperatorMonotone (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorMonotone (𝓐 := L ℋ) f

/-- Fixed-space operator monotonicity on `s` for the Hilbert space `ℋ`. -/
def OperatorMonotoneOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorMonotoneOn (𝓐 := L ℋ) s f

/-- Fixed-space operator antitonicity on the Hilbert space `ℋ`. -/
def OperatorAntitone (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorAntitone (𝓐 := L ℋ) f

/-- Fixed-space operator antitonicity on `s` for the Hilbert space `ℋ`. -/
def OperatorAntitoneOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorAntitoneOn (𝓐 := L ℋ) s f

/-- Fixed-space operator convexity on the Hilbert space `ℋ`. -/
def OperatorConvex (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConvex (𝓐 := L ℋ) f

/-- Fixed-space operator convexity on `s` for the Hilbert space `ℋ`. -/
def OperatorConvexOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConvexOn (𝓐 := L ℋ) s f

/-- Fixed-space operator concavity on the Hilbert space `ℋ`. -/
def OperatorConcave (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConcave (𝓐 := L ℋ) f

/-- Fixed-space operator concavity on `s` for the Hilbert space `ℋ`. -/
def OperatorConcaveOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConcaveOn (𝓐 := L ℋ) s f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator monotonicity over all Hilbert spaces in universe `u`. -/
def OperatorMonotoneAll (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorMonotone (ℋ := K) f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator monotonicity on `s` over all Hilbert spaces in universe `u`. -/
def OperatorMonotoneOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorMonotoneOn (ℋ := K) s f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator antitonicity over all Hilbert spaces in universe `u`. -/
def OperatorAntitoneAll (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorAntitone (ℋ := K) f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator antitonicity on `s` over all Hilbert spaces in universe `u`. -/
def OperatorAntitoneOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorAntitoneOn (ℋ := K) s f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator convexity over all Hilbert spaces in universe `u`. -/
def OperatorConvexAll (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorConvex (ℋ := K) f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator convexity on `s` over all Hilbert spaces in universe `u`. -/
def OperatorConvexOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorConvexOn (ℋ := K) s f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator concavity over all Hilbert spaces in universe `u`. -/
def OperatorConcaveAll (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorConcave (ℋ := K) f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator concavity on `s` over all Hilbert spaces in universe `u`. -/
def OperatorConcaveOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorConcaveOn (ℋ := K) s f

lemma operatorConvex_convexOn_univ {f : ℝ → ℝ} (hf : OperatorConvex (ℋ := ℋ) f) :
    ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hb1 : b ≤ 1 := by
    linarith
  have halg_combo (u v r s : ℝ) :
      u • (algebraMap ℝ (L ℋ) r) + v • (algebraMap ℝ (L ℋ) s) =
        algebraMap ℝ (L ℋ) (u * r + v * s) := by
    calc
      u • (algebraMap ℝ (L ℋ) r) + v • (algebraMap ℝ (L ℋ) s) =
          (algebraMap ℝ (L ℋ) u) * (algebraMap ℝ (L ℋ) r) +
            (algebraMap ℝ (L ℋ) v) * (algebraMap ℝ (L ℋ) s) := by
              rw [Algebra.smul_def, Algebra.smul_def]
      _ = algebraMap ℝ (L ℋ) (u * r) + algebraMap ℝ (L ℋ) (v * s) := by
            simp
      _ = algebraMap ℝ (L ℋ) (u * r + v * s) := by
            simp
  have hop :
      cfcR (ℋ := ℋ) f
          ((1 - b) • (algebraMap ℝ (L ℋ) x) + b • (algebraMap ℝ (L ℋ) y)) ≤
        (1 - b) • cfcR (ℋ := ℋ) f (algebraMap ℝ (L ℋ) x) +
          b • cfcR (ℋ := ℋ) f (algebraMap ℝ (L ℋ) y) :=
    hf (A := algebraMap ℝ (L ℋ) x) (B := algebraMap ℝ (L ℋ) y) (t := b) hb hb1
  have hx :
      cfcR (ℋ := ℋ) f (algebraMap ℝ (L ℋ) x) = algebraMap ℝ (L ℋ) (f x) := by
    simp [cfcR, LownerHeinzCore.cfcR]
  have hy :
      cfcR (ℋ := ℋ) f (algebraMap ℝ (L ℋ) y) = algebraMap ℝ (L ℋ) (f y) := by
    simp [cfcR, LownerHeinzCore.cfcR]
  have hxy :
      cfcR (ℋ := ℋ) f (algebraMap ℝ (L ℋ) ((1 - b) * x + b * y)) =
        algebraMap ℝ (L ℋ) (f ((1 - b) * x + b * y)) := by
    simpa [cfcR, LownerHeinzCore.cfcR] using
      cfc_algebraMap (A := L ℋ) (((1 - b) * x + b * y)) f
  rw [halg_combo (u := 1 - b) (v := b) (r := x) (s := y), hxy, hx, hy,
    halg_combo (u := 1 - b) (v := b) (r := f x) (s := f y)] at hop
  have hscalar :
      algebraMap ℝ (L ℋ) (f ((1 - b) * x + b * y)) ≤
        algebraMap ℝ (L ℋ) ((1 - b) * f x + b * f y) := by
    simpa [Algebra.smul_def] using hop
  have hspec_le :
      ∀ z ∈ spectrum ℝ (algebraMap ℝ (L ℋ) (f ((1 - b) * x + b * y))),
        z ≤ (1 - b) * f x + b * f y := by
    simpa using
      (le_algebraMap_iff_spectrum_le
        (R := ℝ) (A := L ℋ)
        (a := algebraMap ℝ (L ℋ) (f ((1 - b) * x + b * y)))
        (r := (1 - b) * f x + b * f y)
        (ha := cfc_predicate_algebraMap (A := L ℋ) (f ((1 - b) * x + b * y)))).1 hscalar
  have ha' : a = 1 - b := by
    linarith
  have hscalar' : f ((1 - b) * x + b * y) ≤ (1 - b) * f x + b * f y := by
    obtain ⟨z, hz⟩ :=
      ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ)
        (algebraMap ℝ (L ℋ) (f ((1 - b) * x + b * y)))
        (cfc_predicate_algebraMap (A := L ℋ) (f ((1 - b) * x + b * y)))
    have hz_eq : z = f ((1 - b) * x + b * y) := by
      have hz_single :=
        CFC.spectrum_algebraMap_subset (R := ℝ) (A := L ℋ) (f ((1 - b) * x + b * y)) hz
      simpa using hz_single
    simpa [hz_eq] using hspec_le z hz
  simpa [smul_eq_mul, ha'] using hscalar'

lemma operatorConvex_continuousOn_univ {f : ℝ → ℝ} (hf : OperatorConvex (ℋ := ℋ) f) :
    ContinuousOn f Set.univ :=
  ConvexOn.continuousOn isOpen_univ (operatorConvex_convexOn_univ (ℋ := ℋ) hf)

lemma operatorConvex_continuousOn_spectrum_union {f : ℝ → ℝ}
    (hf : OperatorConvex (ℋ := ℋ) f) (A B : L ℋ) :
    ContinuousOn f (spectrum ℝ A ∪ spectrum ℝ B) :=
  (operatorConvex_continuousOn_univ (ℋ := ℋ) hf).mono (by intro x hx; simp)


omit [Nontrivial ℋ] in
lemma one_div_operatorAntitoneOn_Ioi :
    OperatorAntitoneOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) := by
  exact (LownerHeinzCore.one_div_operatorAntitoneOn_Ioi (𝓐 := L ℋ))

lemma one_div_operatorConvexOn_Ioi :
    OperatorConvexOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) := by
  exact (LownerHeinzCore.one_div_operatorConvexOn_Ioi (𝓐 := L ℋ))

omit [Nontrivial ℋ] in
lemma one_div_add_t_operatorAntitoneOn_Ici : ∀ (t : ℝ), 0 < t →
    OperatorAntitoneOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ 1 / (x + t)) := by
  intro t ht
  exact (LownerHeinzCore.one_div_add_t_operatorAntitoneOn_Ici (𝓐 := L ℋ) t ht)

lemma one_div_add_t_operatorConvexOn_Ici : ∀ (t : ℝ), 0 < t →
    OperatorConvexOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ 1 / (x + t)) := by
  intro t ht
  exact (LownerHeinzCore.one_div_add_t_operatorConvexOn_Ici (𝓐 := L ℋ) t ht)

omit [Nontrivial ℋ] in
lemma ratio_add_t_operatorMonotoneOn_Ici : ∀ (t : ℝ), 0 < t →
    OperatorMonotoneOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x / (x + t)) := by
  intro t ht
  exact (LownerHeinzCore.ratio_add_t_operatorMonotoneOn_Ici (𝓐 := L ℋ) t ht)

lemma ratio_add_t_operatorConcaveOn_Ici : ∀ (t : ℝ), 0 < t →
    OperatorConcaveOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x / (x + t)) := by
  intro t ht
  exact (LownerHeinzCore.ratio_add_t_operatorConcaveOn_Ici (𝓐 := L ℋ) t ht)

omit [Nontrivial ℋ] in
lemma power_Icc_zero_one_operatorMonotoneOn_Ici : ∀ p ∈ Set.Icc (0 : ℝ) 1,
    OperatorMonotoneOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  exact (LownerHeinzCore.power_Icc_zero_one_operatorMonotoneOn_Ici (𝓐 := L ℋ) p hp)

lemma power_Icc_zero_one_operatorConcaveOn_Ici : ∀ p ∈ Set.Icc (0 : ℝ) 1,
    OperatorConcaveOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  exact (LownerHeinzCore.power_Icc_zero_one_operatorConcaveOn_Ici (𝓐 := L ℋ) p hp)

lemma power_Icc_one_two_operatorConvexOn_Ici : ∀ p ∈ Set.Icc (1 : ℝ) 2,
    OperatorConvexOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  exact (LownerHeinzCore.power_Icc_one_two_operatorConvexOn_Ici (𝓐 := L ℋ) p hp)

omit [Nontrivial ℋ] in
lemma power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi : ∀ p ∈ Set.Icc (-1 : ℝ) 0,
    OperatorMonotoneOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x ↦ -(x ^ p)) := by
  intro p hp
  exact (LownerHeinzCore.power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi (𝓐 := L ℋ) p hp)

lemma power_Icc_neg_one_zero_neg_operatorConcaveOn_Ioi : ∀ p ∈ Set.Icc (-1 : ℝ) 0,
    OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x ↦ -(x ^ p)) := by
  intro p hp
  exact (LownerHeinzCore.power_Icc_neg_one_zero_neg_operatorConcaveOn_Ioi (𝓐 := L ℋ) p hp)

end LownerHeinzTheorem
