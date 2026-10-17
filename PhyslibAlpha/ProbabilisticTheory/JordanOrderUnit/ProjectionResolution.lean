/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Measurement.BoundedIntegral
public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.JB.Basic

/-!

# Projection resolutions

Projection resolutions: projection-valued effect measures and their bounded Borel calculus.

## i. Overview

A projection resolution is an effect-valued measure whose values are Jordan projections and whose
value on an intersection is the Jordan product of the values. Integrating bounded measurable
functions against it gives a bounded Borel functional calculus.

## ii. Key results

- `MeasurableProjectionResolution` : projection resolutions.
- `MeasurableProjectionResolution.jordanOrthogonal_of_disjoint` : disjoint sets give orthogonal
  projections.
- `MeasurableProjectionResolution.boundedBorel` : the bounded Borel functional calculus.

## iii. Table of contents

- A. Bounded Borel calculus

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

open Function

section Core

variable {Ω E : Type*} [MeasurableSpace Ω] [IsJordanOrderUnit E]

/-- A projection resolution: an effect-valued measure whose values are Jordan projections, with the
value on an intersection the Jordan product of the values. -/
structure MeasurableProjectionResolution (Ω : Type*) [MeasurableSpace Ω] (E : Type*)
    [IsJordanOrderUnit E] where
  /-- The underlying countably additive effect-valued measure. -/
  toEffectValuedMeasure : EffectValuedMeasure Ω E
  /-- Every measurable event is a Jordan projection. -/
  isJordanProjection' : ∀ s hs,
    JordanAlgebra.IsJordanProjection (toEffectValuedMeasure s hs : E)
  /-- Intersection of measurable events is multiplication of their projections. -/
  map_inter' : ∀ s t hs ht,
    (toEffectValuedMeasure s hs : E) * (toEffectValuedMeasure t ht : E) =
      (toEffectValuedMeasure (s ∩ t) (hs.inter ht) : E)

namespace MeasurableProjectionResolution

instance : CoeOut (MeasurableProjectionResolution Ω E) (EffectValuedMeasure Ω E) :=
  ⟨MeasurableProjectionResolution.toEffectValuedMeasure⟩

instance : CoeFun (MeasurableProjectionResolution Ω E) fun _ =>
    ∀ s : Set Ω, MeasurableSet s → Effect E :=
  ⟨fun P => P.toEffectValuedMeasure⟩

/-- Projection resolutions are determined by their event projections.  This is purely structural
and belongs below JBW: normal-state separation is only one later way to establish its premise. -/
@[ext]
lemma ext {P Q : MeasurableProjectionResolution Ω E}
    (h : ∀ s hs, (P s hs : E) = (Q s hs : E)) : P = Q := by
  cases P with
  | mk P hP hPinter =>
    cases Q with
    | mk Q hQ hQinter =>
      dsimp at h ⊢
      have hPQ : P = Q := EffectValuedMeasure.ext fun s hs =>
        Subtype.ext (h s hs)
      subst Q
      rfl

/-- The impossible event is the zero effect. -/
lemma map_empty (P : MeasurableProjectionResolution Ω E) :
    P ∅ MeasurableSet.empty = 0 :=
  P.toEffectValuedMeasure.map_empty

/-- The whole outcome space is the unit effect. -/
lemma map_univ (P : MeasurableProjectionResolution Ω E) :
    P Set.univ MeasurableSet.univ = 1 :=
  P.toEffectValuedMeasure.map_univ

/-- Each event of a measurable projection resolution is an intrinsic Jordan projection. -/
lemma isJordanProjection (P : MeasurableProjectionResolution Ω E)
    (s : Set Ω) (hs : MeasurableSet s) :
    JordanAlgebra.IsJordanProjection (P s hs : E) :=
  P.isJordanProjection' s hs

/-- The projection product computes measurable intersection. -/
lemma map_inter (P : MeasurableProjectionResolution Ω E)
    (s t : Set Ω) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (P s hs : E) * (P t ht : E) = P (s ∩ t) (hs.inter ht) :=
  P.map_inter' s t hs ht

/-- Disjoint measurable events have Jordan-orthogonal projections. -/
lemma jordanOrthogonal_of_disjoint (P : MeasurableProjectionResolution Ω E)
    {s t : Set Ω} (hs : MeasurableSet s) (ht : MeasurableSet t) (hdisj : Disjoint s t) :
    JordanAlgebra.JordanOrthogonal (P s hs : E) (P t ht : E) := by
  rw [JordanAlgebra.JordanOrthogonal, P.map_inter s t hs ht]
  have hinter : s ∩ t = ∅ := hdisj.inter_eq
  simp only [hinter]
  change ((P ∅ MeasurableSet.empty : Effect E) : E) = 0
  rw [P.map_empty]
  rfl

/-- The inherited countable-additivity law, stated in the ambient ordered Jordan algebra. -/
lemma countably_additive (P : MeasurableProjectionResolution Ω E) (s : ℕ → Set Ω)
    (hsm : ∀ n, MeasurableSet (s n)) (hs : Pairwise (Disjoint on s)) :
    IsLUB (Set.range fun N : ℕ => ∑ n ∈ Finset.range N, (P (s n) (hsm n) : E))
      (P (⋃ n, s n) (MeasurableSet.iUnion hsm) : E) :=
  P.toEffectValuedMeasure.countably_additive hsm hs

end MeasurableProjectionResolution

end Core

/-! ## A. Bounded Borel calculus

The resolution does not duplicate the order-unit integral: in a JB algebra, which is complete in
its order-unit norm, this section gives that integral its spectral-calculus name. -/

namespace MeasurableProjectionResolution

section BoundedBorel

variable {Ω E : Type*} [MeasurableSpace Ω] [IsJBOrderUnit E]

/-- The bounded Borel calculus of a measurable projection resolution. This is the existing
effect-valued integral applied to the underlying measure, not a parallel construction. -/
noncomputable def boundedBorel (P : MeasurableProjectionResolution Ω E) (f : Ω → ℝ)
    (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) : E :=
  EffectValuedMeasure.integral hf hM P.toEffectValuedMeasure

/-- A nonnegative bounded Borel function has a positive value under the resolution calculus. -/
lemma nonneg_boundedBorel (P : MeasurableProjectionResolution Ω E) (f : Ω → ℝ)
    (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) (hf0 : ∀ x, 0 ≤ f x) :
    0 ≤ P.boundedBorel f hf hM :=
  EffectValuedMeasure.nonneg_integral hf hM hf0 P.toEffectValuedMeasure

/-- The bounded Borel value is independent of the particular valid uniform bound used to
construct the completed order-unit integral. -/
lemma boundedBorel_indep_of_bound (P : MeasurableProjectionResolution Ω E) (f : Ω → ℝ)
    (hf : Measurable f) {M M' : ℝ} (hM : ∀ x, |f x| ≤ M) (hM' : ∀ x, |f x| ≤ M') :
    P.boundedBorel f hf hM = P.boundedBorel f hf hM' :=
  EffectValuedMeasure.integral_indep_of_bound hf hM hM' P.toEffectValuedMeasure

/-- The bounded Borel calculus is additive. -/
lemma boundedBorel_add (P : MeasurableProjectionResolution Ω E) {f g : Ω → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (hg : Measurable g) {M' : ℝ} (hM' : ∀ x, |g x| ≤ M')
    (hfg : Measurable (f + g)) (hMfg : ∀ x, |(f + g) x| ≤ M + M') :
    P.boundedBorel (f + g) hfg hMfg =
      P.boundedBorel f hf hM + P.boundedBorel g hg hM' :=
  EffectValuedMeasure.integral_add hf hM hg hM' P.toEffectValuedMeasure

/-- The bounded Borel calculus is real-homogeneous. -/
lemma boundedBorel_smul (P : MeasurableProjectionResolution Ω E) (c : ℝ) {f : Ω → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (hcf : Measurable (c • f)) (hMcf : ∀ x, |(c • f) x| ≤ |c| * M) :
    P.boundedBorel (c • f) hcf hMcf = c • P.boundedBorel f hf hM :=
  EffectValuedMeasure.integral_smul hf hM c P.toEffectValuedMeasure

/-- The functional calculus of an indicator is the projection of the event. -/
lemma boundedBorel_indicator (P : MeasurableProjectionResolution Ω E) {s : Set Ω}
    (hs : MeasurableSet s) :
    P.boundedBorel (s.indicator fun _ : Ω => (1 : ℝ)) (measurable_const.indicator hs)
        (M := 1) (by intro x; by_cases hx : x ∈ s <;> simp [hx]) = (P s hs : E) := by
  classical
  let c : Bool → ℝ := fun b => if b then 1 else 0
  let pieces : Bool → Set Ω := fun b => if b then s else sᶜ
  have hpieces : EffectValuedMeasure.IsPartition pieces :=
    { measurable := by intro b; cases b <;> simp [pieces, hs]
      disjoint := by
        intro b b' hne
        cases b <;> cases b'
        · exact (hne rfl).elim
        · exact disjoint_compl_left
        · exact disjoint_compl_right
        · exact (hne rfl).elim
      cover := by
        apply Set.Subset.antisymm
        · exact Set.subset_univ _
        · intro x _
          by_cases hx : x ∈ s
          · exact Set.mem_iUnion.2 ⟨true, by simp [pieces, hx]⟩
          · exact Set.mem_iUnion.2 ⟨false, by simp [pieces, hx]⟩ }
  have hvalue : ∀ x, EffectValuedMeasure.simpleValue c pieces x =
      s.indicator (fun _ : Ω => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ s
    · rw [EffectValuedMeasure.simpleValue_apply_of_mem hpieces (i := true)]
      · simp [c, hx]
      · simp [pieces, hx]
    · rw [EffectValuedMeasure.simpleValue_apply_of_mem hpieces (i := false)]
      · simp [c, hx]
      · simp [pieces, hx]
  rw [boundedBorel, EffectValuedMeasure.integral_eq_simpleIntegral
    (measurable_const.indicator hs) (by intro x; by_cases hx : x ∈ s <;> simp [hx])
    hpieces hvalue]
  unfold EffectValuedMeasure.simpleIntegral
  simp [c, pieces]

/-- The constant-one bounded Borel function integrates to the order unit.  This is the
normalization of the inherited effect-valued measure, recovered from the indicator law for the
whole outcome space. -/
lemma boundedBorel_one (P : MeasurableProjectionResolution Ω E) :
    P.boundedBorel (fun _ : Ω => (1 : ℝ)) measurable_const (M := 1) (by intro _; simp) = 1 := by
  simpa using P.boundedBorel_indicator (s := Set.univ) MeasurableSet.univ

/-- A measurable `[0,1]`-valued bounded function has an effect-valued bounded Borel calculus.
This packages positivity and normalization once at the shared projection-resolution layer; every
JBW projection resolution inherits it. -/
noncomputable def boundedBorelEffect (P : MeasurableProjectionResolution Ω E) (f : Ω → ℝ)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) : Effect E :=
  let g : Ω → ℝ := fun x => 1 - f x
  have hfbound : ∀ x, |f x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (hf0 x)]
    exact hf1 x
  have hgbound : ∀ x, |g x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (sub_nonneg.mpr (hf1 x))]
    exact sub_le_self 1 (hf0 x)
  have hg : Measurable g := measurable_const.sub hf
  have hg0 : ∀ x, 0 ≤ g x := fun x => sub_nonneg.mpr (hf1 x)
  have hsummeas : Measurable (f + g) := hf.add hg
  have hsumbound : ∀ x, |(f + g) x| ≤ 1 + 1 := fun x => by
    change |f x + (1 - f x)| ≤ 1 + 1
    norm_num
  have hsum := P.boundedBorel_add hf hfbound hg hgbound hsummeas hsumbound
  ⟨P.boundedBorel f hf hfbound, P.nonneg_boundedBorel f hf hfbound hf0, by
    have htotal : P.boundedBorel f hf hfbound + P.boundedBorel g hg hgbound = 1 := by
      calc
        P.boundedBorel f hf hfbound + P.boundedBorel g hg hgbound =
            P.boundedBorel (f + g) hsummeas hsumbound := hsum.symm
        _ = 1 := by
          let c : Unit → ℝ := fun _ => 1
          let pieces : Unit → Set Ω := fun _ => Set.univ
          have hpieces : EffectValuedMeasure.IsPartition pieces :=
            { measurable := fun _ => MeasurableSet.univ
              disjoint := by
                intro i j hij
                exact (hij (Subsingleton.elim i j)).elim
              cover := by
                apply Set.Subset.antisymm
                · exact Set.iUnion_subset fun _ => Set.subset_univ _
                · intro x _
                  exact Set.mem_iUnion.2 ⟨Unit.unit, by simp [pieces]⟩ }
          have hvalue : ∀ x, EffectValuedMeasure.simpleValue c pieces x = (f + g) x := by
            intro x
            simp [EffectValuedMeasure.simpleValue, c, pieces, g]
          rw [boundedBorel, EffectValuedMeasure.integral_eq_simpleIntegral
            hsummeas hsumbound hpieces hvalue]
          unfold EffectValuedMeasure.simpleIntegral
          simp [c, pieces]
    rw [← htotal]
    exact le_add_of_nonneg_right (P.nonneg_boundedBorel g hg hgbound hg0)⟩

/-- Coercing the bounded Borel effect forgets only its established interval bounds. -/
@[simp]
lemma coe_boundedBorelEffect (P : MeasurableProjectionResolution Ω E) (f : Ω → ℝ)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    (P.boundedBorelEffect f hf hf0 hf1 : E) =
      P.boundedBorel f hf (M := 1)
        (fun x => by rw [abs_of_nonneg (hf0 x)]; exact hf1 x) :=
  rfl

/-- The bounded Borel calculus determines a projection resolution.  It suffices to compare every
bounded measurable function because indicators recover exactly the event projections. -/
lemma ext_of_forall_boundedBorel_eq {P Q : MeasurableProjectionResolution Ω E}
    (h : ∀ (f : Ω → ℝ) (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M),
      P.boundedBorel f hf hM = Q.boundedBorel f hf hM) : P = Q := by
  apply ext
  intro s hs
  let f : Ω → ℝ := s.indicator fun _ => (1 : ℝ)
  have hf : Measurable f := measurable_const.indicator hs
  have hbound : ∀ x, |f x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ s <;> simp [f, hx]
  have hvalue := h f hf hbound
  rw [P.boundedBorel_indicator hs, Q.boundedBorel_indicator hs] at hvalue
  exact hvalue

end BoundedBorel

end MeasurableProjectionResolution

end ProbabilisticTheory
