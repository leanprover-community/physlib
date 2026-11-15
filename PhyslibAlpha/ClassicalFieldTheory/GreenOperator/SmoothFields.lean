/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GreenOperator.Localization
public import PhyslibAlpha.Relativity.Causality.LightCone
public import PhyslibAlpha.SpaceAndTime.SpaceTime.Fields

/-!

# Smooth spacetime fields as Green operator input

## i. Overview

Smooth fields on spacetime admit past and future localization and temporal cutoffs.

## ii. Key results

- `pastLocalization` : Retarded localization for every admissible field space with local gluing and
  bump stability.
- `futureLocalization` : Advanced localization uses the same field hypotheses and the reversed
  verified causal geometry.
- `smoothPastLocalization` : All past-compact smooth fields admit the compact truncations required
  by the general theory.
- `smoothFutureLocalization` : The same analytic field class supplies advanced localization after
  causal reversal.

## iii. Table of contents

- A. Localization of admissible fields in Minkowski spacetime
- B. Localization of smooth spacetime fields
- C. Temporal cutoffs of spacelike-compact smooth fields

## iv. References

None.

## A. Localization of admissible fields in Minkowski spacetime

- `pastLocalization` : Retarded localization for every admissible field space with local gluing and
  bump stability.
- `futureLocalization` : Advanced localization uses the same field hypotheses and the reversed
  verified causal geometry.

## B. Localization of smooth spacetime fields

- `smoothPastLocalization` : All past-compact smooth fields admit the compact truncations required
  by the general theory.
- `smoothFutureLocalization` : The same analytic field class supplies advanced localization after
  causal reversal.

Lemmas: `smoothFields_bumpStable`.

## C. Temporal cutoffs of spacelike-compact smooth fields

Lemmas: `isCompact_causalPast_inter`, `isCompact_causalFuture_inter`, `tsupport_cutoff_subset`,
`tsupport_cutoff_sub_subset`, `smoothHasCausalCutoffs`.

-/

@[expose] public section

noncomputable section

open scoped ContDiff
open CausalRelation Minkowski Lorentz.Vector Topology

namespace GreenOperator.Minkowski

section
variable {d : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V] {S : Submodule ℝ (SpaceTime d → V)} {P :
    LocalOperator S}

/-- Retarded localization for every admissible field space with local gluing and bump stability. -/
def pastLocalization (hlocal : IsLocalFieldSpace S)
    (hmul : ∀ (b : ContDiffBump (0 : SpaceTime d)) (u : S), (fun x => b x • u.val x) ∈ S) :
    PastLocalization (causalRelation d) P :=
  PastLocalization.ofBumpFunctions hmul hlocal
    (fun _ hK => isClosed_causalFuture hK) local_causalPast_bound

/-- Advanced localization uses the same field hypotheses and the reversed verified causal
geometry. -/
def futureLocalization (hlocal : IsLocalFieldSpace S)
    (hmul : ∀ (b : ContDiffBump (0 : SpaceTime d)) (u : S), (fun x => b x • u.val x) ∈ S) :
    PastLocalization (causalRelation d).reverse P :=
  PastLocalization.ofBumpFunctions hmul hlocal
    (fun _ hK => isClosed_causalPast hK) local_causalFuture_bound
end

section
variable {d : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Smooth scalar bump multiplication preserves the smooth admissible field space. -/
lemma smoothFields_bumpStable (b : ContDiffBump (0 : SpaceTime d)) (u : smoothFields d V) :
    (fun x => b x • u.val x) ∈ smoothFields d V := by
  change ContDiff ℝ ∞ (fun x => b x • u.val x)
  exact b.contDiff.smul (smoothFields_contDiff u)

/-- All past-compact smooth fields admit the compact truncations required by the general theory. -/
def smoothPastLocalization (P : LocalOperator (smoothFields d V)) :
    PastLocalization (causalRelation d) P :=
  Minkowski.pastLocalization smoothFields_isLocal smoothFields_bumpStable

/-- The same analytic field class supplies advanced localization after causal reversal. -/
def smoothFutureLocalization (P : LocalOperator (smoothFields d V)) :
    PastLocalization (causalRelation d).reverse P :=
  Minkowski.futureLocalization smoothFields_isLocal smoothFields_bumpStable
end

section
variable {d : ℕ}

/-- The part of the causal past of a compact set with nonnegative time is compact. -/
lemma isCompact_causalPast_inter {K : Set (SpaceTime d)} (hK : IsCompact K) :
    IsCompact ((causalRelation d).causalPast K ∩ {x | 0 ≤ x.timeComponent}) := by
  obtain ⟨A, hA, hKA⟩ := hK.isBounded.exists_pos_norm_le
  have hc : IsCompact ((equivPi d).symm ''
      Metric.closedBall (0 : Fin 1 ⊕ Fin d → ℝ) (2 * A)) :=
    (isCompact_closedBall _ _).image (equivPi d).symm.continuous
  apply hc.of_isClosed_subset ((isClosed_causalPast hK).inter
    (isClosed_le continuous_const (temporalCLM d).continuous))
  rintro x ⟨⟨l, hl, hxl⟩, hx0⟩
  refine ⟨equivPi d x, ?_, (equivPi d).symm_apply_apply x⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change |x i| ≤ 2 * A
  have hright := (causallyFollows_iff_norm x l).mp hxl
  change ‖(l - x).spatialPart‖ ≤ l (Sum.inl 0) - x (Sum.inl 0) at hright
  have hx0' : 0 ≤ x (Sum.inl 0) := hx0
  have hl0 := (abs_component_le_norm l (Sum.inl 0)).trans (hKA l hl)
  have hthi : x (Sum.inl 0) ≤ l (Sum.inl 0) := by
    linarith [norm_nonneg (l - x).spatialPart]
  cases i with
  | inl i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rw [abs_le]
      constructor <;> linarith [(abs_le.mp hl0).1, (abs_le.mp hl0).2]
  | inr i =>
      have hd : |l (Sum.inr i) - x (Sum.inr i)| ≤ ‖(l - x).spatialPart‖ := by
        simpa only [Real.norm_eq_abs, Lorentz.Vector.apply_sub] using PiLp.norm_apply_le (l -
          x).spatialPart i
      have hli := (abs_component_le_norm l (Sum.inr i)).trans (hKA l hl)
      calc |x (Sum.inr i)| = |l (Sum.inr i) - (l (Sum.inr i) - x (Sum.inr i))| := by ring_nf
        _ ≤ |l (Sum.inr i)| + |l (Sum.inr i) - x (Sum.inr i)| := abs_sub _ _
        _ ≤ 2 * A := by linarith [(abs_le.mp hl0).2]

/-- The part of the causal future of a compact set with time at most one is compact. -/
lemma isCompact_causalFuture_inter {K : Set (SpaceTime d)} (hK : IsCompact K) :
    IsCompact ((causalRelation d).causalFuture K ∩ {x | x.timeComponent ≤ 1}) := by
  obtain ⟨A, hA, hKA⟩ := hK.isBounded.exists_pos_norm_le
  have hc : IsCompact ((equivPi d).symm ''
      Metric.closedBall (0 : Fin 1 ⊕ Fin d → ℝ) (2 * A + 1)) :=
    (isCompact_closedBall _ _).image (equivPi d).symm.continuous
  apply hc.of_isClosed_subset ((isClosed_causalFuture hK).inter
    (isClosed_le (temporalCLM d).continuous continuous_const))
  rintro x ⟨⟨k, hk, hkx⟩, hx1⟩
  refine ⟨equivPi d x, ?_, (equivPi d).symm_apply_apply x⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change |x i| ≤ 2 * A + 1
  have hleft := (causallyFollows_iff_norm k x).mp hkx
  change ‖(x - k).spatialPart‖ ≤ x (Sum.inl 0) - k (Sum.inl 0) at hleft
  have hx1' : x (Sum.inl 0) ≤ 1 := hx1
  have hk0 := (abs_component_le_norm k (Sum.inl 0)).trans (hKA k hk)
  have htlo : k (Sum.inl 0) ≤ x (Sum.inl 0) := by
    linarith [norm_nonneg (x - k).spatialPart]
  cases i with
  | inl i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rw [abs_le]
      constructor <;> linarith [(abs_le.mp hk0).1, (abs_le.mp hk0).2]
  | inr i =>
      have hd : |x (Sum.inr i) - k (Sum.inr i)| ≤ ‖(x - k).spatialPart‖ := by
        simpa only [Real.norm_eq_abs, Lorentz.Vector.apply_sub] using PiLp.norm_apply_le (x -
          k).spatialPart i
      have hki := (abs_component_le_norm k (Sum.inr i)).trans (hKA k hk)
      calc |x (Sum.inr i)| = |(x (Sum.inr i) - k (Sum.inr i)) + k (Sum.inr i)| := by
            rw [sub_add_cancel]
        _ ≤ |x (Sum.inr i) - k (Sum.inr i)| + |k (Sum.inr i)| := abs_add_le _ _
        _ ≤ 2 * A + 1 := by linarith [(abs_le.mp hk0).1]
end

section
variable {d : ℕ}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma tsupport_cutoff_subset (u : SpaceTime d → V) :
    tsupport (fun x : SpaceTime d => Real.smoothTransition x.timeComponent • u x) ⊆
      {x | 0 ≤ x.timeComponent} ∩ tsupport u := by
  refine Set.subset_inter ?_ (tsupport_smul_subset_right _ _)
  refine (tsupport_smul_subset_left _ _).trans ?_
  refine closure_minimal (fun x hx => ?_) (isClosed_le continuous_const (temporalCLM d).continuous)
  by_contra h
  exact hx (Real.smoothTransition.zero_of_nonpos (not_le.1 h).le)

lemma tsupport_cutoff_sub_subset (u : SpaceTime d → V) :
    tsupport (fun x : SpaceTime d => (Real.smoothTransition x.timeComponent - 1) • u x) ⊆
      {x | x.timeComponent ≤ 1} ∩ tsupport u := by
  refine Set.subset_inter ?_ (tsupport_smul_subset_right _ _)
  refine (tsupport_smul_subset_left _ _).trans ?_
  refine closure_minimal (fun x hx => ?_) (isClosed_le (temporalCLM d).continuous continuous_const)
  by_contra h
  exact hx (by simp only [Real.smoothTransition.one_of_one_le (not_le.1 h).le, sub_self])

/-- Every smooth field space has the temporal cutoff splitting of spacelike-compact fields. -/
lemma smoothHasCausalCutoffs (P : LocalOperator (smoothFields d V)) :
    P.HasCausalCutoffs (causalRelation d) := by
  intro u
  obtain ⟨K, hK, hu⟩ := u.property
  set χ : SpaceTime d → ℝ := fun x => Real.smoothTransition x.timeComponent with hχdef
  have hχ : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp (temporalCLM d).contDiff
  have hud := smoothFields_contDiff u.val
  refine ⟨⟨⟨fun x => χ x • u.val.val x, hχ.smul hud⟩,
      K ∪ ((causalRelation d).causalPast K ∩ {x | 0 ≤ x.timeComponent}),
      hK.union (isCompact_causalPast_inter hK), ?_⟩,
    ⟨⟨fun x => (χ x - 1) • u.val.val x, (hχ.sub contDiff_const).smul hud⟩,
      K ∪ ((causalRelation d).causalFuture K ∩ {x | x.timeComponent ≤ 1}),
      hK.union (isCompact_causalFuture_inter hK), ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨h0, hxu⟩ := tsupport_cutoff_subset u.val.val hx
    rcases hu hxu with hf | hp
    · exact (causalRelation d).causalFuture_mono Set.subset_union_left hf
    · exact (causalRelation d).causalFuture_mono Set.subset_union_right
        ((causalRelation d).subset_causalFuture ⟨hp, h0⟩)
  · intro x hx
    obtain ⟨h1, hxu⟩ := tsupport_cutoff_sub_subset u.val.val hx
    rcases hu hxu with hf | hp
    · exact (causalRelation d).reverse.causalFuture_mono Set.subset_union_right
        ((causalRelation d).reverse.subset_causalFuture ⟨hf, h1⟩)
    · exact (causalRelation d).reverse.causalFuture_mono Set.subset_union_left hp
  · refine Subtype.ext (funext fun x => ?_)
    change χ x • u.val.val x - (χ x - 1) • u.val.val x = u.val.val x
    rw [sub_smul, one_smul]; abel
end

end GreenOperator.Minkowski
