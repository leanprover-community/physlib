/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Relativity.Causality.CausallyFollows
public import Physlib.SpaceAndTime.SpaceTime.Basic
public import PhyslibAlpha.Mathematics.Order.CausalRelation
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Data.Nat.Choose.Multinomial

/-!

# Light cones in time and space

Causal future and past of sets in time and space and in Minkowski spacetime.

## i. Overview

Causal future and past of sets in time and space and in Minkowski spacetime. Causal futures of
compact sets are closed and causal diamonds are compact.

## ii. Key results

- `causalFuture` : The causal future of a set of spacetime points, in units where the speed of light
  is `1`.
- `causalPast` : The causal past of a set of spacetime points.
- `precedes_iff_time_space` : In any speed-of-light units the existing geometric causal relation has
  the familiar elapsed-time and spatial-distance characterization.
- `causallyFollows_iff_norm` : The existing Lorentzian causal order is equivalently the spatial norm
  bounded by elapsed Lorentz time.

## iii. Table of contents

- A. Minkowski causal geometry for Green operators
- B. Causal support of the retarded solution

## iv. References

None.

## A. Minkowski causal geometry for Green operators

Lemmas: `causallyFollows_iff_displacement`, `causallyFollows_iff_norm`, `norm_space_eq_spatialPart`,
`precedes_iff_time_space`, `isClosed_causalFuture_zero`, `causalFuture_eq_add`,
`isClosed_causalFuture`, `causalPast_eq_add_neg`, `isClosed_causalPast`,
`component_bound_of_causalDiamond` and more.

## B. Causal support of the retarded solution

- `causalFuture` : The causal future of a set of spacetime points, in units where the speed of light
  is `1`.
- `causalPast` : The causal past of a set of spacetime points.

Lemmas: `isClosed_causalFuture`.

-/

@[expose] public section

noncomputable section

open scoped Pointwise
open CausalRelation Lorentz.Vector Topology TopologicalSpace

namespace Minkowski

section
variable {d : ℕ}

/-- Causal precedence depends only on the displacement between events. -/
lemma causallyFollows_iff_displacement (p q : SpaceTime d) :
    causallyFollows p q ↔ causallyFollows 0 (q - p) := by
  simp only [causallyFollows, interiorFutureLightCone, futureLightConeBoundary,
    Set.mem_ofPred_eq, sub_zero]

/-- The existing Lorentzian causal order is equivalently the spatial norm bounded by elapsed
Lorentz time. Nonnegative elapsed time follows from this inequality. -/
lemma causallyFollows_iff_norm (p q : SpaceTime d) :
    causallyFollows p q ↔ ‖(q - p).spatialPart‖ ≤ (q - p).timeComponent := by
  rw [causallyFollows_iff_displacement]
  constructor
  · exact norm_spatialPart_le_timeComponent_of_causallyFollows
  · intro h
    apply causallyFollows_zero_iff.mpr
    have ht : 0 ≤ (q - p).timeComponent := (norm_nonneg _).trans h
    refine ⟨?_, ht⟩
    rw [minkowskiProduct_self_eq_sq_sub]
    nlinarith [norm_nonneg (q - p).spatialPart]

/-- Minkowski causal geometry reuses the existing Lorentzian future relation. -/
def causalRelation (d : ℕ) : CausalRelation (SpaceTime d) where
  Precedes := causallyFollows
  refl p := by
    apply (causallyFollows_iff_norm p p).mpr
    rw [sub_self]
    change ‖(0 : EuclideanSpace ℝ (Fin d))‖ ≤ (0 : ℝ)
    simp
  trans := by
    intro p q r hpq hqr
    apply (causallyFollows_iff_displacement p r).mpr
    have h := causallyFollows_zero_add_of_causallyFollows
      (causallyFollows_zero_sub hpq) (causallyFollows_zero_sub hqr)
    have heq : q - p + (r - q) = r - p := by abel
    rwa [heq] at h

/-- Physlib's physical-space norm agrees with the Euclidean norm of the Lorentz spatial part. -/
lemma norm_space_eq_spatialPart (p : SpaceTime d) : ‖p.space‖ = ‖p.spatialPart‖ := by
  rw [Space.norm_eq, EuclideanSpace.norm_eq]
  simp only [SpaceTime.space, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    Real.norm_eq_abs, sq_abs]

/-- In any speed-of-light units the existing geometric causal relation has the familiar
elapsed-time and spatial-distance characterization. This is an application representation. -/
lemma precedes_iff_time_space (c : SpeedOfLight) (p q : SpaceTime d) :
    (causalRelation d).Precedes p q ↔
      (p.time c).val ≤ (q.time c).val ∧
        ‖q.space - p.space‖ ≤ (c : ℝ) * ((q.time c).val - (p.time c).val) := by
  have ht : (c : ℝ) * ((q.time c).val - (p.time c).val) = (q - p).timeComponent := by
    change (c : ℝ) * (q (Sum.inl 0) / c - p (Sum.inl 0) / c) =
      q (Sum.inl 0) - p (Sum.inl 0)
    field_simp
  have htle : (p.time c).val ≤ (q.time c).val ↔ 0 ≤ (q - p).timeComponent := by
    change p (Sum.inl 0) / c ≤ q (Sum.inl 0) / c ↔
      0 ≤ q (Sum.inl 0) - p (Sum.inl 0)
    rw [div_le_div_iff_of_pos_right c.val_pos, sub_nonneg]
  have hs : ‖q.space - p.space‖ = ‖(q - p).spatialPart‖ := by
    rw [← map_sub, norm_space_eq_spatialPart]
  change causallyFollows p q ↔ _
  rw [causallyFollows_iff_norm, hs, ht, htle]
  exact ⟨fun h => ⟨(norm_nonneg _).trans h, h⟩, fun h => h.2⟩

/-- The future causal cone at the origin is closed. -/
lemma isClosed_causalFuture_zero : IsClosed ((causalRelation d).causalFuture {0}) := by
  have heq : (causalRelation d).causalFuture {0} =
      {q : SpaceTime d | ‖spatialCLM d q‖ ≤ temporalCLM d q} := by
    ext q
    simp only [causalFuture, causalRelation, Set.mem_ofPred_eq,
      Set.mem_singleton_iff, exists_eq_left, causallyFollows_iff_norm, sub_zero]
    rfl
  rw [heq]
  exact isClosed_le (spatialCLM d).continuous.norm (temporalCLM d).continuous

/-- Futures are translations of the existing future cone, combined over the source set. -/
lemma causalFuture_eq_add (K : Set (SpaceTime d)) :
    (causalRelation d).causalFuture K = K + (causalRelation d).causalFuture {0} := by
  ext q
  constructor
  · rintro ⟨p, hp, hpq⟩
    refine ⟨p, hp, q - p, ⟨0, rfl, causallyFollows_zero_sub hpq⟩, ?_⟩
    abel_nf
  · rintro ⟨p, hp, v, ⟨z, hz, hzv⟩, rfl⟩
    have hz0 : z = 0 := hz
    subst z
    change causallyFollows 0 v at hzv
    refine ⟨p, hp, ?_⟩
    apply (causallyFollows_iff_displacement _ _).mpr
    simpa only [add_sub_cancel_left] using hzv

/-- Causal futures of compact source sets are closed. -/
lemma isClosed_causalFuture {K : Set (SpaceTime d)} (hK : IsCompact K) :
    IsClosed ((causalRelation d).causalFuture K) := by
  rw [causalFuture_eq_add]
  exact isClosed_causalFuture_zero.add_left_of_isCompact hK

/-- Causal pasts are translations of the negated future cone. -/
lemma causalPast_eq_add_neg (K : Set (SpaceTime d)) :
    (causalRelation d).causalPast K = K + -((causalRelation d).causalFuture {0}) := by
  ext q
  constructor
  · rintro ⟨p, hp, hqp⟩
    refine ⟨p, hp, q - p, ?_, ?_⟩
    · change -(q - p) ∈ (causalRelation d).causalFuture {0}
      refine ⟨0, rfl, ?_⟩
      have heq : -(q - p) = p - q := neg_sub _ _
      rw [heq]
      exact causallyFollows_zero_sub hqp
    · abel_nf
  · rintro ⟨p, hp, v, hv, rfl⟩
    change -v ∈ (causalRelation d).causalFuture {0} at hv
    obtain ⟨z, hz, hzv⟩ := hv
    have hz0 : z = 0 := hz
    subst z
    change causallyFollows 0 (-v) at hzv
    refine ⟨p, hp, ?_⟩
    apply (causallyFollows_iff_displacement _ _).mpr
    simpa only [sub_add_cancel_left] using hzv

/-- Causal pasts of compact source sets are closed. -/
lemma isClosed_causalPast {K : Set (SpaceTime d)} (hK : IsCompact K) :
    IsClosed ((causalRelation d).causalPast K) := by
  rw [causalPast_eq_add_neg]
  exact isClosed_causalFuture_zero.neg.add_left_of_isCompact hK

/-- Every component in a causal diamond is bounded by the bounds on its endpoint sets. -/
lemma component_bound_of_causalDiamond {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {k x l : SpaceTime d} (hk : ‖k‖ ≤ A) (hl : ‖l‖ ≤ B)
    (hkx : (causalRelation d).Precedes k x) (hxl : (causalRelation d).Precedes x l)
    (i : Fin 1 ⊕ Fin d) : |x i| ≤ 2 * A + B := by
  have hleft := (causallyFollows_iff_norm k x).mp hkx
  have hright := (causallyFollows_iff_norm x l).mp hxl
  have hk0 := (abs_component_le_norm k (Sum.inl 0)).trans hk
  have hl0 := (abs_component_le_norm l (Sum.inl 0)).trans hl
  have htlo : k (Sum.inl 0) ≤ x (Sum.inl 0) := by
    change ‖(x - k).spatialPart‖ ≤ x (Sum.inl 0) - k (Sum.inl 0) at hleft
    linarith [norm_nonneg (x - k).spatialPart]
  have hthi : x (Sum.inl 0) ≤ l (Sum.inl 0) := by
    change ‖(l - x).spatialPart‖ ≤ l (Sum.inl 0) - x (Sum.inl 0) at hright
    linarith [norm_nonneg (l - x).spatialPart]
  cases i with
  | inl i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      apply abs_le.mpr
      constructor <;> linarith [(abs_le.mp hk0).1, (abs_le.mp hl0).2]
  | inr i =>
      have hd : |x (Sum.inr i) - k (Sum.inr i)| ≤ ‖(x - k).spatialPart‖ := by
        simpa only [Real.norm_eq_abs, Lorentz.Vector.apply_sub] using PiLp.norm_apply_le (x -
          k).spatialPart i
      have hki := (abs_component_le_norm k (Sum.inr i)).trans hk
      change ‖(x - k).spatialPart‖ ≤ x (Sum.inl 0) - k (Sum.inl 0) at hleft
      calc
        |x (Sum.inr i)| = |(x (Sum.inr i) - k (Sum.inr i)) + k (Sum.inr i)| := by
          rw [sub_add_cancel]
        _ ≤ |x (Sum.inr i) - k (Sum.inr i)| + |k (Sum.inr i)| := abs_add_le _ _
        _ ≤ 2 * A + B := by linarith [(abs_le.mp hk0).1, (abs_le.mp hl0).2]

/-- Minkowski causal diamonds between compact endpoint sets are compact in every spatial
dimension. -/
lemma hasCompactCausalDiamonds (d : ℕ) : (causalRelation d).HasCompactCausalDiamonds := by
  intro K L hK hL
  obtain ⟨A, hA, hKA⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨B, hB, hLB⟩ := hL.isBounded.exists_pos_norm_le
  let R := 2 * A + B
  have hc : IsCompact ((equivPi d).symm ''
      Metric.closedBall (0 : Fin 1 ⊕ Fin d → ℝ) R) :=
    (isCompact_closedBall _ _).image (equivPi d).symm.continuous
  apply hc.of_isClosed_subset ((isClosed_causalFuture hK).inter (isClosed_causalPast hL))
  intro x hx
  obtain ⟨k, hk, hkx⟩ := hx.1
  obtain ⟨l, hl, hxl⟩ := hx.2
  refine ⟨equivPi d x, ?_, (equivPi d).symm_apply_apply x⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by dsimp [R]; positivity)).mpr
  intro i
  change |x i| ≤ R
  exact component_bound_of_causalDiamond hA.le hB.le (hKA k hk) (hLB l hl) hkx hxl i

/-- Each event has a compact future observation bound whose causal past is a neighborhood. -/
lemma local_causalPast_bound (p : SpaceTime d) :
    ∃ K : Set (SpaceTime d), IsCompact K ∧ (causalRelation d).causalPast K ∈ 𝓝 p := by
  let q := p + basis (Sum.inl 0)
  have hsp : (q - p).spatialPart = 0 := by
    change (p + basis (Sum.inl 0) - p).spatialPart = 0
    rw [add_sub_cancel_left]
    exact spatialCLM_basis_sum_inl
  have ht : (q - p).timeComponent = 1 := by
    change (p + basis (Sum.inl 0) - p).timeComponent = 1
    rw [add_sub_cancel_left]
    exact timeComponent_basis_sum_inl
  have hopen : IsOpen {x : SpaceTime d | ‖(q - x).spatialPart‖ < (q - x).timeComponent} :=
    isOpen_lt ((spatialCLM d).continuous.comp (continuous_const.sub continuous_id)).norm
      ((temporalCLM d).continuous.comp (continuous_const.sub continuous_id))
  have hp : p ∈ {x : SpaceTime d | ‖(q - x).spatialPart‖ < (q - x).timeComponent} := by
    simp only [Set.mem_ofPred_eq, hsp, ht, norm_zero, zero_lt_one]
  refine ⟨{q}, isCompact_singleton, Filter.mem_of_superset (hopen.mem_nhds hp) ?_⟩
  intro x hx
  exact ⟨q, rfl, (causallyFollows_iff_norm x q).mpr hx.le⟩

/-- Each event has a compact past observation bound whose causal future is a neighborhood. -/
lemma local_causalFuture_bound (p : SpaceTime d) :
    ∃ K : Set (SpaceTime d), IsCompact K ∧ (causalRelation d).causalFuture K ∈ 𝓝 p := by
  let q := p - basis (Sum.inl 0)
  have hsp : (p - q).spatialPart = 0 := by
    change (p - (p - basis (Sum.inl 0))).spatialPart = 0
    rw [sub_sub_cancel]
    exact spatialCLM_basis_sum_inl
  have ht : (p - q).timeComponent = 1 := by
    change (p - (p - basis (Sum.inl 0))).timeComponent = 1
    rw [sub_sub_cancel]
    exact timeComponent_basis_sum_inl
  have hopen : IsOpen {x : SpaceTime d | ‖(x - q).spatialPart‖ < (x - q).timeComponent} :=
    isOpen_lt ((spatialCLM d).continuous.comp (continuous_id.sub continuous_const)).norm
      ((temporalCLM d).continuous.comp (continuous_id.sub continuous_const))
  have hp : p ∈ {x : SpaceTime d | ‖(x - q).spatialPart‖ < (x - q).timeComponent} := by
    simp only [Set.mem_ofPred_eq, hsp, ht, norm_zero, zero_lt_one]
  refine ⟨{q}, isCompact_singleton, Filter.mem_of_superset (hopen.mem_nhds hp) ?_⟩
  intro x hx
  exact ⟨q, rfl, (causallyFollows_iff_norm q x).mpr hx.le⟩
end

end Minkowski

namespace TimeSpace

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]

/-- The causal future of a set of spacetime points, in units where the speed of light is `1`. -/
def causalFuture (K : Set (ℝ × E)) : Set (ℝ × E) :=
  {p | ∃ q ∈ K, ‖p.2 - q.2‖ ≤ p.1 - q.1}

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The causal future of a compact source region is closed. -/
lemma isClosed_causalFuture {K : Set (ℝ × E)} (hK : IsCompact K) :
    IsClosed (causalFuture K) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : IsClosed {w : (ℝ × E) × K | ‖w.1.2 - w.2.val.2‖ ≤ w.1.1 - w.2.val.1} := by
    apply isClosed_le <;> fun_prop
  have he : causalFuture K = Prod.fst ''
      {w : (ℝ × E) × K | ‖w.1.2 - w.2.val.2‖ ≤ w.1.1 - w.2.val.1} := by
    ext p
    constructor
    · rintro ⟨q, hq, hqp⟩
      exact ⟨(p, ⟨q, hq⟩), hqp, rfl⟩
    · rintro ⟨⟨p', q⟩, hqp, rfl⟩
      exact ⟨q.val, q.property, hqp⟩
  rw [he]
  exact isClosedMap_fst_of_compactSpace _ hc

/-- The causal past of a set of spacetime points. -/
def causalPast (K : Set (ℝ × E)) : Set (ℝ × E) :=
  {p | ∃ q ∈ K, ‖p.2 - q.2‖ ≤ q.1 - p.1}
end

end TimeSpace
