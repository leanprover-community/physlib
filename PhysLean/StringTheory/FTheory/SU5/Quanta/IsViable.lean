/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.StringTheory.FTheory.SU5.Charges.AnomalyFree
public import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.ZMod
/-!

# Viable Quanta with Yukawa

## i. Overview

We say a term of a type `Quanta` is viable
  if it satisfies the following properties:
- It has a `Hd`, `Hu` and at least one matter particle in the 5 and 10 representation.
- It has no exotic chiral particles.
- It leads to a top Yukawa coupling.
- It does not lead to a pheno constraining terms.
- It does not lead to a dangerous Yukawa coupling at one insertion of the Yukawa singlets.
- It satisfies linear anomaly cancellation.
- The charges are allowed by an `I` configuration.

We also write down the explicit set of viable quanta, and prove that this set is complete.

One can view the dependencies of this module with:

```
lake exe graph --from
  PhysLean.StringTheory.FTheory.SU5.Fluxes.Basic,PhysLean.Particles.SuperSymmetry.SU5.FieldLabels
  my_graph.pdf
```

## ii. Key results

- `Quanta.IsViable` : The proposition on a `Quanta` that it is viable.
- `Quanta.viableElems` : The multiset of viable quanta.
- `Quanta.isViable_iff_mem_viableElems` : A quanta is viable if and only if it is in the
  `Quanta.viableElems`.

## iii. Table of contents

- A. The condition for a `Quanta` to be viable
  - A.1. Simplification of the prop to use the set of viable charges `viableCharges I`
  - A.2. Further simplification of the prop to use the set of viable charges `Quanta.liftCharge`
  - A.3. Further simplification of the prop to use the anomaly free set of viable charges
- B. The multiset of viable quanta
  - B.1. Every element of the multiset is viable
  - B.2. A quanta is viable if and only if it is in the multiset
  - B.3. Every element of the multiset regenerates Yukawa at two insertions of the Yukawa singlets
  - B.4. Those quanta which satisfy the quartic anomaly cancellation condition
  - B.5. Map down to Z2

## iv. References

The key reference for the material in this module is: arXiv:1507.05961.

-/

@[expose] public section
namespace FTheory

namespace SU5

variable {I : CodimensionOneConfig}

namespace Quanta
open SuperSymmetry.SU5
open PotentialTerm ChargeSpectrum

/-!

## A. The condition for a `Quanta` to be viable

-/

/-- For a given `I : CodimensionOneConfig` the condition on a `Quanta` for it to be
  phenomenologically viable. -/
structure IsViable (x : Quanta) : Prop where
  /-- There is a `Hd`, `Hu`, 5-bar matter and 10d matter. -/
  has_all_charges : x.toCharges.IsComplete
  /-- The charges do not lead to any phenomenologically constraining terms. -/
  not_pheno_constrained : ¬ x.toCharges.IsPhenoConstrained
  /-- The charges are such that dangerous couplings in the super potential are not
    regenerated with the Yukawa terms. -/
  not_regenerate_dangerous_couplings : ¬ x.toCharges.YukawaGeneratesDangerousAtLevel 1
  /-- The charges are such that they are allowed by a configuration of sections on the
    co-dimension 1 fiber. -/
  charges_allowed_by_section_config :
    (∃ I : CodimensionOneConfig, x.toCharges ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges)
  /-- Within the 5-bar matter, there is at most one entry for each charge. -/
  no_duplicate_five_bar_charges : x.F.toCharges.Nodup
  /-- Within the 10d matter, there is at most one entry for each charge. -/
  no_duplicate_ten_charges : x.T.toCharges.Nodup
  /-- The charges permit at least one Top-Yukawa coupling. -/
  allows_top_yukawa : AllowsTerm x.toCharges topYukawa
  /-- The fluxes of the 5-bar matter fields do not lead to any exotic chiral particles. -/
  no_exotics_from_five_bar : x.F.toFluxesFive.NoExotics
  /-- There are 5-bar matter fields where both fluxes are zero (these are not
    being counted here). -/
  no_five_bar_zero_fluxes : x.F.toFluxesFive.HasNoZero
  /-- The fluxes of the 10d matter fields do not lead to any exotic chiral particles. -/
  no_exotics_from_ten : x.T.toFluxesTen.NoExotics
  /-- There are 10d matter fields where both fluxes are zero (these are not
    being counted here). -/
  no_ten_zero_fluxes : x.T.toFluxesTen.HasNoZero
  /-- The quanta satisfy the linear anomaly cancellation conditions. -/
  linear_anomalies : x.LinearAnomalyCancellation

lemma isViable_iff_def (x : Quanta) : IsViable x ↔
    x.toCharges.IsComplete ∧
    ¬ x.toCharges.IsPhenoConstrained ∧
    ¬ x.toCharges.YukawaGeneratesDangerousAtLevel 1 ∧
    (∃ I : CodimensionOneConfig, x.toCharges ∈
      ofFinset I.allowedBarFiveCharges I.allowedTenCharges) ∧
    x.F.toCharges.Nodup ∧
    x.T.toCharges.Nodup ∧
    x.toCharges.AllowsTerm topYukawa ∧
    x.F.toFluxesFive.NoExotics ∧
    x.F.toFluxesFive.HasNoZero ∧
    x.T.toFluxesTen.NoExotics ∧
    x.T.toFluxesTen.HasNoZero ∧
    x.LinearAnomalyCancellation := by
  apply Iff.intro
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-!

### A.1. Simplification of the prop to use the set of viable charges `viableCharges I`

-/

lemma isViable_iff_charges_mem_viableCharges (x : Quanta) :
    IsViable x ↔
        /- 1. Conditions just on the charges. -/
        (∃ I, x.toCharges ∈ viableCharges I) ∧
        x.F.toCharges.Nodup ∧
        x.T.toCharges.Nodup ∧
        /- 2. Conditions just on the fluxes -/
        x.F.toFluxesFive.NoExotics ∧
        x.F.toFluxesFive.HasNoZero ∧
        x.T.toFluxesTen.NoExotics ∧
        x.T.toFluxesTen.HasNoZero ∧
        /- 3. Conditions on the fluxes and the charges. -/
        x.LinearAnomalyCancellation := by
  rw [isViable_iff_def]
  conv_rhs =>
    enter [1, 1, I]
    rw [mem_viableCharges_iff']
  aesop

/-!

### A.2. Further simplification of the prop to use the set of viable charges `Quanta.liftCharge`

-/

lemma isViable_iff_charges_mem_viableCharges_mem_liftCharges (x : Quanta) :
    IsViable x ↔ (∃ I, x.toCharges ∈ viableCharges I) ∧
      x ∈ Quanta.liftCharge x.toCharges ∧
      x.LinearAnomalyCancellation := by
  rw [Quanta.mem_liftCharge_iff]
  simp [toCharges_qHd, toCharges_qHu]
  rw [FiveQuanta.mem_liftCharge_iff, TenQuanta.mem_liftCharge_iff]
  rw [isViable_iff_charges_mem_viableCharges, ← FluxesFive.noExotics_iff_mem_elemsNoExotics,
    ← FluxesTen.noExotics_iff_mem_elemsNoExotics]
  aesop

/-!

### A.3. Further simplification of the prop to use the anomaly free set of viable charges

-/

lemma isViable_iff_filter (x : Quanta) :
    IsViable x ↔ (∃ I, x.toCharges ∈ (viableCharges I).filter IsAnomalyFree) ∧
      x ∈ Quanta.liftCharge x.toCharges
      ∧ x.LinearAnomalyCancellation := by
  rw [isViable_iff_charges_mem_viableCharges_mem_liftCharges]
  simp [IsAnomalyFree]
  aesop

/-!

## B. The multiset of viable quanta

We find all the viable quanta. This can be evaluated with

```
  ((((viableCharges .same ∪ viableCharges .nearestNeighbor ∪
  viableCharges .nextToNearestNeighbor).filter IsAnomalyFree).bind
    Quanta.liftCharge).filter LinearAnomalyCancellation)
```

-/

/-- Given a `CodimensionOneConfig` the `Quanta` which satisfy the condition `IsViable`. -/
def viableElems : Multiset Quanta :=
  {⟨some 2, some (-2), {(-1, ⟨3, -2⟩), (-3, ⟨0, 2⟩)}, {(-1, ⟨3, 0⟩)}⟩,
  ⟨some 2, some (-2), {(-1, ⟨3, -2⟩), (-3, ⟨0, 2⟩)}, {(-1, ⟨3, 0⟩)}⟩,
  ⟨some 2, some (-2), {(-1, ⟨2, -2⟩), (-3, ⟨1, 2⟩)}, {(-1, ⟨3, 0⟩)}⟩,
  ⟨some 2, some (-2), {(-1, ⟨2, -2⟩), (-3, ⟨1, 2⟩)}, {(-1, ⟨3, 0⟩)}⟩,
  ⟨some 2, some (-2), {(1, ⟨3, -2⟩), (-1, ⟨0, 2⟩)}, {(-1, ⟨3, 0⟩)}⟩,
  ⟨some 2, some (-2), {(1, ⟨3, -2⟩), (-1, ⟨0, 2⟩)}, {(-1, ⟨3, 0⟩)}⟩,
  ⟨some 2, some (-2), {(1, ⟨2, -2⟩), (-1, ⟨1, 2⟩)}, {(-1, ⟨3, 0⟩)}⟩,
  ⟨some 2, some (-2), {(1, ⟨2, -2⟩), (-1, ⟨1, 2⟩)}, {(-1, ⟨3, 0⟩)}⟩,
  ⟨some (-2), some 2, {(-1, ⟨3, -2⟩), (1, ⟨0, 2⟩)}, {(1, ⟨3, 0⟩)}⟩,
  ⟨some (-2), some 2, {(-1, ⟨3, -2⟩), (1, ⟨0, 2⟩)}, {(1, ⟨3, 0⟩)}⟩,
  ⟨some (-2), some 2, {(-1, ⟨2, -2⟩), (1, ⟨1, 2⟩)}, {(1, ⟨3, 0⟩)}⟩,
  ⟨some (-2), some 2, {(-1, ⟨2, -2⟩), (1, ⟨1, 2⟩)}, {(1, ⟨3, 0⟩)}⟩,
  ⟨some (-2), some 2, {(1, ⟨3, -2⟩), (3, ⟨0, 2⟩)}, {(1, ⟨3, 0⟩)}⟩,
  ⟨some (-2), some 2, {(1, ⟨3, -2⟩), (3, ⟨0, 2⟩)}, {(1, ⟨3, 0⟩)}⟩,
  ⟨some (-2), some 2, {(1, ⟨2, -2⟩), (3, ⟨1, 2⟩)}, {(1, ⟨3, 0⟩)}⟩,
  ⟨some (-2), some 2, {(1, ⟨2, -2⟩), (3, ⟨1, 2⟩)}, {(1, ⟨3, 0⟩)}⟩,
  ⟨some (-4), some (-14), {(11, ⟨3, -2⟩), (6, ⟨0, 2⟩)}, {(-7, ⟨3, 0⟩)}⟩,
  ⟨some (-4), some (-14), {(11, ⟨3, -2⟩), (6, ⟨0, 2⟩)}, {(-7, ⟨3, 0⟩)}⟩,
  ⟨some (-4), some (-14), {(11, ⟨2, -2⟩), (6, ⟨1, 2⟩)}, {(-7, ⟨3, 0⟩)}⟩,
  ⟨some (-4), some (-14), {(11, ⟨2, -2⟩), (6, ⟨1, 2⟩)}, {(-7, ⟨3, 0⟩)}⟩,
  ⟨some 6, some (-14), {(1, ⟨3, -2⟩), (-9, ⟨0, 2⟩)}, {(-7, ⟨3, 0⟩)}⟩,
  ⟨some 6, some (-14), {(1, ⟨3, -2⟩), (-9, ⟨0, 2⟩)}, {(-7, ⟨3, 0⟩)}⟩,
  ⟨some 6, some (-14), {(1, ⟨2, -2⟩), (-9, ⟨1, 2⟩)}, {(-7, ⟨3, 0⟩)}⟩,
  ⟨some 6, some (-14), {(1, ⟨2, -2⟩), (-9, ⟨1, 2⟩)}, {(-7, ⟨3, 0⟩)}⟩,
  ⟨some 6, some (-14), {(11, ⟨3, -2⟩), (1, ⟨0, 2⟩)}, {(-7, ⟨3, 0⟩)}⟩,
  ⟨some 6, some (-14), {(11, ⟨3, -2⟩), (1, ⟨0, 2⟩)}, {(-7, ⟨3, 0⟩)}⟩,
  ⟨some 6, some (-14), {(11, ⟨2, -2⟩), (1, ⟨1, 2⟩)}, {(-7, ⟨3, 0⟩)}⟩,
  ⟨some 6, some (-14), {(11, ⟨2, -2⟩), (1, ⟨1, 2⟩)}, {(-7, ⟨3, 0⟩)}⟩,
  ⟨some (-14), some 6, {(1, ⟨3, -2⟩), (11, ⟨0, 2⟩)}, {(3, ⟨3, 0⟩)}⟩,
  ⟨some (-14), some 6, {(1, ⟨3, -2⟩), (11, ⟨0, 2⟩)}, {(3, ⟨3, 0⟩)}⟩,
  ⟨some (-14), some 6, {(1, ⟨2, -2⟩), (11, ⟨1, 2⟩)}, {(3, ⟨3, 0⟩)}⟩,
  ⟨some (-14), some 6, {(1, ⟨2, -2⟩), (11, ⟨1, 2⟩)}, {(3, ⟨3, 0⟩)}⟩,
  ⟨some 2, some 12, {(-13, ⟨3, -2⟩), (-8, ⟨0, 2⟩)}, {(6, ⟨3, 0⟩)}⟩,
  ⟨some 2, some 12, {(-13, ⟨3, -2⟩), (-8, ⟨0, 2⟩)}, {(6, ⟨3, 0⟩)}⟩,
  ⟨some 2, some 12, {(-13, ⟨2, -2⟩), (-8, ⟨1, 2⟩)}, {(6, ⟨3, 0⟩)}⟩,
  ⟨some 2, some 12, {(-13, ⟨2, -2⟩), (-8, ⟨1, 2⟩)}, {(6, ⟨3, 0⟩)}⟩}

/-!

### B.1. Every element of the multiset is viable

-/

lemma isViable_of_mem_viableElems (x : Quanta) (h : x ∈ viableElems) :
    IsViable x := by
  rw [isViable_iff_charges_mem_viableCharges_mem_liftCharges]
  revert x
  decide

/-!

### B.2. A quanta is viable if and only if it is in the multiset

-/

lemma isViable_iff_mem_viableElems (x : Quanta) :
    x.IsViable ↔ x ∈ viableElems := by
  constructor
  · intro h
    rw [isViable_iff_filter] at h
    obtain ⟨⟨I, hc⟩, hl, ha⟩ := h
    generalize x.toCharges = c at *
    revert ha
    revert x
    rw [viable_anomalyFree] at hc
    revert c
    revert I
    decide
  · exact isViable_of_mem_viableElems x

/-!

### B.3. Every element of the multiset regenerates Yukawa at two insertions of the Yukawa singlets

-/

/-- Every viable Quanta regenerates a dangerous coupling at two insertions of the Yukawa
  singlets. -/
lemma yukawaSingletsRegenerateDangerousInsertion_two_of_isViable
    (x : Quanta) (h : IsViable x) :
    (toCharges x).YukawaGeneratesDangerousAtLevel 2 := by
  rw [isViable_iff_mem_viableElems] at h
  revert x
  decide

/-!

### B.4. Those quanta which satisfy the quartic anomaly cancellation condition

-/

lemma quarticAnomalyCancellation_iff_mem_of_isViable (x : Quanta) (h : IsViable x) :
    x.QuarticAnomalyCancellation ↔ x ∈
    ({⟨some 2, some (-2), {(-1, ⟨1, 2⟩), (1, ⟨2, -2⟩)}, {(-1, ⟨3, 0⟩)}⟩,
    ⟨some 2, some (-2), {(-1, ⟨0, 2⟩), (1, ⟨3, -2⟩)}, {(-1, ⟨3, 0⟩)}⟩,
    ⟨some (-2), some 2, {(-1, ⟨2, -2⟩), (1, ⟨1, 2⟩)}, {(1, ⟨3, 0⟩)}⟩,
    ⟨some (-2), some 2, {(-1, ⟨3, -2⟩), (1, ⟨0, 2⟩)}, {(1, ⟨3, 0⟩)}⟩,
    ⟨some 6, some (-14), {(-9, ⟨1, 2⟩), (1, ⟨2, -2⟩)}, {(-7, ⟨3, 0⟩)}⟩,
    ⟨some 6, some (-14), {(-9, ⟨0, 2⟩), (1, ⟨3, -2⟩)}, {(-7, ⟨3, 0⟩)}⟩} : Finset Quanta) := by
  rw [isViable_iff_mem_viableElems] at h
  revert x
  decide

/-!

### B.5. Map down to Z2

-/

lemma map_to_Z2_of_isViable (x : Quanta ℤ) (h : IsViable x) :
    x.toCharges.map (Int.castAddHom (ZMod 2)) ∈
    ({⟨some 0, some 0, {1}, {1}⟩, ⟨some 0, some 0, {0,1}, {1}⟩, ⟨some 0, some 0, {0,1}, {0}⟩} :
    Finset (ChargeSpectrum (ZMod 2))) := by
  rw [isViable_iff_mem_viableElems] at h
  revert x
  decide

end Quanta

end SU5

end FTheory
