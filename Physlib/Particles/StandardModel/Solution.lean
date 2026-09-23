/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Particles.StandardModel.Challenge
public import Physlib.Particles.StandardModel.GaugeGroup.MaurerCartan.Freeness
/-!

# The challenges and the existing theorems

## i. Overview

How the challenges of `Physlib.Particles.StandardModel.Challenge` relate to the theorems
already proved in this folder. The existing proofs live on the hand-built field datum
`StandardModel.fieldData` and its jet algebra `JetAlgebra := fieldData.LocalFieldAlgebra`;
the challenges live on the card's datum `StandardModel.Model.fieldData`. The bridge has
two halves.

**First half, proved here.** Given a datum `T'` over the card's gauge data and an
isomorphism `e` of the two local field algebras respecting the jet gauge action, the
Lorentz action and the mass-weight scaling, each classification challenge is equivalent to
the same statement on `T'`, with the Lagrangian terms carried across by `e`. This is the
generic `GaugeFieldData.invariantsLE_map`. The datum meant is the hand-built one,
`StandardModel.fieldData`, whose gauge data is the card's by definition; it is kept as a
parameter here because unifying the two spellings of the gauge-data types inside `e` is
too expensive for the elaborator. The isomorphism `e` itself is the species-wise
identification of the card's target spaces with the hand-built ones (the identity for the
lepton doublet, `valLinEquiv` for the other species) assembled through the universal
property of the local field algebra; it is not yet constructed.

**Second half, not yet buildable.** On the hand-built datum the generic notions coincide
with the ones the existing theorems use: `StandardModel.fieldData.massWeightSubmoduleLE`
with `JetAlgebra.massWeightSubmoduleLE` (defined through `JetAlgebra.massWeightPoly`),
`StandardModel.fieldData.repJet` with `JetAlgebra.repJetGaugeGroupI`,
`StandardModel.fieldData.repLorentzGroup` with `JetAlgebra.repLorentzGroup`, and `e` of the
Higgs mass term with the generator of `isHiggsSector.dotSpan 0 0`. With these, the
challenge at mass weight four is
`CovAlgebraRealization.mem_massWeightSubmodule_four_sup_and_gauge_lorentz_invariant_iff_higgsMass`
for the identity realization and `S = ⊥`, the one at mass weight seven follows from
`mem_massWeightSubmodule_sup_and_gauge_lorentz_invariant_iff` with `standardModelSpan_eq_bot`,
and the sector challenges from the sector files. These identifications cannot be stated
here until `JetAlgebra/SectorEquiv/Basic.lean`, which `JetAlgebra/Basic.lean` imports,
builds again.

**Freeness** needs no bridge: the gauge data of the card is the hand-built one by
definition, so `instFreeLocalGaugeData` proves `gaugeData_free` outright. The centre
challenge is stated on the card's species and is proved by computing the matrix of each
charge tuple at a constant jet; it does not go through the hand-built species files.

## ii. Key results

- `StandardModel.Model.invariantsLE_four_iff`, `invariantsLE_seven_iff`,
  `scalarSector_invariantsLE_eight_iff`, `fermionSector_invariantsLE_eight_iff`,
  `gaugeSector_invariantsLE_seven_iff` : each classification challenge is equivalent to
  its form on another datum over the card's gauge data, given the isomorphism.
- `StandardModel.Model.gaugeData_free_of_hand_built` : the freeness challenge, from the
  hand-built proof.

-/

@[expose] public section

set_option maxHeartbeats 2000000

open LocalGaugeData GaugeFieldData Matrix MatrixGroups

namespace StandardModel

namespace Model

/-- The Higgs mass term `H† H` of the card. -/
local macro "higgsMass" : term =>
  `(fieldData.bosonNormSq ⟨⟨.H, by decide⟩, ⟨0, by decide⟩⟩ higgs.basis)

/-!

## A. The classification challenges, transported to the hand-built datum

-/

section Transport

variable {T' : GaugeFieldData gaugeData}
  (e : fieldData.LocalFieldAlgebra ≃ₐ[ℂ] T'.LocalFieldAlgebra)
  (hjet : ∀ (U : Factors.G gauge) x, e (fieldData.repJet U x) = T'.repJet U (e x))
  (hlor : ∀ (Λ : SL(2,ℂ)) x, e (fieldData.repLorentzGroup Λ x) = T'.repLorentzGroup Λ (e x))
  (hscale : ∀ (c : ℝ) x, e (fieldData.massWeightScale c x) = T'.massWeightScale c (e x))

include hjet hlor hscale in
/-- Equality of a transported submodule with a transported right-hand side reduces to
  equality before transport. -/
lemma map_eq_map_iff (p q : Submodule ℂ fieldData.LocalFieldAlgebra) :
    p.map (e : fieldData.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra)
        = q.map (e : fieldData.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra)
      ↔ p = q :=
  (Submodule.map_injective_of_injective (f := (e : fieldData.LocalFieldAlgebra →ₗ[ℂ]
    T'.LocalFieldAlgebra)) e.injective).eq_iff

/-- The span of the constant term and a term is carried onto the span of the constant term
  and the transported term. -/
lemma map_one_sup_span (x : fieldData.LocalFieldAlgebra) :
    (ℂ ∙ (1 : fieldData.LocalFieldAlgebra) ⊔ ℂ ∙ x).map
        (e : fieldData.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra)
      = ℂ ∙ (1 : T'.LocalFieldAlgebra) ⊔ ℂ ∙ e x := by
  simp only [Submodule.map_sup, Submodule.map_span, Set.image_singleton,
    AlgEquiv.toLinearMap_apply, map_one]

include hjet hlor hscale in
/-- **The challenge at mass weight four, on another datum**: given the isomorphism,
  it is equivalent to the same statement with the Higgs mass term carried across. -/
theorem invariantsLE_four_iff :
    (∀ x : fieldData.LocalFieldAlgebra,
      (x ∈ fieldData.massWeightSubmoduleLE 4
          ∧ (∀ U : Factors.G gauge, fieldData.repJet U x = x)
          ∧ ∀ Λ : SL(2,ℂ), fieldData.repLorentzGroup Λ x = x)
        ↔ x ∈ ℂ ∙ (1 : fieldData.LocalFieldAlgebra) ⊔ ℂ ∙ higgsMass)
      ↔ ∀ y : T'.LocalFieldAlgebra,
        (y ∈ T'.massWeightSubmoduleLE 4 ∧ (∀ U : Factors.G gauge, T'.repJet U y = y)
            ∧ ∀ Λ : SL(2,ℂ), T'.repLorentzGroup Λ y = y)
          ↔ y ∈ ℂ ∙ (1 : T'.LocalFieldAlgebra) ⊔ ℂ ∙ e higgsMass := by
  rw [← invariantsLE_eq_iff, ← invariantsLE_eq_iff]
  have hmap := invariantsLE_map e hjet hlor hscale 4
  have hspan := map_one_sup_span e higgsMass
  exact ⟨fun h => hmap.symm.trans ((congrArg (Submodule.map _) h).trans hspan),
    fun h => (map_eq_map_iff e hjet hlor hscale _ _).1 (hmap.trans (h.trans hspan.symm))⟩

include hjet hlor hscale in
/-- **The challenge at mass weight seven, on the hand-built datum.** -/
theorem invariantsLE_seven_iff :
    (∀ x : fieldData.LocalFieldAlgebra,
      (x ∈ fieldData.massWeightSubmoduleLE 7
          ∧ (∀ U : Factors.G gauge, fieldData.repJet U x = x)
          ∧ ∀ Λ : SL(2,ℂ), fieldData.repLorentzGroup Λ x = x)
        ↔ x ∈ ℂ ∙ (1 : fieldData.LocalFieldAlgebra) ⊔ ℂ ∙ higgsMass)
      ↔ ∀ y : T'.LocalFieldAlgebra,
        (y ∈ T'.massWeightSubmoduleLE 7 ∧ (∀ U : Factors.G gauge, T'.repJet U y = y)
            ∧ ∀ Λ : SL(2,ℂ), T'.repLorentzGroup Λ y = y)
          ↔ y ∈ ℂ ∙ (1 : T'.LocalFieldAlgebra) ⊔ ℂ ∙ e higgsMass := by
  rw [← invariantsLE_eq_iff, ← invariantsLE_eq_iff]
  have hmap := invariantsLE_map e hjet hlor hscale 7
  have hspan := map_one_sup_span e higgsMass
  exact ⟨fun h => hmap.symm.trans ((congrArg (Submodule.map _) h).trans hspan),
    fun h => (map_eq_map_iff e hjet hlor hscale _ _).1 (hmap.trans (h.trans hspan.symm))⟩

include hjet hlor hscale in
/-- **The scalar-sector challenge, on another datum**: given that the isomorphism
  also carries the scalar sector onto the scalar sector. -/
theorem scalarSector_invariantsLE_eight_iff
    (hsec : (fieldData.SectorAlgebra {.scalar}).toSubmodule.map
        (e : fieldData.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra)
      = (T'.SectorAlgebra {.scalar}).toSubmodule) :
    (∀ x : fieldData.LocalFieldAlgebra,
      (x ∈ fieldData.massWeightSubmoduleLE 8 ∧ x ∈ fieldData.SectorAlgebra {.scalar}
          ∧ (∀ U : Factors.G gauge, fieldData.repJet U x = x)
          ∧ ∀ Λ : SL(2,ℂ), fieldData.repLorentzGroup Λ x = x)
        ↔ x ∈ ℂ ∙ (1 : fieldData.LocalFieldAlgebra) ⊔ ℂ ∙ higgsMass
            ⊔ ℂ ∙ (higgsMass * higgsMass))
      ↔ ∀ y : T'.LocalFieldAlgebra,
        (y ∈ T'.massWeightSubmoduleLE 8 ∧ y ∈ T'.SectorAlgebra {.scalar}
            ∧ (∀ U : Factors.G gauge, T'.repJet U y = y)
            ∧ ∀ Λ : SL(2,ℂ), T'.repLorentzGroup Λ y = y)
          ↔ y ∈ ℂ ∙ (1 : T'.LocalFieldAlgebra) ⊔ ℂ ∙ e higgsMass
              ⊔ ℂ ∙ (e higgsMass * e higgsMass) := by
  simp only [← Subalgebra.mem_toSubmodule]
  rw [← invariantsLE_inf_eq_iff, ← invariantsLE_inf_eq_iff]
  have hinj : Function.Injective
      (e : fieldData.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra) :=
    e.injective
  have hmap : (fieldData.invariantsLE 8 ⊓ (fieldData.SectorAlgebra {.scalar}).toSubmodule).map
        (e : fieldData.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra)
      = T'.invariantsLE 8
          ⊓ (T'.SectorAlgebra {.scalar}).toSubmodule :=
    (Submodule.map_inf _ hinj).trans
      (congrArg₂ (· ⊓ ·) (invariantsLE_map e hjet hlor hscale 8) hsec)
  have hspan : (ℂ ∙ (1 : fieldData.LocalFieldAlgebra) ⊔ ℂ ∙ higgsMass
        ⊔ ℂ ∙ (higgsMass * higgsMass)).map
          (e : fieldData.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra)
      = ℂ ∙ (1 : T'.LocalFieldAlgebra) ⊔ ℂ ∙ e higgsMass
          ⊔ ℂ ∙ (e higgsMass * e higgsMass) := by
    simp only [Submodule.map_sup, Submodule.map_span, Set.image_singleton,
      AlgEquiv.toLinearMap_apply, map_one, map_mul]
  exact ⟨fun h => hmap.symm.trans ((congrArg (Submodule.map _) h).trans hspan),
    fun h => (map_eq_map_iff e hjet hlor hscale _ _).1 (hmap.trans (h.trans hspan.symm))⟩

include hjet hlor hscale in
/-- **The fermion-sector challenge, on the hand-built datum.** -/
theorem fermionSector_invariantsLE_eight_iff
    (hsec : (fieldData.SectorAlgebra {.fermion}).toSubmodule.map
        (e : fieldData.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra)
      = (T'.SectorAlgebra {.fermion}).toSubmodule) :
    (∀ x : fieldData.LocalFieldAlgebra,
      (x ∈ fieldData.massWeightSubmoduleLE 8 ∧ x ∈ fieldData.SectorAlgebra {.fermion}
          ∧ (∀ U : Factors.G gauge, fieldData.repJet U x = x)
          ∧ ∀ Λ : SL(2,ℂ), fieldData.repLorentzGroup Λ x = x)
        ↔ x ∈ ℂ ∙ (1 : fieldData.LocalFieldAlgebra))
      ↔ ∀ y : T'.LocalFieldAlgebra,
        (y ∈ T'.massWeightSubmoduleLE 8 ∧ y ∈ T'.SectorAlgebra {.fermion}
            ∧ (∀ U : Factors.G gauge, T'.repJet U y = y)
            ∧ ∀ Λ : SL(2,ℂ), T'.repLorentzGroup Λ y = y)
          ↔ y ∈ ℂ ∙ (1 : T'.LocalFieldAlgebra) := by
  simp only [← Subalgebra.mem_toSubmodule]
  rw [← invariantsLE_inf_eq_iff, ← invariantsLE_inf_eq_iff]
  have hinj : Function.Injective
      (e : fieldData.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra) :=
    e.injective
  have hmap : (fieldData.invariantsLE 8 ⊓ (fieldData.SectorAlgebra {.fermion}).toSubmodule).map
        (e : fieldData.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra)
      = T'.invariantsLE 8
          ⊓ (T'.SectorAlgebra {.fermion}).toSubmodule :=
    (Submodule.map_inf _ hinj).trans
      (congrArg₂ (· ⊓ ·) (invariantsLE_map e hjet hlor hscale 8) hsec)
  have hspan : (ℂ ∙ (1 : fieldData.LocalFieldAlgebra)).map
          (e : fieldData.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra)
      = ℂ ∙ (1 : T'.LocalFieldAlgebra) := by
    simp only [Submodule.map_span, Set.image_singleton, AlgEquiv.toLinearMap_apply, map_one]
  exact ⟨fun h => hmap.symm.trans ((congrArg (Submodule.map _) h).trans hspan),
    fun h => (map_eq_map_iff e hjet hlor hscale _ _).1 (hmap.trans (h.trans hspan.symm))⟩

include hjet hlor hscale in
/-- **The gauge-sector challenge, on the hand-built datum.** -/
theorem gaugeSector_invariantsLE_seven_iff
    (hsec : (fieldData.SectorAlgebra {.gauge}).toSubmodule.map
        (e : fieldData.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra)
      = (T'.SectorAlgebra {.gauge}).toSubmodule) :
    (∀ x : fieldData.LocalFieldAlgebra,
      (x ∈ fieldData.massWeightSubmoduleLE 7 ∧ x ∈ fieldData.SectorAlgebra {.gauge}
          ∧ (∀ U : Factors.G gauge, fieldData.repJet U x = x)
          ∧ ∀ Λ : SL(2,ℂ), fieldData.repLorentzGroup Λ x = x)
        ↔ x ∈ ℂ ∙ (1 : fieldData.LocalFieldAlgebra))
      ↔ ∀ y : T'.LocalFieldAlgebra,
        (y ∈ T'.massWeightSubmoduleLE 7 ∧ y ∈ T'.SectorAlgebra {.gauge}
            ∧ (∀ U : Factors.G gauge, T'.repJet U y = y)
            ∧ ∀ Λ : SL(2,ℂ), T'.repLorentzGroup Λ y = y)
          ↔ y ∈ ℂ ∙ (1 : T'.LocalFieldAlgebra) := by
  simp only [← Subalgebra.mem_toSubmodule]
  rw [← invariantsLE_inf_eq_iff, ← invariantsLE_inf_eq_iff]
  have hinj : Function.Injective
      (e : fieldData.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra) :=
    e.injective
  have hmap : (fieldData.invariantsLE 7 ⊓ (fieldData.SectorAlgebra {.gauge}).toSubmodule).map
        (e : fieldData.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra)
      = T'.invariantsLE 7
          ⊓ (T'.SectorAlgebra {.gauge}).toSubmodule :=
    (Submodule.map_inf _ hinj).trans
      (congrArg₂ (· ⊓ ·) (invariantsLE_map e hjet hlor hscale 7) hsec)
  have hspan : (ℂ ∙ (1 : fieldData.LocalFieldAlgebra)).map
          (e : fieldData.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra)
      = ℂ ∙ (1 : T'.LocalFieldAlgebra) := by
    simp only [Submodule.map_span, Set.image_singleton, AlgEquiv.toLinearMap_apply, map_one]
  exact ⟨fun h => hmap.symm.trans ((congrArg (Submodule.map _) h).trans hspan),
    fun h => (map_eq_map_iff e hjet hlor hscale _ _).1 (hmap.trans (h.trans hspan.symm))⟩

end Transport

/-!

## B. Freeness, from the hand-built proof

-/

/-- **The freeness challenge holds**: the gauge data of the card is the hand-built local
  gauge data by definition, whose freeness is proved factor by factor in
  `GaugeGroup/MaurerCartan/Freeness.lean`. -/
theorem gaugeData_free_of_hand_built : gaugeData.Free := instFreeLocalGaugeData

end Model

end StandardModel
