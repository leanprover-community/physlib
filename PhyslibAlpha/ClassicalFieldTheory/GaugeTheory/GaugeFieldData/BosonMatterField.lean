/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeFieldData.BosonModule
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.Pi
/-!
# The bosonic matter field of a gauge theory

All the bosonic species of a gauge theory with a common mass weight, as one matter field.

## i. Overview

`GaugeFieldData.BosonModule` is the value space of all the bosons of a theory at once. This file
puts on it the structure of a single `MatterField`: the Lorentz representation, the action of the
jets of gauge transformations, the infinitesimal action of the gauge algebra and the mass weight,
all acting species by species. It is the direct sum `GlobalGaugeGroup.MatterField.pi` of the
family `T.boson`, and it is the object a physicist means by "the scalar field" of a theory: for the
Standard Model the Higgs doublet, for a two-Higgs-doublet model the pair of doublets read as one
field.

The bosons here are the matter bosons — the scalars. The gauge bosons are not a species of
`GaugeFieldData` at all, their generator space being fixed by the gauge algebra alone, so
they are not part of this assembly.

Beyond the datum, the assembly needs a shared mass weight. The construction packages the
family into one `MatterField`, which has one weight, so the family must be degenerate in mass
dimension, and the assembled field carries the common mass weight of its entries. That weight
`w` is taken as an argument together with the proof that every species has it. For a theory
whose scalars are all of the same mass dimension, the Standard Model included, this is no
restriction: every bosonic species has weight two. The common statistics comes from the datum
itself, whose field `boson_statistic` requires every bosonic species to be declared bosonic.

Assembling the species loses nothing, and this is the content of the lemmas below. Each
species includes into the bosonic matter field as a subrepresentation, of the Lorentz
group and of the gauge algebra alike, so the several multiplets can be read off the single
field again. What it does lose is the ability to record *different* mass weights, which is
exactly why `GaugeFieldData.BosonGenerators` is a direct sum of component spaces rather
than the component space of this one field.

## ii. Key results

- `GaugeFieldData.bosonMatterField` : the matter field of all the bosons of the
  theory.
- `GaugeFieldData.repJetBosonModule` : the action of the jets of gauge transformations on
  the jets of the bosonic module, needing no common mass weight.
- `GaugeFieldData.bosonMatterField_repLorentz_inclBosonValue`,
  `GaugeFieldData.bosonMatterField_repAlgebra_inclBosonValue` : each species is a
  subrepresentation of it.
- `GaugeFieldData.finrank_bosonMatterField` : its dimension is the sum of the
  dimensions of the species.

## iii. Table of contents

- A. The bosonic matter field
  - A.1. The transformation data species by species
  - A.2. The species as subrepresentations

## iv. References

* None.

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

namespace GaugeFieldData

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ} (T : GaugeFieldData G)

/-!

## A. The bosonic matter field

-/

/-- The bosonic matter field of a gauge theory, the direct sum of the bosonic
  species, valued in `T.BosonModule`, with the Lorentz group, the jets of gauge
  transformations and the gauge algebra all acting species by species. It exists only for
  a family degenerate in mass dimension, where `w` is the common mass weight of the species and
  `h` the proof that they all have it, which for the Standard Model, whose only scalar is
  the Higgs doublet, is weight two. -/
noncomputable def bosonMatterField (w : ℕ) (h : ∀ i, (T.boson i).massWeight = w) :
    G.MatterField :=
  GlobalGaugeGroup.MatterField.pi T.boson w h .bosonic T.boson_statistic

variable {T}

/-- The bosonic matter field carries the common mass weight of the species. -/
@[simp]
lemma bosonMatterField_massWeight (w : ℕ) (h : ∀ i, (T.boson i).massWeight = w) :
    (T.bosonMatterField w h).massWeight = w := rfl

/-- The bosonic matter field is bosonic, as every bosonic species is declared to be. -/
@[simp]
lemma bosonMatterField_statistic (w : ℕ) (h : ∀ i, (T.boson i).massWeight = w) :
    (T.bosonMatterField w h).statistic = .bosonic := rfl

/-!

### A.1. The transformation data species by species

-/

variable (T)

/-- The Lorentz action on the bosonic module, acting species by species. This is the
  Lorentz representation of the bosonic matter field, typed on `T.BosonModule` itself so
  that it can be spoken of without fixing a common mass weight. -/
noncomputable def repLorentzBosonModule : Representation ℂ SL(2,ℂ) T.BosonModule :=
  GlobalGaugeGroup.MatterField.repPi fun i => (T.boson i).repLorentz

variable {T}

@[simp]
lemma repLorentzBosonModule_apply (Λ : SL(2,ℂ)) (v : T.BosonModule) (i : T.BosonSpecies) :
    T.repLorentzBosonModule Λ v i = (T.boson i).repLorentz Λ (v i) := rfl

variable (T)

/-- The action of the jets of gauge transformations on the jets of the bosonic
  module, acting species by species, and typed on `T.BosonModule` itself so that it can
  be spoken of without fixing a common mass weight. -/
noncomputable def repJetBosonModule :
    Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] T.BosonModule) :=
  GlobalGaugeGroup.MatterField.repJetPi T.boson

variable {T}

/-- A bosonic species is a subrepresentation of the jet gauge action on the bosonic
  module. The projection onto its value space intertwines the two actions on the jets. -/
lemma lTensor_projBosonValue_repJetBosonModule (j : T.BosonSpecies) (U : G.gaugeJetGroup) :
    (LinearMap.lTensor SpaceTimeAlgebra (T.projBosonValue j)).comp (T.repJetBosonModule U)
      = ((T.boson j).repJet U).comp
        (LinearMap.lTensor SpaceTimeAlgebra (T.projBosonValue j)) :=
  GlobalGaugeGroup.MatterField.lTensor_proj_repJetPi T.boson j U

/-- The jet gauge action of the bosonic matter field is that of the bosonic module. -/
lemma bosonMatterField_repJet (w : ℕ) (h : ∀ i, (T.boson i).massWeight = w) :
    (T.bosonMatterField w h).repJet = T.repJetBosonModule :=
  GlobalGaugeGroup.MatterField.pi_repJet T.boson w h .bosonic T.boson_statistic

/-- The Lorentz group acts on a bosonic configuration species by species. -/
@[simp]
lemma bosonMatterField_repLorentz_apply (w : ℕ)
    (h : ∀ i, (T.boson i).massWeight = w) (Λ : SL(2,ℂ)) (v : T.BosonModule)
    (i : T.BosonSpecies) :
    (T.bosonMatterField w h).repLorentz Λ v i = (T.boson i).repLorentz Λ (v i) := rfl

/-- The gauge algebra acts on a bosonic configuration species by species. -/
lemma bosonMatterField_repAlgebra_apply (w : ℕ)
    (h : ∀ i, (T.boson i).massWeight = w) (c : G.lieSubalgebra) (v : T.BosonModule)
    (i : T.BosonSpecies) :
    (T.bosonMatterField w h).repAlgebra c v i = (T.boson i).repAlgebra c (v i) := by
  unfold bosonMatterField
  rw [GlobalGaugeGroup.MatterField.pi_repAlgebra]
  rfl

/-!

### A.2. The species as subrepresentations

-/

/-- A bosonic species is a Lorentz subrepresentation of the bosonic matter field.
  Including a value of one species and then transforming is transforming and then
  including. Assembling the species into one field therefore loses no Lorentz
  information. -/
lemma bosonMatterField_repLorentz_inclBosonValue (w : ℕ)
    (h : ∀ i, (T.boson i).massWeight = w) (Λ : SL(2,ℂ)) (i : T.BosonSpecies)
    (x : T.BosonValue i) :
    (T.bosonMatterField w h).repLorentz Λ (T.inclBosonValue i x)
      = T.inclBosonValue i ((T.boson i).repLorentz Λ x) :=
  funext fun j =>
    Pi.apply_single (fun k => (T.boson k).repLorentz Λ) (fun _ => map_zero _) i x j

/-- A bosonic species is a subrepresentation of the gauge algebra action on the
  bosonic matter field, for the same reason. The gauge algebra does not mix the
  species. -/
lemma bosonMatterField_repAlgebra_inclBosonValue (w : ℕ)
    (h : ∀ i, (T.boson i).massWeight = w) (c : G.lieSubalgebra) (i : T.BosonSpecies)
    (x : T.BosonValue i) :
    (T.bosonMatterField w h).repAlgebra c (T.inclBosonValue i x)
      = T.inclBosonValue i ((T.boson i).repAlgebra c x) :=
  funext fun j => by
    rw [bosonMatterField_repAlgebra_apply]
    exact Pi.apply_single (fun k => (T.boson k).repAlgebra c) (fun _ => map_zero _) i x j

/-- The dimension of the bosonic matter field is the sum of the dimensions of the
  species. -/
lemma finrank_bosonMatterField (w : ℕ) (h : ∀ i, (T.boson i).massWeight = w) :
    Module.finrank ℂ (T.bosonMatterField w h).V
      = ∑ i, Module.finrank ℂ (T.BosonValue i) :=
  T.finrank_bosonModule

/-- The projection of the bosonic matter field onto one species, typed as a map out of
  `(T.bosonMatterField w h).V` rather than out of `T.BosonModule`. The two are the same
  type by definition, but naming the first keeps unification from having to unfold the
  direct sum every time the projection meets the matter field. -/
noncomputable abbrev projBosonField (w : ℕ) (h : ∀ i, (T.boson i).massWeight = w)
    (i : T.BosonSpecies) : (T.bosonMatterField w h).V →ₗ[ℂ] (T.boson i).V :=
  LinearMap.proj i

end GaugeFieldData
