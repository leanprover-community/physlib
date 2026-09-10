/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeFieldData.BosonModule
public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.Pi
/-!
# The bosonic matter field of a gauge theory

## i. Overview

`GaugeFieldData.BosonModule` is the value space of all the bosons of a theory at
once. This file puts on it the structure of a single `MatterField`: the Lorentz
representation, the action of the jets of gauge transformations, the infinitesimal action
of the gauge algebra and the mass weight, all acting species by species. It is the direct
sum `MatterField.pi` of the family `T.boson`, and it is the object a physicist means by
"the scalar field" of a theory: for the Standard Model the Higgs doublet, for a
two-Higgs-doublet model the pair of doublets read as one field.

The bosons here are the matter bosons — the scalars. The gauge bosons are not a species of
`GaugeFieldData` at all, their generator space being fixed by the gauge algebra alone, so
they are not part of this assembly.

The one thing the assembly needs beyond the datum is a shared mass weight. A `MatterField`
carries a single weight — that is what makes the mass-weight grading of its field algebra
well defined — so the family must be degenerate in mass dimension, and the common weight
`w` is taken as an argument together with the proof that every species has it. For a
theory whose scalars are all of the same mass dimension, the Standard Model included, this
is no restriction: every bosonic species has weight two.

Assembling the species loses nothing, and this is the content of the lemmas below: each
species includes into the bosonic matter field as a subrepresentation, of the Lorentz
group and of the gauge algebra alike, so the several multiplets can be read off the single
field again. What it does lose is the ability to record *different* mass weights, which is
exactly why `GaugeFieldData.BosonGenerators` is a direct sum of component spaces rather
than the component space of this one field.

## ii. Key results

- `GaugeFieldData.bosonMatterField` : the matter field of all the bosons of the
  theory.
- `GaugeFieldData.bosonMatterField_repLorentz_inclBosonValue`,
  `GaugeFieldData.bosonMatterField_repAlgebra_inclBosonValue` : each species is a
  subrepresentation of it.
- `GaugeFieldData.finrank_bosonMatterField` : its dimension is the sum of the
  dimensions of the species.

## iii. Table of contents

- A. The bosonic matter field
  - A.1. The transformation data species by species
  - A.2. The species as subrepresentations

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

namespace GaugeFieldData

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G 𝔤 G₀ 𝔤J} (T : GaugeFieldData jets)

/-!

## A. The bosonic matter field

-/

/-- **The bosonic matter field of a gauge theory**: the direct sum of the bosonic
  species, valued in `T.BosonModule`, with the Lorentz group, the jets of gauge
  transformations and the gauge algebra all acting species by species. It exists only for
  a family degenerate in mass dimension: `w` is the common mass weight of the species and
  `h` the proof that they all have it, which for the Standard Model, whose only scalar is
  the Higgs doublet, is weight two. -/
noncomputable def bosonMatterField (w : ℕ) (h : ∀ i, (T.boson i).massWeight = w) :
    MatterField jets :=
  MatterField.pi T.boson w h

variable {T}

lemma bosonMatterField_V (w : ℕ) (h : ∀ i, (T.boson i).massWeight = w) :
    (T.bosonMatterField w h).V = T.BosonModule := rfl

/-- The bosonic matter field carries the common mass weight of the species. -/
@[simp]
lemma bosonMatterField_massWeight (w : ℕ) (h : ∀ i, (T.boson i).massWeight = w) :
    (T.bosonMatterField w h).massWeight = w := rfl

/-!

### A.1. The transformation data species by species

-/

variable (T)

/-- **The Lorentz action on the bosonic module**, acting species by species. This is the
  Lorentz representation of the bosonic matter field, typed on `T.BosonModule` itself so
  that it can be spoken of without fixing a common mass weight. -/
noncomputable def repLorentzBosonModule : Representation ℂ SL(2,ℂ) T.BosonModule :=
  MatterField.repPi fun i => (T.boson i).repLorentz

variable {T}

@[simp]
lemma repLorentzBosonModule_apply (Λ : SL(2,ℂ)) (v : T.BosonModule) (i : T.BosonSpecies) :
    T.repLorentzBosonModule Λ v i = (T.boson i).repLorentz Λ (v i) := rfl

/-- The Lorentz action of the bosonic matter field is that of the bosonic module. -/
lemma bosonMatterField_repLorentz (w : ℕ) (h : ∀ i, (T.boson i).massWeight = w) :
    (T.bosonMatterField w h).repLorentz = T.repLorentzBosonModule := rfl

/-- The Lorentz group acts on a bosonic configuration species by species. -/
@[simp]
lemma bosonMatterField_repLorentz_apply (w : ℕ)
    (h : ∀ i, (T.boson i).massWeight = w) (Λ : SL(2,ℂ)) (v : T.BosonModule)
    (i : T.BosonSpecies) :
    (T.bosonMatterField w h).repLorentz Λ v i = (T.boson i).repLorentz Λ (v i) := rfl

/-- The gauge algebra acts on a bosonic configuration species by species. -/
@[simp]
lemma bosonMatterField_repAlgebra_apply (w : ℕ)
    (h : ∀ i, (T.boson i).massWeight = w) (c : 𝔤) (v : T.BosonModule)
    (i : T.BosonSpecies) :
    (T.bosonMatterField w h).repAlgebra c v i = (T.boson i).repAlgebra c (v i) := rfl

/-- The jets of gauge transformations act on the jets of the bosonic field species by
  species, through the identification `jetPiEquiv` of the jets of the bosonic module
  with the family of the jets of the species. -/
lemma bosonMatterField_repJet_apply (w : ℕ)
    (h : ∀ i, (T.boson i).massWeight = w) (U : G)
    (z : JetRing ⊗[ℂ] T.BosonModule) :
    (T.bosonMatterField w h).repJet U z =
      (jetPiEquiv T.BosonValue).symm
        (fun i => (T.boson i).repJet U (jetPiEquiv T.BosonValue z i)) := rfl

/-- The base-point Taylor coefficients of the bosonic jet action are those of the
  species, index by index. -/
lemma repCoeff_bosonMatterField (w : ℕ) (h : ∀ i, (T.boson i).massWeight = w) (U : G)
    (x : Multiset (Fin 1 ⊕ Fin 3)) :
    GaugeAlgebraRealization.repCoeff (T.bosonMatterField w h).repJet U x =
      LinearMap.piMap fun i =>
        GaugeAlgebraRealization.repCoeff (T.boson i).repJet U x :=
  MatterField.repCoeff_repJetPi T.boson U x

/-!

### A.2. The species as subrepresentations

-/

/-- **A bosonic species is a Lorentz subrepresentation of the bosonic matter field**:
  including a value of one species and then transforming is transforming and then
  including. Assembling the species into one field therefore loses no Lorentz
  information. -/
lemma bosonMatterField_repLorentz_inclBosonValue (w : ℕ)
    (h : ∀ i, (T.boson i).massWeight = w) (Λ : SL(2,ℂ)) (i : T.BosonSpecies)
    (x : T.BosonValue i) :
    (T.bosonMatterField w h).repLorentz Λ (T.inclBosonValue i x)
      = T.inclBosonValue i ((T.boson i).repLorentz Λ x) :=
  funext fun j =>
    Pi.apply_single (fun k => (T.boson k).repLorentz Λ) (fun _ => map_zero _) i x j

/-- **A bosonic species is a subrepresentation of the gauge algebra action** on the
  bosonic matter field, for the same reason: the gauge algebra does not mix the
  species. -/
lemma bosonMatterField_repAlgebra_inclBosonValue (w : ℕ)
    (h : ∀ i, (T.boson i).massWeight = w) (c : 𝔤) (i : T.BosonSpecies)
    (x : T.BosonValue i) :
    (T.bosonMatterField w h).repAlgebra c (T.inclBosonValue i x)
      = T.inclBosonValue i ((T.boson i).repAlgebra c x) :=
  funext fun j =>
    Pi.apply_single (fun k => (T.boson k).repAlgebra c) (fun _ => map_zero _) i x j

/-- The dimension of the bosonic matter field is the sum of the dimensions of the
  species. -/
lemma finrank_bosonMatterField (w : ℕ) (h : ∀ i, (T.boson i).massWeight = w) :
    Module.finrank ℂ (T.bosonMatterField w h).V
      = ∑ i, Module.finrank ℂ (T.BosonValue i) :=
  T.finrank_bosonModule

end GaugeFieldData
