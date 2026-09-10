/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeFieldData.FermionModule
public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.Pi
/-!
# The fermionic matter field of a gauge theory

## i. Overview

`GaugeFieldData.FermionModule` is the value space of all the fermions of a theory at
once. This file puts on it the structure of a single `MatterField`: the Lorentz
representation, the action of the jets of gauge transformations, the infinitesimal action
of the gauge algebra and the mass weight, all acting species by species. It is the direct
sum `MatterField.pi` of the family `T.fermion`, and it is the object a physicist means by
"the fermion field" of a theory, as against the fifteen separate multiplets the Standard
Model is usually presented by.

The one thing the assembly needs beyond the datum is a shared mass weight. A `MatterField`
carries a single weight — that is what makes the mass-weight grading of its field algebra
well defined — so the family must be degenerate in mass dimension, and the common weight
`w` is taken as an argument together with the proof that every species has it. For the
Standard Model, and for any theory whose fermions are Weyl spinors, this is no restriction:
every fermionic species has weight three.

Assembling the species loses nothing, and this is the content of the lemmas below: each
species includes into the fermionic matter field as a subrepresentation, of the Lorentz
group and of the gauge algebra alike, so the several multiplets can be read off the single
field again. What it does lose is the ability to record *different* mass weights, which is
exactly why `GaugeFieldData.FermionGenerators` is a direct sum of component spaces rather
than the component space of this one field.

## ii. Key results

- `GaugeFieldData.fermionMatterField` : the matter field of all the fermions of the
  theory.
- `GaugeFieldData.fermionMatterField_repLorentz_inclFermionValue`,
  `GaugeFieldData.fermionMatterField_repAlgebra_inclFermionValue` : each species is a
  subrepresentation of it.
- `GaugeFieldData.finrank_fermionMatterField` : its dimension is the sum of the
  dimensions of the species.

## iii. Table of contents

- A. The fermionic matter field
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

## A. The fermionic matter field

-/

/-- **The fermionic matter field of a gauge theory**: the direct sum of the fermionic
  species, valued in `T.FermionModule`, with the Lorentz group, the jets of gauge
  transformations and the gauge algebra all acting species by species. It exists only for
  a family degenerate in mass dimension: `w` is the common mass weight of the species and
  `h` the proof that they all have it, which for the Standard Model, and for any theory
  whose fermions are Weyl spinors, is weight three. -/
noncomputable def fermionMatterField (w : ℕ) (h : ∀ i, (T.fermion i).massWeight = w) :
    MatterField jets :=
  MatterField.pi T.fermion w h

variable {T}

lemma fermionMatterField_V (w : ℕ) (h : ∀ i, (T.fermion i).massWeight = w) :
    (T.fermionMatterField w h).V = T.FermionModule := rfl

/-- The fermionic matter field carries the common mass weight of the species. -/
@[simp]
lemma fermionMatterField_massWeight (w : ℕ) (h : ∀ i, (T.fermion i).massWeight = w) :
    (T.fermionMatterField w h).massWeight = w := rfl

/-!

### A.1. The transformation data species by species

-/

variable (T)

/-- **The Lorentz action on the fermionic module**, acting species by species. This is the
  Lorentz representation of the fermionic matter field, typed on `T.FermionModule` itself so
  that it can be spoken of without fixing a common mass weight. -/
noncomputable def repLorentzFermionModule : Representation ℂ SL(2,ℂ) T.FermionModule :=
  MatterField.repPi fun i => (T.fermion i).repLorentz

variable {T}

@[simp]
lemma repLorentzFermionModule_apply (Λ : SL(2,ℂ)) (v : T.FermionModule) (i : T.FermionSpecies) :
    T.repLorentzFermionModule Λ v i = (T.fermion i).repLorentz Λ (v i) := rfl

/-- The Lorentz action of the fermionic matter field is that of the fermionic module. -/
lemma fermionMatterField_repLorentz (w : ℕ) (h : ∀ i, (T.fermion i).massWeight = w) :
    (T.fermionMatterField w h).repLorentz = T.repLorentzFermionModule := rfl

/-- The Lorentz group acts on a fermionic configuration species by species. -/
@[simp]
lemma fermionMatterField_repLorentz_apply (w : ℕ)
    (h : ∀ i, (T.fermion i).massWeight = w) (Λ : SL(2,ℂ)) (v : T.FermionModule)
    (i : T.FermionSpecies) :
    (T.fermionMatterField w h).repLorentz Λ v i = (T.fermion i).repLorentz Λ (v i) := rfl

/-- The gauge algebra acts on a fermionic configuration species by species. -/
@[simp]
lemma fermionMatterField_repAlgebra_apply (w : ℕ)
    (h : ∀ i, (T.fermion i).massWeight = w) (c : 𝔤) (v : T.FermionModule)
    (i : T.FermionSpecies) :
    (T.fermionMatterField w h).repAlgebra c v i = (T.fermion i).repAlgebra c (v i) := rfl

/-- The jets of gauge transformations act on the jets of the fermionic field species by
  species, through the identification `jetPiEquiv` of the jets of the fermionic module
  with the family of the jets of the species. -/
lemma fermionMatterField_repJet_apply (w : ℕ)
    (h : ∀ i, (T.fermion i).massWeight = w) (U : G)
    (z : JetRing ⊗[ℂ] T.FermionModule) :
    (T.fermionMatterField w h).repJet U z =
      (jetPiEquiv T.FermionValue).symm
        (fun i => (T.fermion i).repJet U (jetPiEquiv T.FermionValue z i)) := rfl

/-- The base-point Taylor coefficients of the fermionic jet action are those of the
  species, index by index. -/
lemma repCoeff_fermionMatterField (w : ℕ) (h : ∀ i, (T.fermion i).massWeight = w) (U : G)
    (x : Multiset (Fin 1 ⊕ Fin 3)) :
    GaugeAlgebraRealization.repCoeff (T.fermionMatterField w h).repJet U x =
      LinearMap.piMap fun i =>
        GaugeAlgebraRealization.repCoeff (T.fermion i).repJet U x :=
  MatterField.repCoeff_repJetPi T.fermion U x

/-!

### A.2. The species as subrepresentations

-/

/-- **A fermionic species is a Lorentz subrepresentation of the fermionic matter field**:
  including a value of one species and then transforming is transforming and then
  including. Assembling the species into one field therefore loses no Lorentz
  information. -/
lemma fermionMatterField_repLorentz_inclFermionValue (w : ℕ)
    (h : ∀ i, (T.fermion i).massWeight = w) (Λ : SL(2,ℂ)) (i : T.FermionSpecies)
    (x : T.FermionValue i) :
    (T.fermionMatterField w h).repLorentz Λ (T.inclFermionValue i x)
      = T.inclFermionValue i ((T.fermion i).repLorentz Λ x) :=
  funext fun j =>
    Pi.apply_single (fun k => (T.fermion k).repLorentz Λ) (fun _ => map_zero _) i x j

/-- **A fermionic species is a subrepresentation of the gauge algebra action** on the
  fermionic matter field, for the same reason: the gauge algebra does not mix the
  species. -/
lemma fermionMatterField_repAlgebra_inclFermionValue (w : ℕ)
    (h : ∀ i, (T.fermion i).massWeight = w) (c : 𝔤) (i : T.FermionSpecies)
    (x : T.FermionValue i) :
    (T.fermionMatterField w h).repAlgebra c (T.inclFermionValue i x)
      = T.inclFermionValue i ((T.fermion i).repAlgebra c x) :=
  funext fun j =>
    Pi.apply_single (fun k => (T.fermion k).repAlgebra c) (fun _ => map_zero _) i x j

/-- The dimension of the fermionic matter field is the sum of the dimensions of the
  species. -/
lemma finrank_fermionMatterField (w : ℕ) (h : ∀ i, (T.fermion i).massWeight = w) :
    Module.finrank ℂ (T.fermionMatterField w h).V
      = ∑ i, Module.finrank ℂ (T.FermionValue i) :=
  T.finrank_fermionModule

end GaugeFieldData
