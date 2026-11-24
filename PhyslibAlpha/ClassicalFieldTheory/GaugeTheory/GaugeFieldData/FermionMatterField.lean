/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeFieldData.FermionModule
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.Pi
/-!
# The fermionic matter field of a gauge theory

All the fermionic species of a gauge theory with a common mass weight, as one matter field.

## i. Overview

`GaugeFieldData.FermionModule` is the value space of all the fermions of a theory at once. This file
puts on it the structure of a single `MatterField`: the Lorentz representation, the action of the
jets of gauge transformations, the infinitesimal action of the gauge algebra and the mass weight,
all acting species by species. It is the direct sum `GlobalGaugeGroup.MatterField.pi` of the
family `T.fermion`, and it is the object a physicist means by "the fermion field" of a theory, as
against the fifteen separate multiplets the Standard Model is usually presented by.

Beyond the datum, the assembly needs a shared mass weight. The construction packages the
family into one `MatterField`, which has one weight, so the family must be degenerate in mass
dimension, and the assembled field carries the common mass weight of its entries. That weight
`w` is taken as an argument together with the proof that every species has it. For the
Standard Model, and for any theory whose fermions are Weyl spinors, this is no restriction:
every fermionic species has weight three. The common statistics comes from the datum itself,
whose field `fermion_statistic` requires every fermionic species to be declared fermionic.

Assembling the species loses nothing, and this is the content of the lemmas below. Each
species includes into the fermionic matter field as a subrepresentation, of the Lorentz
group and of the gauge algebra alike, so the several multiplets can be read off the single
field again. What it does lose is the ability to record *different* mass weights, which is
exactly why `GaugeFieldData.FermionGenerators` is a direct sum of component spaces rather
than the component space of this one field.

## ii. Key results

- `GaugeFieldData.fermionMatterField` : the matter field of all the fermions of the
  theory.
- `GaugeFieldData.repJetFermionModule` : the action of the jets of gauge transformations
  on the jets of the fermionic module, needing no common mass weight.
- `GaugeFieldData.fermionMatterField_repLorentz_inclFermionValue`,
  `GaugeFieldData.fermionMatterField_repAlgebra_inclFermionValue` : each species is a
  subrepresentation of it.
- `GaugeFieldData.finrank_fermionMatterField` : its dimension is the sum of the
  dimensions of the species.

## iii. Table of contents

- A. The fermionic matter field
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

## A. The fermionic matter field

-/

/-- The fermionic matter field of a gauge theory, the direct sum of the fermionic
  species, valued in `T.FermionModule`, with the Lorentz group, the jets of gauge
  transformations and the gauge algebra all acting species by species. It exists only for
  a family degenerate in mass dimension, where `w` is the common mass weight of the species and
  `h` the proof that they all have it, which for the Standard Model, and for any theory
  whose fermions are Weyl spinors, is weight three. -/
noncomputable def fermionMatterField (w : ℕ) (h : ∀ i, (T.fermion i).massWeight = w) :
    G.MatterField :=
  GlobalGaugeGroup.MatterField.pi T.fermion w h .fermionic T.fermion_statistic

variable {T}

/-- The fermionic matter field carries the common mass weight of the species. -/
@[simp]
lemma fermionMatterField_massWeight (w : ℕ) (h : ∀ i, (T.fermion i).massWeight = w) :
    (T.fermionMatterField w h).massWeight = w := rfl

/-- The fermionic matter field is fermionic, as every fermionic species is declared to be. -/
@[simp]
lemma fermionMatterField_statistic (w : ℕ) (h : ∀ i, (T.fermion i).massWeight = w) :
    (T.fermionMatterField w h).statistic = .fermionic := rfl

/-!

### A.1. The transformation data species by species

-/

variable (T)

/-- The Lorentz action on the fermionic module, acting species by species. This is the
  Lorentz representation of the fermionic matter field, typed on `T.FermionModule` itself so
  that it can be spoken of without fixing a common mass weight. -/
noncomputable def repLorentzFermionModule : Representation ℂ SL(2,ℂ) T.FermionModule :=
  GlobalGaugeGroup.MatterField.repPi fun i => (T.fermion i).repLorentz

variable {T}

@[simp]
lemma repLorentzFermionModule_apply (Λ : SL(2,ℂ)) (v : T.FermionModule) (i : T.FermionSpecies) :
    T.repLorentzFermionModule Λ v i = (T.fermion i).repLorentz Λ (v i) := rfl

variable (T)

/-- The action of the jets of gauge transformations on the jets of the fermionic
  module, acting species by species. Like `repLorentzFermionModule` it is typed on
  `T.FermionModule` itself, so that it can be spoken of without fixing a common mass
  weight; the gauge action of a theory whose fermions carry different mass dimensions is
  perfectly well defined, only its packaging as one `MatterField` is not. -/
noncomputable def repJetFermionModule :
    Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] T.FermionModule) :=
  GlobalGaugeGroup.MatterField.repJetPi T.fermion

variable {T}

/-- A fermionic species is a subrepresentation of the jet gauge action on the fermionic
  module. The projection onto its value space intertwines the two actions on the jets. -/
lemma lTensor_projFermionValue_repJetFermionModule (i : T.FermionSpecies) (U : G.gaugeJetGroup) :
    (LinearMap.lTensor SpaceTimeAlgebra (T.projFermionValue i)).comp (T.repJetFermionModule U)
      = ((T.fermion i).repJet U).comp
        (LinearMap.lTensor SpaceTimeAlgebra (T.projFermionValue i)) :=
  GlobalGaugeGroup.MatterField.lTensor_proj_repJetPi T.fermion i U

/-- The jet gauge action of the fermionic matter field is that of the fermionic module. -/
lemma fermionMatterField_repJet (w : ℕ) (h : ∀ i, (T.fermion i).massWeight = w) :
    (T.fermionMatterField w h).repJet = T.repJetFermionModule :=
  GlobalGaugeGroup.MatterField.pi_repJet T.fermion w h .fermionic T.fermion_statistic

/-- The Lorentz group acts on a fermionic configuration species by species. -/
@[simp]
lemma fermionMatterField_repLorentz_apply (w : ℕ)
    (h : ∀ i, (T.fermion i).massWeight = w) (Λ : SL(2,ℂ)) (v : T.FermionModule)
    (i : T.FermionSpecies) :
    (T.fermionMatterField w h).repLorentz Λ v i = (T.fermion i).repLorentz Λ (v i) := rfl

/-- The gauge algebra acts on a fermionic configuration species by species. -/
lemma fermionMatterField_repAlgebra_apply (w : ℕ)
    (h : ∀ i, (T.fermion i).massWeight = w) (c : G.lieSubalgebra) (v : T.FermionModule)
    (i : T.FermionSpecies) :
    (T.fermionMatterField w h).repAlgebra c v i = (T.fermion i).repAlgebra c (v i) := by
  unfold fermionMatterField
  rw [GlobalGaugeGroup.MatterField.pi_repAlgebra]
  rfl

/-!

### A.2. The species as subrepresentations

-/

/-- A fermionic species is a Lorentz subrepresentation of the fermionic matter field.
  Including a value of one species and then transforming is transforming and then
  including. Assembling the species into one field therefore loses no Lorentz
  information. -/
lemma fermionMatterField_repLorentz_inclFermionValue (w : ℕ)
    (h : ∀ i, (T.fermion i).massWeight = w) (Λ : SL(2,ℂ)) (i : T.FermionSpecies)
    (x : T.FermionValue i) :
    (T.fermionMatterField w h).repLorentz Λ (T.inclFermionValue i x)
      = T.inclFermionValue i ((T.fermion i).repLorentz Λ x) :=
  funext fun j =>
    Pi.apply_single (fun k => (T.fermion k).repLorentz Λ) (fun _ => map_zero _) i x j

/-- A fermionic species is a subrepresentation of the gauge algebra action on the
  fermionic matter field, for the same reason. The gauge algebra does not mix the
  species. -/
lemma fermionMatterField_repAlgebra_inclFermionValue (w : ℕ)
    (h : ∀ i, (T.fermion i).massWeight = w) (c : G.lieSubalgebra) (i : T.FermionSpecies)
    (x : T.FermionValue i) :
    (T.fermionMatterField w h).repAlgebra c (T.inclFermionValue i x)
      = T.inclFermionValue i ((T.fermion i).repAlgebra c x) :=
  funext fun j => by
    rw [fermionMatterField_repAlgebra_apply]
    exact Pi.apply_single (fun k => (T.fermion k).repAlgebra c) (fun _ => map_zero _) i x j

/-- The dimension of the fermionic matter field is the sum of the dimensions of the
  species. -/
lemma finrank_fermionMatterField (w : ℕ) (h : ∀ i, (T.fermion i).massWeight = w) :
    Module.finrank ℂ (T.fermionMatterField w h).V
      = ∑ i, Module.finrank ℂ (T.FermionValue i) :=
  T.finrank_fermionModule

/-- The projection of the fermionic matter field onto one species, typed as a map out of
  `(T.fermionMatterField w h).V` rather than out of `T.FermionModule`. The two are the same
  type by definition, but naming the first keeps unification from having to unfold the
  direct sum every time the projection meets the matter field. -/
noncomputable abbrev projFermionField (w : ℕ) (h : ∀ i, (T.fermion i).massWeight = w)
    (i : T.FermionSpecies) : (T.fermionMatterField w h).V →ₗ[ℂ] (T.fermion i).V :=
  LinearMap.proj i

end GaugeFieldData
