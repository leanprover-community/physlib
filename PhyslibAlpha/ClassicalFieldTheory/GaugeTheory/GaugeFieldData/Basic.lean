/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.InfinitesimalAction
/-!
# The field data of a gauge theory

The matter content of a gauge theory, its fermionic and bosonic species over a gauge group.

## i. Overview

A gauge theory is fixed, before any Lagrangian is chosen, by a global gauge group `G` and a
matter content. The gauge group `G : GlobalGaugeGroup κ` carries its gauge jet group, its Lie
algebra and the jet operations relating them. The matter content is a finite family of
fermionic species and a finite family of bosonic species, each a matter field over `G`
(`G.MatterField`) whose declared statistic is that of its family.

`GaugeFieldData G` bundles the matter content over such a gauge group. This file is the
datum itself and the value spaces it names. Everything derived from it lives in the sibling
files of this directory.

* `FermionGenerators.lean` and `BosonGenerators.lean` give the generator spaces
  `GaugeFieldData.FermionGenerators` and `GaugeFieldData.BosonGenerators`, the direct sums
  of the component spaces of the species, together with the Lorentz and jet gauge actions
  and the mass-weight scaling assembled species by species, and the identification of each
  with the component space of a single matter field.
* `FermionModule.lean` and `BosonModule.lean` give the value spaces of all the species at
  once.
* `FermionMatterField.lean` and `BosonMatterField.lean` give those modules the structure of
  one matter field, when the species share a mass weight.

The connection generator space is not among them. It is the existing
`GaugeBoson.FieldDerivSpace G`, fixed by the gauge group alone.

The algebra built on the three generator spaces, `GaugeFieldData.LocalFieldAlgebra`, and
its mapping-out universal property are in
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Basic`. The split is one of subject
matter, here the datum and the spaces it determines, there the algebra of local expressions
on them.

It is field and transformation data before a Lagrangian, so packaging the species'
representations separately certifies no physical compatibility between them, and no
invariance is claimed here.

## ii. Key results

- `GaugeFieldData` : the matter content of a gauge theory over a gauge group, split into
  fermionic and bosonic species in agreement with their declared statistics.
- `GaugeFieldData.FermionValue`, `GaugeFieldData.BosonValue` : the value space of a
  species.
- `GaugeFieldData.GaugeLorentzCommute`, `GaugeFieldData.GaugeLorentzCompatible` : the
  conditions of `GlobalGaugeGroup.MatterField`, imposed on every species of the datum.
- `GaugeFieldData.GaugeLorentzCommute.gaugeLorentzCompatible` : the first condition implies
  the second.

## iii. Table of contents

- A. The matter content of a gauge theory
- B. The value spaces of the species
- C. Conditions on the species of a datum

## iv. References

* None.

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

/-!

## A. The matter content of a gauge theory

The structure below is the matter content of a gauge theory over a global gauge group `G`, that
is, a finite family of fermionic species and a finite family of bosonic species, each given as a
matter field. The gauge group is the parameter, and the gauge bosons are determined by it
alone, so they are not recorded. The structure is needed because the algebras of local
expressions are built on all the species at once, the fermionic species supplying the
generators of an exterior-algebra factor and the bosonic species those of a symmetric-algebra
factor. A single datum lets the sibling files assemble the species into one fermionic and one
bosonic matter field and keeps the statistic of each family explicit.

-/

/-- The field data of a gauge theory. Over a global gauge group `G`, it records a finite
  family of fermionic species and a finite family of bosonic species, each given by a
  `G.MatterField`. The species types are `Fintype` rather than merely `Finite`, so that a
  theory may be summed over its species. This is what lets the several fermionic multiplets
  be assembled into the single fermionic matter field of `GaugeFieldData.fermionMatterField`.

  Nothing is repeated from `GlobalGaugeGroup.MatterField`, whose fields already carry the
  value space, the Lorentz representation, the gauge actions, the mass weight and the declared
  statistic of a species. The fermionic family supplies the generators of the exterior-algebra
  factor of the local field algebra `GaugeFieldData.LocalFieldAlgebra`, and the bosonic family
  those of its symmetric-algebra factor. The fields `fermion_statistic` and `boson_statistic`
  require every entry of each family to be declared with the corresponding statistics. The
  gauge bosons are not a species, since their generator space is determined by
  `G.lieSubalgebra` alone.

  This is data before a Lagrangian. Collecting representations of the several species does
  not assert that they are jointly consistent. Gauge-Lorentz compatibility is a separate
  condition, not imposed here. -/
structure GaugeFieldData {κ : Type} [Fintype κ] [DecidableEq κ] (G : GlobalGaugeGroup κ) where
  /-- The index type of the fermionic species. -/
  FermionSpecies : Type
  [decidableEqFermionSpecies : DecidableEq FermionSpecies]
  [fintypeFermionSpecies : Fintype FermionSpecies]
  /-- The matter field of each fermionic species. -/
  fermion : FermionSpecies → G.MatterField
  /-- Every fermionic species is declared fermionic. -/
  fermion_statistic : ∀ i, (fermion i).statistic = .fermionic
  /-- The index type of the bosonic species. -/
  BosonSpecies : Type
  [decidableEqBosonSpecies : DecidableEq BosonSpecies]
  [fintypeBosonSpecies : Fintype BosonSpecies]
  /-- The matter field of each bosonic species. -/
  boson : BosonSpecies → G.MatterField
  /-- Every bosonic species is declared bosonic. -/
  boson_statistic : ∀ j, (boson j).statistic = .bosonic

attribute [instance] GaugeFieldData.decidableEqFermionSpecies
  GaugeFieldData.fintypeFermionSpecies GaugeFieldData.decidableEqBosonSpecies
  GaugeFieldData.fintypeBosonSpecies

namespace GaugeFieldData

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ} (T : GaugeFieldData G)

/-!

## B. The value spaces of the species

The datum records one matter field per species, so the value space of a species is simply
the value space of that matter field. Everything built on those value spaces is in the
sibling files. The fermionic and bosonic generator spaces, with the Lorentz action, the jet
gauge action and the mass-weight scaling on them, are in
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeFieldData.FermionGenerators` and its
bosonic twin, which also identify each with the component space of a single matter field.
The value spaces themselves assemble into the `FermionModule` and `BosonModule` of the
remaining siblings.

The connection is not a species. It is fixed by the gauge group alone, and its component functions
`∂_s A_μ^φ` are the existing `GaugeBoson.FieldDerivSpace G`, used without a new name. They are
real, a connection being a real object, which is why the third generator family of the local field
algebra is a real vector space, complexified once inside the algebra. Finite dimensionality of
`G.lieSubalgebra` is what makes `Module.Dual ℝ G.lieSubalgebra` the span of the adjoint components,
so that these generators really are the `A_μ^a`.

-/

/-- The value space of a fermionic species. -/
abbrev FermionValue (i : T.FermionSpecies) : Type := (T.fermion i).V

/-- The value space of a bosonic species. -/
abbrev BosonValue (j : T.BosonSpecies) : Type := (T.boson j).V

TODO "(2026-09-11, lines 143-148) I think these names should likely be
  changed to something more descriptive."

/-!

## C. Conditions on the species of a datum

The conditions on a matter field (from
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.InfinitesimalAction`),
imposed species by species. They are stated on the datum alone so that a concrete theory can
record them next to its field data. The covariant derivative theory assumes the Lie algebra
condition where it needs it, and the descent of invariants assumes the group condition, which
implies it.

-/

/-- The gauge and Lorentz representations of every species of the datum commute. -/
def GaugeLorentzCommute : Prop :=
  (∀ i, (T.fermion i).GaugeLorentzCommute) ∧ (∀ j, (T.boson j).GaugeLorentzCommute)

/-- The infinitesimal gauge action of every species of the datum commutes with its Lorentz
  representation. -/
def GaugeLorentzCompatible : Prop :=
  (∀ i, (T.fermion i).GaugeLorentzCompatible) ∧ (∀ j, (T.boson j).GaugeLorentzCompatible)

variable {T} in
/-- If the gauge and Lorentz representations of every species commute, so do the
  infinitesimal gauge actions and the Lorentz representations. -/
lemma GaugeLorentzCommute.gaugeLorentzCompatible (h : T.GaugeLorentzCommute) :
    T.GaugeLorentzCompatible :=
  ⟨fun i => (h.1 i).gaugeLorentzCompatible, fun j => (h.2 j).gaugeLorentzCompatible⟩

end GaugeFieldData
