/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.Basic
/-!
# The field data of a gauge theory

## i. Overview

A gauge theory is fixed, before any Lagrangian is chosen, by a gauge context and a matter
content. The gauge context is the existing jet data of the gauge group, namely a global
group `G₀` with finite-dimensional real Lie algebra `𝔤`, a jet group `G` with jet Lie
algebra `𝔤J`, and a local-gauge-data package `jets : LocalGaugeData G 𝔤 G₀ 𝔤J` relating them. The
matter content is a finite family of
fermionic species and a finite family of bosonic species, each given by an existing
`MatterField jets`.

`GaugeFieldData jets` bundles the matter content over such a context. This file is the
datum itself and the value spaces it names; everything derived from it lives in the sibling
files of this directory:

* `GaugeFieldData.FermionGenerators` and `GaugeFieldData.BosonGenerators` — the generator
  spaces, as `SpeciesComponentSpace` of the families of value spaces, together with the
  Lorentz and jet gauge actions and the mass-weight scaling assembled species by species,
  and the identification of each with the component space of a single matter field;
* `GaugeFieldData.FermionModule` and `GaugeFieldData.BosonModule` — the value spaces of all
  the species at once;
* `GaugeFieldData.FermionMatterField` and `GaugeFieldData.BosonMatterField` — those modules
  carrying the structure of one matter field, when the species share a mass weight.

The connection generator space is not among them: it is the existing
`GaugeBoson.JetComponentSpace 𝔤`, fixed by the gauge context alone.

The algebra built on the three generator spaces, `GaugeFieldData.LocalFieldAlgebra`, and
its mapping-out universal property are in
`Physlib.ClassicalFieldTheory.JetAlgebra.LocalFieldAlgebra`. The split is one of subject
matter: here the datum and the spaces it determines, there the algebra of local expressions
on them.

It is field and transformation data before a Lagrangian, so packaging the species'
representations separately certifies no physical compatibility between them, and no
invariance is claimed here.

## ii. Key results

- `GaugeFieldData` : the matter content of a gauge theory over a gauge context.
- `GaugeFieldData.FermionValue`, `GaugeFieldData.BosonValue` : the value space of a
  species.

## iii. Table of contents

- A. The gauge context and the field datum
- B. The value spaces of the species

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

/-!

## A. The gauge context and the field datum

The gauge context is the parameter list of the structure below, namely the two groups, the
two Lie algebras, the supplied local-gauge-data package `jets` and its Taylor–Leibniz law. It is
`jets` that makes `𝔤` the gauge algebra of `G` rather than an unrelated Lie algebra, and
it is supplied rather than inferred, so a second package over the same carriers is a
different context. `GaugeFieldData` adds only the matter content on top of it.

-/

/-- The field data of a gauge theory. Over a gauge context, given by a jet gauge group `G`
  with global group `G₀`, a finite-dimensional real gauge algebra `𝔤` with jet algebra
  `𝔤J` and a local-gauge-data package `jets` over them, it records a finite family of fermionic
  species and a finite family of bosonic species, each given by an existing
  `MatterField jets`. The species types are `Fintype` rather than merely `Finite`, so
  that a theory may be summed over its species: this is what lets the several fermionic
  multiplets be assembled into the single fermionic matter field of
  `GaugeFieldData.fermionMatterField`.

  Nothing is repeated from `MatterField`, whose fields already carry the value space, the
  Lorentz representation, the local-gauge-data action and the mass weight of a species. Nothing is
  repeated from the gauge context either, and the gauge bosons are not a species, since
  their generator space is determined by `𝔤` alone.

  This is data before a Lagrangian. Collecting representations of the several species does
  not assert that they are jointly consistent. Gauge-Lorentz compatibility, factorization
  of the jet action through its global value, and richness of the jet group are separate
  conditions, none of them imposed here. -/
structure GaugeFieldData {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [Module.Finite ℝ 𝔤] {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
    (jets : LocalGaugeData G 𝔤 G₀ 𝔤J) where
  /-- The index type of the fermionic species. -/
  FermionSpecies : Type
  [decidableEqFermionSpecies : DecidableEq FermionSpecies]
  [fintypeFermionSpecies : Fintype FermionSpecies]
  /-- The matter field of each fermionic species. -/
  fermion : FermionSpecies → MatterField jets
  /-- The index type of the bosonic species. -/
  BosonSpecies : Type
  [decidableEqBosonSpecies : DecidableEq BosonSpecies]
  [fintypeBosonSpecies : Fintype BosonSpecies]
  /-- The matter field of each bosonic species. -/
  boson : BosonSpecies → MatterField jets

attribute [instance] GaugeFieldData.decidableEqFermionSpecies
  GaugeFieldData.fintypeFermionSpecies GaugeFieldData.decidableEqBosonSpecies
  GaugeFieldData.fintypeBosonSpecies

namespace GaugeFieldData

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G 𝔤 G₀ 𝔤J} (T : GaugeFieldData jets)

/-!

## B. The value spaces of the species

The datum records one matter field per species, so the value space of a species is simply
the value space of that matter field. Everything built on those value spaces is in the
sibling files: the fermionic and bosonic generator spaces, with the Lorentz action, the jet
gauge action and the mass-weight scaling on them, are in
`Physlib.ClassicalFieldTheory.GaugeTheory.GaugeFieldData.FermionGenerators` and
`...BosonGenerators`, which also identify each with the component space of a single matter
field; the value spaces themselves assemble into the `FermionModule` and `BosonModule` of
the remaining siblings.

The connection is not a species. It is fixed by the gauge context alone, and its component
functions `∂_s A_μ^φ` are the existing `GaugeBoson.JetComponentSpace 𝔤`, used without a new
name. They are real, a connection being a real object, which is why the third generator
family of the local field algebra is a real vector space, complexified once inside the
algebra. Finite dimensionality of `𝔤` is what makes `Module.Dual ℝ 𝔤` the span of the
adjoint components, so that these generators really are the `A_μ^a`.

-/

/-- The value space of a fermionic species. -/
abbrev FermionValue (i : T.FermionSpecies) : Type := (T.fermion i).V

/-- The value space of a bosonic species. -/
abbrev BosonValue (j : T.BosonSpecies) : Type := (T.boson j).V

end GaugeFieldData
