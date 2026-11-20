/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeFieldData.Basic
/-!
# The bosonic module of a gauge theory

The value space of all the bosonic species of a gauge theory at once.

## i. Overview

A `GaugeFieldData G` records its bosons species by species, each with its own value
space `(T.boson i).V`. This file assembles those into a single complex vector space, the
bosonic module

`T.BosonModule = ∀ i, (T.boson i).V`,

in which one value of the whole bosonic content of the theory lives at once. For the
Standard Model, whose only bosonic species is the Higgs doublet, this is that doublet
again. A theory with a larger scalar sector, such as a second Higgs doublet or a singlet, has
the column of all of them.

It is the *value* space, not a space of component functions, and so it is not the
`GaugeFieldData.BosonGenerators` of the sibling file. The latter is a direct sum of component
spaces `FieldDerivSpace`, one per species, and is infinite-dimensional because it
carries a derivative label of every order. The bosonic module is finite-dimensional,
with dimension the sum of the dimensions of the species, and it is the space on which
`GaugeFieldData.bosonMatterField` puts the Lorentz, gauge and mass-weight structure of a
single matter field.

The species type is finite, so the product is also a direct sum. A bosonic
configuration is the sum of its species components, `sum_inclBosonValue_proj` below, and
the two descriptions of the module agree.

## ii. Key results

- `GaugeFieldData.BosonModule` : the value space of all the bosons of the theory.
- `GaugeFieldData.projBosonValue`, `GaugeFieldData.inclBosonValue` : the projection
  onto and the inclusion of one species.
- `GaugeFieldData.sum_inclBosonValue_proj` : a configuration is the sum of its species
  components.
- `GaugeFieldData.finrank_bosonModule` : its dimension is the sum of the dimensions of
  the species.

## iii. Table of contents

- A. The bosonic module
  - A.1. The species projections and inclusions
  - A.2. The dimension of the bosonic module

## iv. References

* None.

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

namespace GaugeFieldData

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ} (T : GaugeFieldData G)

/-!

## A. The bosonic module

-/

/-- The bosonic module of a gauge theory, the product over the bosonic species of their
  value spaces. One element of it is a value of the entire bosonic content of the theory, the
  column of all the boson fields. This is as opposed to
  `GaugeFieldData.BosonGenerators`, which is a space of component *functions* and is
  infinite-dimensional. Since the species type is finite the product is also their direct
  sum. -/
abbrev BosonModule : Type := ∀ i, T.BosonValue i

/-!

### A.1. The species projections and inclusions

-/

/-- The component of a bosonic configuration in one species. -/
abbrev projBosonValue (i : T.BosonSpecies) :
    T.BosonModule →ₗ[ℂ] T.BosonValue i :=
  LinearMap.proj i

/-- The inclusion of one bosonic species into the bosonic module, extending a value
  of that species by zero in every other. -/
abbrev inclBosonValue (i : T.BosonSpecies) :
    T.BosonValue i →ₗ[ℂ] T.BosonModule :=
  LinearMap.single ℂ T.BosonValue i

variable {T}

/-- A bosonic configuration is the sum of its species components. The product over
  the species is their direct sum, the species type being finite, so nothing is lost in
  describing the bosonic content of the theory by one module. -/
lemma sum_inclBosonValue_proj (v : T.BosonModule) :
    ∑ i, T.inclBosonValue i (v i) = v :=
  LinearMap.sum_single_apply T.BosonValue v

/-!

### A.2. The dimension of the bosonic module

-/

variable (T)

/-- The dimension of the bosonic module is the sum of the dimensions of the
  species, each species contributing the number of complex components of its
  multiplet. -/
lemma finrank_bosonModule :
    Module.finrank ℂ T.BosonModule = ∑ i, Module.finrank ℂ (T.BosonValue i) :=
  Module.finrank_pi_fintype ℂ

end GaugeFieldData
