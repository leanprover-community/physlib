/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeFieldData.Basic
/-!
# The fermionic module of a gauge theory

## i. Overview

A `GaugeFieldData jets` records its fermions species by species, each with its own value
space `(T.fermion i).V`. This file assembles those into a single complex vector space, the
**fermionic module**

`T.FermionModule = ∀ i, (T.fermion i).V`,

in which one value of the whole fermionic content of the theory lives at once. For the
Standard Model this is the sixteen-complex-dimensional space (fifteen Weyl components in
each of three generations, with the doublets counted with their gauge multiplicity) that a
physicist writes as the column of all the fermion fields.

It is the *value* space, not a space of component functions, and so it is not the
`FermionGenerators` of `GaugeFieldData.Basic`: the latter is a direct sum of component
spaces `JetComponentSpace`, one per species, and is infinite-dimensional because it
carries a derivative label of every order. The fermionic module is finite-dimensional,
with dimension the sum of the dimensions of the species, and it is the space on which
`GaugeFieldData.fermionMatterField` puts the Lorentz, gauge and mass-weight structure of a
single matter field.

The species type is finite, so the product is also a direct sum: a fermionic
configuration is the sum of its species components, `sum_inclFermionValue_proj` below, and
the two descriptions of the module agree.

## ii. Key results

- `GaugeFieldData.FermionModule` : the value space of all the fermions of the theory.
- `GaugeFieldData.projFermionValue`, `GaugeFieldData.inclFermionValue` : the projection
  onto and the inclusion of one species.
- `GaugeFieldData.sum_inclFermionValue_proj` : a configuration is the sum of its species
  components.
- `GaugeFieldData.finrank_fermionModule` : its dimension is the sum of the dimensions of
  the species.

## iii. Table of contents

- A. The fermionic module
  - A.1. The species projections and inclusions
  - A.2. The dimension of the fermionic module

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

namespace GaugeFieldData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} (T : GaugeFieldData jets)

/-!

## A. The fermionic module

-/

/-- **The fermionic module of a gauge theory**: the product, over the fermionic species,
  of their value spaces. One element of it is a value of the entire fermionic content of
  the theory — the column of all the fermion fields — as opposed to
  `GaugeFieldData.FermionGenerators`, which is a space of component *functions* and is
  infinite-dimensional. Since the species type is finite the product is also their direct
  sum. -/
abbrev FermionModule : Type := ∀ i, T.FermionValue i

/-!

### A.1. The species projections and inclusions

-/

/-- The component of a fermionic configuration in one species. -/
abbrev projFermionValue (i : T.FermionSpecies) :
    T.FermionModule →ₗ[ℂ] T.FermionValue i :=
  LinearMap.proj i

/-- The inclusion of one fermionic species into the fermionic module, extending a value
  of that species by zero in every other. -/
abbrev inclFermionValue (i : T.FermionSpecies) :
    T.FermionValue i →ₗ[ℂ] T.FermionModule :=
  LinearMap.single ℂ T.FermionValue i

variable {T}

@[simp]
lemma projFermionValue_apply (i : T.FermionSpecies) (v : T.FermionModule) :
    T.projFermionValue i v = v i := rfl

lemma projFermionValue_inclFermionValue_self (i : T.FermionSpecies)
    (v : T.FermionValue i) : T.projFermionValue i (T.inclFermionValue i v) = v :=
  Pi.single_eq_same i v

/-- A value of one species has no component in any other species: the inclusions of
  distinct species have disjoint supports. -/
lemma projFermionValue_inclFermionValue_of_ne {i j : T.FermionSpecies} (h : i ≠ j)
    (v : T.FermionValue j) : T.projFermionValue i (T.inclFermionValue j v) = 0 :=
  Pi.single_eq_of_ne h v

/-- **A fermionic configuration is the sum of its species components**. The product over
  the species is their direct sum, the species type being finite, so nothing is lost in
  describing the fermionic content of the theory by one module. -/
lemma sum_inclFermionValue_proj (v : T.FermionModule) :
    ∑ i, T.inclFermionValue i (v i) = v :=
  LinearMap.sum_single_apply T.FermionValue v

/-- Two linear maps out of the fermionic module agreeing on every species are equal. -/
lemma fermionModule_hom_ext {N : Type} [AddCommGroup N] [Module ℂ N]
    {F F' : T.FermionModule →ₗ[ℂ] N}
    (h : ∀ i, F.comp (T.inclFermionValue i) = F'.comp (T.inclFermionValue i)) : F = F' :=
  LinearMap.pi_ext' fun i => h i

/-!

### A.2. The dimension of the fermionic module

-/

variable (T)

/-- **The dimension of the fermionic module is the sum of the dimensions of the
  species**, each species contributing the number of complex components of its
  multiplet. -/
lemma finrank_fermionModule :
    Module.finrank ℂ T.FermionModule = ∑ i, Module.finrank ℂ (T.FermionValue i) :=
  Module.finrank_pi_fintype ℂ

end GaugeFieldData
