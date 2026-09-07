/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.Basic
public import Physlib.ClassicalFieldTheory.GaugeTheory.Matter.MatterField
public import Physlib.ClassicalFieldTheory.JetAlgebra.SpeciesGenerators
/-!
# The field data of a gauge theory and its local field algebra

## i. Overview

A gauge theory is fixed, before any Lagrangian is chosen, by a gauge context and a matter
content. The gauge context is the existing jet data of the gauge group, namely a global
group `G₀` with finite-dimensional real Lie algebra `𝔤`, a jet group `G` with jet Lie
algebra `𝔤J`, and the identities `GaugeJet` and `GaugeJetLeibniz` relating them. The matter
content is a finite family of fermionic species and a finite family of bosonic species,
each given by an existing `MatterField G`.

`GaugeFieldData G 𝔤` bundles the matter content over such a context. From it this file
derives, with no further data,

* the fermionic and bosonic generator spaces, as `SpeciesComponentSpace` of the families
  of value spaces;
* the connection generator space, as the existing `GaugeBoson.JetComponentSpace 𝔤`;
* the local field algebra `GaugeFieldData.LocalAlgebra`, the `SpeciesLocalFieldAlgebra` of
  those three, with its generator inclusions and their relations;
* the realization arrow, by which a compatible assignment of the generators in any
  associative unital complex algebra `B`, not assumed commutative, extends to one and only
  one `LocalAlgebra →ₐ[ℂ] B`.

That is the chain `T → J(T) → B`. It is field and transformation data before a Lagrangian,
so packaging the species' representations separately certifies no physical compatibility
between them, and no invariance is claimed here.

The generator spaces carry derivative symbols of every order and are infinite-dimensional
however few species there are. Finiteness of the species types and of the value spaces is
not inherited by them.

## ii. Key results

- `GaugeFieldData` : the matter content of a gauge theory over a gauge context.
- `GaugeFieldData.FermionGenerators`, `GaugeFieldData.BosonGenerators` : the species
  generator spaces.
- `GaugeFieldData.LocalAlgebra` : the local field algebra `J(T)` of the datum.
- `GaugeFieldData.ιFermion`, `GaugeFieldData.ιBoson`, `GaugeFieldData.ιConnection` : the
  generator inclusions, with their statistics.
- `GaugeFieldData.Assignment`, `GaugeFieldData.lift_ιFermion`,
  `GaugeFieldData.existsUnique_algHom` : the realization arrow `J(T) →ₐ[ℂ] B` and its
  uniqueness.
- `GaugeFieldData.repLorentzFermion`, `GaugeFieldData.repJetFermion` : the Lorentz and jet
  gauge actions assembled on the generator spaces.
- `GaugeFieldData.massWeightScaleFermion` : the mass-weight scaling carrying the weight of
  each species.

## iii. Table of contents

- A. The gauge context and the field datum
- B. The generator spaces
  - B.1. The species generator spaces
  - B.2. The connection generator space
- C. The local field algebra of the datum
  - C.1. The generator inclusions
  - C.2. The statistics of the generators
- D. Realizations of the datum
  - D.1. The induced algebra homomorphism
  - D.2. Uniqueness
- E. The transformation data on the generator spaces
  - E.1. The Lorentz action
  - E.2. The jet gauge action
  - E.3. The mass weights

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

/-!

## A. The gauge context and the field datum

The gauge context is the parameter list of the structure below, namely the two groups, the
two Lie algebras and the two gauge-jet classes. It is what makes `𝔤` the gauge algebra of
`G` rather than an unrelated Lie algebra. `GaugeFieldData` adds only the matter content on
top of it.

-/

/-- The field data of a gauge theory. Over a gauge context, given by a jet gauge group `G`
  with global group `G₀`, a finite-dimensional real gauge algebra `𝔤` with jet algebra
  `𝔤J` and the gauge-jet identities, it records a finite family of fermionic species and a
  finite family of bosonic species, each given by an existing `MatterField G`.

  Nothing is repeated from `MatterField`, whose fields already carry the value space, the
  Lorentz representation, the gauge-jet action and the mass weight of a species. Nothing is
  repeated from the gauge context either, and the gauge bosons are not a species, since
  their generator space is determined by `𝔤` alone.

  This is data before a Lagrangian. Collecting representations of the several species does
  not assert that they are jointly consistent. Gauge-Lorentz compatibility, factorization
  of the jet action through its global value, and richness of the jet group are separate
  conditions, none of them imposed here. -/
structure GaugeFieldData (G : Type) [Group G] (𝔤 : Type) [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [Module.Finite ℝ 𝔤] {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
    [GaugeJet G 𝔤 G₀ 𝔤J] [GaugeJetLeibniz G 𝔤 G₀ 𝔤J] where
  /-- The index type of the fermionic species. -/
  FermionSpecies : Type
  [decidableEqFermionSpecies : DecidableEq FermionSpecies]
  [finiteFermionSpecies : Finite FermionSpecies]
  /-- The matter field of each fermionic species. -/
  fermion : FermionSpecies → MatterField G
  /-- The index type of the bosonic species. -/
  BosonSpecies : Type
  [decidableEqBosonSpecies : DecidableEq BosonSpecies]
  [finiteBosonSpecies : Finite BosonSpecies]
  /-- The matter field of each bosonic species. -/
  boson : BosonSpecies → MatterField G

attribute [instance] GaugeFieldData.decidableEqFermionSpecies
  GaugeFieldData.finiteFermionSpecies GaugeFieldData.decidableEqBosonSpecies
  GaugeFieldData.finiteBosonSpecies

namespace GaugeFieldData

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J] [GaugeJet G 𝔤 G₀ 𝔤J]
  [GaugeJetLeibniz G 𝔤 G₀ 𝔤J] (T : GaugeFieldData G 𝔤)

/-!

## B. The generator spaces

### B.1. The species generator spaces

-/

/-- The value space of a fermionic species. -/
abbrev FermionValue (i : T.FermionSpecies) : Type := (T.fermion i).V

/-- The value space of a bosonic species. -/
abbrev BosonValue (j : T.BosonSpecies) : Type := (T.boson j).V

/-- The fermionic generator space of the datum, holding the component functions `∂_s ψ_α`
  and their conjugates of every fermionic species at once, as a direct sum over the
  species. The direct sum, rather than a single component space on the product of the
  value spaces, is what lets the species carry different mass weights. -/
abbrev FermionGenerators : Type := SpeciesComponentSpace T.FermionValue

/-- The bosonic generator space of the datum, assembled from the bosonic species in
  the same way. -/
abbrev BosonGenerators : Type := SpeciesComponentSpace T.BosonValue

/-- The inclusion of the component space of one fermionic species into the fermionic
  generator space. -/
abbrev inclFermion (i : T.FermionSpecies) :
    JetComponentSpace (T.FermionValue i) →ₗ[ℂ] T.FermionGenerators :=
  SpeciesComponentSpace.incl T.FermionValue i

/-- The inclusion of the component space of one bosonic species into the bosonic generator
  space. -/
abbrev inclBoson (j : T.BosonSpecies) :
    JetComponentSpace (T.BosonValue j) →ₗ[ℂ] T.BosonGenerators :=
  SpeciesComponentSpace.incl T.BosonValue j

/-!

### B.2. The connection generator space

The connection is not a species. It is fixed by the gauge context alone, and its component
functions `∂_s A_μ^φ` are the existing `GaugeBoson.JetComponentSpace 𝔤`, used below
without a new name. They are real, a connection being a real object, which is why the
third generator family of the local field algebra is a real vector space, complexified
once inside the algebra. Finite dimensionality of `𝔤` is what makes `Module.Dual ℝ 𝔤` the
span of the adjoint components, so that these generators really are the `A_μ^a`.

## C. The local field algebra of the datum

-/

/-- The local field algebra `J(T)` of a gauge-field datum, in which the local expressions
  of the theory, such as Lagrangian terms, currents and field strengths, live before any
  of them is selected. Its fermionic generators are the component functions of the
  fermionic species, its bosonic generators those of the bosonic species, and its
  connection generators the component functions of the gauge bosons of `𝔤`.

  All the fermionic species share one exterior algebra, so their generators anticommute
  across species and not only within one. -/
abbrev LocalAlgebra : Type :=
  SpeciesLocalFieldAlgebra T.FermionValue T.BosonValue (GaugeBoson.JetComponentSpace 𝔤)

/-!

### C.1. The generator inclusions

-/

/-- The generators of one fermionic species inside the local field algebra. -/
noncomputable def ιFermion (i : T.FermionSpecies) :
    JetComponentSpace (T.FermionValue i) →ₗ[ℂ] T.LocalAlgebra :=
  SpeciesLocalFieldAlgebra.ιFermionSpecies T.FermionValue T.BosonValue
    (GaugeBoson.JetComponentSpace 𝔤) i

/-- The generators of one bosonic species inside the local field algebra. -/
noncomputable def ιBoson (j : T.BosonSpecies) :
    JetComponentSpace (T.BosonValue j) →ₗ[ℂ] T.LocalAlgebra :=
  SpeciesLocalFieldAlgebra.ιBosonSpecies T.FermionValue T.BosonValue
    (GaugeBoson.JetComponentSpace 𝔤) j

/-- The connection generators inside the local field algebra. They are only real-linear,
  since the connection generator space is real. -/
noncomputable def ιConnection : GaugeBoson.JetComponentSpace 𝔤 →ₗ[ℝ] T.LocalAlgebra :=
  LocalFieldAlgebra.ιConnection (SpeciesComponentSpace T.FermionValue)
    (SpeciesComponentSpace T.BosonValue) (GaugeBoson.JetComponentSpace 𝔤)

variable {T}

lemma ιFermion_apply (i : T.FermionSpecies) (x : JetComponentSpace (T.FermionValue i)) :
    T.ιFermion i x
      = LocalFieldAlgebra.ιFermion T.FermionGenerators T.BosonGenerators
          (GaugeBoson.JetComponentSpace 𝔤) (T.inclFermion i x) := rfl

lemma ιBoson_apply (j : T.BosonSpecies) (y : JetComponentSpace (T.BosonValue j)) :
    T.ιBoson j y
      = LocalFieldAlgebra.ιBoson T.FermionGenerators T.BosonGenerators
          (GaugeBoson.JetComponentSpace 𝔤) (T.inclBoson j y) := rfl

/-!

### C.2. The statistics of the generators

The relations of the local field algebra, read at the datum. Fermi statistics holds on the
fermionic generators, across species as well as within one, and everything else commutes.
None of this is new content. Each lemma is the corresponding relation of
`SpeciesLocalFieldAlgebra` with the datum's generator spaces supplied explicitly, which is
what keeps the elaboration directed at the tensor product.

-/

/-- A fermionic generator squares to zero. -/
@[simp]
lemma ιFermion_mul_self (i : T.FermionSpecies) (x : JetComponentSpace (T.FermionValue i)) :
    T.ιFermion i x * T.ιFermion i x = 0 :=
  SpeciesLocalFieldAlgebra.ιFermionSpecies_mul_self (Vf := T.FermionValue)
    (Vb := T.BosonValue) (EA := GaugeBoson.JetComponentSpace 𝔤) i x

/-- The generators of two fermionic species of the datum anticommute. The species
  enter one exterior algebra through different summands of the fermionic generator space,
  so this is ordinary exterior anticommutation and not an extra relation. -/
lemma ιFermion_mul_swap (i j : T.FermionSpecies) (x : JetComponentSpace (T.FermionValue i))
    (y : JetComponentSpace (T.FermionValue j)) :
    T.ιFermion i x * T.ιFermion j y = -(T.ιFermion j y * T.ιFermion i x) :=
  SpeciesLocalFieldAlgebra.ιFermionSpecies_mul_swap (Vf := T.FermionValue)
    (Vb := T.BosonValue) (EA := GaugeBoson.JetComponentSpace 𝔤) i j x y

/-- Bosonic generators commute, across species as well as within one. -/
lemma ιBoson_commute (i j : T.BosonSpecies) (x : JetComponentSpace (T.BosonValue i))
    (y : JetComponentSpace (T.BosonValue j)) :
    Commute (T.ιBoson i x) (T.ιBoson j y) :=
  SpeciesLocalFieldAlgebra.ιBosonSpecies_commute (Vf := T.FermionValue)
    (Vb := T.BosonValue) (EA := GaugeBoson.JetComponentSpace 𝔤) i j x y

/-- A bosonic generator commutes with a fermionic one, bosons being even. -/
lemma ιBoson_commute_ιFermion (j : T.BosonSpecies) (i : T.FermionSpecies)
    (y : JetComponentSpace (T.BosonValue j)) (x : JetComponentSpace (T.FermionValue i)) :
    Commute (T.ιBoson j y) (T.ιFermion i x) :=
  SpeciesLocalFieldAlgebra.ιBosonSpecies_commute_ιFermionSpecies (Vf := T.FermionValue)
    (Vb := T.BosonValue) (EA := GaugeBoson.JetComponentSpace 𝔤) j i y x

/-- A bosonic generator commutes with a connection generator. -/
lemma ιBoson_commute_ιConnection (j : T.BosonSpecies)
    (y : JetComponentSpace (T.BosonValue j)) (v : GaugeBoson.JetComponentSpace 𝔤) :
    Commute (T.ιBoson j y) (T.ιConnection v) :=
  SpeciesLocalFieldAlgebra.ιBosonSpecies_commute_ιConnection (Vf := T.FermionValue)
    (Vb := T.BosonValue) (EA := GaugeBoson.JetComponentSpace 𝔤) j y v

/-- A connection generator commutes with a fermionic one, the connection being even. -/
lemma ιConnection_commute_ιFermion (v : GaugeBoson.JetComponentSpace 𝔤)
    (i : T.FermionSpecies) (x : JetComponentSpace (T.FermionValue i)) :
    Commute (T.ιConnection v) (T.ιFermion i x) :=
  SpeciesLocalFieldAlgebra.ιConnection_commute_ιFermionSpecies (Vf := T.FermionValue)
    (Vb := T.BosonValue) (EA := GaugeBoson.JetComponentSpace 𝔤) v i x

/-- Connection generators commute pairwise. -/
lemma ιConnection_commute (v w : GaugeBoson.JetComponentSpace 𝔤) :
    Commute (T.ιConnection v) (T.ιConnection w) :=
  LocalFieldAlgebra.ιConnection_commute (Ef := T.FermionGenerators)
    (Eb := T.BosonGenerators) (EA := GaugeBoson.JetComponentSpace 𝔤) v w

variable (T)

/-!

## D. Realizations of the datum

-/

/-- A compatible realization of the datum in an algebra `B`, which is not assumed
  commutative. It consists of one linear map per fermionic species, one per bosonic
  species and one real-linear map on the connection generators, subject to exactly the
  statistics of section C.2. The algebra map it induces is `SpeciesAssignment.lift`, of
  type `T.LocalAlgebra →ₐ[ℂ] B`. -/
abbrev Assignment (B : Type*) [Ring B] [Algebra ℂ B] : Type _ :=
  SpeciesAssignment T.FermionValue T.BosonValue (GaugeBoson.JetComponentSpace 𝔤) B

variable {T} {B : Type*} [Ring B] [Algebra ℂ B] (d : T.Assignment B)

/-!

### D.1. The induced algebra homomorphism

-/

@[simp]
lemma lift_ιFermion (i : T.FermionSpecies) (x : JetComponentSpace (T.FermionValue i)) :
    d.lift (T.ιFermion i x) = d.fermion i x :=
  d.lift_ιFermionSpecies i x

@[simp]
lemma lift_ιBoson (j : T.BosonSpecies) (y : JetComponentSpace (T.BosonValue j)) :
    d.lift (T.ιBoson j y) = d.boson j y :=
  d.lift_ιBosonSpecies j y

@[simp]
lemma lift_ιConnection (v : GaugeBoson.JetComponentSpace 𝔤) :
    d.lift (T.ιConnection v) = d.connection v :=
  d.lift_ιConnection v

/-!

### D.2. Uniqueness

-/

/-- Two algebra maps out of `J(T)` are equal as soon as they agree on the generators of
  every species and on the connection generators. -/
lemma algHom_ext {Φ Ψ : T.LocalAlgebra →ₐ[ℂ] B}
    (hf : ∀ i x, Φ (T.ιFermion i x) = Ψ (T.ιFermion i x))
    (hb : ∀ j y, Φ (T.ιBoson j y) = Ψ (T.ιBoson j y))
    (ha : ∀ v, Φ (T.ιConnection v) = Ψ (T.ιConnection v)) : Φ = Ψ :=
  SpeciesAssignment.algHom_ext (Vf := T.FermionValue) (Vb := T.BosonValue)
    (EA := GaugeBoson.JetComponentSpace 𝔤) hf hb ha

/-- The realization arrow of the datum. A compatible realization of the generators in an
  arbitrary, in particular noncommutative, complex algebra `B` extends to one and only one
  complex algebra homomorphism `J(T) →ₐ[ℂ] B`. Injectivity is neither claimed nor wanted,
  since a realization may identify local expressions. -/
lemma existsUnique_algHom :
    ∃! Φ : T.LocalAlgebra →ₐ[ℂ] B,
      (∀ i x, Φ (T.ιFermion i x) = d.fermion i x) ∧
        (∀ j y, Φ (T.ιBoson j y) = d.boson j y) ∧
          (∀ v, Φ (T.ιConnection v) = d.connection v) :=
  d.existsUnique_algHom

variable (T)

/-!

## E. The transformation data on the generator spaces

The datum supplies, per species, a Lorentz representation and a fibrewise action of the
gauge jets. Both land on the generator spaces species by species, so both are assembled by
`SpeciesComponentSpace.rep`. Nothing here asserts that the two actions commute, since
Lorentz transformations act on nonconstant gauge jets, and nothing extends them to the
algebra `J(T)`.

### E.1. The Lorentz action

-/

/-- The Lorentz action on the fermionic generator space, acting on each species through
  the Lorentz representation of its matter field. -/
noncomputable def repLorentzFermion : Representation ℂ SL(2,ℂ) T.FermionGenerators :=
  SpeciesComponentSpace.rep T.FermionValue fun i =>
    JetComponentSpace.repLorentzGroup (T.fermion i).repLorentz

/-- The Lorentz action on the bosonic generator space. -/
noncomputable def repLorentzBoson : Representation ℂ SL(2,ℂ) T.BosonGenerators :=
  SpeciesComponentSpace.rep T.BosonValue fun j =>
    JetComponentSpace.repLorentzGroup (T.boson j).repLorentz

variable {T}

@[simp]
lemma repLorentzFermion_inclFermion (Λ : SL(2,ℂ)) (i : T.FermionSpecies)
    (x : JetComponentSpace (T.FermionValue i)) :
    T.repLorentzFermion Λ (T.inclFermion i x)
      = T.inclFermion i (JetComponentSpace.repLorentzGroup (T.fermion i).repLorentz Λ x) :=
  SpeciesComponentSpace.rep_incl _ Λ i x

@[simp]
lemma repLorentzBoson_inclBoson (Λ : SL(2,ℂ)) (j : T.BosonSpecies)
    (y : JetComponentSpace (T.BosonValue j)) :
    T.repLorentzBoson Λ (T.inclBoson j y)
      = T.inclBoson j (JetComponentSpace.repLorentzGroup (T.boson j).repLorentz Λ y) :=
  SpeciesComponentSpace.rep_incl _ Λ j y

variable (T)

/-!

### E.2. The jet gauge action

-/

/-- The action of the jet gauge group on the fermionic generator space, acting on each
  species through the fibrewise jet action of its matter field. Both the fibrewise
  hypothesis and the finite dimensionality of the value space that
  `JetComponentSpace.repJet` needs are already fields of `MatterField`. -/
noncomputable def repJetFermion : Representation ℂ G T.FermionGenerators :=
  SpeciesComponentSpace.rep T.FermionValue fun i =>
    JetComponentSpace.repJet (T.fermion i).repJet (T.fermion i).repJet_smul

/-- The action of the jet gauge group on the bosonic generator space. -/
noncomputable def repJetBoson : Representation ℂ G T.BosonGenerators :=
  SpeciesComponentSpace.rep T.BosonValue fun j =>
    JetComponentSpace.repJet (T.boson j).repJet (T.boson j).repJet_smul

variable {T}

@[simp]
lemma repJetFermion_inclFermion (U : G) (i : T.FermionSpecies)
    (x : JetComponentSpace (T.FermionValue i)) :
    T.repJetFermion U (T.inclFermion i x)
      = T.inclFermion i
        (JetComponentSpace.repJet (T.fermion i).repJet (T.fermion i).repJet_smul U x) :=
  SpeciesComponentSpace.rep_incl _ U i x

@[simp]
lemma repJetBoson_inclBoson (U : G) (j : T.BosonSpecies)
    (y : JetComponentSpace (T.BosonValue j)) :
    T.repJetBoson U (T.inclBoson j y)
      = T.inclBoson j
        (JetComponentSpace.repJet (T.boson j).repJet (T.boson j).repJet_smul U y) :=
  SpeciesComponentSpace.rep_incl _ U j y

variable (T)

/-!

### E.3. The mass weights

-/

/-- The mass-weight scaling on the fermionic generator space, with the weight of each
  species taken from its matter field. Species of different weight scale differently,
  which is the property the direct-sum generator space was chosen to have. -/
noncomputable def massWeightScaleFermion (c : ℂ) :
    T.FermionGenerators →ₗ[ℂ] T.FermionGenerators :=
  SpeciesComponentSpace.massWeightScale T.FermionValue
    (fun i => (T.fermion i).massWeight) c

/-- The mass-weight scaling on the bosonic generator space. -/
noncomputable def massWeightScaleBoson (c : ℂ) :
    T.BosonGenerators →ₗ[ℂ] T.BosonGenerators :=
  SpeciesComponentSpace.massWeightScale T.BosonValue (fun j => (T.boson j).massWeight) c

variable {T}

/-- On the summand of a fermionic species the scaling is that species' own mass-weight
  scaling, with the weight recorded in its matter field. -/
@[simp]
lemma massWeightScaleFermion_inclFermion (c : ℂ) (i : T.FermionSpecies)
    (x : JetComponentSpace (T.FermionValue i)) :
    T.massWeightScaleFermion c (T.inclFermion i x)
      = T.inclFermion i
        (JetComponentSpace.massWeightScale (T.fermion i).massWeight c x) :=
  SpeciesComponentSpace.massWeightScale_incl _ c i x

/-- On the summand of a bosonic species the scaling is that species' own mass-weight
  scaling. -/
@[simp]
lemma massWeightScaleBoson_inclBoson (c : ℂ) (j : T.BosonSpecies)
    (y : JetComponentSpace (T.BosonValue j)) :
    T.massWeightScaleBoson c (T.inclBoson j y)
      = T.inclBoson j (JetComponentSpace.massWeightScale (T.boson j).massWeight c y) :=
  SpeciesComponentSpace.massWeightScale_incl _ c j y

/-- A component function `∂_s ψ_α` of a fermionic species scales by `c ^ (w + 2 |s|)`,
  where `w` is the mass weight of that species. There is one factor of `c` per unit of
  mass dimension of the field and two per derivative. -/
lemma massWeightScaleFermion_inclFermion_basis_tmul (c : ℂ) (i : T.FermionSpecies)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.FermionValue i)) :
    T.massWeightScaleFermion c (T.inclFermion i
        ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace (T.FermionValue i)))
      = c ^ ((T.fermion i).massWeight + 2 * Multiset.card s) • T.inclFermion i
          ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace (T.FermionValue i)) :=
  SpeciesComponentSpace.massWeightScale_incl_basis_tmul _ c i s φ

/-- A component function `∂_s φ_α` of a bosonic species scales by `c ^ (w + 2 |s|)`
  with that species' own weight `w`. -/
lemma massWeightScaleBoson_inclBoson_basis_tmul (c : ℂ) (j : T.BosonSpecies)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.BosonValue j)) :
    T.massWeightScaleBoson c (T.inclBoson j
        ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace (T.BosonValue j)))
      = c ^ ((T.boson j).massWeight + 2 * Multiset.card s) • T.inclBoson j
          ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace (T.BosonValue j)) :=
  SpeciesComponentSpace.massWeightScale_incl_basis_tmul _ c j s φ

end GaugeFieldData
