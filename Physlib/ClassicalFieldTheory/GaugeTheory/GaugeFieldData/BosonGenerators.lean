/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeFieldData.BosonMatterField
/-!
# The bosonic generators of a gauge theory

## i. Overview

The bosonic species of a `GaugeFieldData` — its scalars — each carry a component space, the
span of the symbols `∂_s φ_α` and their conjugates for that multiplet. This file assembles them into
the **bosonic generator space** of the theory,

`T.BosonGenerators = ⨁ i, JetComponentSpace (T.boson i).V`,

together with the transformation data the species supply: the Lorentz action, the action of
the jets of gauge transformations, and the mass-weight scaling, each assembled species by
species. These are the bosonic generators on which
`GaugeFieldData.LocalFieldAlgebra` builds its symmetric algebra. The gauge bosons are not
among them: their generator space is fixed by the gauge algebra alone.

The direct sum, rather than a single component space on the product of the value spaces, is
what lets the species carry different mass weights: the scaling of one component space is
natural in the value space and so cannot tell the species apart.

Section C shows what happens when the species *do* share a weight, which is the case in any
theory whose scalars all have the same mass dimension. A physicist does not write each
multiplet with its own component space; they write one scalar field `φ` valued in the whole
bosonic module and take its component functions `∂_s φ_α`, a single `JetComponentSpace`
whose target index `α` runs over everything. For the Standard Model, with its one Higgs
doublet, the two are trivially the same; for a larger scalar sector they are not.

The two descriptions agree: there is an isomorphism

`T.BosonGenerators ≃ₗ[ℂ] JetComponentSpace T.BosonModule`,

under which the summand of a species is the pullback along the projection onto that
species, `bosonGeneratorsEquiv_inclBoson`. So the generators of one multiplet sit inside
the generators of the whole scalar field exactly as its target components sit inside the
bosonic module. The isomorphism is not merely one of vector spaces: it intertwines the
Lorentz action and the mass-weight scaling with those of the single matter field
`T.bosonMatterField w h`, the shared weight `w` being needed for the second of these and
for nothing else.

The underlying identification is `JetComponentSpace.piEquiv`, composed with the
identification of a direct sum over a finite index with the product.

## ii. Key results

- `GaugeFieldData.BosonGenerators` : the bosonic generator space.
- `GaugeFieldData.inclBoson` : the inclusion of the component space of one species.
- `GaugeFieldData.assembleBoson`, `GaugeFieldData.bosonGenerators_hom_ext` : the assembly of
  a species-wise family of linear maps, and the fact that it is the only such map.
- `GaugeFieldData.repLorentzBoson`, `GaugeFieldData.repJetBoson` : the Lorentz and jet
  gauge actions assembled on it.
- `GaugeFieldData.massWeightScaleBoson` : the mass-weight scaling carrying the weight of
  each species.
- `GaugeFieldData.bosonGeneratorsEquiv` : with one shared weight, the generator space is
  the component space of the bosonic matter field.
- `GaugeFieldData.bosonGeneratorsEquiv_inclBoson` : a species sits inside it as the
  pullback along the projection onto that species.
- `GaugeFieldData.bosonGeneratorsEquiv_repLorentzBoson`,
  `GaugeFieldData.bosonGeneratorsEquiv_massWeightScaleBoson` : the identification
  carries the Lorentz action and the mass-weight scaling across.

## iii. Table of contents

- A. The bosonic generator space and its species assembly
- B. The transformation data on the generator space
  - B.1. The Lorentz action
  - B.2. The jet gauge action
  - B.3. The mass weights
- C. The bosonic generators as one component space
  - C.1. The species as pullbacks
  - C.2. The identification of the transformation data

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct DirectSum

namespace GaugeFieldData

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G 𝔤 G₀ 𝔤J} (T : GaugeFieldData jets)

/-!

## A. The bosonic generator space and its species assembly

-/

/-- The bosonic generator space of the datum, holding the component functions `∂_s φ_α`
  and their conjugates of every bosonic species at once, as a direct sum over the species.
  A component function of the theory is a finitely supported family of component functions
  of the species.

  The direct sum, rather than a single component space on the product of the value spaces,
  is what lets the species carry different mass weights: the scaling of one component space
  is natural in the value space — `JetComponentSpace.comap_comp_massWeightScale` — and so
  cannot tell the species apart. When the weights do agree the two descriptions coincide,
  which is section C below. -/
abbrev BosonGenerators : Type := ⨁ i, JetComponentSpace (T.BosonValue i)

/-- The inclusion of the component space of one bosonic species into the bosonic generator
  space. -/
abbrev inclBoson (i : T.BosonSpecies) :
    JetComponentSpace (T.BosonValue i) →ₗ[ℂ] T.BosonGenerators :=
  DirectSum.lof ℂ T.BosonSpecies (fun i => JetComponentSpace (T.BosonValue i)) i

section Assemble

variable {N : Type*} [AddCommMonoid N] [Module ℂ N]

/-- The assembly of a species-wise family of linear maps out of the bosonic generator space
  into a common target. -/
abbrev assembleBoson (f : ∀ i, JetComponentSpace (T.BosonValue i) →ₗ[ℂ] N) :
    T.BosonGenerators →ₗ[ℂ] N :=
  DirectSum.toModule ℂ T.BosonSpecies N f

variable {T}

lemma assembleBoson_inclBoson (f : ∀ i, JetComponentSpace (T.BosonValue i) →ₗ[ℂ] N)
    (i : T.BosonSpecies) (x : JetComponentSpace (T.BosonValue i)) :
    T.assembleBoson f (T.inclBoson i x) = f i x :=
  DirectSum.toModule_lof (M := fun i => JetComponentSpace (T.BosonValue i)) ℂ i x

/-- Two linear maps out of the bosonic generator space agreeing on every species are
  equal. -/
lemma bosonGenerators_hom_ext {F F' : T.BosonGenerators →ₗ[ℂ] N}
    (h : ∀ i x, F (T.inclBoson i x) = F' (T.inclBoson i x)) : F = F' :=
  DirectSum.linearMap_ext ℂ fun i => LinearMap.ext (h i)

variable (T)

end Assemble

/-!

## B. The transformation data on the generator space

The datum supplies, per species, a Lorentz representation and a fibrewise action of the
gauge jets. Both act on the generator space one summand at a time, so both are assembled
from the species-wise actions and the representation laws follow from
`bosonGenerators_hom_ext` alone, with no relation between the species used. Nothing here
asserts that the two actions commute, since Lorentz transformations act on nonconstant
gauge jets, and nothing extends them to the algebra `J(T)`.

### B.1. The Lorentz action

-/

/-- The Lorentz action on the bosonic generator space, acting on each species through the
  Lorentz representation of its matter field. -/
noncomputable def repLorentzBoson : Representation ℂ SL(2,ℂ) T.BosonGenerators where
  toFun Λ := T.assembleBoson fun i =>
    (T.inclBoson i).comp (JetComponentSpace.repLorentzGroup (T.boson i).repLorentz Λ)
  map_one' := bosonGenerators_hom_ext fun i x => by simp
  map_mul' Λ Λ' := bosonGenerators_hom_ext fun i x => by simp

variable {T}

@[simp]
lemma repLorentzBoson_inclBoson (Λ : SL(2,ℂ)) (i : T.BosonSpecies)
    (x : JetComponentSpace (T.BosonValue i)) :
    T.repLorentzBoson Λ (T.inclBoson i x)
      = T.inclBoson i (JetComponentSpace.repLorentzGroup (T.boson i).repLorentz Λ x) :=
  assembleBoson_inclBoson _ i x

variable (T)

/-!

### B.2. The jet gauge action

-/

/-- The action of the jet gauge group on the bosonic generator space, acting on each
  species through the fibrewise jet action of its matter field. Both the fibrewise
  hypothesis and the finite dimensionality of the value space that
  `JetComponentSpace.repJet` needs are already fields of `MatterField`. -/
noncomputable def repJetBoson : Representation ℂ G T.BosonGenerators where
  toFun U := T.assembleBoson fun i => (T.inclBoson i).comp
    (JetComponentSpace.repJet (T.boson i).repJet (T.boson i).repJet_smul U)
  map_one' := bosonGenerators_hom_ext fun i x => by simp
  map_mul' U W := bosonGenerators_hom_ext fun i x => by simp

variable {T}

@[simp]
lemma repJetBoson_inclBoson (U : G) (i : T.BosonSpecies)
    (x : JetComponentSpace (T.BosonValue i)) :
    T.repJetBoson U (T.inclBoson i x)
      = T.inclBoson i
        (JetComponentSpace.repJet (T.boson i).repJet (T.boson i).repJet_smul U x) :=
  assembleBoson_inclBoson _ i x

variable (T)

/-!

### B.3. The mass weights

The mass weight is a property of a species, not of the theory, a fermion carrying weight
`3` and a scalar weight `2`. The generator space records one weight per species, and the
scaling acts on the summand of a species through that species' weight alone.

-/

/-- The mass-weight scaling on the bosonic generator space, with the weight of each species
  taken from its matter field. Species of different weight scale differently, which is the
  property the direct-sum generator space was chosen to have. -/
noncomputable def massWeightScaleBoson (c : ℂ) :
    T.BosonGenerators →ₗ[ℂ] T.BosonGenerators :=
  T.assembleBoson fun i =>
    (T.inclBoson i).comp (JetComponentSpace.massWeightScale (T.boson i).massWeight c)

variable {T}

/-- On the summand of a species the scaling is that species' own mass-weight scaling, with
  the weight recorded in its matter field. -/
@[simp]
lemma massWeightScaleBoson_inclBoson (c : ℂ) (i : T.BosonSpecies)
    (x : JetComponentSpace (T.BosonValue i)) :
    T.massWeightScaleBoson c (T.inclBoson i x)
      = T.inclBoson i
        (JetComponentSpace.massWeightScale (T.boson i).massWeight c x) :=
  assembleBoson_inclBoson _ i x

/-- A component function `∂_s φ_α` of a species scales by `c ^ (w + 2 |s|)`, where `w` is
  the mass weight of that species. There is one factor of `c` per unit of mass dimension of
  the field and two per derivative. -/
lemma massWeightScaleBoson_inclBoson_basis_tmul (c : ℂ) (i : T.BosonSpecies)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.BosonValue i)) :
    T.massWeightScaleBoson c (T.inclBoson i
        ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace (T.BosonValue i)))
      = c ^ ((T.boson i).massWeight + 2 * Multiset.card s) • T.inclBoson i
          ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace (T.BosonValue i)) := by
  rw [massWeightScaleBoson_inclBoson, ← LinearMap.map_smul]
  refine congrArg _ (Prod.ext ?_ ?_)
  · exact JetComponentSpace.massWeightScale_fst_basis_tmul (T.boson i).massWeight c s φ 0
  · simp

/-- The conjugate component functions of a species scale with the same weight as its
  unconjugated ones. -/
lemma massWeightScaleBoson_inclBoson_basis_tmul_conj (c : ℂ) (i : T.BosonSpecies)
    (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.BosonValue i))) :
    T.massWeightScaleBoson c (T.inclBoson i
        ((0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) : JetComponentSpace (T.BosonValue i)))
      = c ^ ((T.boson i).massWeight + 2 * Multiset.card s) • T.inclBoson i
          ((0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) : JetComponentSpace (T.BosonValue i)) := by
  rw [massWeightScaleBoson_inclBoson, ← LinearMap.map_smul]
  refine congrArg _ (Prod.ext ?_ ?_)
  · simp
  · simp only [JetComponentSpace.massWeightScale_snd, Prod.smul_snd,
      TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      DerivAlgebraComplex.gradeScale_basis, LinearMap.id_apply, TensorProduct.smul_tmul',
      ← pow_mul, ← smul_assoc, smul_eq_mul, ← pow_add, mul_comm 2 (Multiset.card s)]

variable (T)

/-!

## C. The bosonic generators as one component space

-/

/-- **The bosonic generator space is the component space of the bosonic module.** The
  direct sum over the species of their component spaces is, the species type being finite,
  the same thing as the space of component functions `∂_s φ_α` of a single field valued in
  the whole bosonic module — the presentation of the boson content used in writing a
  theory down. -/
noncomputable def bosonGeneratorsEquiv :
    T.BosonGenerators ≃ₗ[ℂ] JetComponentSpace T.BosonModule :=
  (DirectSum.linearEquivFunOnFintype ℂ T.BosonSpecies
      fun i => JetComponentSpace (T.BosonValue i)).trans
    (JetComponentSpace.piEquiv T.BosonValue).symm

/-!

### C.1. The species as pullbacks

-/

variable {T}

/-- **A species sits inside the bosonic generators as the pullback along the projection
  onto it.** A component function `∂_s φ_α` of the multiplet `i` becomes the component
  function of the whole scalar field whose target covector is supported on that
  multiplet. -/
@[simp]
lemma bosonGeneratorsEquiv_inclBoson (i : T.BosonSpecies)
    (x : JetComponentSpace (T.BosonValue i)) :
    T.bosonGeneratorsEquiv (T.inclBoson i x)
      = JetComponentSpace.comap (T.projBosonValue i) x := by
  rw [bosonGeneratorsEquiv, LinearEquiv.trans_apply,
    show (DirectSum.linearEquivFunOnFintype ℂ T.BosonSpecies
        fun i => JetComponentSpace (T.BosonValue i)) (T.inclBoson i x)
      = Pi.single i x from DirectSum.linearEquivFunOnFintype_lof
      (M := fun i => JetComponentSpace (T.BosonValue i)) ℂ i x,
    JetComponentSpace.piEquiv_symm_single]

/-- Two linear maps out of the component space of the bosonic module agree as soon as they
  agree on every species, the species pullbacks spanning it. This is the counterpart, on
  the single-field side of the identification, of `bosonGenerators_hom_ext`. -/
lemma bosonModuleComponents_hom_ext {N : Type} [AddCommGroup N] [Module ℂ N]
    {F F' : JetComponentSpace T.BosonModule →ₗ[ℂ] N}
    (h : ∀ i x, F (JetComponentSpace.comap (T.projBosonValue i) x)
      = F' (JetComponentSpace.comap (T.projBosonValue i) x)) : F = F' := by
  have key : F.comp T.bosonGeneratorsEquiv.toLinearMap
      = F'.comp T.bosonGeneratorsEquiv.toLinearMap :=
    bosonGenerators_hom_ext fun i x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        bosonGeneratorsEquiv_inclBoson]
      exact h i x
  refine LinearMap.ext fun z => ?_
  simpa using LinearMap.congr_fun key (T.bosonGeneratorsEquiv.symm z)

/-!

### C.2. The identification of the transformation data

-/

/-- **The identification is Lorentz-equivariant.** The species-diagonal Lorentz action on
  the generator space is the Lorentz action on the component functions of the single
  scalar field: each species is a subrepresentation of the bosonic module, so pulling
  back along the projection onto it commutes with the two actions. No common mass weight
  is needed here — the Lorentz action does not see it. -/
lemma bosonGeneratorsEquiv_repLorentzBoson (Λ : SL(2,ℂ)) (y : T.BosonGenerators) :
    T.bosonGeneratorsEquiv (T.repLorentzBoson Λ y)
      = JetComponentSpace.repLorentzGroup T.repLorentzBosonModule Λ
        (T.bosonGeneratorsEquiv y) := by
  have key : T.bosonGeneratorsEquiv.toLinearMap.comp (T.repLorentzBoson Λ)
      = (JetComponentSpace.repLorentzGroup T.repLorentzBosonModule Λ).comp
        T.bosonGeneratorsEquiv.toLinearMap := by
    refine bosonGenerators_hom_ext fun i x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      repLorentzBoson_inclBoson, bosonGeneratorsEquiv_inclBoson,
      bosonGeneratorsEquiv_inclBoson]
    exact LinearMap.congr_fun (JetComponentSpace.comap_comp_repLorentzGroup
      T.repLorentzBosonModule (T.boson i).repLorentz
      (T.projBosonValue i) (fun _ => LinearMap.ext fun _ => rfl) Λ) x
  exact LinearMap.congr_fun key y

/-- **The identification carries the species-wise mass-weight scaling to a single
  scaling.** With one weight `w` shared by every bosonic species, the scaling that acts
  on each species through its own weight is the scaling of weight `w` on the component
  functions of the one scalar field: `comap` is natural in the value space, so it does
  not see which species a generator came from. -/
lemma bosonGeneratorsEquiv_massWeightScaleBoson (w : ℕ)
    (h : ∀ i, (T.boson i).massWeight = w) (c : ℂ) (y : T.BosonGenerators) :
    T.bosonGeneratorsEquiv (T.massWeightScaleBoson c y)
      = JetComponentSpace.massWeightScale w c (T.bosonGeneratorsEquiv y) := by
  have key : T.bosonGeneratorsEquiv.toLinearMap.comp (T.massWeightScaleBoson c)
      = (JetComponentSpace.massWeightScale w c).comp
        T.bosonGeneratorsEquiv.toLinearMap := by
    refine bosonGenerators_hom_ext fun i x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      massWeightScaleBoson_inclBoson, bosonGeneratorsEquiv_inclBoson,
      bosonGeneratorsEquiv_inclBoson, h i]
    exact LinearMap.congr_fun (JetComponentSpace.comap_comp_massWeightScale
      (T.projBosonValue i) w c) x
  exact LinearMap.congr_fun key y

end GaugeFieldData
