/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeFieldData.BosonMatterField
public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.JetComponentSpace.GaugeAction
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
- `GaugeFieldData.jetDerivBoson` : the ordinary derivative shift on the generator space.
- `GaugeFieldData.bosonGeneratorsEquiv` : with one shared weight, the generator space is
  the component space of the bosonic matter field.
- `GaugeFieldData.bosonGeneratorsEquiv_inclBoson` : a species sits inside it as the
  pullback along the projection onto that species.
- `GaugeFieldData.bosonGeneratorsEquiv_repLorentzBoson`,
  `GaugeFieldData.bosonGeneratorsEquiv_repJetBoson`,
  `GaugeFieldData.bosonGeneratorsEquiv_massWeightScaleBoson`,
  `GaugeFieldData.bosonGeneratorsEquiv_jetDerivBoson` : the identification carries the
  Lorentz action, the jet gauge action, the mass-weight scaling and the derivative shift
  across.

## iii. Table of contents

- A. The bosonic generator space and its species assembly
- B. The transformation data on the generator space
  - B.1. The Lorentz action
  - B.2. The jet gauge action
  - B.3. The mass weights
  - B.4. The ordinary derivative
- C. The bosonic generators as one component space
  - C.1. The species as pullbacks
  - C.2. The identification of the transformation data

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct DirectSum

namespace GaugeFieldData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} (T : GaugeFieldData jets)

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
  which is section C below.

  This `def` and its explicit instances reduce instance-term expansion in the symmetric
  algebra and tensor products built on it. Use the inclusion, assembly and extensionality
  API in downstream proofs; unfold the direct-sum representation explicitly when necessary. -/
def BosonGenerators : Type := ⨁ i, JetComponentSpace (T.boson i)

instance : AddCommGroup T.BosonGenerators :=
  inferInstanceAs (AddCommGroup (⨁ i, JetComponentSpace (T.boson i)))

instance : Module ℂ T.BosonGenerators :=
  inferInstanceAs (Module ℂ (⨁ i, JetComponentSpace (T.boson i)))

/-- The inclusion of the component space of one bosonic species into the bosonic generator
  space. -/
def inclBoson (i : T.BosonSpecies) :
    JetComponentSpace (T.boson i) →ₗ[ℂ] T.BosonGenerators :=
  DirectSum.lof ℂ T.BosonSpecies (fun i => JetComponentSpace (T.boson i)) i

section Assemble

variable {N : Type*} [AddCommMonoid N] [Module ℂ N]

/-- The assembly of a species-wise family of linear maps out of the bosonic generator space
  into a common target. -/
def assembleBoson (f : ∀ i, JetComponentSpace (T.boson i) →ₗ[ℂ] N) :
    T.BosonGenerators →ₗ[ℂ] N :=
  DirectSum.toModule ℂ T.BosonSpecies N f

variable {T}

@[simp]
lemma assembleBoson_inclBoson (f : ∀ i, JetComponentSpace (T.boson i) →ₗ[ℂ] N)
    (i : T.BosonSpecies) (x : JetComponentSpace (T.boson i)) :
    T.assembleBoson f (T.inclBoson i x) = f i x :=
  DirectSum.toModule_lof (M := fun i => JetComponentSpace (T.boson i)) ℂ i x

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
    (T.inclBoson i).comp (JetComponentSpace.repLorentzGroup (T.boson i) Λ)
  map_one' := bosonGenerators_hom_ext fun i x => by simp
  map_mul' Λ Λ' := bosonGenerators_hom_ext fun i x => by simp

variable {T}

@[simp]
lemma repLorentzBoson_inclBoson (Λ : SL(2,ℂ)) (i : T.BosonSpecies)
    (x : JetComponentSpace (T.boson i)) :
    T.repLorentzBoson Λ (T.inclBoson i x)
      = T.inclBoson i (JetComponentSpace.repLorentzGroup (T.boson i) Λ x) :=
  assembleBoson_inclBoson _ i x

variable (T)

/-!

### B.2. The jet gauge action

-/

/-- The action of the jet gauge group on the bosonic generator space, acting on each
  species through the fibrewise jet action of its matter field. Both the fibrewise
  hypothesis and the finite dimensionality of the value space that
  `JetComponentSpace.repJet` needs are already fields of `MatterField`. -/
noncomputable def repJetBoson : Representation ℂ GJ T.BosonGenerators where
  toFun U := T.assembleBoson fun i => (T.inclBoson i).comp
    (JetComponentSpace.repJet (T.boson i) U)
  map_one' := bosonGenerators_hom_ext fun i x => by simp
  map_mul' U W := bosonGenerators_hom_ext fun i x => by simp

variable {T}

@[simp]
lemma repJetBoson_inclBoson (U : GJ) (i : T.BosonSpecies)
    (x : JetComponentSpace (T.boson i)) :
    T.repJetBoson U (T.inclBoson i x)
      = T.inclBoson i
        (JetComponentSpace.repJet (T.boson i) U x) :=
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
    (x : JetComponentSpace (T.boson i)) :
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
        ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace (T.boson i)))
      = c ^ ((T.boson i).massWeight + 2 * Multiset.card s) • T.inclBoson i
          ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) : JetComponentSpace (T.boson i)) := by
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
        ((0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) : JetComponentSpace (T.boson i)))
      = c ^ ((T.boson i).massWeight + 2 * Multiset.card s) • T.inclBoson i
          ((0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) : JetComponentSpace (T.boson i)) := by
  rw [massWeightScaleBoson_inclBoson, ← LinearMap.map_smul]
  refine congrArg _ (Prod.ext ?_ ?_)
  · simp
  · simp only [JetComponentSpace.massWeightScale_snd, Prod.smul_snd,
      TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      DerivAlgebraComplex.gradeScale_basis, LinearMap.id_apply, TensorProduct.smul_tmul',
      ← pow_mul, ← smul_assoc, smul_eq_mul, ← pow_add, mul_comm 2 (Multiset.card s)]

variable (T)

/-!

### B.4. The ordinary derivative

The formal total derivative shifts the derivative label of a component function,
`∂_s φ_α ↦ ∂_{s + {μ}} φ_α`. Unlike the two actions it takes no data from the species at
all, the label being blind to the value space, so on the generator space it too is
species-diagonal and the same assembly serves. It is recorded here so that the generator
space carries every operation the local field algebra is built from.

-/

/-- The ordinary derivative shift on the bosonic generator space, acting on each species'
  component functions by appending `∂_μ` to the derivative label. -/
noncomputable def jetDerivBoson (μ : Fin 1 ⊕ Fin 3) :
    T.BosonGenerators →ₗ[ℂ] T.BosonGenerators :=
  T.assembleBoson fun i => (T.inclBoson i).comp (JetComponentSpace.jetDeriv μ)

variable {T}

@[simp]
lemma jetDerivBoson_inclBoson (μ : Fin 1 ⊕ Fin 3) (i : T.BosonSpecies)
    (x : JetComponentSpace (T.boson i)) :
    T.jetDerivBoson μ (T.inclBoson i x)
      = T.inclBoson i (JetComponentSpace.jetDeriv μ x) :=
  assembleBoson_inclBoson _ i x

/-- Mixed partials agree on the bosonic generator space, because they do on each
  species. -/
lemma jetDerivBoson_comm (μ ν : Fin 1 ⊕ Fin 3) :
    (T.jetDerivBoson μ).comp (T.jetDerivBoson ν)
      = (T.jetDerivBoson ν).comp (T.jetDerivBoson μ) :=
  bosonGenerators_hom_ext fun i x => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, jetDerivBoson_inclBoson,
      jetDerivBoson_inclBoson, jetDerivBoson_inclBoson, jetDerivBoson_inclBoson]
    exact congrArg (T.inclBoson i)
      (LinearMap.congr_fun (JetComponentSpace.jetDeriv_comm (M := T.boson i) μ ν) x)

/-- The derivative shift is a Lorentz vector on the bosonic generator space: it is one
  on each species, and both operations are species-diagonal. -/
lemma repLorentzBoson_jetDerivBoson (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (x : T.BosonGenerators) :
    T.repLorentzBoson Λ (T.jetDerivBoson μ x)
      = ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
          T.jetDerivBoson a (T.repLorentzBoson Λ x) := by
  have key : (T.repLorentzBoson Λ).comp (T.jetDerivBoson μ)
      = ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
          (T.jetDerivBoson a).comp (T.repLorentzBoson Λ) :=
    bosonGenerators_hom_ext fun i y => by
      rw [LinearMap.comp_apply, jetDerivBoson_inclBoson, repLorentzBoson_inclBoson,
        JetComponentSpace.repLorentzGroup_jetDeriv, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, LinearMap.smul_apply, LinearMap.comp_apply,
        repLorentzBoson_inclBoson, jetDerivBoson_inclBoson]
  rw [← LinearMap.comp_apply, key, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun a _ => by rw [LinearMap.smul_apply, LinearMap.comp_apply]

/-- The derivative carries mass weight two on the bosonic generator space, whatever the
  weights of the species: the shift adds two units of mass dimension to every component
  function alike. -/
lemma massWeightScaleBoson_jetDerivBoson (c : ℂ) (μ : Fin 1 ⊕ Fin 3) :
    (T.massWeightScaleBoson c).comp (T.jetDerivBoson μ)
      = c ^ 2 • (T.jetDerivBoson μ).comp (T.massWeightScaleBoson c) :=
  bosonGenerators_hom_ext fun i x => by
    rw [LinearMap.comp_apply, jetDerivBoson_inclBoson, massWeightScaleBoson_inclBoson,
      LinearMap.smul_apply, LinearMap.comp_apply, massWeightScaleBoson_inclBoson,
      jetDerivBoson_inclBoson, ← map_smul]
    exact congrArg (T.inclBoson i) (LinearMap.congr_fun
      (JetComponentSpace.massWeightScale_jetDeriv (T.boson i).massWeight c μ) x)

variable (T)

/-!

## C. The bosonic generators as one component space

-/

/-- **The bosonic generator space is the component space of the bosonic matter field.** The
  direct sum over the species of their component spaces is, the species type being finite,
  the same thing as the space of component functions of the single field
  `T.bosonMatterField w h` — the presentation of the boson content used in writing a theory
  down. The shared weight `w` enters only because a component space is now taken of a
  matter field, and the only matter field on `T.BosonModule` is that one; the underlying
  identification does not use it. -/
noncomputable def bosonGeneratorsEquiv (w : ℕ) (h : ∀ i, (T.boson i).massWeight = w) :
    T.BosonGenerators ≃ₗ[ℂ] JetComponentSpace (T.bosonMatterField w h) :=
  (DirectSum.linearEquivFunOnFintype ℂ T.BosonSpecies
      fun i => JetComponentSpace (T.boson i)).trans
    (MatterField.jetComponentSpacePiEquiv T.boson w h).symm

/-!

### C.1. The species as pullbacks

-/

variable {T}

/-- **A species sits inside the bosonic generators as the pullback along the projection
  onto it.** A component function of the multiplet `i` becomes the component function of
  the whole field whose target covector is supported on that multiplet. -/
@[simp]
lemma bosonGeneratorsEquiv_inclBoson (w : ℕ) (h : ∀ i, (T.boson i).massWeight = w)
    (i : T.BosonSpecies) (x : JetComponentSpace (T.boson i)) :
    T.bosonGeneratorsEquiv w h (T.inclBoson i x)
      = JetComponentSpace.comap
        (T.projBosonField w h i) x := by
  have hlof : (DirectSum.linearEquivFunOnFintype ℂ T.BosonSpecies
      fun i => JetComponentSpace (T.boson i)) (T.inclBoson i x) = Pi.single i x :=
    DirectSum.linearEquivFunOnFintype_lof
      (M := fun i => JetComponentSpace (T.boson i)) ℂ i x
  show (MatterField.jetComponentSpacePiEquiv T.boson w h).symm
      ((DirectSum.linearEquivFunOnFintype ℂ T.BosonSpecies
        fun i => JetComponentSpace (T.boson i)) (T.inclBoson i x)) = _
  rw [hlof, MatterField.jetComponentSpacePiEquiv_symm_single]
  rfl

/-- Two linear maps out of the component space of the bosonic matter field agree as soon as
  they agree on every species, the species pullbacks spanning it. This is the counterpart,
  on the single-field side of the identification, of `bosonGenerators_hom_ext`. -/
lemma bosonFieldComponents_hom_ext {N : Type} [AddCommGroup N] [Module ℂ N]
    (w : ℕ) (h : ∀ i, (T.boson i).massWeight = w)
    {F F' : JetComponentSpace (T.bosonMatterField w h) →ₗ[ℂ] N}
    (hs : ∀ i x, F (JetComponentSpace.comap
        (T.projBosonField w h i) x)
      = F' (JetComponentSpace.comap
        (T.projBosonField w h i) x)) : F = F' := by
  have key : F.comp (T.bosonGeneratorsEquiv w h).toLinearMap
      = F'.comp (T.bosonGeneratorsEquiv w h).toLinearMap :=
    bosonGenerators_hom_ext fun i x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        bosonGeneratorsEquiv_inclBoson]
      exact hs i x
  refine LinearMap.ext fun z => ?_
  simpa using LinearMap.congr_fun key ((T.bosonGeneratorsEquiv w h).symm z)

/-!

### C.2. The identification of the transformation data

-/

/-- **The identification is Lorentz-equivariant.** The species-diagonal Lorentz action on
  the generator space is the Lorentz action on the component functions of the single field:
  each species is a subrepresentation of the bosonic matter field, so pulling back along the
  projection onto it commutes with the two actions. -/
lemma bosonGeneratorsEquiv_repLorentzBoson (w : ℕ) (h : ∀ i, (T.boson i).massWeight = w)
    (Λ : SL(2,ℂ)) (y : T.BosonGenerators) :
    T.bosonGeneratorsEquiv w h (T.repLorentzBoson Λ y)
      = JetComponentSpace.repLorentzGroup (T.bosonMatterField w h) Λ
        (T.bosonGeneratorsEquiv w h y) := by
  have key : (T.bosonGeneratorsEquiv w h).toLinearMap.comp (T.repLorentzBoson Λ)
      = (JetComponentSpace.repLorentzGroup (T.bosonMatterField w h) Λ).comp
        (T.bosonGeneratorsEquiv w h).toLinearMap := by
    refine bosonGenerators_hom_ext fun i x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      repLorentzBoson_inclBoson, bosonGeneratorsEquiv_inclBoson,
      bosonGeneratorsEquiv_inclBoson]
    exact LinearMap.congr_fun (JetComponentSpace.comap_comp_repLorentzGroup
      (T.projBosonField w h i)
      (fun _ => LinearMap.ext fun _ => rfl) Λ) x
  exact LinearMap.congr_fun key y

/-- The identification is equivariant for the jet gauge action. The species-diagonal
  action of the jets of gauge transformations on the generator space is the action on the
  component functions of the single boson field, for the same reason as in the fermionic
  case: each species is a subrepresentation of the bosonic module. The common mass weight
  enters only through the packaging of the bosonic module as a matter field; both halves
  of the component space, with every derivative label, are covered. -/
lemma bosonGeneratorsEquiv_repJetBoson (w : ℕ) (h : ∀ i, (T.boson i).massWeight = w)
    (U : GJ) (y : T.BosonGenerators) :
    T.bosonGeneratorsEquiv w h (T.repJetBoson U y)
      = JetComponentSpace.repJet (T.bosonMatterField w h) U
        (T.bosonGeneratorsEquiv w h y) := by
  have key : (T.bosonGeneratorsEquiv w h).toLinearMap.comp (T.repJetBoson U)
      = (JetComponentSpace.repJet (T.bosonMatterField w h) U).comp
        (T.bosonGeneratorsEquiv w h).toLinearMap := by
    refine bosonGenerators_hom_ext fun j x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      repJetBoson_inclBoson, bosonGeneratorsEquiv_inclBoson,
      bosonGeneratorsEquiv_inclBoson]
    exact LinearMap.congr_fun (JetComponentSpace.comap_comp_repJet
      (T.projBosonField w h j)
      (fun U' => lTensor_projBosonValue_repJetBosonModule j U') U) x
  exact LinearMap.congr_fun key y

/-- **The identification carries the species-wise mass-weight scaling to a single
  scaling.** With one weight `w` shared by every species, the scaling that acts on each
  species through its own weight is the scaling of weight `w` on the component functions of
  the one field: `comap` is natural in the value space, so it does not see which species a
  generator came from. -/
lemma bosonGeneratorsEquiv_massWeightScaleBoson (w : ℕ)
    (h : ∀ i, (T.boson i).massWeight = w) (c : ℂ) (y : T.BosonGenerators) :
    T.bosonGeneratorsEquiv w h (T.massWeightScaleBoson c y)
      = JetComponentSpace.massWeightScale w c (T.bosonGeneratorsEquiv w h y) := by
  have key : (T.bosonGeneratorsEquiv w h).toLinearMap.comp (T.massWeightScaleBoson c)
      = (JetComponentSpace.massWeightScale w c).comp
        (T.bosonGeneratorsEquiv w h).toLinearMap := by
    refine bosonGenerators_hom_ext fun i x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      massWeightScaleBoson_inclBoson, bosonGeneratorsEquiv_inclBoson,
      bosonGeneratorsEquiv_inclBoson, h i]
    exact LinearMap.congr_fun (JetComponentSpace.comap_comp_massWeightScale
      (T.projBosonField w h i) w c) x
  exact LinearMap.congr_fun key y

/-- The identification carries the derivative shift across. The species-diagonal shift
  of the derivative label on the generator space is the shift on the component functions of
  the single boson field: `comap` is natural in the value space, and the shift touches only
  the derivative label, so neither operation sees which species a generator came from. The
  common mass weight enters only through the packaging of the bosonic module as a matter
  field. -/
lemma bosonGeneratorsEquiv_jetDerivBoson (w : ℕ) (h : ∀ i, (T.boson i).massWeight = w)
    (μ : Fin 1 ⊕ Fin 3) (y : T.BosonGenerators) :
    T.bosonGeneratorsEquiv w h (T.jetDerivBoson μ y)
      = JetComponentSpace.jetDeriv μ (T.bosonGeneratorsEquiv w h y) := by
  have key : (T.bosonGeneratorsEquiv w h).toLinearMap.comp (T.jetDerivBoson μ)
      = (JetComponentSpace.jetDeriv μ).comp (T.bosonGeneratorsEquiv w h).toLinearMap := by
    refine bosonGenerators_hom_ext fun i x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      jetDerivBoson_inclBoson, bosonGeneratorsEquiv_inclBoson,
      bosonGeneratorsEquiv_inclBoson]
    exact LinearMap.congr_fun
      (JetComponentSpace.comap_jetDeriv (T.projBosonField w h i) μ) x
  exact LinearMap.congr_fun key y

end GaugeFieldData
