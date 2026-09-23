/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.FieldData
public import Physlib.Particles.StandardModel.Fermions.JetAlgebra.Basic
public import Physlib.Particles.StandardModel.HiggsBoson.JetAlgebra.Algebra
public import Physlib.Particles.StandardModel.HiggsBoson.JetAlgebra.Basic
public import Physlib.Particles.StandardModel.Matter.FermionicAlgebra.JetDeriv
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.JetDeriv
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.GaugeField
public import Physlib.Mathematics.ExteriorAlgebra
public import Physlib.Mathematics.SymmetricAlgebra
/-!
# The sector algebras of the Standard Model inside its local field algebra

## i. Overview

The Standard Model jet algebra is `fieldData.LocalFieldAlgebra`, the local field algebra
the generic theory builds from the Standard Model field datum: one exterior algebra on the
direct sum of the fifteen fermionic species component spaces, a symmetric algebra on the
one bosonic species, and the complexified real symmetric algebra on the connection
generators.

Its two matter factors are not the sector algebras the Standard Model files are written
with. `FermionJetAlgebra` is an exterior algebra on the component space of a fifteen-fold
product of value spaces, and the fermionic factor of the carrier an exterior algebra on a
fifteen-fold direct sum of component spaces; `HiggsJetAlgebra` is a symmetric algebra on
the component space of `HiggsVec`, and the bosonic factor one on the generators of the
one-species direct sum. This file identifies the two presentations and lifts the
identification to the sector algebras, which is what the sector inclusions
`JetAlgebra.includeFermion` and `JetAlgebra.includeHiggs` are built from. The connection
factors need no comparison: the Standard Model gauge bosons are the generic
`GaugeBoson GaugeAlgebra`.

The identification of the generators is Joseph Tooby-Smith's generic
`GaugeFieldData.fermionGeneratorsEquiv`, which presents the direct sum over the species as
the component space of a single field valued in `fieldData.FermionModule`. What is left for
the Standard Model is one relabelling: `FermionSpace` is a nested product of five
three-generation blocks and `fieldData.FermionModule` is a dependent function on the fifteen
constructors of `FermionType`. `StandardModel.fermionSpaceEquiv` is that relabelling, and
`JetComponentSpace.comapEquiv` carries it to the component spaces — contravariantly, a
component function being a covector on the target.

## ii. Key results

- `StandardModel.fermionSpaceEquiv` : the total fermionic target space as the family of
  species value spaces.
- `StandardModel.fermionProj` : the projection onto a species, computing to the existing
  Standard Model projections.
- `StandardModel.higgsModuleEquiv` : the Higgs as the one-species bosonic module.
- `StandardModel.fermionGeneratorsEquiv`, `StandardModel.bosonGeneratorsEquiv` : the two
  matter generator identifications.
- `StandardModel.fermionAlgebraEquiv`, `StandardModel.higgsAlgebraEquiv` : the two sector
  algebra equivalences.
- `StandardModel.fermionAlgebraEquiv_jetDeriv`,
  `StandardModel.higgsAlgebraEquiv_jetDeriv` : the sector equivalences are maps of
  differential algebras.

## iii. Table of contents

- A. The two matter generator identifications
  - A.1. The fermionic species as a family over the total target space
  - A.2. The Higgs as the one bosonic species
  - A.3. The generator identifications
- B. The sector algebra equivalences
- C. The generic generators of the field datum
- D. The sector equivalences and the ordinary derivative

-/

@[expose] public section

open TensorProduct Matrix MatrixGroups

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

/-!

## A. The two matter generator identifications

### A.1. The fermionic species as a family over the total target space

The generic theory presents the fermionic generators as the component space of a field
valued in `fieldData.FermionModule`, a dependent function on the fifteen species. The
Standard Model writes the same target space as a nested product of five three-generation
blocks. The only Standard Model input the comparison needs is the relabelling between the
two.

-/

/-- The total fermionic target space is the fermionic module of the datum. The nested
  product of five three-generation blocks that `FermionSpace` is, rearranged into a
  dependent function on the fifteen species. It is a relabelling: every component of a
  value on one side is a component of the corresponding value on the other. -/
noncomputable def fermionSpaceEquiv :
    fermionMatterField.V ≃ₗ[ℂ] (fieldData.fermionMatterField 3 fieldData_fermion_massWeight).V where
  toFun v t :=
    match t with
    | .leptonDoublet i => v.1 i
    | .leptonSinglet i => v.2.1 i
    | .quarkDoublet i => v.2.2.1 i
    | .upSinglet i => v.2.2.2.1 i
    | .downSinglet i => v.2.2.2.2 i
  map_add' v w := funext fun t => by
    cases t with
    | leptonDoublet i => rfl
    | leptonSinglet i => rfl
    | quarkDoublet i => rfl
    | upSinglet i => rfl
    | downSinglet i => rfl
  map_smul' c v := funext fun t => by
    cases t with
    | leptonDoublet i => rfl
    | leptonSinglet i => rfl
    | quarkDoublet i => rfl
    | upSinglet i => rfl
    | downSinglet i => rfl
  invFun f :=
    (fun i => f (.leptonDoublet i), fun i => f (.leptonSinglet i),
      fun i => f (.quarkDoublet i), fun i => f (.upSinglet i), fun i => f (.downSinglet i))
  left_inv v := rfl
  right_inv f := funext fun t => by
    cases t with
    | leptonDoublet i => rfl
    | leptonSinglet i => rfl
    | quarkDoublet i => rfl
    | upSinglet i => rfl
    | downSinglet i => rfl

/-- The projection of the total fermionic target space onto the value space of a species
  of the datum: the relabelling followed by the projection of the module. -/
noncomputable def fermionProj (t : fieldData.FermionSpecies) :
    fermionMatterField.V →ₗ[ℂ] (fieldData.fermion t).V :=
  (fieldData.projFermionField 3 fieldData_fermion_massWeight t).comp
    fermionSpaceEquiv.toLinearMap

lemma fermionProj_eq (t : fieldData.FermionSpecies) :
    fermionProj t = (fieldData.projFermionField 3 fieldData_fermion_massWeight t).comp
      fermionSpaceEquiv.toLinearMap := rfl

@[simp]
lemma fermionProj_leptonDoublet (i : Fin 3) :
    fermionProj (.leptonDoublet i) = FermionSpace.leptonDoubletProj i := rfl

@[simp]
lemma fermionProj_leptonSinglet (i : Fin 3) :
    fermionProj (.leptonSinglet i) = FermionSpace.leptonSingletProj i := rfl

@[simp]
lemma fermionProj_quarkDoublet (i : Fin 3) :
    fermionProj (.quarkDoublet i) = FermionSpace.quarkDoubletProj i := rfl

@[simp]
lemma fermionProj_upSinglet (i : Fin 3) :
    fermionProj (.upSinglet i) = FermionSpace.upSingletProj i := rfl

@[simp]
lemma fermionProj_downSinglet (i : Fin 3) :
    fermionProj (.downSinglet i) = FermionSpace.downSingletProj i := rfl

/-!

### A.2. The Higgs as the one bosonic species

-/

/-- The Higgs multiplet is the bosonic module of the datum. There is one bosonic
  species, so the module of bosonic values is the constant family on it. -/
noncomputable def higgsModuleEquiv :
    HiggsVec.matterField.V ≃ₗ[ℂ] (fieldData.bosonMatterField 2 fieldData_boson_massWeight).V where
  toFun v := fun _ => v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f ()
  left_inv _ := rfl
  right_inv _ := funext fun j => match j with | () => rfl

/-- Reading off the one species undoes the relabelling. -/
lemma projBosonValue_comp_higgsModuleEquiv (j : fieldData.BosonSpecies) :
    (fieldData.projBosonField 2 fieldData_boson_massWeight j).comp
        higgsModuleEquiv.toLinearMap = LinearMap.id :=
  LinearMap.ext fun _ => rfl

/-- The pullback along the relabelling undoes the pullback along the one projection. -/
lemma comap_projBosonValue_comp_comap_higgsModuleEquiv (j : fieldData.BosonSpecies) :
    (JetComponentSpace.comap higgsModuleEquiv.toLinearMap).comp
        (JetComponentSpace.comap (fieldData.projBosonField 2 fieldData_boson_massWeight j))
      = LinearMap.id :=
  ((JetComponentSpace.comap_comp higgsModuleEquiv.toLinearMap
        (fieldData.projBosonField 2 fieldData_boson_massWeight j)).symm.trans
      (congrArg (fun f : HiggsVec.matterField.V →ₗ[ℂ] (fieldData.boson j).V =>
        JetComponentSpace.comap f) (projBosonValue_comp_higgsModuleEquiv j))).trans
    JetComponentSpace.comap_id

/-!

### A.3. The generator identifications

The generic identification of a generator space with the component space of the whole
matter field, composed with the relabelling of the target space. `JetComponentSpace.comap`
is contravariant, so the relabelling `FermionSpace ≃ₗ fieldData.FermionModule` is carried
by `comapEquiv` to a map *from* the component space of the module *to* that of
`FermionSpace`, which is the direction the composite needs.

-/

/-- The fermionic generator space of the datum is the component space of the total
  fermionic target space. The generic presentation of the direct sum as the component
  space of the fermionic module, followed by the relabelling of the target space. -/
noncomputable def fermionGeneratorsEquiv :
    fieldData.FermionGenerators ≃ₗ[ℂ] JetComponentSpace fermionMatterField :=
  (fieldData.fermionGeneratorsEquiv 3 fieldData_fermion_massWeight).trans
    (JetComponentSpace.comapEquiv (M := fermionMatterField)
      (N := fieldData.fermionMatterField 3 fieldData_fermion_massWeight) fermionSpaceEquiv)

/-- A species sits inside the fermionic generators as the pullback along the projection
  onto that species. -/
@[simp]
lemma fermionGeneratorsEquiv_inclFermion (t : fieldData.FermionSpecies)
    (x : JetComponentSpace (fieldData.fermion t)) :
    fermionGeneratorsEquiv (fieldData.inclFermion t x)
      = JetComponentSpace.comap (fermionProj t) x := by
  rw [fermionProj_eq,
    JetComponentSpace.comap_comp fermionSpaceEquiv.toLinearMap
      (fieldData.projFermionField 3 fieldData_fermion_massWeight t),
    fermionGeneratorsEquiv, LinearEquiv.trans_apply,
    GaugeFieldData.fermionGeneratorsEquiv_inclFermion 3 fieldData_fermion_massWeight,
    JetComponentSpace.comapEquiv_apply, LinearMap.comp_apply]

@[simp]
lemma fermionGeneratorsEquiv_symm_comap (t : fieldData.FermionSpecies)
    (x : JetComponentSpace (fieldData.fermion t)) :
    fermionGeneratorsEquiv.symm (JetComponentSpace.comap (fermionProj t) x)
      = fieldData.inclFermion t x := by
  rw [← fermionGeneratorsEquiv_inclFermion, LinearEquiv.symm_apply_apply]

/-- The second half of a pullback of an unconjugated symbol vanishes. -/
lemma _root_.JetComponentSpace.comap_snd_of_zero {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
    {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} {M N : MatterField jets}
    (f : M.V →ₗ[ℂ] N.V) (x : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ N.V) :
    (JetComponentSpace.comap f ((x, 0) : JetComponentSpace N)).2 = 0 := by
  rw [show (JetComponentSpace.comap f ((x, 0) : JetComponentSpace N)).2
    = (TensorProduct.map LinearMap.id (Module.Dual.transpose (ConjModule.map f)))
        (0 : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule N.V)) from rfl, map_zero]

/-- The first half of a pullback of a conjugate symbol vanishes. -/
lemma _root_.JetComponentSpace.comap_fst_of_zero {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
    {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} {M N : MatterField jets}
    (f : M.V →ₗ[ℂ] N.V) (y : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule N.V)) :
    (JetComponentSpace.comap f ((0, y) : JetComponentSpace N)).1 = 0 := by
  rw [show (JetComponentSpace.comap f ((0, y) : JetComponentSpace N)).1
    = (TensorProduct.map LinearMap.id (Module.Dual.transpose f))
        (0 : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ N.V) from rfl, map_zero]

/-- The unconjugated symbol `∂_s ψ_φ` of a species, read on the total target space. -/
lemma fermionGeneratorsEquiv_symm_basis_tmul (t : fieldData.FermionSpecies)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (fieldData.FermionValue t)) :
    fermionGeneratorsEquiv.symm ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ]
        Module.Dual.transpose (fermionProj t) φ, 0) : JetComponentSpace fermionMatterField)
      = fieldData.inclFermion t ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) :
          JetComponentSpace (fieldData.fermion t)) := by
  rw [← fermionGeneratorsEquiv_symm_comap t
    ((DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) :
      JetComponentSpace (fieldData.fermion t))]
  refine congrArg _ (Prod.ext ?_ ?_)
  · exact (JetComponentSpace.comap_fst_tmul (M := fermionMatterField) (N := fieldData.fermion t) (fermionProj t) _ φ 0).symm
  · exact (JetComponentSpace.comap_snd_of_zero (M := fermionMatterField) (N := fieldData.fermion t) (fermionProj t) _).symm

/-- The conjugate symbol `∂_s ψ̄_φ` of a species, read on the total target space. -/
lemma fermionGeneratorsEquiv_symm_basis_tmul_conj (t : fieldData.FermionSpecies)
    (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (fieldData.FermionValue t))) :
    fermionGeneratorsEquiv.symm ((0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ]
        Module.Dual.transpose (ConjModule.map (fermionProj t)) φ) :
          JetComponentSpace fermionMatterField)
      = fieldData.inclFermion t ((0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) :
          JetComponentSpace (fieldData.fermion t)) := by
  rw [← fermionGeneratorsEquiv_symm_comap t
    ((0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) :
      JetComponentSpace (fieldData.fermion t))]
  refine congrArg _ (Prod.ext ?_ ?_)
  · exact (JetComponentSpace.comap_fst_of_zero (M := fermionMatterField) (N := fieldData.fermion t) (fermionProj t) _).symm
  · exact (JetComponentSpace.comap_snd_tmul (M := fermionMatterField) (N := fieldData.fermion t) (fermionProj t) 0 _ φ).symm

/-- The bosonic generator space of the datum is the component space of the Higgs.
  There is one bosonic species, so the direct sum has one summand and the relabelling of
  the target space is the identification of a one-element function space with its
  value. -/
noncomputable def bosonGeneratorsEquiv :
    fieldData.BosonGenerators ≃ₗ[ℂ] JetComponentSpace HiggsVec.matterField :=
  (fieldData.bosonGeneratorsEquiv 2 fieldData_boson_massWeight).trans
    (JetComponentSpace.comapEquiv (M := HiggsVec.matterField)
      (N := fieldData.bosonMatterField 2 fieldData_boson_massWeight) higgsModuleEquiv)

@[simp]
lemma bosonGeneratorsEquiv_inclBoson (j : fieldData.BosonSpecies)
    (y : JetComponentSpace (fieldData.boson j)) :
    bosonGeneratorsEquiv (fieldData.inclBoson j y) = y := by
  rw [bosonGeneratorsEquiv, LinearEquiv.trans_apply,
    GaugeFieldData.bosonGeneratorsEquiv_inclBoson 2 fieldData_boson_massWeight, JetComponentSpace.comapEquiv_apply]
  exact LinearMap.congr_fun (comap_projBosonValue_comp_comap_higgsModuleEquiv j) y

@[simp]
lemma bosonGeneratorsEquiv_symm_apply (y : JetComponentSpace HiggsVec.matterField) :
    bosonGeneratorsEquiv.symm y = fieldData.inclBoson () y :=
  bosonGeneratorsEquiv.injective
    ((bosonGeneratorsEquiv.apply_symm_apply y).trans
      (bosonGeneratorsEquiv_inclBoson () y).symm)

/-!

## B. The sector algebra equivalences

Each sector algebra is a free algebra over one presentation of its generator space and the
corresponding factor of the carrier a free algebra over the other, so the generator
identifications of section A lift to algebra equivalences by functoriality.

-/

/-- The fermionic factor: one exterior algebra, over the two presentations of the same
  generator space. -/
noncomputable def fermionAlgebraEquiv :
    FermionJetAlgebra ≃ₐ[ℂ] ExteriorAlgebra ℂ fieldData.FermionGenerators :=
  ExteriorAlgebra.mapEquiv fermionGeneratorsEquiv.symm

/-- The Higgs factor: one symmetric algebra, over the two presentations of the same
  generator space. -/
noncomputable def higgsAlgebraEquiv :
    HiggsJetAlgebra ≃ₐ[ℂ] SymmetricAlgebra ℂ fieldData.BosonGenerators :=
  SymmetricAlgebra.congr (R := ℂ) (M := JetComponentSpace HiggsVec.matterField)
    (N := fieldData.BosonGenerators) bosonGeneratorsEquiv.symm

@[simp]
lemma fermionAlgebraEquiv_ι (v : JetComponentSpace fermionMatterField) :
    fermionAlgebraEquiv (ExteriorAlgebra.ι ℂ v)
      = ExteriorAlgebra.ι ℂ (fermionGeneratorsEquiv.symm v) :=
  ExteriorAlgebra.map_apply_ι _ v

@[simp]
lemma higgsAlgebraEquiv_ι (v : JetComponentSpace HiggsVec.matterField) :
    higgsAlgebraEquiv (SymmetricAlgebra.ι ℂ (JetComponentSpace HiggsVec.matterField) v)
      = SymmetricAlgebra.ι ℂ fieldData.BosonGenerators (bosonGeneratorsEquiv.symm v) :=
  SymmetricAlgebra.congr_apply_ι bosonGeneratorsEquiv.symm v

/-!

## C. The generic generators of the field datum

The degree-one elements of the three factors, included, are the generic generators
`ιFermion`, `ιBoson` and `ιConnection` of the field datum. These are the reductions the
named Standard Model field symbols are computed by.

-/

/-- A degree-one element of the fermionic factor, included, is a total fermionic
  generator. -/
lemma includeFermion_ι (w : fieldData.FermionGenerators) :
    fieldData.includeFermion (ExteriorAlgebra.ι ℂ w) = fieldData.ιFermionTotal w := rfl

/-- A degree-one element of the bosonic factor, included, is a total bosonic generator. -/
lemma includeBoson_ι (w : fieldData.BosonGenerators) :
    fieldData.includeBoson (SymmetricAlgebra.ι ℂ fieldData.BosonGenerators w)
      = fieldData.ιBosonTotal w := rfl

/-- A real degree-one element of the connection factor, included, is a connection
  generator. -/
lemma includeConnection_one_tmul_ι (v : GaugeBoson.JetComponentSpace GaugeAlgebra) :
    fieldData.includeConnection ((1 : ℂ) ⊗ₜ[ℝ]
        SymmetricAlgebra.ι ℝ (GaugeBoson.JetComponentSpace GaugeAlgebra) v)
      = fieldData.ιConnection v := rfl

/-- The total fermionic generator of a species summand is that species' generator. -/
lemma ιFermionTotal_inclFermion (t : fieldData.FermionSpecies)
    (x : JetComponentSpace (fieldData.fermion t)) :
    fieldData.ιFermionTotal (fieldData.inclFermion t x) = fieldData.ιFermion t x := rfl

/-- The total bosonic generator of a species summand is that species' generator. -/
lemma ιBosonTotal_inclBoson (j : fieldData.BosonSpecies)
    (y : JetComponentSpace (fieldData.boson j)) :
    fieldData.ιBosonTotal (fieldData.inclBoson j y) = fieldData.ιBoson j y := rfl

/-!

## D. The sector equivalences and the ordinary derivative

The derivative shift is blind to the value space, so it commutes with the pullback along
any map of target spaces; the two generator identifications therefore carry the derivative
shift of the datum to the derivative shift of the total component space, and the
free-algebra derivations extending them agree.

These are the bridges the migrated total derivative uses to restrict to the sector
derivatives under their existing names. The species-diagonal half of each is Joseph
Tooby-Smith's generic `GaugeFieldData.fermionGeneratorsEquiv_jetDerivFermion`; what is
added here is the relabelling of the target space, which `JetComponentSpace.comap_jetDeriv`
lets through.

-/

/-- The fermionic generator identification intertwines the derivative shift of the datum
  with the derivative shift on the component space of the total target space. -/
lemma fermionGeneratorsEquiv_jetDerivFermion (μ : Fin 1 ⊕ Fin 3)
    (w : fieldData.FermionGenerators) :
    fermionGeneratorsEquiv (fieldData.jetDerivFermion μ w)
      = JetComponentSpace.jetDeriv μ (fermionGeneratorsEquiv w) := by
  rw [fermionGeneratorsEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    JetComponentSpace.comapEquiv_apply, JetComponentSpace.comapEquiv_apply,
    GaugeFieldData.fermionGeneratorsEquiv_jetDerivFermion]
  exact LinearMap.congr_fun
    (JetComponentSpace.comap_jetDeriv fermionSpaceEquiv.toLinearMap μ) _

/-- The inverse form of `fermionGeneratorsEquiv_jetDerivFermion`. -/
lemma fermionGeneratorsEquiv_symm_jetDeriv (μ : Fin 1 ⊕ Fin 3)
    (v : JetComponentSpace fermionMatterField) :
    fermionGeneratorsEquiv.symm (JetComponentSpace.jetDeriv μ v)
      = fieldData.jetDerivFermion μ (fermionGeneratorsEquiv.symm v) :=
  fermionGeneratorsEquiv.injective <|
    (fermionGeneratorsEquiv.apply_symm_apply _).trans <|
      ((congrArg (JetComponentSpace.jetDeriv μ)
          (fermionGeneratorsEquiv.apply_symm_apply v)).symm.trans
        (fermionGeneratorsEquiv_jetDerivFermion μ _).symm)

/-- The bosonic generator identification intertwines the two derivative shifts. -/
lemma bosonGeneratorsEquiv_jetDerivBoson (μ : Fin 1 ⊕ Fin 3)
    (w : fieldData.BosonGenerators) :
    bosonGeneratorsEquiv (fieldData.jetDerivBoson μ w)
      = JetComponentSpace.jetDeriv μ (bosonGeneratorsEquiv w) := by
  rw [bosonGeneratorsEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    JetComponentSpace.comapEquiv_apply, JetComponentSpace.comapEquiv_apply,
    GaugeFieldData.bosonGeneratorsEquiv_jetDerivBoson]
  exact LinearMap.congr_fun
    (JetComponentSpace.comap_jetDeriv higgsModuleEquiv.toLinearMap μ) _

/-- The inverse form of `bosonGeneratorsEquiv_jetDerivBoson`. -/
lemma bosonGeneratorsEquiv_symm_jetDeriv (μ : Fin 1 ⊕ Fin 3)
    (v : JetComponentSpace HiggsVec.matterField) :
    bosonGeneratorsEquiv.symm (JetComponentSpace.jetDeriv μ v)
      = fieldData.jetDerivBoson μ (bosonGeneratorsEquiv.symm v) :=
  bosonGeneratorsEquiv.injective <|
    (bosonGeneratorsEquiv.apply_symm_apply _).trans <|
      ((congrArg (JetComponentSpace.jetDeriv μ)
          (bosonGeneratorsEquiv.apply_symm_apply v)).symm.trans
        (bosonGeneratorsEquiv_jetDerivBoson μ _).symm)

/-- The total derivative on the fermionic algebra of a species is the general even
  derivation of its exterior algebra extending the derivative shift. The two constructions
  are the same lift into the trivial square-zero extension, written once in the matter
  sector and once in general; the identification lets the general theory apply to the
  fermionic factor of the migrated carrier, whose generator space is a direct sum of
  component spaces rather than a single one. -/
private lemma fermionicAlgebra_jetDeriv_eq (M : MatterField localGaugeData)
    (μ : Fin 1 ⊕ Fin 3) :
    FermionicAlgebra.jetDeriv (M := M) μ
      = ExteriorAlgebra.derivationOfLinear (JetComponentSpace.jetDeriv μ) := rfl

/-- The fermionic sector equivalence is a map of differential algebras: the exterior
  derivation extending the derivative shift on the total target space goes to the exterior
  derivation extending the derivative shift of the datum. -/
lemma fermionAlgebraEquiv_jetDeriv (μ : Fin 1 ⊕ Fin 3) (f : FermionJetAlgebra) :
    fermionAlgebraEquiv (FermionicAlgebra.jetDeriv μ f)
      = ExteriorAlgebra.derivationOfLinear (fieldData.jetDerivFermion μ)
          (fermionAlgebraEquiv f) := by
  rw [fermionicAlgebra_jetDeriv_eq fermionMatterField]
  exact ExteriorAlgebra.algHom_derivationOfLinear fermionAlgebraEquiv.toAlgHom
    (fun x => fermionAlgebraEquiv_ι x) (fun x => fermionGeneratorsEquiv_symm_jetDeriv μ x) f

/-- The Higgs sector equivalence is a map of differential algebras. -/
lemma higgsAlgebraEquiv_jetDeriv (μ : Fin 1 ⊕ Fin 3) (h : HiggsJetAlgebra) :
    higgsAlgebraEquiv (BosonicAlgebra.jetDeriv μ h)
      = SymmetricAlgebra.derivationOfLinear (fieldData.jetDerivBoson μ)
          (higgsAlgebraEquiv h) := by
  show higgsAlgebraEquiv
      (SymmetricAlgebra.derivationOfLinear (JetComponentSpace.jetDeriv μ) h)
    = SymmetricAlgebra.derivationOfLinear (fieldData.jetDerivBoson μ)
        (higgsAlgebraEquiv h)
  exact SymmetricAlgebra.algHom_derivationOfLinear higgsAlgebraEquiv.toAlgHom
    (fun x => higgsAlgebraEquiv_ι x) (fun x => bosonGeneratorsEquiv_symm_jetDeriv μ x) h

end StandardModel
