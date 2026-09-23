/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.CovariantDeriv
public import Physlib.Mathematics.AlgebraRepresentation
/-!
# Realizations of the local field algebra

## i. Overview

A complex algebra `B` carries the fields of a gauge-field datum when the local field
algebra `J(T)` maps into it by a complex algebra map equivariant for the jet gauge group
and the Lorentz group, both acting on `B` by algebra endomorphisms:
`GaugeFieldData.Realization`. The generator images are not stored: they are read off the
map as `Realization.toAssignment`, the connection factor as `Realization.gaugeRealization`
and the matter symbols as `Realization.fermionSymbol` and companions.

By the universal property of `J(T)` a realization is the same thing as a compatible
assignment of the generators satisfying the six generator-level transformation laws of
`GaugeFieldData.Assignment.IsEquivariant`, the connection law being affine: a jet moves a
connection generator by the transport of its inverse plus the Maurer–Cartan shift.

## ii. Key results

- `GaugeFieldData.Realization` : an algebra carrying the fields of a datum.
- `GaugeFieldData.Realization.gaugeRealization` : the gauge bosons of a realization, with
  `toAlgHom_covDerivFieldStrength` identifying the realized field-strength tower.
- `GaugeFieldData.Realization.toAlgHom_covDerivFermion` and companions : the realized
  covariant matter towers are the towers of the realized symbols.
- `GaugeFieldData.Assignment.IsEquivariant` : the generator-level equivariance of an
  assignment, with `IsEquivariant.toRealization` and
  `GaugeFieldData.realizationEquivAssignment`.

## iii. Table of contents

- A. Realizations
- B. The assignment of a realization
- C. The gauge bosons of a realization
- D. The matter symbols and towers of a realization
- E. Equivariant assignments

-/

@[expose] public section

set_option linter.unusedSectionVars false

open TensorProduct Matrix MatrixGroups Lorentz

namespace GaugeFieldData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} {T : GaugeFieldData jets}

/-!

## A. Realizations

-/

/-- A complex algebra `B` carrying the fields of the datum `T`: a complex algebra map out
  of the local field algebra, equivariant for the jet gauge group and the Lorentz group,
  both acting on the whole of `B` by algebra endomorphisms. No commutativity, injectivity
  or surjectivity is assumed, and no derivative operator on `B` is involved. It is built
  from the fields `toAlgHom`, `map_fst`, `map_snd`, `fst_mul`, `snd_mul` of
  `Representation.EquivariantAlgHom`, which the lemmas `map_repJet`, `map_repLorentz`,
  `repJet_mul` and `repLorentz_mul` name. -/
abbrev Realization (T : GaugeFieldData jets) (B : Type) [Ring B] [Algebra ℂ B]
    (repJet : Representation ℂ GJ B) (repLorentz : Representation ℂ SL(2,ℂ) B) :=
  Representation.EquivariantAlgHom (A := T.LocalFieldAlgebra) T.repJet repJet
    T.repLorentzGroup repLorentz

namespace Realization

variable {B : Type} [Ring B] [Algebra ℂ B] {repJet : Representation ℂ GJ B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}

variable (T) in
/-- The local field algebra realized in itself, by the identity. -/
noncomputable def id : Realization T T.LocalFieldAlgebra T.repJet T.repLorentzGroup :=
  Representation.EquivariantAlgHom.id _ _ GaugeFieldData.repJet_apply_mul
    GaugeFieldData.repLorentzGroup_apply_mul

@[simp]
lemma id_toAlgHom : (id T).toAlgHom = AlgHom.id ℂ T.LocalFieldAlgebra := rfl

/-- Two realizations agreeing on the generators of every species and on the connection
  generators are equal. -/
lemma ext_generators {h₁ h₂ : Realization T B repJet repLorentz}
    (hf : ∀ i x, h₁.toAlgHom (T.ιFermion i x) = h₂.toAlgHom (T.ιFermion i x))
    (hb : ∀ j y, h₁.toAlgHom (T.ιBoson j y) = h₂.toAlgHom (T.ιBoson j y))
    (ha : ∀ v, h₁.toAlgHom (T.ιConnection v) = h₂.toAlgHom (T.ιConnection v)) : h₁ = h₂ :=
  Representation.EquivariantAlgHom.ext (algHom_ext hf hb ha)

variable (h : Realization T B repJet repLorentz)

/-- The map is equivariant for the jet gauge group. -/
lemma map_repJet (U : GJ) (x : T.LocalFieldAlgebra) :
    h.toAlgHom (T.repJet U x) = repJet U (h.toAlgHom x) :=
  h.map_fst U x

/-- The map is equivariant for the Lorentz group. -/
lemma map_repLorentz (Λ : SL(2,ℂ)) (x : T.LocalFieldAlgebra) :
    h.toAlgHom (T.repLorentzGroup Λ x) = repLorentz Λ (h.toAlgHom x) :=
  h.map_snd Λ x

include h in
/-- The jet gauge group acts on the whole of `B` by algebra endomorphisms. -/
lemma repJet_mul (U : GJ) (b₁ b₂ : B) : repJet U (b₁ * b₂) = repJet U b₁ * repJet U b₂ :=
  h.fst_mul U b₁ b₂

include h in
/-- The Lorentz group acts on the whole of `B` by algebra endomorphisms. -/
lemma repLorentz_mul (Λ : SL(2,ℂ)) (b₁ b₂ : B) :
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂ :=
  h.snd_mul Λ b₁ b₂

/-!

## B. The assignment of a realization

-/

/-- The generator images of a realization, as a compatible assignment: the inverse of the
  universal property applied to its algebra map. -/
noncomputable def toAssignment : T.Assignment B := (liftEquiv T B).symm h.toAlgHom

lemma toAssignment_fermion (i : T.FermionSpecies) (x : JetComponentSpace (T.fermion i)) :
    h.toAssignment.fermion i x = h.toAlgHom (T.ιFermion i x) := rfl

lemma toAssignment_boson (j : T.BosonSpecies) (y : JetComponentSpace (T.boson j)) :
    h.toAssignment.boson j y = h.toAlgHom (T.ιBoson j y) := rfl

lemma toAssignment_connection (v : GaugeBoson.JetComponentSpace 𝔤) :
    h.toAssignment.connection v = h.toAlgHom (T.ιConnection v) := rfl

@[simp]
lemma lift_toAssignment : h.toAssignment.lift = h.toAlgHom :=
  (liftEquiv T B).apply_symm_apply h.toAlgHom

/-!

## C. The gauge bosons of a realization

-/

/-- The gauge bosons of a realization: the connection factor of `J(T)` carried into `B`,
  so that the gauge-boson symbol theory applies to the images. -/
noncomputable def gaugeRealization : GaugeAlgebraRealization jets B repJet repLorentz where
  toAlgHom := h.toAlgHom.comp T.gaugeRealization.toAlgHom
  A s μ := h.toAlgHom.toLinearMap.restrictScalars ℝ ∘ₗ T.gaugeRealization.A s μ
  A_eq _ _ _ := rfl
  map_repJet U x := by
    rw [AlgHom.comp_apply, T.gaugeRealization.map_repJet, h.map_repJet, AlgHom.comp_apply]
  map_repLorentz Λ x := by
    rw [AlgHom.comp_apply, T.gaugeRealization.map_repLorentz, h.map_repLorentz,
      AlgHom.comp_apply]
  repJet_mul := h.repJet_mul
  repLorentz_mul := h.repLorentz_mul

lemma gaugeRealization_A (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    h.gaugeRealization.A s μ φ = h.toAlgHom (T.gaugeRealization.A s μ φ) := rfl

@[simp]
lemma id_gaugeRealization_A : (id T).gaugeRealization.A = T.gaugeRealization.A := rfl

/-- The map of a realization carries the included field-strength tower to the covariant
  tower of the realized gauge-boson symbols. -/
lemma toAlgHom_covDerivFieldStrength (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    h.toAlgHom (T.covDerivFieldStrength l μ ν φ)
      = GaugeAlgebraRealization.iteratedCovDerivAdjoint h.gaugeRealization.A l
        (GaugeAlgebraRealization.fieldStrength h.gaugeRealization.A μ ν) 0 φ := by
  rw [covDerivFieldStrength_eq_iteratedCovDerivAdjoint]
  exact (GaugeAlgebraRealization.iteratedCovDerivAdjoint_fieldStrength_map
    (B := T.LocalFieldAlgebra) (B' := B) (h.toAlgHom.toLinearMap.restrictScalars ℝ)
    (map_mul h.toAlgHom) T.gaugeRealization.A l μ ν φ).symm

/-!

## D. The matter symbols and towers of a realization

-/

/-- The realized derivative symbols of a fermionic species. -/
noncomputable def fermionSymbol (i : T.FermionSpecies) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (T.FermionValue i) →ₗ[ℂ] B :=
  h.toAlgHom.toLinearMap ∘ₗ T.fermionSymbol i s

/-- The realized conjugate derivative symbols of a fermionic species. -/
noncomputable def conjFermionSymbol (i : T.FermionSpecies) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule (T.FermionValue i)) →ₗ[ℂ] B :=
  h.toAlgHom.toLinearMap ∘ₗ T.conjFermionSymbol i s

/-- The realized derivative symbols of a bosonic species. -/
noncomputable def bosonSymbol (j : T.BosonSpecies) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (T.BosonValue j) →ₗ[ℂ] B :=
  h.toAlgHom.toLinearMap ∘ₗ T.bosonSymbol j s

/-- The realized conjugate derivative symbols of a bosonic species. -/
noncomputable def conjBosonSymbol (j : T.BosonSpecies) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule (T.BosonValue j)) →ₗ[ℂ] B :=
  h.toAlgHom.toLinearMap ∘ₗ T.conjBosonSymbol j s

/-- The realized covariant tower of a fermionic species is the covariant tower of its
  realized symbols, computed against the realized gauge-boson symbols. No derivative
  operator on `B` is involved: both sides are the same finite algebraic expression. -/
lemma toAlgHom_covDerivFermion (i : T.FermionSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.FermionValue i)) :
    h.toAlgHom (T.covDerivFermion i l φ)
      = GaugeAlgebraRealization.covDerivIter h.gaugeRealization.A (T.fermion i).repAlgebra
        (h.fermionSymbol i) n l 0 φ :=
  (LinearMap.congr_fun (congrFun (GaugeAlgebraRealization.covDerivIter_map
    h.toAlgHom.toLinearMap (map_mul h.toAlgHom) T.gaugeRealization.A (T.fermion i).repAlgebra
    (T.fermionSymbol i) n l) 0) φ).symm

lemma toAlgHom_covDerivConjFermion (i : T.FermionSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    h.toAlgHom (T.covDerivConjFermion i l φ)
      = GaugeAlgebraRealization.covDerivIter h.gaugeRealization.A
        (LocalGaugeData.actionConj (T.fermion i).repAlgebra) (h.conjFermionSymbol i) n l 0 φ :=
  (LinearMap.congr_fun (congrFun (GaugeAlgebraRealization.covDerivIter_map
    h.toAlgHom.toLinearMap (map_mul h.toAlgHom) T.gaugeRealization.A
    (LocalGaugeData.actionConj (T.fermion i).repAlgebra) (T.conjFermionSymbol i) n l) 0) φ).symm

lemma toAlgHom_covDerivBoson (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.BosonValue j)) :
    h.toAlgHom (T.covDerivBoson j l φ)
      = GaugeAlgebraRealization.covDerivIter h.gaugeRealization.A (T.boson j).repAlgebra
        (h.bosonSymbol j) n l 0 φ :=
  (LinearMap.congr_fun (congrFun (GaugeAlgebraRealization.covDerivIter_map
    h.toAlgHom.toLinearMap (map_mul h.toAlgHom) T.gaugeRealization.A (T.boson j).repAlgebra
    (T.bosonSymbol j) n l) 0) φ).symm

lemma toAlgHom_covDerivConjBoson (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    h.toAlgHom (T.covDerivConjBoson j l φ)
      = GaugeAlgebraRealization.covDerivIter h.gaugeRealization.A
        (LocalGaugeData.actionConj (T.boson j).repAlgebra) (h.conjBosonSymbol j) n l 0 φ :=
  (LinearMap.congr_fun (congrFun (GaugeAlgebraRealization.covDerivIter_map
    h.toAlgHom.toLinearMap (map_mul h.toAlgHom) T.gaugeRealization.A
    (LocalGaugeData.actionConj (T.boson j).repAlgebra) (T.conjBosonSymbol j) n l) 0) φ).symm

end Realization

/-!

## E. Equivariant assignments

-/

/-- The generator-level transformation laws of an assignment: each matter species
  transforms by the jet action of its own component space, and the connection generators
  transform affinely, by the transport of the inverse jet plus its Maurer–Cartan shift.
  The Lorentz laws are all linear. These are the laws the generators of `J(T)` themselves
  satisfy. -/
structure Assignment.IsEquivariant {B : Type} [Ring B] [Algebra ℂ B] (d : T.Assignment B)
    (repJet : Representation ℂ GJ B) (repLorentz : Representation ℂ SL(2,ℂ) B) : Prop where
  /-- A jet acts on the generators of a fermionic species by the action of its component
    space. -/
  repJet_fermion : ∀ (U : GJ) (i : T.FermionSpecies) (x : JetComponentSpace (T.fermion i)),
    repJet U (d.fermion i x) = d.fermion i (JetComponentSpace.repJet (T.fermion i) U x)
  /-- A jet acts on the generators of a bosonic species by the action of its component
    space. -/
  repJet_boson : ∀ (U : GJ) (j : T.BosonSpecies) (y : JetComponentSpace (T.boson j)),
    repJet U (d.boson j y) = d.boson j (JetComponentSpace.repJet (T.boson j) U y)
  /-- A jet acts affinely on the connection generators. -/
  repJet_connection : ∀ (U : GJ) (v : GaugeBoson.JetComponentSpace 𝔤),
    repJet U (d.connection v) = d.connection (LocalGaugeFieldAlgebra.transport jets U⁻¹ v)
      + (LocalGaugeFieldAlgebra.mcShift jets U⁻¹ v : ℂ) • (1 : B)
  /-- A Lorentz transformation acts on the generators of a fermionic species by the action
    of its component space. -/
  repLorentz_fermion : ∀ (Λ : SL(2,ℂ)) (i : T.FermionSpecies)
    (x : JetComponentSpace (T.fermion i)), repLorentz Λ (d.fermion i x)
      = d.fermion i (JetComponentSpace.repLorentzGroup (T.fermion i) Λ x)
  /-- A Lorentz transformation acts on the generators of a bosonic species by the action of
    its component space. -/
  repLorentz_boson : ∀ (Λ : SL(2,ℂ)) (j : T.BosonSpecies)
    (y : JetComponentSpace (T.boson j)), repLorentz Λ (d.boson j y)
      = d.boson j (JetComponentSpace.repLorentzGroup (T.boson j) Λ y)
  /-- A Lorentz transformation acts linearly on the connection generators. -/
  repLorentz_connection : ∀ (Λ : SL(2,ℂ)) (v : GaugeBoson.JetComponentSpace 𝔤),
    repLorentz Λ (d.connection v)
      = d.connection (GaugeBoson.JetComponentSpace.repLorentzGroup 𝔤 Λ v)

namespace Assignment

variable {B : Type} [Ring B] [Algebra ℂ B] {repJet : Representation ℂ GJ B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- The assignment of a realization is equivariant: the laws are those of the generators of
  `J(T)`, transported along the map. -/
lemma _root_.GaugeFieldData.Realization.toAssignment_isEquivariant
    (h : Realization T B repJet repLorentz) :
    h.toAssignment.IsEquivariant repJet repLorentz where
  repJet_fermion U i x :=
    (h.map_repJet U (T.ιFermion i x)).symm.trans
      (congrArg h.toAlgHom (repJet_ιFermion U i x))
  repJet_boson U j y :=
    (h.map_repJet U (T.ιBoson j y)).symm.trans (congrArg h.toAlgHom (repJet_ιBoson U j y))
  repJet_connection U v :=
    (h.map_repJet U (T.ιConnection v)).symm.trans
      ((congrArg h.toAlgHom (repJet_ιConnection_affine U v)).trans
        (AlgHom.map_add_smul_one h.toAlgHom _ _))
  repLorentz_fermion Λ i x :=
    (h.map_repLorentz Λ (T.ιFermion i x)).symm.trans
      (congrArg h.toAlgHom (repLorentzGroup_ιFermion Λ i x))
  repLorentz_boson Λ j y :=
    (h.map_repLorentz Λ (T.ιBoson j y)).symm.trans
      (congrArg h.toAlgHom (repLorentzGroup_ιBoson Λ j y))
  repLorentz_connection Λ v :=
    (h.map_repLorentz Λ (T.ιConnection v)).symm.trans
      (congrArg h.toAlgHom (repLorentzGroup_ιConnection_eq Λ v))

/-- The lift of an equivariant assignment intertwines the jet gauge actions, as an equality
  of algebra maps: both sides agree on the generators of every species and on the
  connection generators. -/
lemma IsEquivariant.lift_comp_repJetAlgHom {d : T.Assignment B}
    (hd : d.IsEquivariant repJet repLorentz)
    (hJ : ∀ (U : GJ) (b₁ b₂ : B), repJet U (b₁ * b₂) = repJet U b₁ * repJet U b₂) (U : GJ) :
    d.lift.comp (T.repJetAlgHom U) = (repJet.toAlgHom hJ U).comp d.lift := by
  refine algHom_ext (fun i y => ?_) (fun j y => ?_) (fun v => ?_)
  · rw [AlgHom.comp_apply, repJetAlgHom_ιFermion, lift_ιFermion, AlgHom.comp_apply,
      lift_ιFermion, Representation.toAlgHom_apply, hd.repJet_fermion]
  · rw [AlgHom.comp_apply, repJetAlgHom_ιBoson, lift_ιBoson, AlgHom.comp_apply,
      lift_ιBoson, Representation.toAlgHom_apply, hd.repJet_boson]
  · show d.lift (T.repJet U (T.ιConnection v)) = repJet U (d.lift (T.ιConnection v))
    rw [repJet_ιConnection_affine, AlgHom.map_add_smul_one d.lift, lift_ιConnection,
      lift_ιConnection, hd.repJet_connection]

/-- The lift of an equivariant assignment intertwines the Lorentz actions, as an equality of
  algebra maps. -/
lemma IsEquivariant.lift_comp_repLorentzAlgHom {d : T.Assignment B}
    (hd : d.IsEquivariant repJet repLorentz)
    (hL : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
      repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂) (Λ : SL(2,ℂ)) :
    d.lift.comp (T.repLorentzAlgHom Λ) = (repLorentz.toAlgHom hL Λ).comp d.lift := by
  refine algHom_ext (fun i y => ?_) (fun j y => ?_) (fun v => ?_)
  · rw [AlgHom.comp_apply, repLorentzAlgHom_ιFermion, lift_ιFermion, AlgHom.comp_apply,
      lift_ιFermion, Representation.toAlgHom_apply, hd.repLorentz_fermion]
  · rw [AlgHom.comp_apply, repLorentzAlgHom_ιBoson, lift_ιBoson, AlgHom.comp_apply,
      lift_ιBoson, Representation.toAlgHom_apply, hd.repLorentz_boson]
  · show d.lift (T.repLorentzGroup Λ (T.ιConnection v))
        = repLorentz Λ (d.lift (T.ιConnection v))
    rw [repLorentzGroup_ιConnection_eq, lift_ιConnection, lift_ιConnection,
      hd.repLorentz_connection]

/-- An equivariant assignment lifts to a realization: each equivariance law is an equality
  of two algebra maps agreeing on the generators, so it follows from the generator laws by
  the universal property. -/
noncomputable def IsEquivariant.toRealization {d : T.Assignment B}
    (hd : d.IsEquivariant repJet repLorentz)
    (hJ : ∀ (U : GJ) (b₁ b₂ : B), repJet U (b₁ * b₂) = repJet U b₁ * repJet U b₂)
    (hL : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
      repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂) :
    Realization T B repJet repLorentz where
  toAlgHom := d.lift
  map_fst U x := AlgHom.congr_fun (hd.lift_comp_repJetAlgHom hJ U) x
  map_snd Λ x := AlgHom.congr_fun (hd.lift_comp_repLorentzAlgHom hL Λ) x
  fst_mul := hJ
  snd_mul := hL

@[simp]
lemma IsEquivariant.toRealization_toAlgHom {d : T.Assignment B}
    (hd : d.IsEquivariant repJet repLorentz)
    (hJ : ∀ (U : GJ) (b₁ b₂ : B), repJet U (b₁ * b₂) = repJet U b₁ * repJet U b₂)
    (hL : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
      repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂) :
    (hd.toRealization hJ hL).toAlgHom = d.lift := rfl

end Assignment

variable (T) in
/-- The mapping-out universal property of `J(T)` in equivariant form: for target actions by
  algebra endomorphisms, realizations of `T` in `B` are exactly the equivariant compatible
  assignments of its generators. -/
noncomputable def realizationEquivAssignment {B : Type} [Ring B] [Algebra ℂ B]
    {repJet : Representation ℂ GJ B} {repLorentz : Representation ℂ SL(2,ℂ) B}
    (hJ : ∀ (U : GJ) (b₁ b₂ : B), repJet U (b₁ * b₂) = repJet U b₁ * repJet U b₂)
    (hL : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
      repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂) :
    {d : T.Assignment B // d.IsEquivariant repJet repLorentz}
      ≃ Realization T B repJet repLorentz where
  toFun d := d.2.toRealization hJ hL
  invFun h := ⟨h.toAssignment, h.toAssignment_isEquivariant⟩
  left_inv d := Subtype.ext ((liftEquiv T B).symm_apply_apply d.1)
  right_inv h :=
    Representation.EquivariantAlgHom.ext ((liftEquiv T B).apply_symm_apply h.toAlgHom)

end GaugeFieldData
