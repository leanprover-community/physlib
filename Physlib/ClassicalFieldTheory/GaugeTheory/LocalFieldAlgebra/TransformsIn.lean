/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.GaugeAction
public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.LorentzAction
public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.JetComponentSpace.TransformsIn
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.Realization.Basic
/-!
# The field symbols of the local field algebra and their transformation laws

## i. Overview

The generators of the local field algebra `J(T)` of a field datum are the derivative
symbols of its species: `∂_s ψ^φ`, indexed by a derivative multiset `s` and a covector `φ`
of the value space, the conjugate symbols `∂_s ψ̄^φ`, indexed by a covector of the
conjugate value space, and the gauge-field symbols `∂_s A_μ^φ` of the connection factor.
This file packages the matter symbols of each species as families over `s` and proves
their two transformation laws, `LocalGaugeData.TransformsIn` for the jet gauge action and
`IsLorentzDerivTransforms` for the Lorentz action, and packages the connection factor as
a realization of the gauge bosons in `J(T)`, so that the covariant derivative theory of
`Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.CovariantDeriv` applies inside `J(T)`.

## ii. Key results

- `GaugeFieldData.gaugeRealization` : the connection factor as a realization of the gauge
  bosons in `J(T)`.
- `GaugeFieldData.fermionSymbol`, `GaugeFieldData.conjFermionSymbol`,
  `GaugeFieldData.bosonSymbol`, `GaugeFieldData.conjBosonSymbol` : the matter symbols.
- `GaugeFieldData.transformsIn_fermionSymbol`,
  `GaugeFieldData.isLorentzDerivTransforms_fermionSymbol` and companions : their gauge
  and Lorentz laws.

## iii. Table of contents

- A. The connection factor as a realization of the gauge bosons
- B. The matter symbol families
- C. The jet gauge transformation of the matter symbols
- D. The Lorentz transformation of the matter symbols

-/

@[expose] public section

open TensorProduct Matrix MatrixGroups Lorentz

namespace GaugeFieldData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} (T : GaugeFieldData jets)

/-!

## A. The connection factor as a realization of the gauge bosons

-/

/-- The connection factor as a realization of the gauge bosons in `J(T)`: the inclusion of
  the complexified gauge-only algebra, equivariant for both actions, with the included
  gauge-field symbols as its symbols. -/
noncomputable def gaugeRealization :
    GaugeAlgebraRealization jets T.LocalFieldAlgebra T.repJet T.repLorentzGroup where
  toAlgHom := T.includeConnection
  A s μ := (T.includeConnection.restrictScalars ℝ).toLinearMap ∘ₗ
    LocalGaugeFieldAlgebra.gaugeField 𝔤 s μ
  A_eq _ _ _ := rfl
  map_repJet U x := (repJet_includeConnection U x).symm
  map_repLorentz Λ x := (repLorentzGroup_includeConnection Λ x).symm
  repJet_mul := repJet_apply_mul
  repLorentz_mul := repLorentzGroup_apply_mul

variable {T}

lemma gaugeRealization_toAlgHom : T.gaugeRealization.toAlgHom = T.includeConnection := rfl

lemma gaugeRealization_A (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    T.gaugeRealization.A s μ φ
      = T.includeConnection (LocalGaugeFieldAlgebra.gaugeField 𝔤 s μ φ) := rfl

variable (T)

/-!

## B. The matter symbol families

-/

/-- The unconjugated symbols of a fermionic species, as a linear map on the unconjugated
  half of its component space. -/
noncomputable def fermionSymbolMap (i : T.FermionSpecies) :
    DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (T.FermionValue i) →ₗ[ℂ] T.LocalFieldAlgebra :=
  T.ιFermion i ∘ₗ LinearMap.inl ℂ _ _

/-- The conjugate symbols of a fermionic species, as a linear map on the conjugate half of
  its component space. -/
noncomputable def conjFermionSymbolMap (i : T.FermionSpecies) :
    DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule (T.FermionValue i)) →ₗ[ℂ]
      T.LocalFieldAlgebra :=
  T.ιFermion i ∘ₗ LinearMap.inr ℂ _ _

/-- The unconjugated symbols of a bosonic species, as a linear map on the unconjugated
  half of its component space. -/
noncomputable def bosonSymbolMap (j : T.BosonSpecies) :
    DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (T.BosonValue j) →ₗ[ℂ] T.LocalFieldAlgebra :=
  T.ιBoson j ∘ₗ LinearMap.inl ℂ _ _

/-- The conjugate symbols of a bosonic species, as a linear map on the conjugate half of
  its component space. -/
noncomputable def conjBosonSymbolMap (j : T.BosonSpecies) :
    DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule (T.BosonValue j)) →ₗ[ℂ]
      T.LocalFieldAlgebra :=
  T.ιBoson j ∘ₗ LinearMap.inr ℂ _ _

/-- The derivative symbols `∂_s ψ^φ` of a fermionic species: the family over the
  derivative multiset `s`, indexed by the covectors of the value space. -/
noncomputable def fermionSymbol (i : T.FermionSpecies) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (T.FermionValue i) →ₗ[ℂ] T.LocalFieldAlgebra :=
  T.fermionSymbolMap i ∘ₗ TensorProduct.mk ℂ _ _ (DerivAlgebraComplex.basis s)

/-- The conjugate derivative symbols `∂_s ψ̄^φ` of a fermionic species, indexed by the
  covectors of the conjugate value space. -/
noncomputable def conjFermionSymbol (i : T.FermionSpecies) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule (T.FermionValue i)) →ₗ[ℂ] T.LocalFieldAlgebra :=
  T.conjFermionSymbolMap i ∘ₗ TensorProduct.mk ℂ _ _ (DerivAlgebraComplex.basis s)

/-- The derivative symbols `∂_s φ^χ` of a bosonic species. -/
noncomputable def bosonSymbol (j : T.BosonSpecies) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (T.BosonValue j) →ₗ[ℂ] T.LocalFieldAlgebra :=
  T.bosonSymbolMap j ∘ₗ TensorProduct.mk ℂ _ _ (DerivAlgebraComplex.basis s)

/-- The conjugate derivative symbols `∂_s φ̄^χ` of a bosonic species. -/
noncomputable def conjBosonSymbol (j : T.BosonSpecies) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule (T.BosonValue j)) →ₗ[ℂ] T.LocalFieldAlgebra :=
  T.conjBosonSymbolMap j ∘ₗ TensorProduct.mk ℂ _ _ (DerivAlgebraComplex.basis s)

variable {T}

lemma fermionSymbol_apply (i : T.FermionSpecies) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.FermionValue i)) :
    T.fermionSymbol i s φ = T.ιFermion i (DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) := rfl

lemma conjFermionSymbol_apply (i : T.FermionSpecies) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    T.conjFermionSymbol i s φ = T.ιFermion i (0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) := rfl

lemma bosonSymbol_apply (j : T.BosonSpecies) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.BosonValue j)) :
    T.bosonSymbol j s φ = T.ιBoson j (DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ, 0) := rfl

lemma conjBosonSymbol_apply (j : T.BosonSpecies) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    T.conjBosonSymbol j s φ = T.ιBoson j (0, DerivAlgebraComplex.basis s ⊗ₜ[ℂ] φ) := rfl

/-!

## C. The jet gauge transformation of the matter symbols

Each symbol map intertwines the jet gauge action on `J(T)` with `JetComponentSpace.repDual`
on its half of the component space, and the law of the symbols is
`JetComponentSpace.repDual_basis_tmul` pushed through the symbol map.

-/

section GaugeLaw

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]

/-- The transformation law of a family of symbols built from a linear map intertwining the
  jet gauge action with `JetComponentSpace.repDual`. -/
private lemma transformsIn_of_repDual (rep : Representation ℂ GJ (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : GJ) (χ : JetRing) (z : JetRing ⊗[ℂ] V), rep U (χ • z) = χ • rep U z)
    (Φ : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ V →ₗ[ℂ] T.LocalFieldAlgebra)
    (hΦ : ∀ (U : GJ) (x : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ V),
      T.repJet U (Φ x) = Φ (JetComponentSpace.repDual rep hlin U x)) :
    LocalGaugeData.TransformsIn (B := T.LocalFieldAlgebra) T.repJet rep
      (fun s => Φ ∘ₗ TensorProduct.mk ℂ _ _ (DerivAlgebraComplex.basis s)) := by
  intro U φ s
  rw [LinearMap.comp_apply, TensorProduct.mk_apply, hΦ, JetComponentSpace.repDual_basis_tmul,
    map_multiset_sum, Multiset.map_map]
  rfl

/-- The unconjugated fermionic symbol map intertwines the jet gauge actions. -/
lemma repJet_fermionSymbolMap (i : T.FermionSpecies) (U : GJ)
    (x : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (T.FermionValue i)) :
    T.repJet U (T.fermionSymbolMap i x)
      = T.fermionSymbolMap i
        (JetComponentSpace.repDual (T.fermion i).repJet (T.fermion i).repJet_smul U x) := by
  rw [fermionSymbolMap, LinearMap.comp_apply, LinearMap.comp_apply, repJet_ιFermion]
  exact congrArg (T.ιFermion i) (Prod.ext (JetComponentSpace.repJet_fst _ _ _)
    ((JetComponentSpace.repJet_snd _ _ _).trans (map_zero _)))

/-- The conjugate fermionic symbol map intertwines the jet gauge actions. -/
lemma repJet_conjFermionSymbolMap (i : T.FermionSpecies) (U : GJ)
    (x : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    T.repJet U (T.conjFermionSymbolMap i x)
      = T.conjFermionSymbolMap i
        (JetComponentSpace.repDual (JetComponentSpace.repConj (T.fermion i).repJet)
          (JetComponentSpace.repConj_smul_comm (T.fermion i).repJet_smul) U x) := by
  rw [conjFermionSymbolMap, LinearMap.comp_apply, LinearMap.comp_apply, repJet_ιFermion]
  exact congrArg (T.ιFermion i) (Prod.ext ((JetComponentSpace.repJet_fst _ _ _).trans (map_zero _))
    (JetComponentSpace.repJet_snd _ _ _))

/-- The unconjugated bosonic symbol map intertwines the jet gauge actions. -/
lemma repJet_bosonSymbolMap (j : T.BosonSpecies) (U : GJ)
    (x : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (T.BosonValue j)) :
    T.repJet U (T.bosonSymbolMap j x)
      = T.bosonSymbolMap j
        (JetComponentSpace.repDual (T.boson j).repJet (T.boson j).repJet_smul U x) := by
  rw [bosonSymbolMap, LinearMap.comp_apply, LinearMap.comp_apply, repJet_ιBoson]
  exact congrArg (T.ιBoson j) (Prod.ext (JetComponentSpace.repJet_fst _ _ _)
    ((JetComponentSpace.repJet_snd _ _ _).trans (map_zero _)))

/-- The conjugate bosonic symbol map intertwines the jet gauge actions. -/
lemma repJet_conjBosonSymbolMap (j : T.BosonSpecies) (U : GJ)
    (x : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    T.repJet U (T.conjBosonSymbolMap j x)
      = T.conjBosonSymbolMap j
        (JetComponentSpace.repDual (JetComponentSpace.repConj (T.boson j).repJet)
          (JetComponentSpace.repConj_smul_comm (T.boson j).repJet_smul) U x) := by
  rw [conjBosonSymbolMap, LinearMap.comp_apply, LinearMap.comp_apply, repJet_ιBoson]
  exact congrArg (T.ιBoson j) (Prod.ext ((JetComponentSpace.repJet_fst _ _ _).trans (map_zero _))
    (JetComponentSpace.repJet_snd _ _ _))

/-- The symbols of a fermionic species transform in the jet gauge representation of the
  species. -/
lemma transformsIn_fermionSymbol (i : T.FermionSpecies) :
    LocalGaugeData.TransformsIn (B := T.LocalFieldAlgebra) T.repJet (T.fermion i).repJet
      (T.fermionSymbol i) :=
  transformsIn_of_repDual _ _ _ (repJet_fermionSymbolMap i)

/-- The conjugate symbols of a fermionic species transform in the conjugate of the jet
  gauge representation of the species. -/
lemma transformsIn_conjFermionSymbol (i : T.FermionSpecies) :
    LocalGaugeData.TransformsIn (B := T.LocalFieldAlgebra) T.repJet
      (JetComponentSpace.repConj (T.fermion i).repJet) (T.conjFermionSymbol i) :=
  transformsIn_of_repDual _ _ _ (repJet_conjFermionSymbolMap i)

/-- The symbols of a bosonic species transform in the jet gauge representation of the
  species. -/
lemma transformsIn_bosonSymbol (j : T.BosonSpecies) :
    LocalGaugeData.TransformsIn (B := T.LocalFieldAlgebra) T.repJet (T.boson j).repJet
      (T.bosonSymbol j) :=
  transformsIn_of_repDual _ _ _ (repJet_bosonSymbolMap j)

/-- The conjugate symbols of a bosonic species transform in the conjugate of the jet gauge
  representation of the species. -/
lemma transformsIn_conjBosonSymbol (j : T.BosonSpecies) :
    LocalGaugeData.TransformsIn (B := T.LocalFieldAlgebra) T.repJet
      (JetComponentSpace.repConj (T.boson j).repJet) (T.conjBosonSymbol j) :=
  transformsIn_of_repDual _ _ _ (repJet_conjBosonSymbolMap j)

end GaugeLaw

/-!

## D. The Lorentz transformation of the matter symbols

Each symbol map intertwines the Lorentz action on `J(T)` with the tensor product of the
action on derivative labels and the contragredient action on the value index, and the law
of the symbols is that of the derivative monomials,
`DerivAlgebraComplex.repLorentzGroup_basis_ofFn`.

-/

section LorentzLaw

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The Lorentz law of a family of symbols built from a linear map intertwining the Lorentz
  action with the tensor product of the action on derivative labels and a representation on
  the covectors. -/
private lemma isLorentzDerivTransforms_of_tprod (rep : Representation ℂ SL(2,ℂ) V)
    (Φ : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ V →ₗ[ℂ] T.LocalFieldAlgebra)
    (hΦ : ∀ (Λ : SL(2,ℂ)) (x : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ V),
      T.repLorentzGroup Λ (Φ x)
        = Φ ((DerivAlgebraComplex.repLorentzGroup.tprod rep.dual) Λ x)) :
    IsLorentzDerivTransforms (A := T.LocalFieldAlgebra) T.repLorentzGroup rep
      (fun s => Φ ∘ₗ TensorProduct.mk ℂ _ _ (DerivAlgebraComplex.basis s)) := by
  intro Λ n l φ
  rw [LinearMap.comp_apply, TensorProduct.mk_apply, hΦ, Representation.tprod_apply,
    TensorProduct.map_tmul, DerivAlgebraComplex.repLorentzGroup_basis_ofFn,
    TensorProduct.sum_tmul, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← TensorProduct.smul_tmul', map_smul]
  rfl

/-- The unconjugated fermionic symbol map intertwines the Lorentz actions. -/
lemma repLorentzGroup_fermionSymbolMap (i : T.FermionSpecies) (Λ : SL(2,ℂ))
    (x : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (T.FermionValue i)) :
    T.repLorentzGroup Λ (T.fermionSymbolMap i x)
      = T.fermionSymbolMap i
        ((DerivAlgebraComplex.repLorentzGroup.tprod (T.fermion i).repLorentz.dual) Λ x) := by
  rw [fermionSymbolMap, LinearMap.comp_apply, LinearMap.comp_apply, repLorentzGroup_ιFermion]
  exact congrArg (T.ιFermion i) (Prod.ext (JetComponentSpace.repLorentzGroup_fst _ _)
    ((JetComponentSpace.repLorentzGroup_snd _ _).trans (map_zero _)))

/-- The conjugate fermionic symbol map intertwines the Lorentz actions. -/
lemma repLorentzGroup_conjFermionSymbolMap (i : T.FermionSpecies) (Λ : SL(2,ℂ))
    (x : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    T.repLorentzGroup Λ (T.conjFermionSymbolMap i x)
      = T.conjFermionSymbolMap i
        ((DerivAlgebraComplex.repLorentzGroup.tprod (T.fermion i).repLorentz.conj.dual) Λ x) := by
  rw [conjFermionSymbolMap, LinearMap.comp_apply, LinearMap.comp_apply, repLorentzGroup_ιFermion]
  exact congrArg (T.ιFermion i)
    (Prod.ext ((JetComponentSpace.repLorentzGroup_fst _ _).trans (map_zero _))
      (JetComponentSpace.repLorentzGroup_snd _ _))

/-- The unconjugated bosonic symbol map intertwines the Lorentz actions. -/
lemma repLorentzGroup_bosonSymbolMap (j : T.BosonSpecies) (Λ : SL(2,ℂ))
    (x : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (T.BosonValue j)) :
    T.repLorentzGroup Λ (T.bosonSymbolMap j x)
      = T.bosonSymbolMap j
        ((DerivAlgebraComplex.repLorentzGroup.tprod (T.boson j).repLorentz.dual) Λ x) := by
  rw [bosonSymbolMap, LinearMap.comp_apply, LinearMap.comp_apply, repLorentzGroup_ιBoson]
  exact congrArg (T.ιBoson j) (Prod.ext (JetComponentSpace.repLorentzGroup_fst _ _)
    ((JetComponentSpace.repLorentzGroup_snd _ _).trans (map_zero _)))

/-- The conjugate bosonic symbol map intertwines the Lorentz actions. -/
lemma repLorentzGroup_conjBosonSymbolMap (j : T.BosonSpecies) (Λ : SL(2,ℂ))
    (x : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    T.repLorentzGroup Λ (T.conjBosonSymbolMap j x)
      = T.conjBosonSymbolMap j
        ((DerivAlgebraComplex.repLorentzGroup.tprod (T.boson j).repLorentz.conj.dual) Λ x) := by
  rw [conjBosonSymbolMap, LinearMap.comp_apply, LinearMap.comp_apply, repLorentzGroup_ιBoson]
  exact congrArg (T.ιBoson j)
    (Prod.ext ((JetComponentSpace.repLorentzGroup_fst _ _).trans (map_zero _))
      (JetComponentSpace.repLorentzGroup_snd _ _))

/-- The symbols of a fermionic species transform as the derivative symbols of a field in
  the Lorentz representation of the species. -/
lemma isLorentzDerivTransforms_fermionSymbol (i : T.FermionSpecies) :
    IsLorentzDerivTransforms (A := T.LocalFieldAlgebra) T.repLorentzGroup
      (T.fermion i).repLorentz (T.fermionSymbol i) :=
  isLorentzDerivTransforms_of_tprod _ _ (repLorentzGroup_fermionSymbolMap i)

/-- The conjugate symbols of a fermionic species transform as the derivative symbols of a
  field in the conjugate of the Lorentz representation of the species. -/
lemma isLorentzDerivTransforms_conjFermionSymbol (i : T.FermionSpecies) :
    IsLorentzDerivTransforms (A := T.LocalFieldAlgebra) T.repLorentzGroup
      (T.fermion i).repLorentz.conj (T.conjFermionSymbol i) :=
  isLorentzDerivTransforms_of_tprod _ _ (repLorentzGroup_conjFermionSymbolMap i)

/-- The symbols of a bosonic species transform as the derivative symbols of a field in the
  Lorentz representation of the species. -/
lemma isLorentzDerivTransforms_bosonSymbol (j : T.BosonSpecies) :
    IsLorentzDerivTransforms (A := T.LocalFieldAlgebra) T.repLorentzGroup
      (T.boson j).repLorentz (T.bosonSymbol j) :=
  isLorentzDerivTransforms_of_tprod _ _ (repLorentzGroup_bosonSymbolMap j)

/-- The conjugate symbols of a bosonic species transform as the derivative symbols of a
  field in the conjugate of the Lorentz representation of the species. -/
lemma isLorentzDerivTransforms_conjBosonSymbol (j : T.BosonSpecies) :
    IsLorentzDerivTransforms (A := T.LocalFieldAlgebra) T.repLorentzGroup
      (T.boson j).repLorentz.conj (T.conjBosonSymbol j) :=
  isLorentzDerivTransforms_of_tprod _ _ (repLorentzGroup_conjBosonSymbolMap j)

end LorentzLaw

end GaugeFieldData
