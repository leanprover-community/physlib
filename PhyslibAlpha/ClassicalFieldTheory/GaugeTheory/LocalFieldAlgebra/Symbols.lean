/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.GaugeAction
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.LorentzAction
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.FieldDerivSpace.JetCoeffAt
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.GaugeField
/-!
# The field symbols of the local field algebra and their transformation laws

The derivative symbols of the matter species as families in the local field algebra, with their
gauge and Lorentz laws.

## i. Overview

The generators of the local field algebra `J(T)` of a field datum are the derivative
symbols of its species. These are `∂_s ψ^φ`, indexed by a derivative multiset `s` and a covector `φ`
of the value space, the conjugate symbols `∂_s ψ̄^φ`, indexed by a covector of the
conjugate value space, and the gauge-field symbols `∂_s A_μ^φ` of the connection factor.
This file packages the matter symbols of each species as families over `s` and proves
their two transformation laws, the Leibniz convolution law for the jet gauge action and
`IsLorentzDerivTransforms` for the Lorentz action. The gauge-field symbols of `J(T)` are those
of the gauge-boson jet algebra carried in by the inclusion of the connection factor,
`GaugeFieldData.gaugeField`. The inclusion intertwines both actions, so they transform
as a gauge field under both, and the covariant derivative theory of
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.CovariantDeriv`
applies inside `J(T)`.

## ii. Key results

- `GaugeFieldData.gaugeField` : the gauge-field symbols of `J(T)`.
- `GaugeFieldData.transformsAsGaugeField_gaugeField`,
  `GaugeFieldData.lorentzTransformsAsGaugeField_gaugeField` : their gauge and Lorentz laws.
- `GaugeFieldData.fermionSymbol`, `GaugeFieldData.conjFermionSymbol`,
  `GaugeFieldData.bosonSymbol`, `GaugeFieldData.conjBosonSymbol` : the matter symbols.
- `GaugeFieldData.repJet_fermionSymbol`,
  `GaugeFieldData.isLorentzDerivTransforms_fermionSymbol` and companions : their gauge
  and Lorentz laws.

## iii. Table of contents

- A. The gauge-field symbols of the connection factor
- B. The matter symbol families
- C. The jet gauge transformation of the matter symbols
- D. The Lorentz transformation of the matter symbols

## iv. References

* None.

-/

@[expose] public section

open TensorProduct Matrix MatrixGroups Lorentz
open GlobalGaugeGroup (repDualCoeff)
open LocalGaugeFieldAlgebra (mapGaugeField)

namespace GaugeFieldData

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ} (T : GaugeFieldData G)

/-!

## A. The gauge-field symbols of the connection factor

-/

/-- The gauge-field symbols `∂_s A_μ^φ` of `J(T)`, the symbols of the gauge-boson jet algebra
  carried in by the inclusion of the connection factor. The real structure on `J(T)` is the
  one restricted from its complex structure, as for every family of symbols in a complex
  algebra. -/
noncomputable def gaugeField :=
  mapGaugeField (B := T.LocalFieldAlgebra) T.includeConnection

variable {T}

@[simp]
lemma gaugeField_apply (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    T.gaugeField s μ φ = T.includeConnection (LocalGaugeFieldAlgebra.gaugeField G s μ φ) := rfl

/-- The gauge-field symbols of `J(T)` transform as a gauge field under the jet gauge group,
  since the inclusion of the connection factor intertwines the two actions. -/
lemma transformsAsGaugeField_gaugeField :
    GaugeBoson.TransformsAsGaugeField G T.repJet T.gaugeField :=
  LocalGaugeFieldAlgebra.transformsAsGaugeField_mapGaugeField _
    fun U x => (repJet_includeConnection U x).symm

/-- The gauge-field symbols of `J(T)` transform as a gauge field under the Lorentz group. -/
lemma lorentzTransformsAsGaugeField_gaugeField :
    GaugeBoson.LorentzTransformsAsGaugeField T.repLorentzGroup T.gaugeField :=
  LocalGaugeFieldAlgebra.lorentzTransformsAsGaugeField_mapGaugeField _
    fun Λ x => (repLorentzGroup_includeConnection Λ x).symm

variable (T)

/-!

## B. The matter symbol families

-/

/-- The unconjugated symbols of a fermionic species, as a linear map on the unconjugated
  half of its component space. -/
noncomputable def fermionSymbolMap (i : T.FermionSpecies) :
    SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (T.FermionValue i) →ₗ[ℂ] T.LocalFieldAlgebra :=
  T.ιFermion i ∘ₗ LinearMap.inl ℂ _ _

/-- The conjugate symbols of a fermionic species, as a linear map on the conjugate half of
  its component space. -/
noncomputable def conjFermionSymbolMap (i : T.FermionSpecies) :
    SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (ConjModule (T.FermionValue i)) →ₗ[ℂ]
      T.LocalFieldAlgebra :=
  T.ιFermion i ∘ₗ LinearMap.inr ℂ _ _

/-- The unconjugated symbols of a bosonic species, as a linear map on the unconjugated
  half of its component space. -/
noncomputable def bosonSymbolMap (j : T.BosonSpecies) :
    SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (T.BosonValue j) →ₗ[ℂ] T.LocalFieldAlgebra :=
  T.ιBoson j ∘ₗ LinearMap.inl ℂ _ _

/-- The conjugate symbols of a bosonic species, as a linear map on the conjugate half of
  its component space. -/
noncomputable def conjBosonSymbolMap (j : T.BosonSpecies) :
    SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (ConjModule (T.BosonValue j)) →ₗ[ℂ]
      T.LocalFieldAlgebra :=
  T.ιBoson j ∘ₗ LinearMap.inr ℂ _ _

/-- The derivative symbols `∂_s ψ^φ` of a fermionic species, the family over the
  derivative multiset `s`, indexed by the covectors of the value space. -/
noncomputable def fermionSymbol (i : T.FermionSpecies) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (T.FermionValue i) →ₗ[ℂ] T.LocalFieldAlgebra :=
  T.fermionSymbolMap i ∘ₗ TensorProduct.mk ℂ _ _ (SpaceTimeDerivAlgebraℂ.basis s)

/-- The conjugate derivative symbols `∂_s ψ̄^φ` of a fermionic species, indexed by the
  covectors of the conjugate value space. -/
noncomputable def conjFermionSymbol (i : T.FermionSpecies) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule (T.FermionValue i)) →ₗ[ℂ] T.LocalFieldAlgebra :=
  T.conjFermionSymbolMap i ∘ₗ TensorProduct.mk ℂ _ _ (SpaceTimeDerivAlgebraℂ.basis s)

/-- The derivative symbols `∂_s φ^χ` of a bosonic species. -/
noncomputable def bosonSymbol (j : T.BosonSpecies) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (T.BosonValue j) →ₗ[ℂ] T.LocalFieldAlgebra :=
  T.bosonSymbolMap j ∘ₗ TensorProduct.mk ℂ _ _ (SpaceTimeDerivAlgebraℂ.basis s)

/-- The conjugate derivative symbols `∂_s φ̄^χ` of a bosonic species. -/
noncomputable def conjBosonSymbol (j : T.BosonSpecies) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule (T.BosonValue j)) →ₗ[ℂ] T.LocalFieldAlgebra :=
  T.conjBosonSymbolMap j ∘ₗ TensorProduct.mk ℂ _ _ (SpaceTimeDerivAlgebraℂ.basis s)

variable {T}

lemma fermionSymbol_apply (i : T.FermionSpecies) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.FermionValue i)) :
    T.fermionSymbol i s φ = T.ιFermion i (SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ, 0) := rfl

lemma conjFermionSymbol_apply (i : T.FermionSpecies) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    T.conjFermionSymbol i s φ = T.ιFermion i (0, SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ) := rfl

lemma bosonSymbol_apply (j : T.BosonSpecies) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.BosonValue j)) :
    T.bosonSymbol j s φ = T.ιBoson j (SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ, 0) := rfl

lemma conjBosonSymbol_apply (j : T.BosonSpecies) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    T.conjBosonSymbol j s φ = T.ιBoson j (0, SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ) := rfl

/-!

## C. The jet gauge transformation of the matter symbols

Each symbol map intertwines the jet gauge action on `J(T)` with `FieldDerivSpace.repDual`
on its half of the component space, and the law of the symbols is
`FieldDerivSpace.repDual_basis_tmul` pushed through the symbol map.

-/

section GaugeLaw

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]

/-- The transformation law of a family of symbols built from a linear map intertwining the
  jet gauge action with `FieldDerivSpace.repDual`. -/
private lemma repJet_symbol_of_repDual
    (rep : Representation ℂ G.gaugeJetGroup (SpaceTimeAlgebra ⊗[ℂ] V))
    (hlin : ∀ (U : G.gaugeJetGroup) (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (Φ : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ V →ₗ[ℂ] T.LocalFieldAlgebra)
    (hΦ : ∀ (U : G.gaugeJetGroup) (x : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ V),
      T.repJet U (Φ x) = Φ (FieldDerivSpace.repDual rep hlin U x))
    (U : G.gaugeJetGroup) (φ : Module.Dual ℂ V) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    T.repJet U ((Φ ∘ₗ TensorProduct.mk ℂ _ _ (SpaceTimeDerivAlgebraℂ.basis s)) φ) =
      (s.antidiagonal.map fun p => (Φ ∘ₗ TensorProduct.mk ℂ _ _
        (SpaceTimeDerivAlgebraℂ.basis p.2)) (repDualCoeff rep U⁻¹ p.1 φ)).sum := by
  rw [LinearMap.comp_apply, TensorProduct.mk_apply, hΦ, FieldDerivSpace.repDual_basis_tmul,
    map_multiset_sum, Multiset.map_map]
  rfl

/-- The unconjugated fermionic symbol map intertwines the jet gauge actions. -/
lemma repJet_fermionSymbolMap (i : T.FermionSpecies) (U : G.gaugeJetGroup)
    (x : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (T.FermionValue i)) :
    T.repJet U (T.fermionSymbolMap i x)
      = T.fermionSymbolMap i
        (FieldDerivSpace.repDual (T.fermion i).repJet (T.fermion i).repJet_smul U x) := by
  rw [fermionSymbolMap, LinearMap.comp_apply, LinearMap.comp_apply, repJet_ιFermion]
  exact congrArg (T.ιFermion i) (Prod.ext (FieldDerivSpace.repJet_fst (T.fermion i) U _)
    ((FieldDerivSpace.repJet_snd (T.fermion i) U _).trans (map_zero _)))

/-- The conjugate fermionic symbol map intertwines the jet gauge actions. -/
lemma repJet_conjFermionSymbolMap (i : T.FermionSpecies) (U : G.gaugeJetGroup)
    (x : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    T.repJet U (T.conjFermionSymbolMap i x)
      = T.conjFermionSymbolMap i
        (FieldDerivSpace.repDual (FieldDerivSpace.repConj (T.fermion i).repJet)
          (FieldDerivSpace.repConj_smul_comm (T.fermion i).repJet_smul) U x) := by
  rw [conjFermionSymbolMap, LinearMap.comp_apply, LinearMap.comp_apply, repJet_ιFermion]
  exact congrArg (T.ιFermion i) (Prod.ext ((FieldDerivSpace.repJet_fst _ _ _).trans (map_zero _))
    (FieldDerivSpace.repJet_snd _ _ _))

/-- The unconjugated bosonic symbol map intertwines the jet gauge actions. -/
lemma repJet_bosonSymbolMap (j : T.BosonSpecies) (U : G.gaugeJetGroup)
    (x : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (T.BosonValue j)) :
    T.repJet U (T.bosonSymbolMap j x)
      = T.bosonSymbolMap j
        (FieldDerivSpace.repDual (T.boson j).repJet (T.boson j).repJet_smul U x) := by
  rw [bosonSymbolMap, LinearMap.comp_apply, LinearMap.comp_apply, repJet_ιBoson]
  exact congrArg (T.ιBoson j) (Prod.ext (FieldDerivSpace.repJet_fst (T.boson j) U _)
    ((FieldDerivSpace.repJet_snd (T.boson j) U _).trans (map_zero _)))

/-- The conjugate bosonic symbol map intertwines the jet gauge actions. -/
lemma repJet_conjBosonSymbolMap (j : T.BosonSpecies) (U : G.gaugeJetGroup)
    (x : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    T.repJet U (T.conjBosonSymbolMap j x)
      = T.conjBosonSymbolMap j
        (FieldDerivSpace.repDual (FieldDerivSpace.repConj (T.boson j).repJet)
          (FieldDerivSpace.repConj_smul_comm (T.boson j).repJet_smul) U x) := by
  rw [conjBosonSymbolMap, LinearMap.comp_apply, LinearMap.comp_apply, repJet_ιBoson]
  exact congrArg (T.ιBoson j) (Prod.ext ((FieldDerivSpace.repJet_fst _ _ _).trans (map_zero _))
    (FieldDerivSpace.repJet_snd _ _ _))

/-- The symbols of a fermionic species transform in the jet gauge representation of the
  species, each derivative symbol by the Leibniz convolution of the dual base-point
  coefficients against the lower symbols. -/
lemma repJet_fermionSymbol (i : T.FermionSpecies) (U : G.gaugeJetGroup)
    (φ : Module.Dual ℂ (T.FermionValue i)) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    T.repJet U (T.fermionSymbol i s φ) =
      (s.antidiagonal.map fun p =>
        T.fermionSymbol i p.2 (repDualCoeff (T.fermion i).repJet U⁻¹ p.1 φ)).sum :=
  repJet_symbol_of_repDual _ _ _ (repJet_fermionSymbolMap i) U φ s

/-- The conjugate symbols of a fermionic species transform in the conjugate of the jet
  gauge representation of the species. -/
lemma repJet_conjFermionSymbol (i : T.FermionSpecies) (U : G.gaugeJetGroup)
    (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    T.repJet U (T.conjFermionSymbol i s φ) =
      (s.antidiagonal.map fun p =>
        T.conjFermionSymbol i p.2
          (repDualCoeff (FieldDerivSpace.repConj (T.fermion i).repJet) U⁻¹ p.1 φ)).sum :=
  repJet_symbol_of_repDual _ _ _ (repJet_conjFermionSymbolMap i) U φ s

/-- The symbols of a bosonic species transform in the jet gauge representation of the
  species. -/
lemma repJet_bosonSymbol (j : T.BosonSpecies) (U : G.gaugeJetGroup)
    (φ : Module.Dual ℂ (T.BosonValue j)) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    T.repJet U (T.bosonSymbol j s φ) =
      (s.antidiagonal.map fun p =>
        T.bosonSymbol j p.2 (repDualCoeff (T.boson j).repJet U⁻¹ p.1 φ)).sum :=
  repJet_symbol_of_repDual _ _ _ (repJet_bosonSymbolMap j) U φ s

/-- The conjugate symbols of a bosonic species transform in the conjugate of the jet gauge
  representation of the species. -/
lemma repJet_conjBosonSymbol (j : T.BosonSpecies) (U : G.gaugeJetGroup)
    (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    T.repJet U (T.conjBosonSymbol j s φ) =
      (s.antidiagonal.map fun p =>
        T.conjBosonSymbol j p.2
          (repDualCoeff (FieldDerivSpace.repConj (T.boson j).repJet) U⁻¹ p.1 φ)).sum :=
  repJet_symbol_of_repDual _ _ _ (repJet_conjBosonSymbolMap j) U φ s

end GaugeLaw

/-!

## D. The Lorentz transformation of the matter symbols

Each symbol map intertwines the Lorentz action on `J(T)` with the tensor product of the
action on derivative labels and the contragredient action on the value index, and the law
of the symbols is that of the derivative monomials,
`SpaceTimeDerivAlgebraℂ.repLorentzGroup_basis_ofFn`.

-/

section LorentzLaw

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The Lorentz law of a family of symbols built from a linear map intertwining the Lorentz
  action with the tensor product of the action on derivative labels and a representation on
  the covectors. -/
private lemma isLorentzDerivTransforms_of_tprod (rep : Representation ℂ SL(2,ℂ) V)
    (Φ : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ V →ₗ[ℂ] T.LocalFieldAlgebra)
    (hΦ : ∀ (Λ : SL(2,ℂ)) (x : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ V),
      T.repLorentzGroup Λ (Φ x)
        = Φ ((SpaceTimeDerivAlgebraℂ.repLorentzGroup.tprod rep.dual) Λ x)) :
    IsLorentzDerivTransforms (A := T.LocalFieldAlgebra) T.repLorentzGroup rep
      (fun s => Φ ∘ₗ TensorProduct.mk ℂ _ _ (SpaceTimeDerivAlgebraℂ.basis s)) := by
  intro Λ n l φ
  rw [LinearMap.comp_apply, TensorProduct.mk_apply, hΦ, Representation.tprod_apply,
    TensorProduct.map_tmul, SpaceTimeDerivAlgebraℂ.repLorentzGroup_basis_ofFn,
    TensorProduct.sum_tmul, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← TensorProduct.smul_tmul', map_smul]
  rfl

/-- The unconjugated fermionic symbol map intertwines the Lorentz actions. -/
lemma repLorentzGroup_fermionSymbolMap (i : T.FermionSpecies) (Λ : SL(2,ℂ))
    (x : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (T.FermionValue i)) :
    T.repLorentzGroup Λ (T.fermionSymbolMap i x)
      = T.fermionSymbolMap i
        ((SpaceTimeDerivAlgebraℂ.repLorentzGroup.tprod (T.fermion i).repLorentz.dual) Λ x) := by
  rw [fermionSymbolMap, LinearMap.comp_apply, LinearMap.comp_apply, repLorentzGroup_ιFermion]
  exact congrArg (T.ιFermion i) (Prod.ext (FieldDerivSpace.repLorentzGroup_fst _ _)
    ((FieldDerivSpace.repLorentzGroup_snd _ _).trans (map_zero _)))

/-- The conjugate fermionic symbol map intertwines the Lorentz actions. -/
lemma repLorentzGroup_conjFermionSymbolMap (i : T.FermionSpecies) (Λ : SL(2,ℂ))
    (x : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    T.repLorentzGroup Λ (T.conjFermionSymbolMap i x)
      = T.conjFermionSymbolMap i
        ((SpaceTimeDerivAlgebraℂ.repLorentzGroup.tprod
            (T.fermion i).repLorentz.conj.dual) Λ x) := by
  rw [conjFermionSymbolMap, LinearMap.comp_apply, LinearMap.comp_apply, repLorentzGroup_ιFermion]
  exact congrArg (T.ιFermion i)
    (Prod.ext ((FieldDerivSpace.repLorentzGroup_fst _ _).trans (map_zero _))
      (FieldDerivSpace.repLorentzGroup_snd _ _))

/-- The unconjugated bosonic symbol map intertwines the Lorentz actions. -/
lemma repLorentzGroup_bosonSymbolMap (j : T.BosonSpecies) (Λ : SL(2,ℂ))
    (x : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (T.BosonValue j)) :
    T.repLorentzGroup Λ (T.bosonSymbolMap j x)
      = T.bosonSymbolMap j
        ((SpaceTimeDerivAlgebraℂ.repLorentzGroup.tprod (T.boson j).repLorentz.dual) Λ x) := by
  rw [bosonSymbolMap, LinearMap.comp_apply, LinearMap.comp_apply, repLorentzGroup_ιBoson]
  exact congrArg (T.ιBoson j) (Prod.ext (FieldDerivSpace.repLorentzGroup_fst _ _)
    ((FieldDerivSpace.repLorentzGroup_snd _ _).trans (map_zero _)))

/-- The conjugate bosonic symbol map intertwines the Lorentz actions. -/
lemma repLorentzGroup_conjBosonSymbolMap (j : T.BosonSpecies) (Λ : SL(2,ℂ))
    (x : SpaceTimeDerivAlgebraℂ ⊗[ℂ] Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    T.repLorentzGroup Λ (T.conjBosonSymbolMap j x)
      = T.conjBosonSymbolMap j
        ((SpaceTimeDerivAlgebraℂ.repLorentzGroup.tprod (T.boson j).repLorentz.conj.dual) Λ x) := by
  rw [conjBosonSymbolMap, LinearMap.comp_apply, LinearMap.comp_apply, repLorentzGroup_ιBoson]
  exact congrArg (T.ιBoson j)
    (Prod.ext ((FieldDerivSpace.repLorentzGroup_fst _ _).trans (map_zero _))
      (FieldDerivSpace.repLorentzGroup_snd _ _))

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
