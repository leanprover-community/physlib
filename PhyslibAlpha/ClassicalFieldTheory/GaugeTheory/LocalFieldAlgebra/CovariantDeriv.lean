/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Symbols
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.LorentzCovariantDeriv
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.FieldStrength
/-!
# The covariant derivatives in the local field algebra

The iterated covariant derivatives of the matter fields and of the field strength in the local
field algebra, with their gauge and Lorentz laws.

## i. Overview

The covariant expressions of a gauge theory are the iterated covariant derivatives of its
matter fields and of the field strength, built here inside the local field algebra `J(T)`
of a field datum. For a matter species the tower is `GlobalGaugeGroup.covDerivIter`
on the symbol family of the species, `∇_{l 0} ⋯ ∇_{l (n-1)} ψ` along an ordered tuple `l`
of directions, with `∇_ρ F = [∂_ρ F] + A_ρ · F` through the infinitesimal action
`repAlgebra` of the species on the value index, the conjugate components through the
conjugate action. Zero derivatives is the undifferentiated symbol, and the ordered labels
are kept, so nothing is identified with the multiset-indexed ordinary derivatives. For the
gauge bosons the tower is the gauge-only `LocalGaugeFieldAlgebra.covDerivFieldStrength`,
included through the connection factor.

A jet acts on every tower through the base-point Taylor coefficient of its inverse on the
value index alone, and the action on a matter tower factors through evaluation to the ordinary
gauge group, since pure jets act trivially. A Lorentz transformation mixes the covariant
slots by the columns of the Lorentz matrix and the value index contragrediently. For the
matter towers this needs `GlobalGaugeGroup.MatterField.GaugeLorentzCompatible`, and for the
field strength it holds unconditionally.

## ii. Key results

- `GaugeFieldData.covDerivFermion`, `GaugeFieldData.covDerivConjFermion`,
  `GaugeFieldData.covDerivBoson`, `GaugeFieldData.covDerivConjBoson`,
  `GaugeFieldData.covDerivFieldStrength` : the covariant towers.
- `GaugeFieldData.repJet_covDerivFermion` and companions : the gauge laws.
- `GaugeFieldData.repJet_covDerivFermion_ofConstant_eval` and companions : the
  factorization through evaluation.
- `GaugeFieldData.repLorentzGroup_covDerivFermion` and companions : the Lorentz laws.
- `GaugeFieldData.repLorentzGroup_covDerivFermion_mem` and companions : a Lorentz
  transformation of a tower element lies in any subalgebra containing the tower.
- `GaugeFieldData.commute_covDerivFieldStrength`, `GaugeFieldData.commute_covDerivBoson` : the
  field-strength and bosonic towers are central.
- `GaugeFieldData.covDerivFermion_anticomm_covDerivFermion` and companions : any two fermionic
  towers anticommute.
- `GaugeFieldData.covDerivFieldStrength_swap`,
  `GaugeFieldData.covDerivFieldStrength_eq_of_perm_of_map_lie` : the field-strength tower is
  antisymmetric in its covector indices, and symmetric in its derivative slots along a
  functional vanishing on brackets.
- `GaugeFieldData.massWeight_covDerivFermion` and companions : for a mass-weight algebra map
  under which the gauge field has weight `2` and a species weight `c`, the covariant towers
  are eigenvectors of the predicted weights.

## iii. Table of contents

- A. The covariant matter towers
- B. The included field-strength tower
- C. The gauge laws
- D. The Lorentz laws
  - D.1. Transformed tower elements in a subalgebra containing the tower
- E. Statistics and symmetries of the towers
  - E.1. Centrality of the bosonic towers
  - E.2. Anticommutation of the fermionic towers
  - E.3. The symmetries of the field-strength tower
- F. Mass weights of the towers

## iv. References

* None.

-/

@[expose] public section

open TensorProduct Matrix MatrixGroups Lorentz
open GlobalGaugeGroup (covDerivIter covDerivAction actionFamConv repDualCoeff)
open GaugeBoson (fieldStrength iteratedCovDerivAdjoint)

namespace GaugeFieldData

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ} (T : GaugeFieldData G)

/-!

## A. The covariant matter towers

-/

/-- The iterated covariant derivative `∇_{l 0} ⋯ ∇_{l (n-1)} ψ` of a fermionic species along
  an ordered tuple of directions, as a family over the covectors of its value space. -/
noncomputable def covDerivFermion (i : T.FermionSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (T.FermionValue i) →ₗ[ℂ] T.LocalFieldAlgebra :=
  covDerivIter T.gaugeField (T.fermion i).repAlgebra (T.fermionSymbol i) n l 0

/-- The iterated covariant derivative of the conjugate components of a fermionic species,
  through the conjugate infinitesimal action. -/
noncomputable def covDerivConjFermion (i : T.FermionSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule (T.FermionValue i)) →ₗ[ℂ] T.LocalFieldAlgebra :=
  covDerivIter T.gaugeField (GlobalGaugeGroup.actionConj (T.fermion i).repAlgebra)
    (T.conjFermionSymbol i) n l 0

/-- The iterated covariant derivative of a bosonic species. -/
noncomputable def covDerivBoson (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (T.BosonValue j) →ₗ[ℂ] T.LocalFieldAlgebra :=
  covDerivIter T.gaugeField (T.boson j).repAlgebra (T.bosonSymbol j) n l 0

/-- The iterated covariant derivative of the conjugate components of a bosonic species. -/
noncomputable def covDerivConjBoson (j : T.BosonSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule (T.BosonValue j)) →ₗ[ℂ] T.LocalFieldAlgebra :=
  covDerivIter T.gaugeField (GlobalGaugeGroup.actionConj (T.boson j).repAlgebra)
    (T.conjBosonSymbol j) n l 0

/-!

## B. The included field-strength tower

-/

/-- The field strength and its ordered covariant derivatives `∇_l F_μν^φ`, included from
  the real gauge-only algebra through the connection factor. -/
noncomputable def covDerivFieldStrength (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ G.lieSubalgebra →ₗ[ℝ] T.LocalFieldAlgebra :=
  (T.includeConnection.restrictScalars ℝ).toLinearMap ∘ₗ
    (Algebra.TensorProduct.includeRight (R := ℝ) (A := ℂ)
      (B := LocalGaugeFieldAlgebra G)).toLinearMap ∘ₗ
    LocalGaugeFieldAlgebra.covDerivFieldStrength G l μ ν

variable {T}

lemma covDerivFieldStrength_apply (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    T.covDerivFieldStrength l μ ν φ
      = T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ]
          LocalGaugeFieldAlgebra.covDerivFieldStrength G l μ ν φ) := rfl

/-- Zero covariant derivatives give the included field strength. -/
lemma covDerivFieldStrength_nil (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    T.covDerivFieldStrength [] μ ν φ
      = T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ] LocalGaugeFieldAlgebra.fieldStrength G μ ν
        φ) := rfl

/-- The included tower is the covariant tower of the gauge-field symbols of `J(T)` computed
  by the realization theory, the tower being natural along the inclusion of the connection
  factor. -/
lemma covDerivFieldStrength_eq_iteratedCovDerivAdjoint (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    T.covDerivFieldStrength l μ ν φ
      = iteratedCovDerivAdjoint T.gaugeField l
          (fieldStrength T.gaugeField μ ν) 0 φ := by
  let ι : (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G) →ₗ[ℝ] T.LocalFieldAlgebra :=
    T.includeConnection.toLinearMap.restrictScalars ℝ
  have hmul : ∀ x y, ι (x * y) = ι x * ι y := fun x y => map_mul T.includeConnection x y
  have hF : ∀ p, ι ∘ₗ fieldStrength (LocalGaugeFieldAlgebra.gaugeField G) μ ν p
      = fieldStrength (B := T.LocalFieldAlgebra)
          (fun p ρ => ι ∘ₗ LocalGaugeFieldAlgebra.gaugeField G p ρ) μ ν p :=
    fun p => (GaugeBoson.fieldStrength_map
      (B := ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G) (B' := T.LocalFieldAlgebra) ι hmul
      (LocalGaugeFieldAlgebra.gaugeField G) μ ν p).symm
  have key : iteratedCovDerivAdjoint (B := T.LocalFieldAlgebra)
      (fun p ρ => ι ∘ₗ LocalGaugeFieldAlgebra.gaugeField G p ρ) l
      (fieldStrength (B := T.LocalFieldAlgebra)
        (fun p ρ => ι ∘ₗ LocalGaugeFieldAlgebra.gaugeField G p ρ) μ ν) 0 φ
      = ι (iteratedCovDerivAdjoint (LocalGaugeFieldAlgebra.gaugeField G) l
          (fieldStrength (LocalGaugeFieldAlgebra.gaugeField G) μ ν) 0 φ) := by
    rw [← funext hF]
    exact LinearMap.congr_fun (congrFun (GaugeBoson.iteratedCovDerivAdjoint_map
      (B := ℂ ⊗[ℝ] LocalGaugeFieldAlgebra G) (B' := T.LocalFieldAlgebra) ι hmul
      (LocalGaugeFieldAlgebra.gaugeField G) l
      (fieldStrength (LocalGaugeFieldAlgebra.gaugeField G) μ ν)) 0) φ
  rw [covDerivFieldStrength_apply, LocalGaugeFieldAlgebra.covDerivFieldStrength,
    LocalGaugeFieldAlgebra.one_tmul_iteratedCovDerivAdjoint_fieldStrength]
  exact key.symm

/-!

## C. The gauge laws

-/

section GaugeLaws

variable (U : G.gaugeJetGroup)

/-- The gauge law of the covariant tower of a fermionic species. A jet acts through the
  zeroth dual Taylor coefficient of its inverse on the value index alone. -/
lemma repJet_covDerivFermion (i : T.FermionSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.FermionValue i)) :
    T.repJet U (T.covDerivFermion i l φ)
      = T.covDerivFermion i l (repDualCoeff (T.fermion i).repJet U⁻¹ 0 φ) :=
  (T.fermion i).isInfinitesimalActionOf.repGauge_covDerivIter_zero
    transformsAsGaugeField_gaugeField repJet_apply_mul
    (repJet_fermionSymbol i) n l U φ

/-- The gauge law of the conjugate covariant tower of a fermionic species, through the
  conjugate representation. -/
lemma repJet_covDerivConjFermion (i : T.FermionSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    T.repJet U (T.covDerivConjFermion i l φ)
      = T.covDerivConjFermion i l
          (repDualCoeff (FieldDerivSpace.repConj (T.fermion i).repJet) U⁻¹ 0 φ) :=
  (T.fermion i).isInfinitesimalActionOf.conj.repGauge_covDerivIter_zero
    transformsAsGaugeField_gaugeField repJet_apply_mul
    (repJet_conjFermionSymbol i) n l U φ

/-- The gauge law of the covariant tower of a bosonic species. -/
lemma repJet_covDerivBoson (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.BosonValue j)) :
    T.repJet U (T.covDerivBoson j l φ)
      = T.covDerivBoson j l (repDualCoeff (T.boson j).repJet U⁻¹ 0 φ) :=
  (T.boson j).isInfinitesimalActionOf.repGauge_covDerivIter_zero
    transformsAsGaugeField_gaugeField repJet_apply_mul
    (repJet_bosonSymbol j) n l U φ

/-- The gauge law of the conjugate covariant tower of a bosonic species. -/
lemma repJet_covDerivConjBoson (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    T.repJet U (T.covDerivConjBoson j l φ)
      = T.covDerivConjBoson j l
          (repDualCoeff (FieldDerivSpace.repConj (T.boson j).repJet) U⁻¹ 0 φ) :=
  (T.boson j).isInfinitesimalActionOf.conj.repGauge_covDerivIter_zero
    transformsAsGaugeField_gaugeField repJet_apply_mul
    (repJet_conjBosonSymbol j) n l U φ

/-- The gauge law of the included field-strength tower. A jet acts through the dual
  adjoint action of the value of its inverse, from the gauge-only law. -/
lemma repJet_covDerivFieldStrength (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    T.repJet U (T.covDerivFieldStrength l μ ν φ)
      = T.covDerivFieldStrength l μ ν ((G.adjointRep (G.evalGaugeJet
        U⁻¹)).dualMap φ) := by
  rw [covDerivFieldStrength_apply, repJet_apply, repJetAlgHom_includeConnection_one_tmul,
    LocalGaugeFieldAlgebra.repJet_covDerivFieldStrength_eval]
  rfl

/-- The jet action on the covariant tower of a species factors through evaluation, since pure
  jets act trivially. A jet acts as the constant jet of its value. -/
lemma repJet_covDerivFermion_ofConstant_eval (i : T.FermionSpecies)
    {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.FermionValue i)) :
    T.repJet U (T.covDerivFermion i l φ)
      = T.repJet (G.gaugeJetOfConstant (G.evalGaugeJet U))
          (T.covDerivFermion i l φ) :=
  by rw [repJet_covDerivFermion, repJet_covDerivFermion,
    GlobalGaugeGroup.repDualCoeff_inv_zero_eq_ofConstant_eval _ (T.fermion i).repJet_smul
      (T.fermion i).repCoeff_zero_of_eval_eq_one U]

lemma repJet_covDerivConjFermion_ofConstant_eval (i : T.FermionSpecies)
    {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    T.repJet U (T.covDerivConjFermion i l φ)
      = T.repJet (G.gaugeJetOfConstant (G.evalGaugeJet U)) (T.covDerivConjFermion i l
        φ) :=
  by rw [repJet_covDerivConjFermion, repJet_covDerivConjFermion,
    GlobalGaugeGroup.repDualCoeff_inv_zero_eq_ofConstant_eval _
      (FieldDerivSpace.repConj_smul_comm (T.fermion i).repJet_smul)
      (fun hW => GlobalGaugeGroup.repCoeff_repConj_zero_eq_id
        ((T.fermion i).repCoeff_zero_of_eval_eq_one hW)) U]

lemma repJet_covDerivBoson_ofConstant_eval (j : T.BosonSpecies)
    {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.BosonValue j)) :
    T.repJet U (T.covDerivBoson j l φ)
      = T.repJet (G.gaugeJetOfConstant (G.evalGaugeJet U)) (T.covDerivBoson j l φ) :=
  by rw [repJet_covDerivBoson, repJet_covDerivBoson,
    GlobalGaugeGroup.repDualCoeff_inv_zero_eq_ofConstant_eval _ (T.boson j).repJet_smul
      (T.boson j).repCoeff_zero_of_eval_eq_one U]

lemma repJet_covDerivConjBoson_ofConstant_eval (j : T.BosonSpecies)
    {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    T.repJet U (T.covDerivConjBoson j l φ)
      = T.repJet (G.gaugeJetOfConstant (G.evalGaugeJet U)) (T.covDerivConjBoson j l
        φ) :=
  by rw [repJet_covDerivConjBoson, repJet_covDerivConjBoson,
    GlobalGaugeGroup.repDualCoeff_inv_zero_eq_ofConstant_eval _
      (FieldDerivSpace.repConj_smul_comm (T.boson j).repJet_smul)
      (fun hW => GlobalGaugeGroup.repCoeff_repConj_zero_eq_id
        ((T.boson j).repCoeff_zero_of_eval_eq_one hW)) U]

/-- The jet action on the field-strength tower factors through evaluation, with no
  condition. -/
lemma repJet_covDerivFieldStrength_ofConstant_eval (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    T.repJet U (T.covDerivFieldStrength l μ ν φ)
      = T.repJet (G.gaugeJetOfConstant (G.evalGaugeJet U)) (T.covDerivFieldStrength l
        μ ν φ) := by
  rw [repJet_covDerivFieldStrength, repJet_covDerivFieldStrength, map_inv G.evalGaugeJet,
    map_inv G.evalGaugeJet, G.evalGaugeJet_gaugeJetOfConstant]

end GaugeLaws

/-!

## D. The Lorentz laws

-/

section LorentzLaws

-- The entry `Λ_{b a}` of the Lorentz matrix of `Λ : SL(2,ℂ)`, as a complex scalar.
set_option quotPrecheck false in
local notation:max "L[" Λ "]" b:max a:max => (((SL2C.toLorentzGroup Λ).1 b a : ℝ) : ℂ)

variable (Λ : SL(2,ℂ))

/-- The Lorentz law of the covariant tower of a fermionic species, under
  `GlobalGaugeGroup.MatterField.GaugeLorentzCompatible` for the species. Every covariant slot
  mixes by the columns of the Lorentz matrix and the value index transforms contragrediently. -/
lemma repLorentzGroup_covDerivFermion (i : T.FermionSpecies)
    (hi : (T.fermion i).GaugeLorentzCompatible) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.FermionValue i)) :
    T.repLorentzGroup Λ (T.covDerivFermion i l φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ k, L[Λ] (p k) (l k)) •
          T.covDerivFermion i p ((T.fermion i).repLorentz.dual Λ φ) :=
  GlobalGaugeGroup.isLorentzCovDerivTransforms_covDerivIter
    lorentzTransformsAsGaugeField_gaugeField repLorentzGroup_apply_mul hi
    (T.fermionSymbol i) (isLorentzDerivTransforms_fermionSymbol i) Λ n l φ

/-- The Lorentz law of the conjugate covariant tower of a fermionic species. -/
lemma repLorentzGroup_covDerivConjFermion (i : T.FermionSpecies)
    (hi : (T.fermion i).GaugeLorentzCompatible) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    T.repLorentzGroup Λ (T.covDerivConjFermion i l φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ k, L[Λ] (p k) (l k)) •
          T.covDerivConjFermion i p ((T.fermion i).repLorentz.conj.dual Λ φ) :=
  GlobalGaugeGroup.isLorentzCovDerivTransforms_covDerivIter_conj
    lorentzTransformsAsGaugeField_gaugeField repLorentzGroup_apply_mul hi
    (T.conjFermionSymbol i) (isLorentzDerivTransforms_conjFermionSymbol i) Λ n l φ

/-- The Lorentz law of the covariant tower of a bosonic species. -/
lemma repLorentzGroup_covDerivBoson (j : T.BosonSpecies)
    (hj : (T.boson j).GaugeLorentzCompatible) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.BosonValue j)) :
    T.repLorentzGroup Λ (T.covDerivBoson j l φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ k, L[Λ] (p k) (l k)) •
          T.covDerivBoson j p ((T.boson j).repLorentz.dual Λ φ) :=
  GlobalGaugeGroup.isLorentzCovDerivTransforms_covDerivIter
    lorentzTransformsAsGaugeField_gaugeField repLorentzGroup_apply_mul hj
    (T.bosonSymbol j) (isLorentzDerivTransforms_bosonSymbol j) Λ n l φ

/-- The Lorentz law of the conjugate covariant tower of a bosonic species. -/
lemma repLorentzGroup_covDerivConjBoson (j : T.BosonSpecies)
    (hj : (T.boson j).GaugeLorentzCompatible) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    T.repLorentzGroup Λ (T.covDerivConjBoson j l φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ k, L[Λ] (p k) (l k)) •
          T.covDerivConjBoson j p ((T.boson j).repLorentz.conj.dual Λ φ) :=
  GlobalGaugeGroup.isLorentzCovDerivTransforms_covDerivIter_conj
    lorentzTransformsAsGaugeField_gaugeField repLorentzGroup_apply_mul hj
    (T.conjBosonSymbol j) (isLorentzDerivTransforms_conjBosonSymbol j) Λ n l φ

/-- A real scalar acting on the inclusion of a real element of the gauge-only algebra is the
  same complex scalar acting on it. -/
private lemma includeConnection_one_tmul_real_smul (r : ℝ) (x : LocalGaugeFieldAlgebra G) :
    T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ] (r • x))
      = ((r : ℝ) : ℂ) • T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ] x) := by
  rw [TensorProduct.tmul_smul, ← algebraMap_smul ℂ r ((1 : ℂ) ⊗ₜ[ℝ] x), map_smul]
  rfl

/-- The Lorentz law of the field-strength tower, with no condition. Every covariant slot
  and both covector indices mix by the columns of the Lorentz matrix. -/
lemma repLorentzGroup_covDerivFieldStrength {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra) :
    T.repLorentzGroup Λ (T.covDerivFieldStrength (List.ofFn l) μ ν φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ k, L[Λ] (p k) (l k)) •
          ∑ a, L[Λ] a μ • ∑ b, L[Λ] b ν • T.covDerivFieldStrength (List.ofFn p) a b φ := by
  rw [covDerivFieldStrength_apply, repLorentzGroup_apply,
    repLorentzAlgHom_includeConnection_one_tmul,
    LocalGaugeFieldAlgebra.repLorentzGroup_covDerivFieldStrength, TensorProduct.tmul_sum,
    map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [includeConnection_one_tmul_real_smul, Complex.ofReal_prod, TensorProduct.tmul_sum, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [includeConnection_one_tmul_real_smul, TensorProduct.tmul_sum, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun b _ => ?_)
  rw [includeConnection_one_tmul_real_smul]
  rfl

/-!

### D.1. Transformed tower elements in a subalgebra containing the tower

The Lorentz laws mix a tower element only with elements of the same tower, so its Lorentz
transformation lies in any subalgebra containing the required tower elements. This says
nothing about the other elements of such a subalgebra; the covariant field algebra and its
sector subalgebras obtain their stability from it by generation.

-/

variable {S : Subalgebra ℂ T.LocalFieldAlgebra}

/-- Under `GlobalGaugeGroup.MatterField.GaugeLorentzCompatible` for the species, a Lorentz
  transformation
  carries an element of the covariant tower of a fermionic species into any subalgebra
  containing the tower of that length. -/
lemma repLorentzGroup_covDerivFermion_mem (i : T.FermionSpecies)
    (hi : (T.fermion i).GaugeLorentzCompatible) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.FermionValue i))
    (hS : ∀ (p : Fin n → (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℂ (T.FermionValue i)),
      T.covDerivFermion i p ψ ∈ S) :
    T.repLorentzGroup Λ (T.covDerivFermion i l φ) ∈ S := by
  rw [repLorentzGroup_covDerivFermion Λ i hi l φ]
  exact Subalgebra.sum_mem _ fun p _ => Subalgebra.smul_mem _ (hS p _) _

lemma repLorentzGroup_covDerivConjFermion_mem (i : T.FermionSpecies)
    (hi : (T.fermion i).GaugeLorentzCompatible) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.FermionValue i)))
    (hS : ∀ (p : Fin n → (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℂ (ConjModule (T.FermionValue i))),
      T.covDerivConjFermion i p ψ ∈ S) :
    T.repLorentzGroup Λ (T.covDerivConjFermion i l φ) ∈ S := by
  rw [repLorentzGroup_covDerivConjFermion Λ i hi l φ]
  exact Subalgebra.sum_mem _ fun p _ => Subalgebra.smul_mem _ (hS p _) _

lemma repLorentzGroup_covDerivBoson_mem (j : T.BosonSpecies)
    (hj : (T.boson j).GaugeLorentzCompatible) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.BosonValue j))
    (hS : ∀ (p : Fin n → (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℂ (T.BosonValue j)),
      T.covDerivBoson j p ψ ∈ S) :
    T.repLorentzGroup Λ (T.covDerivBoson j l φ) ∈ S := by
  rw [repLorentzGroup_covDerivBoson Λ j hj l φ]
  exact Subalgebra.sum_mem _ fun p _ => Subalgebra.smul_mem _ (hS p _) _

lemma repLorentzGroup_covDerivConjBoson_mem (j : T.BosonSpecies)
    (hj : (T.boson j).GaugeLorentzCompatible) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.BosonValue j)))
    (hS : ∀ (p : Fin n → (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℂ (ConjModule (T.BosonValue j))),
      T.covDerivConjBoson j p ψ ∈ S) :
    T.repLorentzGroup Λ (T.covDerivConjBoson j l φ) ∈ S := by
  rw [repLorentzGroup_covDerivConjBoson Λ j hj l φ]
  exact Subalgebra.sum_mem _ fun p _ => Subalgebra.smul_mem _ (hS p _) _

/-- A Lorentz transformation carries an element of the field-strength tower into any
  subalgebra containing the whole tower of its adjoint covector, with no condition. -/
lemma repLorentzGroup_covDerivFieldStrength_mem (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ G.lieSubalgebra)
    (hS : ∀ (l' : List (Fin 1 ⊕ Fin 3)) (a b : Fin 1 ⊕ Fin 3),
      T.covDerivFieldStrength l' a b φ ∈ S) :
    T.repLorentzGroup Λ (T.covDerivFieldStrength l μ ν φ) ∈ S := by
  obtain ⟨n, l', rfl⟩ : ∃ (n : ℕ) (l' : Fin n → (Fin 1 ⊕ Fin 3)), l = List.ofFn l' :=
    ⟨_, l.get, (List.ofFn_get l).symm⟩
  rw [repLorentzGroup_covDerivFieldStrength]
  exact Subalgebra.sum_mem _ fun p _ => Subalgebra.smul_mem _
    (Subalgebra.sum_mem _ fun a _ => Subalgebra.smul_mem _
      (Subalgebra.sum_mem _ fun b _ => Subalgebra.smul_mem _ (hS _ a b) _) _) _

end LorentzLaws

/-!

## E. Statistics and symmetries of the towers

The connection factor of `J(T)` is central and the bosonic generators commute with every
generator, so the field-strength tower and the bosonic towers are central. Every term of a
fermionic tower is a product of gauge-field symbols with a single fermionic generator, so
two fermionic towers anticommute, whatever their species.

### E.1. Centrality of the bosonic towers

-/

/-- The gauge-field symbols are central, since they lie in the connection factor. -/
lemma gaugeField_commute (p : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ G.lieSubalgebra) (x : T.LocalFieldAlgebra) :
    Commute (T.gaugeField p μ ψ) x := by
  rw [gaugeField_apply]
  exact includeConnection_commute _ x

/-- The field-strength tower is central, since it lies in the connection factor. -/
lemma commute_covDerivFieldStrength (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) (x : T.LocalFieldAlgebra) :
    Commute (T.covDerivFieldStrength l μ ν φ) x := by
  rw [covDerivFieldStrength_apply]
  exact includeConnection_commute _ x

/-- The covariant tower of a bosonic species is central, since it is a polynomial in the
  gauge-field symbols and the generators of the species, all of which are central. -/
lemma commute_covDerivBoson (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.BosonValue j)) (x : T.LocalFieldAlgebra) :
    Commute (T.covDerivBoson j l φ) x := by
  refine Commute.symm (Algebra.commute_of_mem_adjoin_of_forall_mem_commute
    (GlobalGaugeGroup.covDerivIter_mem_adjoin_symbols (A := T.gaugeField)
      (T.boson j).repAlgebra (T.bosonSymbol j) n l 0 φ) ?_)
  rintro z (⟨s, μ, ψ, rfl⟩ | ⟨s, χ, rfl⟩)
  · exact (gaugeField_commute s μ ψ x).symm
  · rw [bosonSymbol_apply]
    exact (commute_ιBoson j _ x).symm

/-- The conjugate covariant tower of a bosonic species is central. -/
lemma commute_covDerivConjBoson (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) (x : T.LocalFieldAlgebra) :
    Commute (T.covDerivConjBoson j l φ) x := by
  refine Commute.symm (Algebra.commute_of_mem_adjoin_of_forall_mem_commute
    (GlobalGaugeGroup.covDerivIter_mem_adjoin_symbols (A := T.gaugeField)
      (GlobalGaugeGroup.actionConj (T.boson j).repAlgebra) (T.conjBosonSymbol j) n l 0 φ) ?_)
  rintro z (⟨s, μ, ψ, rfl⟩ | ⟨s, χ, rfl⟩)
  · exact (gaugeField_commute s μ ψ x).symm
  · rw [conjBosonSymbol_apply]
    exact (commute_ιBoson j _ x).symm

/-!

### E.2. Anticommutation of the fermionic towers

-/

/-- An element commuting with the connection factor and anticommuting with every fermionic
  generator anticommutes with every element of a fermionic tower. -/
lemma covDerivFermion_mem_anticommuteSubmodule (i : T.FermionSpecies) {x : T.LocalFieldAlgebra}
    (hx : ∀ (j : T.FermionSpecies) (y : FieldDerivSpace (T.fermion j)),
      x * T.ιFermion j y = -(T.ιFermion j y * x))
    {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.FermionValue i)) :
    T.covDerivFermion i l φ ∈ GaugeBoson.anticommuteSubmodule x :=
  GlobalGaugeGroup.covDerivIter_mem_anticommuteSubmodule (A := T.gaugeField)
    (T.fermion i).repAlgebra (T.fermionSymbol i)
    (fun p μ ψ => (gaugeField_commute p μ ψ x).symm)
    (fun t χ => by
      rw [GaugeBoson.mem_anticommuteSubmodule_iff, fermionSymbol_apply]
      exact hx i _) n l 0 φ

/-- The conjugate form of `covDerivFermion_mem_anticommuteSubmodule`. -/
lemma covDerivConjFermion_mem_anticommuteSubmodule (i : T.FermionSpecies)
    {x : T.LocalFieldAlgebra}
    (hx : ∀ (j : T.FermionSpecies) (y : FieldDerivSpace (T.fermion j)),
      x * T.ιFermion j y = -(T.ιFermion j y * x))
    {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    T.covDerivConjFermion i l φ ∈ GaugeBoson.anticommuteSubmodule x :=
  GlobalGaugeGroup.covDerivIter_mem_anticommuteSubmodule (A := T.gaugeField)
    (GlobalGaugeGroup.actionConj (T.fermion i).repAlgebra) (T.conjFermionSymbol i)
    (fun p μ ψ => (gaugeField_commute p μ ψ x).symm)
    (fun t χ => by
      rw [GaugeBoson.mem_anticommuteSubmodule_iff, conjFermionSymbol_apply]
      exact hx i _) n l 0 φ

/-- A fermionic generator anticommutes with every element of a fermionic tower. -/
lemma ιFermion_anticomm_covDerivFermion (j : T.FermionSpecies) (y : FieldDerivSpace (T.fermion j))
    (i : T.FermionSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.FermionValue i)) :
    T.ιFermion j y * T.covDerivFermion i l φ = -(T.covDerivFermion i l φ * T.ιFermion j y) :=
  covDerivFermion_mem_anticommuteSubmodule i (fun j' y' => ιFermion_mul_swap j j' y y') l φ

/-- A fermionic generator anticommutes with every element of a conjugate fermionic tower. -/
lemma ιFermion_anticomm_covDerivConjFermion (j : T.FermionSpecies)
    (y : FieldDerivSpace (T.fermion j)) (i : T.FermionSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    T.ιFermion j y * T.covDerivConjFermion i l φ
      = -(T.covDerivConjFermion i l φ * T.ιFermion j y) :=
  covDerivConjFermion_mem_anticommuteSubmodule i (fun j' y' => ιFermion_mul_swap j j' y y') l φ

/-- Two fermionic towers anticommute, of the same species or of different ones. -/
lemma covDerivFermion_anticomm_covDerivFermion (i j : T.FermionSpecies) {n m : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.FermionValue i))
    (l' : Fin m → (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (T.FermionValue j)) :
    T.covDerivFermion i l φ * T.covDerivFermion j l' φ'
      = -(T.covDerivFermion j l' φ' * T.covDerivFermion i l φ) :=
  covDerivFermion_mem_anticommuteSubmodule j (fun k y =>
    GaugeBoson.anticomm_symm (B := T.LocalFieldAlgebra)
      (ιFermion_anticomm_covDerivFermion k y i l φ)) l' φ'

/-- A fermionic tower anticommutes with a conjugate fermionic tower. -/
lemma covDerivFermion_anticomm_covDerivConjFermion (i j : T.FermionSpecies) {n m : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.FermionValue i))
    (l' : Fin m → (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule (T.FermionValue j))) :
    T.covDerivFermion i l φ * T.covDerivConjFermion j l' φ'
      = -(T.covDerivConjFermion j l' φ' * T.covDerivFermion i l φ) :=
  covDerivConjFermion_mem_anticommuteSubmodule j (fun k y =>
    GaugeBoson.anticomm_symm (B := T.LocalFieldAlgebra)
      (ιFermion_anticomm_covDerivFermion k y i l φ)) l' φ'

/-- A conjugate fermionic tower anticommutes with a fermionic tower. -/
lemma covDerivConjFermion_anticomm_covDerivFermion (i j : T.FermionSpecies) {n m : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.FermionValue i)))
    (l' : Fin m → (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (T.FermionValue j)) :
    T.covDerivConjFermion i l φ * T.covDerivFermion j l' φ'
      = -(T.covDerivFermion j l' φ' * T.covDerivConjFermion i l φ) :=
  covDerivFermion_mem_anticommuteSubmodule j (fun k y =>
    GaugeBoson.anticomm_symm (B := T.LocalFieldAlgebra)
      (ιFermion_anticomm_covDerivConjFermion k y i l φ)) l' φ'

/-- Two conjugate fermionic towers anticommute. -/
lemma covDerivConjFermion_anticomm_covDerivConjFermion (i j : T.FermionSpecies) {n m : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.FermionValue i)))
    (l' : Fin m → (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule (T.FermionValue j))) :
    T.covDerivConjFermion i l φ * T.covDerivConjFermion j l' φ'
      = -(T.covDerivConjFermion j l' φ' * T.covDerivConjFermion i l φ) :=
  covDerivConjFermion_mem_anticommuteSubmodule j (fun k y =>
    GaugeBoson.anticomm_symm (B := T.LocalFieldAlgebra)
      (ιFermion_anticomm_covDerivConjFermion k y i l φ)) l' φ'

/-!

### E.3. The symmetries of the field-strength tower

-/

/-- The field-strength tower is antisymmetric in its two covector indices. The field strength
  is, the gauge-field symbols commuting, and the iterated covariant derivative is linear in
  the family it differentiates. -/
lemma covDerivFieldStrength_swap (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    T.covDerivFieldStrength l ν μ φ = - T.covDerivFieldStrength l μ ν φ := by
  have hswap : fieldStrength (LocalGaugeFieldAlgebra.derivA G) ν μ
      = fun t => - fieldStrength (LocalGaugeFieldAlgebra.derivA G) μ ν t :=
    funext fun t => GaugeBoson.fieldStrength_swap _
      (fun _ _ _ _ _ _ => Commute.all _ _) μ ν t
  have h : LocalGaugeFieldAlgebra.covDerivFieldStrength G l ν μ
      = - LocalGaugeFieldAlgebra.covDerivFieldStrength G l μ ν := by
    rw [LocalGaugeFieldAlgebra.covDerivFieldStrength, LocalGaugeFieldAlgebra.covDerivFieldStrength,
      hswap, GaugeBoson.iteratedCovDerivAdjoint_neg_fam]
  simp only [covDerivFieldStrength, LinearMap.comp_apply, h, LinearMap.neg_apply, map_neg]

/-- Along a functional vanishing on every bracket, such as a hypercharge coordinate, the
  field-strength tower depends only on the multiset of its derivative slots, since there the
  covariant derivatives are the ordinary ones, which commute. -/
lemma covDerivFieldStrength_eq_of_perm_of_map_lie {φ : Module.Dual ℝ G.lieSubalgebra}
    (hφ : ∀ x y : G.lieSubalgebra, φ ⁅x, y⁆ = 0) {l l' : List (Fin 1 ⊕ Fin 3)}
    (hl : l.Perm l') (μ ν : Fin 1 ⊕ Fin 3) :
    T.covDerivFieldStrength l μ ν φ = T.covDerivFieldStrength l' μ ν φ := by
  rw [covDerivFieldStrength_eq_iteratedCovDerivAdjoint,
    covDerivFieldStrength_eq_iteratedCovDerivAdjoint]
  exact GaugeBoson.iteratedCovDerivAdjoint_apply_perm_of_map_lie hφ _ _ hl 0

/-!

## F. Mass weights of the towers

The statements take an algebra map `P : J(T) →ₐ[ℂ] Polynomial J(T)` under which every
gauge-field symbol `∂_p A_μ` is an eigenvector of weight `2 * (1 + |p|)`, and under which the
symbols of a species have weight `c + 2 * |s|`. The covariant towers are then eigenvectors of
weight `c + 2 * n`, and the field-strength tower of weight `4 + 2 * |l|`. The mass-weight
polynomial `GaugeFieldData.massWeightPoly`, defined in `LocalFieldAlgebra/MassWeight.lean`, is
such a map (`GaugeFieldData.massWeightPoly_gaugeField`).

-/

section MassWeight

variable (P : T.LocalFieldAlgebra →ₐ[ℂ] Polynomial T.LocalFieldAlgebra)
  (hA : ∀ (p : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (ψ : Module.Dual ℝ G.lieSubalgebra),
    P (T.gaugeField p μ ψ)
      = Polynomial.monomial (2 * (1 + Multiset.card p)) (T.gaugeField p μ ψ))

include hA in
/-- The gauge-field hypothesis in the form of the eigenspace submodules. -/
lemma gaugeField_mem_massWeightEigenspace (p : Multiset (Fin 1 ⊕ Fin 3))
    (μ : Fin 1 ⊕ Fin 3) (ψ : Module.Dual ℝ G.lieSubalgebra) :
    T.gaugeField p μ ψ ∈
      GaugeBoson.massWeightEigenspace P (2 * (1 + Multiset.card p)) :=
  GaugeBoson.mem_massWeightEigenspace_iff.mpr (hA p μ ψ)

include hA in
/-- The mass weight of the field-strength tower is `4 + 2 * |l|`. -/
lemma massWeight_covDerivFieldStrength (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    P (T.covDerivFieldStrength l μ ν φ)
      = Polynomial.monomial (4 + 2 * l.length) (T.covDerivFieldStrength l μ ν φ) := by
  have hmem := GaugeBoson.iteratedCovDerivAdjoint_mem_massWeightEigenspace
    T.gaugeField P (gaugeField_mem_massWeightEigenspace P hA) 4 _
    (GaugeBoson.fieldStrength_mem_massWeightEigenspace T.gaugeField P
      (gaugeField_mem_massWeightEigenspace P hA) μ ν) l 0 φ
  rw [Multiset.card_zero, mul_zero, add_zero,
    GaugeBoson.mem_massWeightEigenspace_iff] at hmem
  rw [covDerivFieldStrength_eq_iteratedCovDerivAdjoint]
  exact hmem

include hA in
/-- The mass weight of the covariant tower of a fermionic species whose symbols have weight
  `c + 2 * |s|` is `c + 2 * n`. -/
lemma massWeight_covDerivFermion (i : T.FermionSpecies) (c : ℕ)
    (hF : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.FermionValue i)),
      P (T.fermionSymbol i s φ)
        = Polynomial.monomial (c + 2 * Multiset.card s) (T.fermionSymbol i s φ))
    {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.FermionValue i)) :
    P (T.covDerivFermion i l φ) = Polynomial.monomial (c + 2 * n) (T.covDerivFermion i l φ) := by
  have hmem := GlobalGaugeGroup.covDerivIter_mem_massWeightEigenspace
    (A := T.gaugeField) (T.fermion i).repAlgebra (T.fermionSymbol i) P c
    (gaugeField_mem_massWeightEigenspace P hA)
    (fun s χ => GaugeBoson.mem_massWeightEigenspace_iff.mpr (hF s χ)) l 0 φ
  rw [Multiset.card_zero, mul_zero, add_zero,
    GaugeBoson.mem_massWeightEigenspace_iff] at hmem
  exact hmem

include hA in
/-- The mass weight of the conjugate covariant tower of a fermionic species. -/
lemma massWeight_covDerivConjFermion (i : T.FermionSpecies) (c : ℕ)
    (hF : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))),
      P (T.conjFermionSymbol i s φ)
        = Polynomial.monomial (c + 2 * Multiset.card s) (T.conjFermionSymbol i s φ))
    {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    P (T.covDerivConjFermion i l φ)
      = Polynomial.monomial (c + 2 * n) (T.covDerivConjFermion i l φ) := by
  have hmem := GlobalGaugeGroup.covDerivIter_mem_massWeightEigenspace
    (A := T.gaugeField) (GlobalGaugeGroup.actionConj (T.fermion i).repAlgebra)
    (T.conjFermionSymbol i) P c (gaugeField_mem_massWeightEigenspace P hA)
    (fun s χ => GaugeBoson.mem_massWeightEigenspace_iff.mpr (hF s χ)) l 0 φ
  rw [Multiset.card_zero, mul_zero, add_zero,
    GaugeBoson.mem_massWeightEigenspace_iff] at hmem
  exact hmem

include hA in
/-- The mass weight of the covariant tower of a bosonic species whose symbols have weight
  `c + 2 * |s|` is `c + 2 * n`. -/
lemma massWeight_covDerivBoson (j : T.BosonSpecies) (c : ℕ)
    (hF : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.BosonValue j)),
      P (T.bosonSymbol j s φ)
        = Polynomial.monomial (c + 2 * Multiset.card s) (T.bosonSymbol j s φ))
    {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.BosonValue j)) :
    P (T.covDerivBoson j l φ) = Polynomial.monomial (c + 2 * n) (T.covDerivBoson j l φ) := by
  have hmem := GlobalGaugeGroup.covDerivIter_mem_massWeightEigenspace
    (A := T.gaugeField) (T.boson j).repAlgebra (T.bosonSymbol j) P c
    (gaugeField_mem_massWeightEigenspace P hA)
    (fun s χ => GaugeBoson.mem_massWeightEigenspace_iff.mpr (hF s χ)) l 0 φ
  rw [Multiset.card_zero, mul_zero, add_zero,
    GaugeBoson.mem_massWeightEigenspace_iff] at hmem
  exact hmem

include hA in
/-- The mass weight of the conjugate covariant tower of a bosonic species. -/
lemma massWeight_covDerivConjBoson (j : T.BosonSpecies) (c : ℕ)
    (hF : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))),
      P (T.conjBosonSymbol j s φ)
        = Polynomial.monomial (c + 2 * Multiset.card s) (T.conjBosonSymbol j s φ))
    {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    P (T.covDerivConjBoson j l φ)
      = Polynomial.monomial (c + 2 * n) (T.covDerivConjBoson j l φ) := by
  have hmem := GlobalGaugeGroup.covDerivIter_mem_massWeightEigenspace
    (A := T.gaugeField) (GlobalGaugeGroup.actionConj (T.boson j).repAlgebra)
    (T.conjBosonSymbol j) P c (gaugeField_mem_massWeightEigenspace P hA)
    (fun s χ => GaugeBoson.mem_massWeightEigenspace_iff.mpr (hF s χ)) l 0 φ
  rw [Multiset.card_zero, mul_zero, add_zero,
    GaugeBoson.mem_massWeightEigenspace_iff] at hmem
  exact hmem

end MassWeight

end GaugeFieldData
