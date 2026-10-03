/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.TransformsIn
public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.LorentzCovariantDeriv
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.FieldStrength
/-!
# The covariant derivatives in the local field algebra

## i. Overview

The covariant expressions of a gauge theory are the iterated covariant derivatives of its
matter fields and of the field strength, built here inside the local field algebra `J(T)`
of a field datum. For a matter species the tower is `GaugeAlgebraRealization.covDerivIter`
on the symbol family of the species: `∇_{l 0} ⋯ ∇_{l (n-1)} ψ` along an ordered tuple `l`
of directions, with `∇_ρ F = [∂_ρ F] + A_ρ · F` through the infinitesimal action
`repAlgebra` of the species on the value index, the conjugate components through the
conjugate action. Zero derivatives is the undifferentiated symbol, and the ordered labels
are kept: nothing is identified with the multiset-indexed ordinary derivatives. For the
gauge bosons the tower is the gauge-only `LocalGaugeFieldAlgebra.covDerivFieldStrength`,
included through the connection factor.

A jet acts on every tower through the base-point Taylor coefficient of its inverse on the
value index alone, unconditionally; under `MatterField.PureJetsActTrivially` the action on
a matter tower factors through evaluation to the ordinary gauge group. A Lorentz
transformation mixes the covariant slots by the columns of the Lorentz matrix and the value
index contragrediently, under `MatterField.GaugeLorentzCompatible` for the matter towers
and unconditionally for the field strength.

## ii. Key results

- `GaugeFieldData.covDerivFermion`, `GaugeFieldData.covDerivConjFermion`,
  `GaugeFieldData.covDerivBoson`, `GaugeFieldData.covDerivConjBoson`,
  `GaugeFieldData.covDerivFieldStrength` : the covariant towers.
- `GaugeFieldData.repJet_covDerivFermion` and companions : the gauge laws;
  `GaugeFieldData.repJet_covDerivFermion_ofConstant_eval` and companions : the
  factorization through evaluation.
- `GaugeFieldData.repLorentzGroup_covDerivFermion` and companions : the Lorentz laws;
  `GaugeFieldData.repLorentzGroup_covDerivFermion_mem` and companions : a Lorentz
  transformation of a tower element lies in any subalgebra containing the tower.

## iii. Table of contents

- A. The covariant matter towers
- B. The included field-strength tower
- C. The gauge laws
- D. The Lorentz laws
  - D.1. Transformed tower elements in a subalgebra containing the tower

-/

@[expose] public section

open TensorProduct Matrix MatrixGroups Lorentz
open GaugeAlgebraRealization (covDerivIter covDerivAction actionFamConv fieldStrength
  iteratedCovDerivAdjoint repDualCoeff)

namespace GaugeFieldData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} (T : GaugeFieldData jets)

/-!

## A. The covariant matter towers

-/

/-- The iterated covariant derivative `∇_{l 0} ⋯ ∇_{l (n-1)} ψ` of a fermionic species along
  an ordered tuple of directions, as a family over the covectors of its value space. -/
noncomputable def covDerivFermion (i : T.FermionSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (T.FermionValue i) →ₗ[ℂ] T.LocalFieldAlgebra :=
  covDerivIter T.gaugeRealization.A (T.fermion i).repAlgebra (T.fermionSymbol i) n l 0

/-- The iterated covariant derivative of the conjugate components of a fermionic species,
  through the conjugate infinitesimal action. -/
noncomputable def covDerivConjFermion (i : T.FermionSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule (T.FermionValue i)) →ₗ[ℂ] T.LocalFieldAlgebra :=
  covDerivIter T.gaugeRealization.A (LocalGaugeData.actionConj (T.fermion i).repAlgebra)
    (T.conjFermionSymbol i) n l 0

/-- The iterated covariant derivative of a bosonic species. -/
noncomputable def covDerivBoson (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (T.BosonValue j) →ₗ[ℂ] T.LocalFieldAlgebra :=
  covDerivIter T.gaugeRealization.A (T.boson j).repAlgebra (T.bosonSymbol j) n l 0

/-- The iterated covariant derivative of the conjugate components of a bosonic species. -/
noncomputable def covDerivConjBoson (j : T.BosonSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule (T.BosonValue j)) →ₗ[ℂ] T.LocalFieldAlgebra :=
  covDerivIter T.gaugeRealization.A (LocalGaugeData.actionConj (T.boson j).repAlgebra)
    (T.conjBosonSymbol j) n l 0

variable {T}

/-- Zero covariant derivatives: the undifferentiated symbol. -/
lemma covDerivFermion_zero (i : T.FermionSpecies) (l : Fin 0 → (Fin 1 ⊕ Fin 3)) :
    T.covDerivFermion i l = T.fermionSymbol i 0 := rfl

lemma covDerivConjFermion_zero (i : T.FermionSpecies) (l : Fin 0 → (Fin 1 ⊕ Fin 3)) :
    T.covDerivConjFermion i l = T.conjFermionSymbol i 0 := rfl

lemma covDerivBoson_zero (j : T.BosonSpecies) (l : Fin 0 → (Fin 1 ⊕ Fin 3)) :
    T.covDerivBoson j l = T.bosonSymbol j 0 := rfl

lemma covDerivConjBoson_zero (j : T.BosonSpecies) (l : Fin 0 → (Fin 1 ⊕ Fin 3)) :
    T.covDerivConjBoson j l = T.conjBosonSymbol j 0 := rfl

/-- One more covariant derivative, peeled off the front of the tuple: the derivative symbol
  `[∂_{l 0} ∇_{l'} ψ]` of the lower tower plus the derived action `A_{l 0} · ∇_{l'} ψ` of the
  gauge field on its value index, both read off the lower tower as a family. -/
lemma covDerivFermion_succ (i : T.FermionSpecies) {n : ℕ} (l : Fin (n + 1) → (Fin 1 ⊕ Fin 3)) :
    T.covDerivFermion i l
      = covDerivIter T.gaugeRealization.A (T.fermion i).repAlgebra (T.fermionSymbol i) n
          (fun k => l k.succ) {l 0}
        + actionFamConv T.gaugeRealization.A (T.fermion i).repAlgebra (l 0)
          (covDerivIter T.gaugeRealization.A (T.fermion i).repAlgebra (T.fermionSymbol i) n
            fun k => l k.succ) 0 := rfl

lemma covDerivConjFermion_succ (i : T.FermionSpecies) {n : ℕ}
    (l : Fin (n + 1) → (Fin 1 ⊕ Fin 3)) :
    T.covDerivConjFermion i l
      = covDerivIter T.gaugeRealization.A (LocalGaugeData.actionConj (T.fermion i).repAlgebra)
          (T.conjFermionSymbol i) n (fun k => l k.succ) {l 0}
        + actionFamConv T.gaugeRealization.A (LocalGaugeData.actionConj (T.fermion i).repAlgebra)
          (l 0) (covDerivIter T.gaugeRealization.A
            (LocalGaugeData.actionConj (T.fermion i).repAlgebra) (T.conjFermionSymbol i) n
            fun k => l k.succ) 0 := rfl

lemma covDerivBoson_succ (j : T.BosonSpecies) {n : ℕ} (l : Fin (n + 1) → (Fin 1 ⊕ Fin 3)) :
    T.covDerivBoson j l
      = covDerivIter T.gaugeRealization.A (T.boson j).repAlgebra (T.bosonSymbol j) n
          (fun k => l k.succ) {l 0}
        + actionFamConv T.gaugeRealization.A (T.boson j).repAlgebra (l 0)
          (covDerivIter T.gaugeRealization.A (T.boson j).repAlgebra (T.bosonSymbol j) n
            fun k => l k.succ) 0 := rfl

lemma covDerivConjBoson_succ (j : T.BosonSpecies) {n : ℕ}
    (l : Fin (n + 1) → (Fin 1 ⊕ Fin 3)) :
    T.covDerivConjBoson j l
      = covDerivIter T.gaugeRealization.A (LocalGaugeData.actionConj (T.boson j).repAlgebra)
          (T.conjBosonSymbol j) n (fun k => l k.succ) {l 0}
        + actionFamConv T.gaugeRealization.A (LocalGaugeData.actionConj (T.boson j).repAlgebra)
          (l 0) (covDerivIter T.gaugeRealization.A
            (LocalGaugeData.actionConj (T.boson j).repAlgebra) (T.conjBosonSymbol j) n
            fun k => l k.succ) 0 := rfl

variable (T)

/-!

## B. The included field-strength tower

-/

/-- The field strength and its ordered covariant derivatives `∇_l F_μν^φ`, included from
  the real gauge-only algebra through the connection factor. -/
noncomputable def covDerivFieldStrength (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ 𝔤 →ₗ[ℝ] T.LocalFieldAlgebra :=
  (T.includeConnection.restrictScalars ℝ).toLinearMap ∘ₗ
    (Algebra.TensorProduct.includeRight (R := ℝ) (A := ℂ)
      (B := LocalGaugeFieldAlgebra 𝔤)).toLinearMap ∘ₗ
    LocalGaugeFieldAlgebra.covDerivFieldStrength 𝔤 l μ ν

variable {T}

lemma covDerivFieldStrength_apply (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    T.covDerivFieldStrength l μ ν φ
      = T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ]
          LocalGaugeFieldAlgebra.covDerivFieldStrength 𝔤 l μ ν φ) := rfl

/-- Zero covariant derivatives: the included field strength. -/
lemma covDerivFieldStrength_nil (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    T.covDerivFieldStrength [] μ ν φ
      = T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ] LocalGaugeFieldAlgebra.fieldStrength 𝔤 μ ν φ) := rfl

/-- The included tower is the covariant tower of the gauge-field symbols of `J(T)` computed
  by the realization theory, the tower being natural along the inclusion of the connection
  factor. -/
lemma covDerivFieldStrength_eq_iteratedCovDerivAdjoint (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    T.covDerivFieldStrength l μ ν φ
      = iteratedCovDerivAdjoint T.gaugeRealization.A l
          (fieldStrength T.gaugeRealization.A μ ν) 0 φ := by
  let ι : (ℂ ⊗[ℝ] LocalGaugeFieldAlgebra 𝔤) →ₗ[ℝ] T.LocalFieldAlgebra :=
    T.includeConnection.toLinearMap.restrictScalars ℝ
  have hmul : ∀ x y, ι (x * y) = ι x * ι y := fun x y => map_mul T.includeConnection x y
  have hF : ∀ p, ι ∘ₗ fieldStrength (LocalGaugeFieldAlgebra.gaugeField 𝔤) μ ν p
      = fieldStrength (B := T.LocalFieldAlgebra)
          (fun p ρ => ι ∘ₗ LocalGaugeFieldAlgebra.gaugeField 𝔤 p ρ) μ ν p :=
    fun p => (GaugeAlgebraRealization.fieldStrength_map
      (B := ℂ ⊗[ℝ] LocalGaugeFieldAlgebra 𝔤) (B' := T.LocalFieldAlgebra) ι hmul
      (LocalGaugeFieldAlgebra.gaugeField 𝔤) μ ν p).symm
  have key : iteratedCovDerivAdjoint (B := T.LocalFieldAlgebra)
      (fun p ρ => ι ∘ₗ LocalGaugeFieldAlgebra.gaugeField 𝔤 p ρ) l
      (fieldStrength (B := T.LocalFieldAlgebra)
        (fun p ρ => ι ∘ₗ LocalGaugeFieldAlgebra.gaugeField 𝔤 p ρ) μ ν) 0 φ
      = ι (iteratedCovDerivAdjoint (LocalGaugeFieldAlgebra.gaugeField 𝔤) l
          (fieldStrength (LocalGaugeFieldAlgebra.gaugeField 𝔤) μ ν) 0 φ) := by
    rw [← funext hF]
    exact LinearMap.congr_fun (congrFun (GaugeAlgebraRealization.iteratedCovDerivAdjoint_map
      (B := ℂ ⊗[ℝ] LocalGaugeFieldAlgebra 𝔤) (B' := T.LocalFieldAlgebra) ι hmul
      (LocalGaugeFieldAlgebra.gaugeField 𝔤) l
      (fieldStrength (LocalGaugeFieldAlgebra.gaugeField 𝔤) μ ν)) 0) φ
  rw [covDerivFieldStrength_apply, LocalGaugeFieldAlgebra.covDerivFieldStrength,
    LocalGaugeFieldAlgebra.one_tmul_iteratedCovDerivAdjoint_fieldStrength]
  exact key.symm

/-!

## C. The gauge laws

-/

section GaugeLaws

variable (U : GJ)

/-- The gauge law of the covariant tower of a fermionic species: a jet acts through the
  zeroth dual Taylor coefficient of its inverse on the value index alone. -/
theorem repJet_covDerivFermion (i : T.FermionSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.FermionValue i)) :
    T.repJet U (T.covDerivFermion i l φ)
      = T.covDerivFermion i l (repDualCoeff (T.fermion i).repJet U⁻¹ 0 φ) :=
  (LocalGaugeData.TransformsIn.covDerivIter T.gaugeRealization (transformsIn_fermionSymbol i)
    (T.fermion i).repAlgebra_isInfinitesimalAction n l).repGauge_zero U φ

/-- The gauge law of the conjugate covariant tower of a fermionic species, through the
  conjugate representation. -/
theorem repJet_covDerivConjFermion (i : T.FermionSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    T.repJet U (T.covDerivConjFermion i l φ)
      = T.covDerivConjFermion i l
          (repDualCoeff (JetComponentSpace.repConj (T.fermion i).repJet) U⁻¹ 0 φ) :=
  (LocalGaugeData.TransformsIn.covDerivIter T.gaugeRealization
    (transformsIn_conjFermionSymbol i)
    (T.fermion i).repAlgebra_isInfinitesimalAction.conj n l).repGauge_zero U φ

/-- The gauge law of the covariant tower of a bosonic species. -/
theorem repJet_covDerivBoson (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.BosonValue j)) :
    T.repJet U (T.covDerivBoson j l φ)
      = T.covDerivBoson j l (repDualCoeff (T.boson j).repJet U⁻¹ 0 φ) :=
  (LocalGaugeData.TransformsIn.covDerivIter T.gaugeRealization (transformsIn_bosonSymbol j)
    (T.boson j).repAlgebra_isInfinitesimalAction n l).repGauge_zero U φ

/-- The gauge law of the conjugate covariant tower of a bosonic species. -/
theorem repJet_covDerivConjBoson (j : T.BosonSpecies) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    T.repJet U (T.covDerivConjBoson j l φ)
      = T.covDerivConjBoson j l
          (repDualCoeff (JetComponentSpace.repConj (T.boson j).repJet) U⁻¹ 0 φ) :=
  (LocalGaugeData.TransformsIn.covDerivIter T.gaugeRealization (transformsIn_conjBosonSymbol j)
    (T.boson j).repAlgebra_isInfinitesimalAction.conj n l).repGauge_zero U φ

/-- The gauge law of the included field-strength tower: a jet acts through the dual
  adjoint action of the value of its inverse, from the gauge-only law. -/
theorem repJet_covDerivFieldStrength (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    T.repJet U (T.covDerivFieldStrength l μ ν φ)
      = T.covDerivFieldStrength l μ ν ((jets.adjointValue (jets.eval U⁻¹)).dualMap φ) := by
  rw [covDerivFieldStrength_apply, repJet_apply, repJetAlgHom_includeConnection_one_tmul,
    LocalGaugeFieldAlgebra.repJet_covDerivFieldStrength_eval]
  rfl

/-- Under `MatterField.PureJetsActTrivially` for the species, the jet action on its
  covariant tower factors through evaluation: a jet acts as the constant jet of its
  value. -/
lemma repJet_covDerivFermion_ofConstant_eval (i : T.FermionSpecies)
    (hi : (T.fermion i).PureJetsActTrivially) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.FermionValue i)) :
    T.repJet U (T.covDerivFermion i l φ)
      = T.repJet (jets.ofConstant (jets.eval U)) (T.covDerivFermion i l φ) :=
  (LocalGaugeData.TransformsIn.covDerivIter T.gaugeRealization (transformsIn_fermionSymbol i)
    (T.fermion i).repAlgebra_isInfinitesimalAction n l).repGauge_zero_eq_ofConstant_eval
    (T.fermion i).repJet_smul hi U φ

lemma repJet_covDerivConjFermion_ofConstant_eval (i : T.FermionSpecies)
    (hi : (T.fermion i).PureJetsActTrivially) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    T.repJet U (T.covDerivConjFermion i l φ)
      = T.repJet (jets.ofConstant (jets.eval U)) (T.covDerivConjFermion i l φ) :=
  (LocalGaugeData.TransformsIn.covDerivIter T.gaugeRealization
    (transformsIn_conjFermionSymbol i)
    (T.fermion i).repAlgebra_isInfinitesimalAction.conj n l).repGauge_zero_eq_ofConstant_eval
    (JetComponentSpace.repConj_smul_comm (T.fermion i).repJet_smul)
    (fun hW => LocalGaugeData.repCoeff_repConj_zero_eq_id (hi hW)) U φ

lemma repJet_covDerivBoson_ofConstant_eval (j : T.BosonSpecies)
    (hj : (T.boson j).PureJetsActTrivially) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.BosonValue j)) :
    T.repJet U (T.covDerivBoson j l φ)
      = T.repJet (jets.ofConstant (jets.eval U)) (T.covDerivBoson j l φ) :=
  (LocalGaugeData.TransformsIn.covDerivIter T.gaugeRealization (transformsIn_bosonSymbol j)
    (T.boson j).repAlgebra_isInfinitesimalAction n l).repGauge_zero_eq_ofConstant_eval
    (T.boson j).repJet_smul hj U φ

lemma repJet_covDerivConjBoson_ofConstant_eval (j : T.BosonSpecies)
    (hj : (T.boson j).PureJetsActTrivially) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    T.repJet U (T.covDerivConjBoson j l φ)
      = T.repJet (jets.ofConstant (jets.eval U)) (T.covDerivConjBoson j l φ) :=
  (LocalGaugeData.TransformsIn.covDerivIter T.gaugeRealization (transformsIn_conjBosonSymbol j)
    (T.boson j).repAlgebra_isInfinitesimalAction.conj n l).repGauge_zero_eq_ofConstant_eval
    (JetComponentSpace.repConj_smul_comm (T.boson j).repJet_smul)
    (fun hW => LocalGaugeData.repCoeff_repConj_zero_eq_id (hj hW)) U φ

/-- The jet action on the field-strength tower factors through evaluation, with no
  condition. -/
lemma repJet_covDerivFieldStrength_ofConstant_eval (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    T.repJet U (T.covDerivFieldStrength l μ ν φ)
      = T.repJet (jets.ofConstant (jets.eval U)) (T.covDerivFieldStrength l μ ν φ) := by
  rw [repJet_covDerivFieldStrength, repJet_covDerivFieldStrength, map_inv jets.eval,
    map_inv jets.eval, jets.eval_ofConstant]

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
  `MatterField.GaugeLorentzCompatible` for the species: every covariant slot mixes by the
  columns of the Lorentz matrix and the value index transforms contragrediently. -/
theorem repLorentzGroup_covDerivFermion (i : T.FermionSpecies)
    (hi : (T.fermion i).GaugeLorentzCompatible) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.FermionValue i)) :
    T.repLorentzGroup Λ (T.covDerivFermion i l φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ k, L[Λ] (p k) (l k)) •
          T.covDerivFermion i p ((T.fermion i).repLorentz.dual Λ φ) :=
  GaugeAlgebraRealization.isLorentzCovDerivTransforms_covDerivIter T.gaugeRealization hi
    (T.fermionSymbol i) (isLorentzDerivTransforms_fermionSymbol i) Λ n l φ

/-- The Lorentz law of the conjugate covariant tower of a fermionic species. -/
theorem repLorentzGroup_covDerivConjFermion (i : T.FermionSpecies)
    (hi : (T.fermion i).GaugeLorentzCompatible) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    T.repLorentzGroup Λ (T.covDerivConjFermion i l φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ k, L[Λ] (p k) (l k)) •
          T.covDerivConjFermion i p ((T.fermion i).repLorentz.conj.dual Λ φ) :=
  GaugeAlgebraRealization.isLorentzCovDerivTransforms_covDerivIter_conj T.gaugeRealization hi
    (T.conjFermionSymbol i) (isLorentzDerivTransforms_conjFermionSymbol i) Λ n l φ

/-- The Lorentz law of the covariant tower of a bosonic species. -/
theorem repLorentzGroup_covDerivBoson (j : T.BosonSpecies)
    (hj : (T.boson j).GaugeLorentzCompatible) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.BosonValue j)) :
    T.repLorentzGroup Λ (T.covDerivBoson j l φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ k, L[Λ] (p k) (l k)) •
          T.covDerivBoson j p ((T.boson j).repLorentz.dual Λ φ) :=
  GaugeAlgebraRealization.isLorentzCovDerivTransforms_covDerivIter T.gaugeRealization hj
    (T.bosonSymbol j) (isLorentzDerivTransforms_bosonSymbol j) Λ n l φ

/-- The Lorentz law of the conjugate covariant tower of a bosonic species. -/
theorem repLorentzGroup_covDerivConjBoson (j : T.BosonSpecies)
    (hj : (T.boson j).GaugeLorentzCompatible) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    T.repLorentzGroup Λ (T.covDerivConjBoson j l φ)
      = ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ k, L[Λ] (p k) (l k)) •
          T.covDerivConjBoson j p ((T.boson j).repLorentz.conj.dual Λ φ) :=
  GaugeAlgebraRealization.isLorentzCovDerivTransforms_covDerivIter_conj T.gaugeRealization hj
    (T.conjBosonSymbol j) (isLorentzDerivTransforms_conjBosonSymbol j) Λ n l φ

/-- A real scalar acting on the inclusion of a real element of the gauge-only algebra is the
  same complex scalar acting on it. -/
private lemma includeConnection_one_tmul_real_smul (r : ℝ) (x : LocalGaugeFieldAlgebra 𝔤) :
    T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ] (r • x))
      = ((r : ℝ) : ℂ) • T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ] x) := by
  rw [TensorProduct.tmul_smul, ← algebraMap_smul ℂ r ((1 : ℂ) ⊗ₜ[ℝ] x), map_smul]
  rfl

/-- The Lorentz law of the field-strength tower, with no condition: every covariant slot
  and both covector indices mix by the columns of the Lorentz matrix. -/
theorem repLorentzGroup_covDerivFieldStrength {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
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

/-- Under `MatterField.GaugeLorentzCompatible` for the species, a Lorentz transformation
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
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤)
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

end GaugeFieldData
