/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.JetAlgebra.MassWeightPoly
public import Physlib.Particles.StandardModel.JetAlgebra.FieldAlgebra
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.TransformsIn
public import Physlib.Particles.StandardModel.Matter.FermionicAlgebra.TransformsIn
/-!
# The transformation laws of the field symbols of the jet algebra

## i. Overview

The thirteen families of derivative symbols of the jet algebra of the Standard Model
carry two group actions: the jet gauge action `JetAlgebra.repJetGaugeGroupI` and the
Lorentz action `JetAlgebra.repLorentzGroup`. This file establishes how each family
transforms under each of them.

The work is mechanical but for one point, which is the content of section A. The three
sector inclusions `includeFermion`, `includeHiggs`, `includeGauge` are equivariant for the
jet gauge action and for the Lorentz action, because both actions are tensor products of
the sector actions and each sector action fixes the unit. `includeGauge` was treated when
the gauge sector was shown to be a gauge field; the other two are proved here, and with
them every transformation law of a matter symbol is its sector's own law, pushed through an
algebra map.

These are the facts from which the transformation laws of an arbitrary Standard Model
are obtained, by pushing them along the defining algebra map out of the jet algebra.

## ii. Key results

- `JetAlgebra.repJetGaugeGroupI_includeHiggs`, `JetAlgebra.repLorentzGroup_includeFermion`
  and their companions : the sector inclusions are equivariant.
- `JetAlgebra.transformsIn_higgsField` and its companions : the jet gauge transformation
  of the thirteen families.
- `JetAlgebra.isLorentzDerivTransforms_higgsField` and its companions : the Lorentz
  transformation of the thirteen families.

## iii. Table of contents

- A. The sector inclusions are equivariant
  - A.1. The sector inclusions on pure tensors
  - A.2. The unit of the gauge sector
  - A.3. Equivariance for the jet gauge action
  - A.4. Equivariance for the Lorentz action
- B. The jet gauge transformation of the field symbols
  - B.1. The Higgs families
  - B.2. The fermion families
- C. The Lorentz transformation of the field symbols
  - C.1. The Higgs families
  - C.2. The fermion families

-/

@[expose] public section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

namespace JetAlgebra

open TensorProduct Matrix MatrixGroups Lorentz

/-!

## A. The sector inclusions are equivariant

Both the jet gauge action and the Lorentz action on the jet algebra are tensor products of
the three sector actions. A sector inclusion puts the unit in the other two factors, so
equivariance is exactly the statement that the other two actions fix their units, which
they do — they are actions by algebra maps.

-/

/-!

### A.1. The sector inclusions on pure tensors

-/

/-- The fermionic inclusion puts the unit in the Higgs and gauge factors. -/
lemma includeFermion_apply (f : FermionJetAlgebra) :
    includeFermion f = ((f ⊗ₜ[ℂ] (1 : HiggsJetAlgebra)) ⊗ₜ[ℂ]
      (1 : ℂ ⊗[ℝ] GaugeJetAlgebra)) := rfl

/-- The Higgs inclusion puts the unit in the fermionic and gauge factors. -/
lemma includeHiggs_apply (h : HiggsJetAlgebra) :
    includeHiggs h = (((1 : FermionJetAlgebra) ⊗ₜ[ℂ] h) ⊗ₜ[ℂ]
      (1 : ℂ ⊗[ℝ] GaugeJetAlgebra)) := rfl

/-!

### A.2. The unit of the gauge sector

-/

/-- The jet gauge action on the complexified gauge sector fixes the unit. -/
lemma complexRepJetGaugeGroupI_apply_one (U : JetGaugeGroupI) :
    GaugeJetAlgebra.complexRepJetGaugeGroupI U (1 : ℂ ⊗[ℝ] GaugeJetAlgebra) = 1 := by
  rw [Algebra.TensorProduct.one_def, GaugeJetAlgebra.complexRepJetGaugeGroupI_tmul,
    GaugeJetAlgebra.repJetGaugeGroupI_apply_one]

/-- The Lorentz action on the complexified gauge sector fixes the unit. -/
lemma complexRepLorentzGroup_apply_one (Λ : SL(2,ℂ)) :
    GaugeJetAlgebra.complexRepLorentzGroup Λ (1 : ℂ ⊗[ℝ] GaugeJetAlgebra) = 1 := by
  rw [Algebra.TensorProduct.one_def, GaugeJetAlgebra.complexRepLorentzGroup_tmul,
    GaugeJetAlgebra.repLorentzGroup_apply_one]

/-!

### A.3. Equivariance for the jet gauge action

-/

/-- The jet gauge action restricts to the fermionic sector's own action. -/
lemma repJetGaugeGroupI_includeFermion (U : JetGaugeGroupI) (f : FermionJetAlgebra) :
    repJetGaugeGroupI U (includeFermion f)
      = includeFermion (FermionJetAlgebra.repJetGaugeGroupI U f) := by
  rw [includeFermion_apply, repJetGaugeGroupI_tmul,
    show (FermionJetAlgebra.repJetGaugeGroupI.tprod HiggsJetAlgebra.repJetGaugeGroupI) U
        (f ⊗ₜ[ℂ] (1 : HiggsJetAlgebra))
      = (FermionJetAlgebra.repJetGaugeGroupI U f) ⊗ₜ[ℂ]
        (HiggsJetAlgebra.repJetGaugeGroupI U (1 : HiggsJetAlgebra)) from rfl,
    show HiggsJetAlgebra.repJetGaugeGroupI U (1 : HiggsJetAlgebra) = 1 from
      BosonicAlgebra.repJetGaugeGroupI_apply_one _ _ U,
    complexRepJetGaugeGroupI_apply_one, includeFermion_apply]

/-- The jet gauge action restricts to the Higgs sector's own action. -/
lemma repJetGaugeGroupI_includeHiggs (U : JetGaugeGroupI) (h : HiggsJetAlgebra) :
    repJetGaugeGroupI U (includeHiggs h)
      = includeHiggs (HiggsJetAlgebra.repJetGaugeGroupI U h) := by
  rw [includeHiggs_apply, repJetGaugeGroupI_tmul,
    show (FermionJetAlgebra.repJetGaugeGroupI.tprod HiggsJetAlgebra.repJetGaugeGroupI) U
        ((1 : FermionJetAlgebra) ⊗ₜ[ℂ] h)
      = (FermionJetAlgebra.repJetGaugeGroupI U (1 : FermionJetAlgebra)) ⊗ₜ[ℂ]
        (HiggsJetAlgebra.repJetGaugeGroupI U h) from rfl,
    show FermionJetAlgebra.repJetGaugeGroupI U (1 : FermionJetAlgebra) = 1 from
      FermionicAlgebra.repJetGaugeGroupI_apply_one _ _ U,
    complexRepJetGaugeGroupI_apply_one, includeHiggs_apply]

/-!

### A.4. Equivariance for the Lorentz action

-/

/-- The Lorentz action restricts to the fermionic sector's own action. -/
lemma repLorentzGroup_includeFermion (Λ : SL(2,ℂ)) (f : FermionJetAlgebra) :
    repLorentzGroup Λ (includeFermion f)
      = includeFermion (FermionJetAlgebra.repLorentzGroup Λ f) := by
  rw [includeFermion_apply, repLorentzGroup_tmul,
    show (FermionJetAlgebra.repLorentzGroup.tprod HiggsJetAlgebra.repLorentzGroup) Λ
        (f ⊗ₜ[ℂ] (1 : HiggsJetAlgebra))
      = (FermionJetAlgebra.repLorentzGroup Λ f) ⊗ₜ[ℂ]
        (HiggsJetAlgebra.repLorentzGroup Λ (1 : HiggsJetAlgebra)) from rfl,
    show HiggsJetAlgebra.repLorentzGroup Λ (1 : HiggsJetAlgebra) = 1 from
      BosonicAlgebra.repLorentzGroup_apply_one _ Λ,
    complexRepLorentzGroup_apply_one, includeFermion_apply]

/-- The Lorentz action restricts to the Higgs sector's own action. -/
lemma repLorentzGroup_includeHiggs (Λ : SL(2,ℂ)) (h : HiggsJetAlgebra) :
    repLorentzGroup Λ (includeHiggs h)
      = includeHiggs (HiggsJetAlgebra.repLorentzGroup Λ h) := by
  rw [includeHiggs_apply, repLorentzGroup_tmul,
    show (FermionJetAlgebra.repLorentzGroup.tprod HiggsJetAlgebra.repLorentzGroup) Λ
        ((1 : FermionJetAlgebra) ⊗ₜ[ℂ] h)
      = (FermionJetAlgebra.repLorentzGroup Λ (1 : FermionJetAlgebra)) ⊗ₜ[ℂ]
        (HiggsJetAlgebra.repLorentzGroup Λ h) from rfl,
    show FermionJetAlgebra.repLorentzGroup Λ (1 : FermionJetAlgebra) = 1 from
      FermionicAlgebra.repLorentzGroup_apply_one _ Λ,
    complexRepLorentzGroup_apply_one, includeHiggs_apply]

/-!

## B. The jet gauge transformation of the field symbols

`TransformsIn` asks that a jet of gauge transformations mix a derivative symbol with the
lower symbols by the all-orders Leibniz convolution of the base-point Taylor coefficients
of the gauge jet. Each sector proves that law for its own symbols; the inclusions of
section A carry it to the full algebra, and the species bridge of
`Physlib.Particles.StandardModel.Fermions.JetAlgebra.Species` moves the fermionic law from
the total target space `FermionSpace` down to the individual species.

-/

/-!

### B.1. The Higgs families

-/

/-- The Higgs symbols transform in the jet gauge representation carried by the jets of the
  Higgs field. -/
theorem transformsIn_higgsField :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI HiggsVec.repJetGaugeGroupI
      higgsField := by
  intro U φ s
  rw [higgsField_eq_includeHiggs, repJetGaugeGroupI_includeHiggs,
    show HiggsJetAlgebra.repJetGaugeGroupI U
        (BosonicAlgebra.iteratedJetDeriv s (BosonicAlgebra.ofField φ))
      = _ from BosonicAlgebra.repJetGaugeGroupI_iteratedJetDeriv_ofField
        HiggsVec.repJetGaugeGroupI HiggsVec.repJetGaugeGroupI_smul U φ s,
    map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  rw [Function.comp_apply, ← higgsField_eq_includeHiggs]

/-- The conjugate Higgs symbols transform in the conjugate of the jet gauge representation
  carried by the jets of the Higgs field. -/
theorem transformsIn_conjHiggsField :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI (repConj HiggsVec.repJetGaugeGroupI)
      conjHiggsField := by
  intro U φ s
  rw [conjHiggsField_eq_includeHiggs, repJetGaugeGroupI_includeHiggs,
    show HiggsJetAlgebra.repJetGaugeGroupI U
        (BosonicAlgebra.iteratedJetDeriv s (BosonicAlgebra.ofConjField φ))
      = _ from BosonicAlgebra.repJetGaugeGroupI_iteratedJetDeriv_ofConjField
        HiggsVec.repJetGaugeGroupI HiggsVec.repJetGaugeGroupI_smul U φ s,
    map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  rw [Function.comp_apply, ← conjHiggsField_eq_includeHiggs]

/-!

### B.2. The fermion families

-/

/-- The jet gauge transformation law of a fermion species: a family of symbols obtained
  from the total fermionic symbols by pulling covectors back along a projection
  intertwining the two jet gauge actions transforms in the species' own representation. -/
private lemma transformsIn_species {W : Type} [AddCommGroup W] [Module ℂ W]
    (repW : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] W)) (p : FermionSpace →ₗ[ℂ] W)
    (hp : ∀ U : JetGaugeGroupI, (LinearMap.lTensor JetRing p).comp
        (FermionSpace.repJetGaugeGroupI U)
      = (repW U).comp (LinearMap.lTensor JetRing p))
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ W →ₗ[ℂ] JetAlgebra}
    (hF : ∀ s φ, F s φ = fermionSymbol s (Module.Dual.transpose p φ)) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI repW F := by
  intro U φ s
  rw [hF, fermionSymbol_eq_includeFermion, repJetGaugeGroupI_includeFermion,
    show FermionJetAlgebra.repJetGaugeGroupI U
        (FermionicAlgebra.iteratedJetDeriv s
          (FermionicAlgebra.ofField (Module.Dual.transpose p φ)))
      = _ from FermionicAlgebra.repJetGaugeGroupI_iteratedJetDeriv_ofField
        FermionSpace.repJetGaugeGroupI FermionSpace.repJetGaugeGroupI_smul U _ s,
    map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun q _ => ?_)
  rw [Function.comp_apply, ← fermionSymbol_eq_includeFermion, hF]
  exact congrArg (fermionSymbol q.2)
    (LinearMap.congr_fun (repDualCoeff_comp p hp U⁻¹ q.1) φ)

/-- The base-point Taylor coefficients of two conjugate jet gauge actions are intertwined,
  on the component-function index, by the conjugate of any map of value spaces intertwining
  the unconjugated coefficients: conjugation changes neither the underlying maps nor the
  real directions in which the coefficients are taken. -/
private lemma repDualCoeff_repConj_transpose {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {repV : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V)}
    {repW : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] W)} (p : V →ₗ[ℂ] W)
    (hp : ∀ (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)),
      p.comp (IsGaugeField.repCoeff repV U s) = (IsGaugeField.repCoeff repW U s).comp p)
    (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule W)) :
    IsGaugeField.repDualCoeff (repConj repV) U s
        (Module.Dual.transpose (ConjModule.map p) φ)
      = Module.Dual.transpose (ConjModule.map p)
          (IsGaugeField.repDualCoeff (repConj repW) U s φ) := by
  refine LinearMap.ext fun v => ?_
  show φ (ConjModule.map p (IsGaugeField.repCoeff (repConj repV) U s v))
    = φ (IsGaugeField.repCoeff (repConj repW) U s (ConjModule.map p v))
  rw [GaugeAlgebra.repCoeff_repConj, GaugeAlgebra.repCoeff_repConj]
  exact congrArg φ (LinearMap.congr_fun (hp U s) v)

/-- The jet gauge transformation law of the conjugate symbols of a fermion species: the law
  of the species itself, read on the conjugate representations. -/
private lemma transformsIn_conjSpecies {W : Type} [AddCommGroup W] [Module ℂ W]
    (repW : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] W)) (p : FermionSpace →ₗ[ℂ] W)
    (hp : ∀ U : JetGaugeGroupI, (LinearMap.lTensor JetRing p).comp
        (FermionSpace.repJetGaugeGroupI U)
      = (repW U).comp (LinearMap.lTensor JetRing p))
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule W) →ₗ[ℂ] JetAlgebra}
    (hF : ∀ s φ, F s φ = conjFermionSymbol s
      (Module.Dual.transpose (ConjModule.map p) φ)) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI (repConj repW) F := by
  intro U φ s
  rw [hF, conjFermionSymbol_eq_includeFermion, repJetGaugeGroupI_includeFermion,
    show FermionJetAlgebra.repJetGaugeGroupI U
        (FermionicAlgebra.iteratedJetDeriv s
          (FermionicAlgebra.ofConjField (Module.Dual.transpose (ConjModule.map p) φ)))
      = _ from FermionicAlgebra.repJetGaugeGroupI_iteratedJetDeriv_ofConjField
        FermionSpace.repJetGaugeGroupI FermionSpace.repJetGaugeGroupI_smul U _ s,
    map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun q _ => ?_)
  rw [Function.comp_apply, ← conjFermionSymbol_eq_includeFermion, hF]
  exact congrArg (conjFermionSymbol q.2)
    (repDualCoeff_repConj_transpose p (fun U' s' => repCoeff_comp p hp U' s') U⁻¹ q.1 φ)


/-- The symbols of the `i`-th generation down-type quark singlet transform in the jet gauge
  representation carried by the jets of that species. -/
theorem transformsIn_downSingletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI DownSinglet.repJetGaugeGroupI
      (downSingletField i) :=
  transformsIn_species _ _ (FermionSpace.lTensor_downSingletProj_repJetGaugeGroupI i)
    (downSingletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation down-type quark singlet transform in the
  conjugate of the jet gauge representation carried by the jets of that species. -/
theorem transformsIn_conjDownSingletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI
      (repConj DownSinglet.repJetGaugeGroupI) (conjDownSingletField i) :=
  transformsIn_conjSpecies _ _ (FermionSpace.lTensor_downSingletProj_repJetGaugeGroupI i)
    (conjDownSingletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation up-type quark singlet transform in the jet gauge
  representation carried by the jets of that species. -/
theorem transformsIn_upSingletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI UpSinglet.repJetGaugeGroupI
      (upSingletField i) :=
  transformsIn_species _ _ (FermionSpace.lTensor_upSingletProj_repJetGaugeGroupI i)
    (upSingletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation up-type quark singlet transform in the
  conjugate of the jet gauge representation carried by the jets of that species. -/
theorem transformsIn_conjUpSingletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI
      (repConj UpSinglet.repJetGaugeGroupI) (conjUpSingletField i) :=
  transformsIn_conjSpecies _ _ (FermionSpace.lTensor_upSingletProj_repJetGaugeGroupI i)
    (conjUpSingletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation quark doublet transform in the jet gauge
  representation carried by the jets of that species. -/
theorem transformsIn_quarkDoubletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI QuarkDoublet.repJetGaugeGroupI
      (quarkDoubletField i) :=
  transformsIn_species _ _ (FermionSpace.lTensor_quarkDoubletProj_repJetGaugeGroupI i)
    (quarkDoubletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation quark doublet transform in the
  conjugate of the jet gauge representation carried by the jets of that species. -/
theorem transformsIn_conjQuarkDoubletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI
      (repConj QuarkDoublet.repJetGaugeGroupI) (conjQuarkDoubletField i) :=
  transformsIn_conjSpecies _ _ (FermionSpace.lTensor_quarkDoubletProj_repJetGaugeGroupI i)
    (conjQuarkDoubletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation lepton doublet transform in the jet gauge
  representation carried by the jets of that species. -/
theorem transformsIn_leptonDoubletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI LeptonDoublet.repJetGaugeGroupI
      (leptonDoubletField i) :=
  transformsIn_species _ _ (FermionSpace.lTensor_leptonDoubletProj_repJetGaugeGroupI i)
    (leptonDoubletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation lepton doublet transform in the
  conjugate of the jet gauge representation carried by the jets of that species. -/
theorem transformsIn_conjLeptonDoubletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI
      (repConj LeptonDoublet.repJetGaugeGroupI) (conjLeptonDoubletField i) :=
  transformsIn_conjSpecies _ _ (FermionSpace.lTensor_leptonDoubletProj_repJetGaugeGroupI i)
    (conjLeptonDoubletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation charged-lepton singlet transform in the jet gauge
  representation carried by the jets of that species. -/
theorem transformsIn_leptonSingletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI LeptonSinglet.repJetGaugeGroupI
      (leptonSingletField i) :=
  transformsIn_species _ _ (FermionSpace.lTensor_leptonSingletProj_repJetGaugeGroupI i)
    (leptonSingletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation charged-lepton singlet transform in the
  conjugate of the jet gauge representation carried by the jets of that species. -/
theorem transformsIn_conjLeptonSingletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI
      (repConj LeptonSinglet.repJetGaugeGroupI) (conjLeptonSingletField i) :=
  transformsIn_conjSpecies _ _ (FermionSpace.lTensor_leptonSingletProj_repJetGaugeGroupI i)
    (conjLeptonSingletField_eq_conjFermionSymbol i)
/-!

## C. The Lorentz transformation of the field symbols

`IsLorentzDerivTransforms` asks that each derivative slot of a symbol mix into all tuples
of directions by the columns of the Lorentz matrix, while the value index transforms by the
contragredient of the species' Lorentz representation. The mixing of the slots is
`IsLorentzDeriv.rep_iteratedD_ofFn`, available because the total derivative on the jet
algebra is a Lorentz vector; what is left is the undifferentiated law at `n = 0`, which is
the equivariance of the component functions of each sector.

-/

/-!

### C.1. The Higgs families

The Higgs is a Lorentz scalar, so its value index carries the trivial representation and
the conjugate index its conjugate.

-/

/-- The Higgs symbols transform as the derivative symbols of a Lorentz scalar. -/
theorem isLorentzDerivTransforms_higgsField :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      (Representation.trivial ℂ SL(2,ℂ) HiggsVec) higgsField := by
  intro Λ n l φ
  refine (Lorentz.IsLorentzDeriv.rep_iteratedD_ofFn jetDeriv_comm Λ l
    (includeHiggs (BosonicAlgebra.ofField φ))).trans ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [repLorentzGroup_includeHiggs,
    show HiggsJetAlgebra.repLorentzGroup Λ (BosonicAlgebra.ofField φ)
      = BosonicAlgebra.ofField ((Representation.trivial ℂ SL(2,ℂ) HiggsVec).dual Λ φ) from
      BosonicAlgebra.repLorentzGroup_ofField _ Λ φ]
  rfl

/-- The conjugate Higgs symbols transform as the derivative symbols of the conjugate of a
  Lorentz scalar. -/
theorem isLorentzDerivTransforms_conjHiggsField :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      (Representation.trivial ℂ SL(2,ℂ) HiggsVec).conj conjHiggsField := by
  intro Λ n l φ
  refine (Lorentz.IsLorentzDeriv.rep_iteratedD_ofFn jetDeriv_comm Λ l
    (includeHiggs (BosonicAlgebra.ofConjField φ))).trans ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [repLorentzGroup_includeHiggs,
    show HiggsJetAlgebra.repLorentzGroup Λ (BosonicAlgebra.ofConjField φ)
      = BosonicAlgebra.ofConjField
        ((Representation.trivial ℂ SL(2,ℂ) HiggsVec).conj.dual Λ φ) from
      BosonicAlgebra.repLorentzGroup_ofConjField _ Λ φ]
  rfl

/-!

### C.2. The fermion families

The Lorentz action on `FermionSpace` is species-diagonal, so the contragredient action on a
covector pulled back from a species is the pullback of the species' own contragredient
action; that identity is definitional, and it is the only input the species need beyond the
law for the total fermionic symbols.

-/

/-- The Lorentz transformation law of a fermion species: a family of symbols obtained from
  the total fermionic symbols by pulling covectors back along a projection whose
  contragredient is species-diagonal transforms in the species' own Weyl representation. -/
private lemma isLorentzDerivTransforms_species {W : Type} [AddCommGroup W] [Module ℂ W]
    (repW : Representation ℂ SL(2,ℂ) W) (p : FermionSpace →ₗ[ℂ] W)
    (hdual : ∀ (Λ : SL(2,ℂ)) (φ : Module.Dual ℂ W),
      FermionSpace.repLorentzGroup.dual Λ (Module.Dual.transpose p φ)
        = Module.Dual.transpose p (repW.dual Λ φ))
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ W →ₗ[ℂ] JetAlgebra}
    (hF : ∀ s φ, F s φ = fermionSymbol s (Module.Dual.transpose p φ)) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup repW F := by
  intro Λ n l φ
  rw [hF]
  refine (Lorentz.IsLorentzDeriv.rep_iteratedD_ofFn jetDeriv_comm Λ l
    (includeFermion (FermionicAlgebra.ofField (Module.Dual.transpose p φ)))).trans ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [repLorentzGroup_includeFermion,
    show FermionJetAlgebra.repLorentzGroup Λ
        (FermionicAlgebra.ofField (Module.Dual.transpose p φ))
      = FermionicAlgebra.ofField
        (FermionSpace.repLorentzGroup.dual Λ (Module.Dual.transpose p φ)) from
      FermionicAlgebra.repLorentzGroup_ofField _ Λ _,
    hdual, hF]
  rfl

/-- The Lorentz transformation law of the conjugate symbols of a fermion species: the law
  of the species itself, read on the conjugate representations. -/
private lemma isLorentzDerivTransforms_conjSpecies {W : Type} [AddCommGroup W]
    [Module ℂ W] (repW : Representation ℂ SL(2,ℂ) W) (p : FermionSpace →ₗ[ℂ] W)
    (hdual : ∀ (Λ : SL(2,ℂ)) (φ : Module.Dual ℂ (ConjModule W)),
      FermionSpace.repLorentzGroup.conj.dual Λ
          (Module.Dual.transpose (ConjModule.map p) φ)
        = Module.Dual.transpose (ConjModule.map p) (repW.conj.dual Λ φ))
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule W) →ₗ[ℂ] JetAlgebra}
    (hF : ∀ s φ, F s φ = conjFermionSymbol s
      (Module.Dual.transpose (ConjModule.map p) φ)) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup repW.conj F := by
  intro Λ n l φ
  rw [hF]
  refine (Lorentz.IsLorentzDeriv.rep_iteratedD_ofFn jetDeriv_comm Λ l
    (includeFermion (FermionicAlgebra.ofConjField
      (Module.Dual.transpose (ConjModule.map p) φ)))).trans ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [repLorentzGroup_includeFermion,
    show FermionJetAlgebra.repLorentzGroup Λ
        (FermionicAlgebra.ofConjField (Module.Dual.transpose (ConjModule.map p) φ))
      = FermionicAlgebra.ofConjField (FermionSpace.repLorentzGroup.conj.dual Λ
          (Module.Dual.transpose (ConjModule.map p) φ)) from
      FermionicAlgebra.repLorentzGroup_ofConjField _ Λ _,
    hdual, hF]
  rfl


/-- The symbols of the `i`-th generation down-type quark singlet transform as the derivative
  symbols of a Weyl spinor in that species' Lorentz representation. -/
theorem isLorentzDerivTransforms_downSingletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      DownSinglet.repLorentzGroup (downSingletField i) :=
  isLorentzDerivTransforms_species _ _ (fun _ _ => rfl)
    (downSingletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation down-type quark singlet transform as the
  derivative symbols of the conjugate Weyl spinor. -/
theorem isLorentzDerivTransforms_conjDownSingletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      DownSinglet.repLorentzGroup.conj (conjDownSingletField i) :=
  isLorentzDerivTransforms_conjSpecies _ _ (fun _ _ => rfl)
    (conjDownSingletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation up-type quark singlet transform as the derivative
  symbols of a Weyl spinor in that species' Lorentz representation. -/
theorem isLorentzDerivTransforms_upSingletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      UpSinglet.repLorentzGroup (upSingletField i) :=
  isLorentzDerivTransforms_species _ _ (fun _ _ => rfl)
    (upSingletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation up-type quark singlet transform as the
  derivative symbols of the conjugate Weyl spinor. -/
theorem isLorentzDerivTransforms_conjUpSingletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      UpSinglet.repLorentzGroup.conj (conjUpSingletField i) :=
  isLorentzDerivTransforms_conjSpecies _ _ (fun _ _ => rfl)
    (conjUpSingletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation quark doublet transform as the derivative
  symbols of a Weyl spinor in that species' Lorentz representation. -/
theorem isLorentzDerivTransforms_quarkDoubletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      QuarkDoublet.repLorentzGroup (quarkDoubletField i) :=
  isLorentzDerivTransforms_species _ _ (fun _ _ => rfl)
    (quarkDoubletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation quark doublet transform as the
  derivative symbols of the conjugate Weyl spinor. -/
theorem isLorentzDerivTransforms_conjQuarkDoubletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      QuarkDoublet.repLorentzGroup.conj (conjQuarkDoubletField i) :=
  isLorentzDerivTransforms_conjSpecies _ _ (fun _ _ => rfl)
    (conjQuarkDoubletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation lepton doublet transform as the derivative
  symbols of a Weyl spinor in that species' Lorentz representation. -/
theorem isLorentzDerivTransforms_leptonDoubletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      LeptonDoublet.repLorentzGroup (leptonDoubletField i) :=
  isLorentzDerivTransforms_species _ _ (fun _ _ => rfl)
    (leptonDoubletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation lepton doublet transform as the
  derivative symbols of the conjugate Weyl spinor. -/
theorem isLorentzDerivTransforms_conjLeptonDoubletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      LeptonDoublet.repLorentzGroup.conj (conjLeptonDoubletField i) :=
  isLorentzDerivTransforms_conjSpecies _ _ (fun _ _ => rfl)
    (conjLeptonDoubletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation charged-lepton singlet transform as the derivative
  symbols of a Weyl spinor in that species' Lorentz representation. -/
theorem isLorentzDerivTransforms_leptonSingletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      LeptonSinglet.repLorentzGroup (leptonSingletField i) :=
  isLorentzDerivTransforms_species _ _ (fun _ _ => rfl)
    (leptonSingletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation charged-lepton singlet transform as the
  derivative symbols of the conjugate Weyl spinor. -/
theorem isLorentzDerivTransforms_conjLeptonSingletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      LeptonSinglet.repLorentzGroup.conj (conjLeptonSingletField i) :=
  isLorentzDerivTransforms_conjSpecies _ _ (fun _ _ => rfl)
    (conjLeptonSingletField_eq_conjFermionSymbol i)

end JetAlgebra

end StandardModel
