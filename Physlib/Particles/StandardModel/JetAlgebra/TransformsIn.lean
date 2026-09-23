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

The work is mechanical. The six sector restriction lemmas it rests on — the three sector
inclusions being equivariant for each of the two actions — are proved where the two actions
are defined, in `Physlib.Particles.StandardModel.JetAlgebra.GaugeAction` and
`Physlib.Particles.StandardModel.JetAlgebra.LorentzAction`; with them every transformation
law of a matter symbol is its sector's own law, pushed through an algebra map.

These are the facts from which the transformation laws of an arbitrary Standard Model
are obtained, by pushing them along the defining algebra map out of the jet algebra.

## ii. Key results

- `JetAlgebra.transformsIn_higgsField` and its companions : the jet gauge transformation
  of the thirteen families.
- `JetAlgebra.isLorentzDerivTransforms_higgsField` and its companions : the Lorentz
  transformation of the thirteen families.

## iii. Table of contents

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
    LocalGaugeData.TransformsIn (B := JetAlgebra) repJetGaugeGroupI HiggsVec.repJetGaugeGroupI
      higgsField := by
  intro U φ s
  refine (congrArg (repJetGaugeGroupI U) (higgsField_eq_includeHiggs s φ)).trans ?_
  refine (repJetGaugeGroupI_includeHiggs U _).trans ?_
  refine (congrArg includeHiggs
    (BosonicAlgebra.repJetGaugeGroupI_iteratedJetDeriv_ofField
      (M := HiggsVec.matterField) U φ s)).trans ?_
  refine (map_multiset_sum includeHiggs _).trans ?_
  refine (congrArg Multiset.sum (Multiset.map_map _ _ _)).trans ?_
  exact congrArg Multiset.sum
    (Multiset.map_congr rfl fun q _ => (higgsField_eq_includeHiggs q.2 _).symm)

/-- The conjugate Higgs symbols transform in the conjugate of the jet gauge representation
  carried by the jets of the Higgs field. -/
theorem transformsIn_conjHiggsField :
    LocalGaugeData.TransformsIn (B := JetAlgebra) repJetGaugeGroupI
      (JetComponentSpace.repConj HiggsVec.repJetGaugeGroupI)
      conjHiggsField := by
  intro U φ s
  refine (congrArg (repJetGaugeGroupI U) (conjHiggsField_eq_includeHiggs s φ)).trans ?_
  refine (repJetGaugeGroupI_includeHiggs U _).trans ?_
  refine (congrArg includeHiggs
    (BosonicAlgebra.repJetGaugeGroupI_iteratedJetDeriv_ofConjField
      (M := HiggsVec.matterField) U φ s)).trans ?_
  refine (map_multiset_sum includeHiggs _).trans ?_
  refine (congrArg Multiset.sum (Multiset.map_map _ _ _)).trans ?_
  exact congrArg Multiset.sum
    (Multiset.map_congr rfl fun q _ => (conjHiggsField_eq_includeHiggs q.2 _).symm)

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
    LocalGaugeData.TransformsIn (B := JetAlgebra) repJetGaugeGroupI repW F := by
  intro U φ s
  refine (congrArg (repJetGaugeGroupI U)
    ((hF s φ).trans (fermionSymbol_eq_includeFermion s _))).trans ?_
  refine (repJetGaugeGroupI_includeFermion U _).trans ?_
  refine (congrArg includeFermion
    (FermionicAlgebra.repJetGaugeGroupI_iteratedJetDeriv_ofField
      (M := fermionMatterField) U _ s)).trans ?_
  refine (map_multiset_sum includeFermion _).trans ?_
  refine (congrArg Multiset.sum (Multiset.map_map _ _ _)).trans ?_
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun q _ => ?_)
  exact (congrArg (fun χ : Module.Dual ℂ FermionSpace =>
        includeFermion (FermionicAlgebra.iteratedJetDeriv q.2
          (FermionicAlgebra.ofField χ)))
      (LinearMap.congr_fun (repDualCoeff_comp p hp U⁻¹ q.1) φ)).trans
    ((fermionSymbol_eq_includeFermion q.2 _).symm.trans
      (hF q.2 (GaugeAlgebraRealization.repDualCoeff repW U⁻¹ q.1 φ)).symm)

/-- The base-point Taylor coefficients of two conjugate jet gauge actions are intertwined,
  on the component-function index, by the conjugate of any map of value spaces intertwining
  the unconjugated coefficients: conjugation changes neither the underlying maps nor the
  real directions in which the coefficients are taken. -/
private lemma repDualCoeff_repConj_transpose {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {repV : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V)}
    {repW : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] W)} (p : V →ₗ[ℂ] W)
    (hp : ∀ (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)),
      p.comp (GaugeAlgebraRealization.repCoeff repV U s)
        = (GaugeAlgebraRealization.repCoeff repW U s).comp p)
    (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule W)) :
    GaugeAlgebraRealization.repDualCoeff (JetComponentSpace.repConj repV) U s
        (Module.Dual.transpose (ConjModule.map p) φ)
      = Module.Dual.transpose (ConjModule.map p)
          (GaugeAlgebraRealization.repDualCoeff (JetComponentSpace.repConj repW) U s φ) := by
  refine LinearMap.ext fun v => ?_
  show φ (ConjModule.map p
      (GaugeAlgebraRealization.repCoeff (JetComponentSpace.repConj repV) U s v))
    = φ (GaugeAlgebraRealization.repCoeff (JetComponentSpace.repConj repW) U s (ConjModule.map p v))
  rw [LocalGaugeData.repCoeff_repConj, LocalGaugeData.repCoeff_repConj]
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
    LocalGaugeData.TransformsIn (B := JetAlgebra) repJetGaugeGroupI
      (JetComponentSpace.repConj repW) F := by
  intro U φ s
  refine (congrArg (repJetGaugeGroupI U)
    ((hF s φ).trans (conjFermionSymbol_eq_includeFermion s _))).trans ?_
  refine (repJetGaugeGroupI_includeFermion U _).trans ?_
  refine (congrArg includeFermion
    (FermionicAlgebra.repJetGaugeGroupI_iteratedJetDeriv_ofConjField
      (M := fermionMatterField) U _ s)).trans ?_
  refine (map_multiset_sum includeFermion _).trans ?_
  refine (congrArg Multiset.sum (Multiset.map_map _ _ _)).trans ?_
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun q _ => ?_)
  exact (congrArg (fun χ : Module.Dual ℂ (ConjModule FermionSpace) =>
        includeFermion (FermionicAlgebra.iteratedJetDeriv q.2
          (FermionicAlgebra.ofConjField χ)))
      (repDualCoeff_repConj_transpose p (fun U' s' => repCoeff_comp p hp U' s')
        U⁻¹ q.1 φ)).trans
    ((conjFermionSymbol_eq_includeFermion q.2 _).symm.trans
      (hF q.2 (GaugeAlgebraRealization.repDualCoeff (JetComponentSpace.repConj repW)
        U⁻¹ q.1 φ)).symm)


/-- The symbols of the `i`-th generation down-type quark singlet transform in the jet gauge
  representation carried by the jets of that species. -/
theorem transformsIn_downSingletField (i : Fin 3) :
    LocalGaugeData.TransformsIn (B := JetAlgebra) repJetGaugeGroupI DownSinglet.repJetGaugeGroupI
      (downSingletField i) :=
  transformsIn_species _ _ (FermionSpace.lTensor_downSingletProj_repJetGaugeGroupI i)
    (downSingletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation down-type quark singlet transform in the
  conjugate of the jet gauge representation carried by the jets of that species. -/
theorem transformsIn_conjDownSingletField (i : Fin 3) :
    LocalGaugeData.TransformsIn (B := JetAlgebra) repJetGaugeGroupI
      (JetComponentSpace.repConj DownSinglet.repJetGaugeGroupI) (conjDownSingletField i) :=
  transformsIn_conjSpecies _ _ (FermionSpace.lTensor_downSingletProj_repJetGaugeGroupI i)
    (conjDownSingletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation up-type quark singlet transform in the jet gauge
  representation carried by the jets of that species. -/
theorem transformsIn_upSingletField (i : Fin 3) :
    LocalGaugeData.TransformsIn (B := JetAlgebra) repJetGaugeGroupI UpSinglet.repJetGaugeGroupI
      (upSingletField i) :=
  transformsIn_species _ _ (FermionSpace.lTensor_upSingletProj_repJetGaugeGroupI i)
    (upSingletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation up-type quark singlet transform in the
  conjugate of the jet gauge representation carried by the jets of that species. -/
theorem transformsIn_conjUpSingletField (i : Fin 3) :
    LocalGaugeData.TransformsIn (B := JetAlgebra) repJetGaugeGroupI
      (JetComponentSpace.repConj UpSinglet.repJetGaugeGroupI) (conjUpSingletField i) :=
  transformsIn_conjSpecies _ _ (FermionSpace.lTensor_upSingletProj_repJetGaugeGroupI i)
    (conjUpSingletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation quark doublet transform in the jet gauge
  representation carried by the jets of that species. -/
theorem transformsIn_quarkDoubletField (i : Fin 3) :
    LocalGaugeData.TransformsIn (B := JetAlgebra) repJetGaugeGroupI QuarkDoublet.repJetGaugeGroupI
      (quarkDoubletField i) :=
  transformsIn_species _ _ (FermionSpace.lTensor_quarkDoubletProj_repJetGaugeGroupI i)
    (quarkDoubletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation quark doublet transform in the
  conjugate of the jet gauge representation carried by the jets of that species. -/
theorem transformsIn_conjQuarkDoubletField (i : Fin 3) :
    LocalGaugeData.TransformsIn (B := JetAlgebra) repJetGaugeGroupI
      (JetComponentSpace.repConj QuarkDoublet.repJetGaugeGroupI) (conjQuarkDoubletField i) :=
  transformsIn_conjSpecies _ _ (FermionSpace.lTensor_quarkDoubletProj_repJetGaugeGroupI i)
    (conjQuarkDoubletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation lepton doublet transform in the jet gauge
  representation carried by the jets of that species. -/
theorem transformsIn_leptonDoubletField (i : Fin 3) :
    LocalGaugeData.TransformsIn (B := JetAlgebra) repJetGaugeGroupI LeptonDoublet.repJetGaugeGroupI
      (leptonDoubletField i) :=
  transformsIn_species _ _ (FermionSpace.lTensor_leptonDoubletProj_repJetGaugeGroupI i)
    (leptonDoubletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation lepton doublet transform in the
  conjugate of the jet gauge representation carried by the jets of that species. -/
theorem transformsIn_conjLeptonDoubletField (i : Fin 3) :
    LocalGaugeData.TransformsIn (B := JetAlgebra) repJetGaugeGroupI
      (JetComponentSpace.repConj LeptonDoublet.repJetGaugeGroupI) (conjLeptonDoubletField i) :=
  transformsIn_conjSpecies _ _ (FermionSpace.lTensor_leptonDoubletProj_repJetGaugeGroupI i)
    (conjLeptonDoubletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation charged-lepton singlet transform in the jet gauge
  representation carried by the jets of that species. -/
theorem transformsIn_leptonSingletField (i : Fin 3) :
    LocalGaugeData.TransformsIn (B := JetAlgebra) repJetGaugeGroupI LeptonSinglet.repJetGaugeGroupI
      (leptonSingletField i) :=
  transformsIn_species _ _ (FermionSpace.lTensor_leptonSingletProj_repJetGaugeGroupI i)
    (leptonSingletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation charged-lepton singlet transform in the
  conjugate of the jet gauge representation carried by the jets of that species. -/
theorem transformsIn_conjLeptonSingletField (i : Fin 3) :
    LocalGaugeData.TransformsIn (B := JetAlgebra) repJetGaugeGroupI
      (JetComponentSpace.repConj LeptonSinglet.repJetGaugeGroupI) (conjLeptonSingletField i) :=
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
  have hstart : ∀ (m : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℂ HiggsVec),
      Lorentz.iteratedD jetDeriv jetDeriv_comm m
          (includeHiggs (BosonicAlgebra.ofField χ)) = higgsField m χ :=
    fun m χ => (iteratedD_includeHiggs m (BosonicAlgebra.ofField χ)).trans
      (higgsField_eq_includeHiggs m χ).symm
  refine (congrArg (repLorentzGroup Λ) (hstart (List.ofFn l) φ).symm).trans ?_
  refine (Lorentz.IsLorentzDeriv.rep_iteratedD_ofFn jetDeriv_comm Λ l
    (includeHiggs (BosonicAlgebra.ofField (M := HiggsVec.matterField) φ))).trans ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  refine congrArg (fun z : JetAlgebra =>
    (∏ i, (((Lorentz.SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ) : ℂ)) • z) ?_
  exact (congrArg (fun z : JetAlgebra =>
      Lorentz.iteratedD jetDeriv jetDeriv_comm (List.ofFn p) z)
    ((repLorentzGroup_includeHiggs Λ (BosonicAlgebra.ofField (M := HiggsVec.matterField) φ)).trans
      (congrArg includeHiggs
        (BosonicAlgebra.repLorentzGroup_ofField (M := HiggsVec.matterField) Λ φ)))).trans
    (hstart (List.ofFn p) _)

/-- The conjugate Higgs symbols transform as the derivative symbols of the conjugate of a
  Lorentz scalar. -/
theorem isLorentzDerivTransforms_conjHiggsField :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      (Representation.trivial ℂ SL(2,ℂ) HiggsVec).conj conjHiggsField := by
  intro Λ n l φ
  have hstart : ∀ (m : Multiset (Fin 1 ⊕ Fin 3))
      (χ : Module.Dual ℂ (ConjModule HiggsVec)),
      Lorentz.iteratedD jetDeriv jetDeriv_comm m
          (includeHiggs (BosonicAlgebra.ofConjField χ)) = conjHiggsField m χ :=
    fun m χ => (iteratedD_includeHiggs m (BosonicAlgebra.ofConjField χ)).trans
      (conjHiggsField_eq_includeHiggs m χ).symm
  refine (congrArg (repLorentzGroup Λ) (hstart (List.ofFn l) φ).symm).trans ?_
  refine (Lorentz.IsLorentzDeriv.rep_iteratedD_ofFn jetDeriv_comm Λ l
    (includeHiggs (BosonicAlgebra.ofConjField (M := HiggsVec.matterField) φ))).trans ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  refine congrArg (fun z : JetAlgebra =>
    (∏ i, (((Lorentz.SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ) : ℂ)) • z) ?_
  exact (congrArg (fun z : JetAlgebra =>
      Lorentz.iteratedD jetDeriv jetDeriv_comm (List.ofFn p) z)
    ((repLorentzGroup_includeHiggs Λ (BosonicAlgebra.ofConjField (M := HiggsVec.matterField) φ)).trans
      (congrArg includeHiggs
        (BosonicAlgebra.repLorentzGroup_ofConjField (M := HiggsVec.matterField) Λ φ)))).trans
    (hstart (List.ofFn p) _)

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
  have hstart : ∀ (m : Multiset (Fin 1 ⊕ Fin 3)) (χ : Module.Dual ℂ FermionSpace),
      Lorentz.iteratedD jetDeriv jetDeriv_comm m
          (includeFermion (FermionicAlgebra.ofField χ)) = fermionSymbol m χ :=
    fun m χ => (iteratedD_includeFermion m (FermionicAlgebra.ofField χ)).trans
      (fermionSymbol_eq_includeFermion m χ).symm
  refine (congrArg (repLorentzGroup Λ)
    ((hF (List.ofFn l) φ).trans (hstart (List.ofFn l) _).symm)).trans ?_
  refine (Lorentz.IsLorentzDeriv.rep_iteratedD_ofFn jetDeriv_comm Λ l
    (includeFermion (FermionicAlgebra.ofField (Module.Dual.transpose p φ)))).trans ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  refine congrArg (fun z : JetAlgebra =>
    (∏ i, (((Lorentz.SL2C.toLorentzGroup Λ).1 (q i) (l i) : ℝ) : ℂ)) • z) ?_
  exact (congrArg (fun z : JetAlgebra =>
      Lorentz.iteratedD jetDeriv jetDeriv_comm (List.ofFn q) z)
    ((repLorentzGroup_includeFermion Λ _).trans
      (congrArg includeFermion
        ((FermionicAlgebra.repLorentzGroup_ofField _ Λ _).trans
          (congrArg FermionicAlgebra.ofField (hdual Λ φ)))))).trans
    ((hstart (List.ofFn q) _).trans (hF (List.ofFn q) (repW.dual Λ φ)).symm)

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
  have hstart : ∀ (m : Multiset (Fin 1 ⊕ Fin 3))
      (χ : Module.Dual ℂ (ConjModule FermionSpace)),
      Lorentz.iteratedD jetDeriv jetDeriv_comm m
          (includeFermion (FermionicAlgebra.ofConjField χ)) = conjFermionSymbol m χ :=
    fun m χ => (iteratedD_includeFermion m (FermionicAlgebra.ofConjField χ)).trans
      (conjFermionSymbol_eq_includeFermion m χ).symm
  refine (congrArg (repLorentzGroup Λ)
    ((hF (List.ofFn l) φ).trans (hstart (List.ofFn l) _).symm)).trans ?_
  refine (Lorentz.IsLorentzDeriv.rep_iteratedD_ofFn jetDeriv_comm Λ l
    (includeFermion (FermionicAlgebra.ofConjField
      (Module.Dual.transpose (ConjModule.map p) φ)))).trans ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  refine congrArg (fun z : JetAlgebra =>
    (∏ i, (((Lorentz.SL2C.toLorentzGroup Λ).1 (q i) (l i) : ℝ) : ℂ)) • z) ?_
  exact (congrArg (fun z : JetAlgebra =>
      Lorentz.iteratedD jetDeriv jetDeriv_comm (List.ofFn q) z)
    ((repLorentzGroup_includeFermion Λ _).trans
      (congrArg includeFermion
        ((FermionicAlgebra.repLorentzGroup_ofConjField _ Λ _).trans
          (congrArg FermionicAlgebra.ofConjField (hdual Λ φ)))))).trans
    ((hstart (List.ofFn q) _).trans (hF (List.ofFn q) (repW.conj.dual Λ φ)).symm)


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
