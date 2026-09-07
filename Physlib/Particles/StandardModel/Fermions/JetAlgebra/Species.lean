/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Fermions.JetAlgebra.Basic
public import Physlib.Particles.StandardModel.Matter.JetComponentSpace.CovariantDeriv
/-!
# Species compatibility inside the fermionic target space

## i. Overview

The fermionic jet algebra is built on `FermionSpace`, the product of the five fermion
species; but each species carries its own Lorentz and jet gauge representation, and the
Standard Model obligations are stated against those. This file is the bridge between the
two levels.

Everything rests on one fact: both actions on `FermionSpace` are species-diagonal — the
jet gauge action through `FermionSpace.jetActionMap`, the Lorentz action through
`Representation.pi` and `Representation.prod`. So each projection
`FermionSpace →ₗ[ℂ] Species` intertwines the total action with the species' own, and hence
also the base-point Taylor coefficients `IsGaugeField.repCoeff` of the two.

The third bridge runs the other way. Component functions are covectors, and a covector on
the species pulls back along the projection to a covector on `FermionSpace`; since
`FermionSpace` is a finite product, the identity is the sum over species and generations of
inclusion after projection, so every covector is a sum of pulled-back ones. The pulled-back
covectors therefore span, which is what lets an adjoin over the species covectors reach an
adjoin over all of them.

## ii. Key results

- `StandardModel.repCoeff_comp` : naturality of the base-point Taylor coefficients along a
  map of value spaces intertwining the two jet gauge actions.
- `FermionSpace.leptonDoubletProj_comp_repCoeff`, … : the gauge compatibility of the five
  species.
- `FermionSpace.leptonDoubletProj_comp_repLorentzGroup`, … : the Lorentz compatibility.
- `FermionSpace.span_speciesDual_eq_top`, `span_speciesConjDual_eq_top` : the covectors
  pulled back from the species span every covector.

## iii. Table of contents

- A. Naturality of the value-space jet toolkit
  - A.1. The pieces of `repCoeff`
  - A.2. Naturality of `repCoeff` and `repDualCoeff`
- B. The jet gauge action is species-diagonal
  - B.1. The species components of the splitting of the jets
  - B.2. The projections intertwine the jet gauge actions
  - B.3. The species compatibility of `repCoeff`
- C. The Lorentz action is species-diagonal
- D. Covectors pulled back from the species
  - D.1. The decomposition of the identity
  - D.2. Covectors
  - D.3. Conjugate covectors

-/

@[expose] public section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace StandardModel

open TensorProduct Matrix MatrixGroups

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-!

## A. Naturality of the value-space jet toolkit

-/

/-!

### A.1. The pieces of `repCoeff`

-/

/-- Including a constant into value-space jets is natural in the value space. -/
lemma lTensor_comp_jetOfConstant (p : V →ₗ[ℂ] W) :
    (LinearMap.lTensor JetRing p).comp jetOfConstant = jetOfConstant.comp p :=
  LinearMap.ext fun _ => rfl

/-- The formal derivative on value-space jets is natural in the value space: it touches
  only the jet factor. -/
lemma lTensor_comp_jetDeriv (p : V →ₗ[ℂ] W) (μ : Fin 1 ⊕ Fin 3) :
    (LinearMap.lTensor JetRing p).comp (jetDeriv μ)
      = (jetDeriv μ).comp (LinearMap.lTensor JetRing p) :=
  TensorProduct.ext' fun _ _ => rfl

/-- The iterated formal derivative on value-space jets is natural in the value space. -/
lemma lTensor_comp_jetIteratedDeriv (p : V →ₗ[ℂ] W) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    (LinearMap.lTensor JetRing p).comp (jetIteratedDeriv s)
      = (jetIteratedDeriv s).comp (LinearMap.lTensor JetRing p) := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [jetIteratedDeriv_zero, LinearMap.comp_id, jetIteratedDeriv_zero,
      LinearMap.id_comp]
  | cons μ s ih =>
    rw [jetIteratedDeriv_cons, jetIteratedDeriv_cons, ← LinearMap.comp_assoc,
      lTensor_comp_jetDeriv, LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]

/-- Evaluation of a value-space jet at the base point is natural in the value space. -/
lemma jetEval_comp_lTensor (p : V →ₗ[ℂ] W) :
    (jetEval (V := W)).comp (LinearMap.lTensor JetRing p) = p.comp jetEval :=
  TensorProduct.ext' fun f v => by
    rw [LinearMap.comp_apply, LinearMap.lTensor_tmul, jetEval_tmul, LinearMap.comp_apply,
      jetEval_tmul, map_smul]

/-!

### A.2. Naturality of `repCoeff` and `repDualCoeff`

-/

/-- The base-point Taylor coefficients of two jet gauge actions are intertwined by any map
  of value spaces intertwining the actions themselves: `repCoeff` is built from
  `jetOfConstant`, `jetIteratedDeriv` and `jetEval`, and each of those is natural. -/
lemma repCoeff_comp {repV : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V)}
    {repW : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] W)} (p : V →ₗ[ℂ] W)
    (hp : ∀ U : JetGaugeGroupI, (LinearMap.lTensor JetRing p).comp (repV U)
      = (repW U).comp (LinearMap.lTensor JetRing p))
    (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    p.comp (IsGaugeField.repCoeff repV U s)
      = (IsGaugeField.repCoeff repW U s).comp p := by
  refine LinearMap.ext fun v => ?_
  have h1 := LinearMap.congr_fun (lTensor_comp_jetOfConstant p) v
  have h2 := LinearMap.congr_fun (hp U) (jetOfConstant v)
  have h3 := LinearMap.congr_fun (lTensor_comp_jetIteratedDeriv p s)
    (repV U (jetOfConstant v))
  have h4 := LinearMap.congr_fun (jetEval_comp_lTensor p)
    (jetIteratedDeriv s (repV U (jetOfConstant v)))
  simp only [LinearMap.comp_apply] at h1 h2 h3 h4 ⊢
  simp only [IsGaugeField.repCoeff, LinearMap.comp_apply]
  rw [← h4, h3, h2, h1]

/-- The transposed form of `repCoeff_comp`: the dual coefficients, which act on the
  component-function index, are intertwined the other way round. -/
lemma repDualCoeff_comp {repV : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V)}
    {repW : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] W)} (p : V →ₗ[ℂ] W)
    (hp : ∀ U : JetGaugeGroupI, (LinearMap.lTensor JetRing p).comp (repV U)
      = (repW U).comp (LinearMap.lTensor JetRing p))
    (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    (IsGaugeField.repDualCoeff repV U s).comp (Module.Dual.transpose p)
      = (Module.Dual.transpose p).comp (IsGaugeField.repDualCoeff repW U s) :=
  LinearMap.ext fun φ => LinearMap.ext fun v =>
    congrArg φ (LinearMap.congr_fun (repCoeff_comp p hp U s) v)

/-!

## B. The jet gauge action is species-diagonal

-/

namespace FermionSpace

/-!

### B.1. The species components of the splitting of the jets

The splitting `FermionSpace.jetEquiv` of the jets of the total fermionic field is, in each
species-and-generation slot, nothing but the projection applied to the value factor.

-/

/-- The lepton-doublet slot of the splitting of the jets is the projection on the value
  factor. -/
lemma jetEquiv_leptonDoublet (i : Fin 3) (z : JetRing ⊗[ℂ] FermionSpace) :
    (jetEquiv z).1 i = LinearMap.lTensor JetRing (leptonDoubletProj i) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul f v => rfl

/-- The charged-lepton-singlet slot of the splitting of the jets is the projection on the value
  factor. -/
lemma jetEquiv_leptonSinglet (i : Fin 3) (z : JetRing ⊗[ℂ] FermionSpace) :
    (jetEquiv z).2.1 i = LinearMap.lTensor JetRing (leptonSingletProj i) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul f v => rfl

/-- The quark-doublet slot of the splitting of the jets is the projection on the value
  factor. -/
lemma jetEquiv_quarkDoublet (i : Fin 3) (z : JetRing ⊗[ℂ] FermionSpace) :
    (jetEquiv z).2.2.1 i = LinearMap.lTensor JetRing (quarkDoubletProj i) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul f v => rfl

/-- The up-type-quark-singlet slot of the splitting of the jets is the projection on the value
  factor. -/
lemma jetEquiv_upSinglet (i : Fin 3) (z : JetRing ⊗[ℂ] FermionSpace) :
    (jetEquiv z).2.2.2.1 i = LinearMap.lTensor JetRing (upSingletProj i) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul f v => rfl

/-- The down-type-quark-singlet slot of the splitting of the jets is the projection on the value
  factor. -/
lemma jetEquiv_downSinglet (i : Fin 3) (z : JetRing ⊗[ℂ] FermionSpace) :
    (jetEquiv z).2.2.2.2 i = LinearMap.lTensor JetRing (downSingletProj i) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul f v => rfl

/-!

### B.2. The projections intertwine the jet gauge actions

`FermionSpace.jetActionMap` is a product of the species actions, slot by slot, so through
the splitting of B.1 each projection carries the total jet gauge action to the species'
own.

-/

/-- The lepton-doublet projection intertwines the total jet gauge action with the
  lepton doublet's own. -/
lemma lTensor_leptonDoubletProj_repJetGaugeGroupI (i : Fin 3) (U : JetGaugeGroupI) :
    (LinearMap.lTensor JetRing (leptonDoubletProj i)).comp (repJetGaugeGroupI U)
      = (LeptonDoublet.repJetGaugeGroupI U).comp
        (LinearMap.lTensor JetRing (leptonDoubletProj i)) := by
  refine LinearMap.ext fun z => ?_
  have hz : jetEquiv (repJetGaugeGroupI U z) = jetActionMap U (jetEquiv z) := by
    show (jetEquiv.restrictScalars ℂ) ((jetEquiv.restrictScalars ℂ).symm
        (jetActionMap U ((jetEquiv.restrictScalars ℂ) z)))
      = jetActionMap U (jetEquiv z)
    rw [(jetEquiv.restrictScalars ℂ).apply_symm_apply]
    rfl
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← jetEquiv_leptonDoublet,
    ← jetEquiv_leptonDoublet, hz]
  rfl

/-- The charged-lepton-singlet projection intertwines the total jet gauge action with the
  charged-lepton singlet's own. -/
lemma lTensor_leptonSingletProj_repJetGaugeGroupI (i : Fin 3) (U : JetGaugeGroupI) :
    (LinearMap.lTensor JetRing (leptonSingletProj i)).comp (repJetGaugeGroupI U)
      = (LeptonSinglet.repJetGaugeGroupI U).comp
        (LinearMap.lTensor JetRing (leptonSingletProj i)) := by
  refine LinearMap.ext fun z => ?_
  have hz : jetEquiv (repJetGaugeGroupI U z) = jetActionMap U (jetEquiv z) := by
    show (jetEquiv.restrictScalars ℂ) ((jetEquiv.restrictScalars ℂ).symm
        (jetActionMap U ((jetEquiv.restrictScalars ℂ) z)))
      = jetActionMap U (jetEquiv z)
    rw [(jetEquiv.restrictScalars ℂ).apply_symm_apply]
    rfl
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← jetEquiv_leptonSinglet,
    ← jetEquiv_leptonSinglet, hz]
  rfl

/-- The quark-doublet projection intertwines the total jet gauge action with the
  quark doublet's own. -/
lemma lTensor_quarkDoubletProj_repJetGaugeGroupI (i : Fin 3) (U : JetGaugeGroupI) :
    (LinearMap.lTensor JetRing (quarkDoubletProj i)).comp (repJetGaugeGroupI U)
      = (QuarkDoublet.repJetGaugeGroupI U).comp
        (LinearMap.lTensor JetRing (quarkDoubletProj i)) := by
  refine LinearMap.ext fun z => ?_
  have hz : jetEquiv (repJetGaugeGroupI U z) = jetActionMap U (jetEquiv z) := by
    show (jetEquiv.restrictScalars ℂ) ((jetEquiv.restrictScalars ℂ).symm
        (jetActionMap U ((jetEquiv.restrictScalars ℂ) z)))
      = jetActionMap U (jetEquiv z)
    rw [(jetEquiv.restrictScalars ℂ).apply_symm_apply]
    rfl
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← jetEquiv_quarkDoublet,
    ← jetEquiv_quarkDoublet, hz]
  rfl

/-- The up-type-quark-singlet projection intertwines the total jet gauge action with the
  up-type quark singlet's own. -/
lemma lTensor_upSingletProj_repJetGaugeGroupI (i : Fin 3) (U : JetGaugeGroupI) :
    (LinearMap.lTensor JetRing (upSingletProj i)).comp (repJetGaugeGroupI U)
      = (UpSinglet.repJetGaugeGroupI U).comp
        (LinearMap.lTensor JetRing (upSingletProj i)) := by
  refine LinearMap.ext fun z => ?_
  have hz : jetEquiv (repJetGaugeGroupI U z) = jetActionMap U (jetEquiv z) := by
    show (jetEquiv.restrictScalars ℂ) ((jetEquiv.restrictScalars ℂ).symm
        (jetActionMap U ((jetEquiv.restrictScalars ℂ) z)))
      = jetActionMap U (jetEquiv z)
    rw [(jetEquiv.restrictScalars ℂ).apply_symm_apply]
    rfl
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← jetEquiv_upSinglet,
    ← jetEquiv_upSinglet, hz]
  rfl

/-- The down-type-quark-singlet projection intertwines the total jet gauge action with the
  down-type quark singlet's own. -/
lemma lTensor_downSingletProj_repJetGaugeGroupI (i : Fin 3) (U : JetGaugeGroupI) :
    (LinearMap.lTensor JetRing (downSingletProj i)).comp (repJetGaugeGroupI U)
      = (DownSinglet.repJetGaugeGroupI U).comp
        (LinearMap.lTensor JetRing (downSingletProj i)) := by
  refine LinearMap.ext fun z => ?_
  have hz : jetEquiv (repJetGaugeGroupI U z) = jetActionMap U (jetEquiv z) := by
    show (jetEquiv.restrictScalars ℂ) ((jetEquiv.restrictScalars ℂ).symm
        (jetActionMap U ((jetEquiv.restrictScalars ℂ) z)))
      = jetActionMap U (jetEquiv z)
    rw [(jetEquiv.restrictScalars ℂ).apply_symm_apply]
    rfl
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← jetEquiv_downSinglet,
    ← jetEquiv_downSinglet, hz]
  rfl

/-!

### B.3. The species compatibility of `repCoeff`

-/

/-- The lepton-doublet projection intertwines the base-point Taylor coefficients of
  the total jet gauge action with those of the lepton doublet's own. -/
lemma leptonDoubletProj_comp_repCoeff (i : Fin 3) (U : JetGaugeGroupI)
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    (leptonDoubletProj i).comp (IsGaugeField.repCoeff repJetGaugeGroupI U s)
      = (IsGaugeField.repCoeff LeptonDoublet.repJetGaugeGroupI U s).comp (leptonDoubletProj i) :=
  repCoeff_comp _ (lTensor_leptonDoubletProj_repJetGaugeGroupI i) U s

/-- The charged-lepton-singlet projection intertwines the base-point Taylor coefficients of
  the total jet gauge action with those of the charged-lepton singlet's own. -/
lemma leptonSingletProj_comp_repCoeff (i : Fin 3) (U : JetGaugeGroupI)
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    (leptonSingletProj i).comp (IsGaugeField.repCoeff repJetGaugeGroupI U s)
      = (IsGaugeField.repCoeff LeptonSinglet.repJetGaugeGroupI U s).comp (leptonSingletProj i) :=
  repCoeff_comp _ (lTensor_leptonSingletProj_repJetGaugeGroupI i) U s

/-- The quark-doublet projection intertwines the base-point Taylor coefficients of
  the total jet gauge action with those of the quark doublet's own. -/
lemma quarkDoubletProj_comp_repCoeff (i : Fin 3) (U : JetGaugeGroupI)
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    (quarkDoubletProj i).comp (IsGaugeField.repCoeff repJetGaugeGroupI U s)
      = (IsGaugeField.repCoeff QuarkDoublet.repJetGaugeGroupI U s).comp (quarkDoubletProj i) :=
  repCoeff_comp _ (lTensor_quarkDoubletProj_repJetGaugeGroupI i) U s

/-- The up-type-quark-singlet projection intertwines the base-point Taylor coefficients of
  the total jet gauge action with those of the up-type quark singlet's own. -/
lemma upSingletProj_comp_repCoeff (i : Fin 3) (U : JetGaugeGroupI)
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    (upSingletProj i).comp (IsGaugeField.repCoeff repJetGaugeGroupI U s)
      = (IsGaugeField.repCoeff UpSinglet.repJetGaugeGroupI U s).comp (upSingletProj i) :=
  repCoeff_comp _ (lTensor_upSingletProj_repJetGaugeGroupI i) U s

/-- The down-type-quark-singlet projection intertwines the base-point Taylor coefficients of
  the total jet gauge action with those of the down-type quark singlet's own. -/
lemma downSingletProj_comp_repCoeff (i : Fin 3) (U : JetGaugeGroupI)
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    (downSingletProj i).comp (IsGaugeField.repCoeff repJetGaugeGroupI U s)
      = (IsGaugeField.repCoeff DownSinglet.repJetGaugeGroupI U s).comp (downSingletProj i) :=
  repCoeff_comp _ (lTensor_downSingletProj_repJetGaugeGroupI i) U s

/-!

## C. The Lorentz action is species-diagonal

`FermionSpace.repLorentzGroup` is a `Representation.prod` of `Representation.pi`s of the
species representations, so each projection intertwines it with the species' own Lorentz
action on the nose.

-/

/-- The lepton-doublet projection intertwines the total Lorentz action with the
  lepton doublet's own. -/
lemma leptonDoubletProj_comp_repLorentzGroup (i : Fin 3) (Λ : SL(2,ℂ)) :
    (leptonDoubletProj i).comp (repLorentzGroup Λ)
      = (LeptonDoublet.repLorentzGroup Λ).comp (leptonDoubletProj i) := rfl

/-- The charged-lepton-singlet projection intertwines the total Lorentz action with the
  charged-lepton singlet's own. -/
lemma leptonSingletProj_comp_repLorentzGroup (i : Fin 3) (Λ : SL(2,ℂ)) :
    (leptonSingletProj i).comp (repLorentzGroup Λ)
      = (LeptonSinglet.repLorentzGroup Λ).comp (leptonSingletProj i) := rfl

/-- The quark-doublet projection intertwines the total Lorentz action with the
  quark doublet's own. -/
lemma quarkDoubletProj_comp_repLorentzGroup (i : Fin 3) (Λ : SL(2,ℂ)) :
    (quarkDoubletProj i).comp (repLorentzGroup Λ)
      = (QuarkDoublet.repLorentzGroup Λ).comp (quarkDoubletProj i) := rfl

/-- The up-type-quark-singlet projection intertwines the total Lorentz action with the
  up-type quark singlet's own. -/
lemma upSingletProj_comp_repLorentzGroup (i : Fin 3) (Λ : SL(2,ℂ)) :
    (upSingletProj i).comp (repLorentzGroup Λ)
      = (UpSinglet.repLorentzGroup Λ).comp (upSingletProj i) := rfl

/-- The down-type-quark-singlet projection intertwines the total Lorentz action with the
  down-type quark singlet's own. -/
lemma downSingletProj_comp_repLorentzGroup (i : Fin 3) (Λ : SL(2,ℂ)) :
    (downSingletProj i).comp (repLorentzGroup Λ)
      = (DownSinglet.repLorentzGroup Λ).comp (downSingletProj i) := rfl

/-!

## D. Covectors pulled back from the species

-/

/-!

### D.1. The decomposition of the identity

-/

/-- The identity on the total fermionic target space is the sum, over the five species and
  the three generations, of the inclusion after the projection. -/
lemma sum_incl_proj (v : FermionSpace) :
    (∑ i, leptonDoubletIncl i (leptonDoubletProj i v))
      + (∑ i, leptonSingletIncl i (leptonSingletProj i v))
      + (∑ i, quarkDoubletIncl i (quarkDoubletProj i v))
      + (∑ i, upSingletIncl i (upSingletProj i v))
      + (∑ i, downSingletIncl i (downSingletProj i v)) = v := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))) <;>
  · funext j
    simp [leptonDoubletIncl, leptonSingletIncl, quarkDoubletIncl, upSingletIncl,
      downSingletIncl, leptonDoubletProj, leptonSingletProj, quarkDoubletProj,
      upSingletProj, downSingletProj, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply,
      Pi.single_apply]

/-- The conjugate form of `sum_incl_proj`: conjugation leaves the underlying additive
  group and the underlying maps alone. -/
lemma sum_conj_incl_proj (v : ConjModule FermionSpace) :
    (∑ i, ConjModule.map (leptonDoubletIncl i)
        (ConjModule.map (leptonDoubletProj i) v))
      + (∑ i, ConjModule.map (leptonSingletIncl i)
          (ConjModule.map (leptonSingletProj i) v))
      + (∑ i, ConjModule.map (quarkDoubletIncl i)
          (ConjModule.map (quarkDoubletProj i) v))
      + (∑ i, ConjModule.map (upSingletIncl i)
          (ConjModule.map (upSingletProj i) v))
      + (∑ i, ConjModule.map (downSingletIncl i)
          (ConjModule.map (downSingletProj i) v)) = v :=
  sum_incl_proj v

/-!

### D.2. Covectors

-/

/-- Every covector on the total fermionic target space is the sum, over the five species
  and the three generations, of its restriction to that species and generation pulled back
  along the corresponding projection. -/
lemma dual_eq_sum (φ : Module.Dual ℂ FermionSpace) :
    φ = (∑ i, Module.Dual.transpose (leptonDoubletProj i)
          (Module.Dual.transpose (leptonDoubletIncl i) φ))
      + (∑ i, Module.Dual.transpose (leptonSingletProj i)
          (Module.Dual.transpose (leptonSingletIncl i) φ))
      + (∑ i, Module.Dual.transpose (quarkDoubletProj i)
          (Module.Dual.transpose (quarkDoubletIncl i) φ))
      + (∑ i, Module.Dual.transpose (upSingletProj i)
          (Module.Dual.transpose (upSingletIncl i) φ))
      + (∑ i, Module.Dual.transpose (downSingletProj i)
          (Module.Dual.transpose (downSingletIncl i) φ)) := by
  refine LinearMap.ext fun v => ?_
  have h := congrArg φ (sum_incl_proj v)
  simp only [map_add, map_sum] at h
  simp only [LinearMap.add_apply, LinearMap.sum_apply]
  exact h.symm

/-- The covectors on the total fermionic target space that are pulled back from a single
  species and generation. -/
def speciesDual : Set (Module.Dual ℂ FermionSpace) :=
  {φ | (∃ (i : Fin 3) (ψ : Module.Dual ℂ LeptonDoublet),
        φ = Module.Dual.transpose (leptonDoubletProj i) ψ)
    ∨ (∃ (i : Fin 3) (ψ : Module.Dual ℂ LeptonSinglet),
        φ = Module.Dual.transpose (leptonSingletProj i) ψ)
    ∨ (∃ (i : Fin 3) (ψ : Module.Dual ℂ QuarkDoublet),
        φ = Module.Dual.transpose (quarkDoubletProj i) ψ)
    ∨ (∃ (i : Fin 3) (ψ : Module.Dual ℂ UpSinglet),
        φ = Module.Dual.transpose (upSingletProj i) ψ)
    ∨ (∃ (i : Fin 3) (ψ : Module.Dual ℂ DownSinglet),
        φ = Module.Dual.transpose (downSingletProj i) ψ)}

/-- The covectors pulled back from the individual species and generations span every
  covector on the total fermionic target space. This is what lets an adjoin taken over the
  species covectors reach an adjoin taken over all of them. -/
lemma span_speciesDual_eq_top : Submodule.span ℂ speciesDual = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun φ => ?_
  rw [dual_eq_sum φ]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ ?_ ?_) ?_) ?_) ?_
  · exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span (Or.inl ⟨i, _, rfl⟩)
  · exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span (Or.inr (Or.inl ⟨i, _, rfl⟩))
  · exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span (Or.inr (Or.inr (Or.inl ⟨i, _, rfl⟩)))
  · exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, _, rfl⟩))))
  · exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, _, rfl⟩))))

/-!

### D.3. Conjugate covectors

-/

/-- The conjugate form of `dual_eq_sum`: every covector on the conjugate of the total
  fermionic target space is the sum of the covectors pulled back from the species and
  generations. -/
lemma conjDual_eq_sum (φ : Module.Dual ℂ (ConjModule FermionSpace)) :
    φ = (∑ i, Module.Dual.transpose (ConjModule.map (leptonDoubletProj i))
          (Module.Dual.transpose (ConjModule.map (leptonDoubletIncl i)) φ))
      + (∑ i, Module.Dual.transpose (ConjModule.map (leptonSingletProj i))
          (Module.Dual.transpose (ConjModule.map (leptonSingletIncl i)) φ))
      + (∑ i, Module.Dual.transpose (ConjModule.map (quarkDoubletProj i))
          (Module.Dual.transpose (ConjModule.map (quarkDoubletIncl i)) φ))
      + (∑ i, Module.Dual.transpose (ConjModule.map (upSingletProj i))
          (Module.Dual.transpose (ConjModule.map (upSingletIncl i)) φ))
      + (∑ i, Module.Dual.transpose (ConjModule.map (downSingletProj i))
          (Module.Dual.transpose (ConjModule.map (downSingletIncl i)) φ)) := by
  refine LinearMap.ext fun v => ?_
  have h := congrArg φ (sum_conj_incl_proj v)
  simp only [map_add, map_sum] at h
  simp only [LinearMap.add_apply, LinearMap.sum_apply]
  exact h.symm

/-- The covectors on the conjugate of the total fermionic target space that are pulled
  back from a single species and generation. -/
def speciesConjDual : Set (Module.Dual ℂ (ConjModule FermionSpace)) :=
  {φ | (∃ (i : Fin 3) (ψ : Module.Dual ℂ (ConjModule LeptonDoublet)),
        φ = Module.Dual.transpose (ConjModule.map (leptonDoubletProj i)) ψ)
    ∨ (∃ (i : Fin 3) (ψ : Module.Dual ℂ (ConjModule LeptonSinglet)),
        φ = Module.Dual.transpose (ConjModule.map (leptonSingletProj i)) ψ)
    ∨ (∃ (i : Fin 3) (ψ : Module.Dual ℂ (ConjModule QuarkDoublet)),
        φ = Module.Dual.transpose (ConjModule.map (quarkDoubletProj i)) ψ)
    ∨ (∃ (i : Fin 3) (ψ : Module.Dual ℂ (ConjModule UpSinglet)),
        φ = Module.Dual.transpose (ConjModule.map (upSingletProj i)) ψ)
    ∨ (∃ (i : Fin 3) (ψ : Module.Dual ℂ (ConjModule DownSinglet)),
        φ = Module.Dual.transpose (ConjModule.map (downSingletProj i)) ψ)}

/-- The conjugate covectors pulled back from the individual species and generations span
  every covector on the conjugate of the total fermionic target space. -/
lemma span_speciesConjDual_eq_top : Submodule.span ℂ speciesConjDual = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun φ => ?_
  rw [conjDual_eq_sum φ]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ ?_ ?_) ?_) ?_) ?_
  · exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span (Or.inl ⟨i, _, rfl⟩)
  · exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span (Or.inr (Or.inl ⟨i, _, rfl⟩))
  · exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span (Or.inr (Or.inr (Or.inl ⟨i, _, rfl⟩)))
  · exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, _, rfl⟩))))
  · exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, _, rfl⟩))))

end FermionSpace

end StandardModel

