/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import Physlib.Particles.StandardModel.JetAlgebra.CovJetAlgebra.Basic
public import Physlib.Particles.StandardModel.AlgebraRealization.HiggsAlgebraCovRealization.Basic
public import Physlib.Particles.StandardModel.JetAlgebra.CovJetAlgebra.Higgs
public import Physlib.Particles.StandardModel.IsGaugeSector.MassWeight.Basic
public import Physlib.Particles.StandardModel.IsFermionSector.MassWeight.Basic
/-!
# The sectors of the covariant jet algebra

## i. Overview

The covariant jet algebra of `CovJetAlgebra.Basic` carries the thirteen covariant towers,
the global gauge action, the Lorentz action and the mass-weight polynomial. This file
records that they split into the three sectors — gauge, Higgs and fermion — and that the
towers of different sectors commute: every gauge-equivariance, Lorentz, mass-weight and
commutation law of the covariant form of the Standard Model holds there.

Nothing new is proved. Each law is the corresponding law of `AlgebraRealization.id` — the
jet algebra's own — read on the subalgebra, where equality is equality of underlying jet
algebra elements. The transport lemmas the three shapes need are section E of
[`Basic.lean`](Basic.lean); this file assembles them.

`CovJetAlgebra` is to the covariant theory what `JetAlgebra` is to the theory in the bare
symbols: the object every other covariant Standard Model receives its fields from. That is
the content of `CovAlgebraRealization`.

## ii. Key results

- `StandardModel.CovJetAlgebra.isHiggsSector`, `StandardModel.CovJetAlgebra.isGaugeSector`,
  `StandardModel.CovJetAlgebra.isFermionSector` : the three sectors of the covariant jet
  algebra.
- `StandardModel.CovJetAlgebra.F_comm_H` and its companions : the towers of different
  sectors commute.

## iii. Table of contents

- A. The three sectors and the cross-sector commutation rules

-/

@[expose] public section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

namespace CovJetAlgebra

/-!

## A. The three sectors and the cross-sector commutation rules

-/

/-- The Higgs sector of the covariant jet algebra: its Higgs towers are the covariant jet
  algebra of the Higgs field, included. -/
noncomputable def isHiggsSector :
    HiggsAlgebraCovRealization CovJetAlgebra repGaugeGroupI repLorentzGroup massWeightPoly where
  toAlgHom := higgsSubalgebra.val
  map_rep _ _ := rfl
  map_repLorentz _ _ := rfl
  map_massWeight x := (Subalgebra.mapAlgHom_polyRestrict _ x).symm
  rep_mul := repGaugeGroupI_mul
  repLorentz_mul := repLorentzGroup_mul

TODO (lines := 64-75) (date := 2026-09-08) "This should be
  renamed to HiggsAlgebraCovRealization.id"

/-- The gauge sector of the covariant jet algebra. -/
theorem isGaugeSector : IsGaugeSector CovJetAlgebra repGaugeGroupI repGaugeGroupI_mul
    repLorentzGroup repLorentzGroup_mul (fun {_n} l μ ν => fieldStrength l μ ν)
    massWeightPoly where
  repGauge_F := fun g {_n} l μ ν φ =>
    Subtype.ext (AlgebraRealization.id.repGlobal_covF g l μ ν φ)
  repLorentz_F := fun Λ n l μ ν φ => Subtype.ext <| by
    simp only [AlgebraRealization.coe_covRepLorentz, AddSubmonoidClass.coe_finsetSum,
      SetLike.val_smul, coe_fieldStrength]
    exact AlgebraRealization.id.repLorentz_covF Λ n l μ ν φ
  massWeight_F := fun {_n} l μ ν φ =>
    massWeightPoly_eq_monomial (AlgebraRealization.id.massWeight_covF l μ ν φ)
  F_comm_F := fun {_n _m} l μ ν ψ l' μ' ν' ψ' =>
    Subtype.ext (AlgebraRealization.id.covF_comm_covF l l' μ ν μ' ν' ψ ψ')
  F_antisymm := fun {_n} l μ ν φ => Subtype.ext (AlgebraRealization.id.covF_swap l μ ν φ)

/-- The fermion sector of the covariant jet algebra. -/
theorem isFermionSector : IsFermionSector CovJetAlgebra repGaugeGroupI repGaugeGroupI_mul
    repLorentzGroup repLorentzGroup_mul
    (fun {_n} i l => downSingletField i l) (fun {_n} i l => conjDownSingletField i l)
    (fun {_n} i l => upSingletField i l) (fun {_n} i l => conjUpSingletField i l)
    (fun {_n} i l => quarkDoubletField i l) (fun {_n} i l => conjQuarkDoubletField i l)
    (fun {_n} i l => leptonDoubletField i l) (fun {_n} i l => conjLeptonDoubletField i l)
    (fun {_n} i l => leptonSingletField i l) (fun {_n} i l => conjLeptonSingletField i l)
    massWeightPoly where
  repGauge_d := fun g i {_n} l φ =>
    Subtype.ext (AlgebraRealization.id.repGlobal_covDerivD g i l φ)
  repGauge_bard := fun g i {_n} l φ =>
    Subtype.ext (AlgebraRealization.id.repGlobal_covDerivBarD g i l φ)
  repGauge_u := fun g i {_n} l φ =>
    Subtype.ext (AlgebraRealization.id.repGlobal_covDerivU g i l φ)
  repGauge_baru := fun g i {_n} l φ =>
    Subtype.ext (AlgebraRealization.id.repGlobal_covDerivBarU g i l φ)
  repGauge_Q := fun g i {_n} l φ =>
    Subtype.ext (AlgebraRealization.id.repGlobal_covDerivQ g i l φ)
  repGauge_barQ := fun g i {_n} l φ =>
    Subtype.ext (AlgebraRealization.id.repGlobal_covDerivBarQ g i l φ)
  repGauge_L := fun g i {_n} l φ =>
    Subtype.ext (AlgebraRealization.id.repGlobal_covDerivL g i l φ)
  repGauge_barL := fun g i {_n} l φ =>
    Subtype.ext (AlgebraRealization.id.repGlobal_covDerivBarL g i l φ)
  repGauge_e := fun g i {_n} l φ =>
    Subtype.ext (AlgebraRealization.id.repGlobal_covDerivE g i l φ)
  repGauge_bare := fun g i {_n} l φ =>
    Subtype.ext (AlgebraRealization.id.repGlobal_covDerivBarE g i l φ)
  repLorentz_d := fun i =>
    isLorentzCovDerivTransforms_of (AlgebraRealization.id.repLorentz_covDerivD i)
  repLorentz_bard := fun i =>
    isLorentzCovDerivTransforms_of (AlgebraRealization.id.repLorentz_covDerivBarD i)
  repLorentz_u := fun i =>
    isLorentzCovDerivTransforms_of (AlgebraRealization.id.repLorentz_covDerivU i)
  repLorentz_baru := fun i =>
    isLorentzCovDerivTransforms_of (AlgebraRealization.id.repLorentz_covDerivBarU i)
  repLorentz_Q := fun i =>
    isLorentzCovDerivTransforms_of (AlgebraRealization.id.repLorentz_covDerivQ i)
  repLorentz_barQ := fun i =>
    isLorentzCovDerivTransforms_of (AlgebraRealization.id.repLorentz_covDerivBarQ i)
  repLorentz_L := fun i =>
    isLorentzCovDerivTransforms_of (AlgebraRealization.id.repLorentz_covDerivL i)
  repLorentz_barL := fun i =>
    isLorentzCovDerivTransforms_of (AlgebraRealization.id.repLorentz_covDerivBarL i)
  repLorentz_e := fun i =>
    isLorentzCovDerivTransforms_of (AlgebraRealization.id.repLorentz_covDerivE i)
  repLorentz_bare := fun i =>
    isLorentzCovDerivTransforms_of (AlgebraRealization.id.repLorentz_covDerivBarE i)
  massWeight_d := fun i {_n} l φ =>
    massWeightPoly_eq_monomial (AlgebraRealization.id.massWeight_covDerivD i l φ)
  massWeight_bard := fun i {_n} l φ =>
    massWeightPoly_eq_monomial (AlgebraRealization.id.massWeight_covDerivBarD i l φ)
  massWeight_u := fun i {_n} l φ =>
    massWeightPoly_eq_monomial (AlgebraRealization.id.massWeight_covDerivU i l φ)
  massWeight_baru := fun i {_n} l φ =>
    massWeightPoly_eq_monomial (AlgebraRealization.id.massWeight_covDerivBarU i l φ)
  massWeight_Q := fun i {_n} l φ =>
    massWeightPoly_eq_monomial (AlgebraRealization.id.massWeight_covDerivQ i l φ)
  massWeight_barQ := fun i {_n} l φ =>
    massWeightPoly_eq_monomial (AlgebraRealization.id.massWeight_covDerivBarQ i l φ)
  massWeight_L := fun i {_n} l φ =>
    massWeightPoly_eq_monomial (AlgebraRealization.id.massWeight_covDerivL i l φ)
  massWeight_barL := fun i {_n} l φ =>
    massWeightPoly_eq_monomial (AlgebraRealization.id.massWeight_covDerivBarL i l φ)
  massWeight_e := fun i {_n} l φ =>
    massWeightPoly_eq_monomial (AlgebraRealization.id.massWeight_covDerivE i l φ)
  massWeight_bare := fun i {_n} l φ =>
    massWeightPoly_eq_monomial (AlgebraRealization.id.massWeight_covDerivBarE i l φ)
  d_anticomm_d := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covD_anticomm_covD i j l l' φ φ')
  d_anticomm_bard := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covD_anticomm_covBarD i j l l' φ φ')
  d_anticomm_u := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covD_anticomm_covU i j l l' φ φ')
  d_anticomm_baru := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covD_anticomm_covBarU i j l l' φ φ')
  d_anticomm_Q := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covD_anticomm_covQ i j l l' φ φ')
  d_anticomm_barQ := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covD_anticomm_covBarQ i j l l' φ φ')
  d_anticomm_L := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covD_anticomm_covL i j l l' φ φ')
  d_anticomm_barL := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covD_anticomm_covBarL i j l l' φ φ')
  d_anticomm_e := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covD_anticomm_covE i j l l' φ φ')
  d_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covD_anticomm_covBarE i j l l' φ φ')
  bard_anticomm_bard := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarD_anticomm_covBarD i j l l' φ φ')
  bard_anticomm_u := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarD_anticomm_covU i j l l' φ φ')
  bard_anticomm_baru := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarD_anticomm_covBarU i j l l' φ φ')
  bard_anticomm_Q := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarD_anticomm_covQ i j l l' φ φ')
  bard_anticomm_barQ := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarD_anticomm_covBarQ i j l l' φ φ')
  bard_anticomm_L := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarD_anticomm_covL i j l l' φ φ')
  bard_anticomm_barL := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarD_anticomm_covBarL i j l l' φ φ')
  bard_anticomm_e := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarD_anticomm_covE i j l l' φ φ')
  bard_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarD_anticomm_covBarE i j l l' φ φ')
  u_anticomm_u := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covU_anticomm_covU i j l l' φ φ')
  u_anticomm_baru := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covU_anticomm_covBarU i j l l' φ φ')
  u_anticomm_Q := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covU_anticomm_covQ i j l l' φ φ')
  u_anticomm_barQ := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covU_anticomm_covBarQ i j l l' φ φ')
  u_anticomm_L := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covU_anticomm_covL i j l l' φ φ')
  u_anticomm_barL := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covU_anticomm_covBarL i j l l' φ φ')
  u_anticomm_e := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covU_anticomm_covE i j l l' φ φ')
  u_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covU_anticomm_covBarE i j l l' φ φ')
  baru_anticomm_baru := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarU_anticomm_covBarU i j l l' φ φ')
  baru_anticomm_Q := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarU_anticomm_covQ i j l l' φ φ')
  baru_anticomm_barQ := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarU_anticomm_covBarQ i j l l' φ φ')
  baru_anticomm_L := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarU_anticomm_covL i j l l' φ φ')
  baru_anticomm_barL := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarU_anticomm_covBarL i j l l' φ φ')
  baru_anticomm_e := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarU_anticomm_covE i j l l' φ φ')
  baru_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarU_anticomm_covBarE i j l l' φ φ')
  Q_anticomm_Q := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covQ_anticomm_covQ i j l l' φ φ')
  Q_anticomm_barQ := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covQ_anticomm_covBarQ i j l l' φ φ')
  Q_anticomm_L := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covQ_anticomm_covL i j l l' φ φ')
  Q_anticomm_barL := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covQ_anticomm_covBarL i j l l' φ φ')
  Q_anticomm_e := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covQ_anticomm_covE i j l l' φ φ')
  Q_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covQ_anticomm_covBarE i j l l' φ φ')
  barQ_anticomm_barQ := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarQ_anticomm_covBarQ i j l l' φ φ')
  barQ_anticomm_L := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarQ_anticomm_covL i j l l' φ φ')
  barQ_anticomm_barL := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarQ_anticomm_covBarL i j l l' φ φ')
  barQ_anticomm_e := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarQ_anticomm_covE i j l l' φ φ')
  barQ_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarQ_anticomm_covBarE i j l l' φ φ')
  L_anticomm_L := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covL_anticomm_covL i j l l' φ φ')
  L_anticomm_barL := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covL_anticomm_covBarL i j l l' φ φ')
  L_anticomm_e := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covL_anticomm_covE i j l l' φ φ')
  L_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covL_anticomm_covBarE i j l l' φ φ')
  barL_anticomm_barL := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarL_anticomm_covBarL i j l l' φ φ')
  barL_anticomm_e := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarL_anticomm_covE i j l l' φ φ')
  barL_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarL_anticomm_covBarE i j l l' φ φ')
  e_anticomm_e := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covE_anticomm_covE i j l l' φ φ')
  e_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covE_anticomm_covBarE i j l l' φ φ')
  bare_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    Subtype.ext (AlgebraRealization.id.covBarE_anticomm_covBarE i j l l' φ φ')

/-- The cross-sector commutation rule `F_comm_H` in the covariant jet algebra. -/
lemma F_comm_H {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) :
    Commute (fieldStrength l μ ν ψ) (higgsField l' φ) :=
  Subtype.ext (AlgebraRealization.id.covF_comm_covH l μ ν ψ l' φ)

/-- The cross-sector commutation rule `F_comm_barH` in the covariant jet algebra. -/
lemma F_comm_barH {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) :
    Commute (fieldStrength l μ ν ψ) (conjHiggsField l' φ) :=
  Subtype.ext (AlgebraRealization.id.covF_comm_covBarH l μ ν ψ l' φ)

/-- The cross-sector commutation rule `F_comm_d` in the covariant jet algebra. -/
lemma F_comm_d {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ DownSinglet) :
    Commute (fieldStrength l μ ν ψ) (downSingletField i l' φ) :=
  Subtype.ext (AlgebraRealization.id.covF_comm_covD l μ ν ψ i l' φ)

/-- The cross-sector commutation rule `F_comm_bard` in the covariant jet algebra. -/
lemma F_comm_bard {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule DownSinglet)) :
    Commute (fieldStrength l μ ν ψ) (conjDownSingletField i l' φ) :=
  Subtype.ext (AlgebraRealization.id.covF_comm_covBarD l μ ν ψ i l' φ)

/-- The cross-sector commutation rule `F_comm_u` in the covariant jet algebra. -/
lemma F_comm_u {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ UpSinglet) :
    Commute (fieldStrength l μ ν ψ) (upSingletField i l' φ) :=
  Subtype.ext (AlgebraRealization.id.covF_comm_covU l μ ν ψ i l' φ)

/-- The cross-sector commutation rule `F_comm_baru` in the covariant jet algebra. -/
lemma F_comm_baru {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule UpSinglet)) :
    Commute (fieldStrength l μ ν ψ) (conjUpSingletField i l' φ) :=
  Subtype.ext (AlgebraRealization.id.covF_comm_covBarU l μ ν ψ i l' φ)

/-- The cross-sector commutation rule `F_comm_Q` in the covariant jet algebra. -/
lemma F_comm_Q {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ QuarkDoublet) :
    Commute (fieldStrength l μ ν ψ) (quarkDoubletField i l' φ) :=
  Subtype.ext (AlgebraRealization.id.covF_comm_covQ l μ ν ψ i l' φ)

/-- The cross-sector commutation rule `F_comm_barQ` in the covariant jet algebra. -/
lemma F_comm_barQ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    Commute (fieldStrength l μ ν ψ) (conjQuarkDoubletField i l' φ) :=
  Subtype.ext (AlgebraRealization.id.covF_comm_covBarQ l μ ν ψ i l' φ)

/-- The cross-sector commutation rule `F_comm_L` in the covariant jet algebra. -/
lemma F_comm_L {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ LeptonDoublet) :
    Commute (fieldStrength l μ ν ψ) (leptonDoubletField i l' φ) :=
  Subtype.ext (AlgebraRealization.id.covF_comm_covL l μ ν ψ i l' φ)

/-- The cross-sector commutation rule `F_comm_barL` in the covariant jet algebra. -/
lemma F_comm_barL {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    Commute (fieldStrength l μ ν ψ) (conjLeptonDoubletField i l' φ) :=
  Subtype.ext (AlgebraRealization.id.covF_comm_covBarL l μ ν ψ i l' φ)

/-- The cross-sector commutation rule `F_comm_e` in the covariant jet algebra. -/
lemma F_comm_e {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ LeptonSinglet) :
    Commute (fieldStrength l μ ν ψ) (leptonSingletField i l' φ) :=
  Subtype.ext (AlgebraRealization.id.covF_comm_covE l μ ν ψ i l' φ)

/-- The cross-sector commutation rule `F_comm_bare` in the covariant jet algebra. -/
lemma F_comm_bare {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    Commute (fieldStrength l μ ν ψ) (conjLeptonSingletField i l' φ) :=
  Subtype.ext (AlgebraRealization.id.covF_comm_covBarE l μ ν ψ i l' φ)

/-- The cross-sector commutation rule `H_comm_d` in the covariant jet algebra. -/
lemma H_comm_d {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ DownSinglet) :
    Commute (higgsField l φ) (downSingletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covH_comm_covD i l l' φ φ')

/-- The cross-sector commutation rule `H_comm_bard` in the covariant jet algebra. -/
lemma H_comm_bard {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule DownSinglet)) :
    Commute (higgsField l φ) (conjDownSingletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covH_comm_covBarD i l l' φ φ')

/-- The cross-sector commutation rule `H_comm_u` in the covariant jet algebra. -/
lemma H_comm_u {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ UpSinglet) :
    Commute (higgsField l φ) (upSingletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covH_comm_covU i l l' φ φ')

/-- The cross-sector commutation rule `H_comm_baru` in the covariant jet algebra. -/
lemma H_comm_baru {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule UpSinglet)) :
    Commute (higgsField l φ) (conjUpSingletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covH_comm_covBarU i l l' φ φ')

/-- The cross-sector commutation rule `H_comm_Q` in the covariant jet algebra. -/
lemma H_comm_Q {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ QuarkDoublet) :
    Commute (higgsField l φ) (quarkDoubletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covH_comm_covQ i l l' φ φ')

/-- The cross-sector commutation rule `H_comm_barQ` in the covariant jet algebra. -/
lemma H_comm_barQ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    Commute (higgsField l φ) (conjQuarkDoubletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covH_comm_covBarQ i l l' φ φ')

/-- The cross-sector commutation rule `H_comm_L` in the covariant jet algebra. -/
lemma H_comm_L {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ LeptonDoublet) :
    Commute (higgsField l φ) (leptonDoubletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covH_comm_covL i l l' φ φ')

/-- The cross-sector commutation rule `H_comm_barL` in the covariant jet algebra. -/
lemma H_comm_barL {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    Commute (higgsField l φ) (conjLeptonDoubletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covH_comm_covBarL i l l' φ φ')

/-- The cross-sector commutation rule `H_comm_e` in the covariant jet algebra. -/
lemma H_comm_e {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ LeptonSinglet) :
    Commute (higgsField l φ) (leptonSingletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covH_comm_covE i l l' φ φ')

/-- The cross-sector commutation rule `H_comm_bare` in the covariant jet algebra. -/
lemma H_comm_bare {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    Commute (higgsField l φ) (conjLeptonSingletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covH_comm_covBarE i l l' φ φ')

/-- The cross-sector commutation rule `barH_comm_d` in the covariant jet algebra. -/
lemma barH_comm_d {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ DownSinglet) :
    Commute (conjHiggsField l φ) (downSingletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covBarH_comm_covD i l l' φ φ')

/-- The cross-sector commutation rule `barH_comm_bard` in the covariant jet algebra. -/
lemma barH_comm_bard {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule DownSinglet)) :
    Commute (conjHiggsField l φ) (conjDownSingletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covBarH_comm_covBarD i l l' φ φ')

/-- The cross-sector commutation rule `barH_comm_u` in the covariant jet algebra. -/
lemma barH_comm_u {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ UpSinglet) :
    Commute (conjHiggsField l φ) (upSingletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covBarH_comm_covU i l l' φ φ')

/-- The cross-sector commutation rule `barH_comm_baru` in the covariant jet algebra. -/
lemma barH_comm_baru {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule UpSinglet)) :
    Commute (conjHiggsField l φ) (conjUpSingletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covBarH_comm_covBarU i l l' φ φ')

/-- The cross-sector commutation rule `barH_comm_Q` in the covariant jet algebra. -/
lemma barH_comm_Q {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ QuarkDoublet) :
    Commute (conjHiggsField l φ) (quarkDoubletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covBarH_comm_covQ i l l' φ φ')

/-- The cross-sector commutation rule `barH_comm_barQ` in the covariant jet algebra. -/
lemma barH_comm_barQ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    Commute (conjHiggsField l φ) (conjQuarkDoubletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covBarH_comm_covBarQ i l l' φ φ')

/-- The cross-sector commutation rule `barH_comm_L` in the covariant jet algebra. -/
lemma barH_comm_L {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ LeptonDoublet) :
    Commute (conjHiggsField l φ) (leptonDoubletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covBarH_comm_covL i l l' φ φ')

/-- The cross-sector commutation rule `barH_comm_barL` in the covariant jet algebra. -/
lemma barH_comm_barL {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    Commute (conjHiggsField l φ) (conjLeptonDoubletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covBarH_comm_covBarL i l l' φ φ')

/-- The cross-sector commutation rule `barH_comm_e` in the covariant jet algebra. -/
lemma barH_comm_e {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ LeptonSinglet) :
    Commute (conjHiggsField l φ) (leptonSingletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covBarH_comm_covE i l l' φ φ')

/-- The cross-sector commutation rule `barH_comm_bare` in the covariant jet algebra. -/
lemma barH_comm_bare {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    Commute (conjHiggsField l φ) (conjLeptonSingletField i l' φ') :=
  Subtype.ext (AlgebraRealization.id.covBarH_comm_covBarE i l l' φ φ')

end CovJetAlgebra

end StandardModel
