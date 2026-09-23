/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import Physlib.Particles.StandardModel.JetAlgebra.CovJetAlgebra.Sectors
/-!
# The covariant algebra valued Standard Model

## i. Overview

An algebra `B` carries a covariant Standard Model when the covariant fields of the Standard
Model, and every polynomial expression in them, sit inside it compatibly with the global
gauge action, the Lorentz action and the mass-weight grading. The covariant jet algebra
`StandardModel.CovJetAlgebra` is the universal object with those fields, so the statement is
a single one: an algebra map `CovJetAlgebra →ₐ[ℂ] B`, equivariant for the global gauge group
and the Lorentz group and compatible with `massWeightPoly`. That is the structure
`CovAlgebraRealization`, together with the two demands that the group actions be
multiplicative on the whole of `B` and not merely on the image of the map.

It stands to the covariant theory exactly as `AlgebraRealization` stands to the structure of
bare derivative symbols it replaced. The thirteen covariant towers are derived rather than
given — section B — and every law they satisfy is the covariant jet algebra's own law pushed
along the map. Section C does that transport once for each shape a law takes, and section D
assembles them: the three sectors — gauge, Higgs and fermion — and the commutation of towers
of different sectors, which is what the classification of invariants is written in terms of.

Section E closes the circle in the other direction: a Standard Model in the bare symbols
carries a covariant one, by restricting its defining algebra map to the covariant
subalgebra.

A `CovAlgebraRealization` inherits every relation the covariant towers satisfy inside the
jet algebra — the Ricci identity relating the antisymmetric part of a second covariant
derivative to the field strength, for one. It is therefore strictly stronger than a bare
list of the sector laws.

## ii. Key results

- `StandardModel.CovAlgebraRealization` : an algebra is a covariant Standard Model when it
  receives an equivariant algebra map from the covariant jet algebra.
- `CovAlgebraRealization.id` : the covariant jet algebra is a covariant Standard Model,
  along the identity algebra map.
- `CovAlgebraRealization.F`, `CovAlgebraRealization.H` and their companions : the thirteen
  covariant towers of a covariant Standard Model.
- `CovAlgebraRealization.isHiggsSector`, `CovAlgebraRealization.isGaugeSector`,
  `CovAlgebraRealization.isFermionSector` : the three sectors of those towers.
- `CovAlgebraRealization.F_comm_H` and its companions : the towers of different sectors
  commute.
- `AlgebraRealization.toCovAlgebraRealization` : every Standard Model carries a covariant
  Standard Model.

## iii. Table of contents

- A. The identity realization
- B. The covariant fields of a covariant Standard Model
- C. Transporting a law along the defining map
- D. The sectors, the statistics and the field algebra
  - D.1. The cross-sector commutation rules
  - D.2. The field algebra
- E. Naturality of the covariant derivative
- F. Every Standard Model is a covariant Standard Model
  - F.1. The covariant towers agree

-/

@[expose] public section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

/-- The algebra `B`, with a gauge action, a Lorentz action and a mass-weight grading, is a
  covariant Standard Model when it receives an algebra map from the covariant jet algebra of
  the Standard Model which is equivariant for both actions and compatible with the grading.
  The covariant fields of the Standard Model then sit inside `B` as the images of the
  covariant jet algebra's own, and every law they satisfy there is the covariant jet
  algebra's own law pushed along the map. It is the covariant counterpart of
  `AlgebraRealization`: where that asks for an equivariant algebra map out of `JetAlgebra`,
  on which the whole jet gauge group acts, this asks for one out of `CovJetAlgebra`, on
  which only the global gauge group acts. The last two fields are not consequences of the
  first four: an equivariant map forces the two actions to be multiplicative only on its
  image, whereas the sector structures demand them multiplicative on the whole of `B`. -/
structure CovAlgebraRealization (B : Type) [Ring B] [Algebra ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (massWeightPoly : B →ₐ[ℂ] Polynomial B) where
  /-- The algebra map out of the covariant jet algebra of the Standard Model: it is what places
  the covariant fields of the Standard Model, and every polynomial expression in them,
  inside `B`. -/
  toAlgHom : CovJetAlgebra →ₐ[ℂ] B
  /-- The map is equivariant for the global gauge group: the gauge action on `B` restricts along
  it to the covariant jet algebra's own. -/
  map_repGauge : ∀ (g : GaugeGroupI) (x : CovJetAlgebra),
    toAlgHom (CovJetAlgebra.repGaugeGroupI g x) = repGauge g (toAlgHom x)
  /-- The map is equivariant for the Lorentz group: the Lorentz action on `B` restricts along it
  to the covariant jet algebra's own. -/
  map_repLorentz : ∀ (Λ : SL(2,ℂ)) (x : CovJetAlgebra),
    toAlgHom (CovJetAlgebra.repLorentzGroup Λ x) = repLorentz Λ (toAlgHom x)
  /-- The map carries the mass-weight grading of the covariant jet algebra to that of `B`: the
  mass-weight polynomial of an image is the image of the mass-weight polynomial. -/
  map_massWeight : ∀ x : CovJetAlgebra, massWeightPoly (toAlgHom x)
    = Polynomial.mapAlgHom toAlgHom (CovJetAlgebra.massWeightPoly x)
  /-- The gauge action preserves products on the whole of `B`, not merely on the image of the
  covariant jet algebra: gauge transformations act by algebra endomorphisms. -/
  repGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂
  /-- Lorentz transformations act on `B` by algebra maps: the action preserves products, so each
  `repLorentz Λ` is an algebra endomorphism of `B`. -/
  repLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂

namespace CovAlgebraRealization

/-!

## A. The identity realization

The covariant jet algebra of the Standard Model is a covariant Standard Model along the
identity algebra map, since `CovAlgebraRealization` asks precisely for an equivariant
algebra map out of it. The four compatibility laws hold by definition, and the two
multiplicativity laws are the ones the global gauge action and the Lorentz action were
shown to satisfy when they were built.

-/

/-- The covariant jet algebra of the Standard Model is a covariant Standard Model: it is one
  along the identity algebra map. -/
noncomputable def id : CovAlgebraRealization CovJetAlgebra CovJetAlgebra.repGaugeGroupI
    CovJetAlgebra.repLorentzGroup CovJetAlgebra.massWeightPoly where
  toAlgHom := AlgHom.id ℂ CovJetAlgebra
  map_repGauge _ _ := rfl
  map_repLorentz _ _ := rfl
  map_massWeight x := by
    simp [Polynomial.mapAlgHom]
  repGauge_mul := CovJetAlgebra.repGaugeGroupI_mul
  repLorentz_mul := CovJetAlgebra.repLorentzGroup_mul

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (k : CovAlgebraRealization B repGauge repLorentz massWeightPoly)

/-!

## B. The covariant fields of a covariant Standard Model

The thirteen covariant towers the theory is written in — the field strength, the Higgs
field and its conjugate, and the five fermion species in three generations with their
conjugates, each with all of its covariant derivatives — are not data of the structure.
They are the corresponding towers of the covariant jet algebra, carried into `B` along the
defining algebra map. The field-strength tower is real-linear in its value index, so the
map is restricted to `ℝ` there.

-/

/-- The covariant derivatives `∇_l F_{μν}` of the field strength inside `B`. -/
noncomputable def covF {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B :=
  k.toAlgHom.toLinearMap.restrictScalars ℝ ∘ₗ CovJetAlgebra.fieldStrength l μ ν

/-- The covariant derivatives `∇_l H` of the Higgs field inside `B`. -/
noncomputable def covH {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ HiggsVec →ₗ[ℂ] B :=
  k.toAlgHom.toLinearMap ∘ₗ CovJetAlgebra.higgsField l

/-- The covariant derivatives `∇_l H̄` of the conjugate Higgs field inside `B`. -/
noncomputable def covBarH {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B :=
  k.toAlgHom.toLinearMap ∘ₗ CovJetAlgebra.conjHiggsField l

/-- The covariant derivatives of the `i`-th generation down-type quark singlet inside `B`. -/
noncomputable def covD (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ DownSinglet →ₗ[ℂ] B :=
  k.toAlgHom.toLinearMap ∘ₗ CovJetAlgebra.downSingletField i l

/-- The covariant derivatives of the `i`-th generation conjugate down-type quark singlet
  inside `B`. -/
noncomputable def covBarD (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B :=
  k.toAlgHom.toLinearMap ∘ₗ CovJetAlgebra.conjDownSingletField i l

/-- The covariant derivatives of the `i`-th generation up-type quark singlet inside `B`. -/
noncomputable def covU (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ UpSinglet →ₗ[ℂ] B :=
  k.toAlgHom.toLinearMap ∘ₗ CovJetAlgebra.upSingletField i l

/-- The covariant derivatives of the `i`-th generation conjugate up-type quark singlet inside
  `B`. -/
noncomputable def covBarU (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B :=
  k.toAlgHom.toLinearMap ∘ₗ CovJetAlgebra.conjUpSingletField i l

/-- The covariant derivatives of the `i`-th generation quark doublet inside `B`. -/
noncomputable def covQ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B :=
  k.toAlgHom.toLinearMap ∘ₗ CovJetAlgebra.quarkDoubletField i l

/-- The covariant derivatives of the `i`-th generation conjugate quark doublet inside `B`. -/
noncomputable def covBarQ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B :=
  k.toAlgHom.toLinearMap ∘ₗ CovJetAlgebra.conjQuarkDoubletField i l

/-- The covariant derivatives of the `i`-th generation lepton doublet inside `B`. -/
noncomputable def covL (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B :=
  k.toAlgHom.toLinearMap ∘ₗ CovJetAlgebra.leptonDoubletField i l

/-- The covariant derivatives of the `i`-th generation conjugate lepton doublet inside `B`. -/
noncomputable def covBarL (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B :=
  k.toAlgHom.toLinearMap ∘ₗ CovJetAlgebra.conjLeptonDoubletField i l

/-- The covariant derivatives of the `i`-th generation charged-lepton singlet inside `B`. -/
noncomputable def covE (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B :=
  k.toAlgHom.toLinearMap ∘ₗ CovJetAlgebra.leptonSingletField i l

/-- The covariant derivatives of the `i`-th generation conjugate charged-lepton singlet inside
  `B`. -/
noncomputable def covBarE (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B :=
  k.toAlgHom.toLinearMap ∘ₗ CovJetAlgebra.conjLeptonSingletField i l

/-!

## C. Transporting a law along the defining map

Every law of the covariant jet algebra becomes a law of `B` when pushed along the defining
algebra map. The transport is the same in each of the shapes the laws take, so each shape
is done once: a gauge law, a commutation law, an anticommutation law, an antisymmetry, a
mass-weight eigenvalue equation and a Lorentz slot-mixing sum. Commutation needs no lemma
of its own — it is `Commute.map`.

-/

/-- A gauge transformation law transports along the defining map: the map is equivariant for
  the global gauge group. -/
lemma map_repGauge_eq {g : GaugeGroupI} {x y : CovJetAlgebra}
    (hxy : CovJetAlgebra.repGaugeGroupI g x = y) :
    repGauge g (k.toAlgHom x) = k.toAlgHom y :=
  (k.map_repGauge g x).symm.trans (congrArg k.toAlgHom hxy)

/-- An anticommutation law transports along the defining map: the map preserves products and
  negation. -/
lemma map_anticomm {x y : CovJetAlgebra} (hxy : x * y = -(y * x)) :
    k.toAlgHom x * k.toAlgHom y = -(k.toAlgHom y * k.toAlgHom x) :=
  (map_mul k.toAlgHom x y).symm.trans
    ((congrArg k.toAlgHom hxy).trans
      ((map_neg k.toAlgHom _).trans
        (congrArg Neg.neg (map_mul k.toAlgHom y x))))

/-- An antisymmetry transports along the defining map: the map preserves negation. -/
lemma map_neg_eq {x y : CovJetAlgebra} (hxy : x = -y) :
    k.toAlgHom x = -k.toAlgHom y :=
  (congrArg k.toAlgHom hxy).trans (map_neg k.toAlgHom y)

/-- A mass-weight eigenvalue equation transports along the defining map: the map carries the
  grading of the covariant jet algebra to that of `B`. -/
lemma map_massWeight_monomial {n : ℕ} {x : CovJetAlgebra}
    (hx : CovJetAlgebra.massWeightPoly x = Polynomial.monomial n x) :
    massWeightPoly (k.toAlgHom x) = Polynomial.monomial n (k.toAlgHom x) :=
  (k.map_massWeight x).trans
    ((congrArg (Polynomial.mapAlgHom k.toAlgHom) hx).trans
      (Polynomial.mapAlgHom_monomial k.toAlgHom n x))

/-- A Lorentz transformation law of a covariant tower transports along the defining map: the
  slot mixing is a finite sum of scalar multiples, and the map is linear and equivariant. -/
lemma map_lorentz {V : Type} [AddCommGroup V] [Module ℂ V]
    {rep : Representation ℂ SL(2,ℂ) V}
    {G : {n : ℕ} → (Fin n → (Fin 1 ⊕ Fin 3)) → Module.Dual ℂ V →ₗ[ℂ] CovJetAlgebra}
    (hG : IsLorentzCovDerivTransforms CovJetAlgebra.repLorentzGroup rep G) :
    IsLorentzCovDerivTransforms repLorentz rep
    (fun {_n} l => k.toAlgHom.toLinearMap ∘ₗ G l) := by
  intro Λ n l φ
  show repLorentz Λ (k.toAlgHom (G l φ)) = _
  exact (k.map_repLorentz Λ (G l φ)).symm.trans
    ((congrArg k.toAlgHom (hG Λ n l φ)).trans
      ((map_sum k.toAlgHom _ _).trans
        (Finset.sum_congr rfl fun p _ => map_smul k.toAlgHom _ _)))

/-!

## D. The sectors, the statistics and the field algebra

The covariant form of the theory splits into three sectors — gauge, Higgs and fermion —
and the towers of different sectors commute. Those are the results the classification of
invariants is written in terms of, and this section makes them available by dot notation on
a covariant Standard Model, each one the covariant jet algebra's own law pushed along the
defining map. The field algebra the
covariant towers generate is here too, together with the centrality of the bosonic towers
inside it.

-/

/-- The Higgs sector of a covariant Standard Model: the defining map restricted to the
  covariant jet algebra of the Higgs field. -/
noncomputable def isHiggsSector :
    HiggsAlgebraCovRealization B repGauge repLorentz massWeightPoly where
  toAlgHom := k.toAlgHom.comp CovJetAlgebra.higgsSubalgebra.val
  map_rep g x := k.map_repGauge g (x : CovJetAlgebra)
  map_repLorentz Λ x := k.map_repLorentz Λ (x : CovJetAlgebra)
  map_massWeight x := by
    show massWeightPoly (k.toAlgHom (x : CovJetAlgebra)) = _
    refine (k.map_massWeight (x : CovJetAlgebra)).trans ?_
    refine (congrArg (Polynomial.mapAlgHom k.toAlgHom)
      (Subalgebra.mapAlgHom_polyRestrict
        CovJetAlgebra.massWeightPoly_mem_polyRange x).symm).trans ?_
    exact AlgHom.congr_fun (Polynomial.mapAlgHom_comp _ k.toAlgHom
      CovJetAlgebra.higgsSubalgebra.val) _
  rep_mul := k.repGauge_mul
  repLorentz_mul := k.repLorentz_mul

/-- The Higgs towers of the Higgs sector of a covariant Standard Model are its own. -/
@[simp]
lemma isHiggsSector_covH (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    k.isHiggsSector.covH n l = k.covH l := rfl

/-- The conjugate Higgs towers of the Higgs sector of a covariant Standard Model are its
  own. -/
@[simp]
lemma isHiggsSector_covBarH (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    k.isHiggsSector.covBarH n l = k.covBarH l := rfl

/-- The gauge sector of a covariant Standard Model. -/
theorem isGaugeSector : IsGaugeSector B repGauge k.repGauge_mul repLorentz k.repLorentz_mul
    (fun {_n} l μ ν => k.covF l μ ν) massWeightPoly where
  repGauge_F := fun g {_n} l μ ν φ =>
    k.map_repGauge_eq (CovJetAlgebra.isGaugeSector.repGauge_F g l μ ν φ)
  repLorentz_F := fun Λ n l μ ν φ => by
    show repLorentz Λ (k.toAlgHom (CovJetAlgebra.fieldStrength l μ ν φ)) = _
    refine (k.map_repLorentz Λ _).symm.trans ?_
    refine (congrArg k.toAlgHom
      (CovJetAlgebra.isGaugeSector.repLorentz_F Λ n l μ ν φ)).trans ?_
    refine (map_sum k.toAlgHom _ _).trans (Finset.sum_congr rfl fun p _ => ?_)
    refine (map_smul k.toAlgHom _ _).trans (congrArg _ ?_)
    refine (map_sum k.toAlgHom _ _).trans (Finset.sum_congr rfl fun a _ => ?_)
    refine (map_smul k.toAlgHom _ _).trans (congrArg _ ?_)
    exact (map_sum k.toAlgHom _ _).trans
      (Finset.sum_congr rfl fun b _ => map_smul k.toAlgHom _ _)
  massWeight_F := fun {_n} l μ ν φ =>
    k.map_massWeight_monomial (CovJetAlgebra.isGaugeSector.massWeight_F l μ ν φ)
  F_comm_F := fun {_n _m} l μ ν ψ l' μ' ν' ψ' =>
    (CovJetAlgebra.isGaugeSector.F_comm_F l μ ν ψ l' μ' ν' ψ').map k.toAlgHom
  F_antisymm := fun {_n} l μ ν φ =>
    k.map_neg_eq (CovJetAlgebra.isGaugeSector.F_antisymm l μ ν φ)

/-- The fermion sector of a covariant Standard Model. -/
theorem isFermionSector : IsFermionSector B repGauge k.repGauge_mul repLorentz k.repLorentz_mul
    (fun {_n} i l => k.covD i l) (fun {_n} i l => k.covBarD i l)
    (fun {_n} i l => k.covU i l) (fun {_n} i l => k.covBarU i l)
    (fun {_n} i l => k.covQ i l) (fun {_n} i l => k.covBarQ i l)
    (fun {_n} i l => k.covL i l) (fun {_n} i l => k.covBarL i l)
    (fun {_n} i l => k.covE i l) (fun {_n} i l => k.covBarE i l) massWeightPoly where
  repGauge_d := fun g i {_n} l φ =>
    k.map_repGauge_eq (CovJetAlgebra.isFermionSector.repGauge_d g i l φ)
  repGauge_bard := fun g i {_n} l φ =>
    k.map_repGauge_eq (CovJetAlgebra.isFermionSector.repGauge_bard g i l φ)
  repGauge_u := fun g i {_n} l φ =>
    k.map_repGauge_eq (CovJetAlgebra.isFermionSector.repGauge_u g i l φ)
  repGauge_baru := fun g i {_n} l φ =>
    k.map_repGauge_eq (CovJetAlgebra.isFermionSector.repGauge_baru g i l φ)
  repGauge_Q := fun g i {_n} l φ =>
    k.map_repGauge_eq (CovJetAlgebra.isFermionSector.repGauge_Q g i l φ)
  repGauge_barQ := fun g i {_n} l φ =>
    k.map_repGauge_eq (CovJetAlgebra.isFermionSector.repGauge_barQ g i l φ)
  repGauge_L := fun g i {_n} l φ =>
    k.map_repGauge_eq (CovJetAlgebra.isFermionSector.repGauge_L g i l φ)
  repGauge_barL := fun g i {_n} l φ =>
    k.map_repGauge_eq (CovJetAlgebra.isFermionSector.repGauge_barL g i l φ)
  repGauge_e := fun g i {_n} l φ =>
    k.map_repGauge_eq (CovJetAlgebra.isFermionSector.repGauge_e g i l φ)
  repGauge_bare := fun g i {_n} l φ =>
    k.map_repGauge_eq (CovJetAlgebra.isFermionSector.repGauge_bare g i l φ)
  repLorentz_d := fun i => k.map_lorentz (CovJetAlgebra.isFermionSector.repLorentz_d i)
  repLorentz_bard := fun i =>
    k.map_lorentz (CovJetAlgebra.isFermionSector.repLorentz_bard i)
  repLorentz_u := fun i => k.map_lorentz (CovJetAlgebra.isFermionSector.repLorentz_u i)
  repLorentz_baru := fun i =>
    k.map_lorentz (CovJetAlgebra.isFermionSector.repLorentz_baru i)
  repLorentz_Q := fun i => k.map_lorentz (CovJetAlgebra.isFermionSector.repLorentz_Q i)
  repLorentz_barQ := fun i =>
    k.map_lorentz (CovJetAlgebra.isFermionSector.repLorentz_barQ i)
  repLorentz_L := fun i => k.map_lorentz (CovJetAlgebra.isFermionSector.repLorentz_L i)
  repLorentz_barL := fun i =>
    k.map_lorentz (CovJetAlgebra.isFermionSector.repLorentz_barL i)
  repLorentz_e := fun i => k.map_lorentz (CovJetAlgebra.isFermionSector.repLorentz_e i)
  repLorentz_bare := fun i =>
    k.map_lorentz (CovJetAlgebra.isFermionSector.repLorentz_bare i)
  massWeight_d := fun i {_n} l φ =>
    k.map_massWeight_monomial (CovJetAlgebra.isFermionSector.massWeight_d i l φ)
  massWeight_bard := fun i {_n} l φ =>
    k.map_massWeight_monomial (CovJetAlgebra.isFermionSector.massWeight_bard i l φ)
  massWeight_u := fun i {_n} l φ =>
    k.map_massWeight_monomial (CovJetAlgebra.isFermionSector.massWeight_u i l φ)
  massWeight_baru := fun i {_n} l φ =>
    k.map_massWeight_monomial (CovJetAlgebra.isFermionSector.massWeight_baru i l φ)
  massWeight_Q := fun i {_n} l φ =>
    k.map_massWeight_monomial (CovJetAlgebra.isFermionSector.massWeight_Q i l φ)
  massWeight_barQ := fun i {_n} l φ =>
    k.map_massWeight_monomial (CovJetAlgebra.isFermionSector.massWeight_barQ i l φ)
  massWeight_L := fun i {_n} l φ =>
    k.map_massWeight_monomial (CovJetAlgebra.isFermionSector.massWeight_L i l φ)
  massWeight_barL := fun i {_n} l φ =>
    k.map_massWeight_monomial (CovJetAlgebra.isFermionSector.massWeight_barL i l φ)
  massWeight_e := fun i {_n} l φ =>
    k.map_massWeight_monomial (CovJetAlgebra.isFermionSector.massWeight_e i l φ)
  massWeight_bare := fun i {_n} l φ =>
    k.map_massWeight_monomial (CovJetAlgebra.isFermionSector.massWeight_bare i l φ)
  d_anticomm_d := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.d_anticomm_d i j l l' φ φ')
  d_anticomm_bard := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.d_anticomm_bard i j l l' φ φ')
  d_anticomm_u := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.d_anticomm_u i j l l' φ φ')
  d_anticomm_baru := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.d_anticomm_baru i j l l' φ φ')
  d_anticomm_Q := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.d_anticomm_Q i j l l' φ φ')
  d_anticomm_barQ := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.d_anticomm_barQ i j l l' φ φ')
  d_anticomm_L := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.d_anticomm_L i j l l' φ φ')
  d_anticomm_barL := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.d_anticomm_barL i j l l' φ φ')
  d_anticomm_e := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.d_anticomm_e i j l l' φ φ')
  d_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.d_anticomm_bare i j l l' φ φ')
  bard_anticomm_bard := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.bard_anticomm_bard i j l l' φ φ')
  bard_anticomm_u := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.bard_anticomm_u i j l l' φ φ')
  bard_anticomm_baru := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.bard_anticomm_baru i j l l' φ φ')
  bard_anticomm_Q := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.bard_anticomm_Q i j l l' φ φ')
  bard_anticomm_barQ := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.bard_anticomm_barQ i j l l' φ φ')
  bard_anticomm_L := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.bard_anticomm_L i j l l' φ φ')
  bard_anticomm_barL := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.bard_anticomm_barL i j l l' φ φ')
  bard_anticomm_e := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.bard_anticomm_e i j l l' φ φ')
  bard_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.bard_anticomm_bare i j l l' φ φ')
  u_anticomm_u := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.u_anticomm_u i j l l' φ φ')
  u_anticomm_baru := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.u_anticomm_baru i j l l' φ φ')
  u_anticomm_Q := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.u_anticomm_Q i j l l' φ φ')
  u_anticomm_barQ := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.u_anticomm_barQ i j l l' φ φ')
  u_anticomm_L := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.u_anticomm_L i j l l' φ φ')
  u_anticomm_barL := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.u_anticomm_barL i j l l' φ φ')
  u_anticomm_e := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.u_anticomm_e i j l l' φ φ')
  u_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.u_anticomm_bare i j l l' φ φ')
  baru_anticomm_baru := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.baru_anticomm_baru i j l l' φ φ')
  baru_anticomm_Q := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.baru_anticomm_Q i j l l' φ φ')
  baru_anticomm_barQ := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.baru_anticomm_barQ i j l l' φ φ')
  baru_anticomm_L := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.baru_anticomm_L i j l l' φ φ')
  baru_anticomm_barL := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.baru_anticomm_barL i j l l' φ φ')
  baru_anticomm_e := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.baru_anticomm_e i j l l' φ φ')
  baru_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.baru_anticomm_bare i j l l' φ φ')
  Q_anticomm_Q := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.Q_anticomm_Q i j l l' φ φ')
  Q_anticomm_barQ := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.Q_anticomm_barQ i j l l' φ φ')
  Q_anticomm_L := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.Q_anticomm_L i j l l' φ φ')
  Q_anticomm_barL := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.Q_anticomm_barL i j l l' φ φ')
  Q_anticomm_e := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.Q_anticomm_e i j l l' φ φ')
  Q_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.Q_anticomm_bare i j l l' φ φ')
  barQ_anticomm_barQ := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.barQ_anticomm_barQ i j l l' φ φ')
  barQ_anticomm_L := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.barQ_anticomm_L i j l l' φ φ')
  barQ_anticomm_barL := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.barQ_anticomm_barL i j l l' φ φ')
  barQ_anticomm_e := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.barQ_anticomm_e i j l l' φ φ')
  barQ_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.barQ_anticomm_bare i j l l' φ φ')
  L_anticomm_L := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.L_anticomm_L i j l l' φ φ')
  L_anticomm_barL := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.L_anticomm_barL i j l l' φ φ')
  L_anticomm_e := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.L_anticomm_e i j l l' φ φ')
  L_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.L_anticomm_bare i j l l' φ φ')
  barL_anticomm_barL := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.barL_anticomm_barL i j l l' φ φ')
  barL_anticomm_e := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.barL_anticomm_e i j l l' φ φ')
  barL_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.barL_anticomm_bare i j l l' φ φ')
  e_anticomm_e := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.e_anticomm_e i j l l' φ φ')
  e_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.e_anticomm_bare i j l l' φ φ')
  bare_anticomm_bare := fun i j {_n _m} l l' φ φ' =>
    k.map_anticomm (CovJetAlgebra.isFermionSector.bare_anticomm_bare i j l l' φ φ')

include k in
/-- The gauge action fixes the unit of the algebra: it is multiplicative, and every element of
  the group is invertible. -/
lemma repGauge_one (g : GaugeGroupI) : repGauge g (1 : B) = 1 := by
  obtain ⟨v, hv⟩ : ∃ v, repGauge g v = 1 :=
    ⟨repGauge g⁻¹ 1, by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one repGauge,
        Module.End.one_apply]⟩
  have h1 := k.repGauge_mul g v 1
  rw [mul_one, hv, one_mul] at h1
  exact h1.symm

include k in
/-- The Lorentz action fixes the unit of the algebra. -/
lemma repLorentz_one (Λ : SL(2,ℂ)) : repLorentz Λ (1 : B) = 1 := by
  obtain ⟨v, hv⟩ : ∃ v, repLorentz Λ v = 1 :=
    ⟨repLorentz Λ⁻¹ 1, by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one repLorentz,
        Module.End.one_apply]⟩
  have h1 := k.repLorentz_mul Λ v 1
  rw [mul_one, hv, one_mul] at h1
  exact h1.symm

/-!

### D.1. The cross-sector commutation rules

-/

/-- The cross-sector commutation rule `F_comm_H` of a covariant Standard Model. -/
lemma F_comm_H {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) :
    Commute (k.covF l μ ν ψ) (k.covH l' φ) :=
  (CovJetAlgebra.F_comm_H l μ ν ψ l' φ).map k.toAlgHom

/-- The cross-sector commutation rule `F_comm_barH` of a covariant Standard Model. -/
lemma F_comm_barH {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) :
    Commute (k.covF l μ ν ψ) (k.covBarH l' φ) :=
  (CovJetAlgebra.F_comm_barH l μ ν ψ l' φ).map k.toAlgHom

/-- The cross-sector commutation rule `F_comm_d` of a covariant Standard Model. -/
lemma F_comm_d {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ DownSinglet) :
    Commute (k.covF l μ ν ψ) (k.covD i l' φ) :=
  (CovJetAlgebra.F_comm_d l μ ν ψ i l' φ).map k.toAlgHom

/-- The cross-sector commutation rule `F_comm_bard` of a covariant Standard Model. -/
lemma F_comm_bard {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule DownSinglet)) :
    Commute (k.covF l μ ν ψ) (k.covBarD i l' φ) :=
  (CovJetAlgebra.F_comm_bard l μ ν ψ i l' φ).map k.toAlgHom

/-- The cross-sector commutation rule `F_comm_u` of a covariant Standard Model. -/
lemma F_comm_u {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ UpSinglet) :
    Commute (k.covF l μ ν ψ) (k.covU i l' φ) :=
  (CovJetAlgebra.F_comm_u l μ ν ψ i l' φ).map k.toAlgHom

/-- The cross-sector commutation rule `F_comm_baru` of a covariant Standard Model. -/
lemma F_comm_baru {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule UpSinglet)) :
    Commute (k.covF l μ ν ψ) (k.covBarU i l' φ) :=
  (CovJetAlgebra.F_comm_baru l μ ν ψ i l' φ).map k.toAlgHom

/-- The cross-sector commutation rule `F_comm_Q` of a covariant Standard Model. -/
lemma F_comm_Q {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ QuarkDoublet) :
    Commute (k.covF l μ ν ψ) (k.covQ i l' φ) :=
  (CovJetAlgebra.F_comm_Q l μ ν ψ i l' φ).map k.toAlgHom

/-- The cross-sector commutation rule `F_comm_barQ` of a covariant Standard Model. -/
lemma F_comm_barQ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    Commute (k.covF l μ ν ψ) (k.covBarQ i l' φ) :=
  (CovJetAlgebra.F_comm_barQ l μ ν ψ i l' φ).map k.toAlgHom

/-- The cross-sector commutation rule `F_comm_L` of a covariant Standard Model. -/
lemma F_comm_L {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ LeptonDoublet) :
    Commute (k.covF l μ ν ψ) (k.covL i l' φ) :=
  (CovJetAlgebra.F_comm_L l μ ν ψ i l' φ).map k.toAlgHom

/-- The cross-sector commutation rule `F_comm_barL` of a covariant Standard Model. -/
lemma F_comm_barL {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    Commute (k.covF l μ ν ψ) (k.covBarL i l' φ) :=
  (CovJetAlgebra.F_comm_barL l μ ν ψ i l' φ).map k.toAlgHom

/-- The cross-sector commutation rule `F_comm_e` of a covariant Standard Model. -/
lemma F_comm_e {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ LeptonSinglet) :
    Commute (k.covF l μ ν ψ) (k.covE i l' φ) :=
  (CovJetAlgebra.F_comm_e l μ ν ψ i l' φ).map k.toAlgHom

/-- The cross-sector commutation rule `F_comm_bare` of a covariant Standard Model. -/
lemma F_comm_bare {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    Commute (k.covF l μ ν ψ) (k.covBarE i l' φ) :=
  (CovJetAlgebra.F_comm_bare l μ ν ψ i l' φ).map k.toAlgHom

/-- The cross-sector commutation rule `H_comm_d` of a covariant Standard Model. -/
lemma H_comm_d {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ DownSinglet) :
    Commute (k.covH l φ) (k.covD i l' φ') :=
  (CovJetAlgebra.H_comm_d l φ i l' φ').map k.toAlgHom

/-- The cross-sector commutation rule `H_comm_bard` of a covariant Standard Model. -/
lemma H_comm_bard {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule DownSinglet)) :
    Commute (k.covH l φ) (k.covBarD i l' φ') :=
  (CovJetAlgebra.H_comm_bard l φ i l' φ').map k.toAlgHom

/-- The cross-sector commutation rule `H_comm_u` of a covariant Standard Model. -/
lemma H_comm_u {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ UpSinglet) :
    Commute (k.covH l φ) (k.covU i l' φ') :=
  (CovJetAlgebra.H_comm_u l φ i l' φ').map k.toAlgHom

/-- The cross-sector commutation rule `H_comm_baru` of a covariant Standard Model. -/
lemma H_comm_baru {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule UpSinglet)) :
    Commute (k.covH l φ) (k.covBarU i l' φ') :=
  (CovJetAlgebra.H_comm_baru l φ i l' φ').map k.toAlgHom

/-- The cross-sector commutation rule `H_comm_Q` of a covariant Standard Model. -/
lemma H_comm_Q {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ QuarkDoublet) :
    Commute (k.covH l φ) (k.covQ i l' φ') :=
  (CovJetAlgebra.H_comm_Q l φ i l' φ').map k.toAlgHom

/-- The cross-sector commutation rule `H_comm_barQ` of a covariant Standard Model. -/
lemma H_comm_barQ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    Commute (k.covH l φ) (k.covBarQ i l' φ') :=
  (CovJetAlgebra.H_comm_barQ l φ i l' φ').map k.toAlgHom

/-- The cross-sector commutation rule `H_comm_L` of a covariant Standard Model. -/
lemma H_comm_L {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ LeptonDoublet) :
    Commute (k.covH l φ) (k.covL i l' φ') :=
  (CovJetAlgebra.H_comm_L l φ i l' φ').map k.toAlgHom

/-- The cross-sector commutation rule `H_comm_barL` of a covariant Standard Model. -/
lemma H_comm_barL {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    Commute (k.covH l φ) (k.covBarL i l' φ') :=
  (CovJetAlgebra.H_comm_barL l φ i l' φ').map k.toAlgHom

/-- The cross-sector commutation rule `H_comm_e` of a covariant Standard Model. -/
lemma H_comm_e {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ LeptonSinglet) :
    Commute (k.covH l φ) (k.covE i l' φ') :=
  (CovJetAlgebra.H_comm_e l φ i l' φ').map k.toAlgHom

/-- The cross-sector commutation rule `H_comm_bare` of a covariant Standard Model. -/
lemma H_comm_bare {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    Commute (k.covH l φ) (k.covBarE i l' φ') :=
  (CovJetAlgebra.H_comm_bare l φ i l' φ').map k.toAlgHom

/-- The cross-sector commutation rule `barH_comm_d` of a covariant Standard Model. -/
lemma barH_comm_d {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ DownSinglet) :
    Commute (k.covBarH l φ) (k.covD i l' φ') :=
  (CovJetAlgebra.barH_comm_d l φ i l' φ').map k.toAlgHom

/-- The cross-sector commutation rule `barH_comm_bard` of a covariant Standard Model. -/
lemma barH_comm_bard {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule DownSinglet)) :
    Commute (k.covBarH l φ) (k.covBarD i l' φ') :=
  (CovJetAlgebra.barH_comm_bard l φ i l' φ').map k.toAlgHom

/-- The cross-sector commutation rule `barH_comm_u` of a covariant Standard Model. -/
lemma barH_comm_u {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ UpSinglet) :
    Commute (k.covBarH l φ) (k.covU i l' φ') :=
  (CovJetAlgebra.barH_comm_u l φ i l' φ').map k.toAlgHom

/-- The cross-sector commutation rule `barH_comm_baru` of a covariant Standard Model. -/
lemma barH_comm_baru {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule UpSinglet)) :
    Commute (k.covBarH l φ) (k.covBarU i l' φ') :=
  (CovJetAlgebra.barH_comm_baru l φ i l' φ').map k.toAlgHom

/-- The cross-sector commutation rule `barH_comm_Q` of a covariant Standard Model. -/
lemma barH_comm_Q {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ QuarkDoublet) :
    Commute (k.covBarH l φ) (k.covQ i l' φ') :=
  (CovJetAlgebra.barH_comm_Q l φ i l' φ').map k.toAlgHom

/-- The cross-sector commutation rule `barH_comm_barQ` of a covariant Standard Model. -/
lemma barH_comm_barQ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)) :
    Commute (k.covBarH l φ) (k.covBarQ i l' φ') :=
  (CovJetAlgebra.barH_comm_barQ l φ i l' φ').map k.toAlgHom

/-- The cross-sector commutation rule `barH_comm_L` of a covariant Standard Model. -/
lemma barH_comm_L {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ LeptonDoublet) :
    Commute (k.covBarH l φ) (k.covL i l' φ') :=
  (CovJetAlgebra.barH_comm_L l φ i l' φ').map k.toAlgHom

/-- The cross-sector commutation rule `barH_comm_barL` of a covariant Standard Model. -/
lemma barH_comm_barL {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)) :
    Commute (k.covBarH l φ) (k.covBarL i l' φ') :=
  (CovJetAlgebra.barH_comm_barL l φ i l' φ').map k.toAlgHom

/-- The cross-sector commutation rule `barH_comm_e` of a covariant Standard Model. -/
lemma barH_comm_e {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ LeptonSinglet) :
    Commute (k.covBarH l φ) (k.covE i l' φ') :=
  (CovJetAlgebra.barH_comm_e l φ i l' φ').map k.toAlgHom

/-- The cross-sector commutation rule `barH_comm_bare` of a covariant Standard Model. -/
lemma barH_comm_bare {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)) :
    Commute (k.covBarH l φ) (k.covBarE i l' φ') :=
  (CovJetAlgebra.barH_comm_bare l φ i l' φ').map k.toAlgHom

/-!

### D.2. The field algebra

-/

/-- The algebra generated by all the covariant fields of a covariant Standard Model: the
  covariant-derivative towers of the field strength, of the Higgs and its conjugate, and of
  the three families of each fermion species with their conjugates. -/
def fieldAlgebra : Subalgebra ℂ B :=
  Algebra.adjoin ℂ
    ((⋃ (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
        Set.range (k.covF l μ ν)) ∪
      (⋃ (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3), Set.range (k.covH l) ∪ Set.range (k.covBarH l)) ∪
      (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3),
        Set.range (k.covD i l) ∪ Set.range (k.covBarD i l) ∪
        Set.range (k.covU i l) ∪ Set.range (k.covBarU i l) ∪
        Set.range (k.covQ i l) ∪ Set.range (k.covBarQ i l) ∪
        Set.range (k.covL i l) ∪ Set.range (k.covBarL i l) ∪
        Set.range (k.covE i l) ∪ Set.range (k.covBarE i l)))

lemma F_commute_mem_fieldAlgebra {n : ℕ} {l : Fin n → Fin 1 ⊕ Fin 3} {μ ν : Fin 1 ⊕ Fin 3}
    (φ : Module.Dual ℝ GaugeAlgebra) (x : B) (hx : x ∈ k.fieldAlgebra) :
    k.covF l μ ν φ * x = x * k.covF l μ ν φ := by
  rw [fieldAlgebra] at hx
  refine (GaugeAlgebraRealization.commute_of_mem_adjoin (y := k.covF l μ ν φ) ?_ hx).symm
  intro z hz
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at hz
  obtain ((⟨n', l', μ', ν', ψ, rfl⟩ | ⟨n', l', ⟨φ', rfl⟩ | ⟨φ', rfl⟩⟩) | ⟨i, n', l', hz⟩) := hz
  · exact (k.isGaugeSector.F_comm_F l μ ν φ l' μ' ν' ψ).symm
  · exact (k.F_comm_H l μ ν φ l' φ').symm
  · exact (k.F_comm_barH l μ ν φ l' φ').symm
  · obtain (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
      ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) := hz
    · exact (k.F_comm_d l μ ν φ i l' φ').symm
    · exact (k.F_comm_bard l μ ν φ i l' φ').symm
    · exact (k.F_comm_u l μ ν φ i l' φ').symm
    · exact (k.F_comm_baru l μ ν φ i l' φ').symm
    · exact (k.F_comm_Q l μ ν φ i l' φ').symm
    · exact (k.F_comm_barQ l μ ν φ i l' φ').symm
    · exact (k.F_comm_L l μ ν φ i l' φ').symm
    · exact (k.F_comm_barL l μ ν φ i l' φ').symm
    · exact (k.F_comm_e l μ ν φ i l' φ').symm
    · exact (k.F_comm_bare l μ ν φ i l' φ').symm

lemma H_commute_mem_fieldAlgebra {n : ℕ} {l : Fin n → Fin 1 ⊕ Fin 3}
    (φ : Module.Dual ℂ HiggsVec) (x : B) (hx : x ∈ k.fieldAlgebra) :
    k.covH l φ * x = x * k.covH l φ := by
  rw [fieldAlgebra] at hx
  refine (GaugeAlgebraRealization.commute_of_mem_adjoin (y := k.covH l φ) ?_ hx).symm
  intro z hz
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at hz
  obtain ((⟨n', l', μ', ν', ψ, rfl⟩ | ⟨n', l', ⟨φ', rfl⟩ | ⟨φ', rfl⟩⟩) | ⟨i, n', l', hz⟩) := hz
  · exact k.F_comm_H l' μ' ν' ψ l φ
  · exact k.isHiggsSector.H_comm_H φ' φ _ _ l' l
  · exact (k.isHiggsSector.H_comm_barH φ φ' _ _ l l').symm
  · obtain (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
      ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) := hz
    · exact (k.H_comm_d l φ i l' φ').symm
    · exact (k.H_comm_bard l φ i l' φ').symm
    · exact (k.H_comm_u l φ i l' φ').symm
    · exact (k.H_comm_baru l φ i l' φ').symm
    · exact (k.H_comm_Q l φ i l' φ').symm
    · exact (k.H_comm_barQ l φ i l' φ').symm
    · exact (k.H_comm_L l φ i l' φ').symm
    · exact (k.H_comm_barL l φ i l' φ').symm
    · exact (k.H_comm_e l φ i l' φ').symm
    · exact (k.H_comm_bare l φ i l' φ').symm

lemma barH_commute_mem_fieldAlgebra {n : ℕ} {l : Fin n → Fin 1 ⊕ Fin 3}
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (x : B) (hx : x ∈ k.fieldAlgebra) :
    k.covBarH l φ * x = x * k.covBarH l φ := by
  rw [fieldAlgebra] at hx
  refine (GaugeAlgebraRealization.commute_of_mem_adjoin (y := k.covBarH l φ) ?_ hx).symm
  intro z hz
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at hz
  obtain ((⟨n', l', μ', ν', ψ, rfl⟩ | ⟨n', l', ⟨φ', rfl⟩ | ⟨φ', rfl⟩⟩) | ⟨i, n', l', hz⟩) := hz
  · exact k.F_comm_barH l' μ' ν' ψ l φ
  · exact k.isHiggsSector.H_comm_barH φ' φ _ _ l' l
  · exact k.isHiggsSector.barH_comm_barH φ' φ _ _ l' l
  · obtain (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
      ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) := hz
    · exact (k.barH_comm_d l φ i l' φ').symm
    · exact (k.barH_comm_bard l φ i l' φ').symm
    · exact (k.barH_comm_u l φ i l' φ').symm
    · exact (k.barH_comm_baru l φ i l' φ').symm
    · exact (k.barH_comm_Q l φ i l' φ').symm
    · exact (k.barH_comm_barQ l φ i l' φ').symm
    · exact (k.barH_comm_L l φ i l' φ').symm
    · exact (k.barH_comm_barL l φ i l' φ').symm
    · exact (k.barH_comm_e l φ i l' φ').symm
    · exact (k.barH_comm_bare l φ i l' φ').symm

end CovAlgebraRealization

/-!

## E. Naturality of the covariant derivative

A covariant tower is built from the bare families by two operations only: the pairing of an
adjoint family against a matter one (`GaugeAlgebraRealization.actionFam`), and the bracket of two
adjoint families (`GaugeAlgebraRealization.bracketFam`). Each expands, in bases of the gauge algebra
and of the value space, as a finite double sum of scalar multiples of products of
components, so each commutes with an algebra map. The whole recursion therefore does, and
that is the content of this section: the covariant towers of a Standard Model are the jet
algebra's own covariant towers pushed along the defining map.

-/

namespace GaugeAlgebraRealization

open _root_.GaugeAlgebraRealization

variable {B B' : Type} [Ring B] [Algebra ℂ B] [Ring B'] [Algebra ℂ B']
  {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

/-- Composing an adjoint-indexed family with an algebra map. -/
noncomputable abbrev mapAdj (Φ : B →ₐ[ℂ] B')
    (f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B' :=
  Φ.toLinearMap.restrictScalars ℝ ∘ₗ f

/-- An algebra map over `ℂ` is real-linear. -/
lemma map_real_smul (Φ : B →ₐ[ℂ] B') (r : ℝ) (b : B) : Φ (r • b) = r • Φ b :=
  (Φ.toLinearMap.restrictScalars ℝ).map_smul r b

/-- The action pairing commutes with an algebra map: it is a finite double sum of scalar
  multiples of products of components. -/
lemma actionFam_map (Φ : B →ₐ[ℂ] B') (act : GaugeAlgebra →ₗ[ℝ] V →ₗ[ℂ] V)
    (f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B) (g : Module.Dual ℂ V →ₗ[ℂ] B)
    (φ : Module.Dual ℂ V) :
    Φ (actionFam act f g φ) = actionFam act (mapAdj Φ f) (Φ.toLinearMap ∘ₗ g) φ := by
  rw [actionFam, actionFam,
    dualPairEquiv_symm_eq_sum (Module.finBasis ℝ GaugeAlgebra) f,
    dualPairEquivC_symm_eq_sum (Module.finBasis ℂ V) g,
    dualPairEquiv_symm_eq_sum (Module.finBasis ℝ GaugeAlgebra) (mapAdj Φ f),
    dualPairEquivC_symm_eq_sum (Module.finBasis ℂ V) (Φ.toLinearMap ∘ₗ g)]
  simp only [map_sum, LinearMap.sum_apply, tensorAction_tmul, dualPairEquivC_tmul,
    map_smul, map_mul, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply]

/-- The bracket of two adjoint families commutes with an algebra map. -/
lemma bracketFam_map (Φ : B →ₐ[ℂ] B') (f g : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    Φ (bracketFam f g φ) = bracketFam (mapAdj Φ f) (mapAdj Φ g) φ := by
  rw [bracketFam, bracketFam,
    dualPairEquiv_symm_eq_sum (Module.finBasis ℝ GaugeAlgebra) f,
    dualPairEquiv_symm_eq_sum (Module.finBasis ℝ GaugeAlgebra) g,
    dualPairEquiv_symm_eq_sum (Module.finBasis ℝ GaugeAlgebra) (mapAdj Φ f),
    dualPairEquiv_symm_eq_sum (Module.finBasis ℝ GaugeAlgebra) (mapAdj Φ g)]
  simp only [map_sum, LinearMap.sum_apply, tensorBracket_tmul, dualPairEquiv_tmul,
    map_real_smul, map_mul, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply]

variable {act : GaugeAlgebra →ₗ[ℝ] V →ₗ[ℂ] V}
  {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
  {A' : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B'}

/-- The action pairing of two families related by an algebra map is the pairing of the images. -/
lemma actionFam_map' (Φ : B →ₐ[ℂ] B')
    {f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B} {f' : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B'}
    (hf : ∀ ψ, Φ (f ψ) = f' ψ)
    {g : Module.Dual ℂ V →ₗ[ℂ] B} {g' : Module.Dual ℂ V →ₗ[ℂ] B'} (hg : ∀ χ, Φ (g χ) = g' χ)
    (φ : Module.Dual ℂ V) :
    Φ (actionFam act f g φ) = actionFam act f' g' φ := by
  rw [actionFam_map Φ act f g φ, show mapAdj Φ f = f' from LinearMap.ext hf,
    show Φ.toLinearMap ∘ₗ g = g' from LinearMap.ext hg]

/-- The bracket of two adjoint families related by an algebra map is the bracket of the
  images. -/
lemma bracketFam_map' (Φ : B →ₐ[ℂ] B')
    {f : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B} {f' : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B'}
    (hf : ∀ ψ, Φ (f ψ) = f' ψ)
    {g : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B} {g' : Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B'}
    (hg : ∀ ψ, Φ (g ψ) = g' ψ) (φ : Module.Dual ℝ GaugeAlgebra) :
    Φ (bracketFam f g φ) = bracketFam f' g' φ := by
  rw [bracketFam_map Φ f g φ, show mapAdj Φ f = f' from LinearMap.ext hf,
    show mapAdj Φ g = g' from LinearMap.ext hg]

/-- The derived action family commutes with an algebra map. -/
lemma actionFamConv_map' (Φ : B →ₐ[ℂ] B') (hA : ∀ p ρ ψ, Φ (A p ρ ψ) = A' p ρ ψ)
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B}
    {F' : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B'}
    (hF : ∀ s χ, Φ (F s χ) = F' s χ) (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ V) :
    Φ (actionFamConv A act ρ F s φ) = actionFamConv A' act ρ F' s φ := by
  rw [actionFamConv, actionFamConv, Multiset.sum_linearMap_apply, Multiset.sum_linearMap_apply,
    Multiset.map_map, Multiset.map_map, map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  exact actionFam_map' Φ (hA p.1 ρ) (hF p.2) φ

/-- The derived bracket family commutes with an algebra map. -/
lemma bracketFamConv_map' (Φ : B →ₐ[ℂ] B') (hA : ∀ p ρ ψ, Φ (A p ρ ψ) = A' p ρ ψ)
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
    {F' : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B'}
    (hF : ∀ s χ, Φ (F s χ) = F' s χ) (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℝ GaugeAlgebra) :
    Φ (bracketFamConv A ρ F s φ) = bracketFamConv A' ρ F' s φ := by
  rw [bracketFamConv, bracketFamConv, Multiset.sum_linearMap_apply,
    Multiset.sum_linearMap_apply, Multiset.map_map, Multiset.map_map, map_multiset_sum,
    Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  exact bracketFam_map' Φ (hA p.1 ρ) (hF p.2) φ

/-- The derived commutator family commutes with an algebra map. -/
lemma commutatorFam_map' (Φ : B →ₐ[ℂ] B') (hA : ∀ p ρ ψ, Φ (A p ρ ψ) = A' p ρ ψ)
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ GaugeAlgebra) :
    Φ (commutatorFam A μ ν s φ) = commutatorFam A' μ ν s φ := by
  rw [commutatorFam, commutatorFam, Multiset.sum_linearMap_apply,
    Multiset.sum_linearMap_apply, Multiset.map_map, Multiset.map_map, map_multiset_sum,
    Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  exact bracketFam_map' Φ (hA p.1 μ) (hA p.2 ν) φ

/-- The field strength commutes with an algebra map. -/
lemma fieldStrength_map' (Φ : B →ₐ[ℂ] B') (hA : ∀ p ρ ψ, Φ (A p ρ ψ) = A' p ρ ψ)
    (μ ν : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℝ GaugeAlgebra) :
    Φ (fieldStrength A μ ν s φ) = fieldStrength A' μ ν s φ := by
  rw [fieldStrength_apply, fieldStrength_apply, map_add, map_sub, hA, hA,
    commutatorFam_map' Φ hA]

/-- The covariant derivative of a matter family commutes with an algebra map. -/
lemma covDerivAction_map' (Φ : B →ₐ[ℂ] B') (hA : ∀ p ρ ψ, Φ (A p ρ ψ) = A' p ρ ψ)
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B}
    {F' : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B'}
    (hF : ∀ s χ, Φ (F s χ) = F' s χ) (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ V) :
    Φ (covDerivAction A act F ρ s φ) = covDerivAction A' act F' ρ s φ := by
  rw [covDerivAction_apply, covDerivAction_apply, map_add, hF, actionFamConv_map' Φ hA hF]

/-- The covariant derivative of an adjoint family commutes with an algebra map. -/
lemma covDerivAdjoint_map' (Φ : B →ₐ[ℂ] B') (hA : ∀ p ρ ψ, Φ (A p ρ ψ) = A' p ρ ψ)
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
    {F' : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B'}
    (hF : ∀ s χ, Φ (F s χ) = F' s χ) (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℝ GaugeAlgebra) :
    Φ (covDerivAdjoint A F ρ s φ) = covDerivAdjoint A' F' ρ s φ := by
  rw [covDerivAdjoint_apply, covDerivAdjoint_apply, map_add, hF, bracketFamConv_map' Φ hA hF]

/-- The iterated covariant derivative of a matter family commutes with an algebra map. -/
lemma covDerivIter_map' (Φ : B →ₐ[ℂ] B') (hA : ∀ p ρ ψ, Φ (A p ρ ψ) = A' p ρ ψ)
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B}
    {F' : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B'}
    (hF : ∀ s χ, Φ (F s χ) = F' s χ) :
    ∀ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ V),
      Φ (covDerivIter A act F n l s φ) = covDerivIter A' act F' n l s φ
  | 0, _, s, φ => hF s φ
  | n + 1, l, s, φ =>
    covDerivAction_map' Φ hA
    (fun s' χ => covDerivIter_map' Φ hA hF n (fun i => l i.succ) s' χ) (l 0) s φ

/-- The iterated covariant derivative of an adjoint family commutes with an algebra map. -/
lemma iteratedCovDerivAdjoint_map' (Φ : B →ₐ[ℂ] B') (hA : ∀ p ρ ψ, Φ (A p ρ ψ) = A' p ρ ψ)
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
    {F' : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B'}
    (hF : ∀ s χ, Φ (F s χ) = F' s χ) :
    ∀ (l : List (Fin 1 ⊕ Fin 3)) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℝ GaugeAlgebra),
      Φ (iteratedCovDerivAdjoint A l F s φ) = iteratedCovDerivAdjoint A' l F' s φ
  | [], s, φ => hF s φ
  | ρ :: l, s, φ =>
    covDerivAdjoint_map' Φ hA
    (fun s' χ => iteratedCovDerivAdjoint_map' Φ hA hF l s' χ) ρ s φ

end GaugeAlgebraRealization

/-!

## F. Every Standard Model is a covariant Standard Model

A Standard Model in the bare symbols carries one in the covariant towers: its defining
algebra map out of the jet algebra restricts to the covariant field algebra, and the
restriction is equivariant for the global gauge group and the Lorentz group and compatible
with the mass-weight grading, because the unrestricted map is. The thirteen covariant
towers of the resulting covariant Standard Model are, on the nose, the covariant towers of
`AlgebraRealization.CovStandardModel`.

-/

namespace AlgebraRealization

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repJet : Representation ℂ JetGaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : AlgebraRealization B repJet repLorentz massWeightPoly)

/-- A Standard Model is a covariant Standard Model, for the global gauge group: the defining
  algebra map out of the jet algebra, restricted to the covariant jet algebra. -/
noncomputable def toCovAlgebraRealization :
    CovAlgebraRealization B (repGlobal repJet) repLorentz massWeightPoly where
  toAlgHom := h.toAlgHom.comp AlgebraRealization.id.covAlgebra.val
  map_repGauge g x := h.map_repJet (JetGaugeGroupI.ofConstant g) (x : JetAlgebra)
  map_repLorentz Λ x := h.map_repLorentz Λ (x : JetAlgebra)
  map_massWeight x := by
    show massWeightPoly (h.toAlgHom (x : JetAlgebra)) = _
    refine (h.map_massWeight (x : JetAlgebra)).trans ?_
    refine (congrArg (Polynomial.mapAlgHom h.toAlgHom)
      (AlgebraRealization.id.mapAlgHom_covMassWeightPoly x).symm).trans ?_
    exact AlgHom.congr_fun
      (Polynomial.mapAlgHom_comp _ h.toAlgHom AlgebraRealization.id.covAlgebra.val) _
  repGauge_mul := h.repGlobal_mul
  repLorentz_mul := h.repLorentz_mul

/-!

### F.1. The covariant towers agree

-/

/-- The defining map of a Standard Model carries the jet algebra's gauge-field symbols to its
  own: both are the jet algebra's, one of them pushed forward. -/
lemma toAlgHom_id_A (p : Multiset (Fin 1 ⊕ Fin 3)) (ρ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) :
    h.toAlgHom (AlgebraRealization.id.A p ρ ψ) = h.A p ρ ψ := rfl

/-- The field-strength tower of the covariant Standard Model carried by a Standard Model is
  its own field-strength tower. -/
@[simp]
lemma toCovAlgebraRealization_covF {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) :
    h.toCovAlgebraRealization.covF l μ ν = h.covF l μ ν := by
  refine LinearMap.ext fun φ => ?_
  have hb : h.toCovAlgebraRealization.covF l μ ν φ
      = h.toAlgHom (AlgebraRealization.id.covF l μ ν φ) := rfl
  rw [hb]
  exact GaugeAlgebraRealization.iteratedCovDerivAdjoint_map' h.toAlgHom h.toAlgHom_id_A
    (F := GaugeAlgebraRealization.fieldStrength AlgebraRealization.id.A μ ν)
    (F' := GaugeAlgebraRealization.fieldStrength h.A μ ν)
    (fun s χ => GaugeAlgebraRealization.fieldStrength_map' (A := AlgebraRealization.id.A)
      (A' := h.A) h.toAlgHom h.toAlgHom_id_A μ ν s χ)
    (List.ofFn l) 0 φ

/-- The higgs tower of the covariant Standard Model carried by a Standard Model is its own. -/
@[simp]
lemma toCovAlgebraRealization_covH {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    h.toCovAlgebraRealization.covH l = h.covDerivH l := by
  refine LinearMap.ext fun φ => ?_
  have hb : h.toCovAlgebraRealization.covH l φ
      = h.toAlgHom (AlgebraRealization.id.covDerivH l φ) := rfl
  rw [hb]
  exact GaugeAlgebraRealization.covDerivIter_map' h.toAlgHom h.toAlgHom_id_A
    (F := AlgebraRealization.id.H ) (F' := h.H ) (fun s χ => rfl) n l 0 φ

/-- The conjugate higgs tower of the covariant Standard Model carried by a Standard Model is
  its own. -/
@[simp]
lemma toCovAlgebraRealization_covBarH {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    h.toCovAlgebraRealization.covBarH l = h.covDerivBarH l := by
  refine LinearMap.ext fun φ => ?_
  have hb : h.toCovAlgebraRealization.covBarH l φ
      = h.toAlgHom (AlgebraRealization.id.covDerivBarH l φ) := rfl
  rw [hb]
  exact GaugeAlgebraRealization.covDerivIter_map' h.toAlgHom h.toAlgHom_id_A
    (F := AlgebraRealization.id.barH ) (F' := h.barH ) (fun s χ => rfl) n l 0 φ

/-- The down-type quark tower of the covariant Standard Model carried by a Standard Model is
  its own. -/
@[simp]
lemma toCovAlgebraRealization_covD (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    h.toCovAlgebraRealization.covD i l = h.covDerivD i l := by
  refine LinearMap.ext fun φ => ?_
  have hb : h.toCovAlgebraRealization.covD i l φ
      = h.toAlgHom (AlgebraRealization.id.covDerivD i l φ) := rfl
  rw [hb]
  exact GaugeAlgebraRealization.covDerivIter_map' h.toAlgHom h.toAlgHom_id_A
    (F := AlgebraRealization.id.d i ) (F' := h.d i ) (fun s χ => rfl) n l 0 φ

/-- The conjugate down-type quark tower of the covariant Standard Model carried by a Standard
  Model is its own. -/
@[simp]
lemma toCovAlgebraRealization_covBarD (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    h.toCovAlgebraRealization.covBarD i l = h.covDerivBarD i l := by
  refine LinearMap.ext fun φ => ?_
  have hb : h.toCovAlgebraRealization.covBarD i l φ
      = h.toAlgHom (AlgebraRealization.id.covDerivBarD i l φ) := rfl
  rw [hb]
  exact GaugeAlgebraRealization.covDerivIter_map' h.toAlgHom h.toAlgHom_id_A
    (F := AlgebraRealization.id.bard i ) (F' := h.bard i ) (fun s χ => rfl) n l 0 φ

/-- The up-type quark tower of the covariant Standard Model carried by a Standard Model is its
  own. -/
@[simp]
lemma toCovAlgebraRealization_covU (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    h.toCovAlgebraRealization.covU i l = h.covDerivU i l := by
  refine LinearMap.ext fun φ => ?_
  have hb : h.toCovAlgebraRealization.covU i l φ
      = h.toAlgHom (AlgebraRealization.id.covDerivU i l φ) := rfl
  rw [hb]
  exact GaugeAlgebraRealization.covDerivIter_map' h.toAlgHom h.toAlgHom_id_A
    (F := AlgebraRealization.id.u i ) (F' := h.u i ) (fun s χ => rfl) n l 0 φ

/-- The conjugate up-type quark tower of the covariant Standard Model carried by a Standard
  Model is its own. -/
@[simp]
lemma toCovAlgebraRealization_covBarU (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    h.toCovAlgebraRealization.covBarU i l = h.covDerivBarU i l := by
  refine LinearMap.ext fun φ => ?_
  have hb : h.toCovAlgebraRealization.covBarU i l φ
      = h.toAlgHom (AlgebraRealization.id.covDerivBarU i l φ) := rfl
  rw [hb]
  exact GaugeAlgebraRealization.covDerivIter_map' h.toAlgHom h.toAlgHom_id_A
    (F := AlgebraRealization.id.baru i ) (F' := h.baru i ) (fun s χ => rfl) n l 0 φ

/-- The quark doublet tower of the covariant Standard Model carried by a Standard Model is its
  own. -/
@[simp]
lemma toCovAlgebraRealization_covQ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    h.toCovAlgebraRealization.covQ i l = h.covDerivQ i l := by
  refine LinearMap.ext fun φ => ?_
  have hb : h.toCovAlgebraRealization.covQ i l φ
      = h.toAlgHom (AlgebraRealization.id.covDerivQ i l φ) := rfl
  rw [hb]
  exact GaugeAlgebraRealization.covDerivIter_map' h.toAlgHom h.toAlgHom_id_A
    (F := AlgebraRealization.id.Q i ) (F' := h.Q i ) (fun s χ => rfl) n l 0 φ

/-- The conjugate quark doublet tower of the covariant Standard Model carried by a Standard
  Model is its own. -/
@[simp]
lemma toCovAlgebraRealization_covBarQ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    h.toCovAlgebraRealization.covBarQ i l = h.covDerivBarQ i l := by
  refine LinearMap.ext fun φ => ?_
  have hb : h.toCovAlgebraRealization.covBarQ i l φ
      = h.toAlgHom (AlgebraRealization.id.covDerivBarQ i l φ) := rfl
  rw [hb]
  exact GaugeAlgebraRealization.covDerivIter_map' h.toAlgHom h.toAlgHom_id_A
    (F := AlgebraRealization.id.barQ i ) (F' := h.barQ i ) (fun s χ => rfl) n l 0 φ

/-- The lepton doublet tower of the covariant Standard Model carried by a Standard Model is
  its own. -/
@[simp]
lemma toCovAlgebraRealization_covL (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    h.toCovAlgebraRealization.covL i l = h.covDerivL i l := by
  refine LinearMap.ext fun φ => ?_
  have hb : h.toCovAlgebraRealization.covL i l φ
      = h.toAlgHom (AlgebraRealization.id.covDerivL i l φ) := rfl
  rw [hb]
  exact GaugeAlgebraRealization.covDerivIter_map' h.toAlgHom h.toAlgHom_id_A
    (F := AlgebraRealization.id.L i ) (F' := h.L i ) (fun s χ => rfl) n l 0 φ

/-- The conjugate lepton doublet tower of the covariant Standard Model carried by a Standard
  Model is its own. -/
@[simp]
lemma toCovAlgebraRealization_covBarL (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    h.toCovAlgebraRealization.covBarL i l = h.covDerivBarL i l := by
  refine LinearMap.ext fun φ => ?_
  have hb : h.toCovAlgebraRealization.covBarL i l φ
      = h.toAlgHom (AlgebraRealization.id.covDerivBarL i l φ) := rfl
  rw [hb]
  exact GaugeAlgebraRealization.covDerivIter_map' h.toAlgHom h.toAlgHom_id_A
    (F := AlgebraRealization.id.barL i ) (F' := h.barL i ) (fun s χ => rfl) n l 0 φ

/-- The charged-lepton singlet tower of the covariant Standard Model carried by a Standard
  Model is its own. -/
@[simp]
lemma toCovAlgebraRealization_covE (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    h.toCovAlgebraRealization.covE i l = h.covDerivE i l := by
  refine LinearMap.ext fun φ => ?_
  have hb : h.toCovAlgebraRealization.covE i l φ
      = h.toAlgHom (AlgebraRealization.id.covDerivE i l φ) := rfl
  rw [hb]
  exact GaugeAlgebraRealization.covDerivIter_map' h.toAlgHom h.toAlgHom_id_A
    (F := AlgebraRealization.id.e i ) (F' := h.e i ) (fun s χ => rfl) n l 0 φ

/-- The conjugate charged-lepton singlet tower of the covariant Standard Model carried by a
  Standard Model is its own. -/
@[simp]
lemma toCovAlgebraRealization_covBarE (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    h.toCovAlgebraRealization.covBarE i l = h.covDerivBarE i l := by
  refine LinearMap.ext fun φ => ?_
  have hb : h.toCovAlgebraRealization.covBarE i l φ
      = h.toAlgHom (AlgebraRealization.id.covDerivBarE i l φ) := rfl
  rw [hb]
  exact GaugeAlgebraRealization.covDerivIter_map' h.toAlgHom h.toAlgHom_id_A
    (F := AlgebraRealization.id.bare i ) (F' := h.bare i ) (fun s χ => rfl) n l 0 φ

end AlgebraRealization


end StandardModel
