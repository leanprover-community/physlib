/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import Physlib.Particles.StandardModel.AlgebraRealization.Basic
/-!
# The statistics of the Standard Model fields

## i. Overview

The thirteen families of derivative symbols of a Standard Model are the jet algebra's own
families pushed along the defining map, so their statistics are the jet algebra's own
statistics pushed along the same map. The gauge field is bosonic: its symbols commute with
each other and with every matter symbol. The Higgs symbols commute with each other and
with every fermion symbol, and the fermion symbols anticommute among themselves. Together
these fix the statistics of every symbol of the theory.

Each law is one line: the corresponding jet algebra fact, transported. A commutation
transports by `Commute.map`, an anticommutation by the private helper `map_anticomm` at
the head of the section, which is the fourth of the transport shapes of section B of
[`Basic.lean`](Basic.lean) and is needed only here. The laws carry the names they carried
when they were axioms of `AlgebraRealization`, so they are used exactly as before.

These are the last of the laws of the bare symbols; the covariant reduction that uses them
is [`CovariantDeriv.lean`](CovariantDeriv.lean).

## ii. Key results

- `AlgebraRealization.A_comm_A`, `AlgebraRealization.A_comm_H` and their companions : the
  gauge-field symbols commute with every symbol of the theory.
- `AlgebraRealization.H_comm_H` and its companions : the Higgs symbols commute with each
  other and with every fermion symbol.
- `AlgebraRealization.d_anticomm_bard` and its companions : the fermion symbols anticommute
  among themselves.

## iii. Table of contents

- A. The statistics of the fields

-/

@[expose] public section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

namespace AlgebraRealization

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repJet : Representation ℂ JetGaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : AlgebraRealization B repJet repLorentz massWeightPoly)

/-!

## A. The statistics of the fields

The gauge field is bosonic: its symbols commute with each other and with every matter
symbol. The Higgs symbols commute with each other and with every fermion symbol, and the
fermion symbols anticommute among themselves. Together these fix the statistics of every
symbol of the theory.

The commutations are the jet algebra's own, pushed along `toAlgHom` by `Commute.map`. The
anticommutations need the transport helper that opens the section: the defining map
preserves products and negation, so an anticommutation in the jet algebra is one in `B`.

-/

/-- An anticommutation transports along the defining map: the map preserves products and
  negation. -/
private lemma map_anticomm {x y : JetAlgebra} (hxy : x * y = -(y * x)) :
    h.toAlgHom x * h.toAlgHom y = -(h.toAlgHom y * h.toAlgHom x) := by
  rw [← map_mul h.toAlgHom, hxy, map_neg h.toAlgHom, map_mul h.toAlgHom]

/-- The law `A_comm_A` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma A_comm_A : ∀ (s s' : Multiset (Fin 1 ⊕ Fin 3)) (μ μ' : Fin 1 ⊕ Fin 3)
    (ψ ψ' : Module.Dual ℝ GaugeAlgebra), Commute (h.A s μ ψ) (h.A s' μ' ψ') :=
  fun s _ μ _ ψ _ => (JetAlgebra.gaugeField_commute s μ ψ _).map h.toAlgHom

/-- The law `A_comm_H` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma A_comm_H : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec),
    Commute (h.A s μ ψ) (h.H s' φ) :=
  fun s μ ψ _ _ => (JetAlgebra.gaugeField_commute s μ ψ _).map h.toAlgHom

/-- The law `A_comm_barH` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma A_comm_barH : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec)),
    Commute (h.A s μ ψ) (h.barH s' φ) :=
  fun s μ ψ _ _ => (JetAlgebra.gaugeField_commute s μ ψ _).map h.toAlgHom

/-- The law `A_comm_d` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma A_comm_d : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ DownSinglet),
    Commute (h.A s μ ψ) (h.d i s' φ) :=
  fun s μ ψ _ _ _ => (JetAlgebra.gaugeField_commute s μ ψ _).map h.toAlgHom

/-- The law `A_comm_bard` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma A_comm_bard : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule DownSinglet)),
    Commute (h.A s μ ψ) (h.bard i s' φ) :=
  fun s μ ψ _ _ _ => (JetAlgebra.gaugeField_commute s μ ψ _).map h.toAlgHom

/-- The law `A_comm_u` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma A_comm_u : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ UpSinglet),
    Commute (h.A s μ ψ) (h.u i s' φ) :=
  fun s μ ψ _ _ _ => (JetAlgebra.gaugeField_commute s μ ψ _).map h.toAlgHom

/-- The law `A_comm_baru` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma A_comm_baru : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule UpSinglet)),
    Commute (h.A s μ ψ) (h.baru i s' φ) :=
  fun s μ ψ _ _ _ => (JetAlgebra.gaugeField_commute s μ ψ _).map h.toAlgHom

/-- The law `A_comm_Q` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma A_comm_Q : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ QuarkDoublet),
    Commute (h.A s μ ψ) (h.Q i s' φ) :=
  fun s μ ψ _ _ _ => (JetAlgebra.gaugeField_commute s μ ψ _).map h.toAlgHom

/-- The law `A_comm_barQ` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma A_comm_barQ : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule QuarkDoublet)),
    Commute (h.A s μ ψ) (h.barQ i s' φ) :=
  fun s μ ψ _ _ _ => (JetAlgebra.gaugeField_commute s μ ψ _).map h.toAlgHom

/-- The law `A_comm_L` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma A_comm_L : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ LeptonDoublet),
    Commute (h.A s μ ψ) (h.L i s' φ) :=
  fun s μ ψ _ _ _ => (JetAlgebra.gaugeField_commute s μ ψ _).map h.toAlgHom

/-- The law `A_comm_barL` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma A_comm_barL : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule LeptonDoublet)),
    Commute (h.A s μ ψ) (h.barL i s' φ) :=
  fun s μ ψ _ _ _ => (JetAlgebra.gaugeField_commute s μ ψ _).map h.toAlgHom

/-- The law `A_comm_e` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma A_comm_e : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ LeptonSinglet),
    Commute (h.A s μ ψ) (h.e i s' φ) :=
  fun s μ ψ _ _ _ => (JetAlgebra.gaugeField_commute s μ ψ _).map h.toAlgHom

/-- The law `A_comm_bare` of a Standard Model, obtained from the corresponding law of the
  jet algebra by pushing it along the defining algebra map. -/
lemma A_comm_bare : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule LeptonSinglet)),
    Commute (h.A s μ ψ) (h.bare i s' φ) :=
  fun s μ ψ _ _ _ => (JetAlgebra.gaugeField_commute s μ ψ _).map h.toAlgHom

/-- The Higgs is bosonic: two Higgs symbols commute. -/
lemma H_comm_H : ∀ (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ φ' : Module.Dual ℂ HiggsVec),
    Commute (h.H s φ) (h.H s' φ') :=
  fun s s' φ φ' => ((JetAlgebra.memHiggsSector_higgsField s φ).commute
    (JetAlgebra.memHiggsSector_higgsField s' φ')).map h.toAlgHom

/-- A Higgs symbol commutes with a conjugate Higgs symbol. -/
lemma H_comm_barH : ∀ (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec)
    (φ' : Module.Dual ℂ (ConjModule HiggsVec)),
    Commute (h.H s φ) (h.barH s' φ') :=
  fun s s' φ φ' => ((JetAlgebra.memHiggsSector_higgsField s φ).commute
    (JetAlgebra.memHiggsSector_conjHiggsField s' φ')).map h.toAlgHom

/-- Two conjugate Higgs symbols commute. -/
lemma barH_comm_barH : ∀ (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ φ' : Module.Dual ℂ
    (ConjModule HiggsVec)),
    Commute (h.barH s φ) (h.barH s' φ') :=
  fun s s' φ φ' => ((JetAlgebra.memHiggsSector_conjHiggsField s φ).commute
    (JetAlgebra.memHiggsSector_conjHiggsField s' φ')).map h.toAlgHom

/-- The Higgs symbols commute with the down-type quark symbols: the Higgs is a boson, so it
  carries no statistics against the fermions. -/
lemma H_comm_d : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
    (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ DownSinglet),
    Commute (h.H s φ) (h.d i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_downSingletField i s' φ').memFermionSector).map h.toAlgHom

/-- The Higgs symbols commute with the conjugate down-type quark symbols: the Higgs is a boson, so
  it carries no statistics against the fermions. -/
lemma H_comm_bard : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
    (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule DownSinglet)),
    Commute (h.H s φ) (h.bard i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_conjDownSingletField i s' φ').memFermionSector).map h.toAlgHom

/-- The Higgs symbols commute with the up-type quark symbols: the Higgs is a boson, so it carries
  no statistics against the fermions. -/
lemma H_comm_u : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
    (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ UpSinglet),
    Commute (h.H s φ) (h.u i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_upSingletField i s' φ').memFermionSector).map h.toAlgHom

/-- The Higgs symbols commute with the conjugate up-type quark symbols: the Higgs is a boson, so
  it carries no statistics against the fermions. -/
lemma H_comm_baru : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
    (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    Commute (h.H s φ) (h.baru i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_conjUpSingletField i s' φ').memFermionSector).map h.toAlgHom

/-- The Higgs symbols commute with the quark doublet symbols: the Higgs is a boson, so it carries
  no statistics against the fermions. -/
lemma H_comm_Q : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
    (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ QuarkDoublet),
    Commute (h.H s φ) (h.Q i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_quarkDoubletField i s' φ').memFermionSector).map h.toAlgHom

/-- The Higgs symbols commute with the conjugate quark doublet symbols: the Higgs is a boson, so
  it carries no statistics against the fermions. -/
lemma H_comm_barQ : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
    (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    Commute (h.H s φ) (h.barQ i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_conjQuarkDoubletField i s' φ').memFermionSector).map h.toAlgHom

/-- The Higgs symbols commute with the lepton doublet symbols: the Higgs is a boson, so it carries
  no statistics against the fermions. -/
lemma H_comm_L : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
    (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ LeptonDoublet),
    Commute (h.H s φ) (h.L i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_leptonDoubletField i s' φ').memFermionSector).map h.toAlgHom

/-- The Higgs symbols commute with the conjugate lepton doublet symbols: the Higgs is a boson, so
  it carries no statistics against the fermions. -/
lemma H_comm_barL : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
    (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    Commute (h.H s φ) (h.barL i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_conjLeptonDoubletField i s' φ').memFermionSector).map
        h.toAlgHom

/-- The Higgs symbols commute with the lepton singlet symbols: the Higgs is a boson, so it carries
  no statistics against the fermions. -/
lemma H_comm_e : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
    (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ LeptonSinglet),
    Commute (h.H s φ) (h.e i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_leptonSingletField i s' φ').memFermionSector).map h.toAlgHom

/-- The Higgs symbols commute with the conjugate lepton singlet symbols: the Higgs is a boson, so
  it carries no statistics against the fermions. -/
lemma H_comm_bare : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
    (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    Commute (h.H s φ) (h.bare i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_conjLeptonSingletField i s' φ').memFermionSector).map
        h.toAlgHom

/-- The conjugate Higgs symbols commute with the down-type quark symbols: the Higgs is a boson, so
  it carries no statistics against the fermions. -/
lemma barH_comm_d : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
    (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ DownSinglet),
    Commute (h.barH s φ) (h.d i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_downSingletField i s' φ').memFermionSector).map h.toAlgHom

/-- The conjugate Higgs symbols commute with the conjugate down-type quark symbols: the Higgs is a
  boson, so it carries no statistics against the fermions. -/
lemma barH_comm_bard : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
    (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule DownSinglet)),
    Commute (h.barH s φ) (h.bard i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_conjDownSingletField i s' φ').memFermionSector).map h.toAlgHom

/-- The conjugate Higgs symbols commute with the up-type quark symbols: the Higgs is a boson, so
  it carries no statistics against the fermions. -/
lemma barH_comm_u : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
    (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ UpSinglet),
    Commute (h.barH s φ) (h.u i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_upSingletField i s' φ').memFermionSector).map h.toAlgHom

/-- The conjugate Higgs symbols commute with the conjugate up-type quark symbols: the Higgs is a
  boson, so it carries no statistics against the fermions. -/
lemma barH_comm_baru : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
    (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    Commute (h.barH s φ) (h.baru i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_conjUpSingletField i s' φ').memFermionSector).map h.toAlgHom

/-- The conjugate Higgs symbols commute with the quark doublet symbols: the Higgs is a boson, so
  it carries no statistics against the fermions. -/
lemma barH_comm_Q : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
    (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ QuarkDoublet),
    Commute (h.barH s φ) (h.Q i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_quarkDoubletField i s' φ').memFermionSector).map h.toAlgHom

/-- The conjugate Higgs symbols commute with the conjugate quark doublet symbols: the Higgs is a
  boson, so it carries no statistics against the fermions. -/
lemma barH_comm_barQ : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
    (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    Commute (h.barH s φ) (h.barQ i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_conjQuarkDoubletField i s' φ').memFermionSector).map h.toAlgHom

/-- The conjugate Higgs symbols commute with the lepton doublet symbols: the Higgs is a boson, so
  it carries no statistics against the fermions. -/
lemma barH_comm_L : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
    (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ LeptonDoublet),
    Commute (h.barH s φ) (h.L i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_leptonDoubletField i s' φ').memFermionSector).map h.toAlgHom

/-- The conjugate Higgs symbols commute with the conjugate lepton doublet symbols: the Higgs is a
  boson, so it carries no statistics against the fermions. -/
lemma barH_comm_barL : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
    (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    Commute (h.barH s φ) (h.barL i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_conjLeptonDoubletField i s' φ').memFermionSector).map
        h.toAlgHom

/-- The conjugate Higgs symbols commute with the lepton singlet symbols: the Higgs is a boson, so
  it carries no statistics against the fermions. -/
lemma barH_comm_e : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
    (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ LeptonSinglet),
    Commute (h.barH s φ) (h.e i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_leptonSingletField i s' φ').memFermionSector).map h.toAlgHom

/-- The conjugate Higgs symbols commute with the conjugate lepton singlet symbols: the Higgs is a
  boson, so it carries no statistics against the fermions. -/
lemma barH_comm_bare : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
    (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    Commute (h.barH s φ) (h.bare i s' φ') :=
  fun s φ i s' φ' =>
    ((JetAlgebra.memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (JetAlgebra.isFermionGenerator_conjLeptonSingletField i s' φ').memFermionSector).map
        h.toAlgHom

/-- The down-type quark symbols anticommute among themselves. -/
lemma d_anticomm_d : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ φ' : Module.Dual ℂ DownSinglet),
    h.d i s φ * h.d j s' φ' = -(h.d j s' φ' * h.d i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_downSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_downSingletField j s' φ'))

/-- The down-type quark symbols anticommute with the conjugate down-type quark symbols. -/
lemma d_anticomm_bard : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ DownSinglet) (φ' : Module.Dual ℂ (ConjModule DownSinglet)),
    h.d i s φ * h.bard j s' φ' = -(h.bard j s' φ' * h.d i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_downSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjDownSingletField j s' φ'))

/-- The down-type quark symbols anticommute with the up-type quark symbols. -/
lemma d_anticomm_u : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ DownSinglet)
    (φ' : Module.Dual ℂ UpSinglet),
    h.d i s φ * h.u j s' φ' = -(h.u j s' φ' * h.d i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_downSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_upSingletField j s' φ'))

/-- The down-type quark symbols anticommute with the conjugate up-type quark symbols. -/
lemma d_anticomm_baru : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ DownSinglet) (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    h.d i s φ * h.baru j s' φ' = -(h.baru j s' φ' * h.d i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_downSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjUpSingletField j s' φ'))

/-- The down-type quark symbols anticommute with the quark doublet symbols. -/
lemma d_anticomm_Q : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ DownSinglet)
    (φ' : Module.Dual ℂ QuarkDoublet),
    h.d i s φ * h.Q j s' φ' = -(h.Q j s' φ' * h.d i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_downSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_quarkDoubletField j s' φ'))

/-- The down-type quark symbols anticommute with the conjugate quark doublet symbols. -/
lemma d_anticomm_barQ : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ DownSinglet) (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    h.d i s φ * h.barQ j s' φ' = -(h.barQ j s' φ' * h.d i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_downSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjQuarkDoubletField j s' φ'))

/-- The down-type quark symbols anticommute with the lepton doublet symbols. -/
lemma d_anticomm_L : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ DownSinglet)
    (φ' : Module.Dual ℂ LeptonDoublet),
    h.d i s φ * h.L j s' φ' = -(h.L j s' φ' * h.d i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_downSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_leptonDoubletField j s' φ'))

/-- The down-type quark symbols anticommute with the conjugate lepton doublet symbols. -/
lemma d_anticomm_barL : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ DownSinglet) (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    h.d i s φ * h.barL j s' φ' = -(h.barL j s' φ' * h.d i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_downSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjLeptonDoubletField j s' φ'))

/-- The down-type quark symbols anticommute with the lepton singlet symbols. -/
lemma d_anticomm_e : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ DownSinglet)
    (φ' : Module.Dual ℂ LeptonSinglet),
    h.d i s φ * h.e j s' φ' = -(h.e j s' φ' * h.d i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_downSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_leptonSingletField j s' φ'))

/-- The down-type quark symbols anticommute with the conjugate lepton singlet symbols. -/
lemma d_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ DownSinglet) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    h.d i s φ * h.bare j s' φ' = -(h.bare j s' φ' * h.d i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_downSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjLeptonSingletField j s' φ'))

/-- The conjugate down-type quark symbols anticommute among themselves. -/
lemma bard_anticomm_bard : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ φ' : Module.Dual ℂ (ConjModule DownSinglet)),
    h.bard i s φ * h.bard j s' φ' = -(h.bard j s' φ' * h.bard i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjDownSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjDownSingletField j s' φ'))

/-- The conjugate down-type quark symbols anticommute with the up-type quark symbols. -/
lemma bard_anticomm_u : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule DownSinglet)) (φ' : Module.Dual ℂ UpSinglet),
    h.bard i s φ * h.u j s' φ' = -(h.u j s' φ' * h.bard i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjDownSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_upSingletField j s' φ'))

/-- The conjugate down-type quark symbols anticommute with the conjugate up-type quark symbols. -/
lemma bard_anticomm_baru : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule DownSinglet)) (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    h.bard i s φ * h.baru j s' φ' = -(h.baru j s' φ' * h.bard i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjDownSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjUpSingletField j s' φ'))

/-- The conjugate down-type quark symbols anticommute with the quark doublet symbols. -/
lemma bard_anticomm_Q : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule DownSinglet)) (φ' : Module.Dual ℂ QuarkDoublet),
    h.bard i s φ * h.Q j s' φ' = -(h.Q j s' φ' * h.bard i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjDownSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_quarkDoubletField j s' φ'))

/-- The conjugate down-type quark symbols anticommute with the conjugate quark doublet symbols. -/
lemma bard_anticomm_barQ : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule DownSinglet)) (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    h.bard i s φ * h.barQ j s' φ' = -(h.barQ j s' φ' * h.bard i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjDownSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjQuarkDoubletField j s' φ'))

/-- The conjugate down-type quark symbols anticommute with the lepton doublet symbols. -/
lemma bard_anticomm_L : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule DownSinglet)) (φ' : Module.Dual ℂ LeptonDoublet),
    h.bard i s φ * h.L j s' φ' = -(h.L j s' φ' * h.bard i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjDownSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_leptonDoubletField j s' φ'))

/-- The conjugate down-type quark symbols anticommute with the conjugate lepton doublet symbols.
  -/
lemma bard_anticomm_barL : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule DownSinglet)) (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    h.bard i s φ * h.barL j s' φ' = -(h.barL j s' φ' * h.bard i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjDownSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjLeptonDoubletField j s' φ'))

/-- The conjugate down-type quark symbols anticommute with the lepton singlet symbols. -/
lemma bard_anticomm_e : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule DownSinglet)) (φ' : Module.Dual ℂ LeptonSinglet),
    h.bard i s φ * h.e j s' φ' = -(h.e j s' φ' * h.bard i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjDownSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_leptonSingletField j s' φ'))

/-- The conjugate down-type quark symbols anticommute with the conjugate lepton singlet symbols.
  -/
lemma bard_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule DownSinglet)) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    h.bard i s φ * h.bare j s' φ' = -(h.bare j s' φ' * h.bard i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjDownSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjLeptonSingletField j s' φ'))

/-- The up-type quark symbols anticommute among themselves. -/
lemma u_anticomm_u : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ φ' : Module.Dual ℂ UpSinglet),
    h.u i s φ * h.u j s' φ' = -(h.u j s' φ' * h.u i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_upSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_upSingletField j s' φ'))

/-- The up-type quark symbols anticommute with the conjugate up-type quark symbols. -/
lemma u_anticomm_baru : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ UpSinglet)
    (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    h.u i s φ * h.baru j s' φ' = -(h.baru j s' φ' * h.u i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_upSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjUpSingletField j s' φ'))

/-- The up-type quark symbols anticommute with the quark doublet symbols. -/
lemma u_anticomm_Q : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ UpSinglet)
    (φ' : Module.Dual ℂ QuarkDoublet),
    h.u i s φ * h.Q j s' φ' = -(h.Q j s' φ' * h.u i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_upSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_quarkDoubletField j s' φ'))

/-- The up-type quark symbols anticommute with the conjugate quark doublet symbols. -/
lemma u_anticomm_barQ : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ UpSinglet)
    (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    h.u i s φ * h.barQ j s' φ' = -(h.barQ j s' φ' * h.u i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_upSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjQuarkDoubletField j s' φ'))

/-- The up-type quark symbols anticommute with the lepton doublet symbols. -/
lemma u_anticomm_L : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ UpSinglet)
    (φ' : Module.Dual ℂ LeptonDoublet),
    h.u i s φ * h.L j s' φ' = -(h.L j s' φ' * h.u i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_upSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_leptonDoubletField j s' φ'))

/-- The up-type quark symbols anticommute with the conjugate lepton doublet symbols. -/
lemma u_anticomm_barL : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ UpSinglet)
    (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    h.u i s φ * h.barL j s' φ' = -(h.barL j s' φ' * h.u i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_upSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjLeptonDoubletField j s' φ'))

/-- The up-type quark symbols anticommute with the lepton singlet symbols. -/
lemma u_anticomm_e : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ UpSinglet)
    (φ' : Module.Dual ℂ LeptonSinglet),
    h.u i s φ * h.e j s' φ' = -(h.e j s' φ' * h.u i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_upSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_leptonSingletField j s' φ'))

/-- The up-type quark symbols anticommute with the conjugate lepton singlet symbols. -/
lemma u_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ UpSinglet)
    (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    h.u i s φ * h.bare j s' φ' = -(h.bare j s' φ' * h.u i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_upSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjLeptonSingletField j s' φ'))

/-- The conjugate up-type quark symbols anticommute among themselves. -/
lemma baru_anticomm_baru : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    h.baru i s φ * h.baru j s' φ' = -(h.baru j s' φ' * h.baru i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjUpSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjUpSingletField j s' φ'))

/-- The conjugate up-type quark symbols anticommute with the quark doublet symbols. -/
lemma baru_anticomm_Q : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule UpSinglet)) (φ' : Module.Dual ℂ QuarkDoublet),
    h.baru i s φ * h.Q j s' φ' = -(h.Q j s' φ' * h.baru i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjUpSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_quarkDoubletField j s' φ'))

/-- The conjugate up-type quark symbols anticommute with the conjugate quark doublet symbols. -/
lemma baru_anticomm_barQ : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule UpSinglet)) (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    h.baru i s φ * h.barQ j s' φ' = -(h.barQ j s' φ' * h.baru i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjUpSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjQuarkDoubletField j s' φ'))

/-- The conjugate up-type quark symbols anticommute with the lepton doublet symbols. -/
lemma baru_anticomm_L : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule UpSinglet)) (φ' : Module.Dual ℂ LeptonDoublet),
    h.baru i s φ * h.L j s' φ' = -(h.L j s' φ' * h.baru i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjUpSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_leptonDoubletField j s' φ'))

/-- The conjugate up-type quark symbols anticommute with the conjugate lepton doublet symbols. -/
lemma baru_anticomm_barL : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule UpSinglet)) (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    h.baru i s φ * h.barL j s' φ' = -(h.barL j s' φ' * h.baru i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjUpSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjLeptonDoubletField j s' φ'))

/-- The conjugate up-type quark symbols anticommute with the lepton singlet symbols. -/
lemma baru_anticomm_e : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule UpSinglet)) (φ' : Module.Dual ℂ LeptonSinglet),
    h.baru i s φ * h.e j s' φ' = -(h.e j s' φ' * h.baru i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjUpSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_leptonSingletField j s' φ'))

/-- The conjugate up-type quark symbols anticommute with the conjugate lepton singlet symbols. -/
lemma baru_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule UpSinglet)) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    h.baru i s φ * h.bare j s' φ' = -(h.bare j s' φ' * h.baru i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjUpSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjLeptonSingletField j s' φ'))

/-- The quark doublet symbols anticommute among themselves. -/
lemma Q_anticomm_Q : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ φ' : Module.Dual ℂ QuarkDoublet),
    h.Q i s φ * h.Q j s' φ' = -(h.Q j s' φ' * h.Q i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_quarkDoubletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_quarkDoubletField j s' φ'))

/-- The quark doublet symbols anticommute with the conjugate quark doublet symbols. -/
lemma Q_anticomm_barQ : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ QuarkDoublet) (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    h.Q i s φ * h.barQ j s' φ' = -(h.barQ j s' φ' * h.Q i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_quarkDoubletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjQuarkDoubletField j s' φ'))

/-- The quark doublet symbols anticommute with the lepton doublet symbols. -/
lemma Q_anticomm_L : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ QuarkDoublet)
    (φ' : Module.Dual ℂ LeptonDoublet),
    h.Q i s φ * h.L j s' φ' = -(h.L j s' φ' * h.Q i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_quarkDoubletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_leptonDoubletField j s' φ'))

/-- The quark doublet symbols anticommute with the conjugate lepton doublet symbols. -/
lemma Q_anticomm_barL : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ QuarkDoublet) (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    h.Q i s φ * h.barL j s' φ' = -(h.barL j s' φ' * h.Q i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_quarkDoubletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjLeptonDoubletField j s' φ'))

/-- The quark doublet symbols anticommute with the lepton singlet symbols. -/
lemma Q_anticomm_e : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ QuarkDoublet)
    (φ' : Module.Dual ℂ LeptonSinglet),
    h.Q i s φ * h.e j s' φ' = -(h.e j s' φ' * h.Q i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_quarkDoubletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_leptonSingletField j s' φ'))

/-- The quark doublet symbols anticommute with the conjugate lepton singlet symbols. -/
lemma Q_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ QuarkDoublet) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    h.Q i s φ * h.bare j s' φ' = -(h.bare j s' φ' * h.Q i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_quarkDoubletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjLeptonSingletField j s' φ'))

/-- The conjugate quark doublet symbols anticommute among themselves. -/
lemma barQ_anticomm_barQ : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    h.barQ i s φ * h.barQ j s' φ' = -(h.barQ j s' φ' * h.barQ i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjQuarkDoubletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjQuarkDoubletField j s' φ'))

/-- The conjugate quark doublet symbols anticommute with the lepton doublet symbols. -/
lemma barQ_anticomm_L : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) (φ' : Module.Dual ℂ LeptonDoublet),
    h.barQ i s φ * h.L j s' φ' = -(h.L j s' φ' * h.barQ i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjQuarkDoubletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_leptonDoubletField j s' φ'))

/-- The conjugate quark doublet symbols anticommute with the conjugate lepton doublet symbols. -/
lemma barQ_anticomm_barL : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    h.barQ i s φ * h.barL j s' φ' = -(h.barL j s' φ' * h.barQ i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjQuarkDoubletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjLeptonDoubletField j s' φ'))

/-- The conjugate quark doublet symbols anticommute with the lepton singlet symbols. -/
lemma barQ_anticomm_e : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) (φ' : Module.Dual ℂ LeptonSinglet),
    h.barQ i s φ * h.e j s' φ' = -(h.e j s' φ' * h.barQ i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjQuarkDoubletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_leptonSingletField j s' φ'))

/-- The conjugate quark doublet symbols anticommute with the conjugate lepton singlet symbols. -/
lemma barQ_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    h.barQ i s φ * h.bare j s' φ' = -(h.bare j s' φ' * h.barQ i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjQuarkDoubletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjLeptonSingletField j s' φ'))

/-- The lepton doublet symbols anticommute among themselves. -/
lemma L_anticomm_L : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ φ' : Module.Dual ℂ LeptonDoublet),
    h.L i s φ * h.L j s' φ' = -(h.L j s' φ' * h.L i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_leptonDoubletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_leptonDoubletField j s' φ'))

/-- The lepton doublet symbols anticommute with the conjugate lepton doublet symbols. -/
lemma L_anticomm_barL : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ LeptonDoublet) (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    h.L i s φ * h.barL j s' φ' = -(h.barL j s' φ' * h.L i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_leptonDoubletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjLeptonDoubletField j s' φ'))

/-- The lepton doublet symbols anticommute with the lepton singlet symbols. -/
lemma L_anticomm_e : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ LeptonDoublet)
    (φ' : Module.Dual ℂ LeptonSinglet),
    h.L i s φ * h.e j s' φ' = -(h.e j s' φ' * h.L i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_leptonDoubletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_leptonSingletField j s' φ'))

/-- The lepton doublet symbols anticommute with the conjugate lepton singlet symbols. -/
lemma L_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ LeptonDoublet) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    h.L i s φ * h.bare j s' φ' = -(h.bare j s' φ' * h.L i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_leptonDoubletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjLeptonSingletField j s' φ'))

/-- The conjugate lepton doublet symbols anticommute among themselves. -/
lemma barL_anticomm_barL : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    h.barL i s φ * h.barL j s' φ' = -(h.barL j s' φ' * h.barL i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjLeptonDoubletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjLeptonDoubletField j s' φ'))

/-- The conjugate lepton doublet symbols anticommute with the lepton singlet symbols. -/
lemma barL_anticomm_e : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule LeptonDoublet)) (φ' : Module.Dual ℂ LeptonSinglet),
    h.barL i s φ * h.e j s' φ' = -(h.e j s' φ' * h.barL i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjLeptonDoubletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_leptonSingletField j s' φ'))

/-- The conjugate lepton doublet symbols anticommute with the conjugate lepton singlet symbols. -/
lemma barL_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule LeptonDoublet)) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet))
      ,
    h.barL i s φ * h.bare j s' φ' = -(h.bare j s' φ' * h.barL i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjLeptonDoubletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjLeptonSingletField j s' φ'))

/-- The lepton singlet symbols anticommute among themselves. -/
lemma e_anticomm_e : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ φ' : Module.Dual ℂ LeptonSinglet),
    h.e i s φ * h.e j s' φ' = -(h.e j s' φ' * h.e i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_leptonSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_leptonSingletField j s' φ'))

/-- The lepton singlet symbols anticommute with the conjugate lepton singlet symbols. -/
lemma e_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ LeptonSinglet) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    h.e i s φ * h.bare j s' φ' = -(h.bare j s' φ' * h.e i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_leptonSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjLeptonSingletField j s' φ'))

/-- The conjugate lepton singlet symbols anticommute among themselves. -/
lemma bare_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (φ φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    h.bare i s φ * h.bare j s' φ' = -(h.bare j s' φ' * h.bare i s φ) :=
  fun i j s s' φ φ' => h.map_anticomm
    ((JetAlgebra.isFermionGenerator_conjLeptonSingletField i s φ).anticomm
      (JetAlgebra.isFermionGenerator_conjLeptonSingletField j s' φ'))

end AlgebraRealization

end StandardModel
