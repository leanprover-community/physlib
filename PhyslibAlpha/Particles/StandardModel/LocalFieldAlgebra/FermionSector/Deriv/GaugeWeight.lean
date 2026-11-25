/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.FermionSector.Basic
/-!
# The gauge weight decomposition of the fermion sector

The fermion derivative submodules decompose by gauge weight, with the weights of the ten species.

## i. Overview

The gauge torus acts diagonally on the basis of each fermion value space, with
weights given by the colour and isospin weights of the fundamental representations
and the species' hypercharge. Through the dual (and, for the barred species, the
conjugate-dual) this makes every symbol component a simultaneous eigenvector, and the
derivative submodules of the fermion sector decompose by gauge weight
(`derivSubmoduleGaugeWeight`), for every number of covariant derivatives.

## ii. Key results

- `derivSubmoduleGaugeWeight` : the gauge weight decomposition of the fermion derivative submodules,
  for any number of covariant derivatives.
- `derivSubmoduleGaugeWeight_supp` : its support, the gauge weights of the ten species.

## iii. Table of contents

- A. The gauge weight decomposition of the derivative submodules
- B. The support of the decomposition

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups

/-!

## A. The gauge weight decomposition of the derivative submodules

-/

namespace FermionSector

/-- The gauge torus acts diagonally on the `d` symbol components. -/
lemma repGauge_gaugeTorusGen_d (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen i) (d f l ((DownSinglet.basis).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (-(DownSinglet.valueGaugeWeight j)) i) • d f l
        ((DownSinglet.basis).coord j) := by
  rw [repGauge_d, DownSinglet.repGaugeGroupI_dual_gaugeTorusGen_coord, map_smul,
    GaugeWeight.coord_neg]

/-- The gauge torus acts diagonally on the `bard` symbol components. -/
lemma repGauge_gaugeTorusGen_bard (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen i) (bard f l (((Basis.conj DownSinglet.basis)).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (DownSinglet.valueGaugeWeight j) i) • bard f l
        (((Basis.conj DownSinglet.basis)).coord j) := by
  rw [repGauge_bard, DownSinglet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord, map_smul]

/-- The gauge torus acts diagonally on the `u` symbol components. -/
lemma repGauge_gaugeTorusGen_u (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen i) (u f l ((UpSinglet.basis).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (-(UpSinglet.valueGaugeWeight j)) i) • u f l
        ((UpSinglet.basis).coord j) := by
  rw [repGauge_u, UpSinglet.repGaugeGroupI_dual_gaugeTorusGen_coord, map_smul,
    GaugeWeight.coord_neg]

/-- The gauge torus acts diagonally on the `baru` symbol components. -/
lemma repGauge_gaugeTorusGen_baru (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen i) (baru f l (((Basis.conj UpSinglet.basis)).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (UpSinglet.valueGaugeWeight j) i) • baru f l
        (((Basis.conj UpSinglet.basis)).coord j) := by
  rw [repGauge_baru, UpSinglet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord, map_smul]

/-- The gauge torus acts diagonally on the `Q` symbol components. -/
lemma repGauge_gaugeTorusGen_Q (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3 × Fin 2) :
    repGauge (gaugeTorusGen i) (Q f l ((QuarkDoublet.basis).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (-(QuarkDoublet.valueGaugeWeight j)) i) • Q f l
        ((QuarkDoublet.basis).coord j) := by
  rw [repGauge_Q, QuarkDoublet.repGaugeGroupI_dual_gaugeTorusGen_coord, map_smul,
    GaugeWeight.coord_neg]

/-- The gauge torus acts diagonally on the `barQ` symbol components. -/
lemma repGauge_gaugeTorusGen_barQ (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3 × Fin 2) :
    repGauge (gaugeTorusGen i) (barQ f l (((Basis.conj QuarkDoublet.basis)).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (QuarkDoublet.valueGaugeWeight j) i) • barQ f l
        (((Basis.conj QuarkDoublet.basis)).coord j) := by
  rw [repGauge_barQ, QuarkDoublet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord, map_smul]

/-- The gauge torus acts diagonally on the `L` symbol components. -/
lemma repGauge_gaugeTorusGen_L (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge (gaugeTorusGen i) (L f l ((LeptonDoubletV.basis).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (-(LeptonDoubletV.valueGaugeWeight j)) i) • L f l
        ((LeptonDoubletV.basis).coord j) := by
  rw [repGauge_L, LeptonDoubletV.repGaugeGroupI_dual_gaugeTorusGen_coord, map_smul,
    GaugeWeight.coord_neg]

/-- The gauge torus acts diagonally on the `barL` symbol components. -/
lemma repGauge_gaugeTorusGen_barL (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge (gaugeTorusGen i) (barL f l (((Basis.conj LeptonDoubletV.basis)).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonDoubletV.valueGaugeWeight j) i) • barL f l
        (((Basis.conj LeptonDoubletV.basis)).coord j) := by
  rw [repGauge_barL, LeptonDoubletV.repGaugeGroupI_conj_dual_gaugeTorusGen_coord, map_smul]

/-- The gauge torus acts diagonally on the `e` symbol components. -/
lemma repGauge_gaugeTorusGen_e (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2) :
    repGauge (gaugeTorusGen i) (e f l ((LeptonSinglet.basis).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (-(LeptonSinglet.valueGaugeWeight j)) i) • e f l
        ((LeptonSinglet.basis).coord j) := by
  rw [repGauge_e, LeptonSinglet.repGaugeGroupI_dual_gaugeTorusGen_coord, map_smul,
    GaugeWeight.coord_neg]

/-- The gauge torus acts diagonally on the `bare` symbol components. -/
lemma repGauge_gaugeTorusGen_bare (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2) :
    repGauge (gaugeTorusGen i) (bare f l (((Basis.conj LeptonSinglet.basis)).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonSinglet.valueGaugeWeight j) i) • bare f l
        (((Basis.conj LeptonSinglet.basis)).coord j) := by
  rw [repGauge_bare, LeptonSinglet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord, map_smul]

/-- The gauge weight decomposition of the range of the `d` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeightD (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (d f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup repGauge_mul fun j : Fin 2 × Fin 3 =>
      GaugeWeightDecomposition.spanSingleton repGauge_mul _ (-(DownSinglet.valueGaugeWeight j))
        (fun i => repGauge_gaugeTorusGen_d i f l j))
    _ (LinearMap.range_eq_iSup_span_coord (DownSinglet.basis) (d f l))

/-- The gauge weight decomposition of the range of the `bard` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeightBarD (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (bard f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup repGauge_mul fun j : Fin 2 × Fin 3 =>
      GaugeWeightDecomposition.spanSingleton repGauge_mul _ (DownSinglet.valueGaugeWeight j)
        (fun i => repGauge_gaugeTorusGen_bard i f l j))
    _ (LinearMap.range_eq_iSup_span_coord ((Basis.conj DownSinglet.basis)) (bard f l))

/-- The gauge weight decomposition of the range of the `u` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeightU (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (u f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup repGauge_mul fun j : Fin 2 × Fin 3 =>
      GaugeWeightDecomposition.spanSingleton repGauge_mul _ (-(UpSinglet.valueGaugeWeight j))
        (fun i => repGauge_gaugeTorusGen_u i f l j))
    _ (LinearMap.range_eq_iSup_span_coord (UpSinglet.basis) (u f l))

/-- The gauge weight decomposition of the range of the `baru` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeightBarU (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (baru f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup repGauge_mul fun j : Fin 2 × Fin 3 =>
      GaugeWeightDecomposition.spanSingleton repGauge_mul _ (UpSinglet.valueGaugeWeight j)
        (fun i => repGauge_gaugeTorusGen_baru i f l j))
    _ (LinearMap.range_eq_iSup_span_coord ((Basis.conj UpSinglet.basis)) (baru f l))

/-- The gauge weight decomposition of the range of the `Q` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeightQ (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (Q f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup repGauge_mul fun j : Fin 2 × Fin 3 × Fin 2 =>
      GaugeWeightDecomposition.spanSingleton repGauge_mul _ (-(QuarkDoublet.valueGaugeWeight j))
        (fun i => repGauge_gaugeTorusGen_Q i f l j))
    _ (LinearMap.range_eq_iSup_span_coord (QuarkDoublet.basis) (Q f l))

/-- The gauge weight decomposition of the range of the `barQ` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeightBarQ (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (barQ f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup repGauge_mul fun j : Fin 2 × Fin 3 × Fin 2 =>
      GaugeWeightDecomposition.spanSingleton repGauge_mul _ (QuarkDoublet.valueGaugeWeight j)
        (fun i => repGauge_gaugeTorusGen_barQ i f l j))
    _ (LinearMap.range_eq_iSup_span_coord ((Basis.conj QuarkDoublet.basis)) (barQ f l))

/-- The gauge weight decomposition of the range of the `L` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeightL (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (L f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup repGauge_mul fun j : Fin 2 × Fin 2 =>
      GaugeWeightDecomposition.spanSingleton repGauge_mul _ (-(LeptonDoubletV.valueGaugeWeight j))
        (fun i => repGauge_gaugeTorusGen_L i f l j))
    _ (LinearMap.range_eq_iSup_span_coord (LeptonDoubletV.basis) (L f l))

/-- The gauge weight decomposition of the range of the `barL` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeightBarL (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (barL f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup repGauge_mul fun j : Fin 2 × Fin 2 =>
      GaugeWeightDecomposition.spanSingleton repGauge_mul _ (LeptonDoubletV.valueGaugeWeight j)
        (fun i => repGauge_gaugeTorusGen_barL i f l j))
    _ (LinearMap.range_eq_iSup_span_coord ((Basis.conj LeptonDoubletV.basis)) (barL f l))

/-- The gauge weight decomposition of the range of the `e` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeightE (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (e f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup repGauge_mul fun j : Fin 2 =>
      GaugeWeightDecomposition.spanSingleton repGauge_mul _ (-(LeptonSinglet.valueGaugeWeight j))
        (fun i => repGauge_gaugeTorusGen_e i f l j))
    _ (LinearMap.range_eq_iSup_span_coord (LeptonSinglet.basis) (e f l))

/-- The gauge weight decomposition of the range of the `bare` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeightBarE (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (bare f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup repGauge_mul fun j : Fin 2 =>
      GaugeWeightDecomposition.spanSingleton repGauge_mul _ (LeptonSinglet.valueGaugeWeight j)
        (fun i => repGauge_gaugeTorusGen_bare i f l j))
    _ (LinearMap.range_eq_iSup_span_coord ((Basis.conj LeptonSinglet.basis)) (bare f l))

/-- The gauge weight decomposition of the fermion derivative submodules, for any
  number of covariant derivatives. It is the join, over families, derivative slots and the
  ten species, of the spans of the symbol components, each of pure gauge weight.

  This is an instance, so the weight decomposition of `derivSubmodule n` is found by
  instance search. The `rangeGaugeWeight*` decompositions above name only a single symbol
  map each, so they are left as plain definitions. -/
@[implicit_reducible]
noncomputable instance derivSubmoduleGaugeWeight (n : ℕ) :
    GaugeWeightDecomposition repGauge (derivSubmodule n) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup repGauge_mul fun f : Fin 3 =>
      GaugeWeightDecomposition.iSup repGauge_mul fun l : Fin n → Fin 1 ⊕ Fin 3 =>
      GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := rangeGaugeWeightD f l)
        (d' := rangeGaugeWeightBarD f l))
        (d' := rangeGaugeWeightU f l))
        (d' := rangeGaugeWeightBarU f l))
        (d' := rangeGaugeWeightQ f l))
        (d' := rangeGaugeWeightBarQ f l))
        (d' := rangeGaugeWeightL f l))
        (d' := rangeGaugeWeightBarL f l))
        (d' := rangeGaugeWeightE f l))
        (d' := rangeGaugeWeightBarE f l))
    _ (by rw [derivSubmodule])


/-!

## B. The support of the decomposition

-/

/-- The gauge weights carried by the fermion symbols, for each species the image of
  its value weights, negated for the unbarred species (the symbols pair with the dual
  of the value space) and taken as they are for the barred ones. -/
def fermionGaugeWeights : Finset GaugeWeight :=
  Finset.univ.image (fun j : Fin 2 × Fin 3 => -(DownSinglet.valueGaugeWeight j))
    ∪ Finset.univ.image (fun j : Fin 2 × Fin 3 => DownSinglet.valueGaugeWeight j)
    ∪ Finset.univ.image (fun j : Fin 2 × Fin 3 => -(UpSinglet.valueGaugeWeight j))
    ∪ Finset.univ.image (fun j : Fin 2 × Fin 3 => UpSinglet.valueGaugeWeight j)
    ∪ Finset.univ.image (fun j : Fin 2 × Fin 3 × Fin 2 => -(QuarkDoublet.valueGaugeWeight j))
    ∪ Finset.univ.image (fun j : Fin 2 × Fin 3 × Fin 2 => QuarkDoublet.valueGaugeWeight j)
    ∪ Finset.univ.image (fun j : Fin 2 × Fin 2 => -(LeptonDoubletV.valueGaugeWeight j))
    ∪ Finset.univ.image (fun j : Fin 2 × Fin 2 => LeptonDoubletV.valueGaugeWeight j)
    ∪ Finset.univ.image (fun j : Fin 2 => -(LeptonSinglet.valueGaugeWeight j))
    ∪ Finset.univ.image (fun j : Fin 2 => LeptonSinglet.valueGaugeWeight j)

/-- The support of the `d` range decomposition. -/
lemma rangeGaugeWeightD_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (rangeGaugeWeightD f l).supp
      = Finset.univ.image (fun j : Fin 2 × Fin 3 => -(DownSinglet.valueGaugeWeight j)) :=
  Finset.biUnion_singleton
/-- The support of the `bard` range decomposition. -/
lemma rangeGaugeWeightBarD_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (rangeGaugeWeightBarD f l).supp
      = Finset.univ.image (fun j : Fin 2 × Fin 3 => DownSinglet.valueGaugeWeight j) :=
  Finset.biUnion_singleton
/-- The support of the `u` range decomposition. -/
lemma rangeGaugeWeightU_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (rangeGaugeWeightU f l).supp
      = Finset.univ.image (fun j : Fin 2 × Fin 3 => -(UpSinglet.valueGaugeWeight j)) :=
  Finset.biUnion_singleton
/-- The support of the `baru` range decomposition. -/
lemma rangeGaugeWeightBarU_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (rangeGaugeWeightBarU f l).supp
      = Finset.univ.image (fun j : Fin 2 × Fin 3 => UpSinglet.valueGaugeWeight j) :=
  Finset.biUnion_singleton
/-- The support of the `Q` range decomposition. -/
lemma rangeGaugeWeightQ_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (rangeGaugeWeightQ f l).supp
      = Finset.univ.image (fun j : Fin 2 × Fin 3 × Fin 2 => -(QuarkDoublet.valueGaugeWeight j)) :=
  Finset.biUnion_singleton
/-- The support of the `barQ` range decomposition. -/
lemma rangeGaugeWeightBarQ_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (rangeGaugeWeightBarQ f l).supp
      = Finset.univ.image (fun j : Fin 2 × Fin 3 × Fin 2 => QuarkDoublet.valueGaugeWeight j) :=
  Finset.biUnion_singleton
/-- The support of the `L` range decomposition. -/
lemma rangeGaugeWeightL_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (rangeGaugeWeightL f l).supp
      = Finset.univ.image (fun j : Fin 2 × Fin 2 => -(LeptonDoubletV.valueGaugeWeight j)) :=
  Finset.biUnion_singleton
/-- The support of the `barL` range decomposition. -/
lemma rangeGaugeWeightBarL_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (rangeGaugeWeightBarL f l).supp
      = Finset.univ.image (fun j : Fin 2 × Fin 2 => LeptonDoubletV.valueGaugeWeight j) :=
  Finset.biUnion_singleton
/-- The support of the `e` range decomposition. -/
lemma rangeGaugeWeightE_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (rangeGaugeWeightE f l).supp
      = Finset.univ.image (fun j : Fin 2 => -(LeptonSinglet.valueGaugeWeight j)) :=
  Finset.biUnion_singleton
/-- The support of the `bare` range decomposition. -/
lemma rangeGaugeWeightBarE_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (rangeGaugeWeightBarE f l).supp
      = Finset.univ.image (fun j : Fin 2 => LeptonSinglet.valueGaugeWeight j) :=
  Finset.biUnion_singleton

/-- The support of the gauge weight decomposition of the fermion derivative
  submodules is the set of gauge weights of the ten species, independent of the number of
  covariant derivatives. -/
lemma derivSubmoduleGaugeWeight_supp (n : ℕ) :
    (derivSubmoduleGaugeWeight n).supp = fermionGaugeWeights := by
  have hconst : ∀ (t : Finset GaugeWeight),
      (Finset.univ.biUnion fun _ : Fin 3 =>
        Finset.univ.biUnion fun _ : Fin n → Fin 1 ⊕ Fin 3 => t) = t := by
    intro t
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨fun ⟨_, _, hx⟩ => hx, fun hx => ⟨0, fun _ => Sum.inl 0, hx⟩⟩
  show (Finset.univ.biUnion fun _ : Fin 3 =>
    Finset.univ.biUnion fun _ : Fin n → Fin 1 ⊕ Fin 3 => fermionGaugeWeights)
      = fermionGaugeWeights
  exact hconst _

end FermionSector

end StandardModel
