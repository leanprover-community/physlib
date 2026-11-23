/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.FermionSector.MassWeight.Basic
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.FermionSector.Deriv.GaugeWeight
/-!
# The gauge weight decomposition of the fermion mass-weight submodules

The gauge-singlet content of the fermion sector up to mass weight eight, the mass and kinetic
pairings of each species with its conjugate.

## i. Overview

Each mass-weight submodule of the fermion sector up to weight eight has an explicit
description in terms of the derivative submodules, and the derivative submodules carry
a gauge weight decomposition. Weights one, two and four are trivial, weights three, five and
seven are the towers with zero, one and two covariant derivatives, weight six is the product
of two underived towers, and weight eight is the kinetic sector.

No single fermion symbol is a gauge singlet, every species carrying a nonzero hypercharge, so
the towers of weights three, five and seven carry no gauge invariant modulo a gauge-stable
submodule (section C). Weights six and eight are products of two towers, and their weight-zero
pieces are the pairings of each species with its own conjugate (section B).

## ii. Key results

- `massWeightSubmoduleGaugeWeightSix`, `massWeightSubmoduleGaugeWeightEight` : the gauge weight
  decompositions of mass weights six and eight.
- `massWeightSubmoduleGaugeWeightSix_piece_zero`, `massWeightSubmoduleGaugeWeightEight_piece_zero` :
  their weight-zero pieces, the pairings of each species with its own conjugate.
- `mem_of_invariant_of_mem_derivSubmodule_sup` : a gauge invariant of a derivative submodule
  joined with a gauge-stable `S` lies in `S`.

## iii. Table of contents

- A. The decompositions at mass weights six and eight
- B. The weight-zero pieces
  - B.1. Infrastructure for the product weights six and eight
- C. Invariants modulo a gauge-stable submodule

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups

namespace FermionSector

/-!

## A. The decompositions at mass weights six and eight

The fermion mass-weight submodules that are products of two towers carry the product of the
gauge weight decompositions of their factors.

-/

/-- Weight six is the products of two underived fermion towers. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightSix :
    GaugeWeightDecomposition repGauge (massWeightSubmodule 6) :=
  GaugeWeightDecomposition.copy (GaugeWeightDecomposition.mul (d := derivSubmoduleGaugeWeight 0)
      (d' := derivSubmoduleGaugeWeight 0)) _
    massWeightSubmodule_six_eq

/-- Weight eight is the kinetic sector, an underived tower against a once-derived one. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightEight :
    GaugeWeightDecomposition repGauge (massWeightSubmodule 8) :=
  GaugeWeightDecomposition.copy (GaugeWeightDecomposition.mul (d := derivSubmoduleGaugeWeight 0)
      (d' := derivSubmoduleGaugeWeight 1)) _
    massWeightSubmodule_eight_eq

/-!

## B. The weight-zero pieces

-/

/-- Every gauge weight carried by a fermion symbol has nonzero hypercharge, since each of the
  ten species has a fixed nonzero hypercharge, independent of colour, isospin and
  family, and the barred species carry the negative of the unbarred one. So the zero
  weight never occurs. -/
lemma zero_not_mem_fermionGaugeWeights : (0 : GaugeWeight) ∉ fermionGaugeWeights := by
  decide

/-- The weight-zero piece of the fermion derivative submodules is trivial. Unlike
  the gauge sector, no single fermion symbol is a gauge singlet, since every one of the
  ten species carries a fixed nonzero hypercharge. A gauge-invariant combination needs
  at least two fermion insertions, which is why it is the mass weights six and eight,
  the products of two towers, that carry the interesting weight-zero content. -/
lemma derivSubmoduleGaugeWeight_piece_zero (n : ℕ) :
    (derivSubmoduleGaugeWeight n).piece 0 = ⊥ :=
  (derivSubmoduleGaugeWeight n).piece_eq_zero_of_not_mem_supp 0
    (derivSubmoduleGaugeWeight_supp n ▸ zero_not_mem_fermionGaugeWeights)

/-!

### B.1. Infrastructure for the product weights six and eight

Mass weights six and eight are products of two fermion towers, and their weight-zero
piece is genuinely nontrivial: it is spanned by pairing each species with its own
conjugate (a mass term). Splitting the product decomposition down to the ten species
and discarding the non-conjugate pairings, whose hypercharges never cancel, takes the
infrastructure developed here.

-/

/-- If the left factor of a product decomposition is a join `VA ⊔ VB`, its weight-`w`
  piece splits along the join. -/
lemma piece_sup_mul {VA VB VC : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    (dA : GaugeWeightDecomposition repGauge VA) (dB : GaugeWeightDecomposition repGauge VB)
    (dC : GaugeWeightDecomposition repGauge VC) (w : GaugeWeight) :
    (GaugeWeightDecomposition.mul (d := GaugeWeightDecomposition.sup (d := dA) (d' := dB))
        (d' := dC)).piece w
      = (GaugeWeightDecomposition.mul (d := dA) (d' := dC)).piece w
        ⊔ (GaugeWeightDecomposition.mul (d := dB) (d' := dC)).piece w :=
  GaugeWeightDecomposition.piece_congr
    (d := GaugeWeightDecomposition.mul (d := GaugeWeightDecomposition.sup (d := dA) (d' := dB))
      (d' := dC))
    (d' := GaugeWeightDecomposition.sup (d := GaugeWeightDecomposition.mul (d := dA) (d' := dC))
      (d' := GaugeWeightDecomposition.mul (d := dB) (d' := dC)))
    (Submodule.sup_mul VA VB VC) w

/-- If the right factor of a product decomposition is a join `VA ⊔ VB`, its weight-`w`
  piece splits along the join. -/
lemma piece_mul_sup {VA VB VC : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    (dC : GaugeWeightDecomposition repGauge VC) (dA : GaugeWeightDecomposition repGauge VA)
    (dB : GaugeWeightDecomposition repGauge VB) (w : GaugeWeight) :
    (GaugeWeightDecomposition.mul (d := dC)
        (d' := GaugeWeightDecomposition.sup (d := dA) (d' := dB))).piece w
      = (GaugeWeightDecomposition.mul (d := dC) (d' := dA)).piece w
        ⊔ (GaugeWeightDecomposition.mul (d := dC) (d' := dB)).piece w :=
  GaugeWeightDecomposition.piece_congr
    (d := GaugeWeightDecomposition.mul (d := dC)
      (d' := GaugeWeightDecomposition.sup (d := dA) (d' := dB)))
    (d' := GaugeWeightDecomposition.sup (d := GaugeWeightDecomposition.mul (d := dC) (d' := dA))
      (d' := GaugeWeightDecomposition.mul (d := dC) (d' := dB)))
    (Submodule.mul_sup VC VA VB) w

/-- Two decompositions with constant, non-cancelling hypercharge across their whole
  supports have a trivial product at weight zero, since a weight from one can never cancel
  a weight from the other. -/
lemma mul_piece_zero_eq_bot_of_hypercharge {V V' : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    {dV : GaugeWeightDecomposition repGauge V} {dV' : GaugeWeightDecomposition repGauge V'}
    {hc hc' : ℤ} (hV : ∀ w ∈ dV.supp, w.2.2.2 = hc) (hV' : ∀ w ∈ dV'.supp, w.2.2.2 = hc')
    (hne : hc + hc' ≠ 0) :
    (GaugeWeightDecomposition.mul (d := dV) (d' := dV')).piece 0 = ⊥ := by
  rw [show (GaugeWeightDecomposition.mul (d := dV) (d' := dV')).piece 0
      = GaugeWeightDecomposition.piece repGauge (V * V') 0 from rfl,
    GaugeWeightDecomposition.mul_piece_eq_sub (d := dV) (d' := dV') 0]
  refine le_antisymm (iSup₂_le fun w1 hw1 => ?_) bot_le
  have h1 := hV w1 hw1
  have h2 : (0 : GaugeWeight) - w1 ∉ dV'.supp := by
    intro hmem
    have h2' := hV' _ hmem
    have e : ((0 : GaugeWeight) - w1).2.2.2 = -(w1.2.2.2) := by
      rw [zero_sub, ← GaugeWeight.coord_three, ← GaugeWeight.coord_three, GaugeWeight.coord_neg]
    rw [e, h1] at h2'
    omega
  rw [dV'.piece_eq_zero_of_not_mem_supp _ h2, Submodule.mul_bot]

/-- The `d` symbols carry hypercharge `2` (the negative of the down-singlet's `-2`),
  independent of colour and family. -/
lemma rangeGaugeWeightD_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (rangeGaugeWeightD f l).supp, w.2.2.2 = 2 := by
  rw [rangeGaugeWeightD_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [DownSinglet.valueGaugeWeight]

/-- The `bard` symbols carry hypercharge `-2`, independent of colour and family. -/
lemma rangeGaugeWeightBarD_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (rangeGaugeWeightBarD f l).supp, w.2.2.2 = -2 := by
  rw [rangeGaugeWeightBarD_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [DownSinglet.valueGaugeWeight]

/-- The `u` symbols carry hypercharge `-4`, independent of colour and family. -/
lemma rangeGaugeWeightU_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (rangeGaugeWeightU f l).supp, w.2.2.2 = -4 := by
  rw [rangeGaugeWeightU_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [UpSinglet.valueGaugeWeight]

/-- The `baru` symbols carry hypercharge `4`, independent of colour and family. -/
lemma rangeGaugeWeightBarU_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (rangeGaugeWeightBarU f l).supp, w.2.2.2 = 4 := by
  rw [rangeGaugeWeightBarU_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [UpSinglet.valueGaugeWeight]

/-- The `Q` symbols carry hypercharge `-1`, independent of colour, isospin and
  family. -/
lemma rangeGaugeWeightQ_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (rangeGaugeWeightQ f l).supp, w.2.2.2 = -1 := by
  rw [rangeGaugeWeightQ_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [QuarkDoublet.valueGaugeWeight]

/-- The `barQ` symbols carry hypercharge `1`, independent of colour, isospin and
  family. -/
lemma rangeGaugeWeightBarQ_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (rangeGaugeWeightBarQ f l).supp, w.2.2.2 = 1 := by
  rw [rangeGaugeWeightBarQ_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [QuarkDoublet.valueGaugeWeight]

/-- The `L` symbols carry hypercharge `3`, independent of isospin and family. -/
lemma rangeGaugeWeightL_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (rangeGaugeWeightL f l).supp, w.2.2.2 = 3 := by
  rw [rangeGaugeWeightL_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [LeptonDoubletV.valueGaugeWeight]

/-- The `barL` symbols carry hypercharge `-3`, independent of isospin and family. -/
lemma rangeGaugeWeightBarL_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (rangeGaugeWeightBarL f l).supp, w.2.2.2 = -3 := by
  rw [rangeGaugeWeightBarL_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [LeptonDoubletV.valueGaugeWeight]

/-- The `e` symbols carry hypercharge `6`, independent of family. -/
lemma rangeGaugeWeightE_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (rangeGaugeWeightE f l).supp, w.2.2.2 = 6 := by
  rw [rangeGaugeWeightE_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [LeptonSinglet.valueGaugeWeight]

/-- The `bare` symbols carry hypercharge `-6`, independent of family. -/
lemma rangeGaugeWeightBarE_hc {n : ℕ} (f : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3) :
    ∀ w ∈ (rangeGaugeWeightBarE f l).supp, w.2.2.2 = -6 := by
  rw [rangeGaugeWeightBarE_supp]
  rintro w hw
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨j, rfl⟩ := hw
  simp [LeptonSinglet.valueGaugeWeight]

/-- The gauge weight decomposition of one family's full set of symbols at fixed
  derivative slots, matching the recipe of `derivSubmodule` itself, the join of the
  ten species' ranges. -/
@[implicit_reducible]
noncomputable def speciesGaugeWeight (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge
      (LinearMap.range (d f l) ⊔ LinearMap.range (bard f l) ⊔
        LinearMap.range (u f l) ⊔ LinearMap.range (baru f l) ⊔
        LinearMap.range (Q f l) ⊔ LinearMap.range (barQ f l) ⊔
        LinearMap.range (L f l) ⊔ LinearMap.range (barL f l) ⊔
        LinearMap.range (e f l) ⊔ LinearMap.range (bare f l)) :=
  GaugeWeightDecomposition.sup (d := GaugeWeightDecomposition.sup
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
  (d' := rangeGaugeWeightBarE f l)

/-- Against the full symbol set of a family, the `d` symbols reach gauge weight zero only
  with the `bard` symbols, the hypercharges of every other species not cancelling theirs. -/
lemma rangeGaugeWeightD_mul_speciesGaugeWeight_piece_zero {n m : ℕ} (f f' : Fin 3)
    (l : Fin n → Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) :
    (GaugeWeightDecomposition.mul (d := rangeGaugeWeightD f l)
        (d' := speciesGaugeWeight f' l')).piece 0
      = (GaugeWeightDecomposition.mul (d := rangeGaugeWeightD f l)
        (d' := rangeGaugeWeightBarD f' l')).piece 0 := by
  have h {V' : Submodule ℂ fieldData.LocalCovFieldAlgebra}
      {dV' : GaugeWeightDecomposition repGauge V'} {hc' : ℤ} :=
    mul_piece_zero_eq_bot_of_hypercharge (dV' := dV') (hc' := hc') (rangeGaugeWeightD_hc f l)
  simp only [piece_mul_sup, h (rangeGaugeWeightD_hc f' l') (by decide),
    h (rangeGaugeWeightU_hc f' l') (by decide), h (rangeGaugeWeightBarU_hc f' l') (by decide),
    h (rangeGaugeWeightQ_hc f' l') (by decide), h (rangeGaugeWeightBarQ_hc f' l') (by decide),
    h (rangeGaugeWeightL_hc f' l') (by decide), h (rangeGaugeWeightBarL_hc f' l') (by decide),
    h (rangeGaugeWeightE_hc f' l') (by decide), h (rangeGaugeWeightBarE_hc f' l') (by decide),
    bot_sup_eq, sup_bot_eq]

/-- Against the full symbol set of a family, the `bard` symbols reach gauge weight zero only
  with the `d` symbols, the hypercharges of every other species not cancelling theirs. -/
lemma rangeGaugeWeightBarD_mul_speciesGaugeWeight_piece_zero {n m : ℕ} (f f' : Fin 3)
    (l : Fin n → Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) :
    (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarD f l)
        (d' := speciesGaugeWeight f' l')).piece 0
      = (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarD f l)
        (d' := rangeGaugeWeightD f' l')).piece 0 := by
  have h {V' : Submodule ℂ fieldData.LocalCovFieldAlgebra}
      {dV' : GaugeWeightDecomposition repGauge V'} {hc' : ℤ} :=
    mul_piece_zero_eq_bot_of_hypercharge (dV' := dV') (hc' := hc') (rangeGaugeWeightBarD_hc f l)
  simp only [piece_mul_sup, h (rangeGaugeWeightBarD_hc f' l') (by decide),
    h (rangeGaugeWeightU_hc f' l') (by decide), h (rangeGaugeWeightBarU_hc f' l') (by decide),
    h (rangeGaugeWeightQ_hc f' l') (by decide), h (rangeGaugeWeightBarQ_hc f' l') (by decide),
    h (rangeGaugeWeightL_hc f' l') (by decide), h (rangeGaugeWeightBarL_hc f' l') (by decide),
    h (rangeGaugeWeightE_hc f' l') (by decide), h (rangeGaugeWeightBarE_hc f' l') (by decide),
    sup_bot_eq]

/-- Against the full symbol set of a family, the `u` symbols reach gauge weight zero only
  with the `baru` symbols, the hypercharges of every other species not cancelling theirs. -/
lemma rangeGaugeWeightU_mul_speciesGaugeWeight_piece_zero {n m : ℕ} (f f' : Fin 3)
    (l : Fin n → Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) :
    (GaugeWeightDecomposition.mul (d := rangeGaugeWeightU f l)
        (d' := speciesGaugeWeight f' l')).piece 0
      = (GaugeWeightDecomposition.mul (d := rangeGaugeWeightU f l)
        (d' := rangeGaugeWeightBarU f' l')).piece 0 := by
  have h {V' : Submodule ℂ fieldData.LocalCovFieldAlgebra}
      {dV' : GaugeWeightDecomposition repGauge V'} {hc' : ℤ} :=
    mul_piece_zero_eq_bot_of_hypercharge (dV' := dV') (hc' := hc') (rangeGaugeWeightU_hc f l)
  simp only [piece_mul_sup, h (rangeGaugeWeightD_hc f' l') (by decide),
    h (rangeGaugeWeightBarD_hc f' l') (by decide), h (rangeGaugeWeightU_hc f' l') (by decide),
    h (rangeGaugeWeightQ_hc f' l') (by decide), h (rangeGaugeWeightBarQ_hc f' l') (by decide),
    h (rangeGaugeWeightL_hc f' l') (by decide), h (rangeGaugeWeightBarL_hc f' l') (by decide),
    h (rangeGaugeWeightE_hc f' l') (by decide), h (rangeGaugeWeightBarE_hc f' l') (by decide),
    bot_sup_eq, sup_bot_eq]

/-- Against the full symbol set of a family, the `baru` symbols reach gauge weight zero only
  with the `u` symbols, the hypercharges of every other species not cancelling theirs. -/
lemma rangeGaugeWeightBarU_mul_speciesGaugeWeight_piece_zero {n m : ℕ} (f f' : Fin 3)
    (l : Fin n → Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) :
    (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarU f l)
        (d' := speciesGaugeWeight f' l')).piece 0
      = (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarU f l)
        (d' := rangeGaugeWeightU f' l')).piece 0 := by
  have h {V' : Submodule ℂ fieldData.LocalCovFieldAlgebra}
      {dV' : GaugeWeightDecomposition repGauge V'} {hc' : ℤ} :=
    mul_piece_zero_eq_bot_of_hypercharge (dV' := dV') (hc' := hc') (rangeGaugeWeightBarU_hc f l)
  simp only [piece_mul_sup, h (rangeGaugeWeightD_hc f' l') (by decide),
    h (rangeGaugeWeightBarD_hc f' l') (by decide), h (rangeGaugeWeightBarU_hc f' l') (by decide),
    h (rangeGaugeWeightQ_hc f' l') (by decide), h (rangeGaugeWeightBarQ_hc f' l') (by decide),
    h (rangeGaugeWeightL_hc f' l') (by decide), h (rangeGaugeWeightBarL_hc f' l') (by decide),
    h (rangeGaugeWeightE_hc f' l') (by decide), h (rangeGaugeWeightBarE_hc f' l') (by decide),
    bot_sup_eq, sup_bot_eq]

/-- Against the full symbol set of a family, the `Q` symbols reach gauge weight zero only
  with the `barQ` symbols, the hypercharges of every other species not cancelling theirs. -/
lemma rangeGaugeWeightQ_mul_speciesGaugeWeight_piece_zero {n m : ℕ} (f f' : Fin 3)
    (l : Fin n → Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) :
    (GaugeWeightDecomposition.mul (d := rangeGaugeWeightQ f l)
        (d' := speciesGaugeWeight f' l')).piece 0
      = (GaugeWeightDecomposition.mul (d := rangeGaugeWeightQ f l)
        (d' := rangeGaugeWeightBarQ f' l')).piece 0 := by
  have h {V' : Submodule ℂ fieldData.LocalCovFieldAlgebra}
      {dV' : GaugeWeightDecomposition repGauge V'} {hc' : ℤ} :=
    mul_piece_zero_eq_bot_of_hypercharge (dV' := dV') (hc' := hc') (rangeGaugeWeightQ_hc f l)
  simp only [piece_mul_sup, h (rangeGaugeWeightD_hc f' l') (by decide),
    h (rangeGaugeWeightBarD_hc f' l') (by decide), h (rangeGaugeWeightU_hc f' l') (by decide),
    h (rangeGaugeWeightBarU_hc f' l') (by decide), h (rangeGaugeWeightQ_hc f' l') (by decide),
    h (rangeGaugeWeightL_hc f' l') (by decide), h (rangeGaugeWeightBarL_hc f' l') (by decide),
    h (rangeGaugeWeightE_hc f' l') (by decide), h (rangeGaugeWeightBarE_hc f' l') (by decide),
    bot_sup_eq, sup_bot_eq]

/-- Against the full symbol set of a family, the `barQ` symbols reach gauge weight zero only
  with the `Q` symbols, the hypercharges of every other species not cancelling theirs. -/
lemma rangeGaugeWeightBarQ_mul_speciesGaugeWeight_piece_zero {n m : ℕ} (f f' : Fin 3)
    (l : Fin n → Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) :
    (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarQ f l)
        (d' := speciesGaugeWeight f' l')).piece 0
      = (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarQ f l)
        (d' := rangeGaugeWeightQ f' l')).piece 0 := by
  have h {V' : Submodule ℂ fieldData.LocalCovFieldAlgebra}
      {dV' : GaugeWeightDecomposition repGauge V'} {hc' : ℤ} :=
    mul_piece_zero_eq_bot_of_hypercharge (dV' := dV') (hc' := hc') (rangeGaugeWeightBarQ_hc f l)
  simp only [piece_mul_sup, h (rangeGaugeWeightD_hc f' l') (by decide),
    h (rangeGaugeWeightBarD_hc f' l') (by decide), h (rangeGaugeWeightU_hc f' l') (by decide),
    h (rangeGaugeWeightBarU_hc f' l') (by decide), h (rangeGaugeWeightBarQ_hc f' l') (by decide),
    h (rangeGaugeWeightL_hc f' l') (by decide), h (rangeGaugeWeightBarL_hc f' l') (by decide),
    h (rangeGaugeWeightE_hc f' l') (by decide), h (rangeGaugeWeightBarE_hc f' l') (by decide),
    bot_sup_eq, sup_bot_eq]

/-- Against the full symbol set of a family, the `L` symbols reach gauge weight zero only
  with the `barL` symbols, the hypercharges of every other species not cancelling theirs. -/
lemma rangeGaugeWeightL_mul_speciesGaugeWeight_piece_zero {n m : ℕ} (f f' : Fin 3)
    (l : Fin n → Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) :
    (GaugeWeightDecomposition.mul (d := rangeGaugeWeightL f l)
        (d' := speciesGaugeWeight f' l')).piece 0
      = (GaugeWeightDecomposition.mul (d := rangeGaugeWeightL f l)
        (d' := rangeGaugeWeightBarL f' l')).piece 0 := by
  have h {V' : Submodule ℂ fieldData.LocalCovFieldAlgebra}
      {dV' : GaugeWeightDecomposition repGauge V'} {hc' : ℤ} :=
    mul_piece_zero_eq_bot_of_hypercharge (dV' := dV') (hc' := hc') (rangeGaugeWeightL_hc f l)
  simp only [piece_mul_sup, h (rangeGaugeWeightD_hc f' l') (by decide),
    h (rangeGaugeWeightBarD_hc f' l') (by decide), h (rangeGaugeWeightU_hc f' l') (by decide),
    h (rangeGaugeWeightBarU_hc f' l') (by decide), h (rangeGaugeWeightQ_hc f' l') (by decide),
    h (rangeGaugeWeightBarQ_hc f' l') (by decide), h (rangeGaugeWeightL_hc f' l') (by decide),
    h (rangeGaugeWeightE_hc f' l') (by decide), h (rangeGaugeWeightBarE_hc f' l') (by decide),
    bot_sup_eq, sup_bot_eq]

/-- Against the full symbol set of a family, the `barL` symbols reach gauge weight zero only
  with the `L` symbols, the hypercharges of every other species not cancelling theirs. -/
lemma rangeGaugeWeightBarL_mul_speciesGaugeWeight_piece_zero {n m : ℕ} (f f' : Fin 3)
    (l : Fin n → Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) :
    (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarL f l)
        (d' := speciesGaugeWeight f' l')).piece 0
      = (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarL f l)
        (d' := rangeGaugeWeightL f' l')).piece 0 := by
  have h {V' : Submodule ℂ fieldData.LocalCovFieldAlgebra}
      {dV' : GaugeWeightDecomposition repGauge V'} {hc' : ℤ} :=
    mul_piece_zero_eq_bot_of_hypercharge (dV' := dV') (hc' := hc') (rangeGaugeWeightBarL_hc f l)
  simp only [piece_mul_sup, h (rangeGaugeWeightD_hc f' l') (by decide),
    h (rangeGaugeWeightBarD_hc f' l') (by decide), h (rangeGaugeWeightU_hc f' l') (by decide),
    h (rangeGaugeWeightBarU_hc f' l') (by decide), h (rangeGaugeWeightQ_hc f' l') (by decide),
    h (rangeGaugeWeightBarQ_hc f' l') (by decide), h (rangeGaugeWeightBarL_hc f' l') (by decide),
    h (rangeGaugeWeightE_hc f' l') (by decide), h (rangeGaugeWeightBarE_hc f' l') (by decide),
    bot_sup_eq, sup_bot_eq]

/-- Against the full symbol set of a family, the `e` symbols reach gauge weight zero only
  with the `bare` symbols, the hypercharges of every other species not cancelling theirs. -/
lemma rangeGaugeWeightE_mul_speciesGaugeWeight_piece_zero {n m : ℕ} (f f' : Fin 3)
    (l : Fin n → Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) :
    (GaugeWeightDecomposition.mul (d := rangeGaugeWeightE f l)
        (d' := speciesGaugeWeight f' l')).piece 0
      = (GaugeWeightDecomposition.mul (d := rangeGaugeWeightE f l)
        (d' := rangeGaugeWeightBarE f' l')).piece 0 := by
  have h {V' : Submodule ℂ fieldData.LocalCovFieldAlgebra}
      {dV' : GaugeWeightDecomposition repGauge V'} {hc' : ℤ} :=
    mul_piece_zero_eq_bot_of_hypercharge (dV' := dV') (hc' := hc') (rangeGaugeWeightE_hc f l)
  simp only [piece_mul_sup, h (rangeGaugeWeightD_hc f' l') (by decide),
    h (rangeGaugeWeightBarD_hc f' l') (by decide), h (rangeGaugeWeightU_hc f' l') (by decide),
    h (rangeGaugeWeightBarU_hc f' l') (by decide), h (rangeGaugeWeightQ_hc f' l') (by decide),
    h (rangeGaugeWeightBarQ_hc f' l') (by decide), h (rangeGaugeWeightL_hc f' l') (by decide),
    h (rangeGaugeWeightBarL_hc f' l') (by decide), h (rangeGaugeWeightE_hc f' l') (by decide),
    bot_sup_eq, sup_bot_eq]

/-- Against the full symbol set of a family, the `bare` symbols reach gauge weight zero only
  with the `e` symbols, the hypercharges of every other species not cancelling theirs. -/
lemma rangeGaugeWeightBarE_mul_speciesGaugeWeight_piece_zero {n m : ℕ} (f f' : Fin 3)
    (l : Fin n → Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) :
    (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarE f l)
        (d' := speciesGaugeWeight f' l')).piece 0
      = (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarE f l)
        (d' := rangeGaugeWeightE f' l')).piece 0 := by
  have h {V' : Submodule ℂ fieldData.LocalCovFieldAlgebra}
      {dV' : GaugeWeightDecomposition repGauge V'} {hc' : ℤ} :=
    mul_piece_zero_eq_bot_of_hypercharge (dV' := dV') (hc' := hc') (rangeGaugeWeightBarE_hc f l)
  simp only [piece_mul_sup, h (rangeGaugeWeightD_hc f' l') (by decide),
    h (rangeGaugeWeightBarD_hc f' l') (by decide), h (rangeGaugeWeightU_hc f' l') (by decide),
    h (rangeGaugeWeightBarU_hc f' l') (by decide), h (rangeGaugeWeightQ_hc f' l') (by decide),
    h (rangeGaugeWeightBarQ_hc f' l') (by decide), h (rangeGaugeWeightL_hc f' l') (by decide),
    h (rangeGaugeWeightBarL_hc f' l') (by decide), h (rangeGaugeWeightBarE_hc f' l') (by decide),
    bot_sup_eq, sup_bot_eq]

/-- The weight-zero piece of the product of two families' full symbol sets collapses
  to the ten conjugate pairings, since every other combination of species has hypercharges
  that cannot cancel. -/
lemma speciesGaugeWeight_mul_piece_zero {n m : ℕ} (f f' : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3)
    (l' : Fin m → Fin 1 ⊕ Fin 3) :
    (GaugeWeightDecomposition.mul (d := speciesGaugeWeight f l)
        (d' := speciesGaugeWeight f' l')).piece 0
      =
      (GaugeWeightDecomposition.mul (d := rangeGaugeWeightD f l)
            (d' := rangeGaugeWeightBarD f' l')).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarD f l)
            (d' := rangeGaugeWeightD f' l')).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightU f l)
            (d' := rangeGaugeWeightBarU f' l')).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarU f l)
            (d' := rangeGaugeWeightU f' l')).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightQ f l)
            (d' := rangeGaugeWeightBarQ f' l')).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarQ f l)
            (d' := rangeGaugeWeightQ f' l')).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightL f l)
            (d' := rangeGaugeWeightBarL f' l')).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarL f l)
            (d' := rangeGaugeWeightL f' l')).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightE f l)
            (d' := rangeGaugeWeightBarE f' l')).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarE f l)
            (d' := rangeGaugeWeightE f' l')).piece 0 := by
  simp only [piece_sup_mul, rangeGaugeWeightD_mul_speciesGaugeWeight_piece_zero,
    rangeGaugeWeightBarD_mul_speciesGaugeWeight_piece_zero,
    rangeGaugeWeightU_mul_speciesGaugeWeight_piece_zero,
    rangeGaugeWeightBarU_mul_speciesGaugeWeight_piece_zero,
    rangeGaugeWeightQ_mul_speciesGaugeWeight_piece_zero,
    rangeGaugeWeightBarQ_mul_speciesGaugeWeight_piece_zero,
    rangeGaugeWeightL_mul_speciesGaugeWeight_piece_zero,
    rangeGaugeWeightBarL_mul_speciesGaugeWeight_piece_zero,
    rangeGaugeWeightE_mul_speciesGaugeWeight_piece_zero,
    rangeGaugeWeightBarE_mul_speciesGaugeWeight_piece_zero]

/-- The zero-index derivative slot collapses a supremum over it to its value, as there
  is nothing to derive with respect to. -/
lemma iSup_fin_zero_eq {α : Type} [CompleteLattice α] (F : (Fin 0 → Fin 1 ⊕ Fin 3) → α) :
    ⨆ l, F l = F ![] :=
  le_antisymm (iSup_le fun l => by rw [Subsingleton.elim l ![]]) (le_iSup F ![])

/-- The underived derivative submodule as a join over families alone, the trivial
  derivative slot dropped. -/
lemma derivSubmodule_zero_eq :
    derivSubmodule 0 = ⨆ (f : Fin 3),
      (LinearMap.range (d f ![]) ⊔
        LinearMap.range (bard f ![]) ⊔
        LinearMap.range (u f ![]) ⊔
        LinearMap.range (baru f ![]) ⊔
        LinearMap.range (Q f ![]) ⊔
        LinearMap.range (barQ f ![]) ⊔
        LinearMap.range (L f ![]) ⊔
        LinearMap.range (barL f ![]) ⊔
        LinearMap.range (e f ![]) ⊔
        LinearMap.range (bare f ![])) := by
  show (⨆ (_ : Fin 3) (_ : Fin 0 → Fin 1 ⊕ Fin 3), _) = _
  exact iSup_congr fun f => iSup_fin_zero_eq _

/-- The once-derived derivative submodule as a join over families and the single derivative
  slot. -/
lemma derivSubmodule_one_eq :
    derivSubmodule 1 = ⨆ (f' : Fin 3) (l' : Fin 1 → Fin 1 ⊕ Fin 3),
      (LinearMap.range (d f' l') ⊔
        LinearMap.range (bard f' l') ⊔
        LinearMap.range (u f' l') ⊔
        LinearMap.range (baru f' l') ⊔
        LinearMap.range (Q f' l') ⊔
        LinearMap.range (barQ f' l') ⊔
        LinearMap.range (L f' l') ⊔
        LinearMap.range (barL f' l') ⊔
        LinearMap.range (e f' l') ⊔
        LinearMap.range (bare f' l')) := rfl

/-- The product of two underived derivative submodules as a join over pairs of families. -/
lemma derivSubmodule_zero_mul_derivSubmodule_zero : derivSubmodule 0 * derivSubmodule 0
    = ⨆ (f : Fin 3) (f' : Fin 3),
      (LinearMap.range (d f ![]) ⊔
        LinearMap.range (bard f ![]) ⊔
        LinearMap.range (u f ![]) ⊔
        LinearMap.range (baru f ![]) ⊔
        LinearMap.range (Q f ![]) ⊔
        LinearMap.range (barQ f ![]) ⊔
        LinearMap.range (L f ![]) ⊔
        LinearMap.range (barL f ![]) ⊔
        LinearMap.range (e f ![]) ⊔
        LinearMap.range (bare f ![]))
        * (LinearMap.range (d f' ![]) ⊔
        LinearMap.range (bard f' ![]) ⊔
        LinearMap.range (u f' ![]) ⊔
        LinearMap.range (baru f' ![]) ⊔
        LinearMap.range (Q f' ![]) ⊔
        LinearMap.range (barQ f' ![]) ⊔
        LinearMap.range (L f' ![]) ⊔
        LinearMap.range (barL f' ![]) ⊔
        LinearMap.range (e f' ![]) ⊔
        LinearMap.range (bare f' ![])) := by
  rw [derivSubmodule_zero_eq, Submodule.iSup_mul]
  exact iSup_congr fun f => Submodule.mul_iSup _ _

/-- The product of an underived and a once-derived derivative submodule as a join over pairs of
  families and the derivative slot. -/
lemma derivSubmodule_zero_mul_derivSubmodule_one : derivSubmodule 0 * derivSubmodule 1
    = ⨆ (f : Fin 3) (f' : Fin 3) (l' : Fin 1 → Fin 1 ⊕ Fin 3),
      (LinearMap.range (d f ![]) ⊔
        LinearMap.range (bard f ![]) ⊔
        LinearMap.range (u f ![]) ⊔
        LinearMap.range (baru f ![]) ⊔
        LinearMap.range (Q f ![]) ⊔
        LinearMap.range (barQ f ![]) ⊔
        LinearMap.range (L f ![]) ⊔
        LinearMap.range (barL f ![]) ⊔
        LinearMap.range (e f ![]) ⊔
        LinearMap.range (bare f ![]))
        * (LinearMap.range (d f' l') ⊔
        LinearMap.range (bard f' l') ⊔
        LinearMap.range (u f' l') ⊔
        LinearMap.range (baru f' l') ⊔
        LinearMap.range (Q f' l') ⊔
        LinearMap.range (barQ f' l') ⊔
        LinearMap.range (L f' l') ⊔
        LinearMap.range (barL f' l') ⊔
        LinearMap.range (e f' l') ⊔
        LinearMap.range (bare f' l')) := by
  rw [derivSubmodule_zero_eq, derivSubmodule_one_eq, Submodule.iSup_mul]
  exact iSup_congr fun f => by
    rw [Submodule.mul_iSup]
    exact iSup_congr fun f' => Submodule.mul_iSup _ _

/-- The weight-zero piece at mass weight six, written out in the mass terms
  themselves, the join, over pairs of families, of the ten ways to pair each
  species with its own conjugate. Every other pairing of species has hypercharges
  that cannot cancel, by `speciesGaugeWeight_mul_piece_zero`. -/
lemma massWeightSubmoduleGaugeWeightSix_piece_zero :
    (massWeightSubmoduleGaugeWeightSix).piece 0
      = ⨆ (f : Fin 3) (f' : Fin 3),
        (GaugeWeightDecomposition.mul (d := rangeGaugeWeightD f ![])
              (d' := rangeGaugeWeightBarD f' ![])).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarD f ![])
              (d' := rangeGaugeWeightD f' ![])).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightU f ![])
              (d' := rangeGaugeWeightBarU f' ![])).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarU f ![])
              (d' := rangeGaugeWeightU f' ![])).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightQ f ![])
              (d' := rangeGaugeWeightBarQ f' ![])).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarQ f ![])
              (d' := rangeGaugeWeightQ f' ![])).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightL f ![])
              (d' := rangeGaugeWeightBarL f' ![])).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarL f ![])
              (d' := rangeGaugeWeightL f' ![])).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightE f ![])
              (d' := rangeGaugeWeightBarE f' ![])).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarE f ![])
              (d' := rangeGaugeWeightE f' ![])).piece 0 := by
  show (GaugeWeightDecomposition.mul (d := derivSubmoduleGaugeWeight 0)
      (d' := derivSubmoduleGaugeWeight 0)).piece 0 = _
  rw [GaugeWeightDecomposition.piece_congr
      (d := GaugeWeightDecomposition.mul (d := derivSubmoduleGaugeWeight 0)
        (d' := derivSubmoduleGaugeWeight 0))
      (d' := GaugeWeightDecomposition.iSup repGauge_mul (fun f =>
        GaugeWeightDecomposition.iSup repGauge_mul (fun f' =>
          GaugeWeightDecomposition.mul (d := speciesGaugeWeight f ![])
            (d' := speciesGaugeWeight f' ![]))))
      derivSubmodule_zero_mul_derivSubmodule_zero 0]
  simp only [GaugeWeightDecomposition.piece_iSup]
  exact iSup_congr fun f => iSup_congr fun f' =>
    speciesGaugeWeight_mul_piece_zero f f' ![] ![]

/-- The weight-zero piece at mass weight eight, written out in the kinetic terms
  themselves, the join, over pairs of families and a once-derived slot, of the ten
  ways to pair each species with its own conjugate. Every other pairing of species has
  hypercharges that cannot cancel, by `speciesGaugeWeight_mul_piece_zero`. -/
lemma massWeightSubmoduleGaugeWeightEight_piece_zero :
    (massWeightSubmoduleGaugeWeightEight).piece 0
      = ⨆ (f : Fin 3) (f' : Fin 3) (l' : Fin 1 → Fin 1 ⊕ Fin 3),
        (GaugeWeightDecomposition.mul (d := rangeGaugeWeightD f ![])
              (d' := rangeGaugeWeightBarD f' l')).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarD f ![])
              (d' := rangeGaugeWeightD f' l')).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightU f ![])
              (d' := rangeGaugeWeightBarU f' l')).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarU f ![])
              (d' := rangeGaugeWeightU f' l')).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightQ f ![])
              (d' := rangeGaugeWeightBarQ f' l')).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarQ f ![])
              (d' := rangeGaugeWeightQ f' l')).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightL f ![])
              (d' := rangeGaugeWeightBarL f' l')).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarL f ![])
              (d' := rangeGaugeWeightL f' l')).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightE f ![])
              (d' := rangeGaugeWeightBarE f' l')).piece 0
          ⊔ (GaugeWeightDecomposition.mul (d := rangeGaugeWeightBarE f ![])
              (d' := rangeGaugeWeightE f' l')).piece 0 := by
  show (GaugeWeightDecomposition.mul (d := derivSubmoduleGaugeWeight 0)
      (d' := derivSubmoduleGaugeWeight 1)).piece 0 = _
  rw [GaugeWeightDecomposition.piece_congr
      (d := GaugeWeightDecomposition.mul (d := derivSubmoduleGaugeWeight 0)
        (d' := derivSubmoduleGaugeWeight 1))
      (d' := GaugeWeightDecomposition.iSup repGauge_mul (fun f =>
        GaugeWeightDecomposition.iSup repGauge_mul (fun f' =>
          GaugeWeightDecomposition.iSup repGauge_mul (fun l' =>
            GaugeWeightDecomposition.mul (d := speciesGaugeWeight f ![])
              (d' := speciesGaugeWeight f' l')))))
      derivSubmodule_zero_mul_derivSubmodule_one 0]
  simp only [GaugeWeightDecomposition.piece_iSup]
  exact iSup_congr fun f => iSup_congr fun f' => iSup_congr fun l' =>
    speciesGaugeWeight_mul_piece_zero f f' ![] l'

/-!

## C. Invariants modulo a gauge-stable submodule

A submodule `S` closed under the gauge action can be discarded from a gauge-invariant
element: if `x` is gauge invariant and lies in a fermionic submodule joined with `S`, then
its fermionic part has to vanish and `x` already lies in `S`. The reason is the one behind
`derivSubmoduleGaugeWeight_piece_zero`: every one of the ten species carries a fixed nonzero
hypercharge, so no nonzero fermionic element is a gauge singlet.

The argument is the torus sieve `GaugeWeightDecomposition.mem_piece_zero_sup_of_invariant`:
each piece of nonzero weight is scaled by a torus generator by a scalar other than one, so
modulo `S` an invariant lies in the weight-zero piece, and the weight-zero piece of a single
tower is trivial (`derivSubmoduleGaugeWeight_piece_zero`).

-/

/-- A gauge-invariant element of `derivSubmodule n ⊔ S`, for any submodule `S` closed under
  the gauge action, already lies in `S`. The fermionic part carries no gauge singlet, since
  each of the ten species has a fixed nonzero hypercharge, so it cannot survive; what is left
  is the part in `S`. Compare `derivSubmoduleGaugeWeight_piece_zero`. -/
lemma mem_of_invariant_of_mem_derivSubmodule_sup {n : ℕ}
    {S : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    (hS : ∀ (g : GaugeGroupI) (y : fieldData.LocalCovFieldAlgebra), y ∈ S → repGauge g y ∈ S)
    {x : fieldData.LocalCovFieldAlgebra} (hx : x ∈ derivSubmodule n ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) : x ∈ S := by
  have hx0 := GaugeWeightDecomposition.mem_piece_zero_sup_of_invariant
    (derivSubmoduleGaugeWeight n) (fun i y hy => hS _ y hy) hx fun _ => hinv _
  rwa [derivSubmoduleGaugeWeight_piece_zero, bot_sup_eq] at hx0

/-- Mass weight one contributes nothing to a join, since the submodule is trivial, so no invariance
  hypothesis is needed. -/
lemma mem_of_mem_massWeightSubmoduleOne_sup {S : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    {x : fieldData.LocalCovFieldAlgebra} (hx : x ∈ massWeightSubmodule 1 ⊔ S) : x ∈ S := by
  rwa [massWeightSubmodule_one_eq, bot_sup_eq] at hx

/-- Mass weight two contributes nothing to a join, since the submodule is trivial, so no invariance
  hypothesis is needed. -/
lemma mem_of_mem_massWeightSubmoduleTwo_sup {S : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    {x : fieldData.LocalCovFieldAlgebra} (hx : x ∈ massWeightSubmodule 2 ⊔ S) : x ∈ S := by
  rwa [massWeightSubmodule_two_eq, bot_sup_eq] at hx

/-- Mass weight four contributes nothing to a join, since the submodule is trivial, so no
  invariance hypothesis is needed. -/
lemma mem_of_mem_massWeightSubmoduleFour_sup {S : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    {x : fieldData.LocalCovFieldAlgebra} (hx : x ∈ massWeightSubmodule 4 ⊔ S) : x ∈ S := by
  rwa [massWeightSubmodule_four_eq, bot_sup_eq] at hx

/-- A gauge-invariant element of `massWeightSubmodule 3 ⊔ S`, for `S` closed under the
  gauge action, lies in `S`, since mass weight three is the underived fermion towers, which carry
  no gauge singlet. -/
lemma mem_of_invariant_of_mem_massWeightSubmoduleThree_sup
    {S : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    (hS : ∀ (g : GaugeGroupI) (y : fieldData.LocalCovFieldAlgebra), y ∈ S → repGauge g y ∈ S)
    {x : fieldData.LocalCovFieldAlgebra} (hx : x ∈ massWeightSubmodule 3 ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) : x ∈ S :=
  mem_of_invariant_of_mem_derivSubmodule_sup hS
    (by rwa [massWeightSubmodule_three_eq] at hx) hinv

/-- A gauge-invariant element of `massWeightSubmodule 5 ⊔ S`, for `S` closed under the
  gauge action, lies in `S`, since mass weight five is the once-derived fermion towers, which carry
  no gauge singlet. -/
lemma mem_of_invariant_of_mem_massWeightSubmoduleFive_sup
    {S : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    (hS : ∀ (g : GaugeGroupI) (y : fieldData.LocalCovFieldAlgebra), y ∈ S → repGauge g y ∈ S)
    {x : fieldData.LocalCovFieldAlgebra} (hx : x ∈ massWeightSubmodule 5 ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) : x ∈ S :=
  mem_of_invariant_of_mem_derivSubmodule_sup hS
    (by rwa [massWeightSubmodule_five_eq] at hx) hinv

/-- A gauge-invariant element of `massWeightSubmodule 7 ⊔ S`, for `S` closed under the
  gauge action, lies in `S`, since mass weight seven is the twice-derived fermion towers, which
  carry no gauge singlet. -/
lemma mem_of_invariant_of_mem_massWeightSubmoduleSeven_sup
    {S : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    (hS : ∀ (g : GaugeGroupI) (y : fieldData.LocalCovFieldAlgebra), y ∈ S → repGauge g y ∈ S)
    {x : fieldData.LocalCovFieldAlgebra} (hx : x ∈ massWeightSubmodule 7 ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) : x ∈ S :=
  mem_of_invariant_of_mem_derivSubmodule_sup hS
    (by rwa [massWeightSubmodule_seven_eq] at hx) hinv

end FermionSector

end StandardModel
