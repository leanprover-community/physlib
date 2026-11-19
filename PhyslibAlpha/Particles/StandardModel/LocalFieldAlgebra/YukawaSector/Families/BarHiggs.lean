/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.YukawaSector.Families.Higgs
/-!
# The Yukawa terms built on the conjugate Higgs symbol

The conjugate-Higgs-type Yukawa terms of the Standard Model's covariant field algebra.

## i. Overview

Everything below is stated about the covariant field algebra `fieldData.LocalCovFieldAlgebra` of the
Standard Model.

The remaining three couplings of the mass-weight-eight Yukawa sector are built on the
conjugate Higgs symbol, `barH bard Q`, `barH u barQ` and `barH L bare`.  Each is the
conjugate of one of the three couplings of `Families/Higgs.lean`, and is the same computation
with every symbol replaced by its conjugate. Fundamental and anti-fundamental indices
exchange, left- and right-handed spinors exchange, and every hypercharge changes sign.  So
the isospin structure of the conjugate up type is `2 ⊗ 2` where its partner had `2̄ ⊗ 2̄`,
and its invariant is again the antisymmetric symbol.

With these six couplings the twelve blocks are accounted for. The other six are the same
six with the two fermion factors exchanged, and by `mul_mul_swap_eq_neg` their terms are
minus these while by `mul_mul_piece_swap` their blocks are the same submodules.

## ii. Key results

- `barDownYukawa`, `barUpYukawa`, `barLeptonYukawa` : the three conjugate Yukawa terms.
- `isEquivariant_colourFundAntiFund_barDownBlock`, `isEquivariant_isospinFundFund_barUpBlock` and
  the rest : the index laws of the three conjugate blocks.
- `yukawaSpan` : the join of all six couplings over all nine family pairs.
- `yukawaSpan_le_inf` : the Yukawa span lies inside the gauge- and Lorentz-invariants of
  the sector at mass weight eight.

## iii. Table of contents

- A. The conjugate down-type Yukawa term
- B. The invariance of the conjugate down-type Yukawa term, and its mass weight
- C. The conjugate up-type Yukawa term
- D. The invariance of the conjugate up-type Yukawa term, and its mass weight
- E. The conjugate charged-lepton Yukawa term
- F. The invariance of the conjugate charged-lepton Yukawa term, and its mass weight
- G. The Yukawa span

## iv. References

* None.

-/

@[expose] public section

open TensorSpecies
open suTensor (fundAntiFundIdx)

namespace StandardModel

open GaugeFieldData (FieldKind)

open TensorProduct Matrix MatrixGroups Lorentz Pointwise ComplexConjugate complexLorentzTensor

namespace LocalCovFieldAlgebra

/-!

## A. The conjugate down-type Yukawa term

The conjugate of the down type: the product `barH bard Q`.  Colour is `3 ⊗ 3̄` with the
conjugate down singlet supplying the fundamental index, isospin is `2 ⊗ 2̄` with the
conjugate Higgs symbol supplying the fundamental index and the quark doublet the
anti-fundamental one, and both fermions are left-handed.

-/

/-- The components of the conjugate down-type Yukawa block `barH bard Q`, a conjugate
  Higgs symbol, a conjugate down-singlet symbol and a quark-doublet symbol, none carrying
  derivatives. -/
noncomputable def barDownBlock (f f' : Fin 3) (i sbd : Fin 2) (cbd : Fin 3) (sQ : Fin 2)
    (cQ : Fin 3) (wQ : Fin 2) : fieldData.LocalCovFieldAlgebra :=
  ScalarSector.barHiggs ![] i * (FermionSector.bardComponent f ![] (sbd, cbd) *
    FermionSector.QComponent f' ![] (sQ, cQ, wQ))

/-- The two colour indices of the conjugate down-type block carry one fundamental and one
  anti-fundamental `su(3)` index, the conjugate down singlet supplying the fundamental
  one. -/
lemma isEquivariant_colourFundAntiFund_barDownBlock (f f' : Fin 3) (i sbd sQ wQ : Fin 2) :
    (suTensor 3).IsEquivariant ![.fund, .antiFund] (repGaugeGroupI.comp GaugeGroupI.ofSU3)
      (liftComponents ((fun l : Fin 2 → Fin 3 =>
        LocalCovFieldAlgebra.barDownBlock f f' i sbd (l 0) sQ (l 1) wQ) ∘ fundAntiFundIdx)) :=
  ColourFundAntiFund.of_law fun U l => by
    simp only [barDownBlock]
    rw [LocalCovFieldAlgebra.repGauge_mul_fixed_left (U, 1, 1)
      (X := fun a => FermionSector.bardComponent f ![] (sbd, a))
      (Y := fun a => FermionSector.QComponent f' ![] (sQ, a, wQ))
      (LocalCovFieldAlgebra.repGauge_su3_barHiggs U ![] i) (FermionSector.repGauge_su3_bard U
        f ![] sbd (l 0))
      (FermionSector.repGauge_su3_Q U f' ![] sQ (l 1) wQ), Physlib.Fin.sum_fin_two_arrow]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The two isospin indices of the conjugate down-type block carry one fundamental and one
  anti-fundamental `su(2)` index, the conjugate Higgs symbol supplying the fundamental
  one. -/
lemma isEquivariant_isospinFundAntiFund_barDownBlock (f f' : Fin 3) (sbd : Fin 2) (cbd : Fin 3)
    (sQ : Fin 2) (cQ : Fin 3) :
    (suTensor 2).IsEquivariant ![.fund, .antiFund] (repGaugeGroupI.comp GaugeGroupI.ofSU2)
      (liftComponents ((fun l : Fin 2 → Fin 2 =>
        LocalCovFieldAlgebra.barDownBlock f f' (l 0) sbd cbd sQ cQ (l 1)) ∘ fundAntiFundIdx)) :=
  IsospinFundAntiFund.of_law fun V l => by
    simp only [barDownBlock]
    rw [LocalCovFieldAlgebra.repGauge_mul_fixed_mid (1, V, 1) (A := fun a => ScalarSector.barHiggs
      ![] a)
      (Y := fun a => FermionSector.QComponent f' ![] (sQ, cQ, a))
      (LocalCovFieldAlgebra.repGauge_su2_barHiggs V ![] (l 0))
        (FermionSector.repGauge_su2_bard V f ![] (sbd, cbd))
      (FermionSector.repGauge_su2_Q V f' ![] sQ cQ (l 1)), Physlib.Fin.sum_fin_two_arrow]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The two spinor indices of the conjugate down-type block are both dual left-handed. -/
lemma isEquivariant_downLDownL_barDownBlock (f f' : Fin 3) (i : Fin 2) (cbd cQ : Fin 3)
    (wQ : Fin 2) :
    complexLorentzTensor.IsEquivariant ![.downL, .downL] repLorentzGroup
      (liftComponents ((fun p => LocalCovFieldAlgebra.barDownBlock f f' i p.1 cbd p.2 cQ wQ) ∘
          pairIdx)) :=
  isEquivariant_liftComponents_pair (S := complexLorentzTensor) (c1 := .downL) (c2 := .downL)
    (fun a b => LocalCovFieldAlgebra.barDownBlock f f' i a cbd b cQ wQ) fun Λ a b => by
    rw [toMatrix_rep_downL]
    simp only [barDownBlock]
    rw [LocalCovFieldAlgebra.repLorentz_mul_fixed_left Λ
      (X := fun a => FermionSector.bardComponent f ![] (a, cbd))
      (Y := fun a => FermionSector.QComponent f' ![] (a, cQ, wQ))
      (LocalCovFieldAlgebra.repLorentz_barHiggs_zero Λ ![] i)
      (FermionSector.repLorentz_bardComponent Λ f ![] (a, cbd))
      (FermionSector.repLorentz_QComponent Λ f' ![] (b, cQ, wQ))]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      simp [Matrix.transpose_apply, SL2C.inverse_coe]

/-- A hypercharge transformation fixes every component of the conjugate down-type block,
  the three hypercharges `3`, `-2` and `-1` cancelling. -/
lemma repGauge_u1_barDownBlock (t : unitary ℂ) (f f' : Fin 3) (i sbd : Fin 2)
    (cbd : Fin 3) (sQ : Fin 2) (cQ : Fin 3) (wQ : Fin 2) :
    repGaugeGroupI ((1, 1, t) : GaugeGroupI) (LocalCovFieldAlgebra.barDownBlock f f' i
      sbd cbd sQ cQ wQ)
      = LocalCovFieldAlgebra.barDownBlock f f' i sbd cbd sQ cQ wQ := by
  have ht : star (t : ℂ) * (t : ℂ) = 1 := t.2.1
  rw [barDownBlock, repGaugeGroupI_mul, repGaugeGroupI_mul,
    LocalCovFieldAlgebra.repGauge_u1_barHiggs, FermionSector.repGauge_u1_bard,
      FermionSector.repGauge_u1_Q, smul_mul_smul_comm,
    smul_mul_smul_comm,
    show (t : ℂ) ^ 3 * ((star (t : ℂ)) ^ 2 * star (t : ℂ)) = 1 from by
      rw [show (t : ℂ) ^ 3 * ((star (t : ℂ)) ^ 2 * star (t : ℂ))
        = (star (t : ℂ) * (t : ℂ)) ^ 3 from by ring, ht, one_pow],
    one_smul]

/-- The colour contraction of the conjugate down-type block. -/
noncomputable def barDownBlockColour (f f' : Fin 3)
    (i sbd sQ wQ : Fin 2) : fieldData.LocalCovFieldAlgebra :=
  ColourFundAntiFund.deltaContraction
    (fun l : Fin 2 → Fin 3 => LocalCovFieldAlgebra.barDownBlock f f' i sbd (l 0) sQ (l 1) wQ)

/-- The colour contraction of the conjugate down-type block written out. -/
lemma barDownBlockColour_eq (f f' : Fin 3) (i sbd sQ wQ : Fin 2) :
    LocalCovFieldAlgebra.barDownBlockColour f f' i sbd sQ wQ
      = ∑ a : Fin 3, LocalCovFieldAlgebra.barDownBlock f f' i sbd a sQ a wQ := by
  simp [barDownBlockColour, ColourFundAntiFund.deltaContraction]

/-- The colour contraction of the conjugate down-type block still carries one fundamental
  and one anti-fundamental isospin index. -/
lemma isEquivariant_isospinFundAntiFund_barDownBlockColour (f f' : Fin 3) (sbd sQ : Fin 2) :
    (suTensor 2).IsEquivariant ![.fund, .antiFund] (repGaugeGroupI.comp GaugeGroupI.ofSU2)
      (liftComponents ((fun l : Fin 2 → Fin 2 =>
        LocalCovFieldAlgebra.barDownBlockColour f f' (l 0) sbd sQ (l 1)) ∘ fundAntiFundIdx)) := by
  simp only [LocalCovFieldAlgebra.barDownBlockColour_eq]
  exact IsospinFundAntiFund.sum fun a =>
    LocalCovFieldAlgebra.isEquivariant_isospinFundAntiFund_barDownBlock f f' sbd a sQ a

/-- The isospin contraction of the colour-contracted conjugate down-type block. -/
noncomputable def barDownBlockIsospin (f f' : Fin 3)
    (sbd sQ : Fin 2) : fieldData.LocalCovFieldAlgebra :=
  IsospinFundAntiFund.deltaContraction
    (fun l : Fin 2 → Fin 2 => LocalCovFieldAlgebra.barDownBlockColour f f' (l 0) sbd sQ (l 1))

/-- The doubly contracted conjugate down-type block written out. -/
lemma barDownBlockIsospin_eq (f f' : Fin 3) (sbd sQ : Fin 2) :
    LocalCovFieldAlgebra.barDownBlockIsospin f f' sbd sQ
      = ∑ p : Fin 2 × Fin 3, LocalCovFieldAlgebra.barDownBlock f f' p.1 sbd p.2 sQ p.2 p.1 := by
  rw [barDownBlockIsospin, IsospinFundAntiFund.deltaContraction,
    LocalCovFieldAlgebra.barDownBlockColour_eq, LocalCovFieldAlgebra.barDownBlockColour_eq,
      Fintype.sum_prod_type, Fin.sum_univ_two]
  simp

/-- The doubly contracted conjugate down-type block carries two dual left-handed Weyl
  indices. -/
lemma isEquivariant_downLDownL_barDownBlockIsospin (f f' : Fin 3) :
    complexLorentzTensor.IsEquivariant ![.downL, .downL] repLorentzGroup
      (liftComponents ((fun p => LocalCovFieldAlgebra.barDownBlockIsospin f f' p.1 p.2) ∘
          pairIdx)) := by
  simp only [LocalCovFieldAlgebra.barDownBlockIsospin_eq, liftComponents_comp_sum]
  exact TensorSpecies.IsEquivariant.sum _ fun p _ =>
    LocalCovFieldAlgebra.isEquivariant_downLDownL_barDownBlock f f' p.1 p.2 p.2 p.1

/-- The conjugate down-type Yukawa term of the family pair `(f, f')`. It is the image of the metric
  `εL'` under the map with the contracted block as its components. -/
noncomputable def barDownYukawa (f f' : Fin 3) : fieldData.LocalCovFieldAlgebra :=
  liftComponents (S := complexLorentzTensor) (c := ![.downL, .downL])
    ((fun p => LocalCovFieldAlgebra.barDownBlockIsospin f f' p.1 p.2) ∘ pairIdx) εL'

/-!

## B. The invariance of the conjugate down-type Yukawa term, and its mass weight

-/

/-- The colour contraction of the conjugate down-type block is fixed by the colour
  factor. -/
lemma repGauge_su3_barDownBlockColour (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (i sbd sQ wQ : Fin 2) :
    repGaugeGroupI ((U, 1, 1) : GaugeGroupI) (LocalCovFieldAlgebra.barDownBlockColour
      f f' i sbd sQ wQ)
      = LocalCovFieldAlgebra.barDownBlockColour f f' i sbd sQ wQ :=
  ColourFundAntiFund.repGauge_deltaContraction
    (LocalCovFieldAlgebra.isEquivariant_colourFundAntiFund_barDownBlock f f' i sbd sQ wQ) U

/-- The doubly contracted conjugate down-type block is fixed by the colour factor. -/
lemma repGauge_su3_barDownBlockIsospin (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (sbd sQ : Fin 2) :
    repGaugeGroupI ((U, 1, 1) : GaugeGroupI) (LocalCovFieldAlgebra.barDownBlockIsospin
      f f' sbd sQ)
      = LocalCovFieldAlgebra.barDownBlockIsospin f f' sbd sQ := by
  rw [barDownBlockIsospin, IsospinFundAntiFund.deltaContraction, map_add,
    LocalCovFieldAlgebra.repGauge_su3_barDownBlockColour,
      LocalCovFieldAlgebra.repGauge_su3_barDownBlockColour]

/-- The doubly contracted conjugate down-type block is fixed by the isospin factor. -/
lemma repGauge_su2_barDownBlockIsospin (V : specialUnitaryGroup (Fin 2) ℂ) (f f' : Fin 3)
    (sbd sQ : Fin 2) :
    repGaugeGroupI ((1, V, 1) : GaugeGroupI) (LocalCovFieldAlgebra.barDownBlockIsospin
      f f' sbd sQ)
      = LocalCovFieldAlgebra.barDownBlockIsospin f f' sbd sQ :=
  IsospinFundAntiFund.repGauge_deltaContraction
    (LocalCovFieldAlgebra.isEquivariant_isospinFundAntiFund_barDownBlockColour f f' sbd sQ) V

/-- The doubly contracted conjugate down-type block is fixed by the hypercharge factor. -/
lemma repGauge_u1_barDownBlockIsospin (t : unitary ℂ) (f f' : Fin 3) (sbd sQ : Fin 2) :
    repGaugeGroupI ((1, 1, t) : GaugeGroupI) (LocalCovFieldAlgebra.barDownBlockIsospin
      f f' sbd sQ)
      = LocalCovFieldAlgebra.barDownBlockIsospin f f' sbd sQ := by
  rw [LocalCovFieldAlgebra.barDownBlockIsospin_eq, map_sum]
  exact Finset.sum_congr rfl fun p _ =>
    LocalCovFieldAlgebra.repGauge_u1_barDownBlock t f f' p.1 sbd p.2 sQ p.2 p.1

/-- The conjugate down-type Yukawa term is gauge invariant. -/
lemma repGauge_barDownYukawa (f f' : Fin 3) (g : GaugeGroupI) :
    repGaugeGroupI g (LocalCovFieldAlgebra.barDownYukawa f f') =
      LocalCovFieldAlgebra.barDownYukawa f f' := by
  refine forall_repGauge_eq_self (fun U => ?_) (fun V => ?_) (fun t => ?_) g <;>
    rw [barDownYukawa, map_liftComponents_comp]
  · simp only [LocalCovFieldAlgebra.repGauge_su3_barDownBlockIsospin]
  · simp only [LocalCovFieldAlgebra.repGauge_su2_barDownBlockIsospin]
  · simp only [LocalCovFieldAlgebra.repGauge_u1_barDownBlockIsospin]

/-- The conjugate down-type Yukawa term is Lorentz invariant. -/
lemma repLorentz_barDownYukawa (f f' : Fin 3) (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ (LocalCovFieldAlgebra.barDownYukawa f f') =
      LocalCovFieldAlgebra.barDownYukawa f f' :=
  (LocalCovFieldAlgebra.isEquivariant_downLDownL_barDownBlockIsospin f f').rep_map_of_invariant
    (fun g => TensorSpecies.metricTensor_invariant g) Λ

/-- Every component of the conjugate down-type block sits at mass weight eight in the
  Yukawa sector. -/
lemma barDownBlock_mem_sectorMassWeight (f f' : Fin 3) (i sbd : Fin 2) (cbd : Fin 3)
    (sQ : Fin 2) (cQ : Fin 3) (wQ : Fin 2) :
    LocalCovFieldAlgebra.barDownBlock f f' i sbd cbd sQ cQ wQ
      ∈ fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} 8 := by
  rw [LocalCovFieldAlgebra.sectorMassWeight_higgs_fermion_eight, barDownBlock]
  exact Submodule.mul_mem_mul (LocalCovFieldAlgebra.barHiggs_mem_derivSubmodule ![] i)
    (Submodule.mul_mem_mul (LocalCovFieldAlgebra.bardComponent_mem_derivSubmodule f ![] (sbd, cbd))
      (LocalCovFieldAlgebra.QComponent_mem_derivSubmodule f' ![] (sQ, cQ, wQ)))

/-- The conjugate down-type Yukawa term sits at mass weight eight in the Yukawa sector. -/
lemma barDownYukawa_mem_sectorMassWeight (f f' : Fin 3) :
    LocalCovFieldAlgebra.barDownYukawa f f'
      ∈ fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} 8 := by
  rw [barDownYukawa]
  refine liftComponents_comp_mem _ _ (fun p => ?_) _
  exact LocalCovFieldAlgebra.barDownBlockIsospin_eq _ _ _ _ ▸
    sum_mem fun p _ => LocalCovFieldAlgebra.barDownBlock_mem_sectorMassWeight _ _ _ _ _ _ _ _

/-!

## C. The conjugate up-type Yukawa term

The conjugate of the up type: the product `barH u barQ`.  Colour is `3 ⊗ 3̄` with the
conjugate quark doublet supplying the fundamental index, isospin is `2 ⊗ 2` — the conjugate
Higgs symbol and the conjugate quark doublet both carry the fundamental, so the invariant
is again the antisymmetric symbol — and both fermions are right-handed.

-/

/-- The components of the conjugate up-type Yukawa block `barH u barQ`. -/
noncomputable def barUpBlock (f f' : Fin 3) (i su : Fin 2) (cu : Fin 3) (sbQ : Fin 2)
    (cbQ : Fin 3) (wbQ : Fin 2) : fieldData.LocalCovFieldAlgebra :=
  ScalarSector.barHiggs ![] i * (FermionSector.uComponent f ![] (su, cu) *
    FermionSector.barQComponent f' ![] (sbQ, cbQ, wbQ))

/-- The two colour indices of the conjugate up-type block carry one fundamental and one
  anti-fundamental `su(3)` index, the conjugate quark doublet supplying the fundamental
  one. -/
lemma isEquivariant_colourFundAntiFund_barUpBlock (f f' : Fin 3) (i su sbQ wbQ : Fin 2) :
    (suTensor 3).IsEquivariant ![.fund, .antiFund] (repGaugeGroupI.comp GaugeGroupI.ofSU3)
      (liftComponents ((fun l : Fin 2 → Fin 3 => LocalCovFieldAlgebra.barUpBlock f f' i su (l 1) sbQ
          (l 0) wbQ) ∘ fundAntiFundIdx)) :=
  ColourFundAntiFund.of_law fun U l => by
    simp only [barUpBlock]
    rw [LocalCovFieldAlgebra.repGauge_mul_fixed_left (U, 1, 1)
      (X := fun a => FermionSector.uComponent f ![] (su, a))
      (Y := fun a => FermionSector.barQComponent f' ![] (sbQ, a, wbQ))
      (LocalCovFieldAlgebra.repGauge_su3_barHiggs U ![] i) (FermionSector.repGauge_su3_u U f
        ![] su (l 1))
      (FermionSector.repGauge_su3_barQ U f' ![] sbQ (l 0) wbQ), Physlib.Fin.sum_fin_two_arrow]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [mul_comm]

/-- The two isospin indices of the conjugate up-type block are both fundamental. The
  conjugate Higgs symbol and the conjugate quark doublet both carry the fundamental of
  `su(2)`. -/
lemma isEquivariant_isospinFundFund_barUpBlock (f f' : Fin 3) (su : Fin 2) (cu : Fin 3)
    (sbQ : Fin 2) (cbQ : Fin 3) :
    (suTensor 2).IsEquivariant (fun _ : Fin 2 => .fund) (repGaugeGroupI.comp GaugeGroupI.ofSU2)
      (liftComponents (fun l : Fin 2 → Fin 2 => LocalCovFieldAlgebra.barUpBlock f f' (l 0) su cu sbQ
          cbQ (l 1))) :=
  IsospinFundFund.of_law fun V l => by
    simp only [barUpBlock]
    rw [LocalCovFieldAlgebra.repGauge_mul_fixed_mid (1, V, 1) (A := fun a => ScalarSector.barHiggs
      ![] a)
      (Y := fun a => FermionSector.barQComponent f' ![] (sbQ, cbQ, a))
      (LocalCovFieldAlgebra.repGauge_su2_barHiggs V ![] (l 0)) (FermionSector.repGauge_su2_u
        V f ![] (su, cu))
      (FermionSector.repGauge_su2_barQ V f' ![] sbQ cbQ (l 1)), Physlib.Fin.sum_fin_two_arrow]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The two spinor indices of the conjugate up-type block are both dual right-handed. -/
lemma isEquivariant_downRDownR_barUpBlock (f f' : Fin 3) (i : Fin 2) (cu cbQ : Fin 3)
    (wbQ : Fin 2) :
    complexLorentzTensor.IsEquivariant ![.downR, .downR] repLorentzGroup
      (liftComponents ((fun p => LocalCovFieldAlgebra.barUpBlock f f' i p.1 cu p.2 cbQ wbQ) ∘
          pairIdx)) :=
  isEquivariant_liftComponents_pair (S := complexLorentzTensor) (c1 := .downR) (c2 := .downR)
    (fun a b => LocalCovFieldAlgebra.barUpBlock f f' i a cu b cbQ wbQ) fun Λ a b => by
    rw [toMatrix_rep_downR]
    simp only [barUpBlock]
    rw [LocalCovFieldAlgebra.repLorentz_mul_fixed_left Λ
      (X := fun a => FermionSector.uComponent f ![] (a, cu))
      (Y := fun a => FermionSector.barQComponent f' ![] (a, cbQ, wbQ))
      (LocalCovFieldAlgebra.repLorentz_barHiggs_zero Λ ![] i)
      (FermionSector.repLorentz_uComponent Λ f ![] (a, cu))
      (FermionSector.repLorentz_barQComponent Λ f' ![] (b, cbQ, wbQ))]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      simp [Matrix.conjTranspose_apply, SL2C.inverse_coe]

/-- A hypercharge transformation fixes every component of the conjugate up-type block, the
  three hypercharges `3`, `-4` and `1` cancelling. -/
lemma repGauge_u1_barUpBlock (t : unitary ℂ) (f f' : Fin 3) (i su : Fin 2) (cu : Fin 3)
    (sbQ : Fin 2) (cbQ : Fin 3) (wbQ : Fin 2) :
    repGaugeGroupI ((1, 1, t) : GaugeGroupI) (LocalCovFieldAlgebra.barUpBlock f f' i
      su cu sbQ cbQ wbQ)
      = LocalCovFieldAlgebra.barUpBlock f f' i su cu sbQ cbQ wbQ := by
  have ht : star (t : ℂ) * (t : ℂ) = 1 := t.2.1
  rw [barUpBlock, repGaugeGroupI_mul, repGaugeGroupI_mul,
    LocalCovFieldAlgebra.repGauge_u1_barHiggs,
    FermionSector.repGauge_u1_u, FermionSector.repGauge_u1_barQ, smul_mul_smul_comm,
      smul_mul_smul_comm,
    show (t : ℂ) ^ 3 * ((star (t : ℂ)) ^ 4 * (t : ℂ)) = 1 from by
      rw [show (t : ℂ) ^ 3 * ((star (t : ℂ)) ^ 4 * (t : ℂ))
        = (star (t : ℂ) * (t : ℂ)) ^ 4 from by ring, ht, one_pow],
    one_smul]

/-- The colour contraction of the conjugate up-type block. -/
noncomputable def barUpBlockColour (f f' : Fin 3)
    (i su sbQ wbQ : Fin 2) : fieldData.LocalCovFieldAlgebra :=
  ColourFundAntiFund.deltaContraction
    (fun l : Fin 2 → Fin 3 => LocalCovFieldAlgebra.barUpBlock f f' i su (l 1) sbQ (l 0) wbQ)

/-- The colour contraction of the conjugate up-type block written out. -/
lemma barUpBlockColour_eq (f f' : Fin 3) (i su sbQ wbQ : Fin 2) :
    LocalCovFieldAlgebra.barUpBlockColour f f' i su sbQ wbQ
      = ∑ a : Fin 3, LocalCovFieldAlgebra.barUpBlock f f' i su a sbQ a wbQ := by
  simp [barUpBlockColour, ColourFundAntiFund.deltaContraction]

/-- The colour contraction of the conjugate up-type block still carries two fundamental
  isospin indices. -/
lemma isEquivariant_isospinFundFund_barUpBlockColour (f f' : Fin 3) (su sbQ : Fin 2) :
    (suTensor 2).IsEquivariant (fun _ : Fin 2 => .fund) (repGaugeGroupI.comp GaugeGroupI.ofSU2)
      (liftComponents (fun l : Fin 2 → Fin 2 => LocalCovFieldAlgebra.barUpBlockColour f f' (l 0) su
          sbQ (l 1))) := by
  simp only [LocalCovFieldAlgebra.barUpBlockColour_eq]
  exact IsospinFundFund.sum fun a => LocalCovFieldAlgebra.isEquivariant_isospinFundFund_barUpBlock f
      f' su a
    sbQ a

/-- The isospin contraction of the colour-contracted conjugate up-type block, by the
  antisymmetric symbol. -/
noncomputable def barUpBlockIsospin (f f' : Fin 3)
    (su sbQ : Fin 2) : fieldData.LocalCovFieldAlgebra :=
  IsospinFundFund.epsilonContraction
    (fun l : Fin 2 → Fin 2 => LocalCovFieldAlgebra.barUpBlockColour f f' (l 0) su sbQ (l 1))

/-- The doubly contracted conjugate up-type block written out. -/
lemma barUpBlockIsospin_eq (f f' : Fin 3) (su sbQ : Fin 2) :
    LocalCovFieldAlgebra.barUpBlockIsospin f f' su sbQ =
      (∑ a : Fin 3, LocalCovFieldAlgebra.barUpBlock f f' 0 su a sbQ a 1)
      - ∑ a : Fin 3, LocalCovFieldAlgebra.barUpBlock f f' 1 su a sbQ a 0 := by
  rw [barUpBlockIsospin, IsospinFundFund.epsilonContraction]
  simp [LocalCovFieldAlgebra.barUpBlockColour_eq]

/-- The doubly contracted conjugate up-type block carries two dual right-handed Weyl
  indices. -/
lemma isEquivariant_downRDownR_barUpBlockIsospin (f f' : Fin 3) :
    complexLorentzTensor.IsEquivariant ![.downR, .downR] repLorentzGroup
      (liftComponents ((fun p => LocalCovFieldAlgebra.barUpBlockIsospin f f' p.1 p.2) ∘
          pairIdx)) := by
  simp only [LocalCovFieldAlgebra.barUpBlockIsospin_eq, liftComponents_comp_sub,
      liftComponents_comp_sum]
  exact (TensorSpecies.IsEquivariant.sum _ fun a _ =>
    LocalCovFieldAlgebra.isEquivariant_downRDownR_barUpBlock f f' 0 a a 1).sub
    (TensorSpecies.IsEquivariant.sum _ fun a _ =>
        LocalCovFieldAlgebra.isEquivariant_downRDownR_barUpBlock
      f f' 1 a a 0)

/-- The conjugate up-type Yukawa term of the family pair `(f, f')`. It is the image of the metric
  `εR'` under the map with the contracted block as its components. -/
noncomputable def barUpYukawa (f f' : Fin 3) : fieldData.LocalCovFieldAlgebra :=
  liftComponents (S := complexLorentzTensor) (c := ![.downR, .downR])
    ((fun p => LocalCovFieldAlgebra.barUpBlockIsospin f f' p.1 p.2) ∘ pairIdx) εR'

/-!

## D. The invariance of the conjugate up-type Yukawa term, and its mass weight

-/

/-- The colour contraction of the conjugate up-type block is fixed by the colour factor. -/
lemma repGauge_su3_barUpBlockColour (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (i su sbQ wbQ : Fin 2) :
    repGaugeGroupI ((U, 1, 1) : GaugeGroupI) (LocalCovFieldAlgebra.barUpBlockColour f
      f' i su sbQ wbQ)
      = LocalCovFieldAlgebra.barUpBlockColour f f' i su sbQ wbQ :=
  ColourFundAntiFund.repGauge_deltaContraction
    (LocalCovFieldAlgebra.isEquivariant_colourFundAntiFund_barUpBlock f f' i su sbQ wbQ) U

/-- The doubly contracted conjugate up-type block is fixed by the colour factor. -/
lemma repGauge_su3_barUpBlockIsospin (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (su sbQ : Fin 2) :
    repGaugeGroupI ((U, 1, 1) : GaugeGroupI) (LocalCovFieldAlgebra.barUpBlockIsospin f
      f' su sbQ)
      = LocalCovFieldAlgebra.barUpBlockIsospin f f' su sbQ := by
  rw [barUpBlockIsospin, IsospinFundFund.epsilonContraction, map_sub,
    LocalCovFieldAlgebra.repGauge_su3_barUpBlockColour,
      LocalCovFieldAlgebra.repGauge_su3_barUpBlockColour]

/-- The doubly contracted conjugate up-type block is fixed by the isospin factor. -/
lemma repGauge_su2_barUpBlockIsospin (V : specialUnitaryGroup (Fin 2) ℂ) (f f' : Fin 3)
    (su sbQ : Fin 2) :
    repGaugeGroupI ((1, V, 1) : GaugeGroupI) (LocalCovFieldAlgebra.barUpBlockIsospin f
      f' su sbQ)
      = LocalCovFieldAlgebra.barUpBlockIsospin f f' su sbQ :=
  IsospinFundFund.repGauge_epsilonContraction
    (LocalCovFieldAlgebra.isEquivariant_isospinFundFund_barUpBlockColour f f' su sbQ) V

/-- The doubly contracted conjugate up-type block is fixed by the hypercharge factor. -/
lemma repGauge_u1_barUpBlockIsospin (t : unitary ℂ) (f f' : Fin 3) (su sbQ : Fin 2) :
    repGaugeGroupI ((1, 1, t) : GaugeGroupI) (LocalCovFieldAlgebra.barUpBlockIsospin f
      f' su sbQ)
      = LocalCovFieldAlgebra.barUpBlockIsospin f f' su sbQ := by
  rw [LocalCovFieldAlgebra.barUpBlockIsospin_eq, map_sub, map_sum, map_sum]
  exact congrArg₂ _
    (Finset.sum_congr rfl fun a _ => LocalCovFieldAlgebra.repGauge_u1_barUpBlock t f f' 0 su a sbQ a
      1)
    (Finset.sum_congr rfl fun a _ => LocalCovFieldAlgebra.repGauge_u1_barUpBlock t f f' 1 su a sbQ a
      0)

/-- The conjugate up-type Yukawa term is gauge invariant. -/
lemma repGauge_barUpYukawa (f f' : Fin 3) (g : GaugeGroupI) :
    repGaugeGroupI g (LocalCovFieldAlgebra.barUpYukawa f f') =
      LocalCovFieldAlgebra.barUpYukawa f f' := by
  refine forall_repGauge_eq_self (fun U => ?_) (fun V => ?_) (fun t => ?_) g <;>
    rw [barUpYukawa, map_liftComponents_comp]
  · simp only [LocalCovFieldAlgebra.repGauge_su3_barUpBlockIsospin]
  · simp only [LocalCovFieldAlgebra.repGauge_su2_barUpBlockIsospin]
  · simp only [LocalCovFieldAlgebra.repGauge_u1_barUpBlockIsospin]

/-- The conjugate up-type Yukawa term is Lorentz invariant. -/
lemma repLorentz_barUpYukawa (f f' : Fin 3) (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ (LocalCovFieldAlgebra.barUpYukawa f f') =
      LocalCovFieldAlgebra.barUpYukawa f f' :=
  (LocalCovFieldAlgebra.isEquivariant_downRDownR_barUpBlockIsospin f f').rep_map_of_invariant
    (fun g => TensorSpecies.metricTensor_invariant g) Λ

/-- Every component of the conjugate up-type block sits at mass weight eight in the Yukawa
  sector. -/
lemma barUpBlock_mem_sectorMassWeight (f f' : Fin 3) (i su : Fin 2) (cu : Fin 3)
    (sbQ : Fin 2) (cbQ : Fin 3) (wbQ : Fin 2) :
    LocalCovFieldAlgebra.barUpBlock f f' i su cu sbQ cbQ wbQ
      ∈ fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} 8 := by
  rw [LocalCovFieldAlgebra.sectorMassWeight_higgs_fermion_eight, barUpBlock]
  exact Submodule.mul_mem_mul (LocalCovFieldAlgebra.barHiggs_mem_derivSubmodule ![] i)
    (Submodule.mul_mem_mul (LocalCovFieldAlgebra.uComponent_mem_derivSubmodule f ![] (su, cu))
      (LocalCovFieldAlgebra.barQComponent_mem_derivSubmodule f' ![] (sbQ, cbQ, wbQ)))

/-- The conjugate up-type Yukawa term sits at mass weight eight in the Yukawa sector. -/
lemma barUpYukawa_mem_sectorMassWeight (f f' : Fin 3) :
    LocalCovFieldAlgebra.barUpYukawa f f'
      ∈ fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} 8 := by
  have hiso : ∀ su sbQ : Fin 2, LocalCovFieldAlgebra.barUpBlockIsospin f f' su sbQ
      ∈ fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} 8 := by
    intro su sbQ
    rw [LocalCovFieldAlgebra.barUpBlockIsospin_eq]
    exact Submodule.sub_mem _
      (sum_mem fun a _ => LocalCovFieldAlgebra.barUpBlock_mem_sectorMassWeight _ _ _ _ _ _ _ _)
      (sum_mem fun a _ => LocalCovFieldAlgebra.barUpBlock_mem_sectorMassWeight _ _ _ _ _ _ _ _)
  exact liftComponents_comp_mem (S := complexLorentzTensor) (c := ![.downR, .downR]) pairIdx
    (fun p => LocalCovFieldAlgebra.barUpBlockIsospin f f' p.1 p.2) (fun p => hiso p.1 p.2) εR'

/-!

## E. The conjugate charged-lepton Yukawa term

The conjugate of the charged-lepton type: the product `barH L bare`.  As with its
unconjugated partner there is no colour at all, so the colour step is plain invariance;
isospin is `2 ⊗ 2̄` with the conjugate Higgs symbol supplying the fundamental index, and
both fermions are left-handed.

-/

/-- The components of the conjugate charged-lepton Yukawa block `barH L bare`. -/
noncomputable def barLeptonBlock (f f' : Fin 3)
    (i sL wL sbe : Fin 2) : fieldData.LocalCovFieldAlgebra :=
  ScalarSector.barHiggs ![] i * (FermionSector.LComponent f ![] (sL, wL) *
    FermionSector.bareComponent f' ![] sbe)

/-- The conjugate lepton block is colour invariant outright. -/
lemma repGauge_su3_barLeptonBlock (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (i sL wL sbe : Fin 2) :
    repGaugeGroupI ((U, 1, 1) : GaugeGroupI) (LocalCovFieldAlgebra.barLeptonBlock f f'
      i sL wL sbe)
      = LocalCovFieldAlgebra.barLeptonBlock f f' i sL wL sbe := by
  rw [barLeptonBlock, repGaugeGroupI_mul, repGaugeGroupI_mul,
    LocalCovFieldAlgebra.repGauge_su3_barHiggs, FermionSector.repGauge_su3_L,
      FermionSector.repGauge_su3_bare]

/-- The two isospin indices of the conjugate lepton block carry one fundamental and one
  anti-fundamental `su(2)` index, the conjugate Higgs symbol supplying the fundamental
  one. -/
lemma isEquivariant_isospinFundAntiFund_barLeptonBlock (f f' : Fin 3) (sL sbe : Fin 2) :
    (suTensor 2).IsEquivariant ![.fund, .antiFund] (repGaugeGroupI.comp GaugeGroupI.ofSU2)
      (liftComponents ((fun l : Fin 2 → Fin 2 => LocalCovFieldAlgebra.barLeptonBlock f f' (l 0) sL
          (l 1) sbe) ∘ fundAntiFundIdx)) :=
  IsospinFundAntiFund.of_law fun V l => by
    simp only [barLeptonBlock]
    rw [LocalCovFieldAlgebra.repGauge_mul_fixed_right (1, V, 1)
      (A := fun a => ScalarSector.barHiggs ![] a)
      (X := fun a => FermionSector.LComponent f ![] (sL, a))
      (LocalCovFieldAlgebra.repGauge_su2_barHiggs V ![] (l 0)) (FermionSector.repGauge_su2_L
        V f ![] sL (l 1))
      (FermionSector.repGauge_su2_bare V f' ![] sbe), Physlib.Fin.sum_fin_two_arrow]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The two spinor indices of the conjugate lepton block are both dual left-handed. -/
lemma isEquivariant_downLDownL_barLeptonBlock (f f' : Fin 3) (i wL : Fin 2) :
    complexLorentzTensor.IsEquivariant ![.downL, .downL] repLorentzGroup
      (liftComponents ((fun p => LocalCovFieldAlgebra.barLeptonBlock f f' i p.1 wL p.2) ∘
        pairIdx)) :=
  isEquivariant_liftComponents_pair (S := complexLorentzTensor) (c1 := .downL) (c2 := .downL)
    (fun a b => LocalCovFieldAlgebra.barLeptonBlock f f' i a wL b) fun Λ a b => by
    rw [toMatrix_rep_downL]
    simp only [barLeptonBlock]
    rw [LocalCovFieldAlgebra.repLorentz_mul_fixed_left Λ
      (X := fun a => FermionSector.LComponent f ![] (a, wL))
      (Y := fun a => FermionSector.bareComponent f' ![] a)
      (LocalCovFieldAlgebra.repLorentz_barHiggs_zero Λ ![] i)
      (FermionSector.repLorentz_LComponent Λ f ![] (a, wL))
      (FermionSector.repLorentz_bareComponent Λ f' ![] b)]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      simp [Matrix.transpose_apply, SL2C.inverse_coe]

/-- A hypercharge transformation fixes every component of the conjugate lepton block, the
  three hypercharges `3`, `3` and `-6` cancelling. -/
lemma repGauge_u1_barLeptonBlock (t : unitary ℂ) (f f' : Fin 3) (i sL wL sbe : Fin 2) :
    repGaugeGroupI ((1, 1, t) : GaugeGroupI) (LocalCovFieldAlgebra.barLeptonBlock f f'
      i sL wL sbe)
      = LocalCovFieldAlgebra.barLeptonBlock f f' i sL wL sbe := by
  have ht : star (t : ℂ) * (t : ℂ) = 1 := t.2.1
  rw [barLeptonBlock, repGaugeGroupI_mul, repGaugeGroupI_mul,
    LocalCovFieldAlgebra.repGauge_u1_barHiggs, FermionSector.repGauge_u1_L,
      FermionSector.repGauge_u1_bare, smul_mul_smul_comm,
    smul_mul_smul_comm,
    show (t : ℂ) ^ 3 * ((t : ℂ) ^ 3 * (star (t : ℂ)) ^ 6) = 1 from by
      rw [show (t : ℂ) ^ 3 * ((t : ℂ) ^ 3 * (star (t : ℂ)) ^ 6)
        = (star (t : ℂ) * (t : ℂ)) ^ 6 from by ring, ht, one_pow],
    one_smul]

/-- The isospin contraction of the conjugate lepton block. -/
noncomputable def barLeptonBlockIsospin (f f' : Fin 3)
    (sL sbe : Fin 2) : fieldData.LocalCovFieldAlgebra :=
  IsospinFundAntiFund.deltaContraction
    (fun l : Fin 2 → Fin 2 => LocalCovFieldAlgebra.barLeptonBlock f f' (l 0) sL (l 1) sbe)

/-- The isospin contraction of the conjugate lepton block written out. -/
lemma barLeptonBlockIsospin_eq (f f' : Fin 3) (sL sbe : Fin 2) :
    LocalCovFieldAlgebra.barLeptonBlockIsospin f f' sL sbe
      = ∑ w : Fin 2, LocalCovFieldAlgebra.barLeptonBlock f f' w sL w sbe := by
  rw [barLeptonBlockIsospin, IsospinFundAntiFund.deltaContraction, Fin.sum_univ_two]
  simp

/-- The contracted conjugate lepton block carries two dual left-handed Weyl indices. -/
lemma isEquivariant_downLDownL_barLeptonBlockIsospin (f f' : Fin 3) :
    complexLorentzTensor.IsEquivariant ![.downL, .downL] repLorentzGroup
      (liftComponents ((fun p => LocalCovFieldAlgebra.barLeptonBlockIsospin f f' p.1 p.2) ∘
          pairIdx)) := by
  simp only [LocalCovFieldAlgebra.barLeptonBlockIsospin_eq, liftComponents_comp_sum]
  exact TensorSpecies.IsEquivariant.sum _ fun w _ =>
    LocalCovFieldAlgebra.isEquivariant_downLDownL_barLeptonBlock f f' w w

/-- The conjugate charged-lepton Yukawa term of the family pair `(f, f')`. It is the image of the
  metric `εL'` under the map with the contracted block as its components. -/
noncomputable def barLeptonYukawa (f f' : Fin 3) : fieldData.LocalCovFieldAlgebra :=
  liftComponents (S := complexLorentzTensor) (c := ![.downL, .downL])
    ((fun p => LocalCovFieldAlgebra.barLeptonBlockIsospin f f' p.1 p.2) ∘ pairIdx)
    εL'

/-!

## F. The invariance of the conjugate charged-lepton Yukawa term, and its mass weight

-/

/-- The contracted conjugate lepton block is fixed by the colour factor. -/
lemma repGauge_su3_barLeptonBlockIsospin (U : specialUnitaryGroup (Fin 3) ℂ)
    (f f' : Fin 3) (sL sbe : Fin 2) :
    repGaugeGroupI ((U, 1, 1) : GaugeGroupI)
      (LocalCovFieldAlgebra.barLeptonBlockIsospin f f' sL sbe)
      = LocalCovFieldAlgebra.barLeptonBlockIsospin f f' sL sbe := by
  rw [LocalCovFieldAlgebra.barLeptonBlockIsospin_eq, map_sum]
  exact Finset.sum_congr rfl fun w _ => LocalCovFieldAlgebra.repGauge_su3_barLeptonBlock U f f' w sL
    w sbe

/-- The contracted conjugate lepton block is fixed by the isospin factor. -/
lemma repGauge_su2_barLeptonBlockIsospin (V : specialUnitaryGroup (Fin 2) ℂ)
    (f f' : Fin 3) (sL sbe : Fin 2) :
    repGaugeGroupI ((1, V, 1) : GaugeGroupI)
      (LocalCovFieldAlgebra.barLeptonBlockIsospin f f' sL sbe)
      = LocalCovFieldAlgebra.barLeptonBlockIsospin f f' sL sbe :=
  IsospinFundAntiFund.repGauge_deltaContraction
    (LocalCovFieldAlgebra.isEquivariant_isospinFundAntiFund_barLeptonBlock f f' sL sbe) V

/-- The contracted conjugate lepton block is fixed by the hypercharge factor. -/
lemma repGauge_u1_barLeptonBlockIsospin (t : unitary ℂ) (f f' : Fin 3) (sL sbe : Fin 2) :
    repGaugeGroupI ((1, 1, t) : GaugeGroupI)
      (LocalCovFieldAlgebra.barLeptonBlockIsospin f f' sL sbe)
      = LocalCovFieldAlgebra.barLeptonBlockIsospin f f' sL sbe := by
  rw [LocalCovFieldAlgebra.barLeptonBlockIsospin_eq, map_sum]
  exact Finset.sum_congr rfl fun w _ => LocalCovFieldAlgebra.repGauge_u1_barLeptonBlock t f f' w sL
    w sbe

/-- The conjugate charged-lepton Yukawa term is gauge invariant. -/
lemma repGauge_barLeptonYukawa (f f' : Fin 3) (g : GaugeGroupI) :
    repGaugeGroupI g (LocalCovFieldAlgebra.barLeptonYukawa f f') =
      LocalCovFieldAlgebra.barLeptonYukawa f f' := by
  refine forall_repGauge_eq_self (fun U => ?_) (fun V => ?_) (fun t => ?_) g <;>
    rw [barLeptonYukawa, map_liftComponents_comp]
  · simp only [LocalCovFieldAlgebra.repGauge_su3_barLeptonBlockIsospin]
  · simp only [LocalCovFieldAlgebra.repGauge_su2_barLeptonBlockIsospin]
  · simp only [LocalCovFieldAlgebra.repGauge_u1_barLeptonBlockIsospin]

/-- The conjugate charged-lepton Yukawa term is Lorentz invariant. -/
lemma repLorentz_barLeptonYukawa (f f' : Fin 3) (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ (LocalCovFieldAlgebra.barLeptonYukawa f f') =
      LocalCovFieldAlgebra.barLeptonYukawa f f' :=
  (LocalCovFieldAlgebra.isEquivariant_downLDownL_barLeptonBlockIsospin f f').rep_map_of_invariant
    (fun g => TensorSpecies.metricTensor_invariant g) Λ

/-- Every component of the conjugate lepton block sits at mass weight eight in the Yukawa
  sector. -/
lemma barLeptonBlock_mem_sectorMassWeight (f f' : Fin 3) (i sL wL sbe : Fin 2) :
    LocalCovFieldAlgebra.barLeptonBlock f f' i sL wL sbe
      ∈ fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} 8 := by
  rw [LocalCovFieldAlgebra.sectorMassWeight_higgs_fermion_eight, barLeptonBlock]
  exact Submodule.mul_mem_mul (LocalCovFieldAlgebra.barHiggs_mem_derivSubmodule ![] i)
    (Submodule.mul_mem_mul (LocalCovFieldAlgebra.LComponent_mem_derivSubmodule f ![] (sL, wL))
      (LocalCovFieldAlgebra.bareComponent_mem_derivSubmodule f' ![] sbe))

/-- The conjugate charged-lepton Yukawa term sits at mass weight eight in the Yukawa
  sector. -/
lemma barLeptonYukawa_mem_sectorMassWeight (f f' : Fin 3) :
    LocalCovFieldAlgebra.barLeptonYukawa f f'
      ∈ fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} 8 := by
  rw [barLeptonYukawa]
  refine liftComponents_comp_mem _ _ (fun p => ?_) _
  exact LocalCovFieldAlgebra.barLeptonBlockIsospin_eq _ _ _ _ ▸
    sum_mem fun w _ => LocalCovFieldAlgebra.barLeptonBlock_mem_sectorMassWeight _ _ _ _ _ _

/-!

## G. The Yukawa span

The six couplings, each joined over the nine family pairs, are the whole Yukawa content of
the sector at mass weight eight: six arbitrary `3 × 3` coupling matrices, and no matrix
written down anywhere.  The join lies inside the sector and inside both spaces of
invariants, which is the direction that makes the eventual classification an equivalence
rather than a one-way inclusion.  The six transposed blocks add nothing: by
`mul_mul_swap_eq_neg` their terms are minus these.

-/

/-- The span of the conjugate down-type Yukawa terms over the nine family pairs. -/
noncomputable def barDownYukawaSpan : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ⨆ (f : Fin 3) (f' : Fin 3), ℂ ∙ LocalCovFieldAlgebra.barDownYukawa f f'

/-- The span of the conjugate up-type Yukawa terms over the nine family pairs. -/
noncomputable def barUpYukawaSpan : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ⨆ (f : Fin 3) (f' : Fin 3), ℂ ∙ LocalCovFieldAlgebra.barUpYukawa f f'

/-- The span of the conjugate charged-lepton Yukawa terms over the nine family pairs. -/
noncomputable def barLeptonYukawaSpan : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ⨆ (f : Fin 3) (f' : Fin 3), ℂ ∙ LocalCovFieldAlgebra.barLeptonYukawa f f'

/-- The conjugate down-type Yukawa span sits at mass weight eight in the Yukawa sector. -/
lemma barDownYukawaSpan_le_sectorMassWeight :
    LocalCovFieldAlgebra.barDownYukawaSpan
      ≤ fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} 8 :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    (LocalCovFieldAlgebra.barDownYukawa_mem_sectorMassWeight f f')

/-- The conjugate down-type Yukawa span is a space of gauge invariants. -/
lemma barDownYukawaSpan_le_invariants : LocalCovFieldAlgebra.barDownYukawaSpan ≤
    repGaugeGroupI.invariants :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    ((Representation.mem_invariants _ _).2 (LocalCovFieldAlgebra.repGauge_barDownYukawa f f'))

/-- The conjugate down-type Yukawa span is a space of Lorentz invariants. -/
lemma barDownYukawaSpan_le_lorentzInvariants :
    LocalCovFieldAlgebra.barDownYukawaSpan ≤ repLorentzGroup.invariants :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    ((Representation.mem_invariants _ _).2 (LocalCovFieldAlgebra.repLorentz_barDownYukawa f f'))

/-- The conjugate up-type Yukawa span sits at mass weight eight in the Yukawa sector. -/
lemma barUpYukawaSpan_le_sectorMassWeight :
    LocalCovFieldAlgebra.barUpYukawaSpan
      ≤ fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} 8 :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    (LocalCovFieldAlgebra.barUpYukawa_mem_sectorMassWeight f f')

/-- The conjugate up-type Yukawa span is a space of gauge invariants. -/
lemma barUpYukawaSpan_le_invariants : LocalCovFieldAlgebra.barUpYukawaSpan ≤
    repGaugeGroupI.invariants :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    ((Representation.mem_invariants _ _).2 (LocalCovFieldAlgebra.repGauge_barUpYukawa f f'))

/-- The conjugate up-type Yukawa span is a space of Lorentz invariants. -/
lemma barUpYukawaSpan_le_lorentzInvariants : LocalCovFieldAlgebra.barUpYukawaSpan ≤
    repLorentzGroup.invariants :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    ((Representation.mem_invariants _ _).2 (LocalCovFieldAlgebra.repLorentz_barUpYukawa f f'))

/-- The conjugate charged-lepton Yukawa span sits at mass weight eight in the Yukawa
  sector. -/
lemma barLeptonYukawaSpan_le_sectorMassWeight :
    LocalCovFieldAlgebra.barLeptonYukawaSpan
      ≤ fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} 8 :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    (LocalCovFieldAlgebra.barLeptonYukawa_mem_sectorMassWeight f f')

/-- The conjugate charged-lepton Yukawa span is a space of gauge invariants. -/
lemma barLeptonYukawaSpan_le_invariants : LocalCovFieldAlgebra.barLeptonYukawaSpan ≤
    repGaugeGroupI.invariants :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    ((Representation.mem_invariants _ _).2 (LocalCovFieldAlgebra.repGauge_barLeptonYukawa f f'))

/-- The conjugate charged-lepton Yukawa span is a space of Lorentz invariants. -/
lemma barLeptonYukawaSpan_le_lorentzInvariants :
    LocalCovFieldAlgebra.barLeptonYukawaSpan ≤ repLorentzGroup.invariants :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    ((Representation.mem_invariants _ _).2 (LocalCovFieldAlgebra.repLorentz_barLeptonYukawa f f'))

/-- The Yukawa span of the Standard Model at mass weight eight, the join of the six
  couplings, each over the nine family pairs. -/
noncomputable def yukawaSpan : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  LocalCovFieldAlgebra.downYukawaSpan ⊔ LocalCovFieldAlgebra.upYukawaSpan ⊔
    LocalCovFieldAlgebra.leptonYukawaSpan
    ⊔ LocalCovFieldAlgebra.barDownYukawaSpan ⊔ LocalCovFieldAlgebra.barUpYukawaSpan ⊔
      LocalCovFieldAlgebra.barLeptonYukawaSpan

/-- The Yukawa span lies inside the gauge- and Lorentz-invariants of the Yukawa sector at
  mass weight eight. This is the easy direction of the classification. Every Yukawa term
  is an invariant of the right mass weight, so the eventual classification is an
  equivalence and not merely a one-way inclusion. -/
lemma yukawaSpan_le_inf :
    LocalCovFieldAlgebra.yukawaSpan ≤ fieldData.sectorMassWeight
      {FieldKind.scalar, FieldKind.fermion} 8
        ⊓ repGaugeGroupI.invariants ⊓ repLorentzGroup.invariants :=
  sup_le (sup_le (sup_le (sup_le (sup_le
    (le_inf (le_inf LocalCovFieldAlgebra.downYukawaSpan_le_sectorMassWeight
      LocalCovFieldAlgebra.downYukawaSpan_le_invariants)
      LocalCovFieldAlgebra.downYukawaSpan_le_lorentzInvariants)
    (le_inf (le_inf LocalCovFieldAlgebra.upYukawaSpan_le_sectorMassWeight
      LocalCovFieldAlgebra.upYukawaSpan_le_invariants)
      LocalCovFieldAlgebra.upYukawaSpan_le_lorentzInvariants))
    (le_inf (le_inf LocalCovFieldAlgebra.leptonYukawaSpan_le_sectorMassWeight
      LocalCovFieldAlgebra.leptonYukawaSpan_le_invariants)
        LocalCovFieldAlgebra.leptonYukawaSpan_le_lorentzInvariants))
    (le_inf (le_inf LocalCovFieldAlgebra.barDownYukawaSpan_le_sectorMassWeight
      LocalCovFieldAlgebra.barDownYukawaSpan_le_invariants)
        LocalCovFieldAlgebra.barDownYukawaSpan_le_lorentzInvariants))
    (le_inf (le_inf LocalCovFieldAlgebra.barUpYukawaSpan_le_sectorMassWeight
      LocalCovFieldAlgebra.barUpYukawaSpan_le_invariants)
      LocalCovFieldAlgebra.barUpYukawaSpan_le_lorentzInvariants))
    (le_inf (le_inf LocalCovFieldAlgebra.barLeptonYukawaSpan_le_sectorMassWeight
      LocalCovFieldAlgebra.barLeptonYukawaSpan_le_invariants)
        LocalCovFieldAlgebra.barLeptonYukawaSpan_le_lorentzInvariants)

end LocalCovFieldAlgebra

end StandardModel
