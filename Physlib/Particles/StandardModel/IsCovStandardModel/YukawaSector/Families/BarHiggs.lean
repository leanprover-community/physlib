/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsCovStandardModel.YukawaSector.Families.Higgs
/-!
# The Yukawa terms built on the conjugate Higgs symbol

## i. Overview

The remaining three couplings of the mass-weight-eight Yukawa sector are built on the
conjugate Higgs symbol: `barH bard Q`, `barH u barQ` and `barH L bare`.  Each is the
conjugate of one of the three couplings of `Families.Higgs`, and is the same computation
with every symbol replaced by its conjugate: fundamental and anti-fundamental indices
exchange, left- and right-handed spinors exchange, and every hypercharge changes sign.  So
the isospin structure of the conjugate up type is `2 ⊗ 2` where its partner had `2̄ ⊗ 2̄`,
and its invariant is again the antisymmetric symbol.

With these six couplings the twelve blocks are accounted for: the other six are the same
six with the two fermion factors exchanged, and by `mul_mul_swap_eq_neg` their terms are
minus these while by `mul_mul_piece_swap` their blocks are the same submodules.

## ii. Key results

- `barDownYukawa`, `barUpYukawa`, `barLeptonYukawa` : the three conjugate Yukawa terms.
- `isSU3FunAntiFun_barDownBlock`, `isSU2BiFundamental_barUpBlock` and the rest : the index
  laws of the three conjugate blocks.
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

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz Pointwise ComplexConjugate

namespace IsCovStandardModel

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  {H : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ HiggsVec →ₗ[ℂ] B}
  {barH : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B}
  {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
  {d : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ DownSinglet →ₗ[ℂ] B}
  {bard : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B}
  {u : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ UpSinglet →ₗ[ℂ] B}
  {baru : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B}
  {Q : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B}
  {barQ : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B}
  {L : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B}
  {barL : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B}
  {e : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B}
  {bare : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B}
  (h : IsCovStandardModel B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
    massWeightPoly H barH F d bard u baru Q barQ L barL e bare)

/-!

## A. The conjugate down-type Yukawa term

The conjugate of the down type: the product `barH bard Q`.  Colour is `3 ⊗ 3̄` with the
conjugate down singlet supplying the fundamental index, isospin is `2 ⊗ 2̄` with the
conjugate Higgs symbol supplying the fundamental index and the quark doublet the
anti-fundamental one, and both fermions are left-handed.

-/

/-- The components of the conjugate down-type Yukawa block `barH bard Q`: a conjugate
  Higgs symbol, a conjugate down-singlet symbol and a quark-doublet symbol, none carrying
  derivatives. -/
noncomputable def barDownBlock (f f' : Fin 3) (i sbd : Fin 2) (cbd : Fin 3) (sQ : Fin 2)
    (cQ : Fin 3) (wQ : Fin 2) : B :=
  h.isHiggsSector.barHiggs ![] i * (h.isFermionSector.bardComponent f ![] (sbd, cbd) *
    h.isFermionSector.QComponent f' ![] (sQ, cQ, wQ))

/-- The two colour indices of the conjugate down-type block carry one fundamental and one
  anti-fundamental `su(3)` index, the conjugate down singlet supplying the fundamental
  one. -/
lemma isSU3FunAntiFun_barDownBlock (f f' : Fin 3) (i sbd sQ wQ : Fin 2) :
    IsSU3FunAntiFun B repGauge
      (fun l : Fin 2 → Fin 3 => h.barDownBlock f f' i sbd (l 0) sQ (l 1) wQ) where
  repGauge_T U l := by
    simp only [barDownBlock]
    rw [h.repGauge_mul_fixed_left (U, 1, 1)
      (X := fun a => h.isFermionSector.bardComponent f ![] (sbd, a))
      (Y := fun a => h.isFermionSector.QComponent f' ![] (sQ, a, wQ))
      (h.repGauge_su3_barHiggs U ![] i) (h.repGauge_su3_bard U f ![] sbd (l 0))
      (h.repGauge_su3_Q U f' ![] sQ (l 1) wQ), IsSU3FunAntiFun.sum_pi_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The two isospin indices of the conjugate down-type block carry one fundamental and one
  anti-fundamental `su(2)` index, the conjugate Higgs symbol supplying the fundamental
  one. -/
lemma isSU2FunAntiFun_barDownBlock (f f' : Fin 3) (sbd : Fin 2) (cbd : Fin 3) (sQ : Fin 2)
    (cQ : Fin 3) :
    IsSU2FunAntiFun B repGauge
      (fun l : Fin 2 → Fin 2 => h.barDownBlock f f' (l 0) sbd cbd sQ cQ (l 1)) where
  repGauge_T V l := by
    simp only [barDownBlock]
    rw [h.repGauge_mul_fixed_mid (1, V, 1) (A := fun a => h.isHiggsSector.barHiggs ![] a)
      (Y := fun a => h.isFermionSector.QComponent f' ![] (sQ, cQ, a))
      (h.repGauge_su2_barHiggs V ![] (l 0)) (h.repGauge_su2_bard V f ![] (sbd, cbd))
      (h.repGauge_su2_Q V f' ![] sQ cQ (l 1)), IsSU2BiFundamental.sum_pi_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The two spinor indices of the conjugate down-type block are both dual left-handed. -/
lemma isBiDualLeftWeyl_barDownBlock (f f' : Fin 3) (i : Fin 2) (cbd cQ : Fin 3)
    (wQ : Fin 2) :
    IsBiDualLeftWeyl B repLorentz
      (fun l : Fin 2 × Fin 2 => h.barDownBlock f f' i l.1 cbd l.2 cQ wQ) where
  repLorentz_T Λ l := by
    simp only [barDownBlock]
    rw [h.repLorentz_mul_fixed_left Λ
      (X := fun a => h.isFermionSector.bardComponent f ![] (a, cbd))
      (Y := fun a => h.isFermionSector.QComponent f' ![] (a, cQ, wQ))
      (h.repLorentz_barHiggs_zero Λ ![] i)
      (h.isFermionSector.repLorentz_bardComponent Λ f ![] (l.1, cbd))
      (h.isFermionSector.repLorentz_QComponent Λ f' ![] (l.2, cQ, wQ))]
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      simp [Matrix.transpose_apply, SL2C.inverse_coe]

/-- A hypercharge transformation fixes every component of the conjugate down-type block,
  the three hypercharges `3`, `-2` and `-1` cancelling. -/
lemma repGauge_u1_barDownBlock (t : unitary ℂ) (f f' : Fin 3) (i sbd : Fin 2)
    (cbd : Fin 3) (sQ : Fin 2) (cQ : Fin 3) (wQ : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.barDownBlock f f' i sbd cbd sQ cQ wQ)
      = h.barDownBlock f f' i sbd cbd sQ cQ wQ := by
  have ht : star (t : ℂ) * (t : ℂ) = 1 := t.2.1
  rw [barDownBlock, h.isHiggsSector.rep_mul, h.isHiggsSector.rep_mul,
    h.repGauge_u1_barHiggs, h.repGauge_u1_bard, h.repGauge_u1_Q, smul_mul_smul_comm,
    smul_mul_smul_comm,
    show (t : ℂ) ^ 3 * ((star (t : ℂ)) ^ 2 * star (t : ℂ)) = 1 from by
      rw [show (t : ℂ) ^ 3 * ((star (t : ℂ)) ^ 2 * star (t : ℂ))
        = (star (t : ℂ) * (t : ℂ)) ^ 3 from by ring, ht, one_pow],
    one_smul]

/-- The colour contraction of the conjugate down-type block. -/
noncomputable def barDownBlockColour (f f' : Fin 3) (i sbd sQ wQ : Fin 2) : B :=
  IsSU3FunAntiFun.deltaContraction
    (fun l : Fin 2 → Fin 3 => h.barDownBlock f f' i sbd (l 0) sQ (l 1) wQ)

/-- The colour contraction of the conjugate down-type block written out. -/
lemma barDownBlockColour_eq (f f' : Fin 3) (i sbd sQ wQ : Fin 2) :
    h.barDownBlockColour f f' i sbd sQ wQ
      = ∑ a : Fin 3, h.barDownBlock f f' i sbd a sQ a wQ := by
  simp [barDownBlockColour, IsSU3FunAntiFun.deltaContraction]

/-- The colour contraction of the conjugate down-type block still carries one fundamental
  and one anti-fundamental isospin index. -/
lemma isSU2FunAntiFun_barDownBlockColour (f f' : Fin 3) (sbd sQ : Fin 2) :
    IsSU2FunAntiFun B repGauge
      (fun l : Fin 2 → Fin 2 => h.barDownBlockColour f f' (l 0) sbd sQ (l 1)) := by
  simp only [h.barDownBlockColour_eq]
  exact IsSU2FunAntiFun.sum fun a => h.isSU2FunAntiFun_barDownBlock f f' sbd a sQ a

/-- The isospin contraction of the colour-contracted conjugate down-type block. -/
noncomputable def barDownBlockIsospin (f f' : Fin 3) (sbd sQ : Fin 2) : B :=
  IsSU2FunAntiFun.deltaContraction
    (fun l : Fin 2 → Fin 2 => h.barDownBlockColour f f' (l 0) sbd sQ (l 1))

/-- The doubly contracted conjugate down-type block written out. -/
lemma barDownBlockIsospin_eq (f f' : Fin 3) (sbd sQ : Fin 2) :
    h.barDownBlockIsospin f f' sbd sQ
      = ∑ p : Fin 2 × Fin 3, h.barDownBlock f f' p.1 sbd p.2 sQ p.2 p.1 := by
  rw [barDownBlockIsospin, IsSU2FunAntiFun.deltaContraction, h.barDownBlockColour_eq,
    h.barDownBlockColour_eq, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp

/-- The doubly contracted conjugate down-type block carries two dual left-handed Weyl
  indices. -/
lemma isBiDualLeftWeyl_barDownBlockIsospin (f f' : Fin 3) :
    IsBiDualLeftWeyl B repLorentz
      (fun l : Fin 2 × Fin 2 => h.barDownBlockIsospin f f' l.1 l.2) := by
  simp only [h.barDownBlockIsospin_eq]
  exact isBiDualLeftWeyl_sum fun p =>
    h.isBiDualLeftWeyl_barDownBlock f f' p.1 p.2 p.2 p.1

/-- The conjugate down-type Yukawa term of the family pair `(f, f')`. -/
noncomputable def barDownYukawa (f f' : Fin 3) : B :=
  IsBiLeftWeyl.epsilonContraction
    (T := fun l : Fin 2 × Fin 2 => h.barDownBlockIsospin f f' l.1 l.2)

/-!

## B. The invariance of the conjugate down-type Yukawa term, and its mass weight

-/

/-- The colour contraction of the conjugate down-type block is fixed by the colour
  factor. -/
lemma repGauge_su3_barDownBlockColour (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (i sbd sQ wQ : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.barDownBlockColour f f' i sbd sQ wQ)
      = h.barDownBlockColour f f' i sbd sQ wQ :=
  IsSU3FunAntiFun.repGauge_deltaContraction
    (h.isSU3FunAntiFun_barDownBlock f f' i sbd sQ wQ) U

/-- The doubly contracted conjugate down-type block is fixed by the colour factor. -/
lemma repGauge_su3_barDownBlockIsospin (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (sbd sQ : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.barDownBlockIsospin f f' sbd sQ)
      = h.barDownBlockIsospin f f' sbd sQ := by
  rw [barDownBlockIsospin, IsSU2FunAntiFun.deltaContraction, map_add,
    h.repGauge_su3_barDownBlockColour, h.repGauge_su3_barDownBlockColour]

/-- The doubly contracted conjugate down-type block is fixed by the isospin factor. -/
lemma repGauge_su2_barDownBlockIsospin (V : specialUnitaryGroup (Fin 2) ℂ) (f f' : Fin 3)
    (sbd sQ : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.barDownBlockIsospin f f' sbd sQ)
      = h.barDownBlockIsospin f f' sbd sQ :=
  IsSU2FunAntiFun.repGauge_deltaContraction
    (h.isSU2FunAntiFun_barDownBlockColour f f' sbd sQ) V

/-- The doubly contracted conjugate down-type block is fixed by the hypercharge factor. -/
lemma repGauge_u1_barDownBlockIsospin (t : unitary ℂ) (f f' : Fin 3) (sbd sQ : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.barDownBlockIsospin f f' sbd sQ)
      = h.barDownBlockIsospin f f' sbd sQ := by
  rw [h.barDownBlockIsospin_eq, map_sum]
  exact Finset.sum_congr rfl fun p _ =>
    h.repGauge_u1_barDownBlock t f f' p.1 sbd p.2 sQ p.2 p.1

/-- The conjugate down-type Yukawa term is gauge invariant. -/
lemma repGauge_barDownYukawa (f f' : Fin 3) (g : GaugeGroupI) :
    repGauge g (h.barDownYukawa f f') = h.barDownYukawa f f' := by
  refine forall_repGauge_eq_self (fun U => ?_) (fun V => ?_) (fun t => ?_) g <;>
    rw [barDownYukawa, IsBiLeftWeyl.epsilonContraction_eq, map_sub]
  · rw [h.repGauge_su3_barDownBlockIsospin, h.repGauge_su3_barDownBlockIsospin]
  · rw [h.repGauge_su2_barDownBlockIsospin, h.repGauge_su2_barDownBlockIsospin]
  · rw [h.repGauge_u1_barDownBlockIsospin, h.repGauge_u1_barDownBlockIsospin]

/-- The conjugate down-type Yukawa term is Lorentz invariant. -/
lemma repLorentz_barDownYukawa (f f' : Fin 3) (Λ : SL(2,ℂ)) :
    repLorentz Λ (h.barDownYukawa f f') = h.barDownYukawa f f' :=
  (h.isBiDualLeftWeyl_barDownBlockIsospin f f').repLorentz_epsilonContraction Λ

/-- Every component of the conjugate down-type block sits at mass weight eight in the
  Yukawa sector. -/
lemma barDownBlock_mem_sectorMassWeight (f f' : Fin 3) (i sbd : Fin 2) (cbd : Fin 3)
    (sQ : Fin 2) (cQ : Fin 3) (wQ : Fin 2) :
    h.barDownBlock f f' i sbd cbd sQ cQ wQ
      ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 := by
  rw [h.sectorMassWeight_higgs_fermion_eight, barDownBlock]
  exact Submodule.mul_mem_mul (h.barHiggs_mem_derivSubmodule ![] i)
    (Submodule.mul_mem_mul (h.bardComponent_mem_derivSubmodule f ![] (sbd, cbd))
      (h.QComponent_mem_derivSubmodule f' ![] (sQ, cQ, wQ)))

/-- The conjugate down-type Yukawa term sits at mass weight eight in the Yukawa sector. -/
lemma barDownYukawa_mem_sectorMassWeight (f f' : Fin 3) :
    h.barDownYukawa f f'
      ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 := by
  rw [barDownYukawa, IsBiLeftWeyl.epsilonContraction_eq]
  refine Submodule.sub_mem _ ?_ ?_ <;>
    exact h.barDownBlockIsospin_eq _ _ _ _ ▸
      sum_mem fun p _ => h.barDownBlock_mem_sectorMassWeight _ _ _ _ _ _ _ _

/-!

## C. The conjugate up-type Yukawa term

The conjugate of the up type: the product `barH u barQ`.  Colour is `3 ⊗ 3̄` with the
conjugate quark doublet supplying the fundamental index, isospin is `2 ⊗ 2` — the conjugate
Higgs symbol and the conjugate quark doublet both carry the fundamental, so the invariant
is again the antisymmetric symbol — and both fermions are right-handed.

-/

/-- The components of the conjugate up-type Yukawa block `barH u barQ`. -/
noncomputable def barUpBlock (f f' : Fin 3) (i su : Fin 2) (cu : Fin 3) (sbQ : Fin 2)
    (cbQ : Fin 3) (wbQ : Fin 2) : B :=
  h.isHiggsSector.barHiggs ![] i * (h.isFermionSector.uComponent f ![] (su, cu) *
    h.isFermionSector.barQComponent f' ![] (sbQ, cbQ, wbQ))

/-- The two colour indices of the conjugate up-type block carry one fundamental and one
  anti-fundamental `su(3)` index, the conjugate quark doublet supplying the fundamental
  one. -/
lemma isSU3FunAntiFun_barUpBlock (f f' : Fin 3) (i su sbQ wbQ : Fin 2) :
    IsSU3FunAntiFun B repGauge
      (fun l : Fin 2 → Fin 3 => h.barUpBlock f f' i su (l 1) sbQ (l 0) wbQ) where
  repGauge_T U l := by
    simp only [barUpBlock]
    rw [h.repGauge_mul_fixed_left (U, 1, 1)
      (X := fun a => h.isFermionSector.uComponent f ![] (su, a))
      (Y := fun a => h.isFermionSector.barQComponent f' ![] (sbQ, a, wbQ))
      (h.repGauge_su3_barHiggs U ![] i) (h.repGauge_su3_u U f ![] su (l 1))
      (h.repGauge_su3_barQ U f' ![] sbQ (l 0) wbQ), IsSU3FunAntiFun.sum_pi_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [mul_comm]

/-- The two isospin indices of the conjugate up-type block are both fundamental: the
  conjugate Higgs symbol and the conjugate quark doublet both carry the fundamental of
  `su(2)`. -/
lemma isSU2BiFundamental_barUpBlock (f f' : Fin 3) (su : Fin 2) (cu : Fin 3)
    (sbQ : Fin 2) (cbQ : Fin 3) :
    IsSU2BiFundamental B repGauge
      (fun l : Fin 2 → Fin 2 => h.barUpBlock f f' (l 0) su cu sbQ cbQ (l 1)) where
  repGauge_T V l := by
    simp only [barUpBlock]
    rw [h.repGauge_mul_fixed_mid (1, V, 1) (A := fun a => h.isHiggsSector.barHiggs ![] a)
      (Y := fun a => h.isFermionSector.barQComponent f' ![] (sbQ, cbQ, a))
      (h.repGauge_su2_barHiggs V ![] (l 0)) (h.repGauge_su2_u V f ![] (su, cu))
      (h.repGauge_su2_barQ V f' ![] sbQ cbQ (l 1)), IsSU2BiFundamental.sum_pi_two]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The two spinor indices of the conjugate up-type block are both dual right-handed. -/
lemma isBiDualRightWeyl_barUpBlock (f f' : Fin 3) (i : Fin 2) (cu cbQ : Fin 3)
    (wbQ : Fin 2) :
    IsBiDualRightWeyl B repLorentz
      (fun l : Fin 2 × Fin 2 => h.barUpBlock f f' i l.1 cu l.2 cbQ wbQ) where
  repLorentz_T Λ l := by
    simp only [barUpBlock]
    rw [h.repLorentz_mul_fixed_left Λ
      (X := fun a => h.isFermionSector.uComponent f ![] (a, cu))
      (Y := fun a => h.isFermionSector.barQComponent f' ![] (a, cbQ, wbQ))
      (h.repLorentz_barHiggs_zero Λ ![] i)
      (h.isFermionSector.repLorentz_uComponent Λ f ![] (l.1, cu))
      (h.isFermionSector.repLorentz_barQComponent Λ f' ![] (l.2, cbQ, wbQ))]
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      simp [Matrix.conjTranspose_apply, SL2C.inverse_coe]

/-- A hypercharge transformation fixes every component of the conjugate up-type block, the
  three hypercharges `3`, `-4` and `1` cancelling. -/
lemma repGauge_u1_barUpBlock (t : unitary ℂ) (f f' : Fin 3) (i su : Fin 2) (cu : Fin 3)
    (sbQ : Fin 2) (cbQ : Fin 3) (wbQ : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.barUpBlock f f' i su cu sbQ cbQ wbQ)
      = h.barUpBlock f f' i su cu sbQ cbQ wbQ := by
  have ht : star (t : ℂ) * (t : ℂ) = 1 := t.2.1
  rw [barUpBlock, h.isHiggsSector.rep_mul, h.isHiggsSector.rep_mul, h.repGauge_u1_barHiggs,
    h.repGauge_u1_u, h.repGauge_u1_barQ, smul_mul_smul_comm, smul_mul_smul_comm,
    show (t : ℂ) ^ 3 * ((star (t : ℂ)) ^ 4 * (t : ℂ)) = 1 from by
      rw [show (t : ℂ) ^ 3 * ((star (t : ℂ)) ^ 4 * (t : ℂ))
        = (star (t : ℂ) * (t : ℂ)) ^ 4 from by ring, ht, one_pow],
    one_smul]

/-- The colour contraction of the conjugate up-type block. -/
noncomputable def barUpBlockColour (f f' : Fin 3) (i su sbQ wbQ : Fin 2) : B :=
  IsSU3FunAntiFun.deltaContraction
    (fun l : Fin 2 → Fin 3 => h.barUpBlock f f' i su (l 1) sbQ (l 0) wbQ)

/-- The colour contraction of the conjugate up-type block written out. -/
lemma barUpBlockColour_eq (f f' : Fin 3) (i su sbQ wbQ : Fin 2) :
    h.barUpBlockColour f f' i su sbQ wbQ
      = ∑ a : Fin 3, h.barUpBlock f f' i su a sbQ a wbQ := by
  simp [barUpBlockColour, IsSU3FunAntiFun.deltaContraction]

/-- The colour contraction of the conjugate up-type block still carries two fundamental
  isospin indices. -/
lemma isSU2BiFundamental_barUpBlockColour (f f' : Fin 3) (su sbQ : Fin 2) :
    IsSU2BiFundamental B repGauge
      (fun l : Fin 2 → Fin 2 => h.barUpBlockColour f f' (l 0) su sbQ (l 1)) := by
  simp only [h.barUpBlockColour_eq]
  exact IsSU2BiFundamental.sum fun a => h.isSU2BiFundamental_barUpBlock f f' su a sbQ a

/-- The isospin contraction of the colour-contracted conjugate up-type block, by the
  antisymmetric symbol. -/
noncomputable def barUpBlockIsospin (f f' : Fin 3) (su sbQ : Fin 2) : B :=
  IsSU2BiFundamental.epsilonContraction
    (fun l : Fin 2 → Fin 2 => h.barUpBlockColour f f' (l 0) su sbQ (l 1))

/-- The doubly contracted conjugate up-type block written out. -/
lemma barUpBlockIsospin_eq (f f' : Fin 3) (su sbQ : Fin 2) :
    h.barUpBlockIsospin f f' su sbQ = (∑ a : Fin 3, h.barUpBlock f f' 0 su a sbQ a 1)
      - ∑ a : Fin 3, h.barUpBlock f f' 1 su a sbQ a 0 := by
  rw [barUpBlockIsospin, IsSU2BiFundamental.epsilonContraction]
  simp [h.barUpBlockColour_eq]

/-- The doubly contracted conjugate up-type block carries two dual right-handed Weyl
  indices. -/
lemma isBiDualRightWeyl_barUpBlockIsospin (f f' : Fin 3) :
    IsBiDualRightWeyl B repLorentz
      (fun l : Fin 2 × Fin 2 => h.barUpBlockIsospin f f' l.1 l.2) := by
  simp only [h.barUpBlockIsospin_eq]
  exact isBiDualRightWeyl_sub
    (isBiDualRightWeyl_sum fun a => h.isBiDualRightWeyl_barUpBlock f f' 0 a a 1)
    (isBiDualRightWeyl_sum fun a => h.isBiDualRightWeyl_barUpBlock f f' 1 a a 0)

/-- The conjugate up-type Yukawa term of the family pair `(f, f')`. -/
noncomputable def barUpYukawa (f f' : Fin 3) : B :=
  IsBiLeftWeyl.epsilonContraction
    (T := fun l : Fin 2 × Fin 2 => h.barUpBlockIsospin f f' l.1 l.2)

/-!

## D. The invariance of the conjugate up-type Yukawa term, and its mass weight

-/

/-- The colour contraction of the conjugate up-type block is fixed by the colour factor. -/
lemma repGauge_su3_barUpBlockColour (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (i su sbQ wbQ : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.barUpBlockColour f f' i su sbQ wbQ)
      = h.barUpBlockColour f f' i su sbQ wbQ :=
  IsSU3FunAntiFun.repGauge_deltaContraction
    (h.isSU3FunAntiFun_barUpBlock f f' i su sbQ wbQ) U

/-- The doubly contracted conjugate up-type block is fixed by the colour factor. -/
lemma repGauge_su3_barUpBlockIsospin (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (su sbQ : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.barUpBlockIsospin f f' su sbQ)
      = h.barUpBlockIsospin f f' su sbQ := by
  rw [barUpBlockIsospin, IsSU2BiFundamental.epsilonContraction, map_sub,
    h.repGauge_su3_barUpBlockColour, h.repGauge_su3_barUpBlockColour]

/-- The doubly contracted conjugate up-type block is fixed by the isospin factor. -/
lemma repGauge_su2_barUpBlockIsospin (V : specialUnitaryGroup (Fin 2) ℂ) (f f' : Fin 3)
    (su sbQ : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.barUpBlockIsospin f f' su sbQ)
      = h.barUpBlockIsospin f f' su sbQ :=
  IsSU2BiFundamental.repGauge_epsilonContraction
    (h.isSU2BiFundamental_barUpBlockColour f f' su sbQ) V

/-- The doubly contracted conjugate up-type block is fixed by the hypercharge factor. -/
lemma repGauge_u1_barUpBlockIsospin (t : unitary ℂ) (f f' : Fin 3) (su sbQ : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.barUpBlockIsospin f f' su sbQ)
      = h.barUpBlockIsospin f f' su sbQ := by
  rw [h.barUpBlockIsospin_eq, map_sub, map_sum, map_sum]
  exact congrArg₂ _
    (Finset.sum_congr rfl fun a _ => h.repGauge_u1_barUpBlock t f f' 0 su a sbQ a 1)
    (Finset.sum_congr rfl fun a _ => h.repGauge_u1_barUpBlock t f f' 1 su a sbQ a 0)

/-- The conjugate up-type Yukawa term is gauge invariant. -/
lemma repGauge_barUpYukawa (f f' : Fin 3) (g : GaugeGroupI) :
    repGauge g (h.barUpYukawa f f') = h.barUpYukawa f f' := by
  refine forall_repGauge_eq_self (fun U => ?_) (fun V => ?_) (fun t => ?_) g <;>
    rw [barUpYukawa, IsBiLeftWeyl.epsilonContraction_eq, map_sub]
  · rw [h.repGauge_su3_barUpBlockIsospin, h.repGauge_su3_barUpBlockIsospin]
  · rw [h.repGauge_su2_barUpBlockIsospin, h.repGauge_su2_barUpBlockIsospin]
  · rw [h.repGauge_u1_barUpBlockIsospin, h.repGauge_u1_barUpBlockIsospin]

/-- The conjugate up-type Yukawa term is Lorentz invariant. -/
lemma repLorentz_barUpYukawa (f f' : Fin 3) (Λ : SL(2,ℂ)) :
    repLorentz Λ (h.barUpYukawa f f') = h.barUpYukawa f f' :=
  (h.isBiDualRightWeyl_barUpBlockIsospin f f').repLorentz_epsilonContraction Λ

/-- Every component of the conjugate up-type block sits at mass weight eight in the Yukawa
  sector. -/
lemma barUpBlock_mem_sectorMassWeight (f f' : Fin 3) (i su : Fin 2) (cu : Fin 3)
    (sbQ : Fin 2) (cbQ : Fin 3) (wbQ : Fin 2) :
    h.barUpBlock f f' i su cu sbQ cbQ wbQ
      ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 := by
  rw [h.sectorMassWeight_higgs_fermion_eight, barUpBlock]
  exact Submodule.mul_mem_mul (h.barHiggs_mem_derivSubmodule ![] i)
    (Submodule.mul_mem_mul (h.uComponent_mem_derivSubmodule f ![] (su, cu))
      (h.barQComponent_mem_derivSubmodule f' ![] (sbQ, cbQ, wbQ)))

/-- The conjugate up-type Yukawa term sits at mass weight eight in the Yukawa sector. -/
lemma barUpYukawa_mem_sectorMassWeight (f f' : Fin 3) :
    h.barUpYukawa f f'
      ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 := by
  have hiso : ∀ su sbQ : Fin 2, h.barUpBlockIsospin f f' su sbQ
      ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 := by
    intro su sbQ
    rw [h.barUpBlockIsospin_eq]
    exact Submodule.sub_mem _
      (sum_mem fun a _ => h.barUpBlock_mem_sectorMassWeight _ _ _ _ _ _ _ _)
      (sum_mem fun a _ => h.barUpBlock_mem_sectorMassWeight _ _ _ _ _ _ _ _)
  rw [barUpYukawa, IsBiLeftWeyl.epsilonContraction_eq]
  exact Submodule.sub_mem _ (hiso _ _) (hiso _ _)

/-!

## E. The conjugate charged-lepton Yukawa term

The conjugate of the charged-lepton type: the product `barH L bare`.  As with its
unconjugated partner there is no colour at all, so the colour step is plain invariance;
isospin is `2 ⊗ 2̄` with the conjugate Higgs symbol supplying the fundamental index, and
both fermions are left-handed.

-/

/-- The components of the conjugate charged-lepton Yukawa block `barH L bare`. -/
noncomputable def barLeptonBlock (f f' : Fin 3) (i sL wL sbe : Fin 2) : B :=
  h.isHiggsSector.barHiggs ![] i * (h.isFermionSector.LComponent f ![] (sL, wL) *
    h.isFermionSector.bareComponent f' ![] sbe)

/-- The conjugate lepton block is colour invariant outright. -/
lemma repGauge_su3_barLeptonBlock (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (i sL wL sbe : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.barLeptonBlock f f' i sL wL sbe)
      = h.barLeptonBlock f f' i sL wL sbe := by
  rw [barLeptonBlock, h.isHiggsSector.rep_mul, h.isHiggsSector.rep_mul,
    h.repGauge_su3_barHiggs, h.repGauge_su3_L, h.repGauge_su3_bare]

/-- The two isospin indices of the conjugate lepton block carry one fundamental and one
  anti-fundamental `su(2)` index, the conjugate Higgs symbol supplying the fundamental
  one. -/
lemma isSU2FunAntiFun_barLeptonBlock (f f' : Fin 3) (sL sbe : Fin 2) :
    IsSU2FunAntiFun B repGauge
      (fun l : Fin 2 → Fin 2 => h.barLeptonBlock f f' (l 0) sL (l 1) sbe) where
  repGauge_T V l := by
    simp only [barLeptonBlock]
    rw [h.repGauge_mul_fixed_right (1, V, 1)
      (A := fun a => h.isHiggsSector.barHiggs ![] a)
      (X := fun a => h.isFermionSector.LComponent f ![] (sL, a))
      (h.repGauge_su2_barHiggs V ![] (l 0)) (h.repGauge_su2_L V f ![] sL (l 1))
      (h.repGauge_su2_bare V f' ![] sbe), IsSU2BiFundamental.sum_pi_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The two spinor indices of the conjugate lepton block are both dual left-handed. -/
lemma isBiDualLeftWeyl_barLeptonBlock (f f' : Fin 3) (i wL : Fin 2) :
    IsBiDualLeftWeyl B repLorentz
      (fun l : Fin 2 × Fin 2 => h.barLeptonBlock f f' i l.1 wL l.2) where
  repLorentz_T Λ l := by
    simp only [barLeptonBlock]
    rw [h.repLorentz_mul_fixed_left Λ
      (X := fun a => h.isFermionSector.LComponent f ![] (a, wL))
      (Y := fun a => h.isFermionSector.bareComponent f' ![] a)
      (h.repLorentz_barHiggs_zero Λ ![] i)
      (h.isFermionSector.repLorentz_LComponent Λ f ![] (l.1, wL))
      (h.isFermionSector.repLorentz_bareComponent Λ f' ![] l.2)]
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      simp [Matrix.transpose_apply, SL2C.inverse_coe]

/-- A hypercharge transformation fixes every component of the conjugate lepton block, the
  three hypercharges `3`, `3` and `-6` cancelling. -/
lemma repGauge_u1_barLeptonBlock (t : unitary ℂ) (f f' : Fin 3) (i sL wL sbe : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.barLeptonBlock f f' i sL wL sbe)
      = h.barLeptonBlock f f' i sL wL sbe := by
  have ht : star (t : ℂ) * (t : ℂ) = 1 := t.2.1
  rw [barLeptonBlock, h.isHiggsSector.rep_mul, h.isHiggsSector.rep_mul,
    h.repGauge_u1_barHiggs, h.repGauge_u1_L, h.repGauge_u1_bare, smul_mul_smul_comm,
    smul_mul_smul_comm,
    show (t : ℂ) ^ 3 * ((t : ℂ) ^ 3 * (star (t : ℂ)) ^ 6) = 1 from by
      rw [show (t : ℂ) ^ 3 * ((t : ℂ) ^ 3 * (star (t : ℂ)) ^ 6)
        = (star (t : ℂ) * (t : ℂ)) ^ 6 from by ring, ht, one_pow],
    one_smul]

/-- The isospin contraction of the conjugate lepton block. -/
noncomputable def barLeptonBlockIsospin (f f' : Fin 3) (sL sbe : Fin 2) : B :=
  IsSU2FunAntiFun.deltaContraction
    (fun l : Fin 2 → Fin 2 => h.barLeptonBlock f f' (l 0) sL (l 1) sbe)

/-- The isospin contraction of the conjugate lepton block written out. -/
lemma barLeptonBlockIsospin_eq (f f' : Fin 3) (sL sbe : Fin 2) :
    h.barLeptonBlockIsospin f f' sL sbe
      = ∑ w : Fin 2, h.barLeptonBlock f f' w sL w sbe := by
  rw [barLeptonBlockIsospin, IsSU2FunAntiFun.deltaContraction, Fin.sum_univ_two]
  simp

/-- The contracted conjugate lepton block carries two dual left-handed Weyl indices. -/
lemma isBiDualLeftWeyl_barLeptonBlockIsospin (f f' : Fin 3) :
    IsBiDualLeftWeyl B repLorentz
      (fun l : Fin 2 × Fin 2 => h.barLeptonBlockIsospin f f' l.1 l.2) := by
  simp only [h.barLeptonBlockIsospin_eq]
  exact isBiDualLeftWeyl_sum fun w => h.isBiDualLeftWeyl_barLeptonBlock f f' w w

/-- The conjugate charged-lepton Yukawa term of the family pair `(f, f')`. -/
noncomputable def barLeptonYukawa (f f' : Fin 3) : B :=
  IsBiLeftWeyl.epsilonContraction
    (T := fun l : Fin 2 × Fin 2 => h.barLeptonBlockIsospin f f' l.1 l.2)

/-!

## F. The invariance of the conjugate charged-lepton Yukawa term, and its mass weight

-/

/-- The contracted conjugate lepton block is fixed by the colour factor. -/
lemma repGauge_su3_barLeptonBlockIsospin (U : specialUnitaryGroup (Fin 3) ℂ)
    (f f' : Fin 3) (sL sbe : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.barLeptonBlockIsospin f f' sL sbe)
      = h.barLeptonBlockIsospin f f' sL sbe := by
  rw [h.barLeptonBlockIsospin_eq, map_sum]
  exact Finset.sum_congr rfl fun w _ => h.repGauge_su3_barLeptonBlock U f f' w sL w sbe

/-- The contracted conjugate lepton block is fixed by the isospin factor. -/
lemma repGauge_su2_barLeptonBlockIsospin (V : specialUnitaryGroup (Fin 2) ℂ)
    (f f' : Fin 3) (sL sbe : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.barLeptonBlockIsospin f f' sL sbe)
      = h.barLeptonBlockIsospin f f' sL sbe :=
  IsSU2FunAntiFun.repGauge_deltaContraction
    (h.isSU2FunAntiFun_barLeptonBlock f f' sL sbe) V

/-- The contracted conjugate lepton block is fixed by the hypercharge factor. -/
lemma repGauge_u1_barLeptonBlockIsospin (t : unitary ℂ) (f f' : Fin 3) (sL sbe : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.barLeptonBlockIsospin f f' sL sbe)
      = h.barLeptonBlockIsospin f f' sL sbe := by
  rw [h.barLeptonBlockIsospin_eq, map_sum]
  exact Finset.sum_congr rfl fun w _ => h.repGauge_u1_barLeptonBlock t f f' w sL w sbe

/-- The conjugate charged-lepton Yukawa term is gauge invariant. -/
lemma repGauge_barLeptonYukawa (f f' : Fin 3) (g : GaugeGroupI) :
    repGauge g (h.barLeptonYukawa f f') = h.barLeptonYukawa f f' := by
  refine forall_repGauge_eq_self (fun U => ?_) (fun V => ?_) (fun t => ?_) g <;>
    rw [barLeptonYukawa, IsBiLeftWeyl.epsilonContraction_eq, map_sub]
  · rw [h.repGauge_su3_barLeptonBlockIsospin, h.repGauge_su3_barLeptonBlockIsospin]
  · rw [h.repGauge_su2_barLeptonBlockIsospin, h.repGauge_su2_barLeptonBlockIsospin]
  · rw [h.repGauge_u1_barLeptonBlockIsospin, h.repGauge_u1_barLeptonBlockIsospin]

/-- The conjugate charged-lepton Yukawa term is Lorentz invariant. -/
lemma repLorentz_barLeptonYukawa (f f' : Fin 3) (Λ : SL(2,ℂ)) :
    repLorentz Λ (h.barLeptonYukawa f f') = h.barLeptonYukawa f f' :=
  (h.isBiDualLeftWeyl_barLeptonBlockIsospin f f').repLorentz_epsilonContraction Λ

/-- Every component of the conjugate lepton block sits at mass weight eight in the Yukawa
  sector. -/
lemma barLeptonBlock_mem_sectorMassWeight (f f' : Fin 3) (i sL wL sbe : Fin 2) :
    h.barLeptonBlock f f' i sL wL sbe
      ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 := by
  rw [h.sectorMassWeight_higgs_fermion_eight, barLeptonBlock]
  exact Submodule.mul_mem_mul (h.barHiggs_mem_derivSubmodule ![] i)
    (Submodule.mul_mem_mul (h.LComponent_mem_derivSubmodule f ![] (sL, wL))
      (h.bareComponent_mem_derivSubmodule f' ![] sbe))

/-- The conjugate charged-lepton Yukawa term sits at mass weight eight in the Yukawa
  sector. -/
lemma barLeptonYukawa_mem_sectorMassWeight (f f' : Fin 3) :
    h.barLeptonYukawa f f'
      ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 := by
  rw [barLeptonYukawa, IsBiLeftWeyl.epsilonContraction_eq]
  refine Submodule.sub_mem _ ?_ ?_ <;>
    exact h.barLeptonBlockIsospin_eq _ _ _ _ ▸
      sum_mem fun w _ => h.barLeptonBlock_mem_sectorMassWeight _ _ _ _ _ _

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
noncomputable def barDownYukawaSpan : Submodule ℂ B :=
  ⨆ (f : Fin 3) (f' : Fin 3), ℂ ∙ h.barDownYukawa f f'

/-- The span of the conjugate up-type Yukawa terms over the nine family pairs. -/
noncomputable def barUpYukawaSpan : Submodule ℂ B :=
  ⨆ (f : Fin 3) (f' : Fin 3), ℂ ∙ h.barUpYukawa f f'

/-- The span of the conjugate charged-lepton Yukawa terms over the nine family pairs. -/
noncomputable def barLeptonYukawaSpan : Submodule ℂ B :=
  ⨆ (f : Fin 3) (f' : Fin 3), ℂ ∙ h.barLeptonYukawa f f'

/-- The conjugate down-type Yukawa span sits at mass weight eight in the Yukawa sector. -/
lemma barDownYukawaSpan_le_sectorMassWeight :
    h.barDownYukawaSpan
      ≤ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    (h.barDownYukawa_mem_sectorMassWeight f f')

/-- The conjugate down-type Yukawa span is a space of gauge invariants. -/
lemma barDownYukawaSpan_le_invariants : h.barDownYukawaSpan ≤ repGauge.invariants :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    ((Representation.mem_invariants _ _).2 (h.repGauge_barDownYukawa f f'))

/-- The conjugate down-type Yukawa span is a space of Lorentz invariants. -/
lemma barDownYukawaSpan_le_lorentzInvariants :
    h.barDownYukawaSpan ≤ repLorentz.invariants :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    ((Representation.mem_invariants _ _).2 (h.repLorentz_barDownYukawa f f'))

/-- The conjugate up-type Yukawa span sits at mass weight eight in the Yukawa sector. -/
lemma barUpYukawaSpan_le_sectorMassWeight :
    h.barUpYukawaSpan
      ≤ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    (h.barUpYukawa_mem_sectorMassWeight f f')

/-- The conjugate up-type Yukawa span is a space of gauge invariants. -/
lemma barUpYukawaSpan_le_invariants : h.barUpYukawaSpan ≤ repGauge.invariants :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    ((Representation.mem_invariants _ _).2 (h.repGauge_barUpYukawa f f'))

/-- The conjugate up-type Yukawa span is a space of Lorentz invariants. -/
lemma barUpYukawaSpan_le_lorentzInvariants : h.barUpYukawaSpan ≤ repLorentz.invariants :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    ((Representation.mem_invariants _ _).2 (h.repLorentz_barUpYukawa f f'))

/-- The conjugate charged-lepton Yukawa span sits at mass weight eight in the Yukawa
  sector. -/
lemma barLeptonYukawaSpan_le_sectorMassWeight :
    h.barLeptonYukawaSpan
      ≤ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    (h.barLeptonYukawa_mem_sectorMassWeight f f')

/-- The conjugate charged-lepton Yukawa span is a space of gauge invariants. -/
lemma barLeptonYukawaSpan_le_invariants : h.barLeptonYukawaSpan ≤ repGauge.invariants :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    ((Representation.mem_invariants _ _).2 (h.repGauge_barLeptonYukawa f f'))

/-- The conjugate charged-lepton Yukawa span is a space of Lorentz invariants. -/
lemma barLeptonYukawaSpan_le_lorentzInvariants :
    h.barLeptonYukawaSpan ≤ repLorentz.invariants :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    ((Representation.mem_invariants _ _).2 (h.repLorentz_barLeptonYukawa f f'))

/-- The Yukawa span of the Standard Model at mass weight eight: the join of the six
  couplings, each over the nine family pairs. -/
noncomputable def yukawaSpan : Submodule ℂ B :=
  h.downYukawaSpan ⊔ h.upYukawaSpan ⊔ h.leptonYukawaSpan
    ⊔ h.barDownYukawaSpan ⊔ h.barUpYukawaSpan ⊔ h.barLeptonYukawaSpan

/-- The Yukawa span lies inside the gauge- and Lorentz-invariants of the Yukawa sector at
  mass weight eight. This is the easy direction of the classification: every Yukawa term
  is an invariant of the right mass weight, so the eventual classification is an
  equivalence and not merely a one-way inclusion. -/
lemma yukawaSpan_le_inf :
    h.yukawaSpan ≤ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8
        ⊓ repGauge.invariants ⊓ repLorentz.invariants :=
  sup_le (sup_le (sup_le (sup_le (sup_le
    (le_inf (le_inf h.downYukawaSpan_le_sectorMassWeight h.downYukawaSpan_le_invariants)
      h.downYukawaSpan_le_lorentzInvariants)
    (le_inf (le_inf h.upYukawaSpan_le_sectorMassWeight h.upYukawaSpan_le_invariants)
      h.upYukawaSpan_le_lorentzInvariants))
    (le_inf (le_inf h.leptonYukawaSpan_le_sectorMassWeight
      h.leptonYukawaSpan_le_invariants) h.leptonYukawaSpan_le_lorentzInvariants))
    (le_inf (le_inf h.barDownYukawaSpan_le_sectorMassWeight
      h.barDownYukawaSpan_le_invariants) h.barDownYukawaSpan_le_lorentzInvariants))
    (le_inf (le_inf h.barUpYukawaSpan_le_sectorMassWeight h.barUpYukawaSpan_le_invariants)
      h.barUpYukawaSpan_le_lorentzInvariants))
    (le_inf (le_inf h.barLeptonYukawaSpan_le_sectorMassWeight
      h.barLeptonYukawaSpan_le_invariants) h.barLeptonYukawaSpan_le_lorentzInvariants)

end IsCovStandardModel

end StandardModel
