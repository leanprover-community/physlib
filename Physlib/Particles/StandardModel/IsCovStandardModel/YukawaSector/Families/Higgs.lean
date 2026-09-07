/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsCovStandardModel.YukawaSector.Families.Symbols
/-!
# The Yukawa terms built on the Higgs symbol

## i. Overview

Three of the twelve blocks of the mass-weight-eight Yukawa sector are built on the Higgs
symbol rather than its conjugate: the down type `H d barQ`, the up type `H baru Q` and the
charged-lepton type `H barL e`.  They are the three genuinely distinct computations of the
sector — the other nine blocks are their conjugates and the two fermion orderings of each —
and this file builds, for each of them, the block, the index laws its three symbols obey,
the iterated contraction those laws admit, and the proof that the contraction is a gauge-
and Lorentz-invariant element of the sector at mass weight eight.

The three differ in exactly two places.  Isospin: the down and lepton types contract a
`2 ⊗ 2̄` by the trace, the up type a `2̄ ⊗ 2̄` by the antisymmetric symbol, since the Higgs
symbol and the quark doublet both carry the anti-fundamental.  Colour: the two quark types
contract a `3 ⊗ 3̄` by the Kronecker delta, while the lepton type carries no colour at all,
so its colour step is plain invariance rather than a classification and its contraction has
two stages instead of three.

The transposed blocks — the same three triples with the two fermion factors exchanged — are
not built here: they are minus these terms and span the same submodules, by
`mul_mul_swap_eq_neg` and `mul_mul_piece_swap`.

## ii. Key results

- `downYukawa`, `upYukawa`, `leptonYukawa` : the three Yukawa terms of a family pair.
- `isSU3FunAntiFun_downBlock`, `isSU2FunAntiFun_downBlock`, `isBiDualRightWeyl_downBlock`
  and their up-type and lepton-type counterparts : the index laws of each block.
- `repGauge_downYukawa`, `repLorentz_downYukawa` and their counterparts : the invariance of
  each Yukawa term.
- `downYukawaSpan`, `upYukawaSpan`, `leptonYukawaSpan` : the join over the nine family
  pairs, which is the coupling with an arbitrary `3 × 3` matrix.

## iii. Table of contents

- A. The down-type Yukawa term
- B. The invariance of the down-type Yukawa term, and its mass weight
- C. The up-type Yukawa term
- D. The invariance of the up-type Yukawa term, and its mass weight
- E. The charged-lepton Yukawa term
- F. The invariance of the charged-lepton Yukawa term, and its mass weight
- G. The spans of the Yukawa terms

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

## A. The down-type Yukawa term

The first block, and the pattern for the other eleven.  The block is the product
`H d barQ`; the conjugate quark doublet supplies the fundamental colour index and the
fundamental isospin index, so it goes in the first slot of both mixed families, while the
down singlet supplies the anti-fundamental colour index and the Higgs symbol the
anti-fundamental isospin one.  Both fermions are right-handed.  The three contractions are
then formed in turn, each one a spectator of the next.

-/

/-- The components of the down-type Yukawa block `H d barQ`: a Higgs symbol, a
  down-singlet symbol and a conjugate quark-doublet symbol, none carrying derivatives,
  multiplied in the order in which the block of
  `sectorMassWeightEightGaugeWeight_piece_zero` multiplies them. -/
noncomputable def downBlock (f f' : Fin 3) (i sd : Fin 2) (cd : Fin 3) (sq : Fin 2)
    (cq : Fin 3) (wq : Fin 2) : B :=
  h.isHiggsSector.higgs ![] i * (h.isFermionSector.dComponent f ![] (sd, cd) *
    h.isFermionSector.barQComponent f' ![] (sq, cq, wq))

/-- The two colour indices of the down-type block carry one fundamental and one
  anti-fundamental `su(3)` index: the conjugate quark doublet supplies the fundamental
  index, so it goes in the first slot, and the down singlet the anti-fundamental one. -/
lemma isSU3FunAntiFun_downBlock (f f' : Fin 3) (i sd sq wq : Fin 2) :
    IsSU3FunAntiFun B repGauge
      (fun l : Fin 2 → Fin 3 => h.downBlock f f' i sd (l 1) sq (l 0) wq) where
  repGauge_T U l := by
    simp only [downBlock]
    rw [h.repGauge_mul_fixed_left (U, 1, 1)
      (X := fun a => h.isFermionSector.dComponent f ![] (sd, a))
      (Y := fun a => h.isFermionSector.barQComponent f' ![] (sq, a, wq))
      (h.repGauge_su3_higgs U ![] i) (h.repGauge_su3_d U f ![] sd (l 1))
      (h.repGauge_su3_barQ U f' ![] sq (l 0) wq), IsSU3FunAntiFun.sum_pi_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [mul_comm]

/-- The two isospin indices of the down-type block carry one fundamental and one
  anti-fundamental `su(2)` index: the conjugate quark doublet supplies the fundamental
  index and the Higgs symbol the anti-fundamental one, so the Higgs index goes in the
  second slot. -/
lemma isSU2FunAntiFun_downBlock (f f' : Fin 3) (sd : Fin 2) (cd : Fin 3) (sq : Fin 2)
    (cq : Fin 3) :
    IsSU2FunAntiFun B repGauge
      (fun l : Fin 2 → Fin 2 => h.downBlock f f' (l 1) sd cd sq cq (l 0)) where
  repGauge_T V l := by
    simp only [downBlock]
    rw [h.repGauge_mul_fixed_mid (1, V, 1) (A := fun a => h.isHiggsSector.higgs ![] a)
      (Y := fun a => h.isFermionSector.barQComponent f' ![] (sq, cq, a))
      (h.repGauge_su2_higgs V ![] (l 1)) (h.repGauge_su2_d V f ![] (sd, cd))
      (h.repGauge_su2_barQ V f' ![] sq cq (l 0)), IsSU2BiFundamental.sum_pi_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [mul_comm]

/-- The two spinor indices of the down-type block are both dual right-handed: the down
  singlet and the conjugate quark doublet are both right-handed, and the Higgs symbol
  without derivatives is a Lorentz scalar. -/
lemma isBiDualRightWeyl_downBlock (f f' : Fin 3) (i : Fin 2) (cd cq : Fin 3) (wq : Fin 2) :
    IsBiDualRightWeyl B repLorentz
      (fun l : Fin 2 × Fin 2 => h.downBlock f f' i l.1 cd l.2 cq wq) where
  repLorentz_T Λ l := by
    simp only [downBlock]
    rw [h.repLorentz_mul_fixed_left Λ
      (X := fun a => h.isFermionSector.dComponent f ![] (a, cd))
      (Y := fun a => h.isFermionSector.barQComponent f' ![] (a, cq, wq))
      (h.repLorentz_higgs_zero Λ ![] i)
      (h.isFermionSector.repLorentz_dComponent Λ f ![] (l.1, cd))
      (h.isFermionSector.repLorentz_barQComponent Λ f' ![] (l.2, cq, wq))]
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      simp [Matrix.conjTranspose_apply, SL2C.inverse_coe]

/-- A hypercharge transformation fixes every component of the down-type block, the three
  hypercharges `-3`, `2` and `1` cancelling. -/
lemma repGauge_u1_downBlock (t : unitary ℂ) (f f' : Fin 3) (i sd : Fin 2) (cd : Fin 3)
    (sq : Fin 2) (cq : Fin 3) (wq : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.downBlock f f' i sd cd sq cq wq)
      = h.downBlock f f' i sd cd sq cq wq := by
  have ht : star (t : ℂ) * (t : ℂ) = 1 := t.2.1
  rw [downBlock, h.isHiggsSector.rep_mul, h.isHiggsSector.rep_mul, h.repGauge_u1_higgs,
    h.repGauge_u1_d, h.repGauge_u1_barQ, smul_mul_smul_comm, smul_mul_smul_comm,
    show (star (t : ℂ)) ^ 3 * ((t : ℂ) ^ 2 * (t : ℂ)) = 1 from by
      rw [show (t : ℂ) ^ 2 * (t : ℂ) = (t : ℂ) ^ 3 from by ring, ← mul_pow, ht, one_pow],
    one_smul]

/-- The colour contraction of the down-type block: the Kronecker delta joining the
  fundamental colour index of the conjugate quark doublet to the anti-fundamental one of
  the down singlet. -/
noncomputable def downBlockColour (f f' : Fin 3) (i sd sq wq : Fin 2) : B :=
  IsSU3FunAntiFun.deltaContraction
    (fun l : Fin 2 → Fin 3 => h.downBlock f f' i sd (l 1) sq (l 0) wq)

/-- The colour contraction written out: the sum of the three components with equal colour
  indices. -/
lemma downBlockColour_eq (f f' : Fin 3) (i sd sq wq : Fin 2) :
    h.downBlockColour f f' i sd sq wq
      = ∑ a : Fin 3, h.downBlock f f' i sd a sq a wq := by
  simp [downBlockColour, IsSU3FunAntiFun.deltaContraction]

/-- The colour contraction of the down-type block still carries one fundamental and one
  anti-fundamental isospin index, the colour sum being an isospin spectator. -/
lemma isSU2FunAntiFun_downBlockColour (f f' : Fin 3) (sd sq : Fin 2) :
    IsSU2FunAntiFun B repGauge
      (fun l : Fin 2 → Fin 2 => h.downBlockColour f f' (l 1) sd sq (l 0)) := by
  simp only [h.downBlockColour_eq]
  exact IsSU2FunAntiFun.sum fun a => h.isSU2FunAntiFun_downBlock f f' sd a sq a

/-- The isospin contraction of the colour-contracted down-type block: the Kronecker delta
  joining the fundamental isospin index of the conjugate quark doublet to the
  anti-fundamental one of the Higgs. -/
noncomputable def downBlockIsospin (f f' : Fin 3) (sd sq : Fin 2) : B :=
  IsSU2FunAntiFun.deltaContraction
    (fun l : Fin 2 → Fin 2 => h.downBlockColour f f' (l 1) sd sq (l 0))

/-- The doubly contracted block written out as a single sum over the isospin and colour
  indices it identifies. -/
lemma downBlockIsospin_eq (f f' : Fin 3) (sd sq : Fin 2) :
    h.downBlockIsospin f f' sd sq
      = ∑ p : Fin 2 × Fin 3, h.downBlock f f' p.1 sd p.2 sq p.2 p.1 := by
  rw [downBlockIsospin, IsSU2FunAntiFun.deltaContraction, h.downBlockColour_eq,
    h.downBlockColour_eq, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp

/-- The doubly contracted block carries two dual right-handed Weyl indices, the colour and
  isospin sums being Lorentz spectators. -/
lemma isBiDualRightWeyl_downBlockIsospin (f f' : Fin 3) :
    IsBiDualRightWeyl B repLorentz
      (fun l : Fin 2 × Fin 2 => h.downBlockIsospin f f' l.1 l.2) := by
  simp only [h.downBlockIsospin_eq]
  exact isBiDualRightWeyl_sum fun p => h.isBiDualRightWeyl_downBlock f f' p.1 p.2 p.2 p.1

/-- The down-type Yukawa term of the family pair `(f, f')`: the down-singlet symbol of
  family `f` against the conjugate quark doublet of family `f'` and a Higgs symbol, with
  the colour indices joined by the Kronecker delta, the isospin indices by the Kronecker
  delta, and the two right-handed spinor indices by the antisymmetric symbol. -/
noncomputable def downYukawa (f f' : Fin 3) : B :=
  IsBiLeftWeyl.epsilonContraction
    (T := fun l : Fin 2 × Fin 2 => h.downBlockIsospin f f' l.1 l.2)

/-!

## B. The invariance of the down-type Yukawa term, and its mass weight

Each contraction is invariant under the factor it contracts, and inert under the other two,
so the composite is fixed by all three factors and hence gauge invariant.  Hypercharge is
already invariant component by component, the three charges `-3`, `2` and `1` summing to
zero.

-/

/-- The colour contraction of the down-type block is fixed by the colour factor. -/
lemma repGauge_su3_downBlockColour (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (i sd sq wq : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.downBlockColour f f' i sd sq wq)
      = h.downBlockColour f f' i sd sq wq :=
  IsSU3FunAntiFun.repGauge_deltaContraction (h.isSU3FunAntiFun_downBlock f f' i sd sq wq) U

/-- The doubly contracted down-type block is fixed by the colour factor. -/
lemma repGauge_su3_downBlockIsospin (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (sd sq : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.downBlockIsospin f f' sd sq)
      = h.downBlockIsospin f f' sd sq := by
  rw [downBlockIsospin, IsSU2FunAntiFun.deltaContraction, map_add,
    h.repGauge_su3_downBlockColour, h.repGauge_su3_downBlockColour]

/-- The doubly contracted down-type block is fixed by the isospin factor. -/
lemma repGauge_su2_downBlockIsospin (V : specialUnitaryGroup (Fin 2) ℂ) (f f' : Fin 3)
    (sd sq : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.downBlockIsospin f f' sd sq)
      = h.downBlockIsospin f f' sd sq :=
  IsSU2FunAntiFun.repGauge_deltaContraction (h.isSU2FunAntiFun_downBlockColour f f' sd sq) V

/-- The doubly contracted down-type block is fixed by the hypercharge factor, already
  component by component. -/
lemma repGauge_u1_downBlockIsospin (t : unitary ℂ) (f f' : Fin 3) (sd sq : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.downBlockIsospin f f' sd sq)
      = h.downBlockIsospin f f' sd sq := by
  rw [h.downBlockIsospin_eq, map_sum]
  exact Finset.sum_congr rfl fun p _ => h.repGauge_u1_downBlock t f f' p.1 sd p.2 sq p.2 p.1

/-- The down-type Yukawa term is gauge invariant: the colour indices are joined by the
  Kronecker delta, the isospin indices by the Kronecker delta, and the three hypercharges
  cancel. -/
lemma repGauge_downYukawa (f f' : Fin 3) (g : GaugeGroupI) :
    repGauge g (h.downYukawa f f') = h.downYukawa f f' := by
  refine forall_repGauge_eq_self (fun U => ?_) (fun V => ?_) (fun t => ?_) g <;>
    rw [downYukawa, IsBiLeftWeyl.epsilonContraction_eq, map_sub]
  · rw [h.repGauge_su3_downBlockIsospin, h.repGauge_su3_downBlockIsospin]
  · rw [h.repGauge_su2_downBlockIsospin, h.repGauge_su2_downBlockIsospin]
  · rw [h.repGauge_u1_downBlockIsospin, h.repGauge_u1_downBlockIsospin]

/-- The down-type Yukawa term is Lorentz invariant, the two right-handed spinor indices
  being joined by the antisymmetric symbol. -/
lemma repLorentz_downYukawa (f f' : Fin 3) (Λ : SL(2,ℂ)) :
    repLorentz Λ (h.downYukawa f f') = h.downYukawa f f' :=
  (h.isBiDualRightWeyl_downBlockIsospin f f').repLorentz_epsilonContraction Λ

/-- Every component of the down-type block sits at mass weight eight in the Yukawa
  sector. -/
lemma downBlock_mem_sectorMassWeight (f f' : Fin 3) (i sd : Fin 2) (cd : Fin 3)
    (sq : Fin 2) (cq : Fin 3) (wq : Fin 2) :
    h.downBlock f f' i sd cd sq cq wq
      ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 := by
  rw [h.sectorMassWeight_higgs_fermion_eight, downBlock]
  exact Submodule.mul_mem_mul (h.higgs_mem_derivSubmodule ![] i)
    (Submodule.mul_mem_mul (h.dComponent_mem_derivSubmodule f ![] (sd, cd))
      (h.barQComponent_mem_derivSubmodule f' ![] (sq, cq, wq)))

/-- The down-type Yukawa term sits at mass weight eight in the Yukawa sector. -/
lemma downYukawa_mem_sectorMassWeight (f f' : Fin 3) :
    h.downYukawa f f' ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 := by
  rw [downYukawa, IsBiLeftWeyl.epsilonContraction_eq]
  refine Submodule.sub_mem _ ?_ ?_ <;>
    exact h.downBlockIsospin_eq _ _ _ _ ▸
      sum_mem fun p _ => h.downBlock_mem_sectorMassWeight _ _ _ _ _ _ _ _

/-!

## C. The up-type Yukawa term

The second computation.  Colour is again `3 ⊗ 3̄`, the conjugate up singlet supplying the
fundamental index, but isospin is `2̄ ⊗ 2̄`: the Higgs symbol and the quark doublet both
carry the anti-fundamental, whose only invariant is the antisymmetric symbol.  Both
fermions are left-handed.

-/

/-- The components of the up-type Yukawa block `H baru Q`: a Higgs symbol, a conjugate
  up-singlet symbol and a quark-doublet symbol, none carrying derivatives. -/
noncomputable def upBlock (f f' : Fin 3) (i su : Fin 2) (cu : Fin 3) (sQ : Fin 2)
    (cQ : Fin 3) (wQ : Fin 2) : B :=
  h.isHiggsSector.higgs ![] i * (h.isFermionSector.baruComponent f ![] (su, cu) *
    h.isFermionSector.QComponent f' ![] (sQ, cQ, wQ))

/-- The two colour indices of the up-type block carry one fundamental and one
  anti-fundamental `su(3)` index, the conjugate up singlet supplying the fundamental
  one. -/
lemma isSU3FunAntiFun_upBlock (f f' : Fin 3) (i su sQ wQ : Fin 2) :
    IsSU3FunAntiFun B repGauge
      (fun l : Fin 2 → Fin 3 => h.upBlock f f' i su (l 0) sQ (l 1) wQ) where
  repGauge_T U l := by
    simp only [upBlock]
    rw [h.repGauge_mul_fixed_left (U, 1, 1)
      (X := fun a => h.isFermionSector.baruComponent f ![] (su, a))
      (Y := fun a => h.isFermionSector.QComponent f' ![] (sQ, a, wQ))
      (h.repGauge_su3_higgs U ![] i) (h.repGauge_su3_baru U f ![] su (l 0))
      (h.repGauge_su3_Q U f' ![] sQ (l 1) wQ), IsSU3FunAntiFun.sum_pi_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The two isospin indices of the up-type block are both anti-fundamental: the Higgs
  symbol and the quark doublet both carry the anti-fundamental of `su(2)`. -/
lemma isSU2BiAntiFun_upBlock (f f' : Fin 3) (su : Fin 2) (cu : Fin 3) (sQ : Fin 2)
    (cQ : Fin 3) :
    IsSU2BiAntiFun B repGauge
      (fun l : Fin 2 → Fin 2 => h.upBlock f f' (l 0) su cu sQ cQ (l 1)) where
  repGauge_T V l := by
    simp only [upBlock]
    rw [h.repGauge_mul_fixed_mid (1, V, 1) (A := fun a => h.isHiggsSector.higgs ![] a)
      (Y := fun a => h.isFermionSector.QComponent f' ![] (sQ, cQ, a))
      (h.repGauge_su2_higgs V ![] (l 0)) (h.repGauge_su2_baru V f ![] (su, cu))
      (h.repGauge_su2_Q V f' ![] sQ cQ (l 1)), IsSU2BiFundamental.sum_pi_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The two spinor indices of the up-type block are both dual left-handed. -/
lemma isBiDualLeftWeyl_upBlock (f f' : Fin 3) (i : Fin 2) (cu cQ : Fin 3) (wQ : Fin 2) :
    IsBiDualLeftWeyl B repLorentz
      (fun l : Fin 2 × Fin 2 => h.upBlock f f' i l.1 cu l.2 cQ wQ) where
  repLorentz_T Λ l := by
    simp only [upBlock]
    rw [h.repLorentz_mul_fixed_left Λ
      (X := fun a => h.isFermionSector.baruComponent f ![] (a, cu))
      (Y := fun a => h.isFermionSector.QComponent f' ![] (a, cQ, wQ))
      (h.repLorentz_higgs_zero Λ ![] i)
      (h.isFermionSector.repLorentz_baruComponent Λ f ![] (l.1, cu))
      (h.isFermionSector.repLorentz_QComponent Λ f' ![] (l.2, cQ, wQ))]
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      simp [Matrix.transpose_apply, SL2C.inverse_coe]

/-- A hypercharge transformation fixes every component of the up-type block, the three
  hypercharges `-3`, `4` and `-1` cancelling. -/
lemma repGauge_u1_upBlock (t : unitary ℂ) (f f' : Fin 3) (i su : Fin 2) (cu : Fin 3)
    (sQ : Fin 2) (cQ : Fin 3) (wQ : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.upBlock f f' i su cu sQ cQ wQ)
      = h.upBlock f f' i su cu sQ cQ wQ := by
  have ht : star (t : ℂ) * (t : ℂ) = 1 := t.2.1
  rw [upBlock, h.isHiggsSector.rep_mul, h.isHiggsSector.rep_mul, h.repGauge_u1_higgs,
    h.repGauge_u1_baru, h.repGauge_u1_Q, smul_mul_smul_comm, smul_mul_smul_comm,
    show (star (t : ℂ)) ^ 3 * ((t : ℂ) ^ 4 * star (t : ℂ)) = 1 from by
      rw [show (star (t : ℂ)) ^ 3 * ((t : ℂ) ^ 4 * star (t : ℂ))
        = (star (t : ℂ) * (t : ℂ)) ^ 4 from by ring, ht, one_pow],
    one_smul]

/-- The colour contraction of the up-type block. -/
noncomputable def upBlockColour (f f' : Fin 3) (i su sQ wQ : Fin 2) : B :=
  IsSU3FunAntiFun.deltaContraction
    (fun l : Fin 2 → Fin 3 => h.upBlock f f' i su (l 0) sQ (l 1) wQ)

/-- The colour contraction of the up-type block written out. -/
lemma upBlockColour_eq (f f' : Fin 3) (i su sQ wQ : Fin 2) :
    h.upBlockColour f f' i su sQ wQ = ∑ a : Fin 3, h.upBlock f f' i su a sQ a wQ := by
  simp [upBlockColour, IsSU3FunAntiFun.deltaContraction]

/-- The colour contraction of the up-type block still carries two anti-fundamental isospin
  indices. -/
lemma isSU2BiAntiFun_upBlockColour (f f' : Fin 3) (su sQ : Fin 2) :
    IsSU2BiAntiFun B repGauge
      (fun l : Fin 2 → Fin 2 => h.upBlockColour f f' (l 0) su sQ (l 1)) := by
  simp only [h.upBlockColour_eq]
  exact IsSU2BiAntiFun.sum fun a => h.isSU2BiAntiFun_upBlock f f' su a sQ a

/-- The isospin contraction of the colour-contracted up-type block, by the antisymmetric
  symbol: two anti-fundamental isospin indices admit no trace. -/
noncomputable def upBlockIsospin (f f' : Fin 3) (su sQ : Fin 2) : B :=
  IsSU2BiFundamental.epsilonContraction
    (fun l : Fin 2 → Fin 2 => h.upBlockColour f f' (l 0) su sQ (l 1))

/-- The doubly contracted up-type block written out. -/
lemma upBlockIsospin_eq (f f' : Fin 3) (su sQ : Fin 2) :
    h.upBlockIsospin f f' su sQ = (∑ a : Fin 3, h.upBlock f f' 0 su a sQ a 1)
      - ∑ a : Fin 3, h.upBlock f f' 1 su a sQ a 0 := by
  rw [upBlockIsospin, IsSU2BiFundamental.epsilonContraction]
  simp [h.upBlockColour_eq]

/-- The doubly contracted up-type block carries two dual left-handed Weyl indices. -/
lemma isBiDualLeftWeyl_upBlockIsospin (f f' : Fin 3) :
    IsBiDualLeftWeyl B repLorentz
      (fun l : Fin 2 × Fin 2 => h.upBlockIsospin f f' l.1 l.2) := by
  simp only [h.upBlockIsospin_eq]
  exact isBiDualLeftWeyl_sub
    (isBiDualLeftWeyl_sum fun a => h.isBiDualLeftWeyl_upBlock f f' 0 a a 1)
    (isBiDualLeftWeyl_sum fun a => h.isBiDualLeftWeyl_upBlock f f' 1 a a 0)

/-- The up-type Yukawa term of the family pair `(f, f')`: the colour indices are joined by
  the Kronecker delta, the isospin indices by the antisymmetric symbol, and the two
  left-handed spinor indices by the antisymmetric symbol. -/
noncomputable def upYukawa (f f' : Fin 3) : B :=
  IsBiLeftWeyl.epsilonContraction
    (T := fun l : Fin 2 × Fin 2 => h.upBlockIsospin f f' l.1 l.2)

/-!

## D. The invariance of the up-type Yukawa term, and its mass weight

-/

/-- The colour contraction of the up-type block is fixed by the colour factor. -/
lemma repGauge_su3_upBlockColour (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (i su sQ wQ : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.upBlockColour f f' i su sQ wQ)
      = h.upBlockColour f f' i su sQ wQ :=
  IsSU3FunAntiFun.repGauge_deltaContraction (h.isSU3FunAntiFun_upBlock f f' i su sQ wQ) U

/-- The doubly contracted up-type block is fixed by the colour factor. -/
lemma repGauge_su3_upBlockIsospin (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (su sQ : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.upBlockIsospin f f' su sQ)
      = h.upBlockIsospin f f' su sQ := by
  rw [upBlockIsospin, IsSU2BiFundamental.epsilonContraction, map_sub,
    h.repGauge_su3_upBlockColour, h.repGauge_su3_upBlockColour]

/-- The doubly contracted up-type block is fixed by the isospin factor. -/
lemma repGauge_su2_upBlockIsospin (V : specialUnitaryGroup (Fin 2) ℂ) (f f' : Fin 3)
    (su sQ : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.upBlockIsospin f f' su sQ)
      = h.upBlockIsospin f f' su sQ :=
  IsSU2BiAntiFun.repGauge_epsilonContraction (h.isSU2BiAntiFun_upBlockColour f f' su sQ) V

/-- The doubly contracted up-type block is fixed by the hypercharge factor. -/
lemma repGauge_u1_upBlockIsospin (t : unitary ℂ) (f f' : Fin 3) (su sQ : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.upBlockIsospin f f' su sQ)
      = h.upBlockIsospin f f' su sQ := by
  rw [h.upBlockIsospin_eq, map_sub, map_sum, map_sum]
  exact congrArg₂ _ (Finset.sum_congr rfl fun a _ => h.repGauge_u1_upBlock t f f' 0 su a sQ a 1)
    (Finset.sum_congr rfl fun a _ => h.repGauge_u1_upBlock t f f' 1 su a sQ a 0)

/-- The up-type Yukawa term is gauge invariant. -/
lemma repGauge_upYukawa (f f' : Fin 3) (g : GaugeGroupI) :
    repGauge g (h.upYukawa f f') = h.upYukawa f f' := by
  refine forall_repGauge_eq_self (fun U => ?_) (fun V => ?_) (fun t => ?_) g <;>
    rw [upYukawa, IsBiLeftWeyl.epsilonContraction_eq, map_sub]
  · rw [h.repGauge_su3_upBlockIsospin, h.repGauge_su3_upBlockIsospin]
  · rw [h.repGauge_su2_upBlockIsospin, h.repGauge_su2_upBlockIsospin]
  · rw [h.repGauge_u1_upBlockIsospin, h.repGauge_u1_upBlockIsospin]

/-- The up-type Yukawa term is Lorentz invariant. -/
lemma repLorentz_upYukawa (f f' : Fin 3) (Λ : SL(2,ℂ)) :
    repLorentz Λ (h.upYukawa f f') = h.upYukawa f f' :=
  (h.isBiDualLeftWeyl_upBlockIsospin f f').repLorentz_epsilonContraction Λ

/-- Every component of the up-type block sits at mass weight eight in the Yukawa sector. -/
lemma upBlock_mem_sectorMassWeight (f f' : Fin 3) (i su : Fin 2) (cu : Fin 3)
    (sQ : Fin 2) (cQ : Fin 3) (wQ : Fin 2) :
    h.upBlock f f' i su cu sQ cQ wQ
      ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 := by
  rw [h.sectorMassWeight_higgs_fermion_eight, upBlock]
  exact Submodule.mul_mem_mul (h.higgs_mem_derivSubmodule ![] i)
    (Submodule.mul_mem_mul (h.baruComponent_mem_derivSubmodule f ![] (su, cu))
      (h.QComponent_mem_derivSubmodule f' ![] (sQ, cQ, wQ)))

/-- The up-type Yukawa term sits at mass weight eight in the Yukawa sector. -/
lemma upYukawa_mem_sectorMassWeight (f f' : Fin 3) :
    h.upYukawa f f' ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 := by
  have hiso : ∀ su sQ : Fin 2, h.upBlockIsospin f f' su sQ
      ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 := by
    intro su sQ
    rw [h.upBlockIsospin_eq]
    exact Submodule.sub_mem _ (sum_mem fun a _ => h.upBlock_mem_sectorMassWeight _ _ _ _ _ _ _ _)
      (sum_mem fun a _ => h.upBlock_mem_sectorMassWeight _ _ _ _ _ _ _ _)
  rw [upYukawa, IsBiLeftWeyl.epsilonContraction_eq]
  exact Submodule.sub_mem _ (hiso _ _) (hiso _ _)

/-!

## E. The charged-lepton Yukawa term

The lepton blocks carry no colour at all, so there is no colour family to classify and no
colour contraction to form: the three symbols are separately fixed by the colour factor,
which is `repGauge_su3_leptonBlock`.  The isospin and Lorentz steps are the same two steps
as for the quark blocks, and the contraction is the composite of those two alone.

-/

/-- The components of the charged-lepton Yukawa block `H barL e`: a Higgs symbol, a
  conjugate lepton-doublet symbol and a lepton-singlet symbol, none carrying
  derivatives. -/
noncomputable def leptonBlock (f f' : Fin 3) (i sL wL se : Fin 2) : B :=
  h.isHiggsSector.higgs ![] i * (h.isFermionSector.barLComponent f ![] (sL, wL) *
    h.isFermionSector.eComponent f' ![] se)

/-- The lepton block is colour invariant outright: none of its three symbols carries a
  colour index. This is what stands in for the colour classification of the quark
  blocks. -/
lemma repGauge_su3_leptonBlock (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (i sL wL se : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.leptonBlock f f' i sL wL se)
      = h.leptonBlock f f' i sL wL se := by
  rw [leptonBlock, h.isHiggsSector.rep_mul, h.isHiggsSector.rep_mul, h.repGauge_su3_higgs,
    h.repGauge_su3_barL, h.repGauge_su3_e]

/-- The two isospin indices of the lepton block carry one fundamental and one
  anti-fundamental `su(2)` index, the conjugate lepton doublet supplying the fundamental
  one. -/
lemma isSU2FunAntiFun_leptonBlock (f f' : Fin 3) (sL se : Fin 2) :
    IsSU2FunAntiFun B repGauge
      (fun l : Fin 2 → Fin 2 => h.leptonBlock f f' (l 1) sL (l 0) se) where
  repGauge_T V l := by
    simp only [leptonBlock]
    rw [h.repGauge_mul_fixed_right (1, V, 1) (A := fun a => h.isHiggsSector.higgs ![] a)
      (X := fun a => h.isFermionSector.barLComponent f ![] (sL, a))
      (h.repGauge_su2_higgs V ![] (l 1)) (h.repGauge_su2_barL V f ![] sL (l 0))
      (h.repGauge_su2_e V f' ![] se), IsSU2BiFundamental.sum_pi_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [mul_comm]

/-- The two spinor indices of the lepton block are both dual right-handed. -/
lemma isBiDualRightWeyl_leptonBlock (f f' : Fin 3) (i wL : Fin 2) :
    IsBiDualRightWeyl B repLorentz
      (fun l : Fin 2 × Fin 2 => h.leptonBlock f f' i l.1 wL l.2) where
  repLorentz_T Λ l := by
    simp only [leptonBlock]
    rw [h.repLorentz_mul_fixed_left Λ
      (X := fun a => h.isFermionSector.barLComponent f ![] (a, wL))
      (Y := fun a => h.isFermionSector.eComponent f' ![] a)
      (h.repLorentz_higgs_zero Λ ![] i)
      (h.isFermionSector.repLorentz_barLComponent Λ f ![] (l.1, wL))
      (h.isFermionSector.repLorentz_eComponent Λ f' ![] l.2)]
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      simp [Matrix.conjTranspose_apply, SL2C.inverse_coe]

/-- A hypercharge transformation fixes every component of the lepton block, the three
  hypercharges `-3`, `-3` and `6` cancelling. -/
lemma repGauge_u1_leptonBlock (t : unitary ℂ) (f f' : Fin 3) (i sL wL se : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.leptonBlock f f' i sL wL se)
      = h.leptonBlock f f' i sL wL se := by
  have ht : star (t : ℂ) * (t : ℂ) = 1 := t.2.1
  rw [leptonBlock, h.isHiggsSector.rep_mul, h.isHiggsSector.rep_mul, h.repGauge_u1_higgs,
    h.repGauge_u1_barL, h.repGauge_u1_e, smul_mul_smul_comm, smul_mul_smul_comm,
    show (star (t : ℂ)) ^ 3 * ((star (t : ℂ)) ^ 3 * (t : ℂ) ^ 6) = 1 from by
      rw [show (star (t : ℂ)) ^ 3 * ((star (t : ℂ)) ^ 3 * (t : ℂ) ^ 6)
        = (star (t : ℂ) * (t : ℂ)) ^ 6 from by ring, ht, one_pow],
    one_smul]

/-- The isospin contraction of the lepton block. -/
noncomputable def leptonBlockIsospin (f f' : Fin 3) (sL se : Fin 2) : B :=
  IsSU2FunAntiFun.deltaContraction
    (fun l : Fin 2 → Fin 2 => h.leptonBlock f f' (l 1) sL (l 0) se)

/-- The isospin contraction of the lepton block written out. -/
lemma leptonBlockIsospin_eq (f f' : Fin 3) (sL se : Fin 2) :
    h.leptonBlockIsospin f f' sL se = ∑ w : Fin 2, h.leptonBlock f f' w sL w se := by
  rw [leptonBlockIsospin, IsSU2FunAntiFun.deltaContraction, Fin.sum_univ_two]
  simp

/-- The contracted lepton block carries two dual right-handed Weyl indices. -/
lemma isBiDualRightWeyl_leptonBlockIsospin (f f' : Fin 3) :
    IsBiDualRightWeyl B repLorentz
      (fun l : Fin 2 × Fin 2 => h.leptonBlockIsospin f f' l.1 l.2) := by
  simp only [h.leptonBlockIsospin_eq]
  exact isBiDualRightWeyl_sum fun w => h.isBiDualRightWeyl_leptonBlock f f' w w

/-- The charged-lepton Yukawa term of the family pair `(f, f')`: the isospin indices are
  joined by the Kronecker delta and the two right-handed spinor indices by the
  antisymmetric symbol, colour playing no part. -/
noncomputable def leptonYukawa (f f' : Fin 3) : B :=
  IsBiLeftWeyl.epsilonContraction
    (T := fun l : Fin 2 × Fin 2 => h.leptonBlockIsospin f f' l.1 l.2)

/-!

## F. The invariance of the charged-lepton Yukawa term, and its mass weight

-/

/-- The contracted lepton block is fixed by the colour factor. -/
lemma repGauge_su3_leptonBlockIsospin (U : specialUnitaryGroup (Fin 3) ℂ) (f f' : Fin 3)
    (sL se : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.leptonBlockIsospin f f' sL se)
      = h.leptonBlockIsospin f f' sL se := by
  rw [h.leptonBlockIsospin_eq, map_sum]
  exact Finset.sum_congr rfl fun w _ => h.repGauge_su3_leptonBlock U f f' w sL w se

/-- The contracted lepton block is fixed by the isospin factor. -/
lemma repGauge_su2_leptonBlockIsospin (V : specialUnitaryGroup (Fin 2) ℂ) (f f' : Fin 3)
    (sL se : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.leptonBlockIsospin f f' sL se)
      = h.leptonBlockIsospin f f' sL se :=
  IsSU2FunAntiFun.repGauge_deltaContraction (h.isSU2FunAntiFun_leptonBlock f f' sL se) V

/-- The contracted lepton block is fixed by the hypercharge factor. -/
lemma repGauge_u1_leptonBlockIsospin (t : unitary ℂ) (f f' : Fin 3) (sL se : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.leptonBlockIsospin f f' sL se)
      = h.leptonBlockIsospin f f' sL se := by
  rw [h.leptonBlockIsospin_eq, map_sum]
  exact Finset.sum_congr rfl fun w _ => h.repGauge_u1_leptonBlock t f f' w sL w se

/-- The charged-lepton Yukawa term is gauge invariant. -/
lemma repGauge_leptonYukawa (f f' : Fin 3) (g : GaugeGroupI) :
    repGauge g (h.leptonYukawa f f') = h.leptonYukawa f f' := by
  refine forall_repGauge_eq_self (fun U => ?_) (fun V => ?_) (fun t => ?_) g <;>
    rw [leptonYukawa, IsBiLeftWeyl.epsilonContraction_eq, map_sub]
  · rw [h.repGauge_su3_leptonBlockIsospin, h.repGauge_su3_leptonBlockIsospin]
  · rw [h.repGauge_su2_leptonBlockIsospin, h.repGauge_su2_leptonBlockIsospin]
  · rw [h.repGauge_u1_leptonBlockIsospin, h.repGauge_u1_leptonBlockIsospin]

/-- The charged-lepton Yukawa term is Lorentz invariant. -/
lemma repLorentz_leptonYukawa (f f' : Fin 3) (Λ : SL(2,ℂ)) :
    repLorentz Λ (h.leptonYukawa f f') = h.leptonYukawa f f' :=
  (h.isBiDualRightWeyl_leptonBlockIsospin f f').repLorentz_epsilonContraction Λ

/-- Every component of the lepton block sits at mass weight eight in the Yukawa sector. -/
lemma leptonBlock_mem_sectorMassWeight (f f' : Fin 3) (i sL wL se : Fin 2) :
    h.leptonBlock f f' i sL wL se
      ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 := by
  rw [h.sectorMassWeight_higgs_fermion_eight, leptonBlock]
  exact Submodule.mul_mem_mul (h.higgs_mem_derivSubmodule ![] i)
    (Submodule.mul_mem_mul (h.barLComponent_mem_derivSubmodule f ![] (sL, wL))
      (h.eComponent_mem_derivSubmodule f' ![] se))

/-- The charged-lepton Yukawa term sits at mass weight eight in the Yukawa sector. -/
lemma leptonYukawa_mem_sectorMassWeight (f f' : Fin 3) :
    h.leptonYukawa f f'
      ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 := by
  rw [leptonYukawa, IsBiLeftWeyl.epsilonContraction_eq]
  refine Submodule.sub_mem _ ?_ ?_ <;>
    exact h.leptonBlockIsospin_eq _ _ _ _ ▸
      sum_mem fun w _ => h.leptonBlock_mem_sectorMassWeight _ _ _ _ _ _

/-!

## G. The spans of the Yukawa terms

The nine family pairs are what the Yukawa coupling matrices are: joining the line of a
Yukawa term over `(f, f') : Fin 3 × Fin 3` gives exactly the space of terms with an
arbitrary `3 × 3` complex coupling matrix, and no matrix has to be written down.  Each such
join lies inside the sector at mass weight eight and inside both spaces of invariants,
which is the direction that will make the eventual classification an equivalence rather
than a one-way inclusion.

-/

/-- The span of the down-type Yukawa terms over the nine family pairs: the down-type
  Yukawa coupling with an arbitrary `3 × 3` matrix. -/
noncomputable def downYukawaSpan : Submodule ℂ B :=
  ⨆ (f : Fin 3) (f' : Fin 3), ℂ ∙ h.downYukawa f f'

/-- The span of the up-type Yukawa terms over the nine family pairs. -/
noncomputable def upYukawaSpan : Submodule ℂ B :=
  ⨆ (f : Fin 3) (f' : Fin 3), ℂ ∙ h.upYukawa f f'

/-- The span of the charged-lepton Yukawa terms over the nine family pairs. -/
noncomputable def leptonYukawaSpan : Submodule ℂ B :=
  ⨆ (f : Fin 3) (f' : Fin 3), ℂ ∙ h.leptonYukawa f f'

/-- The down-type Yukawa span sits at mass weight eight in the Yukawa sector. -/
lemma downYukawaSpan_le_sectorMassWeight :
    h.downYukawaSpan ≤ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    (h.downYukawa_mem_sectorMassWeight f f')

/-- The down-type Yukawa span is a space of gauge invariants. -/
lemma downYukawaSpan_le_invariants : h.downYukawaSpan ≤ repGauge.invariants :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    ((Representation.mem_invariants _ _).2 (h.repGauge_downYukawa f f'))

/-- The down-type Yukawa span is a space of Lorentz invariants. -/
lemma downYukawaSpan_le_lorentzInvariants : h.downYukawaSpan ≤ repLorentz.invariants :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    ((Representation.mem_invariants _ _).2 (h.repLorentz_downYukawa f f'))

/-- The up-type Yukawa span sits at mass weight eight in the Yukawa sector. -/
lemma upYukawaSpan_le_sectorMassWeight :
    h.upYukawaSpan ≤ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    (h.upYukawa_mem_sectorMassWeight f f')

/-- The up-type Yukawa span is a space of gauge invariants. -/
lemma upYukawaSpan_le_invariants : h.upYukawaSpan ≤ repGauge.invariants :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    ((Representation.mem_invariants _ _).2 (h.repGauge_upYukawa f f'))

/-- The up-type Yukawa span is a space of Lorentz invariants. -/
lemma upYukawaSpan_le_lorentzInvariants : h.upYukawaSpan ≤ repLorentz.invariants :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    ((Representation.mem_invariants _ _).2 (h.repLorentz_upYukawa f f'))

/-- The charged-lepton Yukawa span sits at mass weight eight in the Yukawa sector. -/
lemma leptonYukawaSpan_le_sectorMassWeight :
    h.leptonYukawaSpan ≤ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    (h.leptonYukawa_mem_sectorMassWeight f f')

/-- The charged-lepton Yukawa span is a space of gauge invariants. -/
lemma leptonYukawaSpan_le_invariants : h.leptonYukawaSpan ≤ repGauge.invariants :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    ((Representation.mem_invariants _ _).2 (h.repGauge_leptonYukawa f f'))

/-- The charged-lepton Yukawa span is a space of Lorentz invariants. -/
lemma leptonYukawaSpan_le_lorentzInvariants : h.leptonYukawaSpan ≤ repLorentz.invariants :=
  iSup_le fun f => iSup_le fun f' => (Submodule.span_singleton_le_iff_mem _ _).2
    ((Representation.mem_invariants _ _).2 (h.repLorentz_leptonYukawa f f'))

end IsCovStandardModel

end StandardModel
