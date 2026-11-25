/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.YukawaSector.Basic
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.FermionSector.Components
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.Invariants.Basic
public import PhyslibAlpha.Relativity.Fermions.Weyl.Metric
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.InvariantReduction
/-!
# The symbols of the Yukawa blocks

The symbols of the Yukawa blocks of the Standard Model's covariant field algebra.

## i. Overview

Everything below is stated about the covariant field algebra `fieldData.LocalCovFieldAlgebra` of the
Standard Model.

At mass weight eight a Yukawa block is a product of three underived symbols, one Higgs and
two fermions, and every statement about such a block reduces to statements about its three
factors. This file is that reduction. It reads the Higgs symbols at each factor of a gauge
transformation (the fermion symbols are read in `FermionSector/Components.lean`), does the
algebra of a triple product with one inert factor once for each position the inert factor can
occupy, and records the closure of the index laws under the sums and differences a contraction
performs.

Two things here are easy to get wrong and are settled once. A gauge transformation is a
triple and the three index laws each constrain one factor of it. Colour, isospin and
Lorentz between them say nothing about hypercharge, so hypercharge is a fourth step and not
a corollary of the other three, and `forall_repGauge_eq_self`, in `GaugeGroup/Basic.lean`,
is what assembles the four into gauge invariance. And the twelve blocks come in two fermion
orderings, but the fermion
symbols anticommute, so the two orderings of a block span the same submodule and have the
same weight pieces, and `mul_mul_piece_swap` is what makes the six transposed blocks a rewrite
rather than six fresh derivations.

## ii. Key results

- `repGauge_mul_fixed_left`, `repGauge_mul_fixed_mid`, `repGauge_mul_fixed_right`,
  `repLorentz_mul_fixed_left` : the transformation of a triple product with one inert
  factor.
- `repGauge_su3_higgs`, `repGauge_su2_higgs`, `repGauge_u1_higgs` and their conjugates : the three
  gauge laws of the Higgs symbols.
- `mul_mul_piece_swap` : the two fermion orderings of a block have the same weight pieces.

## iii. Table of contents

- A. Triple products with one inert factor
- B. The transformation laws of the Higgs symbols
- C. The symbols inside the derivative submodules
- D. The two fermion orderings

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz Pointwise ComplexConjugate

namespace LocalCovFieldAlgebra

/-!

## A. Triple products with one inert factor

Every block is a product of three symbols, and every classifier moves exactly two of them.
The third is inert, being a colour singlet, an isospin singlet or a Lorentz scalar. The
three lemmas here do the algebra once for each position the inert factor can occupy, and
reduce a transformation law for a block to the laws of its factors.

-/

/-- A triple product whose first factor is fixed and whose second and third move by given
  coefficients moves by the product of those coefficients. -/
lemma repGauge_mul_fixed_left (g : GaugeGroupI) {ι κ : Type} [Fintype ι] [Fintype κ]
    {A : fieldData.LocalCovFieldAlgebra} {X : ι → fieldData.LocalCovFieldAlgebra}
    {Y : κ → fieldData.LocalCovFieldAlgebra}
    {x₀ : ι} {y₀ : κ} {cX : ι → ℂ} {cY : κ → ℂ}
    (hA : repGaugeGroupI g A = A) (hX : repGaugeGroupI g (X x₀) = ∑ x,
      cX x • X x)
    (hY : repGaugeGroupI g (Y y₀) = ∑ y, cY y • Y y) :
    repGaugeGroupI g (A * (X x₀ * Y y₀)) = ∑ x, ∑ y, (cX x * cY y) •
      (A * (X x * Y y)) := by
  rw [repGaugeGroupI_mul, repGaugeGroupI_mul, hA, hX, hY]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [mul_comm]

/-- A triple product whose second factor is fixed. -/
lemma repGauge_mul_fixed_mid (g : GaugeGroupI) {ι κ : Type} [Fintype ι] [Fintype κ]
    {A : ι → fieldData.LocalCovFieldAlgebra} {X : fieldData.LocalCovFieldAlgebra}
    {Y : κ → fieldData.LocalCovFieldAlgebra}
    {a₀ : ι} {y₀ : κ} {cA : ι → ℂ} {cY : κ → ℂ}
    (hA : repGaugeGroupI g (A a₀) = ∑ a, cA a • A a)
      (hX : repGaugeGroupI g X = X)
    (hY : repGaugeGroupI g (Y y₀) = ∑ y, cY y • Y y) :
    repGaugeGroupI g (A a₀ * (X * Y y₀)) = ∑ a, ∑ y, (cA a * cY y) •
      (A a * (X * Y y)) := by
  rw [repGaugeGroupI_mul, repGaugeGroupI_mul, hA, hX, hY]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [mul_comm]

/-- A triple product whose third factor is fixed. -/
lemma repGauge_mul_fixed_right (g : GaugeGroupI) {ι κ : Type} [Fintype ι] [Fintype κ]
    {A : ι → fieldData.LocalCovFieldAlgebra} {X : κ → fieldData.LocalCovFieldAlgebra}
    {Y : fieldData.LocalCovFieldAlgebra} {a₀ : ι}
    {x₀ : κ} {cA : ι → ℂ} {cX : κ → ℂ}
    (hA : repGaugeGroupI g (A a₀) = ∑ a, cA a • A a)
    (hX : repGaugeGroupI g (X x₀) = ∑ x, cX x • X x)
      (hY : repGaugeGroupI g Y = Y) :
    repGaugeGroupI g (A a₀ * (X x₀ * Y)) = ∑ a, ∑ x, (cA a * cX x) •
      (A a * (X x * Y)) := by
  rw [repGaugeGroupI_mul, repGaugeGroupI_mul, hA, hX, hY]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [mul_comm]

/-- The Lorentz analogue of `repGauge_mul_fixed_left`, the Higgs factor being inert. -/
lemma repLorentz_mul_fixed_left (Λ : SL(2,ℂ)) {ι κ : Type} [Fintype ι] [Fintype κ]
    {A : fieldData.LocalCovFieldAlgebra} {X : ι → fieldData.LocalCovFieldAlgebra}
    {Y : κ → fieldData.LocalCovFieldAlgebra}
    {x₀ : ι} {y₀ : κ} {cX : ι → ℂ} {cY : κ → ℂ}
    (hA : repLorentzGroup Λ A = A) (hX : repLorentzGroup Λ (X x₀) = ∑ x,
      cX x • X x)
    (hY : repLorentzGroup Λ (Y y₀) = ∑ y, cY y • Y y) :
    repLorentzGroup Λ (A * (X x₀ * Y y₀)) = ∑ x, ∑ y, (cX x * cY y) •
      (A * (X x * Y y)) := by
  rw [repLorentzGroup_mul, repLorentzGroup_mul, hA, hX, hY]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [mul_comm]

/-!

## B. The transformation laws of the Higgs symbols

Each Higgs symbol is read at the three factors of a gauge transformation in turn, and at the
Lorentz group. Colour fixes it, isospin moves its isospin index, and hypercharge is an overall
scalar, the power of which is the `6Y = ∓3` of the Higgs and its conjugate. The same laws for
the ten fermion species are `FermionSector.repGauge_su3_d` and its companions, next to the
components in `FermionSector/Components.lean`.

-/

/-- A colour transformation fixes a Higgs symbol. -/
lemma repGauge_su3_higgs (U : specialUnitaryGroup (Fin 3) ℂ) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (i : Fin 2) :
    repGaugeGroupI ((U, 1, 1) : GaugeGroupI) (ScalarSector.higgs l i)
      = ScalarSector.higgs l i := by
  rw [ScalarSector.rep_higgsComponent]
  simp [Matrix.one_apply]

/-- An isospin transformation moves the isospin index of a Higgs symbol by the conjugate
  matrix, the index being anti-fundamental. -/
lemma repGauge_su2_higgs (V : specialUnitaryGroup (Fin 2) ℂ) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (i : Fin 2) :
    repGaugeGroupI ((1, V, 1) : GaugeGroupI) (ScalarSector.higgs l i)
      = ∑ a, conj (V.1 a i) • ScalarSector.higgs l a := by
  rw [ScalarSector.rep_higgsComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su2Elt, toSU2_su2Elt, toU1_su2Elt, su2_inv_apply]
  simp

/-- A hypercharge transformation scales a Higgs symbol by the cube of the conjugate
  scalar, the Higgs carrying `6Y = -3`. -/
lemma repGauge_u1_higgs (t : unitary ℂ) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (i : Fin 2) :
    repGaugeGroupI ((1, 1, t) : GaugeGroupI) (ScalarSector.higgs l i)
      = (star (t : ℂ)) ^ 3 • ScalarSector.higgs l i := by
  rw [ScalarSector.rep_higgsComponent]
  simp [Matrix.one_apply, unitary_inv_coe]

/-- A colour transformation fixes a conjugate Higgs symbol. -/
lemma repGauge_su3_barHiggs (U : specialUnitaryGroup (Fin 3) ℂ) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (i : Fin 2) :
    repGaugeGroupI ((U, 1, 1) : GaugeGroupI) (ScalarSector.barHiggs l i)
      = ScalarSector.barHiggs l i := by
  rw [ScalarSector.rep_barHiggsComponent]
  simp [Matrix.one_apply]

/-- An isospin transformation moves the isospin index of a conjugate Higgs symbol by the
  matrix itself, the index being fundamental. -/
lemma repGauge_su2_barHiggs (V : specialUnitaryGroup (Fin 2) ℂ) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (i : Fin 2) :
    repGaugeGroupI ((1, V, 1) : GaugeGroupI) (ScalarSector.barHiggs l i)
      = ∑ a, V.1 a i • ScalarSector.barHiggs l a := by
  rw [ScalarSector.rep_barHiggsComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su2Elt, toSU2_su2Elt, toU1_su2Elt, su2_inv_apply]
  simp

/-- A hypercharge transformation scales a conjugate Higgs symbol by the cube of the
  scalar, the conjugate Higgs carrying `6Y = 3`. -/
lemma repGauge_u1_barHiggs (t : unitary ℂ) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (i : Fin 2) :
    repGaugeGroupI ((1, 1, t) : GaugeGroupI) (ScalarSector.barHiggs l i)
      = (t : ℂ) ^ 3 • ScalarSector.barHiggs l i := by
  rw [ScalarSector.rep_barHiggsComponent]
  simp [Matrix.one_apply, unitary_inv_coe, apply_ite (starRingEnd ℂ)]

/-- A Higgs symbol carrying no derivatives is Lorentz invariant. -/
lemma repLorentz_higgs_zero (Λ : SL(2,ℂ)) (l : Fin 0 → Fin 1 ⊕ Fin 3) (i : Fin 2) :
    repLorentzGroup Λ (ScalarSector.higgs l i) = ScalarSector.higgs l i := by
  rw [ScalarSector.repLorentz_higgs, FermionSector.univ_derivIndex_zero l,
    Finset.sum_singleton]
  simp

/-- A conjugate Higgs symbol carrying no derivatives is Lorentz invariant. -/
lemma repLorentz_barHiggs_zero (Λ : SL(2,ℂ)) (l : Fin 0 → Fin 1 ⊕ Fin 3) (i : Fin 2) :
    repLorentzGroup Λ (ScalarSector.barHiggs l i) = ScalarSector.barHiggs l i := by
  rw [ScalarSector.repLorentz_barHiggs, FermionSector.univ_derivIndex_zero l,
    Finset.sum_singleton]
  simp

/-!

## C. The symbols inside the derivative submodules

A block is a product of three underived symbols, and by
`sectorMassWeight_higgs_fermion_eight` the sector at mass weight eight is the product of
the Higgs derivative submodule with two copies of the fermion one.  So a block sits at mass
weight eight as soon as each of its three symbols is seen inside the matching derivative
submodule.  The ten ranges are recorded as inclusions rather than as memberships, since
section F needs the inclusion and the membership of a component follows from it.

-/

/-- A Higgs symbol lies in the Higgs derivative submodule. -/
lemma higgs_mem_derivSubmodule {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (i : Fin 2) :
    ScalarSector.higgs l i ∈ ScalarSector.derivSubmodule n :=
  Submodule.mem_sup_left (Submodule.mem_iSup_of_mem l ⟨_, rfl⟩)

/-- A conjugate Higgs symbol lies in the Higgs derivative submodule. -/
lemma barHiggs_mem_derivSubmodule {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (i : Fin 2) :
    ScalarSector.barHiggs l i ∈ ScalarSector.derivSubmodule n :=
  Submodule.mem_sup_right (Submodule.mem_iSup_of_mem l ⟨_, rfl⟩)

/-- The range of a down-singlet symbol map lies in the fermion derivative submodule. -/
lemma range_d_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (downSingletField f l) ≤ FermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (
    le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (
    le_sup_of_le_left (le_sup_of_le_left le_sup_left))))))))

/-- The range of a conjugate down-singlet symbol map lies in the fermion derivative submodule. -/
lemma range_bard_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (conjDownSingletField f l) ≤ FermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (
    le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (
    le_sup_of_le_left (le_sup_of_le_left le_sup_right))))))))

/-- The range of an up-singlet symbol map lies in the fermion derivative submodule. -/
lemma range_u_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (upSingletField f l) ≤ FermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (
    le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (
    le_sup_of_le_left le_sup_right)))))))

/-- The range of a conjugate up-singlet symbol map lies in the fermion derivative submodule. -/
lemma range_baru_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (conjUpSingletField f l) ≤ FermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (
    le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))))))

/-- The range of a quark-doublet symbol map lies in the fermion derivative submodule. -/
lemma range_Q_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (quarkDoubletField f l) ≤ FermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (
    le_sup_of_le_left (le_sup_of_le_left le_sup_right)))))

/-- The range of a conjugate quark-doublet symbol map lies in the fermion derivative submodule. -/
lemma range_barQ_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (conjQuarkDoubletField f l) ≤ FermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (
    le_sup_of_le_left le_sup_right))))

/-- The range of a lepton-doublet symbol map lies in the fermion derivative submodule. -/
lemma range_L_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (leptonDoubletField f l) ≤ FermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right)))

/-- The range of a conjugate lepton-doublet symbol map lies in the fermion derivative submodule. -/
lemma range_barL_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (conjLeptonDoubletField f l) ≤ FermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l (le_sup_of_le_left (le_sup_of_le_left le_sup_right))

/-- The range of a lepton-singlet symbol map lies in the fermion derivative submodule. -/
lemma range_e_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (leptonSingletField f l) ≤ FermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l (le_sup_of_le_left le_sup_right)

/-- The range of a conjugate lepton-singlet symbol map lies in the fermion derivative submodule. -/
lemma range_bare_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (conjLeptonSingletField f l) ≤ FermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l le_sup_right

/-- A `d` component lies in the fermion derivative submodule. -/
lemma dComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    FermionSector.dComponent f l j ∈ FermionSector.derivSubmodule n :=
  LocalCovFieldAlgebra.range_d_le_derivSubmodule f l ⟨_, rfl⟩

/-- A `bard` component lies in the fermion derivative submodule. -/
lemma bardComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    FermionSector.bardComponent f l j ∈ FermionSector.derivSubmodule n :=
  LocalCovFieldAlgebra.range_bard_le_derivSubmodule f l ⟨_, rfl⟩

/-- A `u` component lies in the fermion derivative submodule. -/
lemma uComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    FermionSector.uComponent f l j ∈ FermionSector.derivSubmodule n :=
  LocalCovFieldAlgebra.range_u_le_derivSubmodule f l ⟨_, rfl⟩

/-- A `baru` component lies in the fermion derivative submodule. -/
lemma baruComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    FermionSector.baruComponent f l j ∈ FermionSector.derivSubmodule n :=
  LocalCovFieldAlgebra.range_baru_le_derivSubmodule f l ⟨_, rfl⟩

/-- A `Q` component lies in the fermion derivative submodule. -/
lemma QComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3 × Fin 2) :
    FermionSector.QComponent f l j ∈ FermionSector.derivSubmodule n :=
  LocalCovFieldAlgebra.range_Q_le_derivSubmodule f l ⟨_, rfl⟩

/-- A `barQ` component lies in the fermion derivative submodule. -/
lemma barQComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3 × Fin 2) :
    FermionSector.barQComponent f l j ∈ FermionSector.derivSubmodule n :=
  LocalCovFieldAlgebra.range_barQ_le_derivSubmodule f l ⟨_, rfl⟩

/-- A `L` component lies in the fermion derivative submodule. -/
lemma LComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 2) :
    FermionSector.LComponent f l j ∈ FermionSector.derivSubmodule n :=
  LocalCovFieldAlgebra.range_L_le_derivSubmodule f l ⟨_, rfl⟩

/-- A `barL` component lies in the fermion derivative submodule. -/
lemma barLComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 2) :
    FermionSector.barLComponent f l j ∈ FermionSector.derivSubmodule n :=
  LocalCovFieldAlgebra.range_barL_le_derivSubmodule f l ⟨_, rfl⟩

/-- A `e` component lies in the fermion derivative submodule. -/
lemma eComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2) :
    FermionSector.eComponent f l j ∈ FermionSector.derivSubmodule n :=
  LocalCovFieldAlgebra.range_e_le_derivSubmodule f l ⟨_, rfl⟩

/-- A `bare` component lies in the fermion derivative submodule. -/
lemma bareComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2) :
    FermionSector.bareComponent f l j ∈ FermionSector.derivSubmodule n :=
  LocalCovFieldAlgebra.range_bare_le_derivSubmodule f l ⟨_, rfl⟩

/-!

## D. The two fermion orderings

The twelve blocks of the mass-weight-eight decomposition are six choices of a Higgs symbol
and a fermion pair, each occurring in both fermion orderings.  The two orderings are not
the same element — the fermion symbols anticommute, so one is minus the other — but they
span the same submodule, and therefore have the same weight pieces.  So a classification of
one ordering is a classification of the other, and the six transposed blocks need no
argument of their own.

-/

/-- Two submodules of fermion derivative submodules commute, the fermion symbols
  anticommuting and a submodule being closed under negation. -/
lemma mul_comm_of_le_derivSubmodule {n m : ℕ} {V W : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    (hV : V ≤ FermionSector.derivSubmodule n)
    (hW : W ≤ FermionSector.derivSubmodule m) : V * W = W * V := by
  refine le_antisymm ?_ ?_ <;> rw [Submodule.mul_le] <;> intro x hx y hy
  · rw [FermionSector.anticomm_of_mem_derivSubmodule (hV hx) (hW hy)]
    exact Submodule.neg_mem _ (Submodule.mul_mem_mul hy hx)
  · rw [FermionSector.anticomm_of_mem_derivSubmodule (hW hx) (hV hy)]
    exact Submodule.neg_mem _ (Submodule.mul_mem_mul hy hx)

/-- Swapping the two fermion factors of a block leaves every weight piece unchanged. The
  two fermion factors commute as submodules, so the two orderings of the block are the same
  submodule. This is what makes the six transposed blocks of the mass-weight-eight
  decomposition a rewrite rather than six fresh classifications. -/
lemma mul_mul_piece_swap {VH VX VY : Submodule ℂ fieldData.LocalCovFieldAlgebra} {n m : ℕ}
    (dH : GaugeWeightDecomposition repGaugeGroupI VH)
    (dX : GaugeWeightDecomposition repGaugeGroupI VX)
    (dY : GaugeWeightDecomposition repGaugeGroupI VY)
    (hX : VX ≤ FermionSector.derivSubmodule n)
    (hY : VY ≤ FermionSector.derivSubmodule m) (w : GaugeWeight) :
    (GaugeWeightDecomposition.mul (d := dH)
        (d' := GaugeWeightDecomposition.mul (d := dX) (d' := dY))).piece w
      = (GaugeWeightDecomposition.mul (d := dH)
        (d' := GaugeWeightDecomposition.mul (d := dY) (d' := dX))).piece w :=
  GaugeWeightDecomposition.piece_congr
    (d := GaugeWeightDecomposition.mul (d := dH)
      (d' := GaugeWeightDecomposition.mul (d := dX) (d' := dY)))
    (d' := GaugeWeightDecomposition.mul (d := dH)
      (d' := GaugeWeightDecomposition.mul (d := dY) (d' := dX)))
    (by rw [LocalCovFieldAlgebra.mul_comm_of_le_derivSubmodule hX hY]) w

/-- Swapping the two fermion factors of a block negates it. -/
lemma mul_mul_swap_eq_neg {n m : ℕ} (a : fieldData.LocalCovFieldAlgebra)
    {x y : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ FermionSector.derivSubmodule n)
    (hy : y ∈ FermionSector.derivSubmodule m) :
    a * (y * x) = -(a * (x * y)) := by
  rw [FermionSector.anticomm_of_mem_derivSubmodule hy hx, mul_neg]

end LocalCovFieldAlgebra

end StandardModel
