/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsCovStandardModel.YukawaSector.Basic
public import Physlib.Particles.StandardModel.IsFermionSector.Components
public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU3FunAntiFun
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2AntiFundamental
public import Physlib.Relativity.LorentzGroup.Invariants.IsBiLeftWeyl
public import Physlib.Particles.StandardModel.Peeling
/-!
# The symbols of the Yukawa blocks

## i. Overview

At mass weight eight a Yukawa block is a product of three underived symbols, one Higgs and
two fermions, and every statement about such a block reduces to statements about its three
factors. This file is that reduction: it reads each of the twelve symbols at each factor of
a gauge transformation, does the algebra of a triple product with one inert factor once for
each position the inert factor can occupy, and records the closure of the index laws under
the sums and differences a contraction performs.

Two things here are easy to get wrong and are settled once. A gauge transformation is a
triple and the three index laws each constrain one factor of it: colour, isospin and
Lorentz between them say nothing about hypercharge, so hypercharge is a fourth step and not
a corollary of the other three, and `forall_repGauge_eq_self`, in `StandardModel.Peeling`
with the rest of the shared framework, is what assembles the four into gauge invariance.
And the twelve blocks come in two fermion orderings, but the fermion
symbols anticommute, so the two orderings of a block span the same submodule and have the
same weight pieces: `mul_mul_piece_swap` is what makes the six transposed blocks a rewrite
rather than six fresh derivations.

## ii. Key results

- `repGauge_mul_fixed_left`, `repGauge_mul_fixed_mid`, `repGauge_mul_fixed_right`,
  `repLorentz_mul_fixed_left` : the transformation of a triple product with one inert
  factor.
- `repGauge_su3_*`, `repGauge_su2_*`, `repGauge_u1_*` : the three gauge laws of each of the
  twelve symbols.
- `mul_mul_piece_swap` : the two fermion orderings of a block have the same weight pieces.

## iii. Table of contents

- A. Triple products with one inert factor
- B. The transformation laws of the symbols
  - B.1. The Higgs symbols
  - B.2. The down singlet
  - B.3. The conjugate down singlet
  - B.4. The up singlet
  - B.5. The conjugate up singlet
  - B.6. The quark doublet
  - B.7. The conjugate quark doublet
  - B.8. The lepton doublet
  - B.9. The conjugate lepton doublet
  - B.10. The lepton singlet
  - B.11. The conjugate lepton singlet
- C. The symbols inside the derivative submodules
- D. The two fermion orderings

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

## A. Triple products with one inert factor

Every block is a product of three symbols, and every classifier moves exactly two of them:
the third is inert, being a colour singlet, an isospin singlet or a Lorentz scalar.  The
three lemmas here do the algebra once for each position the inert factor can occupy, and
reduce a transformation law for a block to the laws of its factors.

-/

include h in
/-- A triple product whose first factor is fixed and whose second and third move by given
  coefficients moves by the product of those coefficients. -/
lemma repGauge_mul_fixed_left (g : GaugeGroupI) {ι κ : Type} [Fintype ι] [Fintype κ]
    {A : B} {X : ι → B} {Y : κ → B} {x₀ : ι} {y₀ : κ} {cX : ι → ℂ} {cY : κ → ℂ}
    (hA : repGauge g A = A) (hX : repGauge g (X x₀) = ∑ x, cX x • X x)
    (hY : repGauge g (Y y₀) = ∑ y, cY y • Y y) :
    repGauge g (A * (X x₀ * Y y₀)) = ∑ x, ∑ y, (cX x * cY y) • (A * (X x * Y y)) := by
  rw [h.isHiggsSector.rep_mul, h.isHiggsSector.rep_mul, hA, hX, hY]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [mul_comm]

include h in
/-- A triple product whose second factor is fixed. -/
lemma repGauge_mul_fixed_mid (g : GaugeGroupI) {ι κ : Type} [Fintype ι] [Fintype κ]
    {A : ι → B} {X : B} {Y : κ → B} {a₀ : ι} {y₀ : κ} {cA : ι → ℂ} {cY : κ → ℂ}
    (hA : repGauge g (A a₀) = ∑ a, cA a • A a) (hX : repGauge g X = X)
    (hY : repGauge g (Y y₀) = ∑ y, cY y • Y y) :
    repGauge g (A a₀ * (X * Y y₀)) = ∑ a, ∑ y, (cA a * cY y) • (A a * (X * Y y)) := by
  rw [h.isHiggsSector.rep_mul, h.isHiggsSector.rep_mul, hA, hX, hY]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [mul_comm]

include h in
/-- A triple product whose third factor is fixed. -/
lemma repGauge_mul_fixed_right (g : GaugeGroupI) {ι κ : Type} [Fintype ι] [Fintype κ]
    {A : ι → B} {X : κ → B} {Y : B} {a₀ : ι} {x₀ : κ} {cA : ι → ℂ} {cX : κ → ℂ}
    (hA : repGauge g (A a₀) = ∑ a, cA a • A a)
    (hX : repGauge g (X x₀) = ∑ x, cX x • X x) (hY : repGauge g Y = Y) :
    repGauge g (A a₀ * (X x₀ * Y)) = ∑ a, ∑ x, (cA a * cX x) • (A a * (X x * Y)) := by
  rw [h.isHiggsSector.rep_mul, h.isHiggsSector.rep_mul, hA, hX, hY]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [mul_comm]

include h in
/-- The Lorentz analogue of `repGauge_mul_fixed_left`, the Higgs factor being inert. -/
lemma repLorentz_mul_fixed_left (Λ : SL(2,ℂ)) {ι κ : Type} [Fintype ι] [Fintype κ]
    {A : B} {X : ι → B} {Y : κ → B} {x₀ : ι} {y₀ : κ} {cX : ι → ℂ} {cY : κ → ℂ}
    (hA : repLorentz Λ A = A) (hX : repLorentz Λ (X x₀) = ∑ x, cX x • X x)
    (hY : repLorentz Λ (Y y₀) = ∑ y, cY y • Y y) :
    repLorentz Λ (A * (X x₀ * Y y₀)) = ∑ x, ∑ y, (cX x * cY y) • (A * (X x * Y y)) := by
  rw [h.isHiggsSector.repLorentz_mul, h.isHiggsSector.repLorentz_mul, hA, hX, hY]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [mul_comm]

/-!

## B. The transformation laws of the symbols

Each symbol is read at the three factors of a gauge transformation in turn, and the Higgs
symbols also at the Lorentz group.  Colour moves only a colour index, isospin only an
isospin index, and hypercharge is an overall scalar, the power of which is the `6Y` of the
species: `-3` for the Higgs symbols, `2` for the down singlet, `1` for the conjugate quark
doublet, `4` for the conjugate up singlet, `-1` for the quark doublet, `-3` for the
conjugate lepton doublet and `6` for the lepton singlet.  A symbol carrying no index of a
given factor is fixed by it outright.

-/

/-!

### B.1. The Higgs symbols

-/

/-- A colour transformation fixes a Higgs symbol. -/
lemma repGauge_su3_higgs (U : specialUnitaryGroup (Fin 3) ℂ) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (i : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.isHiggsSector.higgs l i)
      = h.isHiggsSector.higgs l i := by
  rw [h.isHiggsSector.rep_higgsComponent]
  simp [Matrix.one_apply]

/-- An isospin transformation moves the isospin index of a Higgs symbol by the conjugate
  matrix, the index being anti-fundamental. -/
lemma repGauge_su2_higgs (V : specialUnitaryGroup (Fin 2) ℂ) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (i : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.isHiggsSector.higgs l i)
      = ∑ a, conj (V.1 a i) • h.isHiggsSector.higgs l a := by
  rw [h.isHiggsSector.rep_higgsComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su2Elt, toSU2_su2Elt, toU1_su2Elt, su2_inv_apply]
  simp

/-- A hypercharge transformation scales a Higgs symbol by the cube of the conjugate
  scalar, the Higgs carrying `6Y = -3`. -/
lemma repGauge_u1_higgs (t : unitary ℂ) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (i : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.isHiggsSector.higgs l i)
      = (star (t : ℂ)) ^ 3 • h.isHiggsSector.higgs l i := by
  rw [h.isHiggsSector.rep_higgsComponent]
  simp [Matrix.one_apply, unitary_inv_coe]

/-- A colour transformation fixes a conjugate Higgs symbol. -/
lemma repGauge_su3_barHiggs (U : specialUnitaryGroup (Fin 3) ℂ) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (i : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.isHiggsSector.barHiggs l i)
      = h.isHiggsSector.barHiggs l i := by
  rw [h.isHiggsSector.rep_barHiggsComponent]
  simp [Matrix.one_apply]

/-- An isospin transformation moves the isospin index of a conjugate Higgs symbol by the
  matrix itself, the index being fundamental. -/
lemma repGauge_su2_barHiggs (V : specialUnitaryGroup (Fin 2) ℂ) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (i : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.isHiggsSector.barHiggs l i)
      = ∑ a, V.1 a i • h.isHiggsSector.barHiggs l a := by
  rw [h.isHiggsSector.rep_barHiggsComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su2Elt, toSU2_su2Elt, toU1_su2Elt, su2_inv_apply]
  simp

/-- A hypercharge transformation scales a conjugate Higgs symbol by the cube of the
  scalar, the conjugate Higgs carrying `6Y = 3`. -/
lemma repGauge_u1_barHiggs (t : unitary ℂ) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (i : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.isHiggsSector.barHiggs l i)
      = (t : ℂ) ^ 3 • h.isHiggsSector.barHiggs l i := by
  rw [h.isHiggsSector.rep_barHiggsComponent]
  simp [Matrix.one_apply, unitary_inv_coe, apply_ite (starRingEnd ℂ)]

/-- A Higgs symbol carrying no derivatives is Lorentz invariant. -/
lemma repLorentz_higgs_zero (Λ : SL(2,ℂ)) (l : Fin 0 → Fin 1 ⊕ Fin 3) (i : Fin 2) :
    repLorentz Λ (h.isHiggsSector.higgs l i) = h.isHiggsSector.higgs l i := by
  rw [h.isHiggsSector.repLorentz_higgs, IsFermionSector.univ_derivIndex_zero l,
    Finset.sum_singleton]
  simp

/-- A conjugate Higgs symbol carrying no derivatives is Lorentz invariant. -/
lemma repLorentz_barHiggs_zero (Λ : SL(2,ℂ)) (l : Fin 0 → Fin 1 ⊕ Fin 3) (i : Fin 2) :
    repLorentz Λ (h.isHiggsSector.barHiggs l i) = h.isHiggsSector.barHiggs l i := by
  rw [h.isHiggsSector.repLorentz_barHiggs, IsFermionSector.univ_derivIndex_zero l,
    Finset.sum_singleton]
  simp

/-!

### B.2. The down singlet

-/

/-- A colour transformation moves the colour index of a down-singlet symbol by the
  conjugate matrix, the index being anti-fundamental. -/
lemma repGauge_su3_d (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.isFermionSector.dComponent f l (s, c))
      = ∑ a, conj (U.1 a c) • h.isFermionSector.dComponent f l (s, a) := by
  rw [h.isFermionSector.rep_dComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su3Elt, toSU3_su3Elt, toU1_su3Elt, su3_inv_apply]
  simp

/-- An isospin transformation fixes a down-singlet symbol, which carries no isospin. -/
lemma repGauge_su2_d (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.isFermionSector.dComponent f l j)
      = h.isFermionSector.dComponent f l j := by
  rw [h.isFermionSector.rep_dComponent]
  simp [Matrix.one_apply]

/-- A hypercharge transformation scales a down-singlet symbol by the square of the scalar,
  the down singlet carrying `6Y = 2`. -/
lemma repGauge_u1_d (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.isFermionSector.dComponent f l j)
      = (t : ℂ) ^ 2 • h.isFermionSector.dComponent f l j := by
  rw [h.isFermionSector.rep_dComponent]
  simp [Matrix.one_apply, unitary_inv_coe]

/-!

### B.3. The conjugate down singlet

-/

/-- A colour transformation moves the colour index of a conjugate down-singlet symbol by
  the matrix itself, the index being fundamental. -/
lemma repGauge_su3_bard (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.isFermionSector.bardComponent f l (s, c))
      = ∑ a, U.1 a c • h.isFermionSector.bardComponent f l (s, a) := by
  rw [h.isFermionSector.rep_bardComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su3Elt, toSU3_su3Elt, toU1_su3Elt, su3_inv_apply]
  simp

/-- An isospin transformation fixes a conjugate down-singlet symbol. -/
lemma repGauge_su2_bard (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.isFermionSector.bardComponent f l j)
      = h.isFermionSector.bardComponent f l j := by
  rw [h.isFermionSector.rep_bardComponent]
  simp [Matrix.one_apply]

/-- A hypercharge transformation scales a conjugate down-singlet symbol by the square of
  the conjugate scalar, the conjugate down singlet carrying `6Y = -2`. -/
lemma repGauge_u1_bard (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.isFermionSector.bardComponent f l j)
      = (star (t : ℂ)) ^ 2 • h.isFermionSector.bardComponent f l j := by
  rw [h.isFermionSector.rep_bardComponent]
  simp [Matrix.one_apply, unitary_inv_coe, apply_ite (starRingEnd ℂ)]

/-!

### B.4. The up singlet

-/

/-- A colour transformation moves the colour index of an up-singlet symbol by the
  conjugate matrix, the index being anti-fundamental. -/
lemma repGauge_su3_u (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.isFermionSector.uComponent f l (s, c))
      = ∑ a, conj (U.1 a c) • h.isFermionSector.uComponent f l (s, a) := by
  rw [h.isFermionSector.rep_uComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su3Elt, toSU3_su3Elt, toU1_su3Elt, su3_inv_apply]
  simp

/-- An isospin transformation fixes an up-singlet symbol. -/
lemma repGauge_su2_u (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.isFermionSector.uComponent f l j)
      = h.isFermionSector.uComponent f l j := by
  rw [h.isFermionSector.rep_uComponent]
  simp [Matrix.one_apply]

/-- A hypercharge transformation scales an up-singlet symbol by the fourth power of the
  conjugate scalar, the up singlet carrying `6Y = -4`. -/
lemma repGauge_u1_u (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.isFermionSector.uComponent f l j)
      = (star (t : ℂ)) ^ 4 • h.isFermionSector.uComponent f l j := by
  rw [h.isFermionSector.rep_uComponent]
  simp [Matrix.one_apply, unitary_inv_coe]

/-!

### B.5. The conjugate up singlet

-/

/-- A colour transformation moves the colour index of a conjugate up-singlet symbol by the
  matrix itself, the index being fundamental. -/
lemma repGauge_su3_baru (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.isFermionSector.baruComponent f l (s, c))
      = ∑ a, U.1 a c • h.isFermionSector.baruComponent f l (s, a) := by
  rw [h.isFermionSector.rep_baruComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su3Elt, toSU3_su3Elt, toU1_su3Elt, su3_inv_apply]
  simp

/-- An isospin transformation fixes a conjugate up-singlet symbol. -/
lemma repGauge_su2_baru (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.isFermionSector.baruComponent f l j)
      = h.isFermionSector.baruComponent f l j := by
  rw [h.isFermionSector.rep_baruComponent]
  simp [Matrix.one_apply]

/-- A hypercharge transformation scales a conjugate up-singlet symbol by the fourth power
  of the scalar, the conjugate up singlet carrying `6Y = 4`. -/
lemma repGauge_u1_baru (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.isFermionSector.baruComponent f l j)
      = (t : ℂ) ^ 4 • h.isFermionSector.baruComponent f l j := by
  rw [h.isFermionSector.rep_baruComponent]
  simp [Matrix.one_apply, unitary_inv_coe, apply_ite (starRingEnd ℂ)]

/-!

### B.6. The quark doublet

-/

/-- A colour transformation moves the colour index of a quark-doublet symbol by the
  conjugate matrix, the index being anti-fundamental. -/
lemma repGauge_su3_Q (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) (w : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.isFermionSector.QComponent f l (s, c, w))
      = ∑ a, conj (U.1 a c) • h.isFermionSector.QComponent f l (s, a, w) := by
  rw [h.isFermionSector.rep_QComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.sum_univ_two, inv_su3Elt, toSU3_su3Elt, toU1_su3Elt, toSU2_su3Elt]
  fin_cases w <;> simp [su3_inv_apply]

/-- An isospin transformation moves the isospin index of a quark-doublet symbol by the
  conjugate matrix, the index being anti-fundamental. -/
lemma repGauge_su2_Q (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) (w : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.isFermionSector.QComponent f l (s, c, w))
      = ∑ a, conj (V.1 a w) • h.isFermionSector.QComponent f l (s, c, a) := by
  rw [h.isFermionSector.rep_QComponent, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.sum_univ_three, inv_su2Elt, toSU2_su2Elt, toU1_su2Elt, toSU3_su2Elt]
  fin_cases c <;> simp [su2_inv_apply]

/-- A hypercharge transformation scales a quark-doublet symbol by the conjugate scalar,
  the quark doublet carrying `6Y = -1`. -/
lemma repGauge_u1_Q (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (s : Fin 2) (c : Fin 3) (w : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.isFermionSector.QComponent f l (s, c, w))
      = star (t : ℂ) • h.isFermionSector.QComponent f l (s, c, w) := by
  rw [h.isFermionSector.rep_QComponent]
  fin_cases w <;> simp [Matrix.one_apply, unitary_inv_coe]

/-!

### B.7. The conjugate quark doublet

-/

/-- A colour transformation moves the colour index of a conjugate quark-doublet symbol by
  the matrix itself, the index being fundamental. -/
lemma repGauge_su3_barQ (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) (w : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.isFermionSector.barQComponent f l (s, c, w))
      = ∑ a, U.1 a c • h.isFermionSector.barQComponent f l (s, a, w) := by
  rw [h.isFermionSector.rep_barQComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.sum_univ_two]
  rw [inv_su3Elt, toSU3_su3Elt, toU1_su3Elt, toSU2_su3Elt]
  fin_cases w <;> simp [su3_inv_apply]

/-- An isospin transformation moves the isospin index of a conjugate quark-doublet symbol
  by the matrix itself, the index being fundamental. -/
lemma repGauge_su2_barQ (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) (w : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.isFermionSector.barQComponent f l (s, c, w))
      = ∑ a, V.1 a w • h.isFermionSector.barQComponent f l (s, c, a) := by
  rw [h.isFermionSector.rep_barQComponent, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.sum_univ_three, inv_su2Elt, toSU2_su2Elt, toU1_su2Elt, toSU3_su2Elt]
  fin_cases c <;> simp [su2_inv_apply]

/-- A hypercharge transformation scales a conjugate quark-doublet symbol by the scalar,
  the conjugate quark doublet carrying `6Y = 1`. -/
lemma repGauge_u1_barQ (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (s : Fin 2) (c : Fin 3) (w : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.isFermionSector.barQComponent f l (s, c, w))
      = (t : ℂ) • h.isFermionSector.barQComponent f l (s, c, w) := by
  rw [h.isFermionSector.rep_barQComponent]
  fin_cases w <;>
    simp [Matrix.one_apply, unitary_inv_coe, apply_ite (starRingEnd ℂ)]

/-!

### B.8. The lepton doublet

-/

/-- A colour transformation fixes a lepton-doublet symbol, which carries no colour. -/
lemma repGauge_su3_L (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.isFermionSector.LComponent f l j)
      = h.isFermionSector.LComponent f l j := by
  rw [h.isFermionSector.rep_LComponent]
  simp [Matrix.one_apply]

/-- An isospin transformation moves the isospin index of a lepton-doublet symbol by the
  conjugate matrix, the index being anti-fundamental. -/
lemma repGauge_su2_L (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s w : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.isFermionSector.LComponent f l (s, w))
      = ∑ a, conj (V.1 a w) • h.isFermionSector.LComponent f l (s, a) := by
  rw [h.isFermionSector.rep_LComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su2Elt, toSU2_su2Elt, toU1_su2Elt, su2_inv_apply]
  simp

/-- A hypercharge transformation scales a lepton-doublet symbol by the cube of the scalar,
  the lepton doublet carrying `6Y = 3`. -/
lemma repGauge_u1_L (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.isFermionSector.LComponent f l j)
      = (t : ℂ) ^ 3 • h.isFermionSector.LComponent f l j := by
  rw [h.isFermionSector.rep_LComponent]
  simp [Matrix.one_apply, unitary_inv_coe]

/-!

### B.9. The conjugate lepton doublet

-/

/-- A colour transformation fixes a conjugate lepton-doublet symbol, which carries no
  colour. -/
lemma repGauge_su3_barL (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.isFermionSector.barLComponent f l j)
      = h.isFermionSector.barLComponent f l j := by
  rw [h.isFermionSector.rep_barLComponent]
  simp [Matrix.one_apply]

/-- An isospin transformation moves the isospin index of a conjugate lepton-doublet symbol
  by the matrix itself, the index being fundamental. -/
lemma repGauge_su2_barL (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s w : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.isFermionSector.barLComponent f l (s, w))
      = ∑ a, V.1 a w • h.isFermionSector.barLComponent f l (s, a) := by
  rw [h.isFermionSector.rep_barLComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su2Elt, toSU2_su2Elt, toU1_su2Elt, su2_inv_apply]
  simp

/-- A hypercharge transformation scales a conjugate lepton-doublet symbol by the cube of
  the conjugate scalar, the conjugate lepton doublet carrying `6Y = -3`. -/
lemma repGauge_u1_barL (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (s w : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.isFermionSector.barLComponent f l (s, w))
      = (star (t : ℂ)) ^ 3 • h.isFermionSector.barLComponent f l (s, w) := by
  rw [h.isFermionSector.rep_barLComponent]
  fin_cases w <;>
    simp [Matrix.one_apply, unitary_inv_coe, apply_ite (starRingEnd ℂ)]

/-!

### B.10. The lepton singlet

-/

/-- A colour transformation fixes a lepton-singlet symbol. -/
lemma repGauge_su3_e (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.isFermionSector.eComponent f l s)
      = h.isFermionSector.eComponent f l s := by
  rw [h.isFermionSector.rep_eComponent]
  simp

/-- An isospin transformation fixes a lepton-singlet symbol. -/
lemma repGauge_su2_e (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.isFermionSector.eComponent f l s)
      = h.isFermionSector.eComponent f l s := by
  rw [h.isFermionSector.rep_eComponent]
  simp

/-- A hypercharge transformation scales a lepton-singlet symbol by the sixth power of the
  scalar, the lepton singlet carrying `6Y = 6`. -/
lemma repGauge_u1_e (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (s : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.isFermionSector.eComponent f l s)
      = (t : ℂ) ^ 6 • h.isFermionSector.eComponent f l s := by
  rw [h.isFermionSector.rep_eComponent]
  simp [unitary_inv_coe]

/-!

### B.11. The conjugate lepton singlet

-/

/-- A colour transformation fixes a conjugate lepton-singlet symbol. -/
lemma repGauge_su3_bare (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (h.isFermionSector.bareComponent f l s)
      = h.isFermionSector.bareComponent f l s := by
  rw [h.isFermionSector.rep_bareComponent]
  simp

/-- An isospin transformation fixes a conjugate lepton-singlet symbol. -/
lemma repGauge_su2_bare (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (h.isFermionSector.bareComponent f l s)
      = h.isFermionSector.bareComponent f l s := by
  rw [h.isFermionSector.rep_bareComponent]
  simp

/-- A hypercharge transformation scales a conjugate lepton-singlet symbol by the sixth
  power of the conjugate scalar, the conjugate lepton singlet carrying `6Y = -6`. -/
lemma repGauge_u1_bare (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (s : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (h.isFermionSector.bareComponent f l s)
      = (star (t : ℂ)) ^ 6 • h.isFermionSector.bareComponent f l s := by
  rw [h.isFermionSector.rep_bareComponent]
  simp [unitary_inv_coe]

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
    h.isHiggsSector.higgs l i ∈ h.isHiggsSector.derivSubmodule n :=
  Submodule.mem_sup_left (Submodule.mem_iSup_of_mem l ⟨_, rfl⟩)

/-- A conjugate Higgs symbol lies in the Higgs derivative submodule. -/
lemma barHiggs_mem_derivSubmodule {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (i : Fin 2) :
    h.isHiggsSector.barHiggs l i ∈ h.isHiggsSector.derivSubmodule n :=
  Submodule.mem_sup_right (Submodule.mem_iSup_of_mem l ⟨_, rfl⟩)

/-- The range of a down-singlet symbol map lies in the fermion derivative submodule. -/
lemma range_d_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (d f l) ≤ h.isFermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (
    le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (
    le_sup_of_le_left (le_sup_of_le_left le_sup_left))))))))

/-- The range of a conjugate down-singlet symbol map lies in the fermion derivative submodule. -/
lemma range_bard_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (bard f l) ≤ h.isFermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (
    le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (
    le_sup_of_le_left (le_sup_of_le_left le_sup_right))))))))

/-- The range of an up-singlet symbol map lies in the fermion derivative submodule. -/
lemma range_u_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (u f l) ≤ h.isFermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (
    le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (
    le_sup_of_le_left le_sup_right)))))))

/-- The range of a conjugate up-singlet symbol map lies in the fermion derivative submodule. -/
lemma range_baru_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (baru f l) ≤ h.isFermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (
    le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))))))

/-- The range of a quark-doublet symbol map lies in the fermion derivative submodule. -/
lemma range_Q_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (Q f l) ≤ h.isFermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (
    le_sup_of_le_left (le_sup_of_le_left le_sup_right)))))

/-- The range of a conjugate quark-doublet symbol map lies in the fermion derivative submodule. -/
lemma range_barQ_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (barQ f l) ≤ h.isFermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (
    le_sup_of_le_left le_sup_right))))

/-- The range of a lepton-doublet symbol map lies in the fermion derivative submodule. -/
lemma range_L_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (L f l) ≤ h.isFermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right)))

/-- The range of a conjugate lepton-doublet symbol map lies in the fermion derivative submodule. -/
lemma range_barL_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (barL f l) ≤ h.isFermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l (le_sup_of_le_left (le_sup_of_le_left le_sup_right))

/-- The range of a lepton-singlet symbol map lies in the fermion derivative submodule. -/
lemma range_e_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (e f l) ≤ h.isFermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l (le_sup_of_le_left le_sup_right)

/-- The range of a conjugate lepton-singlet symbol map lies in the fermion derivative submodule. -/
lemma range_bare_le_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (bare f l) ≤ h.isFermionSector.derivSubmodule n :=
  le_iSup₂_of_le f l le_sup_right

/-- A `d` component lies in the fermion derivative submodule. -/
lemma dComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    h.isFermionSector.dComponent f l j ∈ h.isFermionSector.derivSubmodule n :=
  h.range_d_le_derivSubmodule f l ⟨_, rfl⟩

/-- A `bard` component lies in the fermion derivative submodule. -/
lemma bardComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    h.isFermionSector.bardComponent f l j ∈ h.isFermionSector.derivSubmodule n :=
  h.range_bard_le_derivSubmodule f l ⟨_, rfl⟩

/-- A `u` component lies in the fermion derivative submodule. -/
lemma uComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    h.isFermionSector.uComponent f l j ∈ h.isFermionSector.derivSubmodule n :=
  h.range_u_le_derivSubmodule f l ⟨_, rfl⟩

/-- A `baru` component lies in the fermion derivative submodule. -/
lemma baruComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    h.isFermionSector.baruComponent f l j ∈ h.isFermionSector.derivSubmodule n :=
  h.range_baru_le_derivSubmodule f l ⟨_, rfl⟩

/-- A `Q` component lies in the fermion derivative submodule. -/
lemma QComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3 × Fin 2) :
    h.isFermionSector.QComponent f l j ∈ h.isFermionSector.derivSubmodule n :=
  h.range_Q_le_derivSubmodule f l ⟨_, rfl⟩

/-- A `barQ` component lies in the fermion derivative submodule. -/
lemma barQComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3 × Fin 2) :
    h.isFermionSector.barQComponent f l j ∈ h.isFermionSector.derivSubmodule n :=
  h.range_barQ_le_derivSubmodule f l ⟨_, rfl⟩

/-- A `L` component lies in the fermion derivative submodule. -/
lemma LComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 2) :
    h.isFermionSector.LComponent f l j ∈ h.isFermionSector.derivSubmodule n :=
  h.range_L_le_derivSubmodule f l ⟨_, rfl⟩

/-- A `barL` component lies in the fermion derivative submodule. -/
lemma barLComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 2) :
    h.isFermionSector.barLComponent f l j ∈ h.isFermionSector.derivSubmodule n :=
  h.range_barL_le_derivSubmodule f l ⟨_, rfl⟩

/-- A `e` component lies in the fermion derivative submodule. -/
lemma eComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2) :
    h.isFermionSector.eComponent f l j ∈ h.isFermionSector.derivSubmodule n :=
  h.range_e_le_derivSubmodule f l ⟨_, rfl⟩

/-- A `bare` component lies in the fermion derivative submodule. -/
lemma bareComponent_mem_derivSubmodule (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2) :
    h.isFermionSector.bareComponent f l j ∈ h.isFermionSector.derivSubmodule n :=
  h.range_bare_le_derivSubmodule f l ⟨_, rfl⟩

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
lemma mul_comm_of_le_derivSubmodule {n m : ℕ} {V W : Submodule ℂ B}
    (hV : V ≤ h.isFermionSector.derivSubmodule n)
    (hW : W ≤ h.isFermionSector.derivSubmodule m) : V * W = W * V := by
  refine le_antisymm ?_ ?_ <;> rw [Submodule.mul_le] <;> intro x hx y hy
  · rw [h.isFermionSector.anticomm_of_mem_derivSubmodule (hV hx) (hW hy)]
    exact Submodule.neg_mem _ (Submodule.mul_mem_mul hy hx)
  · rw [h.isFermionSector.anticomm_of_mem_derivSubmodule (hW hx) (hV hy)]
    exact Submodule.neg_mem _ (Submodule.mul_mem_mul hy hx)

/-- Swapping the two fermion factors of a block leaves every weight piece unchanged: the
  two fermion factors commute as submodules, so the two orderings of the block are the same
  submodule. This is what makes the six transposed blocks of the mass-weight-eight
  decomposition a rewrite rather than six fresh classifications. -/
lemma mul_mul_piece_swap {VH VX VY : Submodule ℂ B} {n m : ℕ}
    (dH : GaugeWeightDecomposition repGauge VH)
    (dX : GaugeWeightDecomposition repGauge VX)
    (dY : GaugeWeightDecomposition repGauge VY)
    (hX : VX ≤ h.isFermionSector.derivSubmodule n)
    (hY : VY ≤ h.isFermionSector.derivSubmodule m) (w : GaugeWeight) :
    (GaugeWeightDecomposition.mul (d := dH)
        (d' := GaugeWeightDecomposition.mul (d := dX) (d' := dY))).piece w
      = (GaugeWeightDecomposition.mul (d := dH)
        (d' := GaugeWeightDecomposition.mul (d := dY) (d' := dX))).piece w :=
  GaugeWeightDecomposition.piece_congr
    (d := GaugeWeightDecomposition.mul (d := dH)
      (d' := GaugeWeightDecomposition.mul (d := dX) (d' := dY)))
    (d' := GaugeWeightDecomposition.mul (d := dH)
      (d' := GaugeWeightDecomposition.mul (d := dY) (d' := dX)))
    (by rw [h.mul_comm_of_le_derivSubmodule hX hY]) w

/-- Swapping the two fermion factors of a block negates it. -/
lemma mul_mul_swap_eq_neg {n m : ℕ} (a : B) {x y : B}
    (hx : x ∈ h.isFermionSector.derivSubmodule n)
    (hy : y ∈ h.isFermionSector.derivSubmodule m) :
    a * (y * x) = -(a * (x * y)) := by
  rw [h.isFermionSector.anticomm_of_mem_derivSubmodule hy hx, mul_neg]

end IsCovStandardModel

end StandardModel
