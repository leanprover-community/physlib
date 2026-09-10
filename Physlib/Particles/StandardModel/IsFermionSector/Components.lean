/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsFermionSector.Basic
/-!
# The components of the fermion symbols

## i. Overview

A fermion sector gives the ten species as linear maps out of the dual of a value space.
Fixing a basis of that value space turns each map into a finite family of elements of `B`:
the components. This file records those components and the transformation laws they carry.

Both laws are dictated by the variance. A symbol eats a covector, so it carries the
contragredient of its value space: its gauge charges are the negatives of the value
space's, entering through the matrix entries of the inverse group element, transposed. The
barred species carry the conjugate on top of that, which stars every coefficient. On the
Lorentz side a right-handed value space contributes the entrywise conjugate of the inverse
matrix and a left-handed one the inverse matrix itself, with the conjugates swapping the
two.

## ii. Key results

- `dComponent` ... `bareComponent` : the components of the ten fermion symbols.
- `rep_dComponent` ... `rep_bareComponent` : the gauge transformation of a component,
  expanded over components.
- `repLorentz_dComponent` ... `repLorentz_bareComponent` : the Lorentz transformation of a
  component carrying no derivatives, expanded over components.
- `repGauge_gaugeTorusGen_dComponent` ... `repGauge_gaugeTorusGen_bareComponent` : the
  specialisation of the gauge law to the four torus generators, reproducing the weights
  already recorded for the fermion derivative submodules.

## iii. Table of contents

- A. The components of the ten fermion symbols
- B. The gauge transformation of a component
- C. The Lorentz transformation of a component
- D. The torus specialisation and the recorded gauge weights
  - D.1. The inverses of the torus generators
  - D.2. The weights of the ten components

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

namespace IsFermionSector

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
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
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsFermionSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
      d bard u baru Q barQ L barL e bare massWeightPoly)

/-!

## A. The components of the ten fermion symbols

Each species is evaluated on the dual basis of its value space. The generation index and
the derivative slots ride along untouched; the new index is the basis index of the value
space, which for the barred species is that of the conjugate basis.

-/

set_option linter.unusedVariables false in
/-- The component `∇_l d_i` of the down-singlet symbol against the basis vector `j` of
  `DownSinglet`. -/
noncomputable def dComponent (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly)
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) : B :=
  d i l (DownSinglet.basis.dualBasis j)

set_option linter.unusedVariables false in
/-- The component `∇_l bard_i` of the conjugate down-singlet symbol against the basis
  vector `j` of `ConjModule DownSinglet`. -/
noncomputable def bardComponent (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly)
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) : B :=
  bard i l (DownSinglet.basis.conj.dualBasis j)

set_option linter.unusedVariables false in
/-- The component `∇_l u_i` of the up-singlet symbol against the basis vector `j` of
  `UpSinglet`. -/
noncomputable def uComponent (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly)
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) : B :=
  u i l (UpSinglet.basis.dualBasis j)

set_option linter.unusedVariables false in
/-- The component `∇_l baru_i` of the conjugate up-singlet symbol against the basis vector
  `j` of `ConjModule UpSinglet`. -/
noncomputable def baruComponent (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly)
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) : B :=
  baru i l (UpSinglet.basis.conj.dualBasis j)

set_option linter.unusedVariables false in
/-- The component `∇_l Q_i` of the quark-doublet symbol against the basis vector `j` of
  `QuarkDoublet`. -/
noncomputable def QComponent (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly)
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3 × Fin 2) : B :=
  Q i l (QuarkDoublet.basis.dualBasis j)

set_option linter.unusedVariables false in
/-- The component `∇_l barQ_i` of the conjugate quark-doublet symbol against the basis
  vector `j` of `ConjModule QuarkDoublet`. -/
noncomputable def barQComponent (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly)
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3 × Fin 2) : B :=
  barQ i l (QuarkDoublet.basis.conj.dualBasis j)

set_option linter.unusedVariables false in
/-- The component `∇_l L_i` of the lepton-doublet symbol against the basis vector `j` of
  `LeptonDoublet`. -/
noncomputable def LComponent (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly)
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) : B :=
  L i l (LeptonDoublet.basis.dualBasis j)

set_option linter.unusedVariables false in
/-- The component `∇_l barL_i` of the conjugate lepton-doublet symbol against the basis
  vector `j` of `ConjModule LeptonDoublet`. -/
noncomputable def barLComponent (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly)
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) : B :=
  barL i l (LeptonDoublet.basis.conj.dualBasis j)

set_option linter.unusedVariables false in
/-- The component `∇_l e_i` of the lepton-singlet symbol against the basis vector `j` of
  `LeptonSinglet`. -/
noncomputable def eComponent (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly)
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2) : B :=
  e i l (LeptonSinglet.basis.dualBasis j)

set_option linter.unusedVariables false in
/-- The component `∇_l bare_i` of the conjugate lepton-singlet symbol against the basis
  vector `j` of `ConjModule LeptonSinglet`. -/
noncomputable def bareComponent (h : IsFermionSector B repGauge hrepGauge_mul repLorentz
      hrepLorentz_mul d bard u baru Q barQ L barL e bare massWeightPoly)
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2) : B :=
  bare i l (LeptonSinglet.basis.conj.dualBasis j)

/-!

## B. The gauge transformation of a component

A symbol eats a covector, so it carries the contragredient of its value space: the gauge
charges are the negatives of the value space's, and the coefficients are the matrix entries
of the inverse group element with its indices transposed. The barred species carry the
conjugate on top of that, which stars every coefficient. Colour mixes only the colour
index, weak isospin only the isospin index, and hypercharge is an overall scalar.

-/

/-- The gauge transformation of a down-singlet component: the colour index mixes by the
  transposed `SU(3)` matrix of `g⁻¹`, scaled by the conjugate hypercharge factor. -/
lemma rep_dComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge g (h.dComponent i l j) =
      ∑ c, (star (g⁻¹).toU1.1 ^ 2 * (g⁻¹).toSU3.1 j.2 c) • h.dComponent i l (j.1, c) := by
  rw [dComponent, h.repGauge_d, DownSinglet.repGaugeGroupI_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [map_smul]; rfl

/-- The gauge transformation of a conjugate down-singlet component: the coefficients of
  the down-singlet law, conjugated. -/
lemma rep_bardComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge g (h.bardComponent i l j) =
      ∑ c, star (star (g⁻¹).toU1.1 ^ 2 * (g⁻¹).toSU3.1 j.2 c) •
        h.bardComponent i l (j.1, c) := by
  rw [bardComponent, h.repGauge_bard, DownSinglet.repGaugeGroupI_conj_dual_dualBasis,
    map_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [map_smul]; rfl

/-- The gauge transformation of an up-singlet component: the colour index mixes by the
  transposed `SU(3)` matrix of `g⁻¹`, scaled by the hypercharge factor. -/
lemma rep_uComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge g (h.uComponent i l j) =
      ∑ c, ((g⁻¹).toU1.1 ^ 4 * (g⁻¹).toSU3.1 j.2 c) • h.uComponent i l (j.1, c) := by
  rw [uComponent, h.repGauge_u, UpSinglet.repGaugeGroupI_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [map_smul]; rfl

/-- The gauge transformation of a conjugate up-singlet component: the coefficients of the
  up-singlet law, conjugated. -/
lemma rep_baruComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge g (h.baruComponent i l j) =
      ∑ c, star ((g⁻¹).toU1.1 ^ 4 * (g⁻¹).toSU3.1 j.2 c) •
        h.baruComponent i l (j.1, c) := by
  rw [baruComponent, h.repGauge_baru, UpSinglet.repGaugeGroupI_conj_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [map_smul]; rfl

/-- The gauge transformation of a quark-doublet component: the colour index mixes by the
  transposed `SU(3)` matrix of `g⁻¹` and the isospin index by the transposed `SU(2)`
  matrix, scaled by the hypercharge factor. -/
lemma rep_QComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3 × Fin 2) :
    repGauge g (h.QComponent i l j) =
      ∑ c, ∑ w, ((g⁻¹).toU1.1 * (g⁻¹).toSU3.1 j.2.1 c * (g⁻¹).toSU2.1 j.2.2 w) •
        h.QComponent i l (j.1, c, w) := by
  rw [QComponent, h.repGauge_Q, QuarkDoublet.repGaugeGroupI_dual_dualBasis, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun w _ => by rw [map_smul]; rfl

/-- The gauge transformation of a conjugate quark-doublet component: the coefficients of
  the quark-doublet law, conjugated. -/
lemma rep_barQComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3 × Fin 2) :
    repGauge g (h.barQComponent i l j) =
      ∑ c, ∑ w, star ((g⁻¹).toU1.1 * (g⁻¹).toSU3.1 j.2.1 c * (g⁻¹).toSU2.1 j.2.2 w) •
        h.barQComponent i l (j.1, c, w) := by
  rw [barQComponent, h.repGauge_barQ, QuarkDoublet.repGaugeGroupI_conj_dual_dualBasis,
    map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun w _ => by rw [map_smul]; rfl

/-- The gauge transformation of a lepton-doublet component: the isospin index mixes by the
  transposed `SU(2)` matrix of `g⁻¹`, scaled by the conjugate hypercharge factor. -/
lemma rep_LComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge g (h.LComponent i l j) =
      ∑ w, (star (g⁻¹).toU1.1 ^ 3 * (g⁻¹).toSU2.1 j.2 w) • h.LComponent i l (j.1, w) := by
  rw [LComponent, h.repGauge_L, LeptonDoublet.repGaugeGroupI_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun w _ => by rw [map_smul]; rfl

/-- The gauge transformation of a conjugate lepton-doublet component: the coefficients of
  the lepton-doublet law, conjugated. -/
lemma rep_barLComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge g (h.barLComponent i l j) =
      ∑ w, star (star (g⁻¹).toU1.1 ^ 3 * (g⁻¹).toSU2.1 j.2 w) •
        h.barLComponent i l (j.1, w) := by
  rw [barLComponent, h.repGauge_barL, LeptonDoublet.repGaugeGroupI_conj_dual_dualBasis,
    map_sum]
  exact Finset.sum_congr rfl fun w _ => by rw [map_smul]; rfl

/-- The gauge transformation of a lepton-singlet component: colour and isospin act
  trivially, so the sum over components collapses to the conjugate hypercharge scalar. -/
lemma rep_eComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2) :
    repGauge g (h.eComponent i l j) =
      (star (g⁻¹).toU1.1 ^ 6 : ℂ) • h.eComponent i l j := by
  rw [eComponent, h.repGauge_e, LeptonSinglet.repGaugeGroupI_dual_dualBasis, map_smul]

/-- The gauge transformation of a conjugate lepton-singlet component: the scalar of the
  lepton-singlet law, conjugated. -/
lemma rep_bareComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2) :
    repGauge g (h.bareComponent i l j) =
      star (star (g⁻¹).toU1.1 ^ 6 : ℂ) • h.bareComponent i l j := by
  rw [bareComponent, h.repGauge_bare, LeptonSinglet.repGaugeGroupI_conj_dual_dualBasis,
    map_smul]

/-!

## C. The Lorentz transformation of a component

A tower with `n` covariant derivatives mixes into every assignment of `n` derivative
directions, so its Lorentz law is a sum over such assignments. At `n = 0` there is exactly
one assignment and the product of Lorentz factors is empty, leaving only the action on the
value index. That is the case recorded here: a right-handed value space contributes the
entrywise conjugate of the inverse matrix and a left-handed one the inverse matrix itself,
with the conjugate species swapping the two.

-/

/-- At zero covariant derivatives the assignments of derivative directions form a
  one-element type, so the Lorentz law of a tower has a single term. -/
lemma univ_derivIndex_zero (l : Fin 0 → Fin 1 ⊕ Fin 3) :
    (Finset.univ : Finset (Fin 0 → Fin 1 ⊕ Fin 3)) = {l} :=
  Finset.eq_singleton_iff_unique_mem.mpr
    ⟨Finset.mem_univ l, fun x _ => Subsingleton.elim x l⟩

/-- The Lorentz transformation of a down-singlet component carrying no derivatives: the
  right-handed spinor index transforms by the entrywise conjugate of the inverse matrix. -/
lemma repLorentz_dComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repLorentz Λ (h.dComponent i l j) =
      ∑ β, star ((Λ⁻¹).1 j.1 β) • h.dComponent i l (β, j.2) := by
  rw [dComponent, h.repLorentz_d i Λ 0 l (DownSinglet.basis.dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [DownSinglet.repLorentzGroup_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-- The Lorentz transformation of a conjugate down-singlet component carrying no
  derivatives: the coefficients of the down-singlet law, conjugated. -/
lemma repLorentz_bardComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repLorentz Λ (h.bardComponent i l j) =
      ∑ β, (Λ⁻¹).1 j.1 β • h.bardComponent i l (β, j.2) := by
  rw [bardComponent, h.repLorentz_bard i Λ 0 l (DownSinglet.basis.conj.dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [DownSinglet.repLorentzGroup_conj_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-- The Lorentz transformation of an up-singlet component carrying no derivatives: the
  right-handed spinor index transforms by the entrywise conjugate of the inverse matrix. -/
lemma repLorentz_uComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repLorentz Λ (h.uComponent i l j) =
      ∑ β, star ((Λ⁻¹).1 j.1 β) • h.uComponent i l (β, j.2) := by
  rw [uComponent, h.repLorentz_u i Λ 0 l (UpSinglet.basis.dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [UpSinglet.repLorentzGroup_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-- The Lorentz transformation of a conjugate up-singlet component carrying no
  derivatives: the coefficients of the up-singlet law, conjugated. -/
lemma repLorentz_baruComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repLorentz Λ (h.baruComponent i l j) =
      ∑ β, (Λ⁻¹).1 j.1 β • h.baruComponent i l (β, j.2) := by
  rw [baruComponent, h.repLorentz_baru i Λ 0 l (UpSinglet.basis.conj.dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [UpSinglet.repLorentzGroup_conj_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-- The Lorentz transformation of a quark-doublet component carrying no derivatives: the
  left-handed spinor index transforms by the inverse matrix. -/
lemma repLorentz_QComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3 × Fin 2) :
    repLorentz Λ (h.QComponent i l j) =
      ∑ β, (Λ⁻¹).1 j.1 β • h.QComponent i l (β, j.2.1, j.2.2) := by
  rw [QComponent, h.repLorentz_Q i Λ 0 l (QuarkDoublet.basis.dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [QuarkDoublet.repLorentzGroup_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-- The Lorentz transformation of a conjugate quark-doublet component carrying no
  derivatives: the coefficients of the quark-doublet law, conjugated. -/
lemma repLorentz_barQComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3 × Fin 2) :
    repLorentz Λ (h.barQComponent i l j) =
      ∑ β, star ((Λ⁻¹).1 j.1 β) • h.barQComponent i l (β, j.2.1, j.2.2) := by
  rw [barQComponent, h.repLorentz_barQ i Λ 0 l (QuarkDoublet.basis.conj.dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [QuarkDoublet.repLorentzGroup_conj_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-- The Lorentz transformation of a lepton-doublet component carrying no derivatives: the
  left-handed spinor index transforms by the inverse matrix. -/
lemma repLorentz_LComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 2) :
    repLorentz Λ (h.LComponent i l j) =
      ∑ β, (Λ⁻¹).1 j.1 β • h.LComponent i l (β, j.2) := by
  rw [LComponent, h.repLorentz_L i Λ 0 l (LeptonDoublet.basis.dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [LeptonDoublet.repLorentzGroup_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-- The Lorentz transformation of a conjugate lepton-doublet component carrying no
  derivatives: the coefficients of the lepton-doublet law, conjugated. -/
lemma repLorentz_barLComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 2) :
    repLorentz Λ (h.barLComponent i l j) =
      ∑ β, star ((Λ⁻¹).1 j.1 β) • h.barLComponent i l (β, j.2) := by
  rw [barLComponent, h.repLorentz_barL i Λ 0 l (LeptonDoublet.basis.conj.dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [LeptonDoublet.repLorentzGroup_conj_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-- The Lorentz transformation of a lepton-singlet component carrying no derivatives: the
  right-handed spinor index transforms by the entrywise conjugate of the inverse matrix. -/
lemma repLorentz_eComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2) :
    repLorentz Λ (h.eComponent i l j) =
      ∑ β, star ((Λ⁻¹).1 j β) • h.eComponent i l β := by
  rw [eComponent, h.repLorentz_e i Λ 0 l (LeptonSinglet.basis.dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [LeptonSinglet.repLorentzGroup_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-- The Lorentz transformation of a conjugate lepton-singlet component carrying no
  derivatives: the coefficients of the lepton-singlet law, conjugated. -/
lemma repLorentz_bareComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2) :
    repLorentz Λ (h.bareComponent i l j) =
      ∑ β, (Λ⁻¹).1 j β • h.bareComponent i l β := by
  rw [bareComponent, h.repLorentz_bare i Λ 0 l (LeptonSinglet.basis.conj.dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [LeptonSinglet.repLorentzGroup_conj_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-!

## D. The torus specialisation and the recorded gauge weights

Restricting the gauge law of section B to the four torus generators must return the gauge
weights already recorded for the fermion derivative submodules: the negative of the value
space's weight for an unbarred species, and the value space's own weight for a barred one.
The lemmas below derive exactly those weights from the full-group laws, so the variance of
section B and the weight bookkeeping of the derivative submodules agree.

-/

/-!

### D.1. The inverses of the torus generators

-/

/-- The inverse of the unitary `exp i` is its conjugate. -/
lemma _root_.StandardModel.expI_inv_coe : ((expI⁻¹ : unitary ℂ) : ℂ) = star (expI : ℂ) := rfl

/-- The inverse of the first colour torus generator, `diag (exp (-i), exp i, 1)`. -/
lemma _root_.StandardModel.su3ExpIOne_inv_coe :
    (su3ExpIOne⁻¹ : specialUnitaryGroup (Fin 3) ℂ).1
      = Matrix.diagonal ![star (expI : ℂ), (expI : ℂ), 1] := by
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [su3ExpIOne, Matrix.diagonal]

/-- The inverse of the second colour torus generator, `diag (1, exp (-i), exp i)`. -/
lemma _root_.StandardModel.su3ExpITwo_inv_coe :
    (su3ExpITwo⁻¹ : specialUnitaryGroup (Fin 3) ℂ).1
      = Matrix.diagonal ![1, star (expI : ℂ), (expI : ℂ)] := by
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [su3ExpITwo, Matrix.diagonal]

/-!

### D.2. The weights of the ten components

-/

/-- The `d` components carry the negative of the down-singlet weight. -/
lemma repGauge_gaugeTorusGen_dComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen t) (h.dComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (-(DownSinglet.valueGaugeWeight j)) t) •
        h.dComponent i l j := by
  rw [h.rep_dComponent]
  obtain ⟨k, c⟩ := j
  fin_cases t <;> fin_cases c <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, su3ExpIOne_inv_coe,
      su3ExpITwo_inv_coe, Fin.sum_univ_three, Matrix.diagonal,
      DownSinglet.valueGaugeWeight, colourWeight, GaugeWeight.coord,
      expI_inv_eq_star, expI_inv_coe] <;>
  (try congr 1)

/-- The `bard` components carry the down-singlet weight itself. -/
lemma repGauge_gaugeTorusGen_bardComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen t) (h.bardComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (DownSinglet.valueGaugeWeight j) t) •
        h.bardComponent i l j := by
  rw [h.rep_bardComponent]
  obtain ⟨k, c⟩ := j
  fin_cases t <;> fin_cases c <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, su3ExpIOne_inv_coe,
      su3ExpITwo_inv_coe, Fin.sum_univ_three, Matrix.diagonal,
      DownSinglet.valueGaugeWeight, colourWeight, GaugeWeight.coord,
      expI_inv_eq_star, expI_inv_coe, starRingEnd_expI_pow] <;>
  (try congr 1)

/-- The `u` components carry the negative of the up-singlet weight. -/
lemma repGauge_gaugeTorusGen_uComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen t) (h.uComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (-(UpSinglet.valueGaugeWeight j)) t) •
        h.uComponent i l j := by
  rw [h.rep_uComponent]
  obtain ⟨k, c⟩ := j
  fin_cases t <;> fin_cases c <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, su3ExpIOne_inv_coe,
      su3ExpITwo_inv_coe, Fin.sum_univ_three, Matrix.diagonal,
      UpSinglet.valueGaugeWeight, colourWeight, GaugeWeight.coord,
      expI_inv_eq_star, expI_inv_coe, starRingEnd_expI_pow] <;>
  (try congr 1)

/-- The `baru` components carry the up-singlet weight itself. -/
lemma repGauge_gaugeTorusGen_baruComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen t) (h.baruComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (UpSinglet.valueGaugeWeight j) t) •
        h.baruComponent i l j := by
  rw [h.rep_baruComponent]
  obtain ⟨k, c⟩ := j
  fin_cases t <;> fin_cases c <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, su3ExpIOne_inv_coe,
      su3ExpITwo_inv_coe, Fin.sum_univ_three, Matrix.diagonal,
      UpSinglet.valueGaugeWeight, colourWeight, GaugeWeight.coord,
      expI_inv_eq_star, expI_inv_coe, starRingEnd_expI_pow] <;>
  (try congr 1)

/-- The `Q` components carry the negative of the quark-doublet weight. -/
lemma repGauge_gaugeTorusGen_QComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3 × Fin 2) :
    repGauge (gaugeTorusGen t) (h.QComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (-(QuarkDoublet.valueGaugeWeight j)) t) •
        h.QComponent i l j := by
  rw [h.rep_QComponent]
  obtain ⟨k, c, w⟩ := j
  fin_cases t <;> fin_cases c <;> fin_cases w <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, GaugeGroupI.toSU2,
      su3ExpIOne_inv_coe, su3ExpITwo_inv_coe, su2ExpI_inv_coe, Fin.sum_univ_three,
      Fin.sum_univ_two, Matrix.diagonal, QuarkDoublet.valueGaugeWeight, colourWeight,
      isoWeight, GaugeWeight.coord, expI_inv_eq_star, expI_inv_coe]

/-- The `barQ` components carry the quark-doublet weight itself. -/
lemma repGauge_gaugeTorusGen_barQComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3 × Fin 2) :
    repGauge (gaugeTorusGen t) (h.barQComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (QuarkDoublet.valueGaugeWeight j) t) •
        h.barQComponent i l j := by
  rw [h.rep_barQComponent]
  obtain ⟨k, c, w⟩ := j
  fin_cases t <;> fin_cases c <;> fin_cases w <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, GaugeGroupI.toSU2,
      su3ExpIOne_inv_coe, su3ExpITwo_inv_coe, su2ExpI_inv_coe, Fin.sum_univ_three,
      Fin.sum_univ_two, Matrix.diagonal, QuarkDoublet.valueGaugeWeight, colourWeight,
      isoWeight, GaugeWeight.coord, expI_inv_eq_star, expI_inv_coe]

/-- The `L` components carry the negative of the lepton-doublet weight. -/
lemma repGauge_gaugeTorusGen_LComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge (gaugeTorusGen t) (h.LComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (-(LeptonDoublet.valueGaugeWeight j)) t) •
        h.LComponent i l j := by
  rw [h.rep_LComponent]
  obtain ⟨k, w⟩ := j
  fin_cases t <;> fin_cases w <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU2, su2ExpI_inv_coe,
      Fin.sum_univ_two, LeptonDoublet.valueGaugeWeight, isoWeight,
      GaugeWeight.coord, expI_inv_eq_star, expI_inv_coe] <;>
  (try congr 1)

/-- The `barL` components carry the lepton-doublet weight itself. -/
lemma repGauge_gaugeTorusGen_barLComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge (gaugeTorusGen t) (h.barLComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonDoublet.valueGaugeWeight j) t) •
        h.barLComponent i l j := by
  rw [h.rep_barLComponent]
  obtain ⟨k, w⟩ := j
  fin_cases t <;> fin_cases w <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU2, su2ExpI_inv_coe,
      Fin.sum_univ_two, LeptonDoublet.valueGaugeWeight, isoWeight,
      GaugeWeight.coord, expI_inv_eq_star, expI_inv_coe,
      starRingEnd_expI_pow] <;>
  (try congr 1)

/-- The `e` components carry the negative of the lepton-singlet weight. -/
lemma repGauge_gaugeTorusGen_eComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2) :
    repGauge (gaugeTorusGen t) (h.eComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (-(LeptonSinglet.valueGaugeWeight j)) t) •
        h.eComponent i l j := by
  rw [h.rep_eComponent]
  fin_cases t <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, LeptonSinglet.valueGaugeWeight,
      GaugeWeight.coord, expI_inv_coe]
  (try congr 1)

/-- The `bare` components carry the lepton-singlet weight itself. -/
lemma repGauge_gaugeTorusGen_bareComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2) :
    repGauge (gaugeTorusGen t) (h.bareComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonSinglet.valueGaugeWeight j) t) •
        h.bareComponent i l j := by
  rw [h.rep_bareComponent]
  fin_cases t <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, LeptonSinglet.valueGaugeWeight,
      GaugeWeight.coord, expI_inv_coe, starRingEnd_expI_pow]
  (try congr 1)

end IsFermionSector

end StandardModel
