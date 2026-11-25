/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.FermionSector.Basic
/-!
# The components of the fermion symbols

The components of the ten fermion symbols on a basis of their value spaces, and their gauge and
Lorentz transformation laws.

## i. Overview

The fermion sector of the covariant field algebra gives the ten species as linear maps out of
the dual of a value space. Fixing a basis of that value space turns each map into a finite
family of elements of the covariant field algebra, the components. This file records those
components and the transformation laws they carry.

Both laws are dictated by the variance. A symbol eats a covector, so it carries the
contragredient of its value space. Its gauge charges are the negatives of the value
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
- `repGauge_su3_d`, `repGauge_su2_d`, `repGauge_u1_d` and their companions for the other nine
  species : the gauge law of each component read at the colour, isospin and hypercharge
  factors.

## iii. Table of contents

- A. The components of the ten fermion symbols
- B. The gauge transformation of a component
- C. The Lorentz transformation of a component
- D. The torus specialisation and the recorded gauge weights
- E. The gauge laws of the components at each factor
  - E.1. The down singlet
  - E.2. The conjugate down singlet
  - E.3. The up singlet
  - E.4. The conjugate up singlet
  - E.5. The quark doublet
  - E.6. The conjugate quark doublet
  - E.7. The lepton doublet
  - E.8. The conjugate lepton doublet
  - E.9. The lepton singlet
  - E.10. The conjugate lepton singlet

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

namespace FermionSector

/-!

## A. The components of the ten fermion symbols

Each species is evaluated on the dual basis of its value space. The generation index and
the derivative slots ride along untouched; the new index is the basis index of the value
space, which for the barred species is that of the conjugate basis.

-/

/-- The component `∇_l d_i` of the down-singlet symbol against the basis vector `j` of
  `DownSinglet`. -/
noncomputable def dComponent
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) : fieldData.LocalCovFieldAlgebra :=
  d i l (DownSinglet.basis.dualBasis j)

/-- The component `∇_l bard_i` of the conjugate down-singlet symbol against the basis
  vector `j` of `ConjModule DownSinglet`. -/
noncomputable def bardComponent
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) : fieldData.LocalCovFieldAlgebra :=
  bard i l ((Basis.conj DownSinglet.basis).dualBasis j)

/-- The component `∇_l u_i` of the up-singlet symbol against the basis vector `j` of
  `UpSinglet`. -/
noncomputable def uComponent
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) : fieldData.LocalCovFieldAlgebra :=
  u i l (UpSinglet.basis.dualBasis j)

/-- The component `∇_l baru_i` of the conjugate up-singlet symbol against the basis vector
  `j` of `ConjModule UpSinglet`. -/
noncomputable def baruComponent
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) : fieldData.LocalCovFieldAlgebra :=
  baru i l ((Basis.conj UpSinglet.basis).dualBasis j)

/-- The component `∇_l Q_i` of the quark-doublet symbol against the basis vector `j` of
  `QuarkDoublet`. -/
noncomputable def QComponent
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3 × Fin 2) : fieldData.LocalCovFieldAlgebra :=
  Q i l (QuarkDoublet.basis.dualBasis j)

/-- The component `∇_l barQ_i` of the conjugate quark-doublet symbol against the basis
  vector `j` of `ConjModule QuarkDoublet`. -/
noncomputable def barQComponent
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3 × Fin 2) : fieldData.LocalCovFieldAlgebra :=
  barQ i l ((Basis.conj QuarkDoublet.basis).dualBasis j)

/-- The component `∇_l L_i` of the lepton-doublet symbol against the basis vector `j` of
  `LeptonDoubletV`. -/
noncomputable def LComponent
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 2) : fieldData.LocalCovFieldAlgebra :=
  L i l (LeptonDoubletV.basis.dualBasis j)

/-- The component `∇_l barL_i` of the conjugate lepton-doublet symbol against the basis
  vector `j` of `ConjModule LeptonDoubletV`. -/
noncomputable def barLComponent
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 2) : fieldData.LocalCovFieldAlgebra :=
  barL i l ((Basis.conj LeptonDoubletV.basis).dualBasis j)

/-- The component `∇_l e_i` of the lepton-singlet symbol against the basis vector `j` of
  `LeptonSinglet`. -/
noncomputable def eComponent
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2) : fieldData.LocalCovFieldAlgebra :=
  e i l (LeptonSinglet.basis.dualBasis j)

/-- The component `∇_l bare_i` of the conjugate lepton-singlet symbol against the basis
  vector `j` of `ConjModule LeptonSinglet`. -/
noncomputable def bareComponent
    (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2) : fieldData.LocalCovFieldAlgebra :=
  bare i l ((Basis.conj LeptonSinglet.basis).dualBasis j)

/-!

## B. The gauge transformation of a component

A symbol eats a covector, so it carries the contragredient of its value space. The gauge
charges are the negatives of the value space's, and the coefficients are the matrix entries
of the inverse group element with its indices transposed. The barred species carry the
conjugate on top of that, which stars every coefficient. Colour mixes only the colour
index, weak isospin only the isospin index, and hypercharge is an overall scalar.

-/

/-- The gauge transformation of a down-singlet component. The colour index mixes by the
  transposed `SU(3)` matrix of `g⁻¹`, scaled by the conjugate hypercharge factor. -/
lemma rep_dComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge g (dComponent i l j) =
      ∑ c, (star (g⁻¹).toU1.1 ^ 2 * (g⁻¹).toSU3.1 j.2 c) • dComponent i l (j.1, c) := by
  rw [dComponent, repGauge_d, DownSinglet.repGaugeGroupI_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [map_smul]; rfl

/-- The gauge transformation of a conjugate down-singlet component has the coefficients of
  the down-singlet law, conjugated. -/
lemma rep_bardComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge g (bardComponent i l j) =
      ∑ c, star (star (g⁻¹).toU1.1 ^ 2 * (g⁻¹).toSU3.1 j.2 c) •
        bardComponent i l (j.1, c) := by
  rw [bardComponent, repGauge_bard, DownSinglet.repGaugeGroupI_conj_dual_dualBasis,
    map_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [map_smul]; rfl

/-- The gauge transformation of an up-singlet component. The colour index mixes by the
  transposed `SU(3)` matrix of `g⁻¹`, scaled by the hypercharge factor. -/
lemma rep_uComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge g (uComponent i l j) =
      ∑ c, ((g⁻¹).toU1.1 ^ 4 * (g⁻¹).toSU3.1 j.2 c) • uComponent i l (j.1, c) := by
  rw [uComponent, repGauge_u, UpSinglet.repGaugeGroupI_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [map_smul]; rfl

/-- The gauge transformation of a conjugate up-singlet component has the coefficients of the
  up-singlet law, conjugated. -/
lemma rep_baruComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge g (baruComponent i l j) =
      ∑ c, star ((g⁻¹).toU1.1 ^ 4 * (g⁻¹).toSU3.1 j.2 c) •
        baruComponent i l (j.1, c) := by
  rw [baruComponent, repGauge_baru, UpSinglet.repGaugeGroupI_conj_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [map_smul]; rfl

/-- The gauge transformation of a quark-doublet component. The colour index mixes by the
  transposed `SU(3)` matrix of `g⁻¹` and the isospin index by the transposed `SU(2)`
  matrix, scaled by the hypercharge factor. -/
lemma rep_QComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3 × Fin 2) :
    repGauge g (QComponent i l j) =
      ∑ c, ∑ w, ((g⁻¹).toU1.1 * (g⁻¹).toSU3.1 j.2.1 c * (g⁻¹).toSU2.1 j.2.2 w) •
        QComponent i l (j.1, c, w) := by
  rw [QComponent, repGauge_Q, QuarkDoublet.repGaugeGroupI_dual_dualBasis, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun w _ => by rw [map_smul]; rfl

/-- The gauge transformation of a conjugate quark-doublet component has the coefficients of
  the quark-doublet law, conjugated. -/
lemma rep_barQComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3 × Fin 2) :
    repGauge g (barQComponent i l j) =
      ∑ c, ∑ w, star ((g⁻¹).toU1.1 * (g⁻¹).toSU3.1 j.2.1 c * (g⁻¹).toSU2.1 j.2.2 w) •
        barQComponent i l (j.1, c, w) := by
  rw [barQComponent, repGauge_barQ, QuarkDoublet.repGaugeGroupI_conj_dual_dualBasis,
    map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun w _ => by rw [map_smul]; rfl

/-- The gauge transformation of a lepton-doublet component. The isospin index mixes by the
  transposed `SU(2)` matrix of `g⁻¹`, scaled by the conjugate hypercharge factor. -/
lemma rep_LComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge g (LComponent i l j) =
      ∑ w, (star (g⁻¹).toU1.1 ^ 3 * (g⁻¹).toSU2.1 j.2 w) • LComponent i l (j.1, w) := by
  rw [LComponent, repGauge_L, LeptonDoubletV.repGaugeGroupI_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun w _ => by rw [map_smul]; rfl

/-- The gauge transformation of a conjugate lepton-doublet component has the coefficients of
  the lepton-doublet law, conjugated. -/
lemma rep_barLComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge g (barLComponent i l j) =
      ∑ w, star (star (g⁻¹).toU1.1 ^ 3 * (g⁻¹).toSU2.1 j.2 w) •
        barLComponent i l (j.1, w) := by
  rw [barLComponent, repGauge_barL, LeptonDoubletV.repGaugeGroupI_conj_dual_dualBasis,
    map_sum]
  exact Finset.sum_congr rfl fun w _ => by rw [map_smul]; rfl

/-- The gauge transformation of a lepton-singlet component. Colour and isospin act
  trivially, so the sum over components collapses to the conjugate hypercharge scalar. -/
lemma rep_eComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2) :
    repGauge g (eComponent i l j) =
      (star (g⁻¹).toU1.1 ^ 6 : ℂ) • eComponent i l j := by
  rw [eComponent, repGauge_e, LeptonSinglet.repGaugeGroupI_dual_dualBasis, map_smul]

/-- The gauge transformation of a conjugate lepton-singlet component has the scalar of the
  lepton-singlet law, conjugated. -/
lemma rep_bareComponent (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2) :
    repGauge g (bareComponent i l j) =
      star (star (g⁻¹).toU1.1 ^ 6 : ℂ) • bareComponent i l j := by
  rw [bareComponent, repGauge_bare, LeptonSinglet.repGaugeGroupI_conj_dual_dualBasis,
    map_smul]

/-!

## C. The Lorentz transformation of a component

A tower with `n` covariant derivatives mixes into every assignment of `n` derivative
directions, so its Lorentz law is a sum over such assignments. At `n = 0` there is exactly
one assignment and the product of Lorentz factors is empty, leaving only the action on the
value index. That is the case recorded here. A right-handed value space contributes the
entrywise conjugate of the inverse matrix and a left-handed one the inverse matrix itself,
with the conjugate species swapping the two.

-/

/-- At zero covariant derivatives the assignments of derivative directions form a
  one-element type, so the Lorentz law of a tower has a single term. -/
lemma univ_derivIndex_zero (l : Fin 0 → Fin 1 ⊕ Fin 3) :
    (Finset.univ : Finset (Fin 0 → Fin 1 ⊕ Fin 3)) = {l} :=
  Finset.eq_singleton_iff_unique_mem.mpr
    ⟨Finset.mem_univ l, fun x _ => Subsingleton.elim x l⟩

/-- The Lorentz transformation of a down-singlet component carrying no derivatives. The
  right-handed spinor index transforms by the entrywise conjugate of the inverse matrix. -/
lemma repLorentz_dComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repLorentz Λ (dComponent i l j) =
      ∑ β, star ((Λ⁻¹).1 j.1 β) • dComponent i l (β, j.2) := by
  rw [dComponent, repLorentz_d i Λ 0 l (DownSinglet.basis.dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [DownSinglet.repLorentzGroup_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-- The Lorentz transformation of a conjugate down-singlet component carrying no
  derivatives has the coefficients of the down-singlet law, conjugated. -/
lemma repLorentz_bardComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repLorentz Λ (bardComponent i l j) =
      ∑ β, (Λ⁻¹).1 j.1 β • bardComponent i l (β, j.2) := by
  rw [bardComponent, repLorentz_bard i Λ 0 l ((Basis.conj DownSinglet.basis).dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [DownSinglet.repLorentzGroup_conj_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-- The Lorentz transformation of an up-singlet component carrying no derivatives. The
  right-handed spinor index transforms by the entrywise conjugate of the inverse matrix. -/
lemma repLorentz_uComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repLorentz Λ (uComponent i l j) =
      ∑ β, star ((Λ⁻¹).1 j.1 β) • uComponent i l (β, j.2) := by
  rw [uComponent, repLorentz_u i Λ 0 l (UpSinglet.basis.dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [UpSinglet.repLorentzGroup_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-- The Lorentz transformation of a conjugate up-singlet component carrying no
  derivatives has the coefficients of the up-singlet law, conjugated. -/
lemma repLorentz_baruComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repLorentz Λ (baruComponent i l j) =
      ∑ β, (Λ⁻¹).1 j.1 β • baruComponent i l (β, j.2) := by
  rw [baruComponent, repLorentz_baru i Λ 0 l ((Basis.conj UpSinglet.basis).dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [UpSinglet.repLorentzGroup_conj_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-- The Lorentz transformation of a quark-doublet component carrying no derivatives. The
  left-handed spinor index transforms by the inverse matrix. -/
lemma repLorentz_QComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3 × Fin 2) :
    repLorentz Λ (QComponent i l j) =
      ∑ β, (Λ⁻¹).1 j.1 β • QComponent i l (β, j.2.1, j.2.2) := by
  rw [QComponent, repLorentz_Q i Λ 0 l (QuarkDoublet.basis.dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [QuarkDoublet.repLorentzGroup_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-- The Lorentz transformation of a conjugate quark-doublet component carrying no
  derivatives has the coefficients of the quark-doublet law, conjugated. -/
lemma repLorentz_barQComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3 × Fin 2) :
    repLorentz Λ (barQComponent i l j) =
      ∑ β, star ((Λ⁻¹).1 j.1 β) • barQComponent i l (β, j.2.1, j.2.2) := by
  rw [barQComponent, repLorentz_barQ i Λ 0 l ((Basis.conj QuarkDoublet.basis).dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [QuarkDoublet.repLorentzGroup_conj_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-- The Lorentz transformation of a lepton-doublet component carrying no derivatives. The
  left-handed spinor index transforms by the inverse matrix. -/
lemma repLorentz_LComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 2) :
    repLorentz Λ (LComponent i l j) =
      ∑ β, (Λ⁻¹).1 j.1 β • LComponent i l (β, j.2) := by
  rw [LComponent, repLorentz_L i Λ 0 l (LeptonDoubletV.basis.dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [LeptonDoubletV.repLorentzGroup_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-- The Lorentz transformation of a conjugate lepton-doublet component carrying no
  derivatives has the coefficients of the lepton-doublet law, conjugated. -/
lemma repLorentz_barLComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 2) :
    repLorentz Λ (barLComponent i l j) =
      ∑ β, star ((Λ⁻¹).1 j.1 β) • barLComponent i l (β, j.2) := by
  rw [barLComponent, repLorentz_barL i Λ 0 l ((Basis.conj LeptonDoubletV.basis).dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [LeptonDoubletV.repLorentzGroup_conj_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-- The Lorentz transformation of a lepton-singlet component carrying no derivatives. The
  right-handed spinor index transforms by the entrywise conjugate of the inverse matrix. -/
lemma repLorentz_eComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2) :
    repLorentz Λ (eComponent i l j) =
      ∑ β, star ((Λ⁻¹).1 j β) • eComponent i l β := by
  rw [eComponent, repLorentz_e i Λ 0 l (LeptonSinglet.basis.dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [LeptonSinglet.repLorentzGroup_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-- The Lorentz transformation of a conjugate lepton-singlet component carrying no
  derivatives has the coefficients of the lepton-singlet law, conjugated. -/
lemma repLorentz_bareComponent (Λ : SL(2,ℂ)) (i : Fin 3) (l : Fin 0 → Fin 1 ⊕ Fin 3)
    (j : Fin 2) :
    repLorentz Λ (bareComponent i l j) =
      ∑ β, (Λ⁻¹).1 j β • bareComponent i l β := by
  rw [bareComponent, repLorentz_bare i Λ 0 l ((Basis.conj LeptonSinglet.basis).dualBasis j),
    univ_derivIndex_zero l, Finset.sum_singleton]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  rw [LeptonSinglet.repLorentzGroup_conj_dual_dualBasis, map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [map_smul]; rfl

/-!

## D. The torus specialisation and the recorded gauge weights

Restricting the gauge law of section B to the four torus generators must return the gauge
weights already recorded for the fermion derivative submodules, the negative of the value
space's weight for an unbarred species, and the value space's own weight for a barred one.
The lemmas below derive exactly those weights from the full-group laws, so the variance of
section B and the weight bookkeeping of the derivative submodules agree.

-/

/-- The `d` components carry the negative of the down-singlet weight. -/
lemma repGauge_gaugeTorusGen_dComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen t) (dComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (-(DownSinglet.valueGaugeWeight j)) t) •
        dComponent i l j := by
  rw [rep_dComponent]
  obtain ⟨k, c⟩ := j
  fin_cases t <;> fin_cases c <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, su3ExpIOne_inv_coe,
      su3ExpITwo_inv_coe, Fin.sum_univ_three, Matrix.diagonal,
      DownSinglet.valueGaugeWeight, colourWeight, GaugeWeight.coord,
      expI_inv_eq_star, expI_inv_coe]

/-- The `bard` components carry the down-singlet weight itself. -/
lemma repGauge_gaugeTorusGen_bardComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen t) (bardComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (DownSinglet.valueGaugeWeight j) t) •
        bardComponent i l j := by
  rw [rep_bardComponent]
  obtain ⟨k, c⟩ := j
  fin_cases t <;> fin_cases c <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, su3ExpIOne_inv_coe,
      su3ExpITwo_inv_coe, Fin.sum_univ_three, Matrix.diagonal,
      DownSinglet.valueGaugeWeight, colourWeight, GaugeWeight.coord,
      expI_inv_eq_star, expI_inv_coe, starRingEnd_expI_pow]

/-- The `u` components carry the negative of the up-singlet weight. -/
lemma repGauge_gaugeTorusGen_uComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen t) (uComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (-(UpSinglet.valueGaugeWeight j)) t) •
        uComponent i l j := by
  rw [rep_uComponent]
  obtain ⟨k, c⟩ := j
  fin_cases t <;> fin_cases c <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, su3ExpIOne_inv_coe,
      su3ExpITwo_inv_coe, Fin.sum_univ_three, Matrix.diagonal,
      UpSinglet.valueGaugeWeight, colourWeight, GaugeWeight.coord,
      expI_inv_eq_star, expI_inv_coe, starRingEnd_expI_pow]

/-- The `baru` components carry the up-singlet weight itself. -/
lemma repGauge_gaugeTorusGen_baruComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen t) (baruComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (UpSinglet.valueGaugeWeight j) t) •
        baruComponent i l j := by
  rw [rep_baruComponent]
  obtain ⟨k, c⟩ := j
  fin_cases t <;> fin_cases c <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, su3ExpIOne_inv_coe,
      su3ExpITwo_inv_coe, Fin.sum_univ_three, Matrix.diagonal,
      UpSinglet.valueGaugeWeight, colourWeight, GaugeWeight.coord,
      expI_inv_eq_star, expI_inv_coe, starRingEnd_expI_pow]

/-- The `Q` components carry the negative of the quark-doublet weight. -/
lemma repGauge_gaugeTorusGen_QComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3 × Fin 2) :
    repGauge (gaugeTorusGen t) (QComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (-(QuarkDoublet.valueGaugeWeight j)) t) •
        QComponent i l j := by
  rw [rep_QComponent]
  obtain ⟨k, c, w⟩ := j
  fin_cases t <;> fin_cases c <;> fin_cases w <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, GaugeGroupI.toSU2,
      su3ExpIOne_inv_coe, su3ExpITwo_inv_coe, su2ExpI_inv_coe, Fin.sum_univ_three,
      Fin.sum_univ_two, Matrix.diagonal, QuarkDoublet.valueGaugeWeight, colourWeight,
      isoWeight, GaugeWeight.coord, expI_inv_eq_star, expI_inv_coe]

/-- The `barQ` components carry the quark-doublet weight itself. -/
lemma repGauge_gaugeTorusGen_barQComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3 × Fin 2) :
    repGauge (gaugeTorusGen t) (barQComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (QuarkDoublet.valueGaugeWeight j) t) •
        barQComponent i l j := by
  rw [rep_barQComponent]
  obtain ⟨k, c, w⟩ := j
  fin_cases t <;> fin_cases c <;> fin_cases w <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, GaugeGroupI.toSU2,
      su3ExpIOne_inv_coe, su3ExpITwo_inv_coe, su2ExpI_inv_coe, Fin.sum_univ_three,
      Fin.sum_univ_two, Matrix.diagonal, QuarkDoublet.valueGaugeWeight, colourWeight,
      isoWeight, GaugeWeight.coord, expI_inv_eq_star, expI_inv_coe]

/-- The `L` components carry the negative of the lepton-doublet weight. -/
lemma repGauge_gaugeTorusGen_LComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge (gaugeTorusGen t) (LComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (-(LeptonDoubletV.valueGaugeWeight j)) t) •
        LComponent i l j := by
  rw [rep_LComponent]
  obtain ⟨k, w⟩ := j
  fin_cases t <;> fin_cases w <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU2, su2ExpI_inv_coe,
      Fin.sum_univ_two, LeptonDoubletV.valueGaugeWeight, isoWeight,
      GaugeWeight.coord, expI_inv_eq_star, expI_inv_coe]

/-- The `barL` components carry the lepton-doublet weight itself. -/
lemma repGauge_gaugeTorusGen_barLComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge (gaugeTorusGen t) (barLComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonDoubletV.valueGaugeWeight j) t) •
        barLComponent i l j := by
  rw [rep_barLComponent]
  obtain ⟨k, w⟩ := j
  fin_cases t <;> fin_cases w <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU2, su2ExpI_inv_coe,
      Fin.sum_univ_two, LeptonDoubletV.valueGaugeWeight, isoWeight,
      GaugeWeight.coord, expI_inv_eq_star, expI_inv_coe,
      starRingEnd_expI_pow]

/-- The `e` components carry the negative of the lepton-singlet weight. -/
lemma repGauge_gaugeTorusGen_eComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2) :
    repGauge (gaugeTorusGen t) (eComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (-(LeptonSinglet.valueGaugeWeight j)) t) •
        eComponent i l j := by
  rw [rep_eComponent]
  fin_cases t <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, LeptonSinglet.valueGaugeWeight,
      GaugeWeight.coord, expI_inv_coe]

/-- The `bare` components carry the lepton-singlet weight itself. -/
lemma repGauge_gaugeTorusGen_bareComponent (t : Fin 4) (i : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2) :
    repGauge (gaugeTorusGen t) (bareComponent i l j)
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonSinglet.valueGaugeWeight j) t) •
        bareComponent i l j := by
  rw [rep_bareComponent]
  fin_cases t <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, LeptonSinglet.valueGaugeWeight,
      GaugeWeight.coord, expI_inv_coe, starRingEnd_expI_pow]

open ComplexConjugate

/-!

## E. The gauge laws of the components at each factor

A gauge transformation is a triple, and each of the three index laws that classify a block
constrains one factor of it. So each of the ten symbols is read at each factor in turn:
colour moves only a colour index, isospin only an isospin index, and hypercharge is an
overall scalar whose power is the `6Y` of the species. A symbol eats a covector, so it
carries the contragredient of its value space. The unbarred species come out
anti-fundamental in colour and isospin and the barred ones fundamental, which is what makes
every conjugate pair a fundamental against an anti-fundamental.

-/

/-!

### E.1. The down singlet

-/

/-- A colour transformation moves the colour index of a down-singlet symbol by the
  conjugate matrix, the index being anti-fundamental. -/
lemma repGauge_su3_d (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) :
    repGauge ((U, 1, 1) : GaugeGroupI) (dComponent f l (s, c))
      = ∑ a, conj (U.1 a c) • dComponent f l (s, a) := by
  rw [rep_dComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su3Elt, toSU3_su3Elt, toU1_su3Elt, su3_inv_apply]
  simp

/-- An isospin transformation fixes a down-singlet symbol, which carries no isospin. -/
lemma repGauge_su2_d (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge ((1, V, 1) : GaugeGroupI) (dComponent f l j)
      = dComponent f l j := by
  rw [rep_dComponent]
  simp [Matrix.one_apply]

/-- A hypercharge transformation scales a down-singlet symbol by the square of the scalar,
  the down singlet carrying `6Y = 2`. -/
lemma repGauge_u1_d (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repGauge ((1, 1, t) : GaugeGroupI) (dComponent f l j)
      = (t : ℂ) ^ 2 • dComponent f l j := by
  rw [rep_dComponent]
  simp [Matrix.one_apply, unitary_inv_coe]

/-!

### E.2. The conjugate down singlet

-/

/-- A colour transformation moves the colour index of a conjugate down-singlet symbol by
  the matrix itself, the index being fundamental. -/
lemma repGauge_su3_bard (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) :
    repGauge ((U, 1, 1) : GaugeGroupI) (bardComponent f l (s, c))
      = ∑ a, U.1 a c • bardComponent f l (s, a) := by
  rw [rep_bardComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su3Elt, toSU3_su3Elt, toU1_su3Elt, su3_inv_apply]
  simp

/-- An isospin transformation fixes a conjugate down-singlet symbol. -/
lemma repGauge_su2_bard (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge ((1, V, 1) : GaugeGroupI) (bardComponent f l j)
      = bardComponent f l j := by
  rw [rep_bardComponent]
  simp [Matrix.one_apply]

/-- A hypercharge transformation scales a conjugate down-singlet symbol by the square of
  the conjugate scalar, the conjugate down singlet carrying `6Y = -2`. -/
lemma repGauge_u1_bard (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repGauge ((1, 1, t) : GaugeGroupI) (bardComponent f l j)
      = (star (t : ℂ)) ^ 2 • bardComponent f l j := by
  rw [rep_bardComponent]
  simp [Matrix.one_apply, unitary_inv_coe, apply_ite (starRingEnd ℂ)]

/-!

### E.3. The up singlet

-/

/-- A colour transformation moves the colour index of an up-singlet symbol by the
  conjugate matrix, the index being anti-fundamental. -/
lemma repGauge_su3_u (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) :
    repGauge ((U, 1, 1) : GaugeGroupI) (uComponent f l (s, c))
      = ∑ a, conj (U.1 a c) • uComponent f l (s, a) := by
  rw [rep_uComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su3Elt, toSU3_su3Elt, toU1_su3Elt, su3_inv_apply]
  simp

/-- An isospin transformation fixes an up-singlet symbol. -/
lemma repGauge_su2_u (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge ((1, V, 1) : GaugeGroupI) (uComponent f l j)
      = uComponent f l j := by
  rw [rep_uComponent]
  simp [Matrix.one_apply]

/-- A hypercharge transformation scales an up-singlet symbol by the fourth power of the
  conjugate scalar, the up singlet carrying `6Y = -4`. -/
lemma repGauge_u1_u (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repGauge ((1, 1, t) : GaugeGroupI) (uComponent f l j)
      = (star (t : ℂ)) ^ 4 • uComponent f l j := by
  rw [rep_uComponent]
  simp [Matrix.one_apply, unitary_inv_coe]

/-!

### E.4. The conjugate up singlet

-/

/-- A colour transformation moves the colour index of a conjugate up-singlet symbol by the
  matrix itself, the index being fundamental. -/
lemma repGauge_su3_baru (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) :
    repGauge ((U, 1, 1) : GaugeGroupI) (baruComponent f l (s, c))
      = ∑ a, U.1 a c • baruComponent f l (s, a) := by
  rw [rep_baruComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su3Elt, toSU3_su3Elt, toU1_su3Elt, su3_inv_apply]
  simp

/-- An isospin transformation fixes a conjugate up-singlet symbol. -/
lemma repGauge_su2_baru (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge ((1, V, 1) : GaugeGroupI) (baruComponent f l j)
      = baruComponent f l j := by
  rw [rep_baruComponent]
  simp [Matrix.one_apply]

/-- A hypercharge transformation scales a conjugate up-singlet symbol by the fourth power
  of the scalar, the conjugate up singlet carrying `6Y = 4`. -/
lemma repGauge_u1_baru (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 3) :
    repGauge ((1, 1, t) : GaugeGroupI) (baruComponent f l j)
      = (t : ℂ) ^ 4 • baruComponent f l j := by
  rw [rep_baruComponent]
  simp [Matrix.one_apply, unitary_inv_coe, apply_ite (starRingEnd ℂ)]

/-!

### E.5. The quark doublet

-/

/-- A colour transformation moves the colour index of a quark-doublet symbol by the
  conjugate matrix, the index being anti-fundamental. -/
lemma repGauge_su3_Q (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) (w : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (QComponent f l (s, c, w))
      = ∑ a, conj (U.1 a c) • QComponent f l (s, a, w) := by
  rw [rep_QComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.sum_univ_two, inv_su3Elt, toSU3_su3Elt, toU1_su3Elt, toSU2_su3Elt]
  fin_cases w <;> simp [su3_inv_apply]

/-- An isospin transformation moves the isospin index of a quark-doublet symbol by the
  conjugate matrix, the index being anti-fundamental. -/
lemma repGauge_su2_Q (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) (w : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (QComponent f l (s, c, w))
      = ∑ a, conj (V.1 a w) • QComponent f l (s, c, a) := by
  rw [rep_QComponent, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.sum_univ_three, inv_su2Elt, toSU2_su2Elt, toU1_su2Elt, toSU3_su2Elt]
  fin_cases c <;> simp [su2_inv_apply]

/-- A hypercharge transformation scales a quark-doublet symbol by the conjugate scalar,
  the quark doublet carrying `6Y = -1`. -/
lemma repGauge_u1_Q (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (s : Fin 2) (c : Fin 3) (w : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (QComponent f l (s, c, w))
      = star (t : ℂ) • QComponent f l (s, c, w) := by
  rw [rep_QComponent]
  fin_cases w <;> simp [Matrix.one_apply, unitary_inv_coe]

/-!

### E.6. The conjugate quark doublet

-/

/-- A colour transformation moves the colour index of a conjugate quark-doublet symbol by
  the matrix itself, the index being fundamental. -/
lemma repGauge_su3_barQ (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) (w : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (barQComponent f l (s, c, w))
      = ∑ a, U.1 a c • barQComponent f l (s, a, w) := by
  rw [rep_barQComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.sum_univ_two]
  rw [inv_su3Elt, toSU3_su3Elt, toU1_su3Elt, toSU2_su3Elt]
  fin_cases w <;> simp [su3_inv_apply]

/-- An isospin transformation moves the isospin index of a conjugate quark-doublet symbol
  by the matrix itself, the index being fundamental. -/
lemma repGauge_su2_barQ (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) (c : Fin 3) (w : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (barQComponent f l (s, c, w))
      = ∑ a, V.1 a w • barQComponent f l (s, c, a) := by
  rw [rep_barQComponent, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.sum_univ_three, inv_su2Elt, toSU2_su2Elt, toU1_su2Elt, toSU3_su2Elt]
  fin_cases c <;> simp [su2_inv_apply]

/-- A hypercharge transformation scales a conjugate quark-doublet symbol by the scalar,
  the conjugate quark doublet carrying `6Y = 1`. -/
lemma repGauge_u1_barQ (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (s : Fin 2) (c : Fin 3) (w : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (barQComponent f l (s, c, w))
      = (t : ℂ) • barQComponent f l (s, c, w) := by
  rw [rep_barQComponent]
  fin_cases w <;>
    simp [Matrix.one_apply, unitary_inv_coe, apply_ite (starRingEnd ℂ)]

/-!

### E.7. The lepton doublet

-/

/-- A colour transformation fixes a lepton-doublet symbol, which carries no colour. -/
lemma repGauge_su3_L (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (LComponent f l j)
      = LComponent f l j := by
  rw [rep_LComponent]
  simp [Matrix.one_apply]

/-- An isospin transformation moves the isospin index of a lepton-doublet symbol by the
  conjugate matrix, the index being anti-fundamental. -/
lemma repGauge_su2_L (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s w : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (LComponent f l (s, w))
      = ∑ a, conj (V.1 a w) • LComponent f l (s, a) := by
  rw [rep_LComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su2Elt, toSU2_su2Elt, toU1_su2Elt, su2_inv_apply]
  simp

/-- A hypercharge transformation scales a lepton-doublet symbol by the cube of the scalar,
  the lepton doublet carrying `6Y = 3`. -/
lemma repGauge_u1_L (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (j : Fin 2 × Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (LComponent f l j)
      = (t : ℂ) ^ 3 • LComponent f l j := by
  rw [rep_LComponent]
  simp [Matrix.one_apply, unitary_inv_coe]

/-!

### E.8. The conjugate lepton doublet

-/

/-- A colour transformation fixes a conjugate lepton-doublet symbol, which carries no
  colour. -/
lemma repGauge_su3_barL (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (barLComponent f l j)
      = barLComponent f l j := by
  rw [rep_barLComponent]
  simp [Matrix.one_apply]

/-- An isospin transformation moves the isospin index of a conjugate lepton-doublet symbol
  by the matrix itself, the index being fundamental. -/
lemma repGauge_su2_barL (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s w : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (barLComponent f l (s, w))
      = ∑ a, V.1 a w • barLComponent f l (s, a) := by
  rw [rep_barLComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inv_su2Elt, toSU2_su2Elt, toU1_su2Elt, su2_inv_apply]
  simp

/-- A hypercharge transformation scales a conjugate lepton-doublet symbol by the cube of
  the conjugate scalar, the conjugate lepton doublet carrying `6Y = -3`. -/
lemma repGauge_u1_barL (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (s w : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (barLComponent f l (s, w))
      = (star (t : ℂ)) ^ 3 • barLComponent f l (s, w) := by
  rw [rep_barLComponent]
  fin_cases w <;>
    simp [Matrix.one_apply, unitary_inv_coe, apply_ite (starRingEnd ℂ)]

/-!

### E.9. The lepton singlet

-/

/-- A colour transformation fixes a lepton-singlet symbol. -/
lemma repGauge_su3_e (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (eComponent f l s)
      = eComponent f l s := by
  rw [rep_eComponent]
  simp

/-- An isospin transformation fixes a lepton-singlet symbol. -/
lemma repGauge_su2_e (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (eComponent f l s)
      = eComponent f l s := by
  rw [rep_eComponent]
  simp

/-- A hypercharge transformation scales a lepton-singlet symbol by the sixth power of the
  scalar, the lepton singlet carrying `6Y = 6`. -/
lemma repGauge_u1_e (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (s : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (eComponent f l s)
      = (t : ℂ) ^ 6 • eComponent f l s := by
  rw [rep_eComponent]
  simp [unitary_inv_coe]

/-!

### E.10. The conjugate lepton singlet

-/

/-- A colour transformation fixes a conjugate lepton-singlet symbol. -/
lemma repGauge_su3_bare (U : specialUnitaryGroup (Fin 3) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) :
    repGauge ((U, 1, 1) : GaugeGroupI) (bareComponent f l s)
      = bareComponent f l s := by
  rw [rep_bareComponent]
  simp

/-- An isospin transformation fixes a conjugate lepton-singlet symbol. -/
lemma repGauge_su2_bare (V : specialUnitaryGroup (Fin 2) ℂ) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (s : Fin 2) :
    repGauge ((1, V, 1) : GaugeGroupI) (bareComponent f l s)
      = bareComponent f l s := by
  rw [rep_bareComponent]
  simp

/-- A hypercharge transformation scales a conjugate lepton-singlet symbol by the sixth
  power of the conjugate scalar, the conjugate lepton singlet carrying `6Y = -6`. -/
lemma repGauge_u1_bare (t : unitary ℂ) (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (s : Fin 2) :
    repGauge ((1, 1, t) : GaugeGroupI) (bareComponent f l s)
      = (star (t : ℂ)) ^ 6 • bareComponent f l s := by
  rw [rep_bareComponent]
  simp [unitary_inv_coe]

end FermionSector

end StandardModel
