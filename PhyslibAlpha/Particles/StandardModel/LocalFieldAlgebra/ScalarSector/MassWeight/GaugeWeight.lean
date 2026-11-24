/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.ScalarSector.MassWeight.Basic
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.ScalarSector.DerivSubmodule.GaugeWeight
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.Invariants.Basic
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.SU2Conjugation
/-!
# The gauge weight decomposition of the Higgs mass-weight submodules

The gauge invariants of the scalar sector up to mass weight eight, through the torus weights
and the isospin classifiers.

## i. Overview

Each mass-weight submodule of the scalar sector up to weight eight has an explicit
description in terms of the derivative submodules `derivSubmodule n`, and each derivative
submodule carries a gauge weight decomposition.  Transporting the latter along the former
decomposes every mass-weight submodule up to weight eight.

The weights carried by a derivative submodule are the four weights of the Higgs doublet
and its conjugate, `(0, 0, ∓1, -3)` and `(0, 0, ±1, 3)`.  Every one of them has
hypercharge `± 3`, so a product of `k` derivative submodules can only reach gauge weight
zero when `k` is even and the Higgs and conjugate-Higgs factors are equally many.  This
is what makes the weight-zero pieces small: at mass weight four and six they are spanned
by the isospin-diagonal pairings `∇H^i ∇H̄^i`, and at mass weight eight the quartic
monomials `∇H^i ∇H̄^i ∇H^j ∇H̄^j` join them.

The gauge weight alone cannot finish the job: it cannot separate the isospin singlet
`∇H · ∇H̄` from the neutral component of the isospin triplet, which carries the same
weight.  That separation is `SU(2)` mathematics and belongs to the isospin classifiers of
`GaugeGroup.Invariants` rather than here.  What is left for this file is to present each
surviving piece as a family those classifiers know.  A conjugate Higgs symbol against a
Higgs symbol is a family with a fundamental and an anti-fundamental isospin index — the conjugate
symbol carries the fundamental isospin index and the Higgs symbol the anti-fundamental one, so it
goes
second — and the delta contraction, which spans its invariants, is the isospin contraction
`dotGaugeHiggs`.  The quartic is a family with four fundamental indices once its two Higgs
symbols are re-indexed by the antisymmetric symbol, and of its two epsilon contractions
one is the square of the isospin contraction and the other vanishes, pairing commuting
factors antisymmetrically.

Sections F and G are reductions for the gauge group, stated modulo any gauge-stable
submodule `S`, which is what lets the other sectors be carried along; taking `S` trivial in
section H recovers the statements about the mass-weight submodules themselves.

## ii. Key results

- `massWeightSubmoduleGaugeWeightTwo` up to `massWeightSubmoduleGaugeWeightEight` : the gauge
  weight decompositions of the mass-weight submodules up to weight eight.
- `massWeightSubmoduleGaugeWeightEight_piece_zero` : the weight-zero piece at mass weight eight.
- `isEquivariant_isospinFundAntiFund_isoFamily`, `isEquivariant_isospinQuadFund_quadFamily` : the
  Higgs symbols as isospin families.
- `reducesInvariantsTo_massWeightSubmodule_four` up to
  `reducesInvariantsTo_massWeightSubmodule_eight` : the gauge classification up to mass weight
  eight, modulo a gauge-stable submodule.
- `gaugeInvariantOfMassDim_four_eq_dotSpan` up to `gaugeInvariantOfMassDim_eight_eq_dotSpan` :
  the gauge-invariant submodules up to mass weight eight.

## iii. Table of contents

- A. The decompositions
- B. The pieces of a derivative submodule
- C. The weight-zero pieces of the products
- D. The weight-zero pieces of the mass-weight submodules
- E. The Higgs symbols as isospin families
- F. The isospin spans reduce to the isospin contractions
- G. The gauge classification up to mass weight eight
- H. The gauge-invariant submodules up to mass weight eight

## iv. References

* None.

-/

@[expose] public section

open TensorSpecies
open suTensor (fundAntiFundIdx)

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz ComplexConjugate
open LocalCovFieldAlgebra (repGaugeGroupI repLorentzGroup massWeightPoly)

namespace ScalarSector

/-!

## A. The decompositions

Every term of the Higgs algebra has even mass weight, so the odd mass-weight submodules
vanish (`massWeightSubmodule_odd_eq_bot`). The even ones are built from the
derivative submodules by the descriptions of `MassWeight/Basic.lean`. Weight two is a single
derivative submodule, and the higher weights add the products which distribute the mass
weight over several towers.

-/

/-- Weight two is the underived Higgs tower. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightTwo :
    GaugeWeightDecomposition repGaugeGroupI (massWeightSubmodule 2) :=
  GaugeWeightDecomposition.copy (derivSubmoduleGaugeWeight 0) _
    massWeightSubmodule_two_eq_deriv

/-- Weight four is the once-derived tower together with the products of two underived
  ones. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightFour :
    GaugeWeightDecomposition repGaugeGroupI (massWeightSubmodule 4) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.sup (d := derivSubmoduleGaugeWeight 1)
      (d' := GaugeWeightDecomposition.mul (d := derivSubmoduleGaugeWeight 0)
        (d' := derivSubmoduleGaugeWeight 0))) _
    massWeightSubmodule_four_eq_deriv

/-- Weight six is the twice-derived tower, the once-derived tower against an underived
  one, and the products of three underived ones. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightSix :
    GaugeWeightDecomposition repGaugeGroupI (massWeightSubmodule 6) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.sup
      (d := GaugeWeightDecomposition.sup (d := derivSubmoduleGaugeWeight 2)
        (d' := GaugeWeightDecomposition.mul (d := derivSubmoduleGaugeWeight 1)
          (d' := derivSubmoduleGaugeWeight 0)))
      (d' := GaugeWeightDecomposition.mul
        (d := GaugeWeightDecomposition.mul (d := derivSubmoduleGaugeWeight 0)
          (d' := derivSubmoduleGaugeWeight 0))
        (d' := derivSubmoduleGaugeWeight 0))) _
    massWeightSubmodule_six_eq_deriv

/-- Weight eight is the thrice-derived tower, the two ways of splitting the derivatives over
  two towers, the once-derived tower against two underived ones, and the products of four
  underived ones. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightEight :
    GaugeWeightDecomposition repGaugeGroupI (massWeightSubmodule 8) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.sup
      (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
          (d := GaugeWeightDecomposition.sup (d := derivSubmoduleGaugeWeight 3)
            (d' := GaugeWeightDecomposition.mul (d := derivSubmoduleGaugeWeight 2)
              (d' := derivSubmoduleGaugeWeight 0)))
          (d' := GaugeWeightDecomposition.mul (d := derivSubmoduleGaugeWeight 1)
            (d' := derivSubmoduleGaugeWeight 1)))
        (d' := GaugeWeightDecomposition.mul
          (d := GaugeWeightDecomposition.mul (d := derivSubmoduleGaugeWeight 1)
            (d' := derivSubmoduleGaugeWeight 0))
          (d' := derivSubmoduleGaugeWeight 0)))
      (d' := GaugeWeightDecomposition.mul
        (d := GaugeWeightDecomposition.mul
          (d := GaugeWeightDecomposition.mul (d := derivSubmoduleGaugeWeight 0)
            (d' := derivSubmoduleGaugeWeight 0))
          (d' := derivSubmoduleGaugeWeight 0))
        (d' := derivSubmoduleGaugeWeight 0))) _
    massWeightSubmodule_eight_eq_deriv

/-!

## B. The pieces of a derivative submodule

A derivative submodule is the join of a Higgs and a conjugate-Higgs submodule, and each of
those is concentrated in two weights.  The four weights are distinct, so each piece of the
join is the span of one of the four families of symbols, and every other weight — the zero
weight in particular — has vanishing piece.

-/

/-- The weight-`w` piece of a derivative submodule, as the join of the Higgs and
  conjugate-Higgs pieces. -/
lemma derivSubmoduleGaugeWeight_piece_eq (n : ℕ) (w : GaugeWeight) :
    (derivSubmoduleGaugeWeight n).piece w
      = (if w = ((0, 0, -1, -3) : GaugeWeight) then
          ⨆ d : Fin n → (Fin 1 ⊕ Fin 3), ℂ ∙ higgs d 0
        else if w = ((0, 0, 1, -3) : GaugeWeight) then
          ⨆ d : Fin n → (Fin 1 ⊕ Fin 3), ℂ ∙ higgs d 1
        else ⊥)
        ⊔ (if w = ((0, 0, 1, 3) : GaugeWeight) then
            ⨆ d : Fin n → (Fin 1 ⊕ Fin 3), ℂ ∙ barHiggs d 0
          else if w = ((0, 0, -1, 3) : GaugeWeight) then
            ⨆ d : Fin n → (Fin 1 ⊕ Fin 3), ℂ ∙ barHiggs d 1
          else ⊥) := rfl

/-- The piece at the weight of the upper Higgs component. -/
lemma derivSubmoduleGaugeWeight_piece_higgs_zero (n : ℕ) :
    (derivSubmoduleGaugeWeight n).piece (0, 0, -1, -3)
      = ⨆ d : Fin n → (Fin 1 ⊕ Fin 3), ℂ ∙ higgs d 0 := by
  rw [derivSubmoduleGaugeWeight_piece_eq, ite_eq_left rfl, ite_eq_right (by decide),
    ite_eq_right (by decide), sup_bot_eq]

/-- The piece at the weight of the lower Higgs component. -/
lemma derivSubmoduleGaugeWeight_piece_higgs_one (n : ℕ) :
    (derivSubmoduleGaugeWeight n).piece (0, 0, 1, -3)
      = ⨆ d : Fin n → (Fin 1 ⊕ Fin 3), ℂ ∙ higgs d 1 := by
  rw [derivSubmoduleGaugeWeight_piece_eq, ite_eq_right (by decide), ite_eq_left rfl,
    ite_eq_right (by decide), ite_eq_right (by decide), sup_bot_eq]

/-- The piece at the weight of the upper conjugate-Higgs component. -/
lemma derivSubmoduleGaugeWeight_piece_barHiggs_zero (n : ℕ) :
    (derivSubmoduleGaugeWeight n).piece (0, 0, 1, 3)
      = ⨆ d : Fin n → (Fin 1 ⊕ Fin 3), ℂ ∙ barHiggs d 0 := by
  rw [derivSubmoduleGaugeWeight_piece_eq, ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left rfl, bot_sup_eq]

/-- The piece at the weight of the lower conjugate-Higgs component. -/
lemma derivSubmoduleGaugeWeight_piece_barHiggs_one (n : ℕ) :
    (derivSubmoduleGaugeWeight n).piece (0, 0, -1, 3)
      = ⨆ d : Fin n → (Fin 1 ⊕ Fin 3), ℂ ∙ barHiggs d 1 := by
  rw [derivSubmoduleGaugeWeight_piece_eq, ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_left rfl, bot_sup_eq]

/-- A derivative submodule has no weight-zero content, since every Higgs symbol carries
  hypercharge. -/
lemma derivSubmoduleGaugeWeight_piece_zero (n : ℕ) :
    (derivSubmoduleGaugeWeight n).piece 0 = ⊥ :=
  (derivSubmoduleGaugeWeight n).piece_eq_zero_of_not_mem_supp 0
    (by rw [derivSubmoduleGaugeWeight_supp]; decide)

/-!

## C. The weight-zero pieces of the products

Two derivative submodules pair to weight zero exactly by matching a Higgs symbol against a
conjugate-Higgs symbol of the same isospin component, in either order, so the weight-zero
piece of such a product is a join of four spans of pairings `∇H^i ∇H̄^i`.  Three of them
cannot reach weight zero at all, because hypercharge is `± 3` on every generator, so an odd
number of factors leaves an odd multiple of three.  Four of them reach weight zero on the
three quartic monomials.

-/

/-- The span of the isospin-diagonal pairings of a Higgs symbol carrying `n` derivatives
  with a conjugate-Higgs symbol carrying `m` derivatives, at isospin component `i`. -/
noncomputable def higgsBarHiggsSpan
    (n m : ℕ) (i : Fin 2) : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ⨆ (d : Fin n → (Fin 1 ⊕ Fin 3)) (d' : Fin m → (Fin 1 ⊕ Fin 3)),
    ℂ ∙ (higgs d i * barHiggs d' i)

/-- The span of the underived quartic monomial pairing the isospin components `i` and
  `j`. -/
noncomputable def quarticSpan
    (i j : Fin 2) : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ℂ ∙ (higgs ![] i * barHiggs ![] i * higgs ![] j * barHiggs ![] j)

/-- The weight-zero piece of a product of two derivative submodules is spanned by the
  isospin-diagonal pairings, taken in both orders of the two towers. -/
lemma derivSubmodule_mul_piece_zero (n m : ℕ) :
    GaugeWeightDecomposition.piece repGaugeGroupI (derivSubmodule n * derivSubmodule m) 0
      = higgsBarHiggsSpan n m 0 ⊔ higgsBarHiggsSpan n m 1
        ⊔ higgsBarHiggsSpan m n 0 ⊔ higgsBarHiggsSpan m n 1 := by
  rw [GaugeWeightDecomposition.mul_piece_eq_sub 0, derivSubmoduleGaugeWeight_supp n]
  simp only [Finset.iSup_insert, Finset.iSup_singleton,
    show (0 : GaugeWeight) - (0, 0, -1, -3) = (0, 0, 1, 3) from by decide,
    show (0 : GaugeWeight) - (0, 0, 1, -3) = (0, 0, -1, 3) from by decide,
    show (0 : GaugeWeight) - (0, 0, 1, 3) = (0, 0, -1, -3) from by decide,
    show (0 : GaugeWeight) - (0, 0, -1, 3) = (0, 0, 1, -3) from by decide,
    derivSubmoduleGaugeWeight_piece_higgs_zero,
    derivSubmoduleGaugeWeight_piece_higgs_one,
    derivSubmoduleGaugeWeight_piece_barHiggs_zero,
    derivSubmoduleGaugeWeight_piece_barHiggs_one]
  have hcomm : ∀ {n1 n2 : ℕ} (d1 : Fin n1 → (Fin 1 ⊕ Fin 3)) (d2 : Fin n2 → (Fin 1 ⊕ Fin 3))
      (a b : Fin 2), barHiggs d1 a * higgs d2 b = higgs d2 b * barHiggs d1 a :=
    fun d1 d2 a b => ((H_comm_barH _ _ _ _ _ _).symm).eq
  simp only [Submodule.iSup_mul, Submodule.mul_iSup, Submodule.span_mul_span,
    Set.singleton_mul_singleton, hcomm]
  simp only [higgsBarHiggsSpan, sup_assoc]
  refine congrArg₂ (· ⊔ ·) iSup_comm (congrArg₂ (· ⊔ ·) iSup_comm rfl)

/-- A product of three derivative submodules has no weight-zero content, since the hypercharge of
  three Higgs generators is an odd multiple of three. -/
lemma derivSubmodule_mul_mul_piece_zero (n m k : ℕ) :
    GaugeWeightDecomposition.piece repGaugeGroupI
      (derivSubmodule n * derivSubmodule m * derivSubmodule k) 0 = ⊥ := by
  refine GaugeWeightDecomposition.piece_eq_zero_of_not_mem_supp _ 0 ?_
  rw [GaugeWeightDecomposition.mul_supp, GaugeWeightDecomposition.mul_supp,
    derivSubmoduleGaugeWeight_supp n, derivSubmoduleGaugeWeight_supp m,
    derivSubmoduleGaugeWeight_supp k]
  decide

/-- The weight-zero piece of the product of four underived derivative submodules is spanned by the
  three quartic monomials, the ones pairing two Higgs symbols against two conjugate ones with
  matching isospin. -/
lemma derivSubmodule_zero_pow_four_piece_zero :
    GaugeWeightDecomposition.piece repGaugeGroupI
      (derivSubmodule 0 * derivSubmodule 0 * derivSubmodule 0
        * derivSubmodule 0) 0
      = quarticSpan 0 0 ⊔ quarticSpan 0 1 ⊔ quarticSpan 1 1 := by
  have hbh : ∀ (a b : Fin 2),
      barHiggs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) a * higgs ![] b
        = higgs ![] b * barHiggs ![] a := fun a b => (H_comm_barH _ _ _ _ _ _).symm.eq
  have hbh' : ∀ (a b : Fin 2) (y : fieldData.LocalCovFieldAlgebra),
      barHiggs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) a * (higgs ![] b * y)
        = higgs ![] b * (barHiggs ![] a * y) := fun a b y => by
    rw [← mul_assoc, hbh, mul_assoc]
  have hhh : higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 1 * higgs ![] 0
      = higgs ![] 0 * higgs ![] 1 := (H_comm_H _ _ _ _ _ _).eq
  have hhh' : ∀ y : fieldData.LocalCovFieldAlgebra,
      higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 1 * (higgs ![] 0 * y)
        = higgs ![] 0 * (higgs ![] 1 * y) := fun y => by rw [← mul_assoc, hhh, mul_assoc]
  have hbb : barHiggs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 1 * barHiggs ![] 0
      = barHiggs ![] 0 * barHiggs ![] 1 := (barH_comm_barH _ _ _ _ _ _).eq
  simp +decide only [GaugeWeightDecomposition.mul_piece_eq_sub',
    derivSubmoduleGaugeWeight_supp 0, Finset.iSup_insert, Finset.iSup_singleton,
    derivSubmoduleGaugeWeight_piece_eq, ite_true, ite_false, bot_sup_eq, sup_bot_eq,
    Submodule.bot_mul]
  simp only [Matrix.empty_eq, ciSup_unique, quarticSpan, Submodule.sup_mul,
    Submodule.span_mul_span, Set.singleton_mul_singleton, mul_assoc, hbh, hbh', hhh,
    hhh', hbb]
  generalize (ℂ ∙ (higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 0 *
    (higgs ![] 0 * (barHiggs ![] 0 * barHiggs ![] 0)))) = A
  generalize (ℂ ∙ (higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 0 *
    (higgs ![] 1 * (barHiggs ![] 0 * barHiggs ![] 1)))) = C
  generalize (ℂ ∙ (higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 1 *
    (higgs ![] 1 * (barHiggs ![] 1 * barHiggs ![] 1)))) = D
  simp only [sup_comm, sup_left_comm, sup_idem, sup_left_idem]

/-!

## D. The weight-zero pieces of the mass-weight submodules

Assembling section C along the descriptions of section A gives the weight-zero piece of
each mass-weight submodule up to weight eight.  The odd weights and weight two are trivial,
weight four is the underived pairing, weight six adds the pairings with one derivative on
either factor, and weight eight adds the pairings with two derivatives, those with one
derivative on each factor, and the three quartic monomials.

-/

/-- The weight-zero piece at mass weight two is trivial, since a single Higgs symbol carries
  hypercharge. -/
lemma massWeightSubmoduleGaugeWeightTwo_piece_zero :
    (massWeightSubmoduleGaugeWeightTwo).piece 0 = ⊥ :=
  derivSubmoduleGaugeWeight_piece_zero 0

/-- The weight-zero piece at mass weight four is spanned by the underived isospin-diagonal
  pairings. -/
lemma massWeightSubmoduleGaugeWeightFour_piece_zero :
    (massWeightSubmoduleGaugeWeightFour).piece 0
      = higgsBarHiggsSpan 0 0 0 ⊔ higgsBarHiggsSpan 0 0 1 := by
  show (derivSubmoduleGaugeWeight 1).piece 0
      ⊔ GaugeWeightDecomposition.piece repGaugeGroupI (derivSubmodule 0 * derivSubmodule 0) 0 = _
  rw [derivSubmoduleGaugeWeight_piece_zero 1, derivSubmodule_mul_piece_zero 0 0,
    bot_sup_eq]
  simp only [sup_comm, sup_left_comm, sup_idem, sup_left_idem]

/-- The weight-zero piece at mass weight six is spanned by the isospin-diagonal pairings carrying
  one derivative, on either of the two factors. -/
lemma massWeightSubmoduleGaugeWeightSix_piece_zero :
    (massWeightSubmoduleGaugeWeightSix).piece 0
      = higgsBarHiggsSpan 1 0 0 ⊔ higgsBarHiggsSpan 1 0 1
        ⊔ higgsBarHiggsSpan 0 1 0 ⊔ higgsBarHiggsSpan 0 1 1 := by
  show ((derivSubmoduleGaugeWeight 2).piece 0
      ⊔ GaugeWeightDecomposition.piece repGaugeGroupI (derivSubmodule 1 * derivSubmodule 0) 0)
      ⊔ GaugeWeightDecomposition.piece repGaugeGroupI
        (derivSubmodule 0 * derivSubmodule 0 * derivSubmodule 0) 0 = _
  rw [derivSubmoduleGaugeWeight_piece_zero 2, derivSubmodule_mul_piece_zero 1 0,
    derivSubmodule_mul_mul_piece_zero 0 0 0, bot_sup_eq, sup_bot_eq]

/-- The weight-zero piece at mass weight eight is spanned by the isospin-diagonal pairings carrying
  two derivatives on one factor or one on each, together with the three quartic monomials. -/
lemma massWeightSubmoduleGaugeWeightEight_piece_zero :
    (massWeightSubmoduleGaugeWeightEight).piece 0
      = higgsBarHiggsSpan 2 0 0 ⊔ higgsBarHiggsSpan 2 0 1
        ⊔ higgsBarHiggsSpan 0 2 0 ⊔ higgsBarHiggsSpan 0 2 1
        ⊔ (higgsBarHiggsSpan 1 1 0 ⊔ higgsBarHiggsSpan 1 1 1)
        ⊔ (quarticSpan 0 0 ⊔ quarticSpan 0 1 ⊔ quarticSpan 1 1) := by
  show ((((derivSubmoduleGaugeWeight 3).piece 0
        ⊔ GaugeWeightDecomposition.piece repGaugeGroupI
          (derivSubmodule 2 * derivSubmodule 0) 0)
      ⊔ GaugeWeightDecomposition.piece repGaugeGroupI (derivSubmodule 1 * derivSubmodule 1) 0)
      ⊔ GaugeWeightDecomposition.piece repGaugeGroupI
        (derivSubmodule 1 * derivSubmodule 0 * derivSubmodule 0) 0)
      ⊔ GaugeWeightDecomposition.piece repGaugeGroupI
        (derivSubmodule 0 * derivSubmodule 0 * derivSubmodule 0
          * derivSubmodule 0) 0 = _
  rw [derivSubmoduleGaugeWeight_piece_zero 3, derivSubmodule_mul_piece_zero 2 0,
    derivSubmodule_mul_piece_zero 1 1, derivSubmodule_mul_mul_piece_zero 1 0 0,
    derivSubmodule_zero_pow_four_piece_zero, bot_sup_eq, sup_bot_eq]
  -- the spans are atoms for the final reordering of the join
  generalize higgsBarHiggsSpan 2 0 0 = v1, higgsBarHiggsSpan 2 0 1 = v2,
    higgsBarHiggsSpan 0 2 0 = v3, higgsBarHiggsSpan 0 2 1 = v4, higgsBarHiggsSpan 1 1 0 = v5,
    higgsBarHiggsSpan 1 1 1 = v6, quarticSpan 0 0 = v7, quarticSpan 0 1 = v8,
    quarticSpan 1 1 = v9
  simp only [sup_comm, sup_left_comm, sup_idem, sup_left_idem]

/-!

## E. The Higgs symbols as isospin families

The gauge weight has done all it can.  What it cannot see is the difference between the
isospin singlet `∇H · ∇H̄` and the neutral component of the isospin triplet: both are
neutral under the torus, so both sit in the weight-zero piece, and only the non-abelian
part of `SU(2)` tells them apart.  That is what the isospin classifiers of
`GaugeGroup.Invariants` are for, and this section presents the surviving pieces as
families they classify.

The variance has to be read off correctly, and it is opposite to what the notation
suggests.  A conjugate Higgs symbol carries a fundamental isospin index — an isospin
transformation moves it by the matrix of the `SU(2)` element, with the summed index in the
row slot — and a Higgs symbol carries an anti-fundamental one, moved by the conjugate
matrix.  So the pairing span of section C is the span of the components of
`fun l => barHiggs d' (l 0) * higgs d (l 1)`, conjugate symbol first, which is an
family with a fundamental and an anti-fundamental isospin index; and its delta contraction, which
spans its invariants, is the isospin contraction `dotGaugeHiggs`.  That identification is the whole
point of the section: `dotSpan` is the span of delta contractions, and nothing else
survives.

The quartic needs four fundamental indices, so its two Higgs symbols must be re-indexed by
the antisymmetric symbol first.  `tildeHiggs` is that re-index, `H̃⁰ = H¹` and
`H̃¹ = -H⁰`, and it is fundamental because `SU(2)` is pseudo-real.  The quartic family is
then a product of four fundamental families, and `IsospinQuadFund` classifies it.  Its
two epsilon contractions come out as the square of the isospin contraction and zero:
the second pairs the two conjugate symbols with each other and the two Higgs symbols with
each other, and an antisymmetric contraction of two commuting factors vanishes.

-/

/-- An isospin transformation moves the isospin index of a Higgs symbol by the conjugate
  matrix, the index of a Higgs symbol is anti-fundamental. -/
lemma rep_su2_higgs (V : specialUnitaryGroup (Fin 2) ℂ) {n : ℕ}
    (d : Fin n → (Fin 1 ⊕ Fin 3)) (i : Fin 2) :
    repGaugeGroupI ((1, V, 1) : GaugeGroupI) (higgs d i)
      = ∑ a, conj (V.1 a i) • higgs d a := by
  rw [rep_higgsComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show ((1, V, 1) : GaugeGroupI)⁻¹ = ((1, V⁻¹, 1) : GaugeGroupI) from by simp,
    show GaugeGroupI.toSU2 ((1, V⁻¹, 1) : GaugeGroupI) = V⁻¹ from rfl,
    show GaugeGroupI.toU1 ((1, V⁻¹, 1) : GaugeGroupI) = 1 from rfl, su2_inv_apply]
  simp

/-- An isospin transformation moves the isospin index of a conjugate Higgs symbol by the
  matrix itself, the index of a conjugate Higgs symbol is fundamental. -/
lemma rep_su2_barHiggs (V : specialUnitaryGroup (Fin 2) ℂ) {n : ℕ}
    (d : Fin n → (Fin 1 ⊕ Fin 3)) (i : Fin 2) :
    repGaugeGroupI ((1, V, 1) : GaugeGroupI) (barHiggs d i)
      = ∑ a, V.1 a i • barHiggs d a := by
  rw [rep_barHiggsComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show ((1, V, 1) : GaugeGroupI)⁻¹ = ((1, V⁻¹, 1) : GaugeGroupI) from by simp,
    show GaugeGroupI.toSU2 ((1, V⁻¹, 1) : GaugeGroupI) = V⁻¹ from rfl,
    show GaugeGroupI.toU1 ((1, V⁻¹, 1) : GaugeGroupI) = 1 from rfl, su2_inv_apply]
  simp

/-- A product of two symbols each moving by given coefficients moves by the product of
  those coefficients. -/
lemma rep_mul_pair (g : GaugeGroupI) {ι κ : Type} [Fintype ι] [Fintype κ]
    {X : ι → fieldData.LocalCovFieldAlgebra} {Y : κ → fieldData.LocalCovFieldAlgebra} {x₀ : ι}
    {y₀ : κ} {cX : ι → ℂ} {cY : κ → ℂ}
    (hX : repGaugeGroupI g (X x₀) = ∑ x, cX x • X x)
    (hY : repGaugeGroupI g (Y y₀) = ∑ y, cY y • Y y) :
    repGaugeGroupI g (X x₀ * Y y₀) = ∑ x, ∑ y, (cX x * cY y) • (X x * Y y) := by
  rw [LocalCovFieldAlgebra.repGaugeGroupI_mul, hX, hY, Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_smul_comm]

/-- A Higgs symbol commutes with a conjugate Higgs symbol, in the components. -/
lemma higgs_mul_barHiggs_comm {n m : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3))
    (d' : Fin m → (Fin 1 ⊕ Fin 3)) (i j : Fin 2) :
    higgs d i * barHiggs d' j = barHiggs d' j * higgs d i :=
  (H_comm_barH _ _ _ _ _ _).eq

/-- Two Higgs symbols commute, in the components. -/
lemma higgs_mul_higgs_comm {n m : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3))
    (d' : Fin m → (Fin 1 ⊕ Fin 3)) (i j : Fin 2) :
    higgs d i * higgs d' j = higgs d' j * higgs d i :=
  (H_comm_H _ _ _ _ _ _).eq

/-- Two conjugate Higgs symbols commute, in the components. -/
lemma barHiggs_mul_barHiggs_comm {n m : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3))
    (d' : Fin m → (Fin 1 ⊕ Fin 3)) (i j : Fin 2) :
    barHiggs d i * barHiggs d' j = barHiggs d' j * barHiggs d i :=
  (barH_comm_barH _ _ _ _ _ _).eq

/-- The isospin family of a Higgs tower carrying `n` derivatives against a conjugate tower
  carrying `m`. The conjugate symbol supplies the fundamental index and so goes in the
  first slot, the Higgs symbol the anti-fundamental one. -/
noncomputable def isoFamily
    {n m : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3))
    (d' : Fin m → (Fin 1 ⊕ Fin 3)) : (Fin 2 → Fin 2) → fieldData.LocalCovFieldAlgebra :=
  fun l => barHiggs d' (l 0) * higgs d (l 1)

/-- The isospin family carries one fundamental and one anti-fundamental isospin index. -/
lemma isEquivariant_isospinFundAntiFund_isoFamily {n m : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3))
    (d' : Fin m → (Fin 1 ⊕ Fin 3)) :
    (suTensor 2).IsEquivariant ![.fund, .antiFund] (repGaugeGroupI.comp GaugeGroupI.ofSU2)
      (liftComponents ((isoFamily d d') ∘ fundAntiFundIdx)) :=
  IsospinFundAntiFund.of_law fun V l => by
    rw [isoFamily, rep_mul_pair (1, V, 1)
      (rep_su2_barHiggs V d' (l 0)) (rep_su2_higgs V d (l 1)), Physlib.Fin.sum_fin_two_arrow]
    simp only [isoFamily, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The delta contraction of the isospin family, which spans its isospin invariants, is the
  isospin contraction, the Higgs mass term of the two towers. -/
lemma deltaContraction_isoFamily {n m : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3))
    (d' : Fin m → (Fin 1 ⊕ Fin 3)) :
    IsospinFundAntiFund.deltaContraction (isoFamily d d') = dotGaugeHiggs d d' := by
  rw [IsospinFundAntiFund.deltaContraction, dotGaugeHiggs, isoFamily, isoFamily]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [higgs_mul_barHiggs_comm d d' 0 0, higgs_mul_barHiggs_comm d d' 1 1]

/-- The span of the isospin contractions of a Higgs tower carrying `n` derivatives against
  a conjugate tower carrying `m`, the gauge invariants the isospin classification leaves
  at those two derivative orders. -/
noncomputable def dotSpan
    (n m : ℕ) : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ⨆ (d : Fin n → (Fin 1 ⊕ Fin 3)) (d' : Fin m → (Fin 1 ⊕ Fin 3)), ℂ ∙ dotGaugeHiggs d d'

/-- The span of the isospin family is stable under the whole gauge group, since each factor of a
  component goes to a combination of the factors of components. -/
lemma isoFamily_span_stable {n m : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3))
    (d' : Fin m → (Fin 1 ⊕ Fin 3)) (g : GaugeGroupI) {y : fieldData.LocalCovFieldAlgebra}
    (hy : y ∈ Submodule.span ℂ (Set.range (isoFamily d d'))) :
    repGaugeGroupI g y ∈ Submodule.span ℂ (Set.range (isoFamily d d')) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hy
  rw [map_sum]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [map_smul, isoFamily, rep_mul_pair g
    (X := fun a => barHiggs d' a) (Y := fun a => higgs d a) (rep_barHiggsComponent g d' (l 0))
    (rep_higgsComponent g d (l 1))]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ =>
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨![a, b], rfl⟩

/-- The isospin-diagonal pairing spans of section C sit inside the span of the isospin
  family. A diagonal pairing is one of the four components, the two factors commuting. -/
lemma higgsBarHiggsSpan_le_isoFamily_span (n m : ℕ) :
    higgsBarHiggsSpan n m 0 ⊔ higgsBarHiggsSpan n m 1
      ≤ ⨆ (d : Fin n → (Fin 1 ⊕ Fin 3)) (d' : Fin m → (Fin 1 ⊕ Fin 3)),
        Submodule.span ℂ (Set.range (isoFamily d d')) := by
  have key : ∀ (i : Fin 2), higgsBarHiggsSpan n m i
      ≤ ⨆ (d : Fin n → (Fin 1 ⊕ Fin 3)) (d' : Fin m → (Fin 1 ⊕ Fin 3)),
        Submodule.span ℂ (Set.range (isoFamily d d')) := by
    intro i
    rw [higgsBarHiggsSpan]
    refine iSup_le fun d => iSup_le fun d' => ?_
    rw [Submodule.span_singleton_le_iff_mem]
    refine Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem d' ?_)
    rw [higgs_mul_barHiggs_comm d d' i i]
    exact Submodule.subset_span ⟨![i, i], rfl⟩
  exact sup_le (key 0) (key 1)

/-- The re-index of an underived Higgs symbol by the antisymmetric symbol, `H̃⁰ = H¹` and
  `H̃¹ = -H⁰`.  `SU(2)` is pseudo-real, so this turns the anti-fundamental index of a Higgs
  symbol into a fundamental one, which is what the quartic family needs. -/
noncomputable def tildeHiggs
  (i : Fin 2) : fieldData.LocalCovFieldAlgebra :=
  ∑ m : Fin 2, su2Epsilon i m • higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) m

/-- The re-index at isospin zero is the Higgs symbol of isospin one. -/
@[simp] lemma tildeHiggs_zero :
    tildeHiggs 0 = higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 1 := by
  simp [tildeHiggs, Fin.sum_univ_two]

/-- The re-index at isospin one is minus the Higgs symbol of isospin zero. -/
@[simp] lemma tildeHiggs_one :
    tildeHiggs 1 = -higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 0 := by
  simp [tildeHiggs, Fin.sum_univ_two]

/-- The re-indexed Higgs symbol carries a fundamental isospin index, since the four entry
  identities of `GaugeGroup.SU2Conjugation` remove every complex conjugate. -/
lemma rep_su2_tildeHiggs (V : specialUnitaryGroup (Fin 2) ℂ) (i : Fin 2) :
    repGaugeGroupI ((1, V, 1) : GaugeGroupI) (tildeHiggs i)
      = ∑ a, V.1 a i • tildeHiggs a := by
  have hi : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  rcases hi i with rfl | rfl
  · rw [tildeHiggs_zero, rep_su2_higgs, Fin.sum_univ_two, Fin.sum_univ_two,
      tildeHiggs_zero, tildeHiggs_one]
    simp only [su2_conj_apply_zero_one,
      su2_conj_apply_one_one]
    module
  · rw [tildeHiggs_one, map_neg, rep_su2_higgs, Fin.sum_univ_two, Fin.sum_univ_two,
      tildeHiggs_zero, tildeHiggs_one]
    simp only [su2_conj_apply_zero_zero,
      su2_conj_apply_one_zero]
    module

/-- The quartic isospin family, two conjugate Higgs symbols against two re-indexed Higgs
  symbols, each of the four carrying a fundamental isospin index. -/
noncomputable def quadFamily :
    (Fin 4 → Fin 2) → fieldData.LocalCovFieldAlgebra :=
  fun l => barHiggs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) (l 0)
    * (tildeHiggs (l 1)
      * (barHiggs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) (l 2) * tildeHiggs (l 3)))

/-- The quartic family carries four fundamental isospin indices. -/
lemma isEquivariant_isospinQuadFund_quadFamily :
    (suTensor 2).IsEquivariant (fun _ : Fin 4 => .fund) (repGaugeGroupI.comp GaugeGroupI.ofSU2)
      (liftComponents quadFamily) :=
  IsospinQuadFund.of_law fun V l => by
    simp only [quadFamily]
    rw [LocalCovFieldAlgebra.repGaugeGroupI_mul, LocalCovFieldAlgebra.repGaugeGroupI_mul,
      LocalCovFieldAlgebra.repGaugeGroupI_mul, rep_su2_barHiggs V ![] (l 0),
      rep_su2_tildeHiggs V (l 1),
      rep_su2_barHiggs V ![] (l 2), rep_su2_tildeHiggs V (l 3), suTensor.sum_fin_four_arrow]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    simp only [smul_mul_smul_comm, Fin.prod_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three, mul_assoc]

section Quartic

/-- Moving a Higgs symbol past a conjugate one, at no derivatives and inside a product,
  the normalisation used to compare quartic monomials. -/
private lemma barHiggs_higgs_left_comm_zero (i j : Fin 2) (y : fieldData.LocalCovFieldAlgebra) :
    barHiggs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) i * (higgs ![] j * y)
      = higgs ![] j * (barHiggs ![] i * y) := by
  rw [← mul_assoc, ← higgs_mul_barHiggs_comm ![] ![] j i, mul_assoc]

/-- Moving a Higgs symbol past a conjugate one, at no derivatives. -/
private lemma barHiggs_mul_higgs_comm_zero (i j : Fin 2) :
    barHiggs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) i * higgs ![] j
      = higgs ![] j * barHiggs ![] i :=
  (higgs_mul_barHiggs_comm ![] ![] j i).symm

/-- Sorting two Higgs symbols inside a product. -/
private lemma higgs_left_comm_zero (y : fieldData.LocalCovFieldAlgebra) :
    higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 1 * (higgs ![] 0 * y)
      = higgs ![] 0 * (higgs ![] 1 * y) := by
  rw [← mul_assoc, higgs_mul_higgs_comm ![] ![] 1 0, mul_assoc]

/-- The first epsilon contraction of the quartic family is the square of the isospin
  contraction. Pairing the first conjugate symbol with the first Higgs symbol, and the
  second with the second, is pairing each `H̄` with an `H`. -/
lemma epsilonContraction₁₂_quadFamily :
    IsospinQuadFund.epsilonContraction₁₂ quadFamily
      = dotGaugeHiggs ![] ![] * dotGaugeHiggs ![] ![] := by
  simp only [IsospinQuadFund.epsilonContraction₁₂, quadFamily, dotGaugeHiggs,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, tildeHiggs_zero, tildeHiggs_one, neg_mul,
    mul_neg, neg_neg, add_mul, mul_add, mul_assoc, barHiggs_higgs_left_comm_zero,
    barHiggs_mul_higgs_comm_zero, higgs_left_comm_zero,
    barHiggs_mul_barHiggs_comm ![] ![] 1 0]
  abel

/-- The second epsilon contraction of the quartic family vanishes. It pairs the two
  conjugate symbols with each other and the two Higgs symbols with each other, and an
  antisymmetric contraction of two commuting factors is zero. -/
lemma epsilonContraction₁₃_quadFamily :
    IsospinQuadFund.epsilonContraction₁₃ quadFamily = 0 := by
  simp only [IsospinQuadFund.epsilonContraction₁₃, quadFamily, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_three, tildeHiggs_zero, tildeHiggs_one, neg_mul, mul_neg,
    barHiggs_higgs_left_comm_zero, barHiggs_mul_higgs_comm_zero,
    higgs_left_comm_zero, barHiggs_mul_barHiggs_comm ![] ![] 1 0]
  abel

/-- The three quartic monomials of section C lie in the span of the components of the
  quartic family, each being one of those components up to a sign. -/
lemma quarticSpan_le_quadFamily_span :
    quarticSpan 0 0 ⊔ quarticSpan 0 1 ⊔ quarticSpan 1 1
      ≤ Submodule.span ℂ (Set.range quadFamily) := by
  refine sup_le (sup_le ?_ ?_) ?_ <;>
    rw [quarticSpan, Submodule.span_singleton_le_iff_mem]
  · rw [show higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 0 * barHiggs ![] 0 * higgs ![] 0
        * barHiggs ![] 0 = quadFamily ![0, 1, 0, 1] from by
      simp only [quadFamily, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, tildeHiggs_one,
        neg_mul, mul_neg, neg_neg, mul_assoc, barHiggs_higgs_left_comm_zero,
        barHiggs_mul_higgs_comm_zero]]
    exact Submodule.subset_span ⟨_, rfl⟩
  · rw [show higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 0 * barHiggs ![] 0 * higgs ![] 1
        * barHiggs ![] 1 = -quadFamily ![0, 1, 1, 0] from by
      simp only [quadFamily, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, tildeHiggs_zero,
        tildeHiggs_one, neg_mul, mul_neg, neg_neg, mul_assoc,
        barHiggs_higgs_left_comm_zero, barHiggs_mul_higgs_comm_zero]]
    exact neg_mem (Submodule.subset_span ⟨_, rfl⟩)
  · rw [show higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 1 * barHiggs ![] 1 * higgs ![] 1
        * barHiggs ![] 1 = quadFamily ![1, 0, 1, 0] from by
      simp only [quadFamily, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, tildeHiggs_zero,
        mul_assoc, barHiggs_higgs_left_comm_zero, barHiggs_mul_higgs_comm_zero]]
    exact Submodule.subset_span ⟨_, rfl⟩

end Quartic

/-!

## F. The isospin spans reduce to the isospin contractions

The classification is wanted not for the mass-weight submodule alone but modulo a
submodule `S` gathering the other sectors, so every step is a reduction in the sense of
`ReducesInvariantsTo`: a gauge invariant of `V ⊔ S`, for `S` gauge stable, lies in `W ⊔ S`.

The weight-zero pieces of section D are joins of spans of isospin families.
`IsospinFundAntiFund.reducesInvariantsTo_span_deltaContraction` reduces each
span, for the isospin factor and hence for the gauge group, to the line through its delta
contraction, and `ReducesInvariantsTo.iSup` joins the families. The join asks each span to
be gauge stable, which is `isoFamily_span_stable` and is why the enlargement is `isoSpan`
rather than the pairing span of section C: the pairing span keeps only the diagonal
components and a gauge transformation does not. It asks the target to be gauge stable too,
and the isospin contractions are gauge invariant.

-/

/-- The span of the components of all the isospin families of a Higgs tower carrying `n`
  derivatives against a conjugate tower carrying `m`.  This is the gauge-stable
  enlargement of the pairing span of section C. -/
noncomputable def isoSpan
    (n m : ℕ) : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ⨆ (d : Fin n → (Fin 1 ⊕ Fin 3)) (d' : Fin m → (Fin 1 ⊕ Fin 3)),
    Submodule.span ℂ (Set.range (isoFamily d d'))

/-- The isospin span is stable under the gauge group. -/
lemma isStableUnder_isoSpan (n m : ℕ) :
    IsStableUnder (fun g : GaugeGroupI => repGaugeGroupI g) (isoSpan n m) :=
  isStableUnder_iSup fun d => isStableUnder_iSup fun d' g _ hy =>
    isoFamily_span_stable d d' g hy

/-- The span of the isospin contractions is fixed pointwise by the gauge group. -/
lemma isFixedBy_dotSpan (n m : ℕ) :
    IsFixedBy (fun g : GaugeGroupI => repGaugeGroupI g) (dotSpan n m) :=
  isFixedBy_iSup fun d => isFixedBy_iSup fun d' =>
    isFixedBy_span_singleton fun g => rep_dotGaugeHiggs_invariant g d d'

/-- Each isospin-diagonal pairing span of section C sits inside the isospin span. -/
lemma higgsBarHiggsSpan_le_isoSpan' (n m : ℕ) (i : Fin 2) :
    higgsBarHiggsSpan n m i ≤ isoSpan n m := by
  rw [higgsBarHiggsSpan]
  refine iSup_le fun d => iSup_le fun d' => ?_
  rw [Submodule.span_singleton_le_iff_mem]
  refine Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem d' ?_)
  rw [higgs_mul_barHiggs_comm d d' i i]
  exact Submodule.subset_span ⟨![i, i], rfl⟩

/-- The pairing span of section C sits inside the isospin span. -/
lemma higgsBarHiggsSpan_le_isoSpan (n m : ℕ) :
    higgsBarHiggsSpan n m 0 ⊔ higgsBarHiggsSpan n m 1 ≤ isoSpan n m :=
  higgsBarHiggsSpan_le_isoFamily_span n m

/-- The isospin span reduces, for the gauge group, to the span of the isospin contractions.
  Each family's span reduces to the line through its delta contraction, which is the
  isospin contraction of the two towers. -/
lemma reducesInvariantsTo_isoSpan (n m : ℕ) :
    ReducesInvariantsTo (fun g : GaugeGroupI => repGaugeGroupI g) (isoSpan n m) (dotSpan n m) := by
  classical
  have hW := (isFixedBy_dotSpan n m).isStableUnder
  have hV : ∀ (d : Fin n → (Fin 1 ⊕ Fin 3)) (d' : Fin m → (Fin 1 ⊕ Fin 3)),
      IsStableUnder (fun g : GaugeGroupI => repGaugeGroupI g)
        (Submodule.span ℂ (Set.range (isoFamily d d'))) :=
    fun d d' g _ hy => isoFamily_span_stable d d' g hy
  rw [isoSpan]
  refine ReducesInvariantsTo.iSup (fun d => ReducesInvariantsTo.iSup (fun d' => ?_) (hV d) hW)
    (fun d => isStableUnder_iSup (hV d)) hW
  refine ((IsospinFundAntiFund.reducesInvariantsTo_span_deltaContraction
    (isEquivariant_isospinFundAntiFund_isoFamily d d')).comp
      (σ := fun g : GaugeGroupI => repGaugeGroupI g) (fun V => (1, V, 1))).mono_right ?_
  rw [deltaContraction_isoFamily]
  exact le_iSup₂_of_le d d' le_rfl

/-!

## G. The gauge classification up to mass weight eight

Section F is now run at each weight in turn, after the torus has put a gauge invariant in
the weight-zero piece (`GaugeWeightDecomposition.reducesInvariantsTo_piece_zero`). Weight
two dies outright, its weight-zero piece being trivial: a single Higgs symbol carries
hypercharge. Weights four and six are joins of isospin spans and nothing else, so what is
left are the isospin contractions of the towers occurring at that weight: the Higgs mass
term at weight four, and its once-derived companions at weight six.

Weight eight adds the quartic. `IsospinQuadFund` reduces its span to the two epsilon
contractions, the first the square of the underived isospin contraction and the second
zero. The quartic span is joined with the three isospin spans by `ReducesInvariantsTo.sup`,
which asks stability of the isospin spans only, not of the quartic span.

-/

/-- Mass weight two reduces to `⊥` for the gauge group, since a single Higgs symbol carries
  hypercharge, so the weight-zero piece is trivial. -/
lemma reducesInvariantsTo_massWeightSubmodule_two :
    ReducesInvariantsTo (fun g : GaugeGroupI => repGaugeGroupI g) (massWeightSubmodule 2) ⊥ := by
  have h0 := ReducesInvariantsTo.comp (σ := fun g : GaugeGroupI => repGaugeGroupI g) gaugeTorusGen
    massWeightSubmoduleGaugeWeightTwo.reducesInvariantsTo_piece_zero
  rwa [massWeightSubmoduleGaugeWeightTwo_piece_zero] at h0

/-- Mass weight four reduces, for the gauge group, to the underived isospin contraction,
  the Higgs mass term. -/
lemma reducesInvariantsTo_massWeightSubmodule_four :
    ReducesInvariantsTo (fun g : GaugeGroupI => repGaugeGroupI g) (massWeightSubmodule 4)
      (dotSpan 0 0) :=
  (ReducesInvariantsTo.comp (σ := fun g : GaugeGroupI => repGaugeGroupI g) gaugeTorusGen
    massWeightSubmoduleGaugeWeightFour.reducesInvariantsTo_piece_zero).trans
    ((reducesInvariantsTo_isoSpan 0 0).mono_left
      (massWeightSubmoduleGaugeWeightFour_piece_zero.le.trans
        (higgsBarHiggsSpan_le_isoSpan 0 0)))

/-- Mass weight six reduces, for the gauge group, to the isospin contractions carrying one
  derivative, on either factor. -/
lemma reducesInvariantsTo_massWeightSubmodule_six :
    ReducesInvariantsTo (fun g : GaugeGroupI => repGaugeGroupI g) (massWeightSubmodule 6)
      (dotSpan 1 0 ⊔ dotSpan 0 1) := by
  have hW := ((isFixedBy_dotSpan 1 0).sup (isFixedBy_dotSpan 0 1)).isStableUnder
  have hiso := ((reducesInvariantsTo_isoSpan 1 0).mono_right le_sup_left).sup
    ((reducesInvariantsTo_isoSpan 0 1).mono_right le_sup_right) (isStableUnder_isoSpan 0 1)
    hW
  refine (ReducesInvariantsTo.comp (σ := fun g : GaugeGroupI => repGaugeGroupI g) gaugeTorusGen
    massWeightSubmoduleGaugeWeightSix.reducesInvariantsTo_piece_zero).trans
    (hiso.mono_left ?_)
  rw [massWeightSubmoduleGaugeWeightSix_piece_zero, sup_assoc]
  exact sup_le_sup (higgsBarHiggsSpan_le_isoSpan 1 0) (higgsBarHiggsSpan_le_isoSpan 0 1)

/-- Mass weight eight reduces, for the gauge group, to the isospin contractions carrying two
  derivatives and the square of the underived one, the quartic potential. -/
lemma reducesInvariantsTo_massWeightSubmodule_eight :
    ReducesInvariantsTo (fun g : GaugeGroupI => repGaugeGroupI g) (massWeightSubmodule 8)
      (dotSpan 2 0 ⊔ dotSpan 0 2 ⊔ dotSpan 1 1
        ⊔ ℂ ∙ (dotGaugeHiggs ![] ![] * dotGaugeHiggs ![] ![])) := by
  have hq : ∀ g : GaugeGroupI, repGaugeGroupI g (dotGaugeHiggs (![] : Fin 0 → Fin 1 ⊕ Fin 3) ![]
      * dotGaugeHiggs ![] ![]) = dotGaugeHiggs ![] ![] * dotGaugeHiggs ![] ![] :=
    fun g => by rw [LocalCovFieldAlgebra.repGaugeGroupI_mul, rep_dotGaugeHiggs_invariant]
  have hW := ((((isFixedBy_dotSpan 2 0).sup (isFixedBy_dotSpan 0 2)).sup
    (isFixedBy_dotSpan 1 1)).sup (isFixedBy_span_singleton hq)).isStableUnder
  -- the quartic span reduces to its two epsilon contractions, `(H† H)²` and `0`
  have hquad := ((IsospinQuadFund.reducesInvariantsTo_span_epsilonContractions
    isEquivariant_isospinQuadFund_quadFamily).comp (σ := fun g : GaugeGroupI => repGaugeGroupI g)
      (fun V => (1, V, 1))).mono_right (W := dotSpan 2 0 ⊔ dotSpan 0 2 ⊔ dotSpan 1 1
        ⊔ ℂ ∙ (dotGaugeHiggs ![] ![] * dotGaugeHiggs ![] ![])) (by
      rw [epsilonContraction₁₂_quadFamily, epsilonContraction₁₃_quadFamily, Submodule.span_le,
        Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨Submodule.mem_sup_right (Submodule.mem_span_singleton_self _),
        Submodule.zero_mem _⟩)
  -- the three isospin spans reduce to their isospin contractions
  have hiso := (((reducesInvariantsTo_isoSpan 2 0).mono_right
      (le_sup_of_le_left (le_sup_of_le_left le_sup_left))).sup
    ((reducesInvariantsTo_isoSpan 0 2).mono_right
      (le_sup_of_le_left (le_sup_of_le_left le_sup_right))) (isStableUnder_isoSpan 0 2)
    hW).sup ((reducesInvariantsTo_isoSpan 1 1).mono_right (le_sup_of_le_left le_sup_right))
    (isStableUnder_isoSpan 1 1) hW
  refine (ReducesInvariantsTo.comp (σ := fun g : GaugeGroupI => repGaugeGroupI g) gaugeTorusGen
    massWeightSubmoduleGaugeWeightEight.reducesInvariantsTo_piece_zero).trans
    ((hquad.sup hiso (((isStableUnder_isoSpan 2 0).sup (isStableUnder_isoSpan 0 2)).sup
      (isStableUnder_isoSpan 1 1)) hW).mono_left ?_)
  rw [massWeightSubmoduleGaugeWeightEight_piece_zero]
  have h20 : isoSpan 2 0 ≤ Submodule.span ℂ (Set.range quadFamily)
      ⊔ (isoSpan 2 0 ⊔ isoSpan 0 2 ⊔ isoSpan 1 1) :=
    le_sup_of_le_right (le_sup_of_le_left le_sup_left)
  have h02 : isoSpan 0 2 ≤ Submodule.span ℂ (Set.range quadFamily)
      ⊔ (isoSpan 2 0 ⊔ isoSpan 0 2 ⊔ isoSpan 1 1) :=
    le_sup_of_le_right (le_sup_of_le_left le_sup_right)
  exact sup_le (sup_le (sup_le (sup_le ((higgsBarHiggsSpan_le_isoSpan 2 0).trans h20)
    ((higgsBarHiggsSpan_le_isoSpan' 0 2 0).trans h02))
    ((higgsBarHiggsSpan_le_isoSpan' 0 2 1).trans h02))
    ((higgsBarHiggsSpan_le_isoSpan 1 1).trans (le_sup_of_le_right le_sup_right)))
    (quarticSpan_le_quadFamily_span.trans le_sup_left)

/-!

## H. The gauge-invariant submodules up to mass weight eight

Taking the stable submodule to be the trivial one turns section G into a statement about
the mass-weight submodules themselves, and both inclusions are then available: section G
bounds the invariants from above, and the isospin contractions are themselves gauge
invariant and of the right mass weight, which bounds them from below.  The two meet, so
the gauge-invariant part of each mass-weight submodule up to weight eight is exactly
described.

-/

/-- A gauge-invariant term of mass weight four is a multiple of the underived isospin
  contraction. -/
lemma mem_dotSpan_of_invariant_massWeightSubmodule_four {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ massWeightSubmodule 4) (hg : ∀ g : GaugeGroupI, repGaugeGroupI g x = x) :
    x ∈ dotSpan 0 0 := by
  simpa using reducesInvariantsTo_massWeightSubmodule_four ⊥ isStableUnder_bot x
    (Submodule.mem_sup_left hx) hg

/-- A gauge-invariant term of mass weight six is a combination of the isospin contractions
  carrying one derivative, on either factor. -/
lemma mem_dotSpan_of_invariant_massWeightSubmodule_six {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ massWeightSubmodule 6) (hg : ∀ g : GaugeGroupI, repGaugeGroupI g x = x) :
    x ∈ dotSpan 1 0 ⊔ dotSpan 0 1 := by
  simpa using reducesInvariantsTo_massWeightSubmodule_six ⊥ isStableUnder_bot x
    (Submodule.mem_sup_left hx) hg

/-- A gauge-invariant term of mass weight eight is a combination of the isospin
  contractions carrying two derivatives and of the square of the underived contraction. -/
lemma mem_dotSpan_of_invariant_massWeightSubmodule_eight {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ massWeightSubmodule 8) (hg : ∀ g : GaugeGroupI, repGaugeGroupI g x = x) :
    x ∈ dotSpan 2 0 ⊔ dotSpan 0 2 ⊔ dotSpan 1 1
      ⊔ ℂ ∙ (dotGaugeHiggs ![] ![] * dotGaugeHiggs ![] ![]) := by
  simpa using reducesInvariantsTo_massWeightSubmodule_eight ⊥ isStableUnder_bot x
    (Submodule.mem_sup_left hx) hg

/-- An isospin contraction has the mass weight of its two towers together. -/
lemma dotGaugeHiggs_mem_massWeightSubmodule {n1 n2 : ℕ} (d1 : Fin n1 → (Fin 1 ⊕ Fin 3))
    (d2 : Fin n2 → (Fin 1 ⊕ Fin 3)) :
    dotGaugeHiggs d1 d2 ∈ massWeightSubmodule (2 * (1 + n1) + 2 * (1 + n2)) := by
  have hH : ∀ i, higgs d1 i ∈ massWeightSubmodule (2 * (1 + n1)) := fun i =>
    massWeightSubmodule_higgsSubmodule_le n1
      (Submodule.mem_iSup_of_mem d1 (LinearMap.mem_range_self _ _))
  have hbH : ∀ i, barHiggs d2 i ∈ massWeightSubmodule (2 * (1 + n2)) := fun i =>
    massWeightSubmodule_barHiggsSubmodule_le n2
      (Submodule.mem_iSup_of_mem d2 (LinearMap.mem_range_self _ _))
  rw [dotGaugeHiggs]
  exact add_mem (massWeightSubmodule_mul_le _ _ (Submodule.mul_mem_mul (hH 0) (hbH 0)))
    (massWeightSubmodule_mul_le _ _ (Submodule.mul_mem_mul (hH 1) (hbH 1)))

/-- The gauge invariants of mass weight four are the underived isospin contraction. -/
lemma gaugeInvariantOfMassDim_four_eq_dotSpan :
    gaugeInvariantOfMassDim 4 = dotSpan 0 0 := by
  refine le_antisymm (fun x hx =>
    mem_dotSpan_of_invariant_massWeightSubmodule_four hx.1 hx.2) ?_
  rw [dotSpan]
  refine iSup_le fun d => iSup_le fun d' =>
    (Submodule.span_singleton_le_iff_mem _ _).mpr ⟨?_, fun k =>
      rep_dotGaugeHiggs_invariant k d d'⟩
  exact dotGaugeHiggs_mem_massWeightSubmodule d d'

/-- The gauge invariants of mass weight six are the isospin contractions with one derivative
  on either factor. -/
lemma gaugeInvariantOfMassDim_six_eq_dotSpan :
    gaugeInvariantOfMassDim 6 = dotSpan 1 0 ⊔ dotSpan 0 1 := by
  refine le_antisymm (fun x hx =>
    mem_dotSpan_of_invariant_massWeightSubmodule_six hx.1 hx.2) (sup_le ?_ ?_) <;>
    rw [dotSpan] <;>
    refine iSup_le fun d => iSup_le fun d' =>
      (Submodule.span_singleton_le_iff_mem _ _).mpr ⟨?_, fun k =>
        rep_dotGaugeHiggs_invariant k d d'⟩
  · exact dotGaugeHiggs_mem_massWeightSubmodule d d'
  · exact dotGaugeHiggs_mem_massWeightSubmodule d d'

/-- The gauge invariants of mass weight eight are the isospin contractions with two
  derivatives distributed over the two factors, together with the square of the underived
  contraction — the quartic potential. -/
lemma gaugeInvariantOfMassDim_eight_eq_dotSpan :
    gaugeInvariantOfMassDim 8 = dotSpan 2 0 ⊔ dotSpan 0 2 ⊔ dotSpan 1 1
      ⊔ ℂ ∙ (dotGaugeHiggs ![] ![] * dotGaugeHiggs ![] ![]) := by
  refine le_antisymm (fun x hx =>
    mem_dotSpan_of_invariant_massWeightSubmodule_eight hx.1 hx.2)
    (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_)
  · rw [dotSpan]
    exact iSup_le fun d => iSup_le fun d' =>
      (Submodule.span_singleton_le_iff_mem _ _).mpr
        ⟨dotGaugeHiggs_mem_massWeightSubmodule d d',
          fun k => rep_dotGaugeHiggs_invariant k d d'⟩
  · rw [dotSpan]
    exact iSup_le fun d => iSup_le fun d' =>
      (Submodule.span_singleton_le_iff_mem _ _).mpr
        ⟨dotGaugeHiggs_mem_massWeightSubmodule d d',
          fun k => rep_dotGaugeHiggs_invariant k d d'⟩
  · rw [dotSpan]
    exact iSup_le fun d => iSup_le fun d' =>
      (Submodule.span_singleton_le_iff_mem _ _).mpr
        ⟨dotGaugeHiggs_mem_massWeightSubmodule d d',
          fun k => rep_dotGaugeHiggs_invariant k d d'⟩
  · refine (Submodule.span_singleton_le_iff_mem _ _).mpr ⟨?_, fun k => ?_⟩
    · exact massWeightSubmodule_mul_le 4 4 (Submodule.mul_mem_mul
        (dotGaugeHiggs_mem_massWeightSubmodule ![] ![])
        (dotGaugeHiggs_mem_massWeightSubmodule ![] ![]))
    · rw [LocalCovFieldAlgebra.repGaugeGroupI_mul, rep_dotGaugeHiggs_invariant]

end ScalarSector

end StandardModel
