/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsHiggsSector.MassWeight.Basic
public import Physlib.Particles.StandardModel.IsHiggsSector.DerivSubmodule.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2AntiFundamental
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2QuadFundamental
/-!
# The gauge weight decomposition of the Higgs mass-weight submodules

Each mass-weight submodule of the Higgs sector up to weight eight has an explicit
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
Higgs symbol is an `IsSU2FunAntiFun` family — the conjugate symbol carries the fundamental
isospin index and the Higgs symbol the anti-fundamental one, so it goes second — and the
sole invariant of `2 ⊗ 2̄`, the delta contraction, is the isospin contraction
`dotGaugeHiggs`.  The quartic is an `IsSU2QuadFundamental` family once its two Higgs
symbols are re-indexed by the antisymmetric symbol, and of its two independent
contractions one is the square of the isospin contraction and the other vanishes, pairing
commuting factors antisymmetrically.

- A. The decompositions
- B. The pieces of a derivative submodule
- C. The weight-zero pieces of the products
- D. The weight-zero pieces of the mass-weight submodules
- E. The gauge sieve
- F. The Higgs symbols as isospin families
- G. Peeling the gauge invariants off a stable submodule
- H. The gauge classification up to mass weight eight
- I. The gauge-invariant submodules up to mass weight eight

Everything from section G on is stated modulo a submodule `S` stable under the gauge
group, which is what lets the other sectors be carried along; taking `S` trivial in
section I recovers the statements about the mass-weight submodules themselves.

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz ComplexConjugate

namespace IsHiggsSector

set_option linter.unusedVariables false

variable {B : Type} [Ring B] [Algebra ℂ B]
  {rep : Representation ℂ GaugeGroupI B}
  {hrep_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B), rep g (b₁ * b₂) = rep g b₁ * rep g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {H : (n : ℕ) → (Fin n → (Fin 1 ⊕ Fin 3)) → Module.Dual ℂ HiggsVec →ₗ[ℂ] B}
  {barH : (n : ℕ) → (Fin n → (Fin 1 ⊕ Fin 3)) →
    Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsHiggsSector B rep hrep_mul repLorentz hrepLorentz_mul H barH
      massWeightPoly)

/-!

## A. The decompositions

Every term of the Higgs algebra has even mass weight, so the odd mass-weight submodules
vanish and are decomposed by the empty decomposition.  The even ones are built from the
derivative submodules by the descriptions of `MassWeight.Basic`: weight two is a single
derivative submodule, and the higher weights add the products which distribute the mass
weight over several towers.

-/

/-- The odd mass-weight submodules are trivial, so they carry the empty decomposition. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightOdd (n : ℕ) (hn : Odd n) :
    GaugeWeightDecomposition rep (h.massWeightSubmodule n) :=
  GaugeWeightDecomposition.copy (GaugeWeightDecomposition.bot h.rep_mul) _
    (h.massWeightSubmodule_odd_eq_bot n hn)

/-- Weight one is trivial. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightOne :
    GaugeWeightDecomposition rep (h.massWeightSubmodule 1) :=
  h.massWeightSubmoduleGaugeWeightOdd 1 (by decide)

/-- Weight two is the underived Higgs tower. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightTwo :
    GaugeWeightDecomposition rep (h.massWeightSubmodule 2) :=
  GaugeWeightDecomposition.copy (h.derivSubmoduleGaugeWeight 0) _
    h.massWeightSubmodule_two_eq_deriv

/-- Weight three is trivial. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightThree :
    GaugeWeightDecomposition rep (h.massWeightSubmodule 3) :=
  h.massWeightSubmoduleGaugeWeightOdd 3 (by decide)

/-- Weight four is the once-derived tower together with the products of two underived
  ones. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightFour :
    GaugeWeightDecomposition rep (h.massWeightSubmodule 4) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.sup (d := h.derivSubmoduleGaugeWeight 1)
      (d' := GaugeWeightDecomposition.mul (d := h.derivSubmoduleGaugeWeight 0)
        (d' := h.derivSubmoduleGaugeWeight 0))) _
    h.massWeightSubmodule_four_eq_deriv

/-- Weight five is trivial. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightFive :
    GaugeWeightDecomposition rep (h.massWeightSubmodule 5) :=
  h.massWeightSubmoduleGaugeWeightOdd 5 (by decide)

/-- Weight six is the twice-derived tower, the once-derived tower against an underived
  one, and the products of three underived ones. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightSix :
    GaugeWeightDecomposition rep (h.massWeightSubmodule 6) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.sup
      (d := GaugeWeightDecomposition.sup (d := h.derivSubmoduleGaugeWeight 2)
        (d' := GaugeWeightDecomposition.mul (d := h.derivSubmoduleGaugeWeight 1)
          (d' := h.derivSubmoduleGaugeWeight 0)))
      (d' := GaugeWeightDecomposition.mul
        (d := GaugeWeightDecomposition.mul (d := h.derivSubmoduleGaugeWeight 0)
          (d' := h.derivSubmoduleGaugeWeight 0))
        (d' := h.derivSubmoduleGaugeWeight 0))) _
    h.massWeightSubmodule_six_eq_deriv

/-- Weight seven is trivial. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightSeven :
    GaugeWeightDecomposition rep (h.massWeightSubmodule 7) :=
  h.massWeightSubmoduleGaugeWeightOdd 7 (by decide)

/-- Weight eight: the thrice-derived tower, the two ways of splitting the derivatives over
  two towers, the once-derived tower against two underived ones, and the products of four
  underived ones. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightEight :
    GaugeWeightDecomposition rep (h.massWeightSubmodule 8) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.sup
      (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
          (d := GaugeWeightDecomposition.sup (d := h.derivSubmoduleGaugeWeight 3)
            (d' := GaugeWeightDecomposition.mul (d := h.derivSubmoduleGaugeWeight 2)
              (d' := h.derivSubmoduleGaugeWeight 0)))
          (d' := GaugeWeightDecomposition.mul (d := h.derivSubmoduleGaugeWeight 1)
            (d' := h.derivSubmoduleGaugeWeight 1)))
        (d' := GaugeWeightDecomposition.mul
          (d := GaugeWeightDecomposition.mul (d := h.derivSubmoduleGaugeWeight 1)
            (d' := h.derivSubmoduleGaugeWeight 0))
          (d' := h.derivSubmoduleGaugeWeight 0)))
      (d' := GaugeWeightDecomposition.mul
        (d := GaugeWeightDecomposition.mul
          (d := GaugeWeightDecomposition.mul (d := h.derivSubmoduleGaugeWeight 0)
            (d' := h.derivSubmoduleGaugeWeight 0))
          (d' := h.derivSubmoduleGaugeWeight 0))
        (d' := h.derivSubmoduleGaugeWeight 0))) _
    h.massWeightSubmodule_eight_eq_deriv

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
    (h.derivSubmoduleGaugeWeight n).piece w
      = (if w = ((0, 0, -1, -3) : GaugeWeight) then
          ⨆ d : Fin n → (Fin 1 ⊕ Fin 3), ℂ ∙ h.higgs d 0
        else if w = ((0, 0, 1, -3) : GaugeWeight) then
          ⨆ d : Fin n → (Fin 1 ⊕ Fin 3), ℂ ∙ h.higgs d 1
        else ⊥)
        ⊔ (if w = ((0, 0, 1, 3) : GaugeWeight) then
            ⨆ d : Fin n → (Fin 1 ⊕ Fin 3), ℂ ∙ h.barHiggs d 0
          else if w = ((0, 0, -1, 3) : GaugeWeight) then
            ⨆ d : Fin n → (Fin 1 ⊕ Fin 3), ℂ ∙ h.barHiggs d 1
          else ⊥) := rfl

/-- The piece at the weight of the upper Higgs component. -/
lemma derivSubmoduleGaugeWeight_piece_higgs_zero (n : ℕ) :
    (h.derivSubmoduleGaugeWeight n).piece (0, 0, -1, -3)
      = ⨆ d : Fin n → (Fin 1 ⊕ Fin 3), ℂ ∙ h.higgs d 0 := by
  rw [h.derivSubmoduleGaugeWeight_piece_eq, if_pos rfl, if_neg (by decide),
    if_neg (by decide), sup_bot_eq]

/-- The piece at the weight of the lower Higgs component. -/
lemma derivSubmoduleGaugeWeight_piece_higgs_one (n : ℕ) :
    (h.derivSubmoduleGaugeWeight n).piece (0, 0, 1, -3)
      = ⨆ d : Fin n → (Fin 1 ⊕ Fin 3), ℂ ∙ h.higgs d 1 := by
  rw [h.derivSubmoduleGaugeWeight_piece_eq, if_neg (by decide), if_pos rfl,
    if_neg (by decide), if_neg (by decide), sup_bot_eq]

/-- The piece at the weight of the upper conjugate-Higgs component. -/
lemma derivSubmoduleGaugeWeight_piece_barHiggs_zero (n : ℕ) :
    (h.derivSubmoduleGaugeWeight n).piece (0, 0, 1, 3)
      = ⨆ d : Fin n → (Fin 1 ⊕ Fin 3), ℂ ∙ h.barHiggs d 0 := by
  rw [h.derivSubmoduleGaugeWeight_piece_eq, if_neg (by decide), if_neg (by decide),
    if_pos rfl, bot_sup_eq]

/-- The piece at the weight of the lower conjugate-Higgs component. -/
lemma derivSubmoduleGaugeWeight_piece_barHiggs_one (n : ℕ) :
    (h.derivSubmoduleGaugeWeight n).piece (0, 0, -1, 3)
      = ⨆ d : Fin n → (Fin 1 ⊕ Fin 3), ℂ ∙ h.barHiggs d 1 := by
  rw [h.derivSubmoduleGaugeWeight_piece_eq, if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos rfl, bot_sup_eq]

/-- A derivative submodule has no weight-zero content: every Higgs symbol carries
  hypercharge. -/
lemma derivSubmoduleGaugeWeight_piece_zero (n : ℕ) :
    (h.derivSubmoduleGaugeWeight n).piece 0 = ⊥ :=
  (h.derivSubmoduleGaugeWeight n).piece_eq_zero_of_not_mem_supp 0
    (by rw [h.derivSubmoduleGaugeWeight_supp]; decide)

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
noncomputable def higgsBarHiggsSpan (h : IsHiggsSector B rep hrep_mul repLorentz
      hrepLorentz_mul H barH massWeightPoly) (n m : ℕ) (i : Fin 2) : Submodule ℂ B :=
  ⨆ (d : Fin n → (Fin 1 ⊕ Fin 3)) (d' : Fin m → (Fin 1 ⊕ Fin 3)),
    ℂ ∙ (h.higgs d i * h.barHiggs d' i)

/-- The span of the underived quartic monomial pairing the isospin components `i` and
  `j`. -/
noncomputable def quarticSpan (h : IsHiggsSector B rep hrep_mul repLorentz
      hrepLorentz_mul H barH massWeightPoly) (i j : Fin 2) : Submodule ℂ B :=
  ℂ ∙ (h.higgs ![] i * h.barHiggs ![] i * h.higgs ![] j * h.barHiggs ![] j)

/-- The weight-zero piece of a product of two derivative submodules: the isospin-diagonal
  pairings, taken in both orders of the two towers. -/
lemma derivSubmodule_mul_piece_zero (n m : ℕ) :
    GaugeWeightDecomposition.piece rep (h.derivSubmodule n * h.derivSubmodule m) 0
      = h.higgsBarHiggsSpan n m 0 ⊔ h.higgsBarHiggsSpan n m 1
        ⊔ h.higgsBarHiggsSpan m n 0 ⊔ h.higgsBarHiggsSpan m n 1 := by
  rw [GaugeWeightDecomposition.mul_piece_eq_sub 0, h.derivSubmoduleGaugeWeight_supp n]
  simp only [Finset.iSup_insert, Finset.iSup_singleton,
    show (0 : GaugeWeight) - (0, 0, -1, -3) = (0, 0, 1, 3) from by decide,
    show (0 : GaugeWeight) - (0, 0, 1, -3) = (0, 0, -1, 3) from by decide,
    show (0 : GaugeWeight) - (0, 0, 1, 3) = (0, 0, -1, -3) from by decide,
    show (0 : GaugeWeight) - (0, 0, -1, 3) = (0, 0, 1, -3) from by decide,
    h.derivSubmoduleGaugeWeight_piece_higgs_zero,
    h.derivSubmoduleGaugeWeight_piece_higgs_one,
    h.derivSubmoduleGaugeWeight_piece_barHiggs_zero,
    h.derivSubmoduleGaugeWeight_piece_barHiggs_one]
  have hcomm : ∀ {n1 n2 : ℕ} (d1 : Fin n1 → (Fin 1 ⊕ Fin 3)) (d2 : Fin n2 → (Fin 1 ⊕ Fin 3))
      (a b : Fin 2), h.barHiggs d1 a * h.higgs d2 b = h.higgs d2 b * h.barHiggs d1 a :=
    fun d1 d2 a b => ((h.H_comm_barH _ _ _ _ _ _).symm).eq
  simp only [Submodule.iSup_mul, Submodule.mul_iSup, Submodule.span_mul_span,
    Set.singleton_mul_singleton, hcomm]
  simp only [higgsBarHiggsSpan, sup_assoc]
  refine congrArg₂ (· ⊔ ·) iSup_comm (congrArg₂ (· ⊔ ·) iSup_comm rfl)

/-- A product of three derivative submodules has no weight-zero content: the hypercharge of
  three Higgs generators is an odd multiple of three. -/
lemma derivSubmodule_mul_mul_piece_zero (n m k : ℕ) :
    GaugeWeightDecomposition.piece rep
      (h.derivSubmodule n * h.derivSubmodule m * h.derivSubmodule k) 0 = ⊥ := by
  refine GaugeWeightDecomposition.piece_eq_zero_of_not_mem_supp _ 0 ?_
  rw [GaugeWeightDecomposition.mul_supp, GaugeWeightDecomposition.mul_supp,
    h.derivSubmoduleGaugeWeight_supp n, h.derivSubmoduleGaugeWeight_supp m,
    h.derivSubmoduleGaugeWeight_supp k]
  decide

set_option maxHeartbeats 1000000 in
/-- The weight-zero piece of the product of four underived derivative submodules: the three
  quartic monomials, the ones pairing two Higgs symbols against two conjugate ones with
  matching isospin. -/
lemma derivSubmodule_zero_pow_four_piece_zero :
    GaugeWeightDecomposition.piece rep
      (h.derivSubmodule 0 * h.derivSubmodule 0 * h.derivSubmodule 0
        * h.derivSubmodule 0) 0
      = h.quarticSpan 0 0 ⊔ h.quarticSpan 0 1 ⊔ h.quarticSpan 1 1 := by
  have hbh : ∀ (a b : Fin 2),
      h.barHiggs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) a * h.higgs ![] b
        = h.higgs ![] b * h.barHiggs ![] a := fun a b => (h.H_comm_barH _ _ _ _ _ _).symm.eq
  have hbh' : ∀ (a b : Fin 2) (y : B),
      h.barHiggs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) a * (h.higgs ![] b * y)
        = h.higgs ![] b * (h.barHiggs ![] a * y) := fun a b y => by
    rw [← mul_assoc, hbh, mul_assoc]
  have hhh : h.higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 1 * h.higgs ![] 0
      = h.higgs ![] 0 * h.higgs ![] 1 := (h.H_comm_H _ _ _ _ _ _).eq
  have hhh' : ∀ y : B, h.higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 1 * (h.higgs ![] 0 * y)
      = h.higgs ![] 0 * (h.higgs ![] 1 * y) := fun y => by rw [← mul_assoc, hhh, mul_assoc]
  have hbb : h.barHiggs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 1 * h.barHiggs ![] 0
      = h.barHiggs ![] 0 * h.barHiggs ![] 1 := (h.barH_comm_barH _ _ _ _ _ _).eq
  simp +decide only [GaugeWeightDecomposition.mul_piece_eq_sub',
    h.derivSubmoduleGaugeWeight_supp 0, Finset.iSup_insert, Finset.iSup_singleton,
    h.derivSubmoduleGaugeWeight_piece_eq, if_true, if_false, bot_sup_eq, sup_bot_eq,
    Submodule.bot_mul]
  simp only [Matrix.empty_eq, ciSup_unique, quarticSpan, Submodule.sup_mul,
    Submodule.span_mul_span, Set.singleton_mul_singleton, mul_assoc, hbh, hbh', hhh,
    hhh', hbb]
  generalize (ℂ ∙ (h.higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 0 *
    (h.higgs ![] 0 * (h.barHiggs ![] 0 * h.barHiggs ![] 0)))) = A
  generalize (ℂ ∙ (h.higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 0 *
    (h.higgs ![] 1 * (h.barHiggs ![] 0 * h.barHiggs ![] 1)))) = C
  generalize (ℂ ∙ (h.higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 1 *
    (h.higgs ![] 1 * (h.barHiggs ![] 1 * h.barHiggs ![] 1)))) = D
  simp only [sup_comm, sup_left_comm, sup_idem, sup_left_idem]

/-!

## D. The weight-zero pieces of the mass-weight submodules

Assembling section C along the descriptions of section A gives the weight-zero piece of
each mass-weight submodule up to weight eight.  The odd weights and weight two are trivial,
weight four is the underived pairing, weight six adds the pairings with one derivative on
either factor, and weight eight adds the pairings with two derivatives, those with one
derivative on each factor, and the three quartic monomials.

-/

/-- The weight-zero piece at an odd mass weight: the submodule itself is trivial. -/
lemma massWeightSubmoduleGaugeWeightOdd_piece_zero (n : ℕ) (hn : Odd n) :
    (h.massWeightSubmoduleGaugeWeightOdd n hn).piece 0 = ⊥ := rfl

/-- The weight-zero piece at mass weight two: a single Higgs symbol carries
  hypercharge. -/
lemma massWeightSubmoduleGaugeWeightTwo_piece_zero :
    (h.massWeightSubmoduleGaugeWeightTwo).piece 0 = ⊥ :=
  h.derivSubmoduleGaugeWeight_piece_zero 0

/-- The weight-zero piece at mass weight four: the underived isospin-diagonal pairings. -/
lemma massWeightSubmoduleGaugeWeightFour_piece_zero :
    (h.massWeightSubmoduleGaugeWeightFour).piece 0
      = h.higgsBarHiggsSpan 0 0 0 ⊔ h.higgsBarHiggsSpan 0 0 1 := by
  show (h.derivSubmoduleGaugeWeight 1).piece 0
      ⊔ GaugeWeightDecomposition.piece rep (h.derivSubmodule 0 * h.derivSubmodule 0) 0 = _
  rw [h.derivSubmoduleGaugeWeight_piece_zero 1, h.derivSubmodule_mul_piece_zero 0 0,
    bot_sup_eq]
  simp only [sup_comm, sup_left_comm, sup_idem, sup_left_idem]

/-- The weight-zero piece at mass weight six: the isospin-diagonal pairings carrying one
  derivative, on either of the two factors. -/
lemma massWeightSubmoduleGaugeWeightSix_piece_zero :
    (h.massWeightSubmoduleGaugeWeightSix).piece 0
      = h.higgsBarHiggsSpan 1 0 0 ⊔ h.higgsBarHiggsSpan 1 0 1
        ⊔ h.higgsBarHiggsSpan 0 1 0 ⊔ h.higgsBarHiggsSpan 0 1 1 := by
  show ((h.derivSubmoduleGaugeWeight 2).piece 0
      ⊔ GaugeWeightDecomposition.piece rep (h.derivSubmodule 1 * h.derivSubmodule 0) 0)
      ⊔ GaugeWeightDecomposition.piece rep
        (h.derivSubmodule 0 * h.derivSubmodule 0 * h.derivSubmodule 0) 0 = _
  rw [h.derivSubmoduleGaugeWeight_piece_zero 2, h.derivSubmodule_mul_piece_zero 1 0,
    h.derivSubmodule_mul_mul_piece_zero 0 0 0, bot_sup_eq, sup_bot_eq]

/-- The weight-zero piece at mass weight eight: the isospin-diagonal pairings carrying two
  derivatives on one factor or one on each, together with the three quartic monomials. -/
lemma massWeightSubmoduleGaugeWeightEight_piece_zero :
    (h.massWeightSubmoduleGaugeWeightEight).piece 0
      = h.higgsBarHiggsSpan 2 0 0 ⊔ h.higgsBarHiggsSpan 2 0 1
        ⊔ h.higgsBarHiggsSpan 0 2 0 ⊔ h.higgsBarHiggsSpan 0 2 1
        ⊔ (h.higgsBarHiggsSpan 1 1 0 ⊔ h.higgsBarHiggsSpan 1 1 1)
        ⊔ (h.quarticSpan 0 0 ⊔ h.quarticSpan 0 1 ⊔ h.quarticSpan 1 1) := by
  show ((((h.derivSubmoduleGaugeWeight 3).piece 0
        ⊔ GaugeWeightDecomposition.piece rep
          (h.derivSubmodule 2 * h.derivSubmodule 0) 0)
      ⊔ GaugeWeightDecomposition.piece rep (h.derivSubmodule 1 * h.derivSubmodule 1) 0)
      ⊔ GaugeWeightDecomposition.piece rep
        (h.derivSubmodule 1 * h.derivSubmodule 0 * h.derivSubmodule 0) 0)
      ⊔ GaugeWeightDecomposition.piece rep
        (h.derivSubmodule 0 * h.derivSubmodule 0 * h.derivSubmodule 0
          * h.derivSubmodule 0) 0 = _
  rw [h.derivSubmoduleGaugeWeight_piece_zero 3, h.derivSubmodule_mul_piece_zero 2 0,
    h.derivSubmodule_mul_piece_zero 1 1, h.derivSubmodule_mul_mul_piece_zero 1 0 0,
    h.derivSubmodule_zero_pow_four_piece_zero, bot_sup_eq, sup_bot_eq]
  simp only [sup_assoc, sup_comm, sup_left_comm, sup_idem, sup_left_idem]

/-!

## E. The gauge sieve

A gauge-invariant element is fixed by the gauge torus, so it sits in the weight-zero piece
of any decomposition of a submodule containing it.  Section D therefore bounds the
invariants of each mass-weight submodule up to weight eight.  The bound is a sieve, not a
characterisation: the gauge torus cannot separate the isospin singlet from the neutral
component of the isospin triplet, and that separation needs the Weyl element of `SU(2)`.

-/

/-- A gauge-invariant term of odd mass weight vanishes. -/
lemma eq_zero_of_invariant_massWeightSubmodule_odd (n : ℕ) (hn : Odd n) {x : B}
    (hx : x ∈ h.massWeightSubmodule n) : x = 0 :=
  Submodule.mem_bot ℂ |>.mp (h.massWeightSubmodule_odd_eq_bot n hn ▸ hx)

/-- A gauge-invariant term of mass weight two vanishes: a single Higgs symbol carries
  hypercharge, so nothing at that weight is neutral. -/
lemma eq_zero_of_invariant_massWeightSubmodule_two {x : B}
    (hx : x ∈ h.massWeightSubmodule 2) (hg : ∀ g : GaugeGroupI, rep g x = x) : x = 0 := by
  have hmem := GaugeWeightDecomposition.mem_zero_of_invariant
    h.massWeightSubmoduleGaugeWeightTwo hx hg
  rwa [h.massWeightSubmoduleGaugeWeightTwo_piece_zero, Submodule.mem_bot] at hmem

/-- A gauge-invariant term of mass weight four is a combination of the two underived
  isospin-diagonal pairings. -/
lemma mem_of_invariant_massWeightSubmodule_four {x : B}
    (hx : x ∈ h.massWeightSubmodule 4) (hg : ∀ g : GaugeGroupI, rep g x = x) :
    x ∈ h.higgsBarHiggsSpan 0 0 0 ⊔ h.higgsBarHiggsSpan 0 0 1 := by
  rw [← h.massWeightSubmoduleGaugeWeightFour_piece_zero]
  exact GaugeWeightDecomposition.mem_zero_of_invariant _ hx hg

/-- A gauge-invariant term of mass weight six is a combination of the isospin-diagonal
  pairings carrying one derivative, on either factor. -/
lemma mem_of_invariant_massWeightSubmodule_six {x : B}
    (hx : x ∈ h.massWeightSubmodule 6) (hg : ∀ g : GaugeGroupI, rep g x = x) :
    x ∈ h.higgsBarHiggsSpan 1 0 0 ⊔ h.higgsBarHiggsSpan 1 0 1
      ⊔ h.higgsBarHiggsSpan 0 1 0 ⊔ h.higgsBarHiggsSpan 0 1 1 := by
  rw [← h.massWeightSubmoduleGaugeWeightSix_piece_zero]
  exact GaugeWeightDecomposition.mem_zero_of_invariant _ hx hg

/-- A gauge-invariant term of mass weight eight is a combination of the isospin-diagonal
  pairings carrying two derivatives and of the three quartic monomials. -/
lemma mem_of_invariant_massWeightSubmodule_eight {x : B}
    (hx : x ∈ h.massWeightSubmodule 8) (hg : ∀ g : GaugeGroupI, rep g x = x) :
    x ∈ h.higgsBarHiggsSpan 2 0 0 ⊔ h.higgsBarHiggsSpan 2 0 1
      ⊔ h.higgsBarHiggsSpan 0 2 0 ⊔ h.higgsBarHiggsSpan 0 2 1
      ⊔ (h.higgsBarHiggsSpan 1 1 0 ⊔ h.higgsBarHiggsSpan 1 1 1)
      ⊔ (h.quarticSpan 0 0 ⊔ h.quarticSpan 0 1 ⊔ h.quarticSpan 1 1) := by
  rw [← h.massWeightSubmoduleGaugeWeightEight_piece_zero]
  exact GaugeWeightDecomposition.mem_zero_of_invariant _ hx hg

/-!

## F. The Higgs symbols as isospin families

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
`fun l => h.barHiggs d' (l 0) * h.higgs d (l 1)`, conjugate symbol first, which is an
`IsSU2FunAntiFun` family; and its delta contraction, the sole invariant of `2 ⊗ 2̄`, is the
isospin contraction `dotGaugeHiggs`.  That identification is the whole point of the
section: `dotSpan` is the span of delta contractions, and nothing else survives.

The quartic needs four fundamental indices, so its two Higgs symbols must be re-indexed by
the antisymmetric symbol first.  `tildeHiggs` is that re-index, `H̃⁰ = H¹` and
`H̃¹ = -H⁰`, and it is fundamental because `SU(2)` is pseudo-real.  The quartic family is
then a product of four fundamental families, and `IsSU2QuadFundamental` classifies it.  Its
two independent contractions come out as the square of the isospin contraction and zero:
the second pairs the two conjugate symbols with each other and the two Higgs symbols with
each other, and an antisymmetric contraction of two commuting factors vanishes.

-/

/-- The entries of the inverse of an `SU(2)` element are the conjugated transposed
  entries, the inverse of a unitary matrix being its conjugate transpose. -/
lemma su2_inv_apply (V : specialUnitaryGroup (Fin 2) ℂ) (a b : Fin 2) :
    (V⁻¹).1 a b = conj (V.1 b a) := by
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
  simp [Matrix.star_apply]

include h in
/-- An isospin transformation moves the isospin index of a Higgs symbol by the conjugate
  matrix: the index of a Higgs symbol is anti-fundamental. -/
lemma rep_su2_higgs (V : specialUnitaryGroup (Fin 2) ℂ) {n : ℕ}
    (d : Fin n → (Fin 1 ⊕ Fin 3)) (i : Fin 2) :
    rep ((1, V, 1) : GaugeGroupI) (h.higgs d i)
      = ∑ a, conj (V.1 a i) • h.higgs d a := by
  rw [h.rep_higgsComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show ((1, V, 1) : GaugeGroupI)⁻¹ = ((1, V⁻¹, 1) : GaugeGroupI) from by simp,
    show GaugeGroupI.toSU2 ((1, V⁻¹, 1) : GaugeGroupI) = V⁻¹ from rfl,
    show GaugeGroupI.toU1 ((1, V⁻¹, 1) : GaugeGroupI) = 1 from rfl, su2_inv_apply]
  simp

include h in
/-- An isospin transformation moves the isospin index of a conjugate Higgs symbol by the
  matrix itself: the index of a conjugate Higgs symbol is fundamental. -/
lemma rep_su2_barHiggs (V : specialUnitaryGroup (Fin 2) ℂ) {n : ℕ}
    (d : Fin n → (Fin 1 ⊕ Fin 3)) (i : Fin 2) :
    rep ((1, V, 1) : GaugeGroupI) (h.barHiggs d i)
      = ∑ a, V.1 a i • h.barHiggs d a := by
  rw [h.rep_barHiggsComponent]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show ((1, V, 1) : GaugeGroupI)⁻¹ = ((1, V⁻¹, 1) : GaugeGroupI) from by simp,
    show GaugeGroupI.toSU2 ((1, V⁻¹, 1) : GaugeGroupI) = V⁻¹ from rfl,
    show GaugeGroupI.toU1 ((1, V⁻¹, 1) : GaugeGroupI) = 1 from rfl, su2_inv_apply]
  simp

include h in
/-- A product of two symbols each moving by given coefficients moves by the product of
  those coefficients. -/
lemma rep_mul_pair (g : GaugeGroupI) {ι κ : Type} [Fintype ι] [Fintype κ]
    {X : ι → B} {Y : κ → B} {x₀ : ι} {y₀ : κ} {cX : ι → ℂ} {cY : κ → ℂ}
    (hX : rep g (X x₀) = ∑ x, cX x • X x) (hY : rep g (Y y₀) = ∑ y, cY y • Y y) :
    rep g (X x₀ * Y y₀) = ∑ x, ∑ y, (cX x * cY y) • (X x * Y y) := by
  rw [h.rep_mul, hX, hY, Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_smul_comm]

include h in
/-- A Higgs symbol commutes with a conjugate Higgs symbol, in the components. -/
lemma higgs_mul_barHiggs_comm {n m : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3))
    (d' : Fin m → (Fin 1 ⊕ Fin 3)) (i j : Fin 2) :
    h.higgs d i * h.barHiggs d' j = h.barHiggs d' j * h.higgs d i :=
  (h.H_comm_barH _ _ _ _ _ _).eq

include h in
/-- Two Higgs symbols commute, in the components. -/
lemma higgs_mul_higgs_comm {n m : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3))
    (d' : Fin m → (Fin 1 ⊕ Fin 3)) (i j : Fin 2) :
    h.higgs d i * h.higgs d' j = h.higgs d' j * h.higgs d i :=
  (h.H_comm_H _ _ _ _ _ _).eq

include h in
/-- Two conjugate Higgs symbols commute, in the components. -/
lemma barHiggs_mul_barHiggs_comm {n m : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3))
    (d' : Fin m → (Fin 1 ⊕ Fin 3)) (i j : Fin 2) :
    h.barHiggs d i * h.barHiggs d' j = h.barHiggs d' j * h.barHiggs d i :=
  (h.barH_comm_barH _ _ _ _ _ _).eq

/-- The isospin family of a Higgs tower carrying `n` derivatives against a conjugate tower
  carrying `m`: the conjugate symbol supplies the fundamental index and so goes in the
  first slot, the Higgs symbol the anti-fundamental one. -/
noncomputable def isoFamily (h : IsHiggsSector B rep hrep_mul repLorentz
      hrepLorentz_mul H barH massWeightPoly) {n m : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3))
    (d' : Fin m → (Fin 1 ⊕ Fin 3)) : (Fin 2 → Fin 2) → B :=
  fun l => h.barHiggs d' (l 0) * h.higgs d (l 1)

include h in
/-- The isospin family carries one fundamental and one anti-fundamental isospin index. -/
lemma isSU2FunAntiFun_isoFamily {n m : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3))
    (d' : Fin m → (Fin 1 ⊕ Fin 3)) : IsSU2FunAntiFun B rep (h.isoFamily d d') where
  repGauge_T V l := by
    rw [isoFamily, h.rep_mul_pair (1, V, 1) (h.rep_su2_barHiggs V d' (l 0))
      (h.rep_su2_higgs V d (l 1)), IsSU2BiFundamental.sum_pi_two]
    simp only [isoFamily, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The delta contraction of the isospin family is the isospin contraction: the sole
  invariant of `2 ⊗ 2̄` is the Higgs mass term of the two towers. -/
lemma deltaContraction_isoFamily {n m : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3))
    (d' : Fin m → (Fin 1 ⊕ Fin 3)) :
    IsSU2FunAntiFun.deltaContraction (h.isoFamily d d') = h.dotGaugeHiggs d d' := by
  rw [IsSU2FunAntiFun.deltaContraction, dotGaugeHiggs, isoFamily, isoFamily]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h.higgs_mul_barHiggs_comm d d' 0 0, h.higgs_mul_barHiggs_comm d d' 1 1]

/-- The span of the isospin contractions of a Higgs tower carrying `n` derivatives against
  a conjugate tower carrying `m`: the gauge invariants the isospin classification leaves
  at those two derivative orders. -/
noncomputable def dotSpan (h : IsHiggsSector B rep hrep_mul repLorentz
      hrepLorentz_mul H barH massWeightPoly) (n m : ℕ) : Submodule ℂ B :=
  ⨆ (d : Fin n → (Fin 1 ⊕ Fin 3)) (d' : Fin m → (Fin 1 ⊕ Fin 3)), ℂ ∙ h.dotGaugeHiggs d d'

include h in
/-- The span of the isospin family is stable under the whole gauge group: each factor of a
  component goes to a combination of the factors of components. -/
lemma isoFamily_span_stable {n m : ℕ} (d : Fin n → (Fin 1 ⊕ Fin 3))
    (d' : Fin m → (Fin 1 ⊕ Fin 3)) (g : GaugeGroupI) {y : B}
    (hy : y ∈ IsSU2BiFundamental.span (h.isoFamily d d')) :
    rep g y ∈ IsSU2BiFundamental.span (h.isoFamily d d') := by
  obtain ⟨c, rfl⟩ := (IsSU2BiFundamental.mem_span_iff y).1 hy
  rw [map_sum]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [map_smul, isoFamily, h.rep_mul_pair g (X := fun a => h.barHiggs d' a)
    (Y := fun a => h.higgs d a) (h.rep_barHiggsComponent g d' (l 0))
    (h.rep_higgsComponent g d (l 1))]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ =>
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.mem_iSup_of_mem ![a, b] (Submodule.mem_span_singleton_self _)

/-- The isospin-diagonal pairing spans of section C sit inside the span of the isospin
  family: a diagonal pairing is one of the four components, the two factors commuting. -/
lemma higgsBarHiggsSpan_le_isoFamily_span (n m : ℕ) :
    h.higgsBarHiggsSpan n m 0 ⊔ h.higgsBarHiggsSpan n m 1
      ≤ ⨆ (d : Fin n → (Fin 1 ⊕ Fin 3)) (d' : Fin m → (Fin 1 ⊕ Fin 3)),
        IsSU2BiFundamental.span (h.isoFamily d d') := by
  have key : ∀ (i : Fin 2), h.higgsBarHiggsSpan n m i
      ≤ ⨆ (d : Fin n → (Fin 1 ⊕ Fin 3)) (d' : Fin m → (Fin 1 ⊕ Fin 3)),
        IsSU2BiFundamental.span (h.isoFamily d d') := by
    intro i
    rw [higgsBarHiggsSpan]
    refine iSup_le fun d => iSup_le fun d' => ?_
    rw [Submodule.span_singleton_le_iff_mem]
    refine Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem d' ?_)
    rw [h.higgs_mul_barHiggs_comm d d' i i]
    exact Submodule.mem_iSup_of_mem ![i, i] (Submodule.mem_span_singleton_self _)
  exact sup_le (key 0) (key 1)

/-- The re-index of an underived Higgs symbol by the antisymmetric symbol, `H̃⁰ = H¹` and
  `H̃¹ = -H⁰`.  `SU(2)` is pseudo-real, so this turns the anti-fundamental index of a Higgs
  symbol into a fundamental one, which is what the quartic family needs. -/
noncomputable def tildeHiggs (h : IsHiggsSector B rep hrep_mul repLorentz
      hrepLorentz_mul H barH massWeightPoly) (i : Fin 2) : B :=
  ∑ m : Fin 2, IsSU2BiFundamental.epsilon i m • h.higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) m

/-- The re-index at isospin zero is the Higgs symbol of isospin one. -/
@[simp] lemma tildeHiggs_zero :
    h.tildeHiggs 0 = h.higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 1 := by
  simp [tildeHiggs, Fin.sum_univ_two]

/-- The re-index at isospin one is minus the Higgs symbol of isospin zero. -/
@[simp] lemma tildeHiggs_one :
    h.tildeHiggs 1 = -h.higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 0 := by
  simp [tildeHiggs, Fin.sum_univ_two]

include h in
/-- The re-indexed Higgs symbol carries a fundamental isospin index: the four entry
  identities of `IsSU2BiFundamental` remove every complex conjugate. -/
lemma rep_su2_tildeHiggs (V : specialUnitaryGroup (Fin 2) ℂ) (i : Fin 2) :
    rep ((1, V, 1) : GaugeGroupI) (h.tildeHiggs i)
      = ∑ a, V.1 a i • h.tildeHiggs a := by
  have hi : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  rcases hi i with rfl | rfl
  · rw [tildeHiggs_zero, h.rep_su2_higgs, Fin.sum_univ_two, Fin.sum_univ_two,
      tildeHiggs_zero, tildeHiggs_one]
    simp only [IsSU2BiFundamental.conj_apply_zero_one,
      IsSU2BiFundamental.conj_apply_one_one]
    module
  · rw [tildeHiggs_one, map_neg, h.rep_su2_higgs, Fin.sum_univ_two, Fin.sum_univ_two,
      tildeHiggs_zero, tildeHiggs_one]
    simp only [IsSU2BiFundamental.conj_apply_zero_zero,
      IsSU2BiFundamental.conj_apply_one_zero]
    module

/-- The quartic isospin family: two conjugate Higgs symbols against two re-indexed Higgs
  symbols, each of the four carrying a fundamental isospin index. -/
noncomputable def quadFamily (h : IsHiggsSector B rep hrep_mul repLorentz
      hrepLorentz_mul H barH massWeightPoly) : (Fin 4 → Fin 2) → B :=
  fun l => h.barHiggs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) (l 0)
    * (h.tildeHiggs (l 1)
      * (h.barHiggs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) (l 2) * h.tildeHiggs (l 3)))

include h in
/-- The quartic family carries four fundamental isospin indices. -/
lemma isSU2QuadFundamental_quadFamily : IsSU2QuadFundamental B rep h.quadFamily where
  repGauge_T V l := by
    simp only [quadFamily]
    rw [h.rep_mul, h.rep_mul, h.rep_mul, h.rep_su2_barHiggs V ![] (l 0),
      h.rep_su2_tildeHiggs V (l 1), h.rep_su2_barHiggs V ![] (l 2),
      h.rep_su2_tildeHiggs V (l 3), IsSU2QuadFundamental.sum_pi_four]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    simp only [smul_mul_smul_comm, Fin.prod_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three, mul_assoc]

section Quartic

/-- Moving a Higgs symbol past a conjugate one, at no derivatives and inside a product:
  the normalisation used to compare quartic monomials. -/
private lemma barHiggs_higgs_left_comm_zero (i j : Fin 2) (y : B) :
    h.barHiggs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) i * (h.higgs ![] j * y)
      = h.higgs ![] j * (h.barHiggs ![] i * y) := by
  rw [← mul_assoc, ← h.higgs_mul_barHiggs_comm ![] ![] j i, mul_assoc]

/-- Moving a Higgs symbol past a conjugate one, at no derivatives. -/
private lemma barHiggs_mul_higgs_comm_zero (i j : Fin 2) :
    h.barHiggs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) i * h.higgs ![] j
      = h.higgs ![] j * h.barHiggs ![] i :=
  (h.higgs_mul_barHiggs_comm ![] ![] j i).symm

/-- Sorting two Higgs symbols inside a product. -/
private lemma higgs_left_comm_zero (y : B) :
    h.higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 1 * (h.higgs ![] 0 * y)
      = h.higgs ![] 0 * (h.higgs ![] 1 * y) := by
  rw [← mul_assoc, h.higgs_mul_higgs_comm ![] ![] 1 0, mul_assoc]

/-- The first epsilon contraction of the quartic family is the square of the isospin
  contraction: pairing the first conjugate symbol with the first Higgs symbol, and the
  second with the second, is pairing each `H̄` with an `H`. -/
lemma epsilonContraction₁₂_quadFamily :
    IsSU2QuadFundamental.epsilonContraction₁₂ h.quadFamily
      = h.dotGaugeHiggs ![] ![] * h.dotGaugeHiggs ![] ![] := by
  simp only [IsSU2QuadFundamental.epsilonContraction₁₂, quadFamily, dotGaugeHiggs,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, tildeHiggs_zero, tildeHiggs_one, neg_mul,
    mul_neg, neg_neg, add_mul, mul_add, mul_assoc, h.barHiggs_higgs_left_comm_zero,
    h.barHiggs_mul_higgs_comm_zero, h.higgs_left_comm_zero,
    h.barHiggs_mul_barHiggs_comm ![] ![] 1 0]
  abel

/-- The second epsilon contraction of the quartic family vanishes: it pairs the two
  conjugate symbols with each other and the two Higgs symbols with each other, and an
  antisymmetric contraction of two commuting factors is zero. -/
lemma epsilonContraction₁₃_quadFamily :
    IsSU2QuadFundamental.epsilonContraction₁₃ h.quadFamily = 0 := by
  simp only [IsSU2QuadFundamental.epsilonContraction₁₃, quadFamily, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_three, tildeHiggs_zero, tildeHiggs_one, neg_mul, mul_neg,
    h.barHiggs_higgs_left_comm_zero, h.barHiggs_mul_higgs_comm_zero,
    h.higgs_left_comm_zero, h.barHiggs_mul_barHiggs_comm ![] ![] 1 0]
  abel

/-- The three quartic monomials of section C lie in the span of the components of the
  quartic family, each being one of those components up to a sign. -/
lemma quarticSpan_le_quadFamily_span :
    h.quarticSpan 0 0 ⊔ h.quarticSpan 0 1 ⊔ h.quarticSpan 1 1
      ≤ IsSU2QuadFundamental.span h.quadFamily := by
  refine sup_le (sup_le ?_ ?_) ?_ <;>
    rw [quarticSpan, Submodule.span_singleton_le_iff_mem]
  · rw [show h.higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 0 * h.barHiggs ![] 0 * h.higgs ![] 0
        * h.barHiggs ![] 0 = h.quadFamily ![0, 1, 0, 1] from by
      simp only [quadFamily, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, tildeHiggs_one,
        neg_mul, mul_neg, neg_neg, mul_assoc, h.barHiggs_higgs_left_comm_zero,
        h.barHiggs_mul_higgs_comm_zero]]
    exact IsSU2QuadFundamental.mem_span _
  · rw [show h.higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 0 * h.barHiggs ![] 0 * h.higgs ![] 1
        * h.barHiggs ![] 1 = -h.quadFamily ![0, 1, 1, 0] from by
      simp only [quadFamily, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, tildeHiggs_zero,
        tildeHiggs_one, neg_mul, mul_neg, neg_neg, mul_assoc,
        h.barHiggs_higgs_left_comm_zero, h.barHiggs_mul_higgs_comm_zero]]
    exact neg_mem (IsSU2QuadFundamental.mem_span _)
  · rw [show h.higgs (![] : Fin 0 → (Fin 1 ⊕ Fin 3)) 1 * h.barHiggs ![] 1 * h.higgs ![] 1
        * h.barHiggs ![] 1 = h.quadFamily ![1, 0, 1, 0] from by
      simp only [quadFamily, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, tildeHiggs_zero,
        mul_assoc, h.barHiggs_higgs_left_comm_zero, h.barHiggs_mul_higgs_comm_zero]]
    exact IsSU2QuadFundamental.mem_span _

end Quartic

/-!

## G. Peeling the gauge invariants off a stable submodule

The classification is wanted not for the mass-weight submodule alone but modulo a
submodule `S` gathering the other sectors, so every step has to run for `x` in
`M ⊔ S` rather than `x` in `M`.  Two things are needed for that.

The first is that a gauge invariant of `V ⊔ S` still lies in the weight-zero piece of `V`
joined with `S`.  The weight-eight part of such an element need not itself be invariant, so
nothing places it in the weight-zero piece directly; what does is that every non-zero
weight is seen by one of the four torus generators, which scales that part and fixes
nothing else, so the part can be removed one weight at a time.

The second is the peeling itself.  The weight-zero piece is a finite join of isospin family
spans, and `IsSU2FunAntiFun.mem_span_sup_invariant_iff` removes one span at a time,
each time with the spans not yet removed adjoined to `S`.  That is why the spans have to be
gauge stable, which is `isoFamily_span_stable`, and why the enlargement is `isoSpan` rather
than the pairing span of section C: the pairing span keeps only the diagonal components and
a gauge transformation does not.

-/

/-- The one-weight-at-a-time refinement, with the separating torus generator chosen per
  weight.  Let `S` be closed under the four torus generators and let `s` be a finite set of
  non-zero gauge weights, each seen by some generator.  Then a gauge-invariant element of
  the join of the weight-`w` pieces for `w ∈ s` with `S` already lies in `S`. -/
lemma mem_of_invariant_of_mem_biSup_piece_sup_of_ne_zero {V S : Submodule ℂ B}
    (dV : GaugeWeightDecomposition rep V)
    (hS : ∀ (i : Fin 4) (y : B), y ∈ S → rep (gaugeTorusGen i) y ∈ S) :
    ∀ (s : Finset GaugeWeight), (∀ w ∈ s, ∃ i, w.coord i ≠ 0) →
      ∀ x ∈ (⨆ w ∈ s, dV.piece w) ⊔ S, (∀ g : GaugeGroupI, rep g x = x) → x ∈ S := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ x hx _
    simpa using hx
  | @insert w₀ s' hw₀ ih =>
    intro hs x hx hinv
    obtain ⟨i, hi⟩ := hs w₀ (Finset.mem_insert_self w₀ s')
    rw [Finset.iSup_insert, sup_assoc] at hx
    obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    have hc1 : ((expI : ℂ) ^ w₀.coord i) ≠ 1 := by
      intro hcc
      exact hi (expI_zpow_injective
        (show (expI : ℂ) ^ w₀.coord i = (expI : ℂ) ^ (0 : ℤ) by rw [zpow_zero]; exact hcc))
    have hpiece : ∀ w, ∀ z ∈ dV.piece w, rep (gaugeTorusGen i) z ∈ dV.piece w := by
      intro w z hz
      rw [dV.piece_le w z hz i]
      exact (dV.piece w).smul_mem _ hz
    have hmap : Submodule.map (rep (gaugeTorusGen i)) ((⨆ w ∈ s', dV.piece w) ⊔ S)
        ≤ (⨆ w ∈ s', dV.piece w) ⊔ S := by
      rw [Submodule.map_sup]
      refine sup_le (le_sup_of_le_left ?_) (le_sup_of_le_right ?_)
      · simp only [Submodule.map_iSup]
        exact iSup₂_le fun w hw => le_iSup₂_of_le w hw
          (Submodule.map_le_iff_le_comap.mpr fun z hz => hpiece w z hz)
      · exact Submodule.map_le_iff_le_comap.mpr fun z hz => hS i z hz
    have hsum : ((expI : ℂ) ^ w₀.coord i) • a + rep (gaugeTorusGen i) y = a + y := by
      have hg := hinv (gaugeTorusGen i)
      rwa [map_add, dV.piece_le w₀ a ha i] at hg
    have hkey : ((expI : ℂ) ^ w₀.coord i - 1) • (a + y)
        = ((expI : ℂ) ^ w₀.coord i) • y - rep (gaugeTorusGen i) y := by
      rw [sub_smul, one_smul, smul_add, ← hsum]
      abel
    have hmem : (a + y) ∈ (⨆ w ∈ s', dV.piece w) ⊔ S := by
      have h1 : ((expI : ℂ) ^ w₀.coord i - 1) • (a + y) ∈ (⨆ w ∈ s', dV.piece w) ⊔ S := by
        rw [hkey]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hy) (hmap ⟨y, hy, rfl⟩)
      have h2 := Submodule.smul_mem _ (((expI : ℂ) ^ w₀.coord i - 1)⁻¹) h1
      rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hc1), one_smul] at h2
    exact ih (fun w hw => hs w (Finset.mem_insert_of_mem hw)) (a + y) hmem hinv

/-- A gauge-invariant element of `V ⊔ S`, for `S` closed under the four torus generators,
  already lies in the weight-zero piece joined with `S`: every other weight is seen by some
  generator and is scaled away by it. -/
lemma mem_piece_zero_sup_of_invariant {V S : Submodule ℂ B}
    (dV : GaugeWeightDecomposition rep V)
    (hS : ∀ (i : Fin 4) (y : B), y ∈ S → rep (gaugeTorusGen i) y ∈ S)
    {x : B} (hx : x ∈ V ⊔ S) (hinv : ∀ g : GaugeGroupI, rep g x = x) :
    x ∈ dV.piece 0 ⊔ S := by
  refine mem_of_invariant_of_mem_biSup_piece_sup_of_ne_zero dV ?_ (dV.supp.erase 0) ?_ x ?_
    hinv
  · intro i y hy
    rw [Submodule.mem_sup] at hy ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    refine ⟨rep (gaugeTorusGen i) a, ?_, rep (gaugeTorusGen i) b, hS i b hb, ?_⟩
    · rw [dV.piece_le 0 a ha i]
      exact (dV.piece 0).smul_mem _ ha
    · rw [map_add]
  · intro w hw
    have hw0 : w ≠ 0 := (Finset.mem_erase.mp hw).1
    by_contra hcon
    refine hw0 (GaugeWeight.coord_injective (funext fun i => ?_))
    have hi := not_not.mp (not_exists.mp hcon i)
    rw [hi, GaugeWeight.zero_coord i]
  · have hVle : V ≤ (⨆ w ∈ dV.supp.erase 0, dV.piece w) ⊔ dV.piece 0 := by
      refine le_trans (le_of_eq dV.iSup_piece.symm) (iSup_le fun w => ?_)
      by_cases hw0 : w = 0
      · subst hw0
        exact le_sup_right
      · by_cases hw : w ∈ dV.supp
        · exact le_sup_of_le_left (le_iSup₂_of_le w (Finset.mem_erase.mpr ⟨hw0, hw⟩) le_rfl)
        · rw [dV.piece_eq_bot w hw]
          exact bot_le
    exact ((sup_le_sup_right hVle S).trans (le_of_eq (sup_assoc _ _ _))) hx

/-- Peeling a finite join of the spans of families with one fundamental and one
  anti-fundamental isospin index off a gauge-stable submodule: a gauge invariant of the
  join together with `S` is a combination of the delta contractions of the families plus a
  gauge-invariant remainder in `S`. -/
lemma exists_mem_of_invariant_biSup_isSU2FunAntiFun_span {ι : Type} [DecidableEq ι]
    {T : ι → (Fin 2 → Fin 2) → B} (hT : ∀ i, IsSU2FunAntiFun B rep (T i))
    (hstab : ∀ (i : ι) (g : GaugeGroupI), ∀ y ∈ IsSU2BiFundamental.span (T i),
      rep g y ∈ IsSU2BiFundamental.span (T i))
    (hdc : ∀ (i : ι) (g : GaugeGroupI),
      rep g (IsSU2FunAntiFun.deltaContraction (T i))
        = IsSU2FunAntiFun.deltaContraction (T i))
    (S : Submodule ℂ B) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, rep g y ∈ S) (s : Finset ι)
    {x : B} (hx : x ∈ (⨆ i ∈ s, IsSU2BiFundamental.span (T i)) ⊔ S)
    (hinv : ∀ g : GaugeGroupI, rep g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, rep g y = y)
      ∧ x - y ∈ ⨆ i ∈ s, ℂ ∙ IsSU2FunAntiFun.deltaContraction (T i) := by
  induction s using Finset.induction_on generalizing x with
  | empty =>
    rw [show (⨆ i ∈ (∅ : Finset ι), IsSU2BiFundamental.span (T i)) = ⊥ from by simp,
      bot_sup_eq] at hx
    exact ⟨x, hx, hinv, by simp⟩
  | insert a s ha ih =>
    rw [Finset.iSup_insert, sup_assoc] at hx
    have hstab' : ∀ g : GaugeGroupI,
        ∀ y ∈ (⨆ i ∈ s, IsSU2BiFundamental.span (T i)) ⊔ S,
        rep g y ∈ (⨆ i ∈ s, IsSU2BiFundamental.span (T i)) ⊔ S := by
      intro g y hy
      have key : ((⨆ i ∈ s, IsSU2BiFundamental.span (T i)) ⊔ S)
          ≤ Submodule.comap (rep g) ((⨆ i ∈ s, IsSU2BiFundamental.span (T i)) ⊔ S) :=
        sup_le (iSup_le fun i => iSup_le fun hi => fun z hz =>
            Submodule.mem_sup_left (Submodule.mem_iSup_of_mem i
              (Submodule.mem_iSup_of_mem hi (hstab i g z hz))))
          fun z hz => Submodule.mem_sup_right (hS g z hz)
      exact key hy
    obtain ⟨c, y', hy', hxy', hy'inv⟩ :=
      (hT a).mem_span_sup_invariant_iff x _ hstab' (hdc a) hx hinv
    obtain ⟨y, hyS, hyinv, hy'y⟩ := ih hy' hy'inv
    refine ⟨y, hyS, hyinv, ?_⟩
    rw [Finset.iSup_insert,
      show x - y = c • IsSU2FunAntiFun.deltaContraction (T a) + (y' - y) from by
        rw [hxy']; abel]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self _)))
      (Submodule.mem_sup_right hy'y)

/-- The span of the components of all the isospin families of a Higgs tower carrying `n`
  derivatives against a conjugate tower carrying `m`.  This is the gauge-stable
  enlargement of the pairing span of section C. -/
noncomputable def isoSpan (h : IsHiggsSector B rep hrep_mul repLorentz
      hrepLorentz_mul H barH massWeightPoly) (n m : ℕ) : Submodule ℂ B :=
  ⨆ (d : Fin n → (Fin 1 ⊕ Fin 3)) (d' : Fin m → (Fin 1 ⊕ Fin 3)),
    IsSU2BiFundamental.span (h.isoFamily d d')

include h in
/-- The isospin span is stable under the gauge group. -/
lemma isoSpan_stable (n m : ℕ) (g : GaugeGroupI) {y : B} (hy : y ∈ h.isoSpan n m) :
    rep g y ∈ h.isoSpan n m := by
  have key : h.isoSpan n m ≤ Submodule.comap (rep g) (h.isoSpan n m) :=
    iSup_le fun d => iSup_le fun d' => fun z hz =>
      Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem d'
        (h.isoFamily_span_stable d d' g hz))
  exact key hy

/-- Each isospin-diagonal pairing span of section C sits inside the isospin span. -/
lemma higgsBarHiggsSpan_le_isoSpan' (n m : ℕ) (i : Fin 2) :
    h.higgsBarHiggsSpan n m i ≤ h.isoSpan n m := by
  rw [higgsBarHiggsSpan]
  refine iSup_le fun d => iSup_le fun d' => ?_
  rw [Submodule.span_singleton_le_iff_mem]
  refine Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem d' ?_)
  rw [h.higgs_mul_barHiggs_comm d d' i i]
  exact Submodule.mem_iSup_of_mem ![i, i] (Submodule.mem_span_singleton_self _)

/-- The pairing span of section C sits inside the isospin span. -/
lemma higgsBarHiggsSpan_le_isoSpan (n m : ℕ) :
    h.higgsBarHiggsSpan n m 0 ⊔ h.higgsBarHiggsSpan n m 1 ≤ h.isoSpan n m :=
  h.higgsBarHiggsSpan_le_isoFamily_span n m

include h in
/-- A gauge invariant of the isospin span together with a gauge-stable submodule is a
  combination of the isospin contractions plus a gauge-invariant remainder in `S`. -/
lemma exists_mem_of_invariant_isoSpan_sup (n m : ℕ) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, rep g y ∈ S) {x : B} (hx : x ∈ h.isoSpan n m ⊔ S)
    (hinv : ∀ g : GaugeGroupI, rep g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, rep g y = y) ∧ x - y ∈ h.dotSpan n m := by
  obtain ⟨y, hyS, hyinv, hxy⟩ :=
    exists_mem_of_invariant_biSup_isSU2FunAntiFun_span
      (T := fun p : (Fin n → (Fin 1 ⊕ Fin 3)) × (Fin m → (Fin 1 ⊕ Fin 3)) =>
        h.isoFamily p.1 p.2)
      (fun p => h.isSU2FunAntiFun_isoFamily p.1 p.2)
      (fun p g _ hy => h.isoFamily_span_stable p.1 p.2 g hy)
      (fun p g => by
        rw [h.deltaContraction_isoFamily p.1 p.2, h.rep_dotGaugeHiggs_invariant])
      S hS Finset.univ (by
        rw [show (⨆ p ∈ (Finset.univ :
            Finset ((Fin n → (Fin 1 ⊕ Fin 3)) × (Fin m → (Fin 1 ⊕ Fin 3)))),
              IsSU2BiFundamental.span (h.isoFamily p.1 p.2))
            = h.isoSpan n m from by
          rw [isoSpan]
          simp only [Finset.mem_univ, iSup_pos]
          exact iSup_prod]
        exact hx) hinv
  refine ⟨y, hyS, hyinv, ?_⟩
  rw [show h.dotSpan n m = ⨆ p ∈ (Finset.univ :
      Finset ((Fin n → (Fin 1 ⊕ Fin 3)) × (Fin m → (Fin 1 ⊕ Fin 3)))),
        ℂ ∙ IsSU2FunAntiFun.deltaContraction (h.isoFamily p.1 p.2) from by
    simp only [Finset.mem_univ, iSup_pos, h.deltaContraction_isoFamily]
    rw [dotSpan, iSup_prod]]
  exact hxy

/-!

## H. The gauge classification up to mass weight eight

Section G is now run at each weight in turn.  Weight two dies outright, its weight-zero
piece being trivial: a single Higgs symbol carries hypercharge.  Weights four and six are
joins of isospin spans and nothing else, so peeling leaves the isospin contractions of the
towers occurring at that weight — the Higgs mass term at weight four, and its once-derived
companions at weight six.

Weight eight adds the quartic.  It is peeled off first, so that the isospin spans not yet
touched can serve as the stable submodule and no stability of the quartic span is needed;
what it leaves is a multiple of the square of the underived isospin contraction, the
second contraction of the quartic family being zero.  The three isospin spans then peel off
one after another exactly as at the lower weights.

-/

/-- A join of two gauge-stable submodules is gauge stable. -/
lemma stable_sup {S₁ S₂ : Submodule ℂ B}
    (h₁ : ∀ g : GaugeGroupI, ∀ y ∈ S₁, rep g y ∈ S₁)
    (h₂ : ∀ g : GaugeGroupI, ∀ y ∈ S₂, rep g y ∈ S₂) :
    ∀ g : GaugeGroupI, ∀ y ∈ S₁ ⊔ S₂, rep g y ∈ S₁ ⊔ S₂ := by
  intro g y hy
  have key : (S₁ ⊔ S₂) ≤ Submodule.comap (rep g) (S₁ ⊔ S₂) :=
    sup_le (fun z hz => Submodule.mem_sup_left (h₁ g z hz))
      (fun z hz => Submodule.mem_sup_right (h₂ g z hz))
  exact key hy

include h in
/-- Mass weight two carries no gauge invariant modulo a gauge-stable submodule: a single
  Higgs symbol carries hypercharge, so the weight-zero piece is trivial. -/
theorem mem_of_invariant_massWeightSubmodule_two_sup (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, rep g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmodule 2 ⊔ S) (hinv : ∀ g : GaugeGroupI, rep g x = x) :
    x ∈ S := by
  have hmem := mem_piece_zero_sup_of_invariant h.massWeightSubmoduleGaugeWeightTwo
    (fun i y hy => hS (gaugeTorusGen i) y hy) hx hinv
  rwa [h.massWeightSubmoduleGaugeWeightTwo_piece_zero, bot_sup_eq] at hmem

include h in
/-- Mass weight four modulo a gauge-stable submodule: a gauge invariant is a multiple of
  the underived isospin contraction, the Higgs mass term, plus a gauge-invariant remainder
  in `S`. -/
theorem exists_mem_of_invariant_massWeightSubmodule_four_sup (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, rep g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmodule 4 ⊔ S) (hinv : ∀ g : GaugeGroupI, rep g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, rep g y = y) ∧ x - y ∈ h.dotSpan 0 0 := by
  have hmem := mem_piece_zero_sup_of_invariant h.massWeightSubmoduleGaugeWeightFour
    (fun i y hy => hS (gaugeTorusGen i) y hy) hx hinv
  rw [h.massWeightSubmoduleGaugeWeightFour_piece_zero] at hmem
  exact h.exists_mem_of_invariant_isoSpan_sup 0 0 S hS
    (sup_le_sup_right (h.higgsBarHiggsSpan_le_isoSpan 0 0) S hmem) hinv

include h in
/-- Mass weight six modulo a gauge-stable submodule: a gauge invariant is a combination of
  the isospin contractions carrying one derivative, on either factor, plus a
  gauge-invariant remainder in `S`. -/
theorem exists_mem_of_invariant_massWeightSubmodule_six_sup (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, rep g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmodule 6 ⊔ S) (hinv : ∀ g : GaugeGroupI, rep g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, rep g y = y)
      ∧ x - y ∈ h.dotSpan 1 0 ⊔ h.dotSpan 0 1 := by
  have hmem := mem_piece_zero_sup_of_invariant h.massWeightSubmoduleGaugeWeightSix
    (fun i y hy => hS (gaugeTorusGen i) y hy) hx hinv
  rw [h.massWeightSubmoduleGaugeWeightSix_piece_zero] at hmem
  have hle : h.higgsBarHiggsSpan 1 0 0 ⊔ h.higgsBarHiggsSpan 1 0 1
      ⊔ h.higgsBarHiggsSpan 0 1 0 ⊔ h.higgsBarHiggsSpan 0 1 1
      ≤ h.isoSpan 1 0 ⊔ h.isoSpan 0 1 := by
    rw [show h.higgsBarHiggsSpan 1 0 0 ⊔ h.higgsBarHiggsSpan 1 0 1
        ⊔ h.higgsBarHiggsSpan 0 1 0 ⊔ h.higgsBarHiggsSpan 0 1 1
        = (h.higgsBarHiggsSpan 1 0 0 ⊔ h.higgsBarHiggsSpan 1 0 1)
          ⊔ (h.higgsBarHiggsSpan 0 1 0 ⊔ h.higgsBarHiggsSpan 0 1 1) from by
      rw [sup_assoc]]
    exact sup_le_sup (h.higgsBarHiggsSpan_le_isoSpan 1 0) (h.higgsBarHiggsSpan_le_isoSpan 0 1)
  obtain ⟨y₁, hy₁, hy₁inv, hxy₁⟩ :=
    h.exists_mem_of_invariant_isoSpan_sup 1 0 (h.isoSpan 0 1 ⊔ S)
      (stable_sup (fun g y hy => h.isoSpan_stable 0 1 g hy) hS)
      (by
        refine le_trans (sup_le_sup_right hle S) (le_of_eq (sup_assoc _ _ _)) hmem)
      hinv
  obtain ⟨y, hyS, hyinv, hy₁y⟩ :=
    h.exists_mem_of_invariant_isoSpan_sup 0 1 S hS hy₁ hy₁inv
  refine ⟨y, hyS, hyinv, ?_⟩
  rw [show x - y = (x - y₁) + (y₁ - y) from by abel]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hxy₁) (Submodule.mem_sup_right hy₁y)

include h in
/-- Mass weight eight modulo a gauge-stable submodule: a gauge invariant is a combination
  of the isospin contractions carrying two derivatives and of the square of the underived
  one — the quartic potential — plus a gauge-invariant remainder in `S`. -/
theorem exists_mem_of_invariant_massWeightSubmodule_eight_sup (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, rep g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmodule 8 ⊔ S) (hinv : ∀ g : GaugeGroupI, rep g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, rep g y = y)
      ∧ x - y ∈ h.dotSpan 2 0 ⊔ h.dotSpan 0 2 ⊔ h.dotSpan 1 1
        ⊔ ℂ ∙ (h.dotGaugeHiggs ![] ![] * h.dotGaugeHiggs ![] ![]) := by
  have hmem := mem_piece_zero_sup_of_invariant h.massWeightSubmoduleGaugeWeightEight
    (fun i y hy => hS (gaugeTorusGen i) y hy) hx hinv
  rw [h.massWeightSubmoduleGaugeWeightEight_piece_zero] at hmem
  set S₃ := h.isoSpan 1 1 ⊔ S with hS₃def
  set S₂ := h.isoSpan 0 2 ⊔ S₃ with hS₂def
  set S₁ := h.isoSpan 2 0 ⊔ S₂ with hS₁def
  have hS₃ : ∀ g : GaugeGroupI, ∀ y ∈ S₃, rep g y ∈ S₃ :=
    stable_sup (fun g y hy => h.isoSpan_stable 1 1 g hy) hS
  have hS₂ : ∀ g : GaugeGroupI, ∀ y ∈ S₂, rep g y ∈ S₂ :=
    stable_sup (fun g y hy => h.isoSpan_stable 0 2 g hy) hS₃
  have hS₁ : ∀ g : GaugeGroupI, ∀ y ∈ S₁, rep g y ∈ S₁ :=
    stable_sup (fun g y hy => h.isoSpan_stable 2 0 g hy) hS₂
  have hQ : IsSU2QuadFundamental.span h.quadFamily
      ≤ IsSU2QuadFundamental.span h.quadFamily ⊔ S₁ := le_sup_left
  have hA20 : h.isoSpan 2 0 ≤ IsSU2QuadFundamental.span h.quadFamily ⊔ S₁ :=
    le_sup_of_le_right le_sup_left
  have hA02 : h.isoSpan 0 2 ≤ IsSU2QuadFundamental.span h.quadFamily ⊔ S₁ :=
    le_sup_of_le_right (le_sup_of_le_right le_sup_left)
  have hA11 : h.isoSpan 1 1 ≤ IsSU2QuadFundamental.span h.quadFamily ⊔ S₁ :=
    le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right le_sup_left))
  have hSle : S ≤ IsSU2QuadFundamental.span h.quadFamily ⊔ S₁ :=
    le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right le_sup_right))
  have hquad : x ∈ IsSU2QuadFundamental.span h.quadFamily ⊔ S₁ :=
    sup_le (sup_le (sup_le (sup_le (sup_le (sup_le
      ((h.higgsBarHiggsSpan_le_isoSpan' 2 0 0).trans hA20)
      ((h.higgsBarHiggsSpan_le_isoSpan' 2 0 1).trans hA20))
      ((h.higgsBarHiggsSpan_le_isoSpan' 0 2 0).trans hA02))
      ((h.higgsBarHiggsSpan_le_isoSpan' 0 2 1).trans hA02))
      (sup_le ((h.higgsBarHiggsSpan_le_isoSpan' 1 1 0).trans hA11)
        ((h.higgsBarHiggsSpan_le_isoSpan' 1 1 1).trans hA11)))
      (h.quarticSpan_le_quadFamily_span.trans hQ)) hSle hmem
  obtain ⟨c₁, c₂, y₁, hy₁, hxy₁, hy₁inv⟩ :=
    h.isSU2QuadFundamental_quadFamily.mem_span_sup_invariant_iff x S₁ hS₁
      (fun g => by
        rw [epsilonContraction₁₂_quadFamily, h.rep_mul, h.rep_dotGaugeHiggs_invariant])
      (fun g => by rw [epsilonContraction₁₃_quadFamily, map_zero]) hquad hinv
  have hxy₁' : x - y₁ ∈ ℂ ∙ (h.dotGaugeHiggs ![] ![] * h.dotGaugeHiggs ![] ![]) := by
    rw [show x - y₁ = c₁ • IsSU2QuadFundamental.epsilonContraction₁₂ h.quadFamily
        + c₂ • IsSU2QuadFundamental.epsilonContraction₁₃ h.quadFamily from by
      rw [hxy₁]; abel, epsilonContraction₁₂_quadFamily, epsilonContraction₁₃_quadFamily,
      smul_zero, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  obtain ⟨y₂, hy₂, hy₂inv, hy₁y₂⟩ :=
    h.exists_mem_of_invariant_isoSpan_sup 2 0 S₂ hS₂ hy₁ hy₁inv
  obtain ⟨y₃, hy₃, hy₃inv, hy₂y₃⟩ :=
    h.exists_mem_of_invariant_isoSpan_sup 0 2 S₃ hS₃ hy₂ hy₂inv
  obtain ⟨y, hyS, hyinv, hy₃y⟩ :=
    h.exists_mem_of_invariant_isoSpan_sup 1 1 S hS hy₃ hy₃inv
  refine ⟨y, hyS, hyinv, ?_⟩
  rw [show x - y = (y₁ - y₂) + ((y₂ - y₃) + ((y₃ - y) + (x - y₁))) from by abel]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left hy₁y₂)))
    (Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right hy₂y₃)))
      (Submodule.add_mem _
        (Submodule.mem_sup_left (Submodule.mem_sup_right hy₃y))
        (Submodule.mem_sup_right hxy₁')))

/-!

## I. The gauge-invariant submodules up to mass weight eight

Taking the stable submodule to be the trivial one turns section H into a statement about
the mass-weight submodules themselves, and both inclusions are then available: section H
bounds the invariants from above, and the isospin contractions are themselves gauge
invariant and of the right mass weight, which bounds them from below.  The two meet, so
the gauge-invariant part of each mass-weight submodule up to weight eight is exactly
described.

-/

include h in
/-- A gauge-invariant term of mass weight four is a multiple of the underived isospin
  contraction. -/
lemma mem_dotSpan_of_invariant_massWeightSubmodule_four {x : B}
    (hx : x ∈ h.massWeightSubmodule 4) (hg : ∀ g : GaugeGroupI, rep g x = x) :
    x ∈ h.dotSpan 0 0 := by
  obtain ⟨y, hy, -, hxy⟩ := h.exists_mem_of_invariant_massWeightSubmodule_four_sup ⊥
    (fun g z hz => by rw [Submodule.mem_bot] at hz; simp [hz])
    (Submodule.mem_sup_left hx) hg
  rw [Submodule.mem_bot] at hy
  rwa [hy, sub_zero] at hxy

include h in
/-- A gauge-invariant term of mass weight six is a combination of the isospin contractions
  carrying one derivative, on either factor. -/
lemma mem_dotSpan_of_invariant_massWeightSubmodule_six {x : B}
    (hx : x ∈ h.massWeightSubmodule 6) (hg : ∀ g : GaugeGroupI, rep g x = x) :
    x ∈ h.dotSpan 1 0 ⊔ h.dotSpan 0 1 := by
  obtain ⟨y, hy, -, hxy⟩ := h.exists_mem_of_invariant_massWeightSubmodule_six_sup ⊥
    (fun g z hz => by rw [Submodule.mem_bot] at hz; simp [hz])
    (Submodule.mem_sup_left hx) hg
  rw [Submodule.mem_bot] at hy
  rwa [hy, sub_zero] at hxy

include h in
/-- A gauge-invariant term of mass weight eight is a combination of the isospin
  contractions carrying two derivatives and of the square of the underived contraction. -/
lemma mem_dotSpan_of_invariant_massWeightSubmodule_eight {x : B}
    (hx : x ∈ h.massWeightSubmodule 8) (hg : ∀ g : GaugeGroupI, rep g x = x) :
    x ∈ h.dotSpan 2 0 ⊔ h.dotSpan 0 2 ⊔ h.dotSpan 1 1
      ⊔ ℂ ∙ (h.dotGaugeHiggs ![] ![] * h.dotGaugeHiggs ![] ![]) := by
  obtain ⟨y, hy, -, hxy⟩ := h.exists_mem_of_invariant_massWeightSubmodule_eight_sup ⊥
    (fun g z hz => by rw [Submodule.mem_bot] at hz; simp [hz])
    (Submodule.mem_sup_left hx) hg
  rw [Submodule.mem_bot] at hy
  rwa [hy, sub_zero] at hxy

include h in
/-- An isospin contraction has the mass weight of its two towers together. -/
lemma dotGaugeHiggs_mem_massWeightSubmodule {n1 n2 : ℕ} (d1 : Fin n1 → (Fin 1 ⊕ Fin 3))
    (d2 : Fin n2 → (Fin 1 ⊕ Fin 3)) :
    h.dotGaugeHiggs d1 d2 ∈ h.massWeightSubmodule (2 * (1 + n1) + 2 * (1 + n2)) := by
  have hH : ∀ i, h.higgs d1 i ∈ h.massWeightSubmodule (2 * (1 + n1)) := fun i =>
    h.massWeightSubmodule_higgsSubmodule_le n1
      (Submodule.mem_iSup_of_mem d1 (LinearMap.mem_range_self _ _))
  have hbH : ∀ i, h.barHiggs d2 i ∈ h.massWeightSubmodule (2 * (1 + n2)) := fun i =>
    h.massWeightSubmodule_barHiggsSubmodule_le n2
      (Submodule.mem_iSup_of_mem d2 (LinearMap.mem_range_self _ _))
  rw [dotGaugeHiggs]
  exact add_mem (h.massWeightSubmodule_mul_le _ _ (Submodule.mul_mem_mul (hH 0) (hbH 0)))
    (h.massWeightSubmodule_mul_le _ _ (Submodule.mul_mem_mul (hH 1) (hbH 1)))

/-- The gauge invariants of mass weight four: the underived isospin contraction. -/
lemma gaugeInvariantOfMassDim_four_eq_dotSpan :
    h.gaugeInvariantOfMassDim 4 = h.dotSpan 0 0 := by
  refine le_antisymm (fun x hx =>
    h.mem_dotSpan_of_invariant_massWeightSubmodule_four hx.1 hx.2) ?_
  rw [dotSpan]
  refine iSup_le fun d => iSup_le fun d' =>
    (Submodule.span_singleton_le_iff_mem _ _).mpr ⟨?_, fun k =>
      h.rep_dotGaugeHiggs_invariant k d d'⟩
  exact h.dotGaugeHiggs_mem_massWeightSubmodule d d'

/-- The gauge invariants of mass weight six: the isospin contractions with one derivative
  on either factor. -/
lemma gaugeInvariantOfMassDim_six_eq_dotSpan :
    h.gaugeInvariantOfMassDim 6 = h.dotSpan 1 0 ⊔ h.dotSpan 0 1 := by
  refine le_antisymm (fun x hx =>
    h.mem_dotSpan_of_invariant_massWeightSubmodule_six hx.1 hx.2) (sup_le ?_ ?_) <;>
    rw [dotSpan] <;>
    refine iSup_le fun d => iSup_le fun d' =>
      (Submodule.span_singleton_le_iff_mem _ _).mpr ⟨?_, fun k =>
        h.rep_dotGaugeHiggs_invariant k d d'⟩
  · exact h.dotGaugeHiggs_mem_massWeightSubmodule d d'
  · exact h.dotGaugeHiggs_mem_massWeightSubmodule d d'

/-- The gauge invariants of mass weight eight: the isospin contractions with two
  derivatives distributed over the two factors, together with the square of the underived
  contraction — the quartic potential. -/
lemma gaugeInvariantOfMassDim_eight_eq_dotSpan :
    h.gaugeInvariantOfMassDim 8 = h.dotSpan 2 0 ⊔ h.dotSpan 0 2 ⊔ h.dotSpan 1 1
      ⊔ ℂ ∙ (h.dotGaugeHiggs ![] ![] * h.dotGaugeHiggs ![] ![]) := by
  refine le_antisymm (fun x hx =>
    h.mem_dotSpan_of_invariant_massWeightSubmodule_eight hx.1 hx.2)
    (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_)
  · rw [dotSpan]
    exact iSup_le fun d => iSup_le fun d' =>
      (Submodule.span_singleton_le_iff_mem _ _).mpr
        ⟨h.dotGaugeHiggs_mem_massWeightSubmodule d d',
          fun k => h.rep_dotGaugeHiggs_invariant k d d'⟩
  · rw [dotSpan]
    exact iSup_le fun d => iSup_le fun d' =>
      (Submodule.span_singleton_le_iff_mem _ _).mpr
        ⟨h.dotGaugeHiggs_mem_massWeightSubmodule d d',
          fun k => h.rep_dotGaugeHiggs_invariant k d d'⟩
  · rw [dotSpan]
    exact iSup_le fun d => iSup_le fun d' =>
      (Submodule.span_singleton_le_iff_mem _ _).mpr
        ⟨h.dotGaugeHiggs_mem_massWeightSubmodule d d',
          fun k => h.rep_dotGaugeHiggs_invariant k d d'⟩
  · refine (Submodule.span_singleton_le_iff_mem _ _).mpr ⟨?_, fun k => ?_⟩
    · exact h.massWeightSubmodule_mul_le 4 4 (Submodule.mul_mem_mul
        (h.dotGaugeHiggs_mem_massWeightSubmodule ![] ![])
        (h.dotGaugeHiggs_mem_massWeightSubmodule ![] ![]))
    · rw [h.rep_mul, h.rep_dotGaugeHiggs_invariant]

end IsHiggsSector

end StandardModel
