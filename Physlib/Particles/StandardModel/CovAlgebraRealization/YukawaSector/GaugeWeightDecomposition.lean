/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.CovAlgebraRealization.YukawaSector.Basic
public import Physlib.Particles.StandardModel.IsFermionSector.MassWeight.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.AlgebraRealization.HiggsAlgebraCovRealization.DerivSubmodule.GaugeWeightDecomposition
/-!
# The gauge weight decomposition of the Yukawa sector at mass weight eight

Mass weight eight is where the Yukawa sector first has anything to say: by
`sectorMassWeight_higgs_fermion_eight` the whole sector at that weight is one Higgs
tower against two underived fermion towers, the weight of `H ψ ψ` itself.  Transporting
the gauge weight decompositions of the two sectors along that identification decomposes
the sector, and the question of which Yukawa couplings can exist becomes the question of
which pieces survive at gauge weight zero.

Almost none of them do, and the reason is hypercharge alone.  Writing `6Y` for the
normalisation used throughout, a symbol carries the contragredient of its value space and
so the negative of its charge: the Higgs symbols carry `-3` and their conjugates `+3`,
while the ten fermion species carry

`d = 2`, `bard = -2`, `u = -4`, `baru = 4`, `Q = -1`, `barQ = 1`, `L = 3`, `barL = -3`,
`e = 6`, `bare = -6`.

A block of the decomposition is a choice of one Higgs symbol and two fermion species, and
it can reach gauge weight zero only if the three charges sum to zero.  Against the Higgs
that asks the fermion pair to sum to `+3`, which happens only for `{d, barQ}`,
`{baru, Q}` and `{barL, e}`; against the conjugate Higgs it asks for `-3`, which happens
only for `{bard, Q}`, `{u, barQ}` and `{L, bare}`.  No species pairs with itself, since
`2f = ±3` has no solution.  Each of the six pairs occurs in both orders inside the product
of the two fermion towers, so of the `2 * 10 * 10 = 200` blocks exactly twelve survive and
one hundred and eighty-eight are `⊥`.

That is the whole content of this file: the surviving twelve are the Yukawa couplings
`H d barQ`, `H baru Q`, `H barL e`, `barH bard Q`, `barH u barQ`, `barH L bare` and their
transposes.  The colour and isospin structure eliminates nothing further here — it only
decides which components inside a surviving block pair up, which is a later question.

- A. The sector at mass weight eight, decomposed
- B. Splitting a Higgs-fermion-fermion product along its joins
- C. Hypercharge adds across a product
- D. The two Higgs hypercharges
- E. The hypercharge sieve on two fermions against one Higgs
- F. The twelve surviving blocks
- G. Invariants modulo a gauge-stable submodule

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz Pointwise

namespace CovAlgebraRealization

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : CovAlgebraRealization B repGauge repLorentz massWeightPoly)

/-!

## A. The sector at mass weight eight, decomposed

-/

/-- The gauge weight decomposition of the Yukawa sector at mass weight eight, transported
  along `sectorMassWeight_higgs_fermion_eight` from the product of the Higgs derivative
  submodule with two copies of the underived fermion towers. -/
@[implicit_reducible]
noncomputable def sectorMassWeightEightGaugeWeight :
    GaugeWeightDecomposition repGauge
      (h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.mul (d := h.isHiggsSector.derivSubmoduleGaugeWeight 0)
      (d' := GaugeWeightDecomposition.mul
        (d := h.isFermionSector.derivSubmoduleGaugeWeight 0)
        (d' := h.isFermionSector.derivSubmoduleGaugeWeight 0)))
    _ h.sectorMassWeight_higgs_fermion_eight

/-!

## B. Splitting a Higgs-fermion-fermion product along its joins

The two fermion factors are each a join over ten species, so the product has to be
distributed over both before any species-level statement can be made.  The left factor is
handled by `IsFermionSector.piece_sup_mul`; the two lemmas here reach the inner factors of
a triple product, which that lemma cannot see.

-/

/-- If the first fermion factor of a triple product is a join `VA ⊔ VB`, its weight-`w`
  piece splits along the join. -/
lemma piece_mul_sup_mul {VX VA VB VZ : Submodule ℂ B}
    (dX : GaugeWeightDecomposition repGauge VX) (dA : GaugeWeightDecomposition repGauge VA)
    (dB : GaugeWeightDecomposition repGauge VB) (dZ : GaugeWeightDecomposition repGauge VZ)
    (w : GaugeWeight) :
    (GaugeWeightDecomposition.mul (d := dX)
        (d' := GaugeWeightDecomposition.mul
          (d := GaugeWeightDecomposition.sup (d := dA) (d' := dB)) (d' := dZ))).piece w
      = (GaugeWeightDecomposition.mul (d := dX)
            (d' := GaugeWeightDecomposition.mul (d := dA) (d' := dZ))).piece w
        ⊔ (GaugeWeightDecomposition.mul (d := dX)
            (d' := GaugeWeightDecomposition.mul (d := dB) (d' := dZ))).piece w :=
  GaugeWeightDecomposition.piece_congr
    (d := GaugeWeightDecomposition.mul (d := dX)
      (d' := GaugeWeightDecomposition.mul
        (d := GaugeWeightDecomposition.sup (d := dA) (d' := dB)) (d' := dZ)))
    (d' := GaugeWeightDecomposition.sup
      (d := GaugeWeightDecomposition.mul (d := dX)
        (d' := GaugeWeightDecomposition.mul (d := dA) (d' := dZ)))
      (d' := GaugeWeightDecomposition.mul (d := dX)
        (d' := GaugeWeightDecomposition.mul (d := dB) (d' := dZ))))
    (by rw [Submodule.sup_mul, Submodule.mul_sup]) w

/-- If the second fermion factor of a triple product is a join `VA ⊔ VB`, its weight-`w`
  piece splits along the join. -/
lemma piece_mul_mul_sup {VX VY VA VB : Submodule ℂ B}
    (dX : GaugeWeightDecomposition repGauge VX) (dY : GaugeWeightDecomposition repGauge VY)
    (dA : GaugeWeightDecomposition repGauge VA) (dB : GaugeWeightDecomposition repGauge VB)
    (w : GaugeWeight) :
    (GaugeWeightDecomposition.mul (d := dX)
        (d' := GaugeWeightDecomposition.mul (d := dY)
          (d' := GaugeWeightDecomposition.sup (d := dA) (d' := dB)))).piece w
      = (GaugeWeightDecomposition.mul (d := dX)
            (d' := GaugeWeightDecomposition.mul (d := dY) (d' := dA))).piece w
        ⊔ (GaugeWeightDecomposition.mul (d := dX)
            (d' := GaugeWeightDecomposition.mul (d := dY) (d' := dB))).piece w :=
  GaugeWeightDecomposition.piece_congr
    (d := GaugeWeightDecomposition.mul (d := dX)
      (d' := GaugeWeightDecomposition.mul (d := dY)
        (d' := GaugeWeightDecomposition.sup (d := dA) (d' := dB))))
    (d' := GaugeWeightDecomposition.sup
      (d := GaugeWeightDecomposition.mul (d := dX)
        (d' := GaugeWeightDecomposition.mul (d := dY) (d' := dA)))
      (d' := GaugeWeightDecomposition.mul (d := dX)
        (d' := GaugeWeightDecomposition.mul (d := dY) (d' := dB))))
    (by rw [Submodule.mul_sup, Submodule.mul_sup]) w

/-!

## C. Hypercharge adds across a product

`IsFermionSector.mul_piece_zero_eq_bot_of_hypercharge` kills a product of two
decompositions whose constant hypercharges do not cancel.  To use it on a triple product
the two fermion factors have to be read as a single decomposition, and the only thing
needed about them is that their hypercharges add.

-/

/-- Two decompositions with constant hypercharge have a product of constant hypercharge,
  the sum of the two: the support of a product is the pointwise sum of the supports, and
  hypercharge is the fourth coordinate of a gauge weight. -/
lemma mul_supp_hypercharge {V V' : Submodule ℂ B}
    {dV : GaugeWeightDecomposition repGauge V} {dV' : GaugeWeightDecomposition repGauge V'}
    {hc hc' : ℤ} (hV : ∀ w ∈ dV.supp, w.2.2.2 = hc) (hV' : ∀ w ∈ dV'.supp, w.2.2.2 = hc') :
    ∀ w ∈ (GaugeWeightDecomposition.mul (d := dV) (d' := dV')).supp, w.2.2.2 = hc + hc' := by
  intro w hw
  have hw' : w ∈ dV.supp + dV'.supp := hw
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Finset.mem_add.mp hw'
  show w₁.2.2.2 + w₂.2.2.2 = hc + hc'
  rw [hV w₁ hw₁, hV' w₂ hw₂]

/-!

## D. The two Higgs hypercharges

-/

/-- The Higgs symbols carry hypercharge `-3`, independent of isospin and of the number of
  derivatives: the two weights in the support are `(0, 0, ∓1, -3)`. -/
lemma higgsSubmoduleGaugeWeight_hc (n : ℕ) :
    ∀ w ∈ (h.isHiggsSector.higgsSubmoduleGaugeWeight n).supp, w.2.2.2 = -3 := by
  intro w hw
  have hw' : w ∈ ({((0, 0, -1, -3) : GaugeWeight), (0, 0, 1, -3)} : Finset GaugeWeight) := hw
  fin_cases hw' <;> rfl

/-- The conjugate-Higgs symbols carry hypercharge `3`, independent of isospin and of the
  number of derivatives: the two weights in the support are `(0, 0, ±1, 3)`. -/
lemma barHiggsSubmoduleGaugeWeight_hc (n : ℕ) :
    ∀ w ∈ (h.isHiggsSector.barHiggsSubmoduleGaugeWeight n).supp, w.2.2.2 = 3 := by
  intro w hw
  have hw' : w ∈ ({((0, 0, 1, 3) : GaugeWeight), (0, 0, -1, 3)} : Finset GaugeWeight) := hw
  fin_cases hw' <;> rfl

/-!

## E. The hypercharge sieve on two fermions against one Higgs

Everything the Standard Model gauge group has to say about which Yukawa couplings exist is
already said by hypercharge.  A block of the mass-weight-eight decomposition is a Higgs
symbol against a pair of fermion species, and the three hypercharges have to cancel.  Since
the Higgs contributes `∓3`, the fermion pair must contribute `±3`, and the ten species
charges `2, -2, -4, 4, -1, 1, 3, -3, 6, -6` admit only three unordered pairs of each sign.

The two lemmas below are stated for an arbitrary decomposition `dV` of constant hypercharge
rather than for the Higgs submodules themselves, since that is all the argument uses; the
Higgs and conjugate-Higgs cases are then two applications.  No species pairs with itself:
`2f = ±3` has no integer solution.

-/

open IsFermionSector in
/-- The hypercharge sieve against a Higgs symbol. If `dV` has constant hypercharge `-3`,
  as the Higgs symbols do, then of the hundred species pairings in a product of two fermion
  towers only the six whose hypercharges sum to `+3` survive at gauge weight zero: `d barQ`,
  `baru Q` and `barL e`, each in both orders. The other ninety-four pairings leave a nonzero
  hypercharge behind and so contribute nothing. -/
lemma mul_speciesGaugeWeight_mul_piece_zero_neg_three {V : Submodule ℂ B}
    {dV : GaugeWeightDecomposition repGauge V} (hV : ∀ w ∈ dV.supp, w.2.2.2 = -3)
    {n m : ℕ} (f f' : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3)
    (l' : Fin m → Fin 1 ⊕ Fin 3) :
    (GaugeWeightDecomposition.mul (d := dV)
        (d' := GaugeWeightDecomposition.mul
          (d := h.isFermionSector.speciesGaugeWeight f l)
          (d' := h.isFermionSector.speciesGaugeWeight f' l'))).piece 0
      = (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_d f l)
              (d' := h.isFermionSector.rangeGaugeWeight_barQ f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_barQ f l)
              (d' := h.isFermionSector.rangeGaugeWeight_d f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_baru f l)
              (d' := h.isFermionSector.rangeGaugeWeight_Q f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_Q f l)
              (d' := h.isFermionSector.rangeGaugeWeight_baru f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_barL f l)
              (d' := h.isFermionSector.rangeGaugeWeight_e f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_e f l)
              (d' := h.isFermionSector.rangeGaugeWeight_barL f' l'))).piece 0 := by
  have hd := h.isFermionSector.rangeGaugeWeight_d_hc f l
  have hbard := h.isFermionSector.rangeGaugeWeight_bard_hc f l
  have hu := h.isFermionSector.rangeGaugeWeight_u_hc f l
  have hbaru := h.isFermionSector.rangeGaugeWeight_baru_hc f l
  have hQ := h.isFermionSector.rangeGaugeWeight_Q_hc f l
  have hbarQ := h.isFermionSector.rangeGaugeWeight_barQ_hc f l
  have hL := h.isFermionSector.rangeGaugeWeight_L_hc f l
  have hbarL := h.isFermionSector.rangeGaugeWeight_barL_hc f l
  have he := h.isFermionSector.rangeGaugeWeight_e_hc f l
  have hbare := h.isFermionSector.rangeGaugeWeight_bare_hc f l
  have hd' := h.isFermionSector.rangeGaugeWeight_d_hc f' l'
  have hbard' := h.isFermionSector.rangeGaugeWeight_bard_hc f' l'
  have hu' := h.isFermionSector.rangeGaugeWeight_u_hc f' l'
  have hbaru' := h.isFermionSector.rangeGaugeWeight_baru_hc f' l'
  have hQ' := h.isFermionSector.rangeGaugeWeight_Q_hc f' l'
  have hbarQ' := h.isFermionSector.rangeGaugeWeight_barQ_hc f' l'
  have hL' := h.isFermionSector.rangeGaugeWeight_L_hc f' l'
  have hbarL' := h.isFermionSector.rangeGaugeWeight_barL_hc f' l'
  have he' := h.isFermionSector.rangeGaugeWeight_e_hc f' l'
  have hbare' := h.isFermionSector.rangeGaugeWeight_bare_hc f' l'
  simp only [piece_mul_sup_mul, piece_mul_mul_sup,
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hd hd') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hd hbard') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hd hu') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hd hbaru') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hd hQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hd hL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hd hbarL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hd he') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hd hbare') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbard hd') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbard hbard') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbard hu') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbard hbaru') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbard hQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbard hbarQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbard hL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbard hbarL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbard he') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbard hbare') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hu hd') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hu hbard') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hu hu') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hu hbaru') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hu hQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hu hbarQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hu hL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hu hbarL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hu he') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hu hbare') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbaru hd') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbaru hbard') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbaru hu') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbaru hbaru') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbaru hbarQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbaru hL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbaru hbarL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbaru he') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbaru hbare') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hQ hd') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hQ hbard') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hQ hu') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hQ hQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hQ hbarQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hQ hL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hQ hbarL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hQ he') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hQ hbare') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarQ hbard') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarQ hu') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarQ hbaru') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarQ hQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarQ hbarQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarQ hL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarQ hbarL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarQ he') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarQ hbare') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hL hd') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hL hbard') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hL hu') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hL hbaru') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hL hQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hL hbarQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hL hL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hL hbarL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hL he') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hL hbare') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarL hd') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarL hbard') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarL hu') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarL hbaru') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarL hQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarL hbarQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarL hL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarL hbarL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarL hbare') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge he hd') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge he hbard') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge he hu') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge he hbaru') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge he hQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge he hbarQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge he hL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge he he') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge he hbare') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbare hd') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbare hbard') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbare hu') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbare hbaru') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbare hQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbare hbarQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbare hL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbare hbarL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbare he') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbare hbare') (by decide),
    bot_sup_eq, sup_bot_eq]
  ac_rfl

open IsFermionSector in
/-- The hypercharge sieve against a conjugate-Higgs symbol. If `dV` has constant
  hypercharge `3`, as the conjugate-Higgs symbols do, then of the hundred species pairings
  only the six whose hypercharges sum to `-3` survive at gauge weight zero: `bard Q`,
  `u barQ` and `L bare`, each in both orders. -/
lemma mul_speciesGaugeWeight_mul_piece_zero_pos_three {V : Submodule ℂ B}
    {dV : GaugeWeightDecomposition repGauge V} (hV : ∀ w ∈ dV.supp, w.2.2.2 = 3)
    {n m : ℕ} (f f' : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3)
    (l' : Fin m → Fin 1 ⊕ Fin 3) :
    (GaugeWeightDecomposition.mul (d := dV)
        (d' := GaugeWeightDecomposition.mul
          (d := h.isFermionSector.speciesGaugeWeight f l)
          (d' := h.isFermionSector.speciesGaugeWeight f' l'))).piece 0
      = (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_bard f l)
              (d' := h.isFermionSector.rangeGaugeWeight_Q f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_Q f l)
              (d' := h.isFermionSector.rangeGaugeWeight_bard f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_u f l)
              (d' := h.isFermionSector.rangeGaugeWeight_barQ f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_barQ f l)
              (d' := h.isFermionSector.rangeGaugeWeight_u f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_L f l)
              (d' := h.isFermionSector.rangeGaugeWeight_bare f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_bare f l)
              (d' := h.isFermionSector.rangeGaugeWeight_L f' l'))).piece 0 := by
  have hd := h.isFermionSector.rangeGaugeWeight_d_hc f l
  have hbard := h.isFermionSector.rangeGaugeWeight_bard_hc f l
  have hu := h.isFermionSector.rangeGaugeWeight_u_hc f l
  have hbaru := h.isFermionSector.rangeGaugeWeight_baru_hc f l
  have hQ := h.isFermionSector.rangeGaugeWeight_Q_hc f l
  have hbarQ := h.isFermionSector.rangeGaugeWeight_barQ_hc f l
  have hL := h.isFermionSector.rangeGaugeWeight_L_hc f l
  have hbarL := h.isFermionSector.rangeGaugeWeight_barL_hc f l
  have he := h.isFermionSector.rangeGaugeWeight_e_hc f l
  have hbare := h.isFermionSector.rangeGaugeWeight_bare_hc f l
  have hd' := h.isFermionSector.rangeGaugeWeight_d_hc f' l'
  have hbard' := h.isFermionSector.rangeGaugeWeight_bard_hc f' l'
  have hu' := h.isFermionSector.rangeGaugeWeight_u_hc f' l'
  have hbaru' := h.isFermionSector.rangeGaugeWeight_baru_hc f' l'
  have hQ' := h.isFermionSector.rangeGaugeWeight_Q_hc f' l'
  have hbarQ' := h.isFermionSector.rangeGaugeWeight_barQ_hc f' l'
  have hL' := h.isFermionSector.rangeGaugeWeight_L_hc f' l'
  have hbarL' := h.isFermionSector.rangeGaugeWeight_barL_hc f' l'
  have he' := h.isFermionSector.rangeGaugeWeight_e_hc f' l'
  have hbare' := h.isFermionSector.rangeGaugeWeight_bare_hc f' l'
  simp only [piece_mul_sup_mul, piece_mul_mul_sup,
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hd hd') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hd hbard') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hd hu') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hd hbaru') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hd hQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hd hbarQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hd hL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hd hbarL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hd he') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hd hbare') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbard hd') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbard hbard') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbard hu') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbard hbaru') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbard hbarQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbard hL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbard hbarL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbard he') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbard hbare') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hu hd') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hu hbard') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hu hu') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hu hbaru') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hu hQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hu hL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hu hbarL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hu he') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hu hbare') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbaru hd') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbaru hbard') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbaru hu') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbaru hbaru') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbaru hQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbaru hbarQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbaru hL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbaru hbarL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbaru he') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbaru hbare') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hQ hd') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hQ hu') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hQ hbaru') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hQ hQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hQ hbarQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hQ hL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hQ hbarL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hQ he') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hQ hbare') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarQ hd') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarQ hbard') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarQ hbaru') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarQ hQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarQ hbarQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarQ hL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarQ hbarL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarQ he') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarQ hbare') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hL hd') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hL hbard') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hL hu') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hL hbaru') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hL hQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hL hbarQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hL hL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hL hbarL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hL he') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarL hd') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarL hbard') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarL hu') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarL hbaru') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarL hQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarL hbarQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarL hL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarL hbarL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarL he') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbarL hbare') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge he hd') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge he hbard') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge he hu') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge he hbaru') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge he hQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge he hbarQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge he hL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge he hbarL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge he he') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge he hbare') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbare hd') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbare hbard') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbare hu') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbare hbaru') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbare hQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbare hbarQ') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbare hbarL') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbare he') (by decide),
    mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hbare hbare') (by decide),
    bot_sup_eq, sup_bot_eq]
  ac_rfl

/-!

## F. The twelve surviving blocks

The pieces now assemble.  Unfolding the Higgs derivative submodule into its Higgs and
conjugate-Higgs halves and the fermion towers into a join over families splits the product
into blocks indexed by a Higgs choice and two families, and the sieve of section E reduces
each block to six terms.  Twelve survive in all, and they are exactly the Yukawa couplings
of the Standard Model: the down-type coupling `H d barQ`, the up-type coupling `H baru Q`,
the charged-lepton coupling `H barL e`, their conjugates `barH bard Q`, `barH u barQ` and
`barH L bare`, and the transpose of each, the two fermion towers being interchangeable.

Nothing here constrains the families: all nine pairs `(f, f')` occur, which is where the
Yukawa matrices come from.

-/

/-- The weight-zero piece of the Yukawa sector at mass weight eight: the join, over pairs
  of families, of the twelve blocks that hypercharge allows.  Of the two hundred ways of
  choosing one Higgs symbol and two fermion species, only these twelve have vanishing total
  hypercharge; the remaining one hundred and eighty-eight are killed by
  `mul_speciesGaugeWeight_mul_piece_zero_neg_three` and
  `mul_speciesGaugeWeight_mul_piece_zero_pos_three`. -/
lemma sectorMassWeightEightGaugeWeight_piece_zero :
    h.sectorMassWeightEightGaugeWeight.piece 0
      = ⨆ (f : Fin 3) (f' : Fin 3),
        (GaugeWeightDecomposition.mul
            (d := h.isHiggsSector.higgsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_d f ![])
              (d' := h.isFermionSector.rangeGaugeWeight_barQ f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := h.isHiggsSector.higgsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_barQ f ![])
              (d' := h.isFermionSector.rangeGaugeWeight_d f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := h.isHiggsSector.higgsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_baru f ![])
              (d' := h.isFermionSector.rangeGaugeWeight_Q f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := h.isHiggsSector.higgsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_Q f ![])
              (d' := h.isFermionSector.rangeGaugeWeight_baru f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := h.isHiggsSector.higgsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_barL f ![])
              (d' := h.isFermionSector.rangeGaugeWeight_e f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := h.isHiggsSector.higgsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_e f ![])
              (d' := h.isFermionSector.rangeGaugeWeight_barL f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := h.isHiggsSector.barHiggsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_bard f ![])
              (d' := h.isFermionSector.rangeGaugeWeight_Q f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := h.isHiggsSector.barHiggsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_Q f ![])
              (d' := h.isFermionSector.rangeGaugeWeight_bard f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := h.isHiggsSector.barHiggsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_u f ![])
              (d' := h.isFermionSector.rangeGaugeWeight_barQ f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := h.isHiggsSector.barHiggsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_barQ f ![])
              (d' := h.isFermionSector.rangeGaugeWeight_u f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := h.isHiggsSector.barHiggsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_L f ![])
              (d' := h.isFermionSector.rangeGaugeWeight_bare f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := h.isHiggsSector.barHiggsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.rangeGaugeWeight_bare f ![])
              (d' := h.isFermionSector.rangeGaugeWeight_L f' ![]))).piece 0 := by
  have hprod : h.isHiggsSector.derivSubmodule 0
      * (h.isFermionSector.derivSubmodule 0 * h.isFermionSector.derivSubmodule 0)
      = ⨆ (f : Fin 3) (f' : Fin 3),
        (h.isHiggsSector.higgsSubmodule 0 ⊔ h.isHiggsSector.barHiggsSubmodule 0)
          * ((LinearMap.range (h.covD f ![]) ⊔
            LinearMap.range (h.covBarD f ![]) ⊔
            LinearMap.range (h.covU f ![]) ⊔
            LinearMap.range (h.covBarU f ![]) ⊔
            LinearMap.range (h.covQ f ![]) ⊔
            LinearMap.range (h.covBarQ f ![]) ⊔
            LinearMap.range (h.covL f ![]) ⊔
            LinearMap.range (h.covBarL f ![]) ⊔
            LinearMap.range (h.covE f ![]) ⊔
            LinearMap.range (h.covBarE f ![]))
            * (LinearMap.range (h.covD f' ![]) ⊔
            LinearMap.range (h.covBarD f' ![]) ⊔
            LinearMap.range (h.covU f' ![]) ⊔
            LinearMap.range (h.covBarU f' ![]) ⊔
            LinearMap.range (h.covQ f' ![]) ⊔
            LinearMap.range (h.covBarQ f' ![]) ⊔
            LinearMap.range (h.covL f' ![]) ⊔
            LinearMap.range (h.covBarL f' ![]) ⊔
            LinearMap.range (h.covE f' ![]) ⊔
            LinearMap.range (h.covBarE f' ![]))) := by
    rw [HiggsAlgebraCovRealization.derivSubmodule, h.isFermionSector.derivSubmodule_zero_eq,
      Submodule.iSup_mul, Submodule.mul_iSup]
    exact iSup_congr fun f => by rw [Submodule.mul_iSup, Submodule.mul_iSup]
  show (GaugeWeightDecomposition.mul (d := h.isHiggsSector.derivSubmoduleGaugeWeight 0)
      (d' := GaugeWeightDecomposition.mul
        (d := h.isFermionSector.derivSubmoduleGaugeWeight 0)
        (d' := h.isFermionSector.derivSubmoduleGaugeWeight 0))).piece 0 = _
  rw [GaugeWeightDecomposition.piece_congr
      (d := GaugeWeightDecomposition.mul (d := h.isHiggsSector.derivSubmoduleGaugeWeight 0)
        (d' := GaugeWeightDecomposition.mul
          (d := h.isFermionSector.derivSubmoduleGaugeWeight 0)
          (d' := h.isFermionSector.derivSubmoduleGaugeWeight 0)))
      (d' := GaugeWeightDecomposition.iSup h.repGauge_mul fun f =>
        GaugeWeightDecomposition.iSup h.repGauge_mul fun f' =>
          GaugeWeightDecomposition.mul
            (d := GaugeWeightDecomposition.sup
              (d := h.isHiggsSector.higgsSubmoduleGaugeWeight 0)
              (d' := h.isHiggsSector.barHiggsSubmoduleGaugeWeight 0))
            (d' := GaugeWeightDecomposition.mul
              (d := h.isFermionSector.speciesGaugeWeight f ![])
              (d' := h.isFermionSector.speciesGaugeWeight f' ![])))
      hprod 0]
  simp only [GaugeWeightDecomposition.piece_iSup, IsFermionSector.piece_sup_mul]
  refine iSup_congr fun f => iSup_congr fun f' => ?_
  rw [h.mul_speciesGaugeWeight_mul_piece_zero_neg_three
      (h.higgsSubmoduleGaugeWeight_hc 0) f f' ![] ![],
    h.mul_speciesGaugeWeight_mul_piece_zero_pos_three
      (h.barHiggsSubmoduleGaugeWeight_hc 0) f f' ![] ![]]
  ac_rfl

/-!

## G. Invariants modulo a gauge-stable submodule

A gauge-invariant element sits in the weight-zero piece, and the same holds modulo a
submodule `S` stable under the torus: an invariant lying in the sector joined with `S`
lies in the weight-zero piece joined with `S`.  This is what turns the twelve blocks of
section F into a statement about the invariants themselves, the remaining work being to
peel the blocks apart, which is not done here.

The statement is `GaugeWeightDecomposition.mem_piece_zero_sup_of_invariant`, whose
induction chooses the separating torus generator weight by weight.  That matters here: at
mass weight eight the sector carries weights of vanishing hypercharge and nonzero colour or
isospin — `H d bard` is one — so, unlike the fermion sector, no single generator sees every
weight.

-/

/-- A gauge-invariant element of the Yukawa sector at mass weight eight joined with a
  torus-stable `S` lies in the weight-zero piece joined with `S`, so the twelve blocks of
  `sectorMassWeightEightGaugeWeight_piece_zero` are all that a Yukawa invariant can be
  built from. -/
lemma mem_sectorMassWeightEight_piece_zero_sup_of_invariant {S : Submodule ℂ B}
    (hS : ∀ (i : Fin 4) (y : B), y ∈ S → repGauge (gaugeTorusGen i) y ∈ S) {x : B}
    (hx : x ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 8 ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    x ∈ h.sectorMassWeightEightGaugeWeight.piece 0 ⊔ S :=
  GaugeWeightDecomposition.mem_piece_zero_sup_of_invariant _ hS hx hinv

end CovAlgebraRealization

end StandardModel
