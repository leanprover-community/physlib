/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.YukawaSector.Basic
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.FermionSector.MassWeight.GaugeWeight
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.ScalarSector.DerivSubmodule.GaugeWeight
/-!
# The gauge weight decomposition of the Yukawa sector at mass weight eight

The gauge weight decomposition of the Yukawa sector of the Standard Model's covariant field algebra.

## i. Overview

Everything below is stated about the covariant field algebra `fieldData.LocalCovFieldAlgebra` of the
Standard Model.

Mass weight eight is where the Yukawa sector first has anything to say. By
`sectorMassWeight_higgs_fermion_eight` the whole sector at that weight is one Higgs
tower against two underived fermion towers, the weight of `H ψ ψ` itself.  Transporting
the gauge weight decompositions of the two sectors along that identification decomposes
the sector, and the question of which Yukawa couplings can exist becomes the question of
which pieces survive at gauge weight zero.

Almost none of them do, and the reason is hypercharge alone.  Writing `6Y` for the
normalisation used throughout, a symbol carries the contragredient of its value space and
so the negative of its charge. The Higgs symbols carry `-3` and their conjugates `+3`,
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

That is the whole content of this file. The surviving twelve are the Yukawa couplings
`H d barQ`, `H baru Q`, `H barL e`, `barH bard Q`, `barH u barQ`, `barH L bare` and their
transposes. The colour and isospin structure eliminates nothing further here. It only
decides which components inside a surviving block pair up, which is a later question.

## ii. Key results

- `sectorMassWeightEightGaugeWeight` : the gauge weight decomposition of the Yukawa sector at mass
  weight eight.
- `mul_speciesGaugeWeight_mul_piece_zero_neg_three`,
  `mul_speciesGaugeWeight_mul_piece_zero_pos_three` : the hypercharge sieve against a Higgs and a
  conjugate-Higgs symbol.
- `sectorMassWeightEightGaugeWeight_piece_zero` : the weight-zero piece, the twelve blocks that
  hypercharge allows.
- `mem_sectorMassWeightEight_piece_zero_sup_of_invariant` : a gauge invariant lies in the
  weight-zero piece modulo a torus-stable submodule.

## iii. Table of contents

- A. The sector at mass weight eight, decomposed
- B. Splitting a Higgs-fermion-fermion product along its joins
- C. Hypercharge adds across a product
- D. The two Higgs hypercharges
- E. The hypercharge sieve on two fermions against one Higgs
- F. The twelve surviving blocks
- G. Invariants modulo a gauge-stable submodule

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open GaugeFieldData (FieldKind)

open TensorProduct Matrix MatrixGroups Lorentz Pointwise

namespace LocalCovFieldAlgebra

/-!

## A. The sector at mass weight eight, decomposed

-/

/-- The gauge weight decomposition of the Yukawa sector at mass weight eight, transported
  along `sectorMassWeight_higgs_fermion_eight` from the product of the Higgs derivative
  submodule with two copies of the underived fermion towers. -/
@[implicit_reducible]
noncomputable def sectorMassWeightEightGaugeWeight :
    GaugeWeightDecomposition repGaugeGroupI
      (fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} 8) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.mul (d := ScalarSector.derivSubmoduleGaugeWeight 0)
      (d' := GaugeWeightDecomposition.mul
        (d := FermionSector.derivSubmoduleGaugeWeight 0)
        (d' := FermionSector.derivSubmoduleGaugeWeight 0)))
    _ LocalCovFieldAlgebra.sectorMassWeight_higgs_fermion_eight

/-!

## B. Splitting a Higgs-fermion-fermion product along its joins

The two fermion factors are each a join over ten species, so the product has to be
distributed over both before any species-level statement can be made.  The left factor is
handled by `FermionSector.piece_sup_mul`; the two lemmas here reach the inner factors of
a triple product, which that lemma cannot see.

-/

/-- If the first fermion factor of a triple product is a join `VA ⊔ VB`, its weight-`w`
  piece splits along the join. -/
lemma piece_mul_sup_mul {VX VA VB VZ : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    (dX : GaugeWeightDecomposition repGaugeGroupI VX) (dA : GaugeWeightDecomposition
      repGaugeGroupI VA)
    (dB : GaugeWeightDecomposition repGaugeGroupI VB) (dZ : GaugeWeightDecomposition
      repGaugeGroupI VZ)
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
lemma piece_mul_mul_sup {VX VY VA VB : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    (dX : GaugeWeightDecomposition repGaugeGroupI VX) (dY : GaugeWeightDecomposition
      repGaugeGroupI VY)
    (dA : GaugeWeightDecomposition repGaugeGroupI VA) (dB : GaugeWeightDecomposition
      repGaugeGroupI VB)
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

`FermionSector.mul_piece_zero_eq_bot_of_hypercharge` kills a product of two
decompositions whose constant hypercharges do not cancel.  To use it on a triple product
the two fermion factors have to be read as a single decomposition, and the only thing
needed about them is that their hypercharges add.

-/

/-- Two decompositions with constant hypercharge have a product of constant hypercharge,
  the sum of the two. The support of a product is the pointwise sum of the supports, and
  hypercharge is the fourth coordinate of a gauge weight. -/
lemma mul_supp_hypercharge {V V' : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    {dV : GaugeWeightDecomposition repGaugeGroupI V} {dV' : GaugeWeightDecomposition
      repGaugeGroupI V'}
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
  derivatives. The two weights in the support are `(0, 0, ∓1, -3)`. -/
lemma higgsSubmoduleGaugeWeight_hc (n : ℕ) :
    ∀ w ∈ (ScalarSector.higgsSubmoduleGaugeWeight n).supp, w.2.2.2 = -3 := by
  intro w hw
  have hw' : w ∈ ({((0, 0, -1, -3) : GaugeWeight), (0, 0, 1, -3)} : Finset GaugeWeight) := hw
  fin_cases hw' <;> rfl

/-- The conjugate-Higgs symbols carry hypercharge `3`, independent of isospin and of the
  number of derivatives. The two weights in the support are `(0, 0, ±1, 3)`. -/
lemma barHiggsSubmoduleGaugeWeight_hc (n : ℕ) :
    ∀ w ∈ (ScalarSector.barHiggsSubmoduleGaugeWeight n).supp, w.2.2.2 = 3 := by
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
Higgs and conjugate-Higgs cases are then two applications. No species pairs with itself,
`2f = ±3` having no integer solution.

-/

/-- A triple product of decompositions of constant hypercharges `h`, `a` and `b` has a nonzero
  weight-zero piece only if the three hypercharges cancel. -/
lemma mul_mul_piece_zero_eq_ite {V VA VB : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    {dV : GaugeWeightDecomposition repGaugeGroupI V}
    {dA : GaugeWeightDecomposition repGaugeGroupI VA}
    {dB : GaugeWeightDecomposition repGaugeGroupI VB} {h a b : ℤ}
    (hV : ∀ w ∈ dV.supp, w.2.2.2 = h) (hA : ∀ w ∈ dA.supp, w.2.2.2 = a)
    (hB : ∀ w ∈ dB.supp, w.2.2.2 = b) :
    (GaugeWeightDecomposition.mul (d := dV)
        (d' := GaugeWeightDecomposition.mul (d := dA) (d' := dB))).piece 0
      = if h + (a + b) = 0 then (GaugeWeightDecomposition.mul (d := dV)
          (d' := GaugeWeightDecomposition.mul (d := dA) (d' := dB))).piece 0 else ⊥ := by
  split_ifs with hne
  · rfl
  · exact FermionSector.mul_piece_zero_eq_bot_of_hypercharge hV (mul_supp_hypercharge hA hB) hne

/-- The weight-zero piece of a decomposition of constant hypercharge `h` against one of constant
  hypercharge `a` and the full symbol set of a family. Only the species whose hypercharge
  cancels `h + a` survive. -/
lemma mul_mul_speciesGaugeWeight_piece_zero {V VA : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    {dV : GaugeWeightDecomposition repGaugeGroupI V}
    {dA : GaugeWeightDecomposition repGaugeGroupI VA} {h a : ℤ}
    (hV : ∀ w ∈ dV.supp, w.2.2.2 = h) (hA : ∀ w ∈ dA.supp, w.2.2.2 = a)
    {m : ℕ} (f' : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) :
    (GaugeWeightDecomposition.mul (d := dV)
        (d' := GaugeWeightDecomposition.mul (d := dA)
          (d' := FermionSector.speciesGaugeWeight f' l'))).piece 0
      = (if h + (a + 2) = 0 then (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul (d := dA)
              (d' := FermionSector.rangeGaugeWeightD f' l'))).piece 0 else ⊥)
        ⊔ (if h + (a + -2) = 0 then (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul (d := dA)
              (d' := FermionSector.rangeGaugeWeightBarD f' l'))).piece 0 else ⊥)
        ⊔ (if h + (a + -4) = 0 then (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul (d := dA)
              (d' := FermionSector.rangeGaugeWeightU f' l'))).piece 0 else ⊥)
        ⊔ (if h + (a + 4) = 0 then (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul (d := dA)
              (d' := FermionSector.rangeGaugeWeightBarU f' l'))).piece 0 else ⊥)
        ⊔ (if h + (a + -1) = 0 then (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul (d := dA)
              (d' := FermionSector.rangeGaugeWeightQ f' l'))).piece 0 else ⊥)
        ⊔ (if h + (a + 1) = 0 then (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul (d := dA)
              (d' := FermionSector.rangeGaugeWeightBarQ f' l'))).piece 0 else ⊥)
        ⊔ (if h + (a + 3) = 0 then (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul (d := dA)
              (d' := FermionSector.rangeGaugeWeightL f' l'))).piece 0 else ⊥)
        ⊔ (if h + (a + -3) = 0 then (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul (d := dA)
              (d' := FermionSector.rangeGaugeWeightBarL f' l'))).piece 0 else ⊥)
        ⊔ (if h + (a + 6) = 0 then (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul (d := dA)
              (d' := FermionSector.rangeGaugeWeightE f' l'))).piece 0 else ⊥)
        ⊔ (if h + (a + -6) = 0 then (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul (d := dA)
              (d' := FermionSector.rangeGaugeWeightBarE f' l'))).piece 0 else ⊥) := by
  simp only [piece_mul_mul_sup]
  refine congrArg₂ (· ⊔ ·) (congrArg₂ (· ⊔ ·) (congrArg₂ (· ⊔ ·) (congrArg₂ (· ⊔ ·)
    (congrArg₂ (· ⊔ ·) (congrArg₂ (· ⊔ ·) (congrArg₂ (· ⊔ ·) (congrArg₂ (· ⊔ ·)
    (congrArg₂ (· ⊔ ·) ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  exacts [mul_mul_piece_zero_eq_ite hV hA (FermionSector.rangeGaugeWeightD_hc f' l'),
    mul_mul_piece_zero_eq_ite hV hA (FermionSector.rangeGaugeWeightBarD_hc f' l'),
    mul_mul_piece_zero_eq_ite hV hA (FermionSector.rangeGaugeWeightU_hc f' l'),
    mul_mul_piece_zero_eq_ite hV hA (FermionSector.rangeGaugeWeightBarU_hc f' l'),
    mul_mul_piece_zero_eq_ite hV hA (FermionSector.rangeGaugeWeightQ_hc f' l'),
    mul_mul_piece_zero_eq_ite hV hA (FermionSector.rangeGaugeWeightBarQ_hc f' l'),
    mul_mul_piece_zero_eq_ite hV hA (FermionSector.rangeGaugeWeightL_hc f' l'),
    mul_mul_piece_zero_eq_ite hV hA (FermionSector.rangeGaugeWeightBarL_hc f' l'),
    mul_mul_piece_zero_eq_ite hV hA (FermionSector.rangeGaugeWeightE_hc f' l'),
    mul_mul_piece_zero_eq_ite hV hA (FermionSector.rangeGaugeWeightBarE_hc f' l')]

open FermionSector in
/-- The hypercharge sieve against a Higgs symbol. If `dV` has constant hypercharge `-3`,
  as the Higgs symbols do, then of the hundred species pairings in a product of two fermion
  towers only the six whose hypercharges sum to `+3` survive at gauge weight zero, `d barQ`,
  `baru Q` and `barL e`, each in both orders. The other ninety-four pairings leave a nonzero
  hypercharge behind and so contribute nothing. -/
lemma mul_speciesGaugeWeight_mul_piece_zero_neg_three
    {V : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    {dV : GaugeWeightDecomposition repGaugeGroupI V} (hV : ∀ w ∈ dV.supp, w.2.2.2 =
      -3)
    {n m : ℕ} (f f' : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3)
    (l' : Fin m → Fin 1 ⊕ Fin 3) :
    (GaugeWeightDecomposition.mul (d := dV)
        (d' := GaugeWeightDecomposition.mul
          (d := FermionSector.speciesGaugeWeight f l)
          (d' := FermionSector.speciesGaugeWeight f' l'))).piece 0
      = (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightD f l)
              (d' := FermionSector.rangeGaugeWeightBarQ f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightBarQ f l)
              (d' := FermionSector.rangeGaugeWeightD f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightBarU f l)
              (d' := FermionSector.rangeGaugeWeightQ f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightQ f l)
              (d' := FermionSector.rangeGaugeWeightBarU f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightBarL f l)
              (d' := FermionSector.rangeGaugeWeightE f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightE f l)
              (d' := FermionSector.rangeGaugeWeightBarL f' l'))).piece 0 := by
  simp only [piece_mul_sup_mul,
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightD_hc f l),
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightBarD_hc f l),
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightU_hc f l),
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightBarU_hc f l),
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightQ_hc f l),
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightBarQ_hc f l),
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightL_hc f l),
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightBarL_hc f l),
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightE_hc f l),
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightBarE_hc f l),
    Int.reduceNeg, Int.reduceAdd, Int.reduceEq, ↓reduceIte, bot_sup_eq, sup_bot_eq]
  ac_rfl

open FermionSector in
/-- The hypercharge sieve against a conjugate-Higgs symbol. If `dV` has constant
  hypercharge `3`, as the conjugate-Higgs symbols do, then of the hundred species pairings
  only the six whose hypercharges sum to `-3` survive at gauge weight zero, `bard Q`,
  `u barQ` and `L bare`, each in both orders. -/
lemma mul_speciesGaugeWeight_mul_piece_zero_pos_three
    {V : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    {dV : GaugeWeightDecomposition repGaugeGroupI V} (hV : ∀ w ∈ dV.supp, w.2.2.2 = 3)
    {n m : ℕ} (f f' : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3)
    (l' : Fin m → Fin 1 ⊕ Fin 3) :
    (GaugeWeightDecomposition.mul (d := dV)
        (d' := GaugeWeightDecomposition.mul
          (d := FermionSector.speciesGaugeWeight f l)
          (d' := FermionSector.speciesGaugeWeight f' l'))).piece 0
      = (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightBarD f l)
              (d' := FermionSector.rangeGaugeWeightQ f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightQ f l)
              (d' := FermionSector.rangeGaugeWeightBarD f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightU f l)
              (d' := FermionSector.rangeGaugeWeightBarQ f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightBarQ f l)
              (d' := FermionSector.rangeGaugeWeightU f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightL f l)
              (d' := FermionSector.rangeGaugeWeightBarE f' l'))).piece 0
        ⊔ (GaugeWeightDecomposition.mul (d := dV)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightBarE f l)
              (d' := FermionSector.rangeGaugeWeightL f' l'))).piece 0 := by
  simp only [piece_mul_sup_mul,
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightD_hc f l),
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightBarD_hc f l),
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightU_hc f l),
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightBarU_hc f l),
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightQ_hc f l),
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightBarQ_hc f l),
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightL_hc f l),
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightBarL_hc f l),
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightE_hc f l),
    mul_mul_speciesGaugeWeight_piece_zero hV (FermionSector.rangeGaugeWeightBarE_hc f l),
    Int.reduceNeg, Int.reduceAdd, Int.reduceEq, ↓reduceIte, bot_sup_eq, sup_bot_eq]
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

/-- The Yukawa product at mass weight eight, an underived Higgs tower against two underived
  fermion towers, as a join over pairs of families. -/
lemma higgs_mul_fermion_mul_fermion_derivSubmodule_zero : ScalarSector.derivSubmodule 0
    * (FermionSector.derivSubmodule 0 * FermionSector.derivSubmodule 0)
    = ⨆ (f : Fin 3) (f' : Fin 3),
      (ScalarSector.higgsSubmodule 0 ⊔ ScalarSector.barHiggsSubmodule 0)
        * ((LinearMap.range (downSingletField f ![]) ⊔
          LinearMap.range (conjDownSingletField f ![]) ⊔
          LinearMap.range (upSingletField f ![]) ⊔
          LinearMap.range (conjUpSingletField f ![]) ⊔
          LinearMap.range (quarkDoubletField f ![]) ⊔
          LinearMap.range (conjQuarkDoubletField f ![]) ⊔
          LinearMap.range (leptonDoubletField f ![]) ⊔
          LinearMap.range (conjLeptonDoubletField f ![]) ⊔
          LinearMap.range (leptonSingletField f ![]) ⊔
          LinearMap.range (conjLeptonSingletField f ![]))
          * (LinearMap.range (downSingletField f' ![]) ⊔
          LinearMap.range (conjDownSingletField f' ![]) ⊔
          LinearMap.range (upSingletField f' ![]) ⊔
          LinearMap.range (conjUpSingletField f' ![]) ⊔
          LinearMap.range (quarkDoubletField f' ![]) ⊔
          LinearMap.range (conjQuarkDoubletField f' ![]) ⊔
          LinearMap.range (leptonDoubletField f' ![]) ⊔
          LinearMap.range (conjLeptonDoubletField f' ![]) ⊔
          LinearMap.range (leptonSingletField f' ![]) ⊔
          LinearMap.range (conjLeptonSingletField f' ![]))) := by
  rw [ScalarSector.derivSubmodule, FermionSector.derivSubmodule_zero_eq,
    Submodule.iSup_mul, Submodule.mul_iSup]
  exact iSup_congr fun f => by rw [Submodule.mul_iSup, Submodule.mul_iSup]

/-- The weight-zero piece of the Yukawa sector at mass weight eight, the join, over pairs
  of families, of the twelve blocks that hypercharge allows.  Of the two hundred ways of
  choosing one Higgs symbol and two fermion species, only these twelve have vanishing total
  hypercharge; the remaining one hundred and eighty-eight are killed by
  `mul_speciesGaugeWeight_mul_piece_zero_neg_three` and
  `mul_speciesGaugeWeight_mul_piece_zero_pos_three`. -/
lemma sectorMassWeightEightGaugeWeight_piece_zero :
    LocalCovFieldAlgebra.sectorMassWeightEightGaugeWeight.piece 0
      = ⨆ (f : Fin 3) (f' : Fin 3),
        (GaugeWeightDecomposition.mul
            (d := ScalarSector.higgsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightD f ![])
              (d' := FermionSector.rangeGaugeWeightBarQ f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := ScalarSector.higgsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightBarQ f ![])
              (d' := FermionSector.rangeGaugeWeightD f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := ScalarSector.higgsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightBarU f ![])
              (d' := FermionSector.rangeGaugeWeightQ f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := ScalarSector.higgsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightQ f ![])
              (d' := FermionSector.rangeGaugeWeightBarU f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := ScalarSector.higgsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightBarL f ![])
              (d' := FermionSector.rangeGaugeWeightE f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := ScalarSector.higgsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightE f ![])
              (d' := FermionSector.rangeGaugeWeightBarL f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := ScalarSector.barHiggsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightBarD f ![])
              (d' := FermionSector.rangeGaugeWeightQ f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := ScalarSector.barHiggsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightQ f ![])
              (d' := FermionSector.rangeGaugeWeightBarD f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := ScalarSector.barHiggsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightU f ![])
              (d' := FermionSector.rangeGaugeWeightBarQ f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := ScalarSector.barHiggsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightBarQ f ![])
              (d' := FermionSector.rangeGaugeWeightU f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := ScalarSector.barHiggsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightL f ![])
              (d' := FermionSector.rangeGaugeWeightBarE f' ![]))).piece 0
        ⊔ (GaugeWeightDecomposition.mul
            (d := ScalarSector.barHiggsSubmoduleGaugeWeight 0)
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.rangeGaugeWeightBarE f ![])
              (d' := FermionSector.rangeGaugeWeightL f' ![]))).piece 0 := by
  show (GaugeWeightDecomposition.mul (d := ScalarSector.derivSubmoduleGaugeWeight 0)
      (d' := GaugeWeightDecomposition.mul
        (d := FermionSector.derivSubmoduleGaugeWeight 0)
        (d' := FermionSector.derivSubmoduleGaugeWeight 0))).piece 0 = _
  rw [GaugeWeightDecomposition.piece_congr
      (d := GaugeWeightDecomposition.mul (d := ScalarSector.derivSubmoduleGaugeWeight 0)
        (d' := GaugeWeightDecomposition.mul
          (d := FermionSector.derivSubmoduleGaugeWeight 0)
          (d' := FermionSector.derivSubmoduleGaugeWeight 0)))
      (d' := GaugeWeightDecomposition.iSup repGaugeGroupI_mul fun f =>
        GaugeWeightDecomposition.iSup repGaugeGroupI_mul fun f' =>
          GaugeWeightDecomposition.mul
            (d := GaugeWeightDecomposition.sup
              (d := ScalarSector.higgsSubmoduleGaugeWeight 0)
              (d' := ScalarSector.barHiggsSubmoduleGaugeWeight 0))
            (d' := GaugeWeightDecomposition.mul
              (d := FermionSector.speciesGaugeWeight f ![])
              (d' := FermionSector.speciesGaugeWeight f' ![])))
      higgs_mul_fermion_mul_fermion_derivSubmodule_zero 0]
  simp only [GaugeWeightDecomposition.piece_iSup, FermionSector.piece_sup_mul]
  refine iSup_congr fun f => iSup_congr fun f' => ?_
  rw [LocalCovFieldAlgebra.mul_speciesGaugeWeight_mul_piece_zero_neg_three
      (LocalCovFieldAlgebra.higgsSubmoduleGaugeWeight_hc 0) f f' ![] ![],
    LocalCovFieldAlgebra.mul_speciesGaugeWeight_mul_piece_zero_pos_three
      (LocalCovFieldAlgebra.barHiggsSubmoduleGaugeWeight_hc 0) f f' ![] ![]]
  ac_rfl

/-!

## G. Invariants modulo a gauge-stable submodule

A gauge-invariant element sits in the weight-zero piece, and the same holds modulo a
submodule `S` stable under the torus: an invariant lying in the sector joined with `S`
lies in the weight-zero piece joined with `S`.  This is what turns the twelve blocks of
section F into a statement about the invariants themselves, the remaining work being to
peel the blocks apart, which is not done here.

The statement is `GaugeWeightDecomposition.mem_piece_zero_sup_of_invariant`, which chooses
the separating torus generator weight by weight.  That matters here: at
mass weight eight the sector carries weights of vanishing hypercharge and nonzero colour or
isospin — `H d bard` is one — so, unlike the fermion sector, no single generator sees every
weight.

-/

/-- A gauge-invariant element of the Yukawa sector at mass weight eight joined with a
  torus-stable `S` lies in the weight-zero piece joined with `S`, so the twelve blocks of
  `sectorMassWeightEightGaugeWeight_piece_zero` are all that a Yukawa invariant can be
  built from. -/
lemma mem_sectorMassWeightEight_piece_zero_sup_of_invariant
    {S : Submodule ℂ fieldData.LocalCovFieldAlgebra}
    (hS : ∀ (i : Fin 4) (y : fieldData.LocalCovFieldAlgebra), y ∈ S →
      repGaugeGroupI (gaugeTorusGen i) y ∈ S) {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} 8
      ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGaugeGroupI g x = x) :
    x ∈ LocalCovFieldAlgebra.sectorMassWeightEightGaugeWeight.piece 0 ⊔ S :=
  GaugeWeightDecomposition.mem_piece_zero_sup_of_invariant _ hS hx fun _ => hinv _

end LocalCovFieldAlgebra

end StandardModel
