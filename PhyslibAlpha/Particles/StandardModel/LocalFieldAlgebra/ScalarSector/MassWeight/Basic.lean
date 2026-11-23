/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.ScalarSector.DerivSubmodule.Basic
/-!
# The mass-weight grading of the scalar sector, in derivative submodules

The mass-weight submodules of the scalar sector up to weight eight, written with the derivative
submodules.

## i. Overview

The mass-weight submodules of the scalar sector are described in
`ScalarSector/Basic.lean` in terms of the Higgs and conjugate-Higgs submodules
separately. Since the two always occur together, the description is cleaner in terms
of the derivative submodules `derivSubmodule n = higgsSubmodule n ⊔ barHiggsSubmodule n`.
A Higgs tower with `n` derivatives has mass weight `2 * (1 + n)`, twice its mass dimension
`1 + n`, only even weights are non-zero, and the mass weights up to eight (mass dimension
at most four) are the partitions of the weight into such towers.

## ii. Key results

- `derivSubmodule_le_massWeightSubmodule` : the derivative submodule sits in the mass-weight
  submodule of weight `2 * (1 + n)`.
- `massWeightSubmodule_eq_iSup_derivSubmodule_mul` : removing the leftmost Higgs tower, a term
  of positive weight `w` is a sum of products of a tower `derivSubmodule n`, of weight
  `2 * (1 + n) ≤ w`, with a term of the remaining weight.
- `massWeightSubmodule_two_eq_deriv` up to `massWeightSubmodule_eight_eq_deriv` : the mass
  weights up to eight.

## iii. Table of contents

- A. The mass-weight grading in derivative submodules

## iv. References

* None.

-/

/-!

## A. The mass-weight grading in derivative submodules

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz
open LocalCovFieldAlgebra (repGaugeGroupI repLorentzGroup massWeightPoly)

namespace ScalarSector

/-- The derivative submodule sits in the mass-weight submodule of weight `2 * (1 + n)`. -/
lemma derivSubmodule_le_massWeightSubmodule (n : ℕ) :
    derivSubmodule n ≤ massWeightSubmodule (2 * (1 + n)) :=
  sup_le (massWeightSubmodule_higgsSubmodule_le n)
    (massWeightSubmodule_barHiggsSubmodule_le n)

/-- Removing the leftmost Higgs tower, written with the derivative submodules. A term of
  positive weight `w` is a sum of products of a tower `derivSubmodule n`, of weight
  `2 * (1 + n) ≤ w`, with a term of the remaining weight. -/
lemma massWeightSubmodule_eq_iSup_derivSubmodule_mul (w : ℕ) (hw : 0 < w) :
    massWeightSubmodule w
      = ⨆ n ∈ (Finset.range (w + 1)).filter (fun n => 2 * (1 + n) ≤ w),
          derivSubmodule n * massWeightSubmodule (w - 2 * (1 + n)) :=
  massWeightSubmodule_eq_iSup_mul w hw

/-- Weight two is the underived Higgs symbols. -/
lemma massWeightSubmodule_two_eq_deriv :
    massWeightSubmodule 2 = derivSubmodule 0 :=
  massWeightSubmodule_two_eq

/-- Weight four. The leftmost tower is underived, leaving weight two, which is an underived
  tower, or once-derived, leaving weight zero. -/
lemma massWeightSubmodule_four_eq_deriv :
    massWeightSubmodule 4
      = derivSubmodule 1 ⊔ derivSubmodule 0 * derivSubmodule 0 := by
  rw [massWeightSubmodule_eq_iSup_derivSubmodule_mul 4 (by decide),
    show (Finset.range 5).filter (fun n => 2 * (1 + n) ≤ 4) = {0, 1} from by decide,
    Finset.iSup_insert, Finset.iSup_singleton]
  simp [massWeightSubmodule_two_eq_deriv, massWeightSubmodule_zero_eq, sup_comm]

/-- Weight six. The leftmost tower leaves weight four, two or zero. The product of an
  underived tower with a once-derived one occurs in both orders, which agree by
  `derivSubmodule_mul_comm`. -/
lemma massWeightSubmodule_six_eq_deriv :
    massWeightSubmodule 6
      = derivSubmodule 2 ⊔ derivSubmodule 1 * derivSubmodule 0
        ⊔ derivSubmodule 0 * derivSubmodule 0 * derivSubmodule 0 := by
  rw [massWeightSubmodule_eq_iSup_derivSubmodule_mul 6 (by decide),
    show (Finset.range 7).filter (fun n => 2 * (1 + n) ≤ 6) = {0, 1, 2} from by decide,
    Finset.iSup_insert, Finset.iSup_insert, Finset.iSup_singleton]
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, massWeightSubmodule_four_eq_deriv,
    massWeightSubmodule_two_eq_deriv, massWeightSubmodule_zero_eq, mul_one,
    Submodule.mul_sup, mul_assoc, derivSubmodule_mul_comm 0 1]
  -- the products are atoms for the final reordering of the join
  generalize derivSubmodule 2 = v1, derivSubmodule 1 * derivSubmodule 0 = v2,
    derivSubmodule 0 * (derivSubmodule 0 * derivSubmodule 0) = v3
  simp only [sup_comm, sup_left_comm, sup_left_idem]

/-- Weight eight. The leftmost tower leaves weight six, four, two or zero. Products that
  differ only in the order of commuting towers agree by `derivSubmodule_mul_comm`. -/
lemma massWeightSubmodule_eight_eq_deriv :
    massWeightSubmodule 8
      = derivSubmodule 3 ⊔ derivSubmodule 2 * derivSubmodule 0
        ⊔ derivSubmodule 1 * derivSubmodule 1
        ⊔ derivSubmodule 1 * derivSubmodule 0 * derivSubmodule 0
        ⊔ derivSubmodule 0 * derivSubmodule 0 * derivSubmodule 0
          * derivSubmodule 0 := by
  rw [massWeightSubmodule_eq_iSup_derivSubmodule_mul 8 (by decide),
    show (Finset.range 9).filter (fun n => 2 * (1 + n) ≤ 8) = {0, 1, 2, 3} from by decide,
    Finset.iSup_insert, Finset.iSup_insert, Finset.iSup_insert, Finset.iSup_singleton]
  have hlc (C : Submodule ℂ fieldData.LocalCovFieldAlgebra) :
      derivSubmodule 0 * (derivSubmodule 1 * C) = derivSubmodule 1 * (derivSubmodule 0 * C) :=
    Commute.left_comm (derivSubmodule_mul_comm 0 1) C
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, massWeightSubmodule_six_eq_deriv,
    massWeightSubmodule_four_eq_deriv, massWeightSubmodule_two_eq_deriv,
    massWeightSubmodule_zero_eq, mul_one, Submodule.mul_sup, mul_assoc, hlc,
    derivSubmodule_mul_comm 0 2]
  -- the products are atoms for the final reordering of the join
  generalize derivSubmodule 3 = v1, derivSubmodule 2 * derivSubmodule 0 = v2,
    derivSubmodule 1 * derivSubmodule 1 = v3,
    derivSubmodule 1 * (derivSubmodule 0 * derivSubmodule 0) = v4,
    derivSubmodule 0 * (derivSubmodule 0 * (derivSubmodule 0 * derivSubmodule 0)) = v5
  simp only [sup_comm, sup_left_comm, sup_left_idem]

end ScalarSector

end StandardModel
