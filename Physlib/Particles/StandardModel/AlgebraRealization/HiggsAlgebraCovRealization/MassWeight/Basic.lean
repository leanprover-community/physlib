/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.AlgebraRealization.HiggsAlgebraCovRealization.DerivSubmodule.Basic
/-!
# The mass-weight grading of the Higgs sector, in derivative submodules

The mass-weight submodules of the Higgs sector are described in
`HiggsAlgebraCovRealization.Basic` in terms of the Higgs and conjugate-Higgs submodules
separately.  Since the two always occur together, the description is cleaner in terms
of the derivative submodules `derivSubmodule n = higgsSubmodule n ⊔ barHiggsSubmodule n`:
a Higgs tower with `n` derivatives has mass weight `2 * (1 + n)`, twice its mass dimension
`1 + n`, only even weights are non-zero, and the mass weights up to eight (mass dimension
at most four) are the partitions of the weight into such towers.

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

namespace HiggsAlgebraCovRealization

set_option linter.unusedVariables false

variable {B : Type} [Ring B] [Algebra ℂ B]
  {rep : Representation ℂ GaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : HiggsAlgebraCovRealization B rep repLorentz massWeightPoly)

/-- The derivative submodule sits in the mass-weight submodule of weight `2 * (1 + n)`. -/
lemma derivSubmodule_le_massWeightSubmodule (n : ℕ) :
    h.derivSubmodule n ≤ h.massWeightSubmodule (2 * (1 + n)) :=
  sup_le (h.massWeightSubmodule_higgsSubmodule_le n)
    (h.massWeightSubmodule_barHiggsSubmodule_le n)

/-- The weight recursion, with the single-symbol part written as a derivative
  submodule. -/
lemma massWeightSubmodule_eq_derivSubmodule (i : ℕ) (hi : 0 < i) :
    h.massWeightSubmodule i
      = (⨆ k ∈ Finset.univ.filter (fun k : Fin i => 2 * (1 + (k : ℕ)) = i),
          h.derivSubmodule (k : ℕ))
        ⊔ (⨆ p ∈ Finset.univ.filter (fun p : Fin i × Fin i => (p.1 : ℕ) + (p.2 : ℕ) = i),
            h.massWeightSubmodule (p.1 : ℕ) * h.massWeightSubmodule (p.2 : ℕ)) :=
  h.massWeightSubmodule_eq i hi

/-- Removing the leftmost Higgs tower, written with the derivative submodules: a term of
  positive weight `w` is a sum of products of a tower `derivSubmodule n`, of weight
  `2 * (1 + n) ≤ w`, with a term of the remaining weight. -/
lemma massWeightSubmodule_eq_iSup_derivSubmodule_mul (w : ℕ) (hw : 0 < w) :
    h.massWeightSubmodule w
      = ⨆ n ∈ (Finset.range (w + 1)).filter (fun n => 2 * (1 + n) ≤ w),
          h.derivSubmodule n * h.massWeightSubmodule (w - 2 * (1 + n)) :=
  h.massWeightSubmodule_eq_iSup_mul w hw

/-- Weight two is the underived Higgs symbols. -/
lemma massWeightSubmodule_two_eq_deriv :
    h.massWeightSubmodule 2 = h.derivSubmodule 0 :=
  h.massWeightSubmodule_two_eq

/-- Weight four: the leftmost tower is underived, leaving weight two, which is an underived
  tower, or once-derived, leaving weight zero. -/
lemma massWeightSubmodule_four_eq_deriv :
    h.massWeightSubmodule 4
      = h.derivSubmodule 1 ⊔ h.derivSubmodule 0 * h.derivSubmodule 0 := by
  rw [h.massWeightSubmodule_eq_iSup_derivSubmodule_mul 4 (by decide),
    show (Finset.range 5).filter (fun n => 2 * (1 + n) ≤ 4) = {0, 1} from by decide,
    Finset.iSup_insert, Finset.iSup_singleton]
  simp [h.massWeightSubmodule_two_eq_deriv, h.massWeightSubmodule_zero_eq, sup_comm]

/-- Weight six: the leftmost tower leaves weight four, two or zero. The product of an
  underived tower with a once-derived one occurs in both orders, which agree by
  `derivSubmodule_mul_comm`. -/
lemma massWeightSubmodule_six_eq_deriv :
    h.massWeightSubmodule 6
      = h.derivSubmodule 2 ⊔ h.derivSubmodule 1 * h.derivSubmodule 0
        ⊔ h.derivSubmodule 0 * h.derivSubmodule 0 * h.derivSubmodule 0 := by
  rw [h.massWeightSubmodule_eq_iSup_derivSubmodule_mul 6 (by decide),
    show (Finset.range 7).filter (fun n => 2 * (1 + n) ≤ 6) = {0, 1, 2} from by decide,
    Finset.iSup_insert, Finset.iSup_insert, Finset.iSup_singleton]
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, h.massWeightSubmodule_four_eq_deriv,
    h.massWeightSubmodule_two_eq_deriv, h.massWeightSubmodule_zero_eq, mul_one,
    Submodule.mul_sup, mul_assoc, h.derivSubmodule_mul_comm 0 1]
  simp only [sup_assoc, sup_comm, sup_left_comm, sup_left_idem]

/-- Weight eight: the leftmost tower leaves weight six, four, two or zero. Products that
  differ only in the order of commuting towers agree by `derivSubmodule_mul_comm`. -/
lemma massWeightSubmodule_eight_eq_deriv :
    h.massWeightSubmodule 8
      = h.derivSubmodule 3 ⊔ h.derivSubmodule 2 * h.derivSubmodule 0
        ⊔ h.derivSubmodule 1 * h.derivSubmodule 1
        ⊔ h.derivSubmodule 1 * h.derivSubmodule 0 * h.derivSubmodule 0
        ⊔ h.derivSubmodule 0 * h.derivSubmodule 0 * h.derivSubmodule 0
          * h.derivSubmodule 0 := by
  rw [h.massWeightSubmodule_eq_iSup_derivSubmodule_mul 8 (by decide),
    show (Finset.range 9).filter (fun n => 2 * (1 + n) ≤ 8) = {0, 1, 2, 3} from by decide,
    Finset.iSup_insert, Finset.iSup_insert, Finset.iSup_insert, Finset.iSup_singleton]
  have hlc (C : Submodule ℂ B) : h.derivSubmodule 0 * (h.derivSubmodule 1 * C)
      = h.derivSubmodule 1 * (h.derivSubmodule 0 * C) :=
    Commute.left_comm (h.derivSubmodule_mul_comm 0 1) C
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, h.massWeightSubmodule_six_eq_deriv,
    h.massWeightSubmodule_four_eq_deriv, h.massWeightSubmodule_two_eq_deriv,
    h.massWeightSubmodule_zero_eq, mul_one, Submodule.mul_sup, mul_assoc, hlc,
    h.derivSubmodule_mul_comm 0 2]
  simp only [sup_assoc, sup_comm, sup_left_comm, sup_left_idem]

end HiggsAlgebraCovRealization

end StandardModel
