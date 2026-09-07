/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsHiggsSector.DerivSubmodule.Basic
/-!
# The mass-weight grading of the Higgs sector, in derivative submodules

The mass-weight submodules of the Higgs sector are described in
`IsHiggsSector.Basic` in terms of the Higgs and conjugate-Higgs submodules
separately.  Since the two always occur together, the description is cleaner in terms
of the derivative submodules `derivSubmodule n = higgsSubmodule n ⊔ barHiggsSubmodule n`:
a Higgs tower with `n` derivatives has weight `2 * (1 + n)`, only even weights are
non-zero, and the weights up to eight are the partitions of the weight into such
towers.

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

namespace IsHiggsSector

set_option linter.unusedVariables false

variable {B : Type} [Ring B] [Algebra ℂ B]
  {rep : Representation ℂ GaugeGroupI B}
  {hrep_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B), rep g (b₁ * b₂) = rep g b₁ * rep g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {H : (n : ℕ) → (Fin n → (Fin 1 ⊕ Fin 3)) → Module.Dual ℂ HiggsVec →ₗ[ℂ] B}
  {barH : (n : ℕ) → (Fin n → (Fin 1 ⊕ Fin 3)) →  Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsHiggsSector B rep hrep_mul repLorentz hrepLorentz_mul H barH
      massWeightPoly)

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

/-- Weight two is the underived Higgs symbols. -/
lemma massWeightSubmodule_two_eq_deriv :
    h.massWeightSubmodule 2 = h.derivSubmodule 0 :=
  h.massWeightSubmodule_two_eq

/-- Weight four. -/
lemma massWeightSubmodule_four_eq_deriv :
    h.massWeightSubmodule 4
      = h.derivSubmodule 1 ⊔ h.derivSubmodule 0 * h.derivSubmodule 0 := by
  rw [h.massWeightSubmodule_four_eq]
  simp only [derivSubmodule, Submodule.sup_mul, Submodule.mul_sup,
    h.barHiggsSubmodule_comm_higgsSubmodule 0 0]
  simp only [sup_assoc, sup_comm, sup_left_comm, sup_left_idem]

/-- Higgs and conjugate-Higgs submodules commute past a third factor. -/
lemma barHiggs_higgs_left_comm (n1 n2 : ℕ) (C : Submodule ℂ B) :
    h.barHiggsSubmodule n1 * (h.higgsSubmodule n2 * C)
      = h.higgsSubmodule n2 * (h.barHiggsSubmodule n1 * C) :=
  Commute.left_comm (h.barHiggsSubmodule_comm_higgsSubmodule n1 n2) C

set_option maxHeartbeats 2000000 in
/-- Weight six. -/
lemma massWeightSubmodule_six_eq_deriv :
    h.massWeightSubmodule 6
      = h.derivSubmodule 2 ⊔ h.derivSubmodule 1 * h.derivSubmodule 0
        ⊔ h.derivSubmodule 0 * h.derivSubmodule 0 * h.derivSubmodule 0 := by
  rw [h.massWeightSubmodule_six_eq]
  simp only [derivSubmodule, Submodule.sup_mul, Submodule.mul_sup,
    barHiggsSubmodule_comm_higgsSubmodule, mul_assoc, h.barHiggs_higgs_left_comm]
  simp only [sup_assoc, sup_comm, sup_left_comm, sup_left_idem]

set_option maxHeartbeats 4000000 in
/-- Weight eight. -/
lemma massWeightSubmodule_eight_eq_deriv :
    h.massWeightSubmodule 8
      = h.derivSubmodule 3 ⊔ h.derivSubmodule 2 * h.derivSubmodule 0
        ⊔ h.derivSubmodule 1 * h.derivSubmodule 1
        ⊔ h.derivSubmodule 1 * h.derivSubmodule 0 * h.derivSubmodule 0
        ⊔ h.derivSubmodule 0 * h.derivSubmodule 0 * h.derivSubmodule 0
          * h.derivSubmodule 0 := by
  rw [h.massWeightSubmodule_eight_eq]
  simp only [derivSubmodule, Submodule.sup_mul, Submodule.mul_sup,
    barHiggsSubmodule_comm_higgsSubmodule, mul_assoc, h.barHiggs_higgs_left_comm]
  simp only [sup_assoc, sup_comm, sup_left_comm, sup_left_idem]

end IsHiggsSector

end StandardModel
