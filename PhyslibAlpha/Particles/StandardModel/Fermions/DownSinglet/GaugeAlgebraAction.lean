/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.Fermions.DownSinglet.MatterField
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.LieAlgebra
public import PhyslibAlpha.Mathematics.TensorProductComm
/-!
# The infinitesimal gauge action on the down-type singlet

The explicit `(3, 1)_{-2}` action of the gauge algebra on the down-type singlet, and its agreement
with the matter field.

## i. Overview

The infinitesimal `(3, 1)_{-2}` action of the gauge algebra on the down-type singlet, its
compatibility with the Lorentz action, and its identification with the action of the gauge
algebra of the matter field `DownSinglet.matterField`.

## ii. Key results

- `DownSinglet.colourEnd` : the endomorphism of the down singlet defined by a `3 × 3` complex
  matrix acting on the colour index, with the Weyl factor untouched.
- `DownSinglet.actionMatrix` : the matrix of the infinitesimal action of a gauge algebra
  element.
- `DownSinglet.gaugeAlgebraAction` : the infinitesimal `(3, 1)_{-2}` action.
- `DownSinglet.gaugeAlgebraAction_comm_repLorentzGroup` : the gauge action commutes with the
  Lorentz action.
- `DownSinglet.matterField_repAlgebra_gaugeAlgebraEquiv` : the action of the gauge algebra
  of the matter field is `DownSinglet.gaugeAlgebraAction`.

## iii. Table of contents

- A. The action of the gauge algebra
- B. The gauge action commutes with the Lorentz action
- C. The matter field

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open GlobalGaugeGroup GlobalGaugeGroup.MatterField TensorProduct Matrix MatrixGroups

namespace DownSinglet

/-!

## A. The action of the gauge algebra

The infinitesimal `(3, 1)_{-2}` action of the gauge algebra on the down-type singlet:
the colour part of the algebra element acts on the colour index and the hypercharge
part scales, both through the physicists' factor of `i`, matching the group action
`(star u) ^ 2 • U₃` infinitesimally.

-/

/-- The endomorphism of the down singlet defined by a `3 × 3` complex matrix acting on
  the colour index, with the Weyl factor untouched. -/
noncomputable def colourEnd (A : Matrix (Fin 3) (Fin 3) ℂ) :
    DownSinglet →ₗ[ℂ] DownSinglet :=
  valLinEquiv.symm.toLinearMap ∘ₗ
    Module.End.lTensorAlgHom ℂ (EuclideanSpace ℂ (Fin 3)) Fermion.RightHandedWeyl
      (Matrix.toLpLinAlgEquiv 2 A) ∘ₗ valLinEquiv.toLinearMap

lemma colourEnd_apply_mk (A : Matrix (Fin 3) (Fin 3) ℂ) (v : DownSinglet) :
    colourEnd A v
      = valLinEquiv.symm
          (Module.End.lTensorAlgHom ℂ (EuclideanSpace ℂ (Fin 3)) Fermion.RightHandedWeyl
            (Matrix.toLpLinAlgEquiv 2 A) (valLinEquiv v)) := rfl

lemma colourEnd_add (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    colourEnd (A + B) = colourEnd A + colourEnd B := by
  rw [colourEnd, colourEnd, colourEnd, map_add, map_add, LinearMap.add_comp,
    LinearMap.comp_add]

lemma colourEnd_smul (z : ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    colourEnd (z • A) = z • colourEnd A := by
  rw [colourEnd, colourEnd, map_smul, map_smul, LinearMap.smul_comp,
    LinearMap.comp_smul]

/-- The matrix of the infinitesimal `(3, 1)_{-2}` action of a gauge algebra element on
  the colour index, `i` times the colour part shifted by `i` times `-2` the
  hypercharge. -/
noncomputable def actionMatrix (c : GaugeAlgebra) : Matrix (Fin 3) (Fin 3) ℂ :=
  Complex.I • (c.toSU3Matrix - ((2 : ℂ) • c.toU1Value) • 1)

/-- The infinitesimal action of the gauge algebra on the down-type singlet, the
  derivative of the `(3, 1)_{-2}` action of the gauge group, real-linear in the
  algebra slot and complex-linear in the value slot. -/
noncomputable def gaugeAlgebraAction :
    GaugeAlgebra →ₗ[ℝ] DownSinglet →ₗ[ℂ] DownSinglet where
  toFun c := colourEnd (actionMatrix c)
  map_add' c₁ c₂ := by
    rw [show actionMatrix (c₁ + c₂) = actionMatrix c₁ + actionMatrix c₂ from by
      rw [actionMatrix, actionMatrix, actionMatrix, GaugeAlgebra.add_toSU3Matrix,
        GaugeAlgebra.add_toU1Value]
      module]
    rw [colourEnd_add]
  map_smul' r c := by
    rw [show actionMatrix (r • c) = (r : ℂ) • actionMatrix c from by
      rw [actionMatrix, actionMatrix, GaugeAlgebra.smul_toSU3Matrix,
        GaugeAlgebra.smul_toU1Value,
        show (r • c.toSU3Matrix : Matrix (Fin 3) (Fin 3) ℂ)
          = (r : ℂ) • c.toSU3Matrix from by
        rw [← algebraMap_smul ℂ r c.toSU3Matrix]; rfl,
        show r • c.toU1Value = (r : ℂ) • c.toU1Value from by
        rw [← algebraMap_smul ℂ r c.toU1Value]; rfl]
      module,
      colourEnd_smul]
    refine LinearMap.ext fun v => ?_
    rw [RingHom.id_apply]
    show (r : ℂ) • colourEnd (actionMatrix c) v = r • colourEnd (actionMatrix c) v
    rw [show ((r : ℝ) : ℂ) = algebraMap ℝ ℂ r from rfl, algebraMap_smul]

/-!

## B. The gauge action commutes with the Lorentz action

-/

/-- The infinitesimal gauge action on the down-type singlet acts on the colour factor, the
  Lorentz action on the Weyl factor, so the two commute. -/
lemma gaugeAlgebraAction_comm_repLorentzGroup (c : GaugeAlgebra) (Λ : SL(2,ℂ))
    (v : DownSinglet) :
    DownSinglet.gaugeAlgebraAction c (DownSinglet.repLorentzGroup Λ v) =
      DownSinglet.repLorentzGroup Λ (DownSinglet.gaugeAlgebraAction c v) :=
  DownSinglet.valLinEquiv.injective
    (lTensor_map_id_comm _ (Fermion.RightHandedWeyl.rep Λ) (DownSinglet.valLinEquiv v))

/-!

## C. The matter field

-/

/-- The colour endomorphism of a matrix is the endomorphism of the matrix representation. -/
lemma colourEnd_eq_valEnd (A : Matrix (Fin 3) (Fin 3) ℂ) :
    colourEnd A = MatrixRep.valEnd tensorEquiv A := by
  have h : colourEnd A ∘ₗ tensorEquiv.symm.toLinearMap =
      MatrixRep.valEnd tensorEquiv A ∘ₗ tensorEquiv.symm.toLinearMap :=
    TensorProduct.ext' fun s w => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        MatrixRep.valEnd_apply_symm_tmul, tensorEquiv_symm_tmul, colourEnd_apply_mk,
        tensorEquiv_symm_tmul]
      rfl
  exact (LinearMap.cancel_right
    (show Function.Surjective tensorEquiv.symm.toLinearMap from tensorEquiv.symm.surjective)).1 h

/-- The action matrix of the matrix representation on `gaugeAlgebraEquiv c` is `actionMatrix c`. -/
lemma derivMat_gaugeRep_gaugeAlgebraEquiv (c : GaugeAlgebra) :
    derivMat gaugeRep (gaugeAlgebraEquiv c) = actionMatrix c := by
  show derivMat (MatrixRep.charge (-2) hypercharge su3Fund) (gaugeAlgebraEquiv c) = _
  rw [MatrixRep.derivMat_charge (-2) hypercharge su3Fund (z := Complex.I * c.toU1Value)
    (hypercharge_exp_gaugeAlgebraEquiv c), derivMat_su3Fund_gaugeAlgebraEquiv, actionMatrix]
  push_cast
  module

/-- The action of the gauge algebra of the matter field of the down-type singlet, on the
  image of `gaugeAlgebraEquiv`, is `gaugeAlgebraAction`. -/
lemma matterField_repAlgebra_gaugeAlgebraEquiv (c : GaugeAlgebra) :
    matterField.repAlgebra (gaugeAlgebraEquiv c) = gaugeAlgebraAction c := by
  rw [matterField_repAlgebra, derivMat_gaugeRep_gaugeAlgebraEquiv]
  exact (colourEnd_eq_valEnd _).symm

end DownSinglet

end StandardModel
