/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.Fermions.UpSinglet.Basic
public import PhyslibAlpha.Mathematics.TensorProductComm
public import PhyslibAlpha.Particles.StandardModel.Fermions.UpSinglet.MatterField
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.LieAlgebra
/-!
# The infinitesimal gauge action on the up-type singlet

The explicit `(3, 1)_{4}` action of the gauge algebra on the up-type singlet, and its agreement
with the matter field.

## i. Overview

The `(3, 1)_{4}` action of the gauge algebra on the up-type singlet. The colour part of
the algebra element acts on the colour index and the hypercharge part scales, both
through the physicists' factor of `i`, matching the group action `u ^ 4 • U₃`
infinitesimally. This action is the action of the gauge algebra of the matter field
`UpSinglet.matterField`, transported along `gaugeAlgebraEquiv`, and it commutes with
the Lorentz action.

## ii. Key results

- `colourEnd` : the endomorphism of the up singlet defined by a colour matrix.
- `gaugeAlgebraAction` : the infinitesimal `(3, 1)_{4}` action of the gauge algebra.
- `matterField_repAlgebra_gaugeAlgebraEquiv` : the gauge algebra action of the matrix
  matter field is `gaugeAlgebraAction`.
- `gaugeAlgebraAction_comm_repLorentzGroup` : the gauge action commutes with the Lorentz
  action.

## iii. Table of contents

- A. The action of the gauge algebra
- B. Comparison with the matter field
- C. The gauge action commutes with the Lorentz action

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open TensorProduct

namespace UpSinglet

open Matrix MatrixGroups GlobalGaugeGroup

/-!

## A. The action of the gauge algebra

-/

/-- The endomorphism of the up singlet defined by a `3 × 3` complex matrix acting on
  the colour index, with the Weyl factor untouched. -/
noncomputable def colourEnd (A : Matrix (Fin 3) (Fin 3) ℂ) :
    UpSinglet →ₗ[ℂ] UpSinglet :=
  valLinEquiv.symm.toLinearMap ∘ₗ
    Module.End.lTensorAlgHom ℂ (EuclideanSpace ℂ (Fin 3)) Fermion.RightHandedWeyl
      (Matrix.toLpLinAlgEquiv 2 A) ∘ₗ valLinEquiv.toLinearMap

lemma colourEnd_apply_mk (A : Matrix (Fin 3) (Fin 3) ℂ) (v : UpSinglet) :
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

/-- The matrix of the infinitesimal `(3, 1)_{4}` action of a gauge algebra element on
  the colour index, `i` times the colour part shifted by `i` times `4` the
  hypercharge. -/
noncomputable def actionMatrix (c : GaugeAlgebra) : Matrix (Fin 3) (Fin 3) ℂ :=
  Complex.I • (c.toSU3Matrix + ((4 : ℂ) • c.toU1Value) • 1)

/-- The infinitesimal action of the gauge algebra on the up-type singlet, the
  derivative of the `(3, 1)_{4}` action of the gauge group, real-linear in the
  algebra slot and complex-linear in the value slot. -/
noncomputable def gaugeAlgebraAction :
    GaugeAlgebra →ₗ[ℝ] UpSinglet →ₗ[ℂ] UpSinglet where
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

## B. Comparison with the matter field

-/

/-- The colour endomorphism of a matrix is the endomorphism of the matrix representation
  picture `tensorEquiv`. -/
lemma colourEnd_eq_valEnd (B : Matrix (Fin 3) (Fin 3) ℂ) :
    colourEnd B = MatrixRep.valEnd tensorEquiv B := by
  have h : colourEnd B ∘ₗ tensorEquiv.symm.toLinearMap =
      MatrixRep.valEnd tensorEquiv B ∘ₗ tensorEquiv.symm.toLinearMap :=
    TensorProduct.ext' fun s w => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        MatrixRep.valEnd_apply_symm_tmul, tensorEquiv_symm_tmul]
      refine valLinEquiv.injective ?_
      rw [colourEnd_apply_mk, LinearEquiv.apply_symm_apply]
      rfl
  refine LinearMap.ext fun (v : UpSinglet) => ?_
  have h' := LinearMap.congr_fun h (tensorEquiv v)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h'
  exact h'

/-- The action of the gauge algebra of the matter field of the up-type singlet, on the
  image of `gaugeAlgebraEquiv`, is `gaugeAlgebraAction`. -/
lemma matterField_repAlgebra_gaugeAlgebraEquiv (c : GaugeAlgebra) :
    matterField.repAlgebra (gaugeAlgebraEquiv c) = gaugeAlgebraAction c := by
  rw [matterField_repAlgebra, ← colourEnd_eq_valEnd]
  show colourEnd _ = colourEnd (actionMatrix c)
  congr 1
  show derivMat (MatrixRep.charge (4) hypercharge su3Fund) (gaugeAlgebraEquiv c) = _
  rw [MatrixRep.derivMat_charge (4) hypercharge su3Fund (z := Complex.I * c.toU1Value)
    (hypercharge_exp_gaugeAlgebraEquiv c), derivMat_su3Fund_gaugeAlgebraEquiv, actionMatrix]
  push_cast
  module

/-!

## C. The gauge action commutes with the Lorentz action

-/

/-- The infinitesimal gauge action on the up-type singlet acts on the colour factor, the
  Lorentz action on the Weyl factor, so the two commute. -/
lemma gaugeAlgebraAction_comm_repLorentzGroup (c : GaugeAlgebra) (Λ : SL(2,ℂ))
    (v : UpSinglet) :
    UpSinglet.gaugeAlgebraAction c (UpSinglet.repLorentzGroup Λ v) =
      UpSinglet.repLorentzGroup Λ (UpSinglet.gaugeAlgebraAction c v) :=
  UpSinglet.valLinEquiv.injective
    (lTensor_map_id_comm _ (Fermion.RightHandedWeyl.rep Λ) (UpSinglet.valLinEquiv v))

end UpSinglet

end StandardModel
