/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.Fermions.LeptonDoublet.MatterField
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.LieAlgebra
/-!
# The infinitesimal gauge action on the lepton doublet

The explicit `(1, 2)_{-3}` action of the gauge algebra on the lepton doublet, and its agreement
with the matter field.

## i. Overview

In the infinitesimal `(1, 2)_{-3}` action of the gauge algebra on the lepton doublet, the
weak part of the algebra element acts on the weak index and the hypercharge part scales,
both through the physicists' factor of `i`, matching the group action
`(star u) ^ 3 • U₂` infinitesimally. This action is the action of the Lie algebra of the
global gauge group on the matter field of the lepton doublet, transported along
`StandardModel.gaugeAlgebraEquiv`, and it commutes with the Lorentz action.

## ii. Key results

- `weakEnd` : the endomorphism of the lepton doublet defined by a `2 × 2` matrix on the
  weak index.
- `gaugeAlgebraAction` : the infinitesimal `(1, 2)_{-3}` action of the gauge algebra.
- `matterField_repAlgebra_gaugeAlgebraEquiv` : the gauge-algebra action is the action of
  the matter field of the lepton doublet.
- `gaugeAlgebraAction_comm_repLorentzGroup` : the gauge action commutes with the Lorentz
  action.

## iii. Table of contents

- A. The action of the gauge algebra
- B. The action of the matter field
- C. The gauge action commutes with the Lorentz action

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open TensorProduct

namespace LeptonDoubletV

open GlobalGaugeGroup GlobalGaugeGroup.MatterField Matrix MatrixGroups

/-!

## A. The action of the gauge algebra

-/

/-- The endomorphism of the lepton doublet defined by a `2 × 2` complex matrix acting on
  the weak index, with the Weyl factor untouched. -/
noncomputable def weakEnd (A : Matrix (Fin 2) (Fin 2) ℂ) :
    LeptonDoubletV →ₗ[ℂ] LeptonDoubletV :=
  MatrixRep.valEnd tensorEquiv A

lemma weakEnd_add (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    weakEnd (A + B) = weakEnd A + weakEnd B :=
  MatrixRep.valEnd_add tensorEquiv A B

lemma weakEnd_smul (z : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    weakEnd (z • A) = z • weakEnd A :=
  MatrixRep.valEnd_smul tensorEquiv z A

/-- The matrix of the infinitesimal `(1, 2)_{-3}` action of a gauge algebra element on
  the weak index, `i` times the weak part shifted by `i` times `-3` the
  hypercharge. -/
noncomputable def actionMatrix (c : GaugeAlgebra) : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.I • (c.toSU2Matrix - ((3 : ℂ) • c.toU1Value) • 1)

/-- The infinitesimal action of the gauge algebra on the lepton doublet, the
  derivative of the `(1, 2)_{-3}` action of the gauge group, real-linear in the
  algebra slot and complex-linear in the value slot. -/
noncomputable def gaugeAlgebraAction :
    GaugeAlgebra →ₗ[ℝ] LeptonDoubletV →ₗ[ℂ] LeptonDoubletV where
  toFun c := weakEnd (actionMatrix c)
  map_add' c₁ c₂ := by
    rw [show actionMatrix (c₁ + c₂) = actionMatrix c₁ + actionMatrix c₂ from by
      rw [actionMatrix, actionMatrix, actionMatrix, GaugeAlgebra.add_toSU2Matrix,
        GaugeAlgebra.add_toU1Value]
      module]
    rw [weakEnd_add]
  map_smul' r c := by
    rw [show actionMatrix (r • c) = (r : ℂ) • actionMatrix c from by
      rw [actionMatrix, actionMatrix, GaugeAlgebra.smul_toSU2Matrix,
        GaugeAlgebra.smul_toU1Value,
        show (r • c.toSU2Matrix : Matrix (Fin 2) (Fin 2) ℂ)
          = (r : ℂ) • c.toSU2Matrix from by
        rw [← algebraMap_smul ℂ r c.toSU2Matrix]; rfl,
        show r • c.toU1Value = (r : ℂ) • c.toU1Value from by
        rw [← algebraMap_smul ℂ r c.toU1Value]; rfl]
      module,
      weakEnd_smul]
    refine LinearMap.ext fun v => ?_
    rw [RingHom.id_apply]
    show (r : ℂ) • weakEnd (actionMatrix c) v = r • weakEnd (actionMatrix c) v
    rw [show ((r : ℝ) : ℂ) = algebraMap ℝ ℂ r from rfl, algebraMap_smul]

/-!

## B. The action of the matter field

The action of the Lie algebra of the global gauge group on the matter field of the lepton
doublet is the gauge-algebra action, transported along `gaugeAlgebraEquiv`.

-/

/-- The action matrix of the gauge representation of the lepton doublet on the image of a gauge
  algebra element under `gaugeAlgebraEquiv` is the action matrix of the gauge algebra. -/
lemma derivMat_gaugeRep_gaugeAlgebraEquiv (c : GaugeAlgebra) :
    derivMat gaugeRep (gaugeAlgebraEquiv c) = actionMatrix c := by
  show derivMat (MatrixRep.charge (-3) hypercharge su2Fund) (gaugeAlgebraEquiv c) = _
  rw [MatrixRep.derivMat_charge (-3) hypercharge su2Fund (z := Complex.I * c.toU1Value)
    (hypercharge_exp_gaugeAlgebraEquiv c), derivMat_su2Fund_gaugeAlgebraEquiv, actionMatrix]
  push_cast
  module

/-- The action of the gauge algebra of the matter field of the lepton doublet, on the
  image of a gauge algebra element under `gaugeAlgebraEquiv`, is `gaugeAlgebraAction`. -/
lemma matterField_repAlgebra_gaugeAlgebraEquiv (c : GaugeAlgebra) :
    matterField.repAlgebra (gaugeAlgebraEquiv c) = gaugeAlgebraAction c := by
  rw [matterField_repAlgebra, derivMat_gaugeRep_gaugeAlgebraEquiv]
  rfl

/-!

## C. The gauge action commutes with the Lorentz action

-/

/-- The infinitesimal gauge action on the lepton doublet acts on the weak factor, the
  Lorentz action on the Weyl factor, so the two commute. -/
lemma gaugeAlgebraAction_comm_repLorentzGroup (c : GaugeAlgebra) (Λ : SL(2,ℂ))
    (v : LeptonDoubletV) :
    LeptonDoubletV.gaugeAlgebraAction c (LeptonDoubletV.repLorentzGroup Λ v) =
      LeptonDoubletV.repLorentzGroup Λ (LeptonDoubletV.gaugeAlgebraAction c v) := by
  rw [← matterField_repAlgebra_gaugeAlgebraEquiv]
  exact matterField_gaugeLorentzCommute.gaugeLorentzCompatible _ Λ v

end LeptonDoubletV

end StandardModel
