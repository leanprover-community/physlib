/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.Fermions.LeptonSinglet.MatterField
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.LieAlgebra
/-!
# The infinitesimal gauge action on the charged-lepton singlet

The explicit `(1, 1)_{-6}` action of the gauge algebra on the charged-lepton singlet, and its
agreement with the matter field.

## i. Overview

The charged-lepton singlet carries the `(1, 1)_{-6}` representation of the gauge group,
so the infinitesimal action of the gauge algebra is scalar, multiplication by
`i` times `-6` times the `u(1)` value of the algebra element. This file defines that
action and identifies it with the action of the gauge algebra of the matter field of
the charged-lepton singlet, through the isomorphism of the gauge algebra with the Lie algebra
of the global gauge group.

## ii. Key results

- `gaugeAlgebraAction` : the infinitesimal `(1, 1)_{-6}` action of the gauge algebra.
- `matterField_repAlgebra_gaugeAlgebraEquiv` : the action of the gauge algebra of the
  matter field is `gaugeAlgebraAction`.
- `gaugeAlgebraAction_comm_repLorentzGroup` : the gauge action commutes with the Lorentz
  action.

## iii. Table of contents

- A. The infinitesimal action of the gauge algebra
- B. The action of the matter field
- C. The gauge action commutes with the Lorentz action

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

namespace LeptonSinglet

open GlobalGaugeGroup GlobalGaugeGroup.MatterField Matrix MatrixGroups TensorProduct

/-!

## A. The infinitesimal action of the gauge algebra

The `(1, 1)_{-6}` representation acts through the `u(1)` factor alone, so its
derivative is scalar multiplication by `i (-6)` times the `u(1)` value.

-/

/-- The infinitesimal action of the gauge algebra on the charged-lepton singlet, the derivative
  of the `(1, 1)_{-6}` action of the gauge group. It is scalar multiplication by `i` times `-6`
  times the `u(1)` value, real-linear in the algebra slot and complex-linear in the value
  slot. -/
noncomputable def gaugeAlgebraAction :
    GaugeAlgebra →ₗ[ℝ] LeptonSinglet →ₗ[ℂ] LeptonSinglet where
  toFun c := (Complex.I * (-(6 : ℂ) * c.toU1Value))
    • (LinearMap.id : LeptonSinglet →ₗ[ℂ] LeptonSinglet)
  map_add' c₁ c₂ := by
    rw [GaugeAlgebra.add_toU1Value,
      show Complex.I * (-(6 : ℂ) * (c₁.toU1Value + c₂.toU1Value))
          = Complex.I * (-(6 : ℂ) * c₁.toU1Value)
            + Complex.I * (-(6 : ℂ) * c₂.toU1Value) from by ring,
      add_smul]
  map_smul' r c := by
    rw [GaugeAlgebra.smul_toU1Value, RingHom.id_apply,
      show r • c.toU1Value = algebraMap ℝ ℂ r * c.toU1Value from by
        rw [← algebraMap_smul ℂ r c.toU1Value, smul_eq_mul],
      show Complex.I * (-(6 : ℂ) * (algebraMap ℝ ℂ r * c.toU1Value))
          = algebraMap ℝ ℂ r * (Complex.I * (-(6 : ℂ) * c.toU1Value)) from by ring,
      mul_smul, algebraMap_smul]

/-- The gauge-algebra action on the charged-lepton singlet is scalar multiplication
  by `i` times `-6` times the `u(1)` value. -/
lemma gaugeAlgebraAction_apply (c : GaugeAlgebra) :
    gaugeAlgebraAction c
      = (Complex.I * (-(6 : ℂ) * c.toU1Value))
        • (LinearMap.id : LeptonSinglet →ₗ[ℂ] LeptonSinglet) := rfl

/-!

## B. The action of the matter field

-/

/-- The action of the gauge algebra of the matter field of the charged-lepton singlet,
  evaluated on the image of a gauge algebra element, is `gaugeAlgebraAction`. -/
lemma matterField_repAlgebra_gaugeAlgebraEquiv (c : GaugeAlgebra) :
    matterField.repAlgebra (gaugeAlgebraEquiv c) = gaugeAlgebraAction c := by
  rw [matterField_repAlgebra]
  have hact : derivMat gaugeRep (gaugeAlgebraEquiv c) =
      (Complex.I * (-(6 : ℂ) * c.toU1Value)) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    show derivMat (MatrixRep.charge (-6) hypercharge MatrixRep.trivial) (gaugeAlgebraEquiv c) = _
    rw [MatrixRep.derivMat_charge (-6) hypercharge MatrixRep.trivial
      (z := Complex.I * c.toU1Value) (hypercharge_exp_gaugeAlgebraEquiv c),
      MatrixRep.derivMat_trivial, zero_add]
    congr 1
    push_cast
    ring
  rw [hact, MatrixRep.valEnd_smul, MatrixRep.valEnd_one, gaugeAlgebraAction_apply]

/-!

## C. The gauge action commutes with the Lorentz action

-/

/-- The infinitesimal gauge action on the charged-lepton singlet is a scalar, so it
  commutes with the Lorentz action. -/
lemma gaugeAlgebraAction_comm_repLorentzGroup (c : GaugeAlgebra) (Λ : SL(2,ℂ))
    (v : LeptonSinglet) :
    LeptonSinglet.gaugeAlgebraAction c (LeptonSinglet.repLorentzGroup Λ v) =
      LeptonSinglet.repLorentzGroup Λ (LeptonSinglet.gaugeAlgebraAction c v) := by
  show (Complex.I * (-(6 : ℂ) * c.toU1Value)) • (LeptonSinglet.repLorentzGroup Λ v) =
    LeptonSinglet.repLorentzGroup Λ ((Complex.I * (-(6 : ℂ) * c.toU1Value)) • v)
  rw [map_smul]

end LeptonSinglet

end StandardModel
