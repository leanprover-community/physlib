/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.HiggsBoson.MatterField
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.LieAlgebra
/-!
# The infinitesimal gauge action on the Higgs doublet

The explicit `(1, 2)_{3}` action of the gauge algebra on the Higgs doublet, and its agreement
with the matter field.

## i. Overview

The infinitesimal `(1, 2)_{3}` action of the gauge algebra on the Higgs doublet is written out
here in the form used by physicists. The weak part of the algebra element acts on the weak index
and the hypercharge part scales, both through the physicists' factor of `i`, matching the group
action `u ^ 3 • U₂` infinitesimally. Section B checks that this is the action of the Lie algebra
on the matter field `HiggsVec.matterField`, which is defined abstractly as the derivative of the
group action, transported along the Lie algebra isomorphism `gaugeAlgebraEquiv`.

## ii. Key results

- `StandardModel.HiggsVec.weakEnd` : the endomorphism of the Higgs doublet defined by a
  `2 × 2` matrix on the weak index.
- `StandardModel.HiggsVec.gaugeAlgebraAction` : the infinitesimal `(1, 2)_{3}` action of the
  gauge algebra.
- `StandardModel.HiggsVec.matterField_repAlgebra_gaugeAlgebraEquiv` : the action of the Lie
  algebra on the matter field of the Higgs, at the image of `c` under `gaugeAlgebraEquiv`, is
  `gaugeAlgebraAction c`.

## iii. Table of contents

- A. The action of the gauge algebra
- B. The action of the gauge algebra of the matter field

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open TensorProduct

namespace HiggsVec

open GlobalGaugeGroup Matrix MatrixGroups

/-!

## A. The action of the gauge algebra

-/

/-- The endomorphism of the Higgs doublet defined by a `2 × 2` complex matrix acting on
  the weak index. -/
noncomputable def weakEnd (A : Matrix (Fin 2) (Fin 2) ℂ) :
    HiggsVec →ₗ[ℂ] HiggsVec :=
  (Matrix.toLpLinAlgEquiv 2 A : Module.End ℂ HiggsVec)

/-- The weak endomorphism applies the matrix to the doublet. -/
lemma weakEnd_apply (A : Matrix (Fin 2) (Fin 2) ℂ) (v : HiggsVec) :
    weakEnd A v = Matrix.toLpLinAlgEquiv 2 A v := rfl

/-- The weak endomorphism is additive in the matrix. -/
lemma weakEnd_add (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    weakEnd (A + B) = weakEnd A + weakEnd B := by
  rw [weakEnd, weakEnd, weakEnd, map_add]

/-- The weak endomorphism is complex-linear in the matrix. -/
lemma weakEnd_smul (z : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    weakEnd (z • A) = z • weakEnd A := by
  rw [weakEnd, weakEnd, map_smul]

/-- The matrix of the infinitesimal `(1, 2)_{3}` action of a gauge algebra element on
  the weak index, `i` times the weak part shifted by `i` times `3` the hypercharge. -/
noncomputable def actionMatrix (c : GaugeAlgebra) : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.I • (c.toSU2Matrix + ((3 : ℂ) • c.toU1Value) • 1)

/-- The infinitesimal action of the gauge algebra on the Higgs doublet, the derivative of the
  `(1, 2)_{3}` action of the gauge group. It is real-linear in the algebra slot and
  complex-linear in the value slot. -/
noncomputable def gaugeAlgebraAction :
    GaugeAlgebra →ₗ[ℝ] HiggsVec →ₗ[ℂ] HiggsVec where
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

## B. The action of the gauge algebra of the matter field

-/

/-- The endomorphism of the Higgs doublet induced by a matrix on the internal index, through
  the identification `tensorEquiv`, is the weak endomorphism. -/
lemma valEnd_eq_weakEnd (A : Matrix (Fin 2) (Fin 2) ℂ) :
    MatrixRep.valEnd tensorEquiv A = weakEnd A := by
  refine LinearMap.ext fun (v : HiggsVec) => ?_
  have h1 : v = tensorEquiv.symm ((1 : ℂ) ⊗ₜ[ℂ] v.ofLp) := by
    apply tensorEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    simp [tensorEquiv]
  conv_lhs => rw [h1]
  rw [MatrixRep.valEnd_apply_symm_tmul]
  simp [tensorEquiv, weakEnd_apply]
  rfl

/-- The matrix of the action of the gauge algebra on the gauge representation of the Higgs,
  at the image of `c` under `gaugeAlgebraEquiv`, is `actionMatrix c`. -/
lemma derivMat_gaugeRep_gaugeAlgebraEquiv (c : GaugeAlgebra) :
    derivMat gaugeRep (gaugeAlgebraEquiv c) = actionMatrix c := by
  show derivMat (MatrixRep.charge (3) hypercharge su2Fund) (gaugeAlgebraEquiv c) = _
  rw [MatrixRep.derivMat_charge (3) hypercharge su2Fund (z := Complex.I * c.toU1Value)
    (hypercharge_exp_gaugeAlgebraEquiv c), derivMat_su2Fund_gaugeAlgebraEquiv, actionMatrix]
  push_cast
  module

/-- The action of the gauge algebra of the matter field of the Higgs, at the image of
  `c` under `gaugeAlgebraEquiv`, is `gaugeAlgebraAction c`. -/
lemma matterField_repAlgebra_gaugeAlgebraEquiv (c : GaugeAlgebra) :
    matterField.repAlgebra (gaugeAlgebraEquiv c) = gaugeAlgebraAction c := by
  rw [matterField_repAlgebra, derivMat_gaugeRep_gaugeAlgebraEquiv, valEnd_eq_weakEnd]
  rfl

end HiggsVec

end StandardModel
