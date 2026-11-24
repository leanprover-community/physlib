/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.HiggsBoson.Basic
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.GlobalGaugeGroup
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.InfinitesimalAction
/-!
# The Higgs field as a matter field

The Higgs doublet `(1, 2)_{3}` as a matter field of the Standard Model global gauge group.

## i. Overview

The target space `HiggsVec` is the Euclidean space `ℂ²`, already normed. The Higgs is a Lorentz
scalar, so its Lorentz representation is the trivial one on `ℂ`. The global gauge group acts on
it by the fundamental representation of the `SU(2)` block, twisted by the power `3` of the
hypercharge phase. This is the charge `3` twist of the fundamental representation of `SU(2)`,
which gives a bosonic matter field of mass weight two. Its action of the global gauge group, on
the image of `StandardModel.gaugeGroupEquiv`, is the existing action
`StandardModel.HiggsVec.repGaugeGroupI`.

## ii. Key results

- `StandardModel.HiggsVec.matterField` : the Higgs as a matter field of
  `StandardModel.globalGaugeGroup`.
- `StandardModel.HiggsVec.matterField_repAlgebra` : its action of the gauge algebra.
- `StandardModel.HiggsVec.matterField_rep_gaugeGroupEquiv` : its action of the gauge
  group is `StandardModel.HiggsVec.repGaugeGroupI`.
- `StandardModel.HiggsVec.matterField_lorentzContinuous`,
  `StandardModel.HiggsVec.matterField_gaugeLorentzCommute` : its Lorentz action is continuous and
  commutes with its gauge action.

## iii. Table of contents

- A. The gauge representation
- B. The matter field

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel.HiggsVec

open GlobalGaugeGroup GlobalGaugeGroup.MatterField Matrix MatrixGroups TensorProduct

/-!

## A. The gauge representation

-/

/-- The Higgs vectors as a Lorentz scalar valued in `ℂ ⊗ ℂ²`. -/
noncomputable def tensorEquiv : HiggsVec ≃ₗ[ℂ] ℂ ⊗[ℂ] (Fin 2 → ℂ) :=
  (WithLp.linearEquiv 2 ℂ (Fin 2 → ℂ)).trans (TensorProduct.lid ℂ (Fin 2 → ℂ)).symm

/-- The representation of the global gauge group on the weak index of the Higgs, the
  fundamental representation of `SU(2)` twisted by the power `3` of the hypercharge. -/
noncomputable def gaugeRep : globalGaugeGroup.group →ₜ* (Matrix (Fin 2) (Fin 2) ℂ)ˣ :=
  MatrixRep.charge 3 hypercharge su2Fund

/-!

## B. The matter field

-/

/-- The Higgs `(1, 2)_{3}` as a matter field of the Standard Model global gauge group,
  a Lorentz scalar. -/
noncomputable def matterField : globalGaugeGroup.MatterField :=
  ofMatrixRep tensorEquiv gaugeRep (Representation.trivial ℂ SL(2,ℂ) ℂ) 2 .bosonic

/-- The target space of the matter field is `HiggsVec`. -/
@[simp]
lemma matterField_V : matterField.V = HiggsVec := rfl

/-- The action of the gauge algebra of the matter field is the action matrix of its matrix
  representation. -/
lemma matterField_repAlgebra (c : globalGaugeGroup.lieSubalgebra) :
    matterField.repAlgebra c = MatrixRep.valEnd tensorEquiv (derivMat gaugeRep c) :=
  ofMatrixRep_repAlgebra _ _ _ _ _ c

/-- The Lorentz action of the matter field is that of the trivial scalar
  representation. -/
@[simp]
lemma matterField_repLorentz :
    matterField.repLorentz =
      MatrixRep.repLorentz tensorEquiv (Representation.trivial ℂ SL(2,ℂ) ℂ) := rfl

/-- The mass weight of the Higgs. -/
@[simp]
lemma matterField_massWeight : matterField.massWeight = 2 := rfl

/-- The Higgs is bosonic. -/
@[simp]
lemma matterField_statistic : matterField.statistic = .bosonic := rfl

/-- The Lorentz action of the matter field of the Higgs is continuous. -/
lemma matterField_lorentzContinuous : matterField.LorentzContinuous :=
  ofMatrixRep_lorentzContinuous _ _ _ 2 _ fun s ψ => by
    simpa [Representation.trivial_apply] using continuous_const (y := ψ s)

/-- The gauge and Lorentz representations of the matter field of the Higgs commute. -/
lemma matterField_gaugeLorentzCommute : matterField.GaugeLorentzCommute :=
  ofMatrixRep_gaugeLorentzCommute _ _ _ 2 _

/-- The Lorentz action of the matter field is trivial. -/
lemma matterField_repLorentz_eq (Λ : SL(2,ℂ)) :
    (matterField.repLorentz Λ : HiggsVec →ₗ[ℂ] HiggsVec) = LinearMap.id := by
  have h : (MatrixRep.repLorentz tensorEquiv (Representation.trivial ℂ SL(2,ℂ) ℂ) Λ) ∘ₗ
      tensorEquiv.symm.toLinearMap =
      (LinearMap.id : HiggsVec →ₗ[ℂ] HiggsVec) ∘ₗ tensorEquiv.symm.toLinearMap :=
    TensorProduct.ext' fun s w => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        MatrixRep.repLorentz_apply_symm_tmul]
      simp
  refine LinearMap.ext fun (v : HiggsVec) => ?_
  have h' := LinearMap.congr_fun h (tensorEquiv v)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h'
  exact h'

/-- The action of the gauge group on the matter field of the Higgs, through
  `gaugeGroupEquiv`, is the action `repGaugeGroupI`. -/
lemma matterField_rep_gaugeGroupEquiv (g : GaugeGroupI) :
    (((matterField.rep (gaugeGroupEquiv g) : _ˣ) :
      matterField.V →L[ℂ] matterField.V) : matterField.V →ₗ[ℂ]
        matterField.V) =
        (repGaugeGroupI g : matterField.V →ₗ[ℂ] matterField.V) := by
  refine LinearMap.ext fun (v : HiggsVec) => ?_
  have hu : ((u1Phase (gaugeGroupEquiv g) : ℂˣ) : ℂ) = (g.toU1.1 : ℂ) :=
    u1Phase_gaugeGroupEquiv g
  have hs : su2Block (gaugeGroupEquiv g) = (g.toSU2.1 : Matrix (Fin 2) (Fin 2) ℂ) :=
    su2Block_gaugeGroupEquiv g
  have hu' : ((u1Phase (gaugeGroupEquiv g) ^ (3 : ℤ) : ℂˣ) : ℂ) = (g.toU1.1 : ℂ) ^ 3 := by
    rw [Units.val_zpow_eq_zpow_val, hu]
    rfl
  show MatrixRep.valEnd tensorEquiv (gaugeRep (gaugeGroupEquiv g) : Matrix (Fin 2) (Fin 2) ℂ) v = _
  rw [show (gaugeRep (gaugeGroupEquiv g) : Matrix (Fin 2) (Fin 2) ℂ) =
    ((u1Phase (gaugeGroupEquiv g) ^ (3 : ℤ) : ℂˣ) : ℂ) • su2Block (gaugeGroupEquiv g) from
      (MatrixRep.charge_val 3 hypercharge su2Fund _).trans rfl, MatrixRep.valEnd_smul, hs]
  have hv : MatrixRep.valEnd tensorEquiv (g.toSU2.1 : Matrix (Fin 2) (Fin 2) ℂ) v =
      WithLp.toLp 2 ((g.toSU2.1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v.ofLp) := by
    have h1 : v = tensorEquiv.symm ((1 : ℂ) ⊗ₜ[ℂ] v.ofLp) := by
      apply tensorEquiv.injective
      rw [LinearEquiv.apply_symm_apply]
      simp [tensorEquiv]
    conv_lhs => rw [h1]
    rw [MatrixRep.valEnd_apply_symm_tmul]
    simp [tensorEquiv]
  rw [LinearMap.smul_apply, hv, hu']
  exact (repGaugeGroupI_apply g v).symm

end StandardModel.HiggsVec
