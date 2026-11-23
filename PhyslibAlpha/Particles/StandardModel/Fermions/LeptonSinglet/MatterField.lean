/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.Fermions.LeptonSinglet.Basic
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.GlobalGaugeGroup
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.InfinitesimalAction
/-!
# The charged-lepton singlet as a matter field

The charged-lepton singlet `(1, 1)_{-6}` as a matter field of the Standard Model global gauge
group.

## i. Overview

The target space `LeptonSinglet` is normed by the coordinates of its basis. A charged-lepton
singlet is a right-handed Weyl spinor with a trivial internal index, and the global gauge group
acts on it by the power `-6` of the hypercharge phase. This is the charge `-6` twist of the
trivial matrix representation, which gives a matter field of mass weight three. Its action of
the global gauge group, on the image of `StandardModel.gaugeGroupEquiv`, is the existing action
`StandardModel.LeptonSinglet.repGaugeGroupI`.

## ii. Key results

- `StandardModel.LeptonSinglet.matterField` : the charged-lepton singlet as a matter field of
  `StandardModel.globalGaugeGroup`.
- `StandardModel.LeptonSinglet.matterField_repAlgebra` : its action of the gauge algebra.
- `StandardModel.LeptonSinglet.matterField_rep_gaugeGroupEquiv` : its action of the gauge
  group is `StandardModel.LeptonSinglet.repGaugeGroupI`.
- `StandardModel.LeptonSinglet.matterField_lorentzContinuous`,
  `StandardModel.LeptonSinglet.matterField_gaugeLorentzCommute` :
  its Lorentz action is continuous and commutes with its gauge action.

## iii. Table of contents

- A. The normed structure
- B. The matter field
- C. Its actions

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel.LeptonSinglet

open GlobalGaugeGroup GlobalGaugeGroup.MatterField Matrix MatrixGroups TensorProduct

/-!

## A. The normed structure

The target space is normed by the largest modulus of its coordinates in its basis.

-/

/-- The norm on the charged-lepton singlets, the largest modulus of the coordinates in its
  basis. -/
@[instance_reducible]
noncomputable def instNormedAddCommGroup : NormedAddCommGroup LeptonSinglet :=
  NormedAddCommGroup.induced LeptonSinglet (Fin 2 → ℂ) basis.equivFun basis.equivFun.injective

attribute [local instance] instNormedAddCommGroup

/-- The charged-lepton singlets as a normed space over `ℂ`. -/
@[instance_reducible]
noncomputable def instNormedSpace : NormedSpace ℂ LeptonSinglet :=
  NormedSpace.induced ℂ LeptonSinglet (Fin 2 → ℂ) basis.equivFun

attribute [local instance] instNormedSpace

/-!

## B. The matter field

The field is a right-handed Weyl spinor with a trivial internal index, and its gauge group
acts through the hypercharge only.

-/

/-- The identification of the charged-lepton singlets with a right-handed Weyl spinor tensored
  with a trivial internal index. -/
noncomputable def tensorEquiv :
    LeptonSinglet ≃ₗ[ℂ] Fermion.RightHandedWeyl ⊗[ℂ] (Fin 1 → ℂ) :=
  valLinEquiv.trans ((TensorProduct.rid ℂ Fermion.RightHandedWeyl).symm.trans
    (TensorProduct.congr (LinearEquiv.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm))

/-- The identification `tensorEquiv` on a pure tensor. -/
lemma tensorEquiv_symm_tmul (s : Fermion.RightHandedWeyl) (w : Fin 1 → ℂ) :
    tensorEquiv.symm (s ⊗ₜ[ℂ] w) = ⟨w 0 • s⟩ := by
  simp [tensorEquiv, valLinEquiv_symm_apply]
  rfl

/-- The representation of the global gauge group on the internal index of the charged-lepton
  singlet, the trivial representation twisted by the power `-6` of the hypercharge. -/
noncomputable def gaugeRep : globalGaugeGroup.group →ₜ* (Matrix (Fin 1) (Fin 1) ℂ)ˣ :=
  MatrixRep.charge (-6) hypercharge MatrixRep.trivial

/-- The charged-lepton singlet `(1, 1)_{-6}` as a matter field of the Standard Model global
  gauge group, with its right-handed Lorentz action. -/
noncomputable def matterField : globalGaugeGroup.MatterField :=
  letI : FiniteDimensional ℂ LeptonSinglet := Module.Finite.of_basis basis
  ofMatrixRep tensorEquiv gaugeRep Fermion.RightHandedWeyl.rep 3 .fermionic

/-- The target space of the matter field is the charged-lepton singlets. -/
@[simp]
lemma matterField_V : matterField.V = LeptonSinglet := rfl

/-- The Lorentz action of the matter field is that of the right-handed Weyl spinor. -/
@[simp]
lemma matterField_repLorentz :
    matterField.repLorentz = MatrixRep.repLorentz tensorEquiv Fermion.RightHandedWeyl.rep := rfl

/-- The mass weight of the charged-lepton singlet. -/
@[simp]
lemma matterField_massWeight : matterField.massWeight = 3 := rfl

/-- The charged-lepton singlet is fermionic. -/
@[simp]
lemma matterField_statistic : matterField.statistic = .fermionic := rfl

/-- The action of the gauge algebra of the matter field of the charged-lepton singlet is the
  action matrix of its matrix representation. -/
lemma matterField_repAlgebra (c : globalGaugeGroup.lieSubalgebra) :
    matterField.repAlgebra c = MatrixRep.valEnd tensorEquiv (derivMat gaugeRep c) :=
  ofMatrixRep_repAlgebra _ _ _ _ _ c

/-!

## C. Its actions

-/

/-- The Lorentz action of the matter field is the right-handed Lorentz action. -/
lemma matterField_repLorentz_eq (Λ : SL(2,ℂ)) :
    (matterField.repLorentz Λ : LeptonSinglet →ₗ[ℂ] LeptonSinglet) =
      repLorentzGroup Λ := by
  have h : (MatrixRep.repLorentz tensorEquiv Fermion.RightHandedWeyl.rep Λ) ∘ₗ
        tensorEquiv.symm.toLinearMap = (repLorentzGroup Λ) ∘ₗ tensorEquiv.symm.toLinearMap :=
    TensorProduct.ext' fun s w => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        MatrixRep.repLorentz_apply_symm_tmul]
      rw [tensorEquiv_symm_tmul, tensorEquiv_symm_tmul]
      show (⟨w 0 • Fermion.RightHandedWeyl.rep Λ s⟩ : LeptonSinglet) =
        ⟨Fermion.RightHandedWeyl.rep Λ (w 0 • s)⟩
      rw [map_smul]
  refine LinearMap.ext fun (v : LeptonSinglet) => ?_
  have h' := LinearMap.congr_fun h (tensorEquiv v)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h'
  exact h'

/-- The Lorentz action of the matter field of the charged-lepton singlet is continuous. -/
lemma matterField_lorentzContinuous : matterField.LorentzContinuous :=
  ofMatrixRep_lorentzContinuous _ _ _ 3 _ Fermion.RightHandedWeyl.continuous_rep_apply

/-- The gauge and Lorentz representations of the matter field of the charged-lepton singlet
  commute. -/
lemma matterField_gaugeLorentzCommute : matterField.GaugeLorentzCommute :=
  ofMatrixRep_gaugeLorentzCommute _ _ _ 3 _

/-- The action of the gauge group on the matter field of the charged-lepton singlet,
  through `gaugeGroupEquiv`, is the action `repGaugeGroupI`. -/
lemma matterField_rep_gaugeGroupEquiv (g : GaugeGroupI) :
    (((matterField.rep (gaugeGroupEquiv g) : _ˣ) : matterField.V →L[ℂ] matterField.V) :
      matterField.V →ₗ[ℂ] matterField.V) =
        (repGaugeGroupI g : matterField.V →ₗ[ℂ] matterField.V) := by
  refine LinearMap.ext fun (v : LeptonSinglet) => ?_
  have hu : ((u1Phase (gaugeGroupEquiv g) : ℂˣ) : ℂ) = (g.toU1.1 : ℂ) :=
    u1Phase_gaugeGroupEquiv g
  have hz : ((u1Phase (gaugeGroupEquiv g) ^ (-6 : ℤ) : ℂˣ) : ℂ) = star (g.toU1.1 : ℂ) ^ 6 := by
    rw [Units.val_zpow_eq_zpow_val, hu, _root_.zpow_neg, ← _root_.inv_zpow, zpow_ofNat]
    congr 1
    have h := Unitary.coe_star_mul_self g.toU1
    exact (eq_inv_of_mul_eq_one_left h).symm
  show MatrixRep.valEnd tensorEquiv (gaugeRep (gaugeGroupEquiv g) : Matrix (Fin 1) (Fin 1) ℂ) v = _
  rw [show (gaugeRep (gaugeGroupEquiv g) : Matrix (Fin 1) (Fin 1) ℂ) =
    ((u1Phase (gaugeGroupEquiv g) ^ (-6 : ℤ) : ℂˣ) : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) from
      (MatrixRep.charge_val (-6) hypercharge MatrixRep.trivial _).trans rfl,
    MatrixRep.valEnd_smul, MatrixRep.valEnd_one, hz]
  rfl

end StandardModel.LeptonSinglet
