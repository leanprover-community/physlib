/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.Fermions.DownSinglet.Basic
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.GlobalGaugeGroup
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.InfinitesimalAction
/-!
# The down-type singlet as a matter field

The down-type singlet `(3, 1)_{-2}` as a matter field of the Standard Model global
gauge group.

## i. Overview

The target space `DownSinglet` is normed by the coordinates of its basis. A down-type singlet
is a right-handed Weyl spinor with a colour index, and the global gauge group acts on it by the
fundamental representation of `SU(3)` twisted by the power `-2` of the hypercharge phase. This
is the charge `-2` twist of the fundamental representation of the colour factor, which gives a
matter field of mass weight three. Its action of the global gauge group, on the image of
`StandardModel.gaugeGroupEquiv`, is the existing action
`StandardModel.DownSinglet.repGaugeGroupI`.

## ii. Key results

- `StandardModel.DownSinglet.matterField` : the down-type singlet as a matrix matter
  field of `StandardModel.globalGaugeGroup`.
- `StandardModel.DownSinglet.matterField_repAlgebra` : its action of the gauge algebra.
- `StandardModel.DownSinglet.matterField_rep_gaugeGroupEquiv` : its action of the gauge
  group is `StandardModel.DownSinglet.repGaugeGroupI`.
- `StandardModel.DownSinglet.matterField_lorentzContinuous`,
  `StandardModel.DownSinglet.matterField_gaugeLorentzCommute` :
  its Lorentz action is continuous and commutes with its gauge action.

## iii. Table of contents

- A. The normed structure
- B. The gauge representation
- C. The matter field

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel.DownSinglet

open GlobalGaugeGroup GlobalGaugeGroup.MatterField Matrix MatrixGroups TensorProduct

/-!

## A. The normed structure

The target space is normed by the largest modulus of its coordinates in its basis.

-/

/-- The norm on the down singlets, the largest modulus of the coordinates in its
  basis. -/
@[instance_reducible]
noncomputable def instNormedAddCommGroup : NormedAddCommGroup DownSinglet :=
  NormedAddCommGroup.induced DownSinglet (Fin 2 × Fin 3 → ℂ) basis.equivFun
    basis.equivFun.injective

attribute [local instance] instNormedAddCommGroup

/-- The down singlets as a normed space over `ℂ`. -/
@[instance_reducible]
noncomputable def instNormedSpace : NormedSpace ℂ DownSinglet :=
  NormedSpace.induced ℂ DownSinglet (Fin 2 × Fin 3 → ℂ) basis.equivFun

attribute [local instance] instNormedSpace

/-!

## B. The gauge representation

-/

/-- The down singlets as a right-handed Weyl spinor with a colour index. -/
noncomputable def tensorEquiv : DownSinglet ≃ₗ[ℂ] Fermion.RightHandedWeyl ⊗[ℂ] (Fin 3 → ℂ) :=
  valLinEquiv.trans
    (TensorProduct.congr (LinearEquiv.refl ℂ _) (WithLp.linearEquiv 2 ℂ (Fin 3 → ℂ)))

/-- The inverse of the identification `tensorEquiv` on a pure tensor. -/
lemma tensorEquiv_symm_tmul (s : Fermion.RightHandedWeyl) (w : Fin 3 → ℂ) :
    tensorEquiv.symm (s ⊗ₜ[ℂ] w) = ⟨s ⊗ₜ[ℂ] (WithLp.toLp 2 w)⟩ := by
  simp [tensorEquiv, valLinEquiv_symm_apply]

/-- The representation of the global gauge group on the colour index of the down-type
  singlet, the fundamental representation of `SU(3)` twisted by the power `-2` of the
  hypercharge. -/
noncomputable def gaugeRep : globalGaugeGroup.group →ₜ* (Matrix (Fin 3) (Fin 3) ℂ)ˣ :=
  MatrixRep.charge (-2) hypercharge su3Fund

/-!

## C. The matter field

-/

/-- The down-type singlet `(3, 1)_{-2}` as a matter field of the Standard Model
  global gauge group, with its right-handed Lorentz action. -/
noncomputable def matterField : globalGaugeGroup.MatterField :=
  letI : FiniteDimensional ℂ DownSinglet := Module.Finite.of_basis basis
  ofMatrixRep tensorEquiv gaugeRep Fermion.RightHandedWeyl.rep 3 .fermionic

/-- The target space of the matter field is the down singlets. -/
@[simp]
lemma matterField_V : matterField.V = DownSinglet := rfl

/-- The action of the gauge algebra of the matter field is the action matrix of its matrix
  representation. -/
lemma matterField_repAlgebra (c : globalGaugeGroup.lieSubalgebra) :
    matterField.repAlgebra c = MatrixRep.valEnd tensorEquiv (derivMat gaugeRep c) :=
  ofMatrixRep_repAlgebra _ _ _ _ _ c

/-- The Lorentz action of the matter field is that of the right-handed Weyl
  spinor. -/
@[simp]
lemma matterField_repLorentz :
    matterField.repLorentz = MatrixRep.repLorentz tensorEquiv Fermion.RightHandedWeyl.rep := rfl

/-- The mass weight of the down-type singlet. -/
@[simp]
lemma matterField_massWeight : matterField.massWeight = 3 := rfl

/-- The down-type singlet is fermionic. -/
@[simp]
lemma matterField_statistic : matterField.statistic = .fermionic := rfl

/-- The Lorentz action of the matter field of the down-type quark singlet is continuous. -/
lemma matterField_lorentzContinuous : matterField.LorentzContinuous :=
  ofMatrixRep_lorentzContinuous _ _ _ 3 _ Fermion.RightHandedWeyl.continuous_rep_apply

/-- The gauge and Lorentz representations of the matter field of the down-type quark singlet
  commute. -/
lemma matterField_gaugeLorentzCommute : matterField.GaugeLorentzCommute :=
  ofMatrixRep_gaugeLorentzCommute _ _ _ 3 _

/-- The Lorentz action of the matter field is the right-handed Lorentz action. -/
lemma matterField_repLorentz_eq (Λ : SL(2,ℂ)) :
    (matterField.repLorentz Λ : DownSinglet →ₗ[ℂ] DownSinglet) =
      repLorentzGroup Λ := by
  have h : (MatrixRep.repLorentz tensorEquiv Fermion.RightHandedWeyl.rep Λ) ∘ₗ
      tensorEquiv.symm.toLinearMap =
      (repLorentzGroup Λ) ∘ₗ tensorEquiv.symm.toLinearMap :=
    TensorProduct.ext' fun s w => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        MatrixRep.repLorentz_apply_symm_tmul]
      rw [tensorEquiv_symm_tmul, tensorEquiv_symm_tmul]
      rfl
  refine LinearMap.ext fun (v : DownSinglet) => ?_
  have h' := LinearMap.congr_fun h (tensorEquiv v)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h'
  exact h'

/-- The action of the gauge group on the matter field of the down-type singlet,
  through `gaugeGroupEquiv`, is the action `repGaugeGroupI`. -/
lemma matterField_rep_gaugeGroupEquiv (g : GaugeGroupI) :
    (((matterField.rep (gaugeGroupEquiv g) : _ˣ) :
      matterField.V →L[ℂ] matterField.V) : matterField.V →ₗ[ℂ]
        matterField.V) =
        (repGaugeGroupI g : matterField.V →ₗ[ℂ] matterField.V) := by
  have hu : ((u1Phase (gaugeGroupEquiv g) : ℂˣ) : ℂ) = (g.toU1.1 : ℂ) :=
    u1Phase_gaugeGroupEquiv g
  have hs : su3Block (gaugeGroupEquiv g) = g.toSU3.1 :=
    su3Block_gaugeGroupEquiv g
  have hz : ((u1Phase (gaugeGroupEquiv g) ^ (-2 : ℤ) : ℂˣ) : ℂ) =
      star (g.toU1.1 : ℂ) ^ 2 := by
    rw [Units.val_zpow_eq_zpow_val, hu, _root_.zpow_neg, ← _root_.inv_zpow, zpow_ofNat]
    congr 1
    have h := Unitary.coe_star_mul_self g.toU1
    exact (eq_inv_of_mul_eq_one_left h).symm
  have hM : (gaugeRep (gaugeGroupEquiv g) : Matrix (Fin 3) (Fin 3) ℂ) =
      (star (g.toU1.1 : ℂ) ^ 2) • (g.toSU3.1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    refine (MatrixRep.charge_val (-2) hypercharge su3Fund _).trans ?_
    show ((u1Phase (gaugeGroupEquiv g) ^ (-2 : ℤ) : ℂˣ) : ℂ) • su3Block (gaugeGroupEquiv g) = _
    rw [hz, hs]
  have h : (((matterField.rep (gaugeGroupEquiv g) : _ˣ) :
      matterField.V →L[ℂ] matterField.V) :
        matterField.V →ₗ[ℂ] matterField.V) ∘ₗ
      tensorEquiv.symm.toLinearMap = (repGaugeGroupI g) ∘ₗ tensorEquiv.symm.toLinearMap :=
    TensorProduct.ext' fun s w => by
      show MatrixRep.valEnd tensorEquiv (gaugeRep (gaugeGroupEquiv g) : Matrix (Fin 3) (Fin 3) ℂ)
        (tensorEquiv.symm (s ⊗ₜ[ℂ] w)) = repGaugeGroupI g (tensorEquiv.symm (s ⊗ₜ[ℂ] w))
      rw [hM, MatrixRep.valEnd_smul, LinearMap.smul_apply, MatrixRep.valEnd_apply_symm_tmul,
        tensorEquiv_symm_tmul, tensorEquiv_symm_tmul, repGaugeGroupI_tmul]
      rfl
  exact (LinearMap.cancel_right
    (show Function.Surjective tensorEquiv.symm.toLinearMap from tensorEquiv.symm.surjective)).1 h

end StandardModel.DownSinglet
