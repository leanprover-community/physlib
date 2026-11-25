/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.Fermions.UpSinglet.Basic
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.GlobalGaugeGroup
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.InfinitesimalAction
/-!
# The up-type singlet as a matter field

The up-type singlet `(3, 1)_{4}` as a matter field of the Standard Model global
gauge group.

## i. Overview

The target space `UpSinglet` is normed by the coordinates of its basis. An up-type singlet is a
right-handed Weyl spinor with a colour index in `Fin 3`, and the global gauge group acts on it by
the fundamental representation of the `SU(3)` block twisted by the power `4` of the hypercharge
phase. This is the charge `4` twist of the fundamental representation of the colour factor,
which gives a matter field of mass weight three. Its action of the global gauge group, on the
image of `StandardModel.gaugeGroupEquiv`, is the existing action
`StandardModel.UpSinglet.repGaugeGroupI`.

## ii. Key results

- `StandardModel.UpSinglet.matterField` : the up-type singlet as a matter field of
  `StandardModel.globalGaugeGroup`.
- `StandardModel.UpSinglet.matterField_repAlgebra` : its action of the gauge algebra.
- `StandardModel.UpSinglet.matterField_rep_gaugeGroupEquiv` : its action of the gauge
  group is `StandardModel.UpSinglet.repGaugeGroupI`.
- `StandardModel.UpSinglet.matterField_lorentzContinuous`,
  `StandardModel.UpSinglet.matterField_gaugeLorentzCommute` :
  its Lorentz action is continuous and commutes with its gauge action.

## iii. Table of contents

- A. The normed structure
- B. The gauge representation
- C. The matter field

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel.UpSinglet

open GlobalGaugeGroup GlobalGaugeGroup.MatterField Matrix MatrixGroups TensorProduct

/-!

## A. The normed structure

The target space is normed by the largest modulus of its coordinates in its basis.

-/

/-- The norm on the up-type singlets, the largest modulus of the coordinates in its
  basis. -/
@[instance_reducible]
noncomputable def instNormedAddCommGroup : NormedAddCommGroup UpSinglet :=
  NormedAddCommGroup.induced UpSinglet (Fin 2 × Fin 3 → ℂ) basis.equivFun
    basis.equivFun.injective

attribute [local instance] instNormedAddCommGroup

/-- The up-type singlets as a normed space over `ℂ`. -/
@[instance_reducible]
noncomputable def instNormedSpace : NormedSpace ℂ UpSinglet :=
  NormedSpace.induced ℂ UpSinglet (Fin 2 × Fin 3 → ℂ) basis.equivFun

attribute [local instance] instNormedSpace

/-!

## B. The gauge representation

-/

/-- The up-type singlets as a right-handed Weyl spinor with a colour index. -/
noncomputable def tensorEquiv : UpSinglet ≃ₗ[ℂ] Fermion.RightHandedWeyl ⊗[ℂ] (Fin 3 → ℂ) :=
  valLinEquiv.trans (TensorProduct.congr (LinearEquiv.refl ℂ _)
    (WithLp.linearEquiv 2 ℂ (Fin 3 → ℂ)))

/-- The inverse of the identification `tensorEquiv` on a pure tensor. -/
lemma tensorEquiv_symm_tmul (s : Fermion.RightHandedWeyl) (w : Fin 3 → ℂ) :
    tensorEquiv.symm (s ⊗ₜ[ℂ] w) = ⟨s ⊗ₜ[ℂ] (WithLp.toLp 2 w)⟩ := rfl

/-- The representation of the global gauge group on the colour index of the up-type singlet,
  the fundamental representation of `SU(3)` twisted by the power `4` of the hypercharge. -/
noncomputable def gaugeRep : globalGaugeGroup.group →ₜ* (Matrix (Fin 3) (Fin 3) ℂ)ˣ :=
  MatrixRep.charge 4 hypercharge su3Fund

/-!

## C. The matter field

-/

/-- The up-type singlet `(3, 1)_{4}` as a matter field of the Standard Model global
  gauge group, with its right-handed Lorentz action. -/
noncomputable def matterField : globalGaugeGroup.MatterField :=
  letI : FiniteDimensional ℂ UpSinglet := Module.Finite.of_basis basis
  ofMatrixRep tensorEquiv gaugeRep Fermion.RightHandedWeyl.rep 3 .fermionic

/-- The target space of the matter field is the up-type singlets. -/
@[simp]
lemma matterField_V : matterField.V = UpSinglet := rfl

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

/-- The mass weight of the up-type singlet. -/
@[simp]
lemma matterField_massWeight : matterField.massWeight = 3 := rfl

/-- The up-type singlet is fermionic. -/
@[simp]
lemma matterField_statistic : matterField.statistic = .fermionic := rfl

/-- The Lorentz action of the matter field of the up-type quark singlet is continuous. -/
lemma matterField_lorentzContinuous : matterField.LorentzContinuous :=
  ofMatrixRep_lorentzContinuous _ _ _ 3 _ Fermion.RightHandedWeyl.continuous_rep_apply

/-- The gauge and Lorentz representations of the matter field of the up-type quark singlet
  commute. -/
lemma matterField_gaugeLorentzCommute : matterField.GaugeLorentzCommute :=
  ofMatrixRep_gaugeLorentzCommute _ _ _ 3 _

/-- The Lorentz action of the matter field is the right-handed Lorentz action. -/
lemma matterField_repLorentz_eq (Λ : SL(2,ℂ)) :
    (matterField.repLorentz Λ : UpSinglet →ₗ[ℂ] UpSinglet) =
      repLorentzGroup Λ := by
  have h : (MatrixRep.repLorentz tensorEquiv Fermion.RightHandedWeyl.rep Λ) ∘ₗ
      tensorEquiv.symm.toLinearMap =
      (repLorentzGroup Λ) ∘ₗ tensorEquiv.symm.toLinearMap :=
    TensorProduct.ext' fun s w => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        MatrixRep.repLorentz_apply_symm_tmul]
      rw [tensorEquiv_symm_tmul, tensorEquiv_symm_tmul]
      rfl
  refine LinearMap.ext fun (v : UpSinglet) => ?_
  have h' := LinearMap.congr_fun h (tensorEquiv v)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h'
  exact h'

/-- The action of the gauge group on the matter field of the up-type singlet,
  through `gaugeGroupEquiv`, is the action `repGaugeGroupI`. -/
lemma matterField_rep_gaugeGroupEquiv (g : GaugeGroupI) :
    (((matterField.rep (gaugeGroupEquiv g) : _ˣ) :
      matterField.V →L[ℂ] matterField.V) : matterField.V →ₗ[ℂ]
        matterField.V) =
        (repGaugeGroupI g : matterField.V →ₗ[ℂ] matterField.V) := by
  have hu : ((u1Phase (gaugeGroupEquiv g) : ℂˣ) : ℂ) = (g.toU1.1 : ℂ) :=
    u1Phase_gaugeGroupEquiv g
  have hz : ((u1Phase (gaugeGroupEquiv g) ^ (4 : ℤ) : ℂˣ) : ℂ) = (g.toU1.1 : ℂ) ^ 4 := by
    rw [Units.val_zpow_eq_zpow_val, hu]
    rfl
  have hs : su3Block (gaugeGroupEquiv g) = (g.toSU3.1 : Matrix (Fin 3) (Fin 3) ℂ) :=
    su3Block_gaugeGroupEquiv g
  have hc : (gaugeRep (gaugeGroupEquiv g) : Matrix (Fin 3) (Fin 3) ℂ) =
      ((g.toU1.1 : ℂ) ^ 4) • (g.toSU3.1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    rw [← hz, ← hs]
    exact (MatrixRep.charge_val 4 hypercharge su3Fund _).trans rfl
  have h : MatrixRep.valEnd tensorEquiv (gaugeRep (gaugeGroupEquiv g) : Matrix (Fin 3) (Fin 3) ℂ) ∘ₗ
      tensorEquiv.symm.toLinearMap = (repGaugeGroupI g) ∘ₗ tensorEquiv.symm.toLinearMap :=
    TensorProduct.ext' fun s w => by
      rw [hc, MatrixRep.valEnd_smul, LinearMap.comp_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearMap.smul_apply, MatrixRep.valEnd_apply_symm_tmul,
        tensorEquiv_symm_tmul, tensorEquiv_symm_tmul]
      rw [repGaugeGroupI_tmul]
      refine valLinEquiv.injective ?_
      rw [map_smul]
      simp only [valLinEquiv_apply]
      rw [TensorProduct.smul_tmul']
      rfl
  refine LinearMap.ext fun (v : UpSinglet) => ?_
  have h' := LinearMap.congr_fun h (tensorEquiv v)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h'
  exact h'

end StandardModel.UpSinglet
