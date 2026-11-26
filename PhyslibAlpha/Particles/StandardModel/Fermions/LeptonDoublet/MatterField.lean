/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.Fermions.LeptonDoublet.Basic
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.GlobalGaugeGroup
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.InfinitesimalAction
/-!
# The lepton doublet as a matter field

The lepton doublet `(1, 2)_{-3}` as a matter field of the Standard Model global gauge
group.

## i. Overview

The target space `LeptonDoubletV` is normed by the coordinates of its basis. A lepton doublet
is a left-handed Weyl spinor with a weak index, and the global gauge group acts on the weak
index by its `SU(2)` block scaled by the power `-3` of the hypercharge phase. This is the
charge `-3` twist of the fundamental representation of `SU(2)`, which gives a matter field of
mass weight three. Its action of the global gauge group, on the image of
`StandardModel.gaugeGroupEquiv`, is the existing action
`StandardModel.LeptonDoubletV.repGaugeGroupI`.

## ii. Key results

- `StandardModel.LeptonDoubletV.matterField` : the lepton doublet as a matrix matter
  field of `StandardModel.globalGaugeGroup`.
- `StandardModel.LeptonDoubletV.matterField_repAlgebra` : its action of the gauge
  algebra.
- `StandardModel.LeptonDoubletV.matterField_rep_gaugeGroupEquiv` : its action of the
  gauge group is `StandardModel.LeptonDoubletV.repGaugeGroupI`.
- `StandardModel.LeptonDoubletV.matterField_lorentzContinuous`,
  `StandardModel.LeptonDoubletV.matterField_gaugeLorentzCommute` :
  its Lorentz action is continuous and commutes with its gauge action.

## iii. Table of contents

- A. The normed structure
- B. The gauge representation
- C. The matter field

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel.LeptonDoubletV

open GlobalGaugeGroup GlobalGaugeGroup.MatterField Matrix MatrixGroups TensorProduct

/-!

## A. The normed structure

The target space is normed by the largest modulus of its coordinates in its basis.

-/

/-- The norm on the lepton doublets, the largest modulus of the coordinates in its basis. -/
@[instance_reducible]
noncomputable def instNormedAddCommGroup : NormedAddCommGroup LeptonDoubletV :=
  NormedAddCommGroup.induced LeptonDoubletV (Fin 2 × Fin 2 → ℂ) basis.equivFun
    basis.equivFun.injective

attribute [local instance] instNormedAddCommGroup

/-- The lepton doublets as a normed space over `ℂ`. -/
@[instance_reducible]
noncomputable def instNormedSpace : NormedSpace ℂ LeptonDoubletV :=
  NormedSpace.induced ℂ LeptonDoubletV (Fin 2 × Fin 2 → ℂ) basis.equivFun

attribute [local instance] instNormedSpace

/-!

## B. The gauge representation

-/

/-- The lepton doublets as a left-handed Weyl spinor tensored with the weak coordinates. -/
noncomputable def tensorEquiv : LeptonDoubletV ≃ₗ[ℂ] Fermion.LeftHandedWeyl ⊗[ℂ] (Fin 2 → ℂ) :=
  LinearEquiv.refl ℂ _

/-- The representation of the global gauge group on the weak index of the lepton doublet,
  the fundamental representation of `SU(2)` twisted by the power `-3` of the hypercharge. -/
noncomputable def gaugeRep : globalGaugeGroup.group →ₜ* (Matrix (Fin 2) (Fin 2) ℂ)ˣ :=
  MatrixRep.charge (-3) hypercharge su2Fund

/-!

## C. The matter field

-/

/-- The lepton doublet `(1, 2)_{-3}` as a matter field of the Standard Model global
  gauge group, with its left-handed Lorentz action. -/
noncomputable def matterField : globalGaugeGroup.MatterField :=
  letI : FiniteDimensional ℂ LeptonDoubletV := Module.Finite.of_basis basis
  ofMatrixRep tensorEquiv gaugeRep Fermion.LeftHandedWeyl.rep 3 .fermionic

/-- The target space of the matter field is the lepton doublets. -/
@[simp]
lemma matterField_V : matterField.V = LeptonDoubletV := rfl

/-- The action of the gauge algebra of the matter field is the action matrix of its matrix
  representation. -/
lemma matterField_repAlgebra (c : globalGaugeGroup.lieSubalgebra) :
    matterField.repAlgebra c = MatrixRep.valEnd tensorEquiv (derivMat gaugeRep c) :=
  ofMatrixRep_repAlgebra _ _ _ _ _ c

/-- The Lorentz action of the matter field is that of the left-handed Weyl spinor. -/
@[simp]
lemma matterField_repLorentz :
    matterField.repLorentz = MatrixRep.repLorentz tensorEquiv Fermion.LeftHandedWeyl.rep := rfl

/-- The mass weight of the lepton doublet. -/
@[simp]
lemma matterField_massWeight : matterField.massWeight = 3 := rfl

/-- The lepton doublet is fermionic. -/
@[simp]
lemma matterField_statistic : matterField.statistic = .fermionic := rfl

/-- The Lorentz action of the matter field of the lepton doublet is continuous. -/
lemma matterField_lorentzContinuous : matterField.LorentzContinuous :=
  ofMatrixRep_lorentzContinuous _ _ _ 3 _ Fermion.LeftHandedWeyl.continuous_rep_apply

/-- The gauge and Lorentz representations of the matter field of the lepton doublet commute. -/
lemma matterField_gaugeLorentzCommute : matterField.GaugeLorentzCommute :=
  ofMatrixRep_gaugeLorentzCommute _ _ _ 3 _

/-- The Lorentz action of the matter field is the left-handed Lorentz action. -/
lemma matterField_repLorentz_eq (Λ : SL(2,ℂ)) :
    (matterField.repLorentz Λ : LeptonDoubletV →ₗ[ℂ] LeptonDoubletV) =
      repLorentzGroup Λ := by
  have key : ∀ v : LeptonDoubletV,
      (MatrixRep.repLorentz tensorEquiv Fermion.LeftHandedWeyl.rep Λ) v = repLorentzGroup Λ v := by
    intro v
    induction v using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul s w =>
      have h := MatrixRep.repLorentz_apply_symm_tmul tensorEquiv Fermion.LeftHandedWeyl.rep Λ s w
      rw [repLorentzGroup_tmul]
      exact h
  exact LinearMap.ext key

/-- A matrix acts on the lepton doublet, through the identification `tensorEquiv`, on the weak
  index alone. -/
lemma valEnd_eq_map (B : Matrix (Fin 2) (Fin 2) ℂ) :
    MatrixRep.valEnd tensorEquiv B = TensorProduct.map LinearMap.id (Matrix.toLin' B) :=
  TensorProduct.ext' fun s w => MatrixRep.valEnd_apply_symm_tmul tensorEquiv B s w

/-- The action of the gauge group on the matter field of the lepton doublet, through
  `gaugeGroupEquiv`, is the action `repGaugeGroupI`. -/
lemma matterField_rep_gaugeGroupEquiv (g : GaugeGroupI) :
    (((matterField.rep (gaugeGroupEquiv g) : _ˣ) :
      matterField.V →L[ℂ] matterField.V) : matterField.V →ₗ[ℂ]
        matterField.V) =
        (repGaugeGroupI g : matterField.V →ₗ[ℂ] matterField.V) := by
  have hu : ((u1Phase (gaugeGroupEquiv g) : ℂˣ) : ℂ) = (g.toU1.1 : ℂ) :=
    u1Phase_gaugeGroupEquiv g
  have hs : su2Block (gaugeGroupEquiv g) = g.toSU2.1 :=
    su2Block_gaugeGroupEquiv g
  have hz : ((u1Phase (gaugeGroupEquiv g) ^ (-3 : ℤ) : ℂˣ) : ℂ) = star (g.toU1.1 : ℂ) ^ 3 := by
    rw [Units.val_zpow_eq_zpow_val, hu, _root_.zpow_neg, ← _root_.inv_zpow, zpow_ofNat]
    congr 1
    have h := Unitary.coe_star_mul_self g.toU1
    exact (eq_inv_of_mul_eq_one_left h).symm
  show MatrixRep.valEnd tensorEquiv (gaugeRep (gaugeGroupEquiv g) : Matrix (Fin 2) (Fin 2) ℂ) = _
  rw [show (gaugeRep (gaugeGroupEquiv g) : Matrix (Fin 2) (Fin 2) ℂ) =
    ((u1Phase (gaugeGroupEquiv g) ^ (-3 : ℤ) : ℂˣ) : ℂ) • su2Block (gaugeGroupEquiv g) from
      (MatrixRep.charge_val (-3) hypercharge su2Fund _).trans rfl,
    hz, hs, valEnd_eq_map]
  rfl

end StandardModel.LeptonDoubletV
