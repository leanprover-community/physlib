/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.Fermions.QuarkDoublet.Basic
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.GlobalGaugeGroup
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.InfinitesimalAction
/-!
# The quark doublet as a matter field

The quark doublet `(3, 2)_1` as a matter field of the Standard Model global gauge group.

## i. Overview

The target space `QuarkDoublet` is normed by the coordinates of its basis. A quark doublet is a
left-handed Weyl spinor with a combined colour and weak index in `Fin 3 × Fin 2`, and the global
gauge group acts on it by the hypercharge phase times the Kronecker product of the `SU(3)` and
`SU(2)` blocks. This is the charge `1` twist of the Kronecker product of the fundamental
representations of the two factors, which gives a matter field of mass weight three. Its action
of the global gauge group, on the image of `StandardModel.gaugeGroupEquiv`, is the existing
action `StandardModel.QuarkDoublet.repGaugeGroupI`.

## ii. Key results

- `StandardModel.QuarkDoublet.matterField` : the quark doublet as a matter field of
  `StandardModel.globalGaugeGroup`.
- `StandardModel.QuarkDoublet.matterField_repAlgebra` : its action of the gauge algebra.
- `StandardModel.QuarkDoublet.valEnd_smul_kronecker` : the action of a scaled Kronecker product
  of matrices on the combined colour and weak index.
- `StandardModel.QuarkDoublet.matterField_rep_gaugeGroupEquiv` : its action of the gauge
  group is `StandardModel.QuarkDoublet.repGaugeGroupI`.
- `StandardModel.QuarkDoublet.matterField_lorentzContinuous`,
  `StandardModel.QuarkDoublet.matterField_gaugeLorentzCommute` :
  its Lorentz action is continuous and commutes with its gauge action.

## iii. Table of contents

- A. The normed structure
- B. The gauge representation
- C. The matter field
- D. The action of matrices on the combined index
- E. The action of the gauge group

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel.QuarkDoublet

open GlobalGaugeGroup GlobalGaugeGroup.MatterField Matrix MatrixGroups TensorProduct
  Kronecker

/-!

## A. The normed structure

The target space is normed by the largest modulus of its coordinates in its basis.

-/

/-- The norm on the quark doublets, the largest modulus of the coordinates in its
  basis. -/
@[instance_reducible]
noncomputable def instNormedAddCommGroup : NormedAddCommGroup QuarkDoublet :=
  NormedAddCommGroup.induced QuarkDoublet (Fin 2 × Fin 3 × Fin 2 → ℂ) basis.equivFun
    basis.equivFun.injective

attribute [local instance] instNormedAddCommGroup

/-- The quark doublets as a normed space over `ℂ`. -/
@[instance_reducible]
noncomputable def instNormedSpace : NormedSpace ℂ QuarkDoublet :=
  NormedSpace.induced ℂ QuarkDoublet (Fin 2 × Fin 3 × Fin 2 → ℂ) basis.equivFun

attribute [local instance] instNormedSpace

/-!

## B. The gauge representation

-/

/-- The quark doublets as a left-handed Weyl spinor with a combined colour and weak index. -/
noncomputable def tensorEquiv :
    QuarkDoublet ≃ₗ[ℂ] Fermion.LeftHandedWeyl ⊗[ℂ] (Fin 3 × Fin 2 → ℂ) :=
  valLinEquiv.trans <|
    (TensorProduct.assoc ℂ Fermion.LeftHandedWeyl (EuclideanSpace ℂ (Fin 3))
      (EuclideanSpace ℂ (Fin 2))).trans <|
        TensorProduct.congr (LinearEquiv.refl ℂ _) colourWeakEquiv

/-- The identification `tensorEquiv` on a pure tensor. -/
lemma tensorEquiv_mk (s : Fermion.LeftHandedWeyl) (c : EuclideanSpace ℂ (Fin 3))
    (w : EuclideanSpace ℂ (Fin 2)) :
    tensorEquiv ⟨(s ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] w⟩ = s ⊗ₜ[ℂ] colourWeakEquiv (c ⊗ₜ[ℂ] w) := rfl

/-- The inverse of the identification `tensorEquiv` on a pure tensor. -/
lemma tensorEquiv_symm_tmul (s : Fermion.LeftHandedWeyl) (c : EuclideanSpace ℂ (Fin 3))
    (w : EuclideanSpace ℂ (Fin 2)) :
    tensorEquiv.symm (s ⊗ₜ[ℂ] colourWeakEquiv (c ⊗ₜ[ℂ] w)) = ⟨(s ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] w⟩ :=
  (LinearEquiv.symm_apply_eq tensorEquiv).mpr (tensorEquiv_mk s c w).symm

/-- Two linear maps on the quark doublets are equal when they agree on the elements built from
  pure tensors. -/
lemma linearMap_ext_mk {f g : QuarkDoublet →ₗ[ℂ] QuarkDoublet}
    (h : ∀ (s : Fermion.LeftHandedWeyl) (c : EuclideanSpace ℂ (Fin 3))
      (w : EuclideanSpace ℂ (Fin 2)), f ⟨(s ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] w⟩ = g ⟨(s ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] w⟩) :
    f = g := by
  have h' : f ∘ₗ valLinEquiv.symm.toLinearMap = g ∘ₗ valLinEquiv.symm.toLinearMap :=
    TensorProduct.ext_threefold fun s c w => h s c w
  refine LinearMap.ext fun q => ?_
  have := LinearMap.congr_fun h' (valLinEquiv q)
  exact this

/-- The representation of the global gauge group on the colour and weak index of the quark
  doublet, the Kronecker product of the fundamental representations of `SU(3)` and `SU(2)`
  twisted by the power `1` of the hypercharge. -/
noncomputable def gaugeRep :
    globalGaugeGroup.group →ₜ* (Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ)ˣ :=
  MatrixRep.charge 1 hypercharge (MatrixRep.kron su3Fund su2Fund)

/-!

## C. The matter field

-/

/-- The quark doublet `(3, 2)_1` as a matter field of the Standard Model global gauge
  group, with its left-handed Lorentz action. -/
noncomputable def matterField : globalGaugeGroup.MatterField :=
  ofMatrixRep tensorEquiv gaugeRep Fermion.LeftHandedWeyl.rep 3 .fermionic

/-- The target space of the matter field is the quark doublets. -/
@[simp]
lemma matterField_V : matterField.V = QuarkDoublet := rfl

/-- The action of the gauge algebra of the matter field is the action matrix of its matrix
  representation. -/
lemma matterField_repAlgebra (c : globalGaugeGroup.lieSubalgebra) :
    matterField.repAlgebra c = MatrixRep.valEnd tensorEquiv (derivMat gaugeRep c) :=
  ofMatrixRep_repAlgebra _ _ _ _ _ c

/-- The Lorentz action of the matter field is that of the left-handed Weyl
  spinor. -/
@[simp]
lemma matterField_repLorentz :
    matterField.repLorentz = MatrixRep.repLorentz tensorEquiv Fermion.LeftHandedWeyl.rep := rfl

/-- The mass weight of the quark doublet. -/
@[simp]
lemma matterField_massWeight : matterField.massWeight = 3 := rfl

/-- The quark doublet is fermionic. -/
@[simp]
lemma matterField_statistic : matterField.statistic = .fermionic := rfl

/-- The Lorentz action of the matter field of the quark doublet is continuous. -/
lemma matterField_lorentzContinuous : matterField.LorentzContinuous :=
  ofMatrixRep_lorentzContinuous _ _ _ 3 _ Fermion.LeftHandedWeyl.continuous_rep_apply

/-- The gauge and Lorentz representations of the matter field of the quark doublet commute. -/
lemma matterField_gaugeLorentzCommute : matterField.GaugeLorentzCommute :=
  ofMatrixRep_gaugeLorentzCommute _ _ _ 3 _

/-- The Lorentz action of the matter field is the left-handed Lorentz action. -/
lemma matterField_repLorentz_eq (Λ : SL(2,ℂ)) :
    (matterField.repLorentz Λ : QuarkDoublet →ₗ[ℂ] QuarkDoublet) =
      repLorentzGroup Λ := by
  refine linearMap_ext_mk fun s c w => ?_
  rw [← tensorEquiv_symm_tmul s c w]
  show MatrixRep.repLorentz tensorEquiv Fermion.LeftHandedWeyl.rep Λ _ = _
  rw [MatrixRep.repLorentz_apply_symm_tmul]
  rw [tensorEquiv_symm_tmul, tensorEquiv_symm_tmul]
  rfl

/-!

## D. The action of matrices on the combined index

-/

/-- The action of a scaled Kronecker product of a colour matrix and a weak matrix on the
  quark doublets, through the identification `tensorEquiv`, is the action of the two matrices on the
  colour and weak factors, scaled. -/
lemma valEnd_smul_kronecker (z : ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (q : QuarkDoublet) :
    MatrixRep.valEnd tensorEquiv (z • (A ⊗ₖ B)) q =
      ⟨z • TensorProduct.map (TensorProduct.map LinearMap.id A.toEuclideanLin)
        B.toEuclideanLin q.val⟩ := by
  have h : (MatrixRep.valEnd tensorEquiv (z • (A ⊗ₖ B)) : QuarkDoublet →ₗ[ℂ] QuarkDoublet) =
      valLinEquiv.symm.toLinearMap ∘ₗ (z • TensorProduct.map (TensorProduct.map LinearMap.id
        A.toEuclideanLin) B.toEuclideanLin) ∘ₗ valLinEquiv.toLinearMap := by
    refine linearMap_ext_mk fun s c w => ?_
    rw [← tensorEquiv_symm_tmul s c w, MatrixRep.valEnd_apply_symm_tmul]
    have hv : (z • (A ⊗ₖ B)).mulVec (colourWeakEquiv (c ⊗ₜ[ℂ] w)) =
        z • colourWeakEquiv (A.toEuclideanLin c ⊗ₜ[ℂ] B.toEuclideanLin w) := by
      funext p
      simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, toEuclideanLin]
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hv, TensorProduct.tmul_smul, map_smul, tensorEquiv_symm_tmul, tensorEquiv_symm_tmul]
    refine QuarkDoublet.ext ?_
    simp [valLinEquiv_symm_apply]
  exact LinearMap.congr_fun h q

/-!

## E. The action of the gauge group

-/

/-- The action of the gauge group on the matter field of the quark doublet,
  through `gaugeGroupEquiv`, is the action `repGaugeGroupI`. -/
lemma matterField_rep_gaugeGroupEquiv (g : GaugeGroupI) :
    (((matterField.rep (gaugeGroupEquiv g) : _ˣ) :
      matterField.V →L[ℂ] matterField.V) : matterField.V →ₗ[ℂ]
        matterField.V) =
        (repGaugeGroupI g : matterField.V →ₗ[ℂ] matterField.V) := by
  have hu : ((u1Phase (gaugeGroupEquiv g) : ℂˣ) : ℂ) = (g.toU1.1 : ℂ) :=
    u1Phase_gaugeGroupEquiv g
  have hs3 : su3Block (gaugeGroupEquiv g) = g.toSU3.1 :=
    su3Block_gaugeGroupEquiv g
  have hs2 : su2Block (gaugeGroupEquiv g) = g.toSU2.1 :=
    su2Block_gaugeGroupEquiv g
  have hM : ((gaugeRep (gaugeGroupEquiv g) : (Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ)ˣ) :
      Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) =
      (g.toU1.1 : ℂ) • ((g.toSU3.1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ
        (g.toSU2.1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    refine (MatrixRep.charge_val 1 hypercharge (MatrixRep.kron su3Fund su2Fund) _).trans ?_
    show ((u1Phase (gaugeGroupEquiv g) ^ (1 : ℤ) : ℂˣ) : ℂ) •
      (su3Block (gaugeGroupEquiv g) ⊗ₖ su2Block (gaugeGroupEquiv g)) = _
    rw [zpow_one, hu, hs3, hs2]
  refine LinearMap.ext fun (q : QuarkDoublet) => ?_
  show MatrixRep.valEnd tensorEquiv
    ((gaugeRep (gaugeGroupEquiv g) : (Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ)ˣ) :
      Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) q = _
  rw [hM, valEnd_smul_kronecker]
  refine QuarkDoublet.ext ?_
  exact (map_smul (TensorProduct.map (TensorProduct.map LinearMap.id
    g.toSU3.1.toEuclideanLin) g.toSU2.1.toEuclideanLin) (g.toU1 : ℂ) q.val).symm

end StandardModel.QuarkDoublet
