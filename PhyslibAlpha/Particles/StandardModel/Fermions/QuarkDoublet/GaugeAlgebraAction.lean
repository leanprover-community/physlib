/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.Fermions.QuarkDoublet.MatterField
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.LieAlgebra
public import PhyslibAlpha.Mathematics.TensorProductComm
/-!
# The infinitesimal gauge action on the quark doublet

The explicit `(3, 2)_{1}` action of the gauge algebra on the quark doublet, and its agreement
with the matter field.

## i. Overview

The `(3, 2)_{1}` action of the gauge algebra on the quark doublet. The colour and weak
parts of the algebra element act on the combined colour–weak index through the Kronecker
sum, and the hypercharge part scales, all through the physicists' factor of `i`, matching
the group action `u • (U₃ ⊗ₖ U₂)` infinitesimally. The action is the action of the gauge
algebra of the matter field of the quark doublet, transported along
`StandardModel.gaugeAlgebraEquiv`, and it commutes with the Lorentz action.

## ii. Key results

- `colourWeakEnd` : the endomorphism of the quark doublet defined by a colour–weak
  matrix.
- `gaugeAlgebraAction` : the infinitesimal `(3, 2)_{1}` action of the gauge algebra.
- `matterField_repAlgebra_gaugeAlgebraEquiv` : the action of the gauge algebra of the
  matter field is `gaugeAlgebraAction`.
- `gaugeAlgebraAction_comm_repLorentzGroup` : the gauge action commutes with the Lorentz
  action.

## iii. Table of contents

- A. The action of the gauge algebra
- B. The matter field
- C. The gauge action commutes with the Lorentz action

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open TensorProduct

namespace QuarkDoublet

open Matrix MatrixGroups Kronecker

/-!

## A. The action of the gauge algebra

-/

/-- The complex-linear identification of the quark doublet with a left-handed Weyl spinor
  tensored with a colour–weak vector over the combined index `Fin 3 × Fin 2`. -/
noncomputable def colourWeakValLinEquiv :
    QuarkDoublet ≃ₗ[ℂ] Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3 × Fin 2) :=
  (valLinEquiv.trans (TensorProduct.assoc ℂ Fermion.LeftHandedWeyl
      (EuclideanSpace ℂ (Fin 3)) (EuclideanSpace ℂ (Fin 2)))).trans <|
    TensorProduct.congr (LinearEquiv.refl ℂ Fermion.LeftHandedWeyl)
      (colourWeakEquiv.trans (WithLp.linearEquiv 2 ℂ (Fin 3 × Fin 2 → ℂ)).symm)

/-- The endomorphism of the quark doublet defined by a complex matrix over the
  combined colour–weak index, with the Weyl factor untouched. -/
noncomputable def colourWeakEnd (A : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) :
    QuarkDoublet →ₗ[ℂ] QuarkDoublet :=
  colourWeakValLinEquiv.symm.toLinearMap ∘ₗ
    Module.End.lTensorAlgHom ℂ (EuclideanSpace ℂ (Fin 3 × Fin 2)) Fermion.LeftHandedWeyl
      (Matrix.toLpLinAlgEquiv 2 A) ∘ₗ colourWeakValLinEquiv.toLinearMap

lemma colourWeakEnd_apply_mk (A : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ)
    (v : QuarkDoublet) :
    colourWeakEnd A v
      = colourWeakValLinEquiv.symm
          (Module.End.lTensorAlgHom ℂ (EuclideanSpace ℂ (Fin 3 × Fin 2))
            Fermion.LeftHandedWeyl
            (Matrix.toLpLinAlgEquiv 2 A) (colourWeakValLinEquiv v)) := rfl

lemma colourWeakEnd_add (A B : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) :
    colourWeakEnd (A + B) = colourWeakEnd A + colourWeakEnd B := by
  rw [colourWeakEnd, colourWeakEnd, colourWeakEnd, map_add, map_add,
    LinearMap.add_comp, LinearMap.comp_add]

lemma colourWeakEnd_smul (z : ℂ) (A : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) :
    colourWeakEnd (z • A) = z • colourWeakEnd A := by
  rw [colourWeakEnd, colourWeakEnd, map_smul, map_smul, LinearMap.smul_comp,
    LinearMap.comp_smul]

/-- The matrix of the infinitesimal `(3, 2)_{1}` action of a gauge algebra element on
  the combined colour–weak index, `i` times the Kronecker sum of the colour and weak
  parts shifted by `i` times the hypercharge. -/
noncomputable def actionMatrix (c : GaugeAlgebra) :
    Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ :=
  Complex.I • (c.toSU3Matrix ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    + (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ c.toSU2Matrix
    + c.toU1Value • 1)

/-- The infinitesimal action of the gauge algebra on the quark doublet, the derivative of
  the `(3, 2)_{1}` action of the gauge group, real-linear in the algebra slot and
  complex-linear in the value slot. -/
noncomputable def gaugeAlgebraAction :
    GaugeAlgebra →ₗ[ℝ] QuarkDoublet →ₗ[ℂ] QuarkDoublet where
  toFun c := colourWeakEnd (actionMatrix c)
  map_add' c₁ c₂ := by
    rw [show actionMatrix (c₁ + c₂) = actionMatrix c₁ + actionMatrix c₂ from by
      rw [actionMatrix, actionMatrix, actionMatrix, GaugeAlgebra.add_toSU3Matrix,
        GaugeAlgebra.add_toSU2Matrix, GaugeAlgebra.add_toU1Value,
        Matrix.add_kronecker, Matrix.kronecker_add]
      module]
    rw [colourWeakEnd_add]
  map_smul' r c := by
    rw [show actionMatrix (r • c) = (r : ℂ) • actionMatrix c from by
      rw [actionMatrix, actionMatrix, GaugeAlgebra.smul_toSU3Matrix,
        GaugeAlgebra.smul_toSU2Matrix, GaugeAlgebra.smul_toU1Value,
        show (r • c.toSU3Matrix : Matrix (Fin 3) (Fin 3) ℂ)
          = (r : ℂ) • c.toSU3Matrix from by
        rw [← algebraMap_smul ℂ r c.toSU3Matrix]; rfl,
        show (r • c.toSU2Matrix : Matrix (Fin 2) (Fin 2) ℂ)
          = (r : ℂ) • c.toSU2Matrix from by
        rw [← algebraMap_smul ℂ r c.toSU2Matrix]; rfl,
        show r • c.toU1Value = (r : ℂ) • c.toU1Value from by
        rw [← algebraMap_smul ℂ r c.toU1Value]; rfl,
        Matrix.smul_kronecker, Matrix.kronecker_smul]
      module,
      colourWeakEnd_smul]
    refine LinearMap.ext fun v => ?_
    rw [RingHom.id_apply]
    show (r : ℂ) • colourWeakEnd (actionMatrix c) v
      = r • colourWeakEnd (actionMatrix c) v
    rw [show ((r : ℝ) : ℂ) = algebraMap ℝ ℂ r from rfl, algebraMap_smul]

/-!

## B. The matter field

-/

open GlobalGaugeGroup GlobalGaugeGroup.MatterField

/-- The colour–weak endomorphism of a matrix is the endomorphism of the matter field
  of the quark doublet defined by that matrix. -/
lemma colourWeakEnd_eq_valEnd (A : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) :
    colourWeakEnd A = MatrixRep.valEnd tensorEquiv A := by
  have h : colourWeakEnd A ∘ₗ tensorEquiv.symm.toLinearMap =
      MatrixRep.valEnd tensorEquiv A ∘ₗ tensorEquiv.symm.toLinearMap := by
    refine TensorProduct.ext' fun s v => ?_
    show colourWeakEnd A (tensorEquiv.symm (s ⊗ₜ[ℂ] v))
      = MatrixRep.valEnd tensorEquiv A (tensorEquiv.symm (s ⊗ₜ[ℂ] v))
    rw [MatrixRep.valEnd_apply_symm_tmul]
    refine colourWeakValLinEquiv.injective ?_
    rw [colourWeakEnd_apply_mk, LinearEquiv.apply_symm_apply]
    have key : ∀ q, colourWeakValLinEquiv q = TensorProduct.map LinearMap.id
        (WithLp.linearEquiv 2 ℂ (Fin 3 × Fin 2 → ℂ)).symm.toLinearMap (tensorEquiv q) := fun q => by
      simp only [colourWeakValLinEquiv, tensorEquiv, LinearEquiv.trans_apply]
      generalize (TensorProduct.assoc ℂ Fermion.LeftHandedWeyl (EuclideanSpace ℂ (Fin 3))
        (EuclideanSpace ℂ (Fin 2))) (valLinEquiv q) = z
      induction z using TensorProduct.inductionOn with
      | tmul a b => simp
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [key, key, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      TensorProduct.map_tmul, TensorProduct.map_tmul]
    rfl
  exact LinearMap.ext fun q => by simpa using LinearMap.congr_fun h (tensorEquiv q)

/-- The matrix of the action of the gauge algebra element `gaugeAlgebraEquiv c` in the
  gauge representation of the quark doublet is `actionMatrix c`. -/
lemma derivMat_gaugeRep_gaugeAlgebraEquiv (c : GaugeAlgebra) :
    derivMat gaugeRep (gaugeAlgebraEquiv c) = actionMatrix c := by
  show derivMat (MatrixRep.charge 1 hypercharge (MatrixRep.kron su3Fund su2Fund))
    (gaugeAlgebraEquiv c) = _
  rw [MatrixRep.derivMat_charge 1 hypercharge (MatrixRep.kron su3Fund su2Fund)
    (z := Complex.I * c.toU1Value) (hypercharge_exp_gaugeAlgebraEquiv c),
    MatrixRep.derivMat_kron, derivMat_su3Fund_gaugeAlgebraEquiv,
    derivMat_su2Fund_gaugeAlgebraEquiv, actionMatrix, Matrix.smul_kronecker,
    Matrix.kronecker_smul]
  simp [smul_add, smul_smul]

/-- The action of the gauge algebra of the matter field of the quark doublet, on the
  image of `gaugeAlgebraEquiv`, is `gaugeAlgebraAction`. -/
lemma matterField_repAlgebra_gaugeAlgebraEquiv (c : GaugeAlgebra) :
    matterField.repAlgebra (gaugeAlgebraEquiv c) = gaugeAlgebraAction c := by
  rw [matterField_repAlgebra, derivMat_gaugeRep_gaugeAlgebraEquiv]
  exact (colourWeakEnd_eq_valEnd _).symm

/-!

## C. The gauge action commutes with the Lorentz action

-/

/-- The infinitesimal gauge action on the quark doublet acts on the combined colour–weak
  factor, the Lorentz action on the Weyl factor, so the two commute. -/
lemma gaugeAlgebraAction_comm_repLorentzGroup (c : GaugeAlgebra) (Λ : SL(2,ℂ))
    (v : QuarkDoublet) :
    QuarkDoublet.gaugeAlgebraAction c (QuarkDoublet.repLorentzGroup Λ v) =
      QuarkDoublet.repLorentzGroup Λ (QuarkDoublet.gaugeAlgebraAction c v) := by
  have hg : ∀ x : QuarkDoublet, QuarkDoublet.colourWeakValLinEquiv
      (QuarkDoublet.gaugeAlgebraAction c x) =
      LinearMap.lTensor Fermion.LeftHandedWeyl
        (Matrix.toLpLinAlgEquiv 2 (QuarkDoublet.actionMatrix c))
        (QuarkDoublet.colourWeakValLinEquiv x) := fun x => by
    rw [show QuarkDoublet.gaugeAlgebraAction c x =
      QuarkDoublet.colourWeakEnd (QuarkDoublet.actionMatrix c) x from rfl,
      QuarkDoublet.colourWeakEnd_apply_mk, LinearEquiv.apply_symm_apply]
    rfl
  have hl : ∀ x : QuarkDoublet, QuarkDoublet.colourWeakValLinEquiv
      (QuarkDoublet.repLorentzGroup Λ x) =
      TensorProduct.map (Fermion.LeftHandedWeyl.rep Λ) LinearMap.id
        (QuarkDoublet.colourWeakValLinEquiv x) := fun x => by
    have h1 : QuarkDoublet.valLinEquiv (QuarkDoublet.repLorentzGroup Λ x) =
        TensorProduct.map (TensorProduct.map (Fermion.LeftHandedWeyl.rep Λ) LinearMap.id)
          LinearMap.id (QuarkDoublet.valLinEquiv x) := rfl
    simp only [QuarkDoublet.colourWeakValLinEquiv, LinearEquiv.trans_apply, h1]
    exact congr_assoc_map_id_comm _ _ _
  refine QuarkDoublet.colourWeakValLinEquiv.injective ?_
  rw [hg (QuarkDoublet.repLorentzGroup Λ v), hl v,
    hl (QuarkDoublet.gaugeAlgebraAction c v), hg v]
  exact lTensor_map_id_comm _ _ _

end QuarkDoublet

end StandardModel
