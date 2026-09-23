/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.Basic
/-!
# The gauge action on the bosonic algebra

## i. Overview

Given a fibrewise action of the jet gauge group on the jets `JetRing ⊗[ℂ] V` of a bosonic
matter field, the jet gauge group acts on the bosonic algebra by the symmetric-algebra
functor applied to the induced action on the jet component space. On a component function
`∂_s φ_α` the action is the all-orders Leibniz rule: each splitting of the derivative
multiset contributes a Taylor coefficient of the gauge jet against a lower component
function.

Restricting along `JetGaugeGroupI.ofConstant` gives the action of the constant — that is,
global — gauge transformations, which is diagonal in the derivative label.

## ii. Key results

- `BosonicAlgebra.repJetGaugeGroupI` : the jet gauge action on the bosonic algebra.
- `BosonicAlgebra.repJetGaugeGroupIAlgHom` : the action as an algebra homomorphism.
- `BosonicAlgebra.repJetGaugeGroupI_ofField` : `ofField` is gauge equivariant, for the
  value of the gauge transformation at the base point.
- `BosonicAlgebra.repGaugeGroupI` : the action of the constant gauge transformations.

## iii. Table of contents

- A. The action of the jet gauge group
  - A.1. Equivariance of the field and its conjugate
- B. Constant gauge transformations

-/

@[expose] public section

namespace StandardModel

namespace BosonicAlgebra

open Matrix MatrixGroups TensorProduct

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} (M : MatterField jets)

/-!

## A. The action of the jet gauge group

-/

/-- **The jet gauge action on the bosonic algebra** of the matter field `M`: the symmetric-algebra functor
  applied to the gauge action on the jet component space. The fibrewise action on the jets and its
  fibrewise-linearity are fields of `M`. -/
noncomputable def repJetGaugeGroupI :
    Representation ℂ GJ (BosonicAlgebra M) where
  toFun U :=
    (SymmetricAlgebra.map (JetComponentSpace.repJet M U)).toLinearMap
  map_one' := by
    simp only [map_one, Module.End.one_eq_id, SymmetricAlgebra.map_id, AlgHom.toLinearMap_id]
  map_mul' U W := by
    simp only [map_mul, Module.End.mul_eq_comp, ← SymmetricAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

lemma repJetGaugeGroupI_apply
    (U : GJ) (x : BosonicAlgebra M) :
    repJetGaugeGroupI M U x =
      SymmetricAlgebra.map (JetComponentSpace.repJet M U) x := rfl

@[simp]
lemma repJetGaugeGroupI_apply_one
    (U : GJ) :
    repJetGaugeGroupI M U (1 : BosonicAlgebra M) = 1 := by
  simp [repJetGaugeGroupI_apply]

lemma repJetGaugeGroupI_apply_mul
    (U : GJ) (x y : BosonicAlgebra M) :
    repJetGaugeGroupI M U (x * y) =
      repJetGaugeGroupI M U x * repJetGaugeGroupI M U y := by
  simp [repJetGaugeGroupI_apply]

/-- On a component function the jet gauge action is the action on the component space. -/
@[simp]
lemma repJetGaugeGroupI_ι
    (U : GJ) (v : JetComponentSpace M) :
    repJetGaugeGroupI M U (SymmetricAlgebra.ι ℂ _ v) =
      SymmetricAlgebra.ι ℂ _ (JetComponentSpace.repJet M U v) := by
  rw [repJetGaugeGroupI_apply, SymmetricAlgebra.map_apply_ι]

/-- The jet gauge action as an algebra homomorphism: a gauge transformation acts on a
  Lagrangian term factor by factor. -/
noncomputable def repJetGaugeGroupIAlgHom
    (U : GJ) : BosonicAlgebra M →ₐ[ℂ] BosonicAlgebra M where
  toFun := repJetGaugeGroupI M U
  map_add' := LinearMap.map_add _
  map_zero' := LinearMap.map_zero _
  map_one' := repJetGaugeGroupI_apply_one M U
  map_mul' := repJetGaugeGroupI_apply_mul M U
  commutes' r := by simp [repJetGaugeGroupI_apply]

/-!

### A.1. Equivariance of the field and its conjugate

Unlike a derivative generator `∂_s φ_α`, which mixes with lower generators through the
Taylor coefficients of the gauge jet, the undifferentiated generator `φ_α` transforms by
the *value* of the gauge transformation at the base point alone. So `ofField` and
`ofConjField` are equivariant on the nose, for the contragredient of that value.

-/

/-- **`ofField` is gauge equivariant.** The undifferentiated component functions transform
  by the contragredient of the value of the gauge transformation at the base point; no
  derivative of the gauge jet contributes. -/
lemma repJetGaugeGroupI_ofField
    (U : GJ) (φ : Module.Dual ℂ M.V) :
    repJetGaugeGroupI M U (ofField φ) =
      ofField (Module.Dual.transpose (jetEval ∘ₗ (M.repJet U⁻¹).comp jetOfConstant) φ) := by
  rw [ofField_apply, repJetGaugeGroupI_ι, ofField_apply]
  congr 1
  refine Prod.ext ?_ ?_
  · exact JetComponentSpace.repDual_one_tmul M.repJet M.repJet_smul U φ
  · rw [JetComponentSpace.repJet_snd]
    exact map_zero _

/-- **`ofConjField` is gauge equivariant**, for the conjugate action
  `JetComponentSpace.repConj rep` on the
  jets of the conjugate field — which is the physicists' `φ̄ ↦ φ̄ U†`. -/
lemma repJetGaugeGroupI_ofConjField
    (U : GJ) (φ : Module.Dual ℂ (ConjModule M.V)) :
    repJetGaugeGroupI M U (ofConjField φ) =
      ofConjField (Module.Dual.transpose
        (jetEval ∘ₗ (JetComponentSpace.repConj M.repJet U⁻¹).comp jetOfConstant) φ) := by
  rw [ofConjField_apply, repJetGaugeGroupI_ι, ofConjField_apply]
  congr 1
  refine Prod.ext ?_ ?_
  · rw [JetComponentSpace.repJet_fst]
    exact map_zero _
  · exact JetComponentSpace.repDual_one_tmul (JetComponentSpace.repConj M.repJet)
      (JetComponentSpace.repConj_smul_comm M.repJet_smul) U φ

/-!

## B. Constant gauge transformations

-/

/-- The action of the constant — that is, global — gauge transformations on the bosonic
  algebra, obtained by including a gauge transformation as a constant gauge jet. -/
noncomputable def repGaugeGroupI :
    Representation ℂ G₀ (BosonicAlgebra M) :=
  (repJetGaugeGroupI M).comp jets.ofConstant

lemma repGaugeGroupI_apply
    (g : G₀) (x : BosonicAlgebra M) :
    repGaugeGroupI M g x =
      repJetGaugeGroupI M (jets.ofConstant g) x := rfl

@[simp]
lemma repGaugeGroupI_apply_one
    (g : G₀) :
    repGaugeGroupI M g (1 : BosonicAlgebra M) = 1 :=
  repJetGaugeGroupI_apply_one M _

lemma repGaugeGroupI_apply_mul
    (g : G₀) (x y : BosonicAlgebra M) :
    repGaugeGroupI M g (x * y) =
      repGaugeGroupI M g x * repGaugeGroupI M g y :=
  repJetGaugeGroupI_apply_mul M _ x y

/-- A constant gauge transformation acts on the undifferentiated field by the
  contragredient of its value — which for a constant jet is the transformation itself. -/
lemma repGaugeGroupI_ofField
    (g : G₀) (φ : Module.Dual ℂ M.V) :
    repGaugeGroupI M g (ofField φ) =
      ofField (Module.Dual.transpose
        (jetEval ∘ₗ (M.repJet (jets.ofConstant g⁻¹)).comp jetOfConstant) φ) := by
  have h : (jets.ofConstant g)⁻¹ = jets.ofConstant g⁻¹ :=
    (map_inv jets.ofConstant g).symm
  rw [repGaugeGroupI_apply, repJetGaugeGroupI_ofField, h]

/-- A constant gauge transformation acts on the undifferentiated conjugate field by the
  conjugate contragredient of its value. -/
lemma repGaugeGroupI_ofConjField
    (g : G₀) (φ : Module.Dual ℂ (ConjModule M.V)) :
    repGaugeGroupI M g (ofConjField φ) =
      ofConjField (Module.Dual.transpose
        (jetEval ∘ₗ (JetComponentSpace.repConj M.repJet (jets.ofConstant g⁻¹)).comp
          jetOfConstant) φ) := by
  have h : (jets.ofConstant g)⁻¹ = jets.ofConstant g⁻¹ :=
    (map_inv jets.ofConstant g).symm
  rw [repGaugeGroupI_apply, repJetGaugeGroupI_ofConjField, h]

end BosonicAlgebra

end StandardModel
