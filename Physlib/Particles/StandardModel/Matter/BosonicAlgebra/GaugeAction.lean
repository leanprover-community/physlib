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

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]

/-!

## A. The action of the jet gauge group

-/

/-- **The jet gauge action on the bosonic algebra** of a `V`-valued matter field, induced
  from a fibrewise action `rep` on the jets of the field: the symmetric-algebra functor
  applied to the gauge action on the jet component space. The hypothesis `hlin` is the
  statement that a gauge transformation acts on the *values* of the field, over the
  identity on spacetime. -/
noncomputable def repJetGaugeGroupI
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : JetGaugeGroupI) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z) :
    Representation ℂ JetGaugeGroupI (BosonicAlgebra V) where
  toFun U :=
    (SymmetricAlgebra.map (JetComponentSpace.repJetGaugeGroupI rep hlin U)).toLinearMap
  map_one' := by
    simp only [map_one, Module.End.one_eq_id, SymmetricAlgebra.map_id, AlgHom.toLinearMap_id]
  map_mul' U W := by
    simp only [map_mul, Module.End.mul_eq_comp, ← SymmetricAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

lemma repJetGaugeGroupI_apply
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : JetGaugeGroupI) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : JetGaugeGroupI) (x : BosonicAlgebra V) :
    repJetGaugeGroupI rep hlin U x =
      SymmetricAlgebra.map (JetComponentSpace.repJetGaugeGroupI rep hlin U) x := rfl

@[simp]
lemma repJetGaugeGroupI_apply_one
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : JetGaugeGroupI) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : JetGaugeGroupI) :
    repJetGaugeGroupI rep hlin U (1 : BosonicAlgebra V) = 1 := by
  simp [repJetGaugeGroupI_apply]

lemma repJetGaugeGroupI_apply_mul
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : JetGaugeGroupI) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : JetGaugeGroupI) (x y : BosonicAlgebra V) :
    repJetGaugeGroupI rep hlin U (x * y) =
      repJetGaugeGroupI rep hlin U x * repJetGaugeGroupI rep hlin U y := by
  simp [repJetGaugeGroupI_apply]

/-- On a component function the jet gauge action is the action on the component space. -/
@[simp]
lemma repJetGaugeGroupI_ι
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : JetGaugeGroupI) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : JetGaugeGroupI) (v : JetComponentSpace V) :
    repJetGaugeGroupI rep hlin U (SymmetricAlgebra.ι ℂ _ v) =
      SymmetricAlgebra.ι ℂ _ (JetComponentSpace.repJetGaugeGroupI rep hlin U v) := by
  rw [repJetGaugeGroupI_apply, SymmetricAlgebra.map_apply_ι]

/-- The jet gauge action as an algebra homomorphism: a gauge transformation acts on a
  Lagrangian term factor by factor. -/
noncomputable def repJetGaugeGroupIAlgHom
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : JetGaugeGroupI) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : JetGaugeGroupI) : BosonicAlgebra V →ₐ[ℂ] BosonicAlgebra V where
  toFun := repJetGaugeGroupI rep hlin U
  map_add' := LinearMap.map_add _
  map_zero' := LinearMap.map_zero _
  map_one' := repJetGaugeGroupI_apply_one rep hlin U
  map_mul' := repJetGaugeGroupI_apply_mul rep hlin U
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
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : JetGaugeGroupI) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : JetGaugeGroupI) (φ : Module.Dual ℂ V) :
    repJetGaugeGroupI rep hlin U (ofField φ) =
      ofField (Module.Dual.transpose (jetEval ∘ₗ (rep U⁻¹).comp jetOfConstant) φ) := by
  rw [ofField_apply, repJetGaugeGroupI_ι, ofField_apply]
  congr 1
  refine Prod.ext ?_ ?_
  · exact repDual_one_tmul rep hlin U φ
  · rw [JetComponentSpace.repJetGaugeGroupI_snd]
    exact map_zero _

/-- **`ofConjField` is gauge equivariant**, for the conjugate action `repConj rep` on the
  jets of the conjugate field — which is the physicists' `φ̄ ↦ φ̄ U†`. -/
lemma repJetGaugeGroupI_ofConjField
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : JetGaugeGroupI) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : JetGaugeGroupI) (φ : Module.Dual ℂ (ConjModule V)) :
    repJetGaugeGroupI rep hlin U (ofConjField φ) =
      ofConjField (Module.Dual.transpose
        (jetEval ∘ₗ (repConj rep U⁻¹).comp jetOfConstant) φ) := by
  rw [ofConjField_apply, repJetGaugeGroupI_ι, ofConjField_apply]
  congr 1
  refine Prod.ext ?_ ?_
  · rw [JetComponentSpace.repJetGaugeGroupI_fst]
    exact map_zero _
  · exact repDual_one_tmul (repConj rep) (repConj_smul_comm hlin) U φ

/-!

## B. Constant gauge transformations

-/

/-- The action of the constant — that is, global — gauge transformations on the bosonic
  algebra, obtained by including a gauge transformation as a constant gauge jet. -/
noncomputable def repGaugeGroupI
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : JetGaugeGroupI) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z) :
    Representation ℂ GaugeGroupI (BosonicAlgebra V) :=
  (repJetGaugeGroupI rep hlin).comp JetGaugeGroupI.ofConstant

lemma repGaugeGroupI_apply
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : JetGaugeGroupI) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (g : GaugeGroupI) (x : BosonicAlgebra V) :
    repGaugeGroupI rep hlin g x =
      repJetGaugeGroupI rep hlin (JetGaugeGroupI.ofConstant g) x := rfl

@[simp]
lemma repGaugeGroupI_apply_one
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : JetGaugeGroupI) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (g : GaugeGroupI) :
    repGaugeGroupI rep hlin g (1 : BosonicAlgebra V) = 1 :=
  repJetGaugeGroupI_apply_one rep hlin _

lemma repGaugeGroupI_apply_mul
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : JetGaugeGroupI) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (g : GaugeGroupI) (x y : BosonicAlgebra V) :
    repGaugeGroupI rep hlin g (x * y) =
      repGaugeGroupI rep hlin g x * repGaugeGroupI rep hlin g y :=
  repJetGaugeGroupI_apply_mul rep hlin _ x y

/-- A constant gauge transformation acts on the undifferentiated field by the
  contragredient of its value — which for a constant jet is the transformation itself. -/
lemma repGaugeGroupI_ofField
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : JetGaugeGroupI) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (g : GaugeGroupI) (φ : Module.Dual ℂ V) :
    repGaugeGroupI rep hlin g (ofField φ) =
      ofField (Module.Dual.transpose
        (jetEval ∘ₗ (rep (JetGaugeGroupI.ofConstant g⁻¹)).comp jetOfConstant) φ) := by
  have h : (JetGaugeGroupI.ofConstant g)⁻¹ = JetGaugeGroupI.ofConstant g⁻¹ :=
    (map_inv JetGaugeGroupI.ofConstant g).symm
  rw [repGaugeGroupI_apply, repJetGaugeGroupI_ofField, h]

/-- A constant gauge transformation acts on the undifferentiated conjugate field by the
  conjugate contragredient of its value. -/
lemma repGaugeGroupI_ofConjField
    (rep : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : JetGaugeGroupI) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (g : GaugeGroupI) (φ : Module.Dual ℂ (ConjModule V)) :
    repGaugeGroupI rep hlin g (ofConjField φ) =
      ofConjField (Module.Dual.transpose
        (jetEval ∘ₗ (repConj rep (JetGaugeGroupI.ofConstant g⁻¹)).comp jetOfConstant) φ) := by
  have h : (JetGaugeGroupI.ofConstant g)⁻¹ = JetGaugeGroupI.ofConstant g⁻¹ :=
    (map_inv JetGaugeGroupI.ofConstant g).symm
  rw [repGaugeGroupI_apply, repJetGaugeGroupI_ofConjField, h]

end BosonicAlgebra

end StandardModel
