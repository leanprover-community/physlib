/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.JetAlgebra.FieldAlgebra.Basic
public import Physlib.ClassicalFieldTheory.JetAlgebra.JetComponentSpace.GaugeAction
/-!
# The gauge action on the field algebra

## i. Overview

Given a fibrewise action of a group `G` on the jets `JetRing ⊗[ℂ] V` of a matter
field, the group `G` acts on the field algebra by the algebra
functor applied to the induced action on the jet component space. On a component function
`∂_s φ_α` the action is the all-orders Leibniz rule: each splitting of the derivative
multiset contributes a Taylor coefficient of the gauge jet against a lower component
function.

Here `G` is any group acting fibrewise on the jets. For the Standard Model, `G` is the jet
gauge group `JetGaugeGroupI`, and the restriction to constant gauge transformations is in
`Physlib.Particles.StandardModel.Matter.FieldAlgebra.GaugeAction`.

## ii. Key results

- `FieldAlgebra.repJet` : the jet gauge action on the field algebra.
- `FieldAlgebra.repJetAlgHom` : the action as an algebra homomorphism.
- `FieldAlgebra.repJet_ofField` : `ofField` is gauge equivariant, for the
  value of the gauge transformation at the base point.

## iii. Table of contents

- A. The action of the group `G`
  - A.1. Equivariance of the field and its conjugate

-/

@[expose] public section

namespace FieldAlgebra

open Matrix MatrixGroups TensorProduct

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]
variable {A : Type} [Ring A] [Algebra ℂ A] [IsFieldAlgebra V A]
variable {G : Type*} [Group G]

/-!

## A. The action of the group `G`

-/

/-- **The jet gauge action on the field algebra** of a `V`-valued matter field, induced
  from a fibrewise action `rep` on the jets of the field: the algebra functor
  applied to the gauge action on the jet component space. The hypothesis `hlin` is the
  statement that a gauge transformation acts on the *values* of the field, over the
  identity on spacetime. -/
noncomputable def repJet
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z) :
    Representation ℂ G (A) where
  toFun U :=
    (map A (JetComponentSpace.repJet rep hlin U)).toLinearMap
  map_one' := by
    simp only [map_one, Module.End.one_eq_id, map_id, AlgHom.toLinearMap_id]
  map_mul' U W := by
    simp only [map_mul, Module.End.mul_eq_comp, ← map_comp_map,
      AlgHom.comp_toLinearMap]

lemma repJet_apply
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : G) (x : A) :
    repJet rep hlin U x =
      map A (JetComponentSpace.repJet rep hlin U) x := rfl

@[simp]
lemma repJet_apply_one
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : G) :
    repJet rep hlin U (1 : A) = 1 := by
  simp [repJet_apply]

lemma repJet_apply_mul
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : G) (x y : A) :
    repJet rep hlin U (x * y) =
      repJet rep hlin U x * repJet rep hlin U y := by
  simp [repJet_apply]

/-- On a component function the jet gauge action is the action on the component space. -/
@[simp]
lemma repJet_ι
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : G) (v : JetComponentSpace V) :
    repJet rep hlin U (ι A v) =
      ι A (JetComponentSpace.repJet rep hlin U v) := by
  rw [repJet_apply, map_ι]

/-- The jet gauge action as an algebra homomorphism: a gauge transformation acts on a
  Lagrangian term factor by factor. -/
noncomputable def repJetAlgHom
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : G) : A →ₐ[ℂ] A where
  toFun := repJet rep hlin U
  map_add' := LinearMap.map_add _
  map_zero' := LinearMap.map_zero _
  map_one' := repJet_apply_one rep hlin U
  map_mul' := repJet_apply_mul rep hlin U
  commutes' r := by simp [repJet_apply]

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
lemma repJet_ofField
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : G) (φ : Module.Dual ℂ V) :
    repJet rep hlin U (ofField A φ) =
      ofField A (Module.Dual.transpose (jetEval ∘ₗ (rep U⁻¹).comp jetOfConstant) φ) := by
  rw [ofField_apply, repJet_ι, ofField_apply]
  congr 1
  refine Prod.ext ?_ ?_
  · exact JetComponentSpace.repDual_one_tmul rep hlin U φ
  · rw [JetComponentSpace.repJet_snd]
    exact map_zero _

/-- **`ofConjField` is gauge equivariant**, for the conjugate action `repConj rep` on the
  jets of the conjugate field — which is the physicists' `φ̄ ↦ φ̄ U†`. -/
lemma repJet_ofConjField
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : G) (φ : Module.Dual ℂ (ConjModule V)) :
    repJet rep hlin U (ofConjField A φ) =
      ofConjField A (Module.Dual.transpose
        (jetEval ∘ₗ (JetComponentSpace.repConj rep U⁻¹).comp jetOfConstant) φ) := by
  rw [ofConjField_apply, repJet_ι, ofConjField_apply]
  congr 1
  refine Prod.ext ?_ ?_
  · rw [JetComponentSpace.repJet_fst]
    exact map_zero _
  · exact JetComponentSpace.repDual_one_tmul (JetComponentSpace.repConj rep)
      (JetComponentSpace.repConj_smul_comm hlin) U φ

end FieldAlgebra
