/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.JetAlgebra.FieldAlgebra.GaugeAction
/-!
# Constant gauge transformations on a field algebra

## i. Overview

A jet gauge group `G` contains the constant — that is, global — gauge transformations as
the image of a homomorphism `ι : G₀ →* G` from the value group `G₀` (for the Standard Model,
`JetGaugeGroupI.ofConstant`). Restricting the jet gauge action `FieldAlgebra.repJet` along
`ι` gives the action of the global gauge group on the field algebra, which is diagonal in
the derivative label: it is the action whose invariants the classification theorems
describe.

## ii. Key results

- `FieldAlgebra.repConstant` : the action of the constant gauge transformations.
- `FieldAlgebra.repConstant_ofField`, `FieldAlgebra.repConstant_ofConjField` : on the
  undifferentiated field it is the contragredient of the value.

-/

@[expose] public section

namespace FieldAlgebra

open TensorProduct

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]
variable {A : Type} [Ring A] [Algebra ℂ A] [IsFieldAlgebra V A]
variable {G : Type} [Group G] {G₀ : Type} [Group G₀] (ι : G₀ →* G)

/-- The action of the constant — that is, global — gauge transformations on the field
  algebra: the restriction of the jet gauge action along the inclusion `ι : G₀ →* G` of the
  constant jets. -/
noncomputable def repConstant
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z) :
    Representation ℂ G₀ A :=
  (repJet rep hlin).comp ι

lemma repConstant_apply
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (g : G₀) (x : A) :
    repConstant ι rep hlin g x =
      repJet rep hlin (ι g) x := rfl

@[simp]
lemma repConstant_apply_one
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (g : G₀) :
    repConstant ι rep hlin g (1 : A) = 1 :=
  repJet_apply_one rep hlin _

lemma repConstant_apply_mul
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (g : G₀) (x y : A) :
    repConstant ι rep hlin g (x * y) =
      repConstant ι rep hlin g x * repConstant ι rep hlin g y :=
  repJet_apply_mul rep hlin _ x y

/-- A constant gauge transformation acts on the undifferentiated field by the
  contragredient of its value — which for a constant jet is the transformation itself. -/
lemma repConstant_ofField
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (g : G₀) (φ : Module.Dual ℂ V) :
    repConstant ι rep hlin g (ofField A φ) =
      ofField A (Module.Dual.transpose
        (jetEval ∘ₗ (rep (ι g⁻¹)).comp jetOfConstant) φ) := by
  have h : (ι g)⁻¹ = ι g⁻¹ :=
    (map_inv ι g).symm
  rw [repConstant_apply, repJet_ofField, h]

/-- A constant gauge transformation acts on the undifferentiated conjugate field by the
  conjugate contragredient of its value. -/
lemma repConstant_ofConjField
    (rep : Representation ℂ G (JetRing ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (g : G₀) (φ : Module.Dual ℂ (ConjModule V)) :
    repConstant ι rep hlin g (ofConjField A φ) =
      ofConjField A (Module.Dual.transpose
        (jetEval ∘ₗ (JetComponentSpace.repConj rep (ι g⁻¹)).comp
          jetOfConstant) φ) := by
  have h : (ι g)⁻¹ = ι g⁻¹ :=
    (map_inv ι g).symm
  rw [repConstant_apply, repJet_ofConjField, h]

end FieldAlgebra
