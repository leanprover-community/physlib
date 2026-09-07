/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.JetAlgebra.FieldAlgebra.ConstantGaugeAction
public import Physlib.ClassicalFieldTheory.JetAlgebra.FieldAlgebra.LorentzAction
public import Physlib.ClassicalFieldTheory.JetAlgebra.FieldAlgebra.MassDim
public import Physlib.ClassicalFieldTheory.JetAlgebra.FieldAlgebra.Statistics
/-!
# Matter fields of a gauge theory

## i. Overview

A matter field of a gauge theory with (jet) gauge group `G` is specified by the data a
physicist writes down: a finite-dimensional complex vector space `V` in which the field
takes its values, the representation of the Lorentz group on `V`, the action of the jets of
gauge transformations on the jets of the field — which must be *fibrewise*, that is act on the
values of the field over the identity of spacetime — and the mass weight of the field.

`MatterField G` bundles this data. From it the general theory produces, on any field algebra
`A` over `V` (bosonic or fermionic), the jet gauge action, the global gauge action, the
Lorentz action and the mass-weight scaling. A concrete theory therefore only has to supply
a `MatterField` for each of its fields.

## ii. Key results

- `MatterField` : the data of a matter field.
- `MatterField.repJetAlgebra` : the jet gauge action on a field algebra of the field.
- `MatterField.repConstant` : the global gauge action, along `ι : G₀ →* G`.
- `MatterField.repLorentzGroup` : the Lorentz action on a field algebra of the field.
- `MatterField.massWeightScale` : the mass-weight scaling on a field algebra of the field.

## iii. Table of contents

- A. The data of a matter field
- B. The bosonic and fermionic jet algebras
- C. The actions on a field algebra of the matter field

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

/-!

## A. The data of a matter field

-/

/-- **A matter field** of a gauge theory with jet gauge group `G`: a finite-dimensional complex
  target space `V`, the Lorentz representation on `V`, a fibrewise action of `G` on the
  jets `JetRing ⊗[ℂ] V` of the field, and the mass weight of the field (in the units in
  which a derivative has weight `2`). -/
structure MatterField (G : Type) [Group G] where
  /-- The target space of the field. -/
  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module ℂ V]
  [instFree : Module.Free ℂ V]
  [instFinite : Module.Finite ℂ V]
  /-- The representation of the Lorentz group on the target space. -/
  repLorentz : Representation ℂ SL(2,ℂ) V
  /-- The action of the jets of gauge transformations on the jets of the field. -/
  repJet : Representation ℂ G (JetRing ⊗[ℂ] V)
  /-- The gauge action is fibrewise: it commutes with multiplication by scalar jets. -/
  repJet_smul : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V), repJet U (χ • z) = χ • repJet U z
  /-- The mass weight of the field. -/
  massWeight : ℕ

attribute [instance] MatterField.instAddCommGroup MatterField.instModule
  MatterField.instFree MatterField.instFinite

namespace MatterField

variable {G : Type} [Group G] (M : MatterField G)

/-!

## B. The bosonic and fermionic jet algebras

-/

/-- The bosonic jet algebra of a matter field. -/
abbrev BosonicJetAlgebra : Type := BosonicAlgebra M.V

/-- The fermionic jet algebra of a matter field. -/
abbrev FermionicJetAlgebra : Type := FermionicAlgebra M.V

/-!

## C. The actions on a field algebra of the matter field

-/

variable (A : Type) [Ring A] [Algebra ℂ A] [IsFieldAlgebra M.V A]

/-- The jet gauge action on a field algebra of the matter field. -/
noncomputable def repJetAlgebra : Representation ℂ G A :=
  FieldAlgebra.repJet M.repJet M.repJet_smul

/-- The global gauge action on a field algebra of the matter field, along the inclusion
  `ι : G₀ →* G` of the constant jets. -/
noncomputable def repConstant {G₀ : Type} [Group G₀] (ι : G₀ →* G) : Representation ℂ G₀ A :=
  FieldAlgebra.repConstant ι M.repJet M.repJet_smul

/-- The Lorentz action on a field algebra of the matter field. -/
noncomputable def repLorentzGroup : Representation ℂ SL(2,ℂ) A :=
  FieldAlgebra.repLorentzGroup M.repLorentz

/-- The mass-weight scaling on a field algebra of the matter field. -/
noncomputable def massWeightScale (c : ℂ) : A →ₐ[ℂ] A :=
  FieldAlgebra.massWeightScale M.massWeight c

lemma repJetAlgebra_ι (U : G) (x : JetComponentSpace M.V) :
    M.repJetAlgebra A U (FieldAlgebra.ι A x) =
      FieldAlgebra.ι A (JetComponentSpace.repJet M.repJet M.repJet_smul U x) :=
  FieldAlgebra.repJet_ι _ _ U x

lemma repConstant_apply {G₀ : Type} [Group G₀] (ι : G₀ →* G) (g : G₀) :
    M.repConstant A ι g = M.repJetAlgebra A (ι g) := rfl

lemma repLorentzGroup_ι (Λ : SL(2,ℂ)) (x : JetComponentSpace M.V) :
    M.repLorentzGroup A Λ (FieldAlgebra.ι A x) =
      FieldAlgebra.ι A (JetComponentSpace.repLorentzGroup M.repLorentz Λ x) :=
  FieldAlgebra.repLorentzGroup_ι _ Λ x

lemma massWeightScale_ι (c : ℂ) (x : JetComponentSpace M.V) :
    M.massWeightScale A c (FieldAlgebra.ι A x) =
      FieldAlgebra.ι A (JetComponentSpace.massWeightScale M.massWeight c x) :=
  FieldAlgebra.massWeightScale_ι _ c x

end MatterField
