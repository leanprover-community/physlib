/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.InfinitesimalAction
/-!
# Matter fields of a gauge theory

## i. Overview

A matter field of a gauge theory is specified by the data a physicist writes down: a
finite-dimensional complex vector space `V` in which the field takes its values, the
representation of the Lorentz group on `V`, the action of the jets of gauge
transformations on the jets of the field — which must be *fibrewise*, that is act on the
values of the field over the identity of spacetime — and the mass weight of the field.
All of this is relative to a gauge context `jets : LocalGaugeData G 𝔤 G₀ 𝔤J`: the jet gauge
group `G` the field's jet action is a representation of, and the global group `G₀`, Lie
algebras `𝔤`, `𝔤J` and structure maps that make `G` the jets of `G₀` rather than an
unrelated group. Fixing `jets` rather than `G` alone is what lets the global gauge action
`repConstant` below be taken along the *canonical* inclusion `jets.ofConstant`, instead of
an arbitrary homomorphism supplied by hand.

`MatterField jets` bundles this data. From it the general theory produces, on any field
algebra `A` of the field (bosonic or fermionic), the jet gauge action, the global gauge
action, the Lorentz action and the mass-weight scaling — all in
`Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.FieldAlgebra`, downstream of the
component space this file's data indexes. A concrete theory therefore only has to supply a
`MatterField` for each of its fields.

## ii. Key results

- `MatterField` : the data of a matter field.

## iii. Table of contents

- A. The data of a matter field


-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

/-!

## A. The data of a matter field

-/

/-- **A matter field** of a gauge theory over the gauge context `jets : LocalGaugeData G 𝔤 G₀ 𝔤J`:
  a finite-dimensional complex target space `V`, the Lorentz representation on `V`, a
  fibrewise action of `G` on the jets `JetRing ⊗[ℂ] V` of the field, the infinitesimal
  action of the gauge algebra generating it, and the mass weight of the field (in the units
  in which a derivative has weight `2`). -/
structure MatterField {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
    (jets : LocalGaugeData G 𝔤 G₀ 𝔤J) where
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
  /-- The action of the gauge algebra. -/
  repAlgebra : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V
  /-- The gauge action is fibrewise: it commutes with multiplication by scalar jets. -/
  repJet_smul : ∀ (U : G) (χ : JetRing) (z : JetRing ⊗[ℂ] V), repJet U (χ • z) = χ • repJet U z
  /-- The action of the gauge algebra generates the action of the jets of gauge
    transformations: it is the infinitesimal action underlying `repJet`, the physicists'
    `i dρ(T^a)`. This is what makes the covariant derivative of the field transform
    covariantly. -/
  repAlgebra_isInfinitesimalAction : jets.IsInfinitesimalActionOf repAlgebra repJet
  /-- The mass weight of the field. -/
  massWeight : ℕ

attribute [instance] MatterField.instAddCommGroup MatterField.instModule
  MatterField.instFree MatterField.instFinite

namespace MatterField

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G 𝔤 G₀ 𝔤J} (M : MatterField jets)

end MatterField
