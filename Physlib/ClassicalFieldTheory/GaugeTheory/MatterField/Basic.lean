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
All of this is relative to a gauge context `jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J`: the jet gauge
group `GJ` the field's jet action is a representation of, and the global group `G₀`, Lie
algebras `𝔤`, `𝔤J` and structure maps that make `GJ` the jets of `G₀` rather than an
unrelated group. Fixing `jets` rather than `GJ` alone is what lets the global gauge action
`repConstant` below be taken along the *canonical* inclusion `jets.ofConstant`, instead of
an arbitrary homomorphism supplied by hand.

`MatterField jets` bundles this data. From it the general theory produces, on the bosonic
and fermionic algebras of the field, the jet gauge action, the global gauge action, the
Lorentz action and the mass-weight scaling — in
`Physlib.Particles.StandardModel.Matter.BosonicAlgebra` and
`Physlib.Particles.StandardModel.Matter.FermionicAlgebra`, downstream of the component
space this file's data indexes. A concrete theory therefore only has to supply a
`MatterField` for each of its fields.

## ii. Key results

- `MatterField` : the data of a matter field.
- `MatterField.PureJetsActTrivially`, `MatterField.GaugeLorentzCompatible` : two conditions
  on a matter field used by the covariant derivative theory.

## iii. Table of contents

- A. The data of a matter field
- B. Conditions on a matter field


-/

@[expose] public section

open Matrix MatrixGroups TensorProduct

/-!

## A. The data of a matter field

-/

/-- **A matter field** of a gauge theory over the gauge context `jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J`:
  a finite-dimensional complex target space `V`, the Lorentz representation on `V`, a
  fibrewise action of `GJ` on the jets `JetRing ⊗[ℂ] V` of the field, the infinitesimal
  action of the gauge algebra generating it, and the mass weight of the field (in the units
  in which a derivative has weight `2`). -/
structure MatterField {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
    (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J) where
  /-- The target space of the field. -/
  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module ℂ V]
  [instFree : Module.Free ℂ V]
  [instFinite : Module.Finite ℂ V]
  /-- The representation of the Lorentz group on the target space. -/
  repLorentz : Representation ℂ SL(2,ℂ) V
  /-- The action of the jets of gauge transformations on the jets of the field. -/
  repJet : Representation ℂ GJ (JetRing ⊗[ℂ] V)
  /-- The action of the gauge algebra. -/
  repAlgebra : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V
  /-- The gauge action is fibrewise: it commutes with multiplication by scalar jets. -/
  repJet_smul : ∀ (U : GJ) (χ : JetRing) (z : JetRing ⊗[ℂ] V), repJet U (χ • z) = χ • repJet U z
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

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} (M : MatterField jets)

/-!

## B. Conditions on a matter field

Two properties the data of a matter field does not in general imply: the transformation
laws constrain the base-point coefficient of a pure jet only to commute with the
infinitesimal action (a scalar twist by a character of the jet group nontrivial on pure
jets preserves every field of the structure), and they do not relate the gauge and Lorentz
actions at all. Both hold for the matter fields of the physical theories, and they are
recorded as conditions rather than as fields, to be assumed where the covariant derivative
theory needs them: the first for the factorization of the jet action through evaluation,
the second for the Lorentz law of the covariant derivatives.

-/

/-- Pure gauge jets act trivially at the base point: a jet with trivial value has identity
  zeroth Taylor coefficient on the value space. With the fibrewise law, the base-point
  value of the jet action is then a function of the value of the jet. -/
def PureJetsActTrivially : Prop :=
  ∀ {W : GJ}, jets.eval W = 1 → GaugeAlgebraRealization.repCoeff M.repJet W 0 = LinearMap.id

/-- The infinitesimal gauge action commutes with the Lorentz representation on the value
  space. -/
def GaugeLorentzCompatible : Prop :=
  ∀ (c : 𝔤) (Λ : SL(2,ℂ)) (v : M.V),
    M.repAlgebra c (M.repLorentz Λ v) = M.repLorentz Λ (M.repAlgebra c v)

end MatterField
