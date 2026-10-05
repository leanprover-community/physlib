/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Fermions.JetAlgebra.Basic
public import Physlib.Particles.StandardModel.HiggsBoson.JetAlgebra.Algebra
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.LocalGaugeData
public import Physlib.Mathematics.AlgebraRepresentation
public import Physlib.Particles.StandardModel.JetAlgebra.SectorEquiv.Basic
/-!
# The jet algebra of the Standard Model

## i. Overview

The full jet algebra of the Standard Model — the algebra in which a Standard Model
Lagrangian lives — is the local field algebra of its field datum,
`StandardModel.fieldData.LocalFieldAlgebra`: the exterior algebra on the fermionic
generators of the datum, tensored with the symmetric algebra on its bosonic generators,
tensored with the complexified symmetric algebra on the connection generators. The bosonic
factors commute with everything, so the ordinary tensor product is correct; the
anticommutativity of the fermions lives entirely inside the fermionic factor, where all
fifteen species share one exterior algebra.

The three sector inclusions keep their old names and their old sources — the sector
algebras `FermionJetAlgebra`, `HiggsJetAlgebra` and `LocalGaugeFieldAlgebra GaugeAlgebra` — so
that every downstream family of field symbols is unchanged. The two matter inclusions
factor through the sector equivalences of
`Physlib.Particles.StandardModel.JetAlgebra.SectorEquiv.Basic`; the connection sector needs
no equivalence, the two presentations of it being the same type.

This file defines the algebra and its three sector inclusions, and proves that the gauge
sector is central. The Lorentz action, the jet gauge action, the formal total derivative
and the mass-dimension scaling are assembled factorwise in the sibling files.

## ii. Key results

- `JetAlgebra` : the jet algebra of the Standard Model.
- `JetAlgebra.includeFermion`, `includeHiggs`, `includeGauge` : the sector inclusions.
- `JetAlgebra.includeGauge_commute` : the gauge sector is central.
- `JetAlgebra.includeFermion_ι`, `JetAlgebra.includeHiggs_ι`,
  `JetAlgebra.includeGauge_one_tmul_ι` : the included degree-one elements of the three
  sectors are the generic generators of the field datum.

## iii. Table of contents

- A. The jet algebra of the Standard Model
  - A.1. The sector inclusions
  - A.2. Centrality of the gauge sector

-/

@[expose] public section

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

open TensorProduct Matrix MatrixGroups

/-!

## A. The jet algebra of the Standard Model

-/

/-- The jet algebra of the Standard Model: the local field algebra of the Standard
  Model field datum. A Standard Model Lagrangian is an element of this algebra. -/
abbrev JetAlgebra : Type := fieldData.LocalFieldAlgebra

namespace JetAlgebra

/-!

### A.1. The sector inclusions

-/

/-- The inclusion of the fermionic sector. -/
noncomputable def includeFermion : FermionJetAlgebra →ₐ[ℂ] JetAlgebra :=
  fieldData.includeFermion.comp fermionAlgebraEquiv.toAlgHom

/-- The inclusion of the Higgs sector. -/
noncomputable def includeHiggs : HiggsJetAlgebra →ₐ[ℂ] JetAlgebra :=
  fieldData.includeBoson.comp higgsAlgebraEquiv.toAlgHom

/-- The inclusion of the gauge sector. The Standard Model gauge bosons are the generic
  ones at `GaugeAlgebra`, so this is the connection inclusion of the datum itself. -/
noncomputable def includeGauge :
    (ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra GaugeAlgebra)) →ₐ[ℂ] JetAlgebra :=
  fieldData.includeConnection

lemma includeGauge_apply (y : ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra GaugeAlgebra)) :
    includeGauge y = ((1 : fieldData.MatterAlgebra) ⊗ₜ[ℂ] y : JetAlgebra) :=
  GaugeFieldData.includeConnection_apply y

/-- The fermionic sector inclusion factors through the sector equivalence and the generic
  fermionic factor inclusion. -/
lemma includeFermion_apply_equiv (a : FermionJetAlgebra) :
    includeFermion a = fieldData.includeFermion (fermionAlgebraEquiv a) := rfl

/-- The Higgs sector inclusion factors through the sector equivalence and the generic
  bosonic factor inclusion. -/
lemma includeHiggs_apply_equiv (h : HiggsJetAlgebra) :
    includeHiggs h = fieldData.includeBoson (higgsAlgebraEquiv h) := rfl

/-- The gauge sector inclusion is the generic connection factor inclusion. -/
lemma includeGauge_eq_includeConnection :
    includeGauge = fieldData.includeConnection := rfl

/-- A degree-one element of the fermionic sector, included, is a total fermionic generator
  of the field datum, read through the fermionic generator identification. -/
lemma includeFermion_ι (v : JetComponentSpace fermionMatterField) :
    includeFermion (ExteriorAlgebra.ι ℂ v)
      = fieldData.ιFermionTotal (fermionGeneratorsEquiv.symm v) :=
  (includeFermion_apply_equiv (ExteriorAlgebra.ι ℂ v)).trans
    ((congrArg (fun a : ExteriorAlgebra ℂ fieldData.FermionGenerators =>
        fieldData.includeFermion a) (fermionAlgebraEquiv_ι v)).trans
      (StandardModel.includeFermion_ι (fermionGeneratorsEquiv.symm v)))

/-- A degree-one element of the Higgs sector, included, is the generator of the one bosonic
  species of the field datum. -/
lemma includeHiggs_ι (v : JetComponentSpace HiggsVec.matterField) :
    includeHiggs (SymmetricAlgebra.ι ℂ (JetComponentSpace HiggsVec.matterField) v)
      = fieldData.ιBoson () v :=
  (((includeHiggs_apply_equiv (SymmetricAlgebra.ι ℂ (JetComponentSpace HiggsVec.matterField) v)).trans
        (congrArg (fun b : SymmetricAlgebra ℂ fieldData.BosonGenerators =>
          fieldData.includeBoson b) (higgsAlgebraEquiv_ι v))).trans
      (StandardModel.includeBoson_ι (bosonGeneratorsEquiv.symm v))).trans
    ((congrArg (fun w : fieldData.BosonGenerators => fieldData.ιBosonTotal w)
        (bosonGeneratorsEquiv_symm_apply v)).trans (ιBosonTotal_inclBoson () v))

/-- A real degree-one element of the gauge sector, included, is a connection generator of
  the field datum: the connection factors of the two presentations are the same type, and
  the complexification is the scalar one. -/
lemma includeGauge_one_tmul_ι (v : GaugeBoson.JetComponentSpace GaugeAlgebra) :
    includeGauge ((1 : ℂ) ⊗ₜ[ℝ]
        SymmetricAlgebra.ι ℝ (GaugeBoson.JetComponentSpace GaugeAlgebra) v)
      = fieldData.ιConnection v :=
  StandardModel.includeConnection_one_tmul_ι v

/-!

### A.2. Centrality of the gauge sector

-/

/-- The right factor of a tensor product with a commutative right factor is central:
  the abstract statement, proved by tensor induction at abstract types so that it can be
  instantiated on the jet algebra without rewriting inside it. -/
private lemma tensor_includeRight_comm {A B : Type*} [Ring A] [Algebra ℂ A]
    [CommRing B] [Algebra ℂ B] (y : B) (x : A ⊗[ℂ] B) :
    x * Algebra.TensorProduct.includeRight (R := ℂ) (A := A) y
      = Algebra.TensorProduct.includeRight (R := ℂ) (A := A) y * x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, mul_zero]
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]
  | tmul w g =>
    rw [show (Algebra.TensorProduct.includeRight (R := ℂ) (A := A) y : A ⊗[ℂ] B)
        = (1 : A) ⊗ₜ[ℂ] y from rfl,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul, mul_comm g y]

/-- The image of the gauge sector is central: gauge-boson symbols commute with
  everything, as bosons must. -/
lemma includeGauge_commute (y : ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra GaugeAlgebra)) (x : JetAlgebra) :
    x * includeGauge y = includeGauge y * x :=
  tensor_includeRight_comm y x

end JetAlgebra

end StandardModel
