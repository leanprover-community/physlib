/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.JetAlgebra.Basic
public import Physlib.Particles.StandardModel.Matter.FermionicAlgebra.GaugeAction
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.GaugeAction
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.GaugeAction
public import Physlib.Particles.StandardModel.GaugeGroup.LocalGaugeData
public import Physlib.Particles.StandardModel.JetAlgebra.SectorEquiv.Structure
/-!
# The jet gauge action on the jet algebra of the Standard Model

## i. Overview

The jet gauge group acts on the jet algebra of the Standard Model factor by factor. On the
two matter factors it is the free-algebra functor applied to the species-wise action
`fieldData.repJetFermion`, `fieldData.repJetBoson` on the generator spaces; on the
connection factor it is the generic affine action `LocalGaugeFieldAlgebra.complexRepJet` of the
Standard Model's local gauge data, whose linear part is the all-orders Leibniz convolution
of the adjoint Taylor coefficients and whose constant part is the Maurer–Cartan shift. The
action is multiplicative — a jet of gauge transformations acts on a Lagrangian term factor
by factor — and restricts to each sector's own action through the sector inclusion.

## ii. Key results

- `JetAlgebra.repJetGaugeGroupI` : the jet gauge action.
- `JetAlgebra.repJetGaugeGroupI_apply_mul` : the action is multiplicative.
- `JetAlgebra.repJetGaugeGroupI_includeConnection`,
  `JetAlgebra.repJetGaugeGroupI_includeFermionFactor`,
  `JetAlgebra.repJetGaugeGroupI_includeBosonFactor` : the restriction to each of the three
  factors of the carrier.
- `JetAlgebra.repJetGaugeGroupI_includeGauge`,
  `JetAlgebra.repJetGaugeGroupI_includeFermion`,
  `JetAlgebra.repJetGaugeGroupI_includeHiggs` : the restriction to each of the three
  sectors, in the Standard Model presentation of them.

## iii. Table of contents

- A. The action of the jet gauge group
  - A.1. Multiplicativity
  - A.2. The action on the three factors
  - A.3. The action on the three sectors

-/

@[expose] public section

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

open TensorProduct Matrix MatrixGroups

namespace JetAlgebra

/-!

## A. The action of the jet gauge group

-/

/-- The jet gauge action on the fermionic factor: the exterior-algebra functor applied to
  the species-wise action on the fermionic generator space. -/
noncomputable abbrev repJetGaugeGroupIFermion :
    Representation ℂ JetGaugeGroupI (ExteriorAlgebra ℂ fieldData.FermionGenerators) :=
  fieldData.repJetFermion.exteriorAlgebra

/-- The jet gauge action on the bosonic factor: the symmetric-algebra functor applied to
  the species-wise action on the bosonic generator space. -/
noncomputable abbrev repJetGaugeGroupIBoson :
    Representation ℂ JetGaugeGroupI (SymmetricAlgebra ℂ fieldData.BosonGenerators) :=
  fieldData.repJetBoson.symmetricAlgebra

/-- The jet gauge action on the jet algebra of the Standard Model. Matter is acted on
  species by species from `fieldData`; the connection factor carries the generic affine
  `LocalGaugeFieldAlgebra.complexRepJet` action of the Standard Model local gauge data. -/
noncomputable def repJetGaugeGroupI : Representation ℂ JetGaugeGroupI JetAlgebra :=
  (repJetGaugeGroupIFermion.tprod repJetGaugeGroupIBoson).tprod
    (_root_.LocalGaugeFieldAlgebra.complexRepJet localGaugeData)

@[simp]
lemma repJetGaugeGroupI_tmul (U : JetGaugeGroupI)
    (w : ExteriorAlgebra ℂ fieldData.FermionGenerators ⊗[ℂ]
      SymmetricAlgebra ℂ fieldData.BosonGenerators)
    (g : ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra) :
    repJetGaugeGroupI U (w ⊗ₜ[ℂ] g)
      = ((repJetGaugeGroupIFermion.tprod repJetGaugeGroupIBoson) U w)
          ⊗ₜ[ℂ] (_root_.LocalGaugeFieldAlgebra.complexRepJet localGaugeData U g) := rfl

/-!

### A.1. Multiplicativity

-/

/-- The jet gauge action on the jet algebra is multiplicative: a jet of gauge
  transformations acts on a Lagrangian term factor by factor. -/
lemma repJetGaugeGroupI_apply_mul (U : JetGaugeGroupI) (x y : JetAlgebra) :
    repJetGaugeGroupI U (x * y) = repJetGaugeGroupI U x * repJetGaugeGroupI U y :=
  Representation.tprod_apply_mul _ _
    (Representation.tprod_apply_mul _ _
      (fun V a b => Representation.exteriorAlgebra_apply_mul _ V a b)
      (fun V a b => Representation.symmetricAlgebra_apply_mul _ V a b))
    (fun V a b => _root_.LocalGaugeFieldAlgebra.complexRepJet_apply_mul (jets := localGaugeData)
      V a b) U x y

/-!

### A.2. The action on the three factors

-/

/-- The jet gauge action on the complexified gauge sector fixes the unit. -/
lemma complexRepJetGaugeGroupI_apply_one (U : JetGaugeGroupI) :
    (_root_.LocalGaugeFieldAlgebra.complexRepJet localGaugeData) U
      (1 : ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra GaugeAlgebra)) = 1 := by
  rw [Algebra.TensorProduct.one_def, _root_.LocalGaugeFieldAlgebra.complexRepJet_tmul,
    _root_.LocalGaugeFieldAlgebra.repJet_apply_one]

/-- The matter factor of the jet gauge action fixes the unit. The proof instantiates the
  abstract `Representation.tprod_apply_one`, so that the unit of the matter factor is never
  unfolded: its two free algebras are quotients by congruences. -/
lemma repJetGaugeGroupI_matter_one (U : JetGaugeGroupI) :
    (repJetGaugeGroupIFermion.tprod repJetGaugeGroupIBoson) U
        (1 : fieldData.MatterAlgebra) = 1 :=
  Representation.tprod_apply_one _ _ U
    (Representation.exteriorAlgebra_apply_one _ U)
    (Representation.symmetricAlgebra_apply_one _ U)

/-- The jet gauge action restricts to the generic connection factor, where it is the
  generic affine action of the Standard Model local gauge data. -/
lemma repJetGaugeGroupI_includeConnection (U : JetGaugeGroupI)
    (y : ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra) :
    repJetGaugeGroupI U (fieldData.includeConnection y)
      = fieldData.includeConnection
          (_root_.LocalGaugeFieldAlgebra.complexRepJet localGaugeData U y) :=
  (congrArg (repJetGaugeGroupI U) (GaugeFieldData.includeConnection_apply y)).trans
    ((Representation.tprod_apply_one_tmul _ _ U (repJetGaugeGroupI_matter_one U) y).trans
      (GaugeFieldData.includeConnection_apply
        (_root_.LocalGaugeFieldAlgebra.complexRepJet localGaugeData U y)).symm)

/-- The jet gauge action restricts to the fermionic factor, where it is the
  exterior-algebra functor applied to the species-wise action of the datum. The factor
  inclusions are unfolded through the generic `GaugeFieldData` rules rather than by `rfl`:
  at the Standard Model datum the definitional unfolding of the units has to see through
  the unexposed ring congruence of the symmetric algebra. -/
lemma repJetGaugeGroupI_includeFermionFactor (U : JetGaugeGroupI)
    (a : ExteriorAlgebra ℂ fieldData.FermionGenerators) :
    repJetGaugeGroupI U (fieldData.includeFermion a)
      = fieldData.includeFermion (repJetGaugeGroupIFermion U a) :=
  (congrArg (repJetGaugeGroupI U) (GaugeFieldData.includeFermion_apply a)).trans
    ((Representation.tprod_apply_tmul_one _ _ U _
        (complexRepJetGaugeGroupI_apply_one U)).trans
      ((congrArg (fun w : fieldData.MatterAlgebra =>
            ((w ⊗ₜ[ℂ] (1 : ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra)) : JetAlgebra))
          (Representation.tprod_apply_tmul_one _ _ U a
            (Representation.symmetricAlgebra_apply_one _ U))).trans
        (GaugeFieldData.includeFermion_apply (repJetGaugeGroupIFermion U a)).symm))

/-- The jet gauge action restricts to the bosonic factor, where it is the
  symmetric-algebra functor applied to the species-wise action of the datum. -/
lemma repJetGaugeGroupI_includeBosonFactor (U : JetGaugeGroupI)
    (b : SymmetricAlgebra ℂ fieldData.BosonGenerators) :
    repJetGaugeGroupI U (fieldData.includeBoson b)
      = fieldData.includeBoson (repJetGaugeGroupIBoson U b) :=
  (congrArg (repJetGaugeGroupI U) (GaugeFieldData.includeBoson_apply b)).trans
    ((Representation.tprod_apply_tmul_one _ _ U _
        (complexRepJetGaugeGroupI_apply_one U)).trans
      ((congrArg (fun w : fieldData.MatterAlgebra =>
            ((w ⊗ₜ[ℂ] (1 : ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra)) : JetAlgebra))
          (Representation.tprod_apply_one_tmul _ _ U
            (Representation.exteriorAlgebra_apply_one _ U) b)).trans
        (GaugeFieldData.includeBoson_apply (repJetGaugeGroupIBoson U b)).symm))

/-!

### A.3. The action on the three sectors

The two matter sector inclusions factor through the sector equivalences, which intertwine
the two presentations of the jet gauge action by section C of
`Physlib.Particles.StandardModel.JetAlgebra.SectorEquiv.Structure`; so the action restricts
to each sector's own action under its existing name.

-/

/-- The jet gauge action restricts to the gauge sector's own action. The gauge sector
  inclusion is the connection inclusion of the datum, the Standard Model gauge bosons being
  the generic ones at `GaugeAlgebra`. -/
lemma repJetGaugeGroupI_includeGauge (U : JetGaugeGroupI)
    (y : ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra GaugeAlgebra)) :
    repJetGaugeGroupI U (includeGauge y)
      = includeGauge (_root_.LocalGaugeFieldAlgebra.complexRepJet localGaugeData U y) :=
  repJetGaugeGroupI_includeConnection U y

/-- The jet gauge action restricts to the fermionic sector's own action. -/
lemma repJetGaugeGroupI_includeFermion (U : JetGaugeGroupI) (f : FermionJetAlgebra) :
    repJetGaugeGroupI U (includeFermion f)
      = includeFermion (FermionJetAlgebra.repJetGaugeGroupI U f) :=
  (repJetGaugeGroupI_includeFermionFactor U (fermionAlgebraEquiv f)).trans
    (congrArg fieldData.includeFermion
      (fermionAlgebraEquiv_repJetGaugeGroupI U f).symm)

/-- The jet gauge action restricts to the Higgs sector's own action. -/
lemma repJetGaugeGroupI_includeHiggs (U : JetGaugeGroupI) (h : HiggsJetAlgebra) :
    repJetGaugeGroupI U (includeHiggs h)
      = includeHiggs (HiggsJetAlgebra.repJetGaugeGroupI U h) :=
  (repJetGaugeGroupI_includeBosonFactor U (higgsAlgebraEquiv h)).trans
    (congrArg fieldData.includeBoson (higgsAlgebraEquiv_repJetGaugeGroupI U h).symm)

end JetAlgebra

end StandardModel
