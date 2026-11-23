/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.CovariantDeriv
public import PhyslibAlpha.Mathematics.AlgebraRepresentation
/-!
# Realizations of the local field algebra

Equivariant algebra maps out of the local field algebra of a gauge theory.

## i. Overview

A complex algebra `B` carries the fields of a gauge-field datum when the local field
algebra `J(T)` maps into it by a complex algebra map equivariant for the jet gauge group
and the Lorentz group, both acting on `B` by algebra endomorphisms. Such a map is a
`GaugeFieldData.Realization`. The gauge-field symbols of a realization are those of the
gauge-boson jet algebra carried along the composite of the inclusion of the connection factor
with the map, `mapGaugeField (h.toAlgHom.comp T.includeConnection)`. They transform as a gauge
field, so the gauge-boson symbol theory applies to them, and the realized field-strength tower
is identified with their covariant tower.

## ii. Key results

- `GaugeFieldData.Realization` : an algebra carrying the fields of a datum.
- `GaugeFieldData.Realization.id` : the local field algebra realized in itself.
- `GaugeFieldData.Realization.transformsAsGaugeField_mapGaugeField` : the gauge-field symbols
  of a realization transform as a gauge field.
- `GaugeFieldData.Realization.toAlgHom_covDerivFieldStrength` : the realized field-strength
  tower is the covariant tower of the realized symbols.

## iii. Table of contents

- A. Realizations
- B. The gauge bosons of a realization

## iv. References

* None.

-/

@[expose] public section

set_option linter.unusedSectionVars false

open TensorProduct Matrix MatrixGroups Lorentz
open LocalGaugeFieldAlgebra (mapGaugeField)
open GaugeBoson (fieldStrength iteratedCovDerivAdjoint)

namespace GaugeFieldData

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ} {T : GaugeFieldData G}

/-!

## A. Realizations

-/

/-- A complex algebra `B` carrying the fields of the datum `T`, through a complex algebra map out
  of the local field algebra, equivariant for the jet gauge group and the Lorentz group,
  both acting on the whole of `B` by algebra endomorphisms. No commutativity, injectivity
  or surjectivity is assumed, and no derivative operator on `B` is involved. It is built
  from the fields `toAlgHom`, `map_fst`, `map_snd`, `fst_mul`, `snd_mul` of
  `Representation.EquivariantAlgHom`, which the lemmas `map_repJet`, `map_repLorentz`,
  `repJet_mul` and `repLorentz_mul` name. -/
abbrev Realization (T : GaugeFieldData G) (B : Type) [Ring B] [Algebra ℂ B]
    (repJet : Representation ℂ G.gaugeJetGroup B) (repLorentz : Representation ℂ SL(2,ℂ) B) :=
  Representation.EquivariantAlgHom (A := T.LocalFieldAlgebra) T.repJet repJet
    T.repLorentzGroup repLorentz

namespace Realization

variable {B : Type} [Ring B] [Algebra ℂ B] {repJet : Representation ℂ G.gaugeJetGroup B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}

variable (T) in
/-- The local field algebra realized in itself, by the identity. -/
noncomputable def id : Realization T T.LocalFieldAlgebra T.repJet T.repLorentzGroup :=
  Representation.EquivariantAlgHom.id _ _ GaugeFieldData.repJet_apply_mul
    GaugeFieldData.repLorentzGroup_apply_mul

variable (h : Realization T B repJet repLorentz)

/-- The map is equivariant for the jet gauge group. -/
lemma map_repJet (U : G.gaugeJetGroup) (x : T.LocalFieldAlgebra) :
    h.toAlgHom (T.repJet U x) = repJet U (h.toAlgHom x) :=
  h.map_fst U x

/-- The map is equivariant for the Lorentz group. -/
lemma map_repLorentz (Λ : SL(2,ℂ)) (x : T.LocalFieldAlgebra) :
    h.toAlgHom (T.repLorentzGroup Λ x) = repLorentz Λ (h.toAlgHom x) :=
  h.map_snd Λ x

include h in
/-- The jet gauge group acts on the whole of `B` by algebra endomorphisms. -/
lemma repJet_mul (U : G.gaugeJetGroup) (b₁ b₂ : B) :
    repJet U (b₁ * b₂) = repJet U b₁ * repJet U b₂ :=
  h.fst_mul U b₁ b₂

include h in
/-- The Lorentz group acts on the whole of `B` by algebra endomorphisms. -/
lemma repLorentz_mul (Λ : SL(2,ℂ)) (b₁ b₂ : B) :
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂ :=
  h.snd_mul Λ b₁ b₂

/-!

## B. The gauge bosons of a realization

-/

/-- The gauge-field symbols of a realization, those of `J(T)` carried along the map, transform
  as a gauge field. -/
lemma transformsAsGaugeField_mapGaugeField :
    GaugeBoson.TransformsAsGaugeField G repJet
      (mapGaugeField (h.toAlgHom.comp T.includeConnection)) :=
  LocalGaugeFieldAlgebra.transformsAsGaugeField_mapGaugeField _ fun U x => by
    rw [AlgHom.comp_apply, ← repJet_includeConnection, h.map_repJet, AlgHom.comp_apply]

/-- The map of a realization carries the included field-strength tower to the covariant
  tower of the realized gauge-field symbols. -/
lemma toAlgHom_covDerivFieldStrength (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ G.lieSubalgebra) :
    h.toAlgHom (T.covDerivFieldStrength l μ ν φ)
      = iteratedCovDerivAdjoint (mapGaugeField (h.toAlgHom.comp T.includeConnection)) l
        (fieldStrength (mapGaugeField (h.toAlgHom.comp T.includeConnection)) μ ν) 0 φ := by
  rw [covDerivFieldStrength_eq_iteratedCovDerivAdjoint]
  exact (GaugeBoson.iteratedCovDerivAdjoint_fieldStrength_map
    (B := T.LocalFieldAlgebra) (B' := B) (h.toAlgHom.toLinearMap.restrictScalars ℝ)
    (map_mul h.toAlgHom) T.gaugeField l μ ν φ).symm

end Realization

end GaugeFieldData
