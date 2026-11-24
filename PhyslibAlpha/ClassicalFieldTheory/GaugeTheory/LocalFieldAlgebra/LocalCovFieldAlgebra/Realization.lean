/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.LocalCovFieldAlgebra.Basic
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Realization
/-!
# Realizations of the covariant field algebra

Equivariant algebra maps out of the covariant field algebra of a gauge theory.

## i. Overview

A complex algebra `B` carries the covariant expressions of a gauge-field datum when the
covariant field algebra maps into it by a complex algebra map equivariant for the ordinary
gauge group `G.group` and for the Lorentz group, both acting on `B` by algebra endomorphisms.
Such a map is a `GaugeFieldData.LocalCovFieldAlgebra.Realization`. The gauge compatibility is
with `G.group` alone because the source action of the ordinary gauge group is the jet action at
the constant jets. The Lorentz action of the source exists only under
`GaugeFieldData.GaugeLorentzCompatible`, which is therefore a parameter.

A realization of the local field algebra restricts to one of the covariant field algebra
(`GaugeFieldData.Realization.restrict`), with `G.group` acting on the target through the
constant jets. The converse extension is not claimed.

## ii. Key results

- `GaugeFieldData.LocalCovFieldAlgebra.Realization` : an algebra carrying the covariant
  field algebra, with the equivariance laws `map_repValue` and `map_repLorentz`.
- `GaugeFieldData.Realization.restrict` : restriction to the covariant field algebra.

## iii. Table of contents

- A. Realizations
- B. Restriction from the local field algebra

## iv. References

* None.

-/

@[expose] public section

set_option linter.unusedSectionVars false

open TensorProduct Matrix MatrixGroups Lorentz

namespace GaugeFieldData

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ} {T : GaugeFieldData G}

namespace LocalCovFieldAlgebra

/-!

## A. Realizations

-/

/-- A complex algebra `B` carrying the covariant expressions of the datum `T`, through a complex
  algebra map out of the covariant field algebra, equivariant for the ordinary gauge group
  and the Lorentz group, both acting on the whole of `B` by algebra endomorphisms. The
  Lorentz action of the source needs `GaugeFieldData.GaugeLorentzCompatible`, which is a
  parameter. No other species condition is used. It is built from the fields `toAlgHom`,
  `map_fst`, `map_snd`, `fst_mul`, `snd_mul` of `Representation.EquivariantAlgHom`, which
  the lemmas `map_repValue`, `map_repLorentz`, `repGauge_mul` and `repLorentz_mul` name. -/
abbrev Realization (T : GaugeFieldData G) (hGL : T.GaugeLorentzCompatible) (B : Type)
    [Semiring B] [Algebra ℂ B] (repGauge : Representation ℂ G.group B)
    (repLorentz : Representation ℂ SL(2,ℂ) B) :=
  Representation.EquivariantAlgHom (repValue T) repGauge (repLorentzGroup T hGL) repLorentz

namespace Realization

variable {B : Type} [Semiring B] [Algebra ℂ B] {repGauge : Representation ℂ G.group B}
  {repLorentz : Representation ℂ SL(2,ℂ) B} {hGL : T.GaugeLorentzCompatible}

variable (k : Realization T hGL B repGauge repLorentz)

/-- The map is equivariant for the ordinary gauge group. -/
lemma map_repValue (g : G.group) (x : ↥T.LocalCovFieldAlgebra) :
    k.toAlgHom (repValue T g x) = repGauge g (k.toAlgHom x) :=
  k.map_fst g x

/-- The map is equivariant for the Lorentz group. -/
lemma map_repLorentz (Λ : SL(2,ℂ)) (x : ↥T.LocalCovFieldAlgebra) :
    k.toAlgHom (repLorentzGroup T hGL Λ x) = repLorentz Λ (k.toAlgHom x) :=
  k.map_snd Λ x

include k in
/-- The ordinary gauge group acts on the whole of `B` by algebra endomorphisms. -/
lemma repGauge_mul (g : G.group) (b₁ b₂ : B) :
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂ :=
  k.fst_mul g b₁ b₂

include k in
/-- The Lorentz group acts on the whole of `B` by algebra endomorphisms. -/
lemma repLorentz_mul (Λ : SL(2,ℂ)) (b₁ b₂ : B) :
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂ :=
  k.snd_mul Λ b₁ b₂

end Realization

end LocalCovFieldAlgebra

/-!

## B. Restriction from the local field algebra

-/

namespace Realization

variable {B : Type} [Ring B] [Algebra ℂ B] {repJet : Representation ℂ G.gaugeJetGroup B}
  {repLorentz : Representation ℂ SL(2,ℂ) B} (h : Realization T B repJet repLorentz)
  (hGL : T.GaugeLorentzCompatible)

/-- The restriction of a realization of the local field algebra to the covariant field
  algebra, along the inclusion; the ordinary gauge group acts on the target through the
  constant jets. No species condition beyond `hGL` is used. -/
noncomputable def restrict :
    LocalCovFieldAlgebra.Realization T hGL B (repJet.comp G.gaugeJetOfConstant) repLorentz :=
  (h.restrictSubalgebra T.LocalCovFieldAlgebra
    (fun U _ hx => LocalCovFieldAlgebra.repJet_mem U hx)
    (fun Λ _ hx => LocalCovFieldAlgebra.repLorentzGroup_mem hGL Λ hx)).compFst
      G.gaugeJetOfConstant

@[simp]
lemma restrict_toAlgHom_apply (x : ↥T.LocalCovFieldAlgebra) :
    (h.restrict hGL).toAlgHom x = h.toAlgHom x := rfl

end Realization

end GaugeFieldData
