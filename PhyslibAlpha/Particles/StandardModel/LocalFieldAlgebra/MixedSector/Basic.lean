/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.LocalCovFieldAlgebra.Sectors
/-!
# The mixed sector

The gauge-Higgs-fermion sector of the Standard Model's covariant field algebra, at low weight.

## i. Overview

Everything below is stated about the covariant field algebra `fieldData.LocalCovFieldAlgebra` of the
Standard Model.

The sector `fieldData.sectorMassWeight {gauge, scalar, fermion} w` of the generic
`GaugeFieldData.sectorMassWeight` is the home of any term that mixes all three kinds of
covariant field at once. A field-strength tower carries weight at least `4`, a Higgs (or
conjugate Higgs) tower weight at least `2`, and a fermion tower weight at least `3`, so a
product of generators of all three kinds has total weight at least `4 + 2 + 3 = 9`, by
`GaugeFieldData.sectorMassWeight_eq_bot_of_lt`.

Consequently the mixed sector vanishes identically below weight nine
(`sectorMassWeight_mixed_eq_bot_of_lt_nine`), in particular at every weight up to
eight. There is no Standard-Model term of mass dimension at most four (mass
weight, twice the mass dimension, at most eight) that mixes gauge, Higgs and fermion
fields together.

Below weight nine, then, there is nothing left to classify. The sector is `⊥`, so an
element of `⊥ ⊔ S` is an element of `S` outright, whatever `S` may be. Section B records
that in the shape the other sectors carry, so that the four can later be combined; unlike
them it asks no stability of `S` and no invariance of the element, there being nothing to
peel away and no parity or index count to run.

## ii. Key results

- `minKindWeight` : the minimum mass weight of a generator of each kind.
- `sectorMassWeight_mixed_eq_bot_of_lt_nine` : the mixed sector vanishes below weight nine.
- `mem_sectorMassWeight_mixed_lt_nine_sup_and_gauge_lorentz_invariant_iff` : the classification
  below mass weight nine as an equivalence.

## iii. Table of contents

- A. The mixed sector vanishes below weight nine
- B. The classification below weight nine

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open GaugeFieldData (FieldKind)

open TensorProduct Matrix MatrixGroups Lorentz


namespace LocalCovFieldAlgebra

/-!

## A. The mixed sector vanishes below weight nine

-/

/-- The minimum mass weight of a covariant generator of each kind in the Standard Model, four
  for the field strength, two for the Higgs and three for the fermions. -/
def minKindWeight : FieldKind → ℕ
  | .gauge => 4
  | .scalar => 2
  | .fermion => 3

/-- Every covariant generator of the Standard Model has at least the minimum mass weight of its
  kind. -/
lemma minKindWeight_le {k : FieldKind} {v : ℕ} {b : fieldData.LocalCovFieldAlgebra}
    (hb : b ∈ fieldData.weightedGenerators k v) : minKindWeight k ≤ v := by
  cases k with
  | gauge => exact GaugeFieldData.four_le_of_mem_weightedGenerators_gauge hb
  | scalar =>
    exact GaugeFieldData.le_of_mem_weightedGenerators_scalar
      (fun j => (fieldData_boson_massWeight j).ge) hb
  | fermion =>
    exact GaugeFieldData.le_of_mem_weightedGenerators_fermion
      (fun i => (fieldData_fermion_massWeight i).ge) hb

/-- The mixed sector vanishes below weight nine, since a product of generators of all three kinds
  carries gauge weight at least four, Higgs weight at least two and fermion weight at least
  three, for a total of at least nine. So no such product exists at a lower weight, and the
  sector's span there is trivial. -/
lemma sectorMassWeight_mixed_eq_bot_of_lt_nine {w : ℕ} (hw : w < 9) :
    fieldData.sectorMassWeight
      {FieldKind.gauge, FieldKind.scalar, FieldKind.fermion} w = ⊥ := by
  have h9 : ∑ k ∈ ({FieldKind.gauge, FieldKind.scalar, FieldKind.fermion} : Finset FieldKind),
      minKindWeight k = 9 := by decide
  exact GaugeFieldData.sectorMassWeight_eq_bot_of_lt (m := minKindWeight)
    (fun _ _ _ _ hb => minKindWeight_le hb) (lt_of_lt_of_eq hw h9.symm)

/-!

## B. The classification below weight nine

Nine is beyond every weight a dimension-four term can reach, so the vanishing of section A settles
the whole of the mixed sector at a stroke. An element of `⊥ ⊔ S` is an element of `S`. The three
statements below are those of the gauge and Yukawa sectors, name for name, so that the four sectors
can be combined uniformly. There the forward direction is an argument — a metric trace, an index
count, the sign at the centre of `SL(2,ℂ)` — and needs `S` stable and the element invariant; here it
is the emptiness of the sector, and the invariance conjuncts ride along in the equivalences only to
keep the shapes matched.

-/

/-- Below mass weight nine the mixed sector adds nothing to a submodule `S`. An element of
  `fieldData.sectorMassWeight {gauge, scalar, fermion} w ⊔ S` for `w < 9` already lies in `S`. The
  sector is trivial there, so no invariance is asked of `x` and no stability of `S`. -/
lemma mem_of_invariant_sectorMassWeight_mixed_lt_nine_sup (w : ℕ) (hw : w < 9)
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra) {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.scalar,
      FieldKind.fermion} w ⊔ S) : x ∈ S := by
  rwa [LocalCovFieldAlgebra.sectorMassWeight_mixed_eq_bot_of_lt_nine hw, bot_sup_eq] at hx

/-- The classification below mass weight nine as an equivalence, in the shape of the
  gauge- and Yukawa-sector statements. An element of
  `fieldData.sectorMassWeight {gauge, scalar, fermion} w ⊔ S` for `w < 9` is fixed by both groups
  exactly when it is itself an element of `S` fixed by both groups. Neither stability
  hypothesis on `S` is needed, the forward direction being the vanishing of the sector. -/
lemma mem_sectorMassWeight_mixed_lt_nine_sup_and_gauge_lorentz_invariant_iff (w : ℕ)
    (hw : w < 9) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.scalar,
          FieldKind.fermion} w ⊔ S
        ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x) ∧ ∀ g : SL(2,ℂ),
          repLorentzGroup g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGaugeGroupI g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentzGroup g y = y)
          ∧ x = y := by
  constructor
  · rintro ⟨hx, hG, hL⟩
    exact ⟨x, LocalCovFieldAlgebra.mem_of_invariant_sectorMassWeight_mixed_lt_nine_sup w hw S hx,
      hG, hL, rfl⟩
  · rintro ⟨y, hyS, hyG, hyL, rfl⟩
    exact ⟨Submodule.mem_sup_right hyS, hyG, hyL⟩

/-- The same classification without the existential. Below mass weight nine an element of
  `fieldData.sectorMassWeight {gauge, scalar, fermion} w ⊔ S` fixed by both groups is an element of
  `S` fixed by both groups, and conversely. -/
lemma mem_sectorMassWeight_mixed_lt_nine_sup_and_gauge_lorentz_invariant_iff_mem (w : ℕ)
    (hw : w < 9) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.scalar,
          FieldKind.fermion} w ⊔ S
        ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x) ∧ ∀ g : SL(2,ℂ),
          repLorentzGroup g x = x)
      ↔ (x ∈ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x) :=
  ⟨fun hx => ⟨LocalCovFieldAlgebra.mem_of_invariant_sectorMassWeight_mixed_lt_nine_sup w hw S hx.1,
    hx.2⟩,
    fun hx => ⟨Submodule.mem_sup_right hx.1, hx.2⟩⟩

end LocalCovFieldAlgebra

end StandardModel
