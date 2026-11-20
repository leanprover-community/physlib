/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.ScalarSector.DerivSubmodule.Centre
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.YukawaSector.Basic
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.FermionSector.Deriv.Centre
public import PhyslibAlpha.Relativity.Tensors.ComplexTensor.Vector.ContractionTensor
/-!
# The Yukawa invariants below mass weight eight

No gauge- and Lorentz-invariant Yukawa term of the covariant field algebra sits below weight eight.

## i. Overview

Everything below is stated about the covariant field algebra `fieldData.LocalCovFieldAlgebra` of the
Standard Model.

Mass weight eight is the first weight at which the Yukawa sector can carry an invariant.
It is the weight of `H ψ ψ`, one Higgs against two fermions. Below it the sector is nearly
empty — it vanishes outright below weight five and again at weight six — and the little
that survives, at weights five and seven, is barred from carrying an invariant by a parity
count.

The count is on spin, not on the number of covector indices as in the gauge sector. The
Higgs is a Lorentz scalar and a fermion carries one Weyl-spinor index, so each of the four
products surviving at weights five and seven, having exactly one fermion factor, is of
half-integer spin, and a half-integer spin carries no Lorentz invariant.

The count is run at the centre of `SL(2,ℂ)`, where `Invariants/CentreEigenspace.lean` puts it. The
element `-1` covers the identity Lorentz transformation, so it acts by `+1` on the Higgs
derivative submodules and by `-1` on the fermion ones, and the Lorentz action on the
covariant field algebra of the Standard Model is by algebra maps, so the signs multiply over a
product. Section A does that multiplication for
the four products, and the peeling modulo a Lorentz-stable submodule `S` is
`mem_of_invariant_of_mem_sup_centreEigenspace_neg_one`.

Unlike the gauge-sector statement, the final statement needs no `0 < w`. The Yukawa sector
is a product of two non-empty sectors, so it already vanishes at weight zero and the
scalars never enter.

## ii. Key results

- `mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_five_sup`,
  `mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_seven_sup` : mass weights five and seven
  carry no Lorentz invariant, being of half-integer spin.
- `mem_sectorMassWeight_higgs_fermion_lt_eight_sup_and_gauge_lorentz_invariant_iff` : the
  classification below mass weight eight as an equivalence.

## iii. Table of contents

- A. Integer Higgs against half-integer fermion
- B. Mass weights five and seven
- C. The classification below mass weight eight

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open GaugeFieldData (FieldKind)

open TensorProduct Matrix MatrixGroups Lorentz Lorentz.Invariants

namespace LocalCovFieldAlgebra

/-!

## A. Integer Higgs against half-integer fermion

The signs the two factors carry at the centre are already proved: the Higgs derivative
submodules carry `+1`, being Lorentz scalars with inert derivative slots, and the fermion
ones carry `-1`, the Weyl-spinor value index doing the work. The Lorentz action on the
covariant field algebra is by algebra maps, so the sign of a product is the product of the
signs, and each of the products surviving below weight eight has exactly one fermion
factor. The term with two
Higgs factors multiplies twice, `+1` against `+1` staying `+1` before the fermion turns the
total `-1`.

-/

/-- A Higgs derivative submodule against a fermion one is of half-integer spin, `+1` times
  `-1`. -/
private lemma higgsFermion_le_centreEigenspace (a b : ℕ) :
    ScalarSector.derivSubmodule a * FermionSector.derivSubmodule b
      ≤ centreEigenspace repLorentzGroup (-1) := by
  simpa using mul_le_centreEigenspace repLorentzGroup_mul
    (ScalarSector.derivSubmodule_le_centreEigenspace a)
    (FermionSector.derivSubmodule_le_centreEigenspace b)

/-- Two Higgs derivative submodules against a fermion one is of half-integer spin, `+1`
  times `+1` times `-1`. -/
private lemma higgsSqFermion_le_centreEigenspace (a b c : ℕ) :
    ScalarSector.derivSubmodule a * ScalarSector.derivSubmodule b
        * FermionSector.derivSubmodule c
      ≤ centreEigenspace repLorentzGroup (-1) := by
  simpa using mul_le_centreEigenspace repLorentzGroup_mul
    (mul_le_centreEigenspace repLorentzGroup_mul
      (ScalarSector.derivSubmodule_le_centreEigenspace a)
      (ScalarSector.derivSubmodule_le_centreEigenspace b))
    (FermionSector.derivSubmodule_le_centreEigenspace c)

/-!

## B. Mass weights five and seven

Weight five is a single product, the Higgs field against the underived fermion towers.
Weight seven is a join of three: the Higgs field against the once-derived towers, the
once-derived Higgs field against the underived ones, and two Higgs fields against the
underived ones. Each of the four has exactly one fermion factor, so section A gives all of
them the sign `-1`, the join included, and the invariant is left in `S`.

-/

/-- Mass weight five carries no Lorentz invariant modulo a Lorentz-stable submodule. A
  Lorentz invariant of `fieldData.sectorMassWeight {scalar, fermion} 5 ⊔ S` lies in `S`. The
  weight is one Higgs field against the underived fermion towers, of half-integer spin. -/
lemma mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_five_sup
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} 5
      ⊔ S)
    (hL : ∀ g : SL(2,ℂ), repLorentzGroup g x = x) : x ∈ S := by
  rw [LocalCovFieldAlgebra.sectorMassWeight_higgs_fermion_five] at hx
  exact mem_of_invariant_of_mem_sup_centreEigenspace_neg_one
    (LocalCovFieldAlgebra.higgsFermion_le_centreEigenspace 0 0) S hSL hx hL

/-- Mass weight seven carries no Lorentz invariant modulo a Lorentz-stable submodule. A
  Lorentz invariant of `fieldData.sectorMassWeight {scalar, fermion} 7 ⊔ S` lies in `S`. Each of the
  three products making up the weight has a single fermion factor, so each is of
  half-integer spin and so is their join. -/
lemma mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_seven_sup
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y
      ∈ S) {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} 7
      ⊔ S)
    (hL : ∀ g : SL(2,ℂ), repLorentzGroup g x = x) : x ∈ S := by
  rw [LocalCovFieldAlgebra.sectorMassWeight_higgs_fermion_seven] at hx
  exact mem_of_invariant_of_mem_sup_centreEigenspace_neg_one
    (sup_le (sup_le (LocalCovFieldAlgebra.higgsFermion_le_centreEigenspace 0 1)
      (LocalCovFieldAlgebra.higgsFermion_le_centreEigenspace 1 0))
      (LocalCovFieldAlgebra.higgsSqFermion_le_centreEigenspace 0 0 0)) S hSL hx hL

/-!

## C. The classification below mass weight eight

The eight weights below eight are now settled: the sector vanishes below weight five and
at weight six, and weights five and seven are section B. So below weight eight the Yukawa
sector supplies no invariant beyond what `S` already carries, and the equivalences record
it.

No lower bound on the weight is needed, unlike the gauge-sector statement. The Yukawa
sector is the two-class sector of the Higgs and fermion generators, so both classes must
be present with a non-zero weight and the sector is already trivial at weight zero; the
scalars, which are what force `0 < w` there, never appear.

-/

/-- Below mass weight eight the Yukawa sector carries no Lorentz invariant. A Lorentz
  invariant of `fieldData.sectorMassWeight {scalar, fermion} w ⊔ S` for `w < 8` lies in `S`. Weights
  below five and weight six are trivial submodules, and weights five and seven are section
  B. -/
lemma mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_lt_eight_sup (w : ℕ)
    (hw : w < 8) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} w
      ⊔ S)
    (hL : ∀ g : SL(2,ℂ), repLorentzGroup g x = x) : x ∈ S := by
  rcases lt_or_ge w 5 with hw5 | hw5
  · rwa [LocalCovFieldAlgebra.sectorMassWeight_higgs_fermion_eq_bot_of_lt_five hw5, bot_sup_eq] at
      hx
  interval_cases w
  · exact LocalCovFieldAlgebra.mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_five_sup S
      hSL hx hL
  · rwa [LocalCovFieldAlgebra.sectorMassWeight_higgs_fermion_six, bot_sup_eq] at hx
  · exact LocalCovFieldAlgebra.mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_seven_sup S
      hSL hx hL

/-- The classification below mass weight eight as an equivalence, in the shape of the
  gauge-sector statement `mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff`.
  An element of `fieldData.sectorMassWeight {scalar, fermion} w ⊔ S` for `w < 8` is fixed by both
  groups exactly when it is itself an element of `S` fixed by both groups. Gauge stability
  of `S` is not needed, and neither is gauge invariance of `x`. The forward direction is
  the spin parity argument, which uses the Lorentz group alone. -/
lemma mem_sectorMassWeight_higgs_fermion_lt_eight_sup_and_gauge_lorentz_invariant_iff
    (w : ℕ) (hw : w < 8) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} w ⊔ S
        ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x) ∧ ∀ g : SL(2,ℂ),
          repLorentzGroup g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGaugeGroupI g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentzGroup g y = y)
          ∧ x = y := by
  constructor
  · rintro ⟨hx, hG, hL⟩
    exact ⟨x,
      LocalCovFieldAlgebra.mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_lt_eight_sup w hw
      S
      hSL hx hL, hG, hL, rfl⟩
  · rintro ⟨y, hyS, hyG, hyL, rfl⟩
    exact ⟨Submodule.mem_sup_right hyS, hyG, hyL⟩

/-- The same classification without the existential. Below mass weight eight an element of
  `fieldData.sectorMassWeight {scalar, fermion} w ⊔ S` fixed by both groups is an element of
  `S` fixed by both groups, and conversely. -/
lemma mem_sectorMassWeight_higgs_fermion_lt_eight_sup_and_gauge_lorentz_invariant_iff_mem
    (w : ℕ) (hw : w < 8) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} w ⊔ S
        ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x) ∧ ∀ g : SL(2,ℂ),
          repLorentzGroup g x = x)
      ↔ (x ∈ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x) :=
  ⟨fun hx =>
    ⟨LocalCovFieldAlgebra.mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_lt_eight_sup w hw
    S
    hSL hx.1 hx.2.2, hx.2⟩, fun hx => ⟨Submodule.mem_sup_right hx.1, hx.2⟩⟩

end LocalCovFieldAlgebra

end StandardModel
