/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.AlgebraRealization.HiggsAlgebraCovRealization.DerivSubmodule.Centre
public import Physlib.Particles.StandardModel.CovAlgebraRealization.YukawaSector.Basic
public import Physlib.Particles.StandardModel.IsFermionSector.DerivSubmodule.Centre
public import Physlib.Relativity.LorentzGroup.Invariants.RankFour
/-!
# The Yukawa invariants below mass weight eight

Mass weight eight is the first weight at which the Yukawa sector can carry an invariant:
it is the weight of `H ψ ψ`, one Higgs against two fermions. Below it the sector is nearly
empty — it vanishes outright below weight five and again at weight six — and the little
that survives, at weights five and seven, is barred from carrying an invariant by a parity
count.

The count is on spin, not on the number of covector indices as in the gauge sector. The
Higgs is a Lorentz scalar and a fermion carries one Weyl-spinor index, so each of the four
products surviving at weights five and seven, having exactly one fermion factor, is of
half-integer spin; and a half-integer spin carries no Lorentz invariant.

The count is run at the centre of `SL(2,ℂ)`, where `Invariants/Centre.lean` puts it: the
element `-1` covers the identity Lorentz transformation, so it acts by `+1` on the Higgs
derivative submodules and by `-1` on the fermion ones, and the Lorentz action on `B` is by
algebra maps, so the signs multiply over a product. Section A does that multiplication for
the four products, and the peeling modulo a Lorentz-stable submodule `S` is
`mem_of_invariant_of_mem_sup_centreEigenspace_neg_one`.

- A. Integer Higgs against half-integer fermion
- B. Mass weights five and seven
- C. The classification below mass weight eight

Unlike the gauge-sector statement, the final theorem needs no `0 < w`: the Yukawa sector
is a product of two non-empty sectors, so it already vanishes at weight zero and the
scalars never enter.

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz Lorentz.Invariants

namespace CovAlgebraRealization

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : CovAlgebraRealization B repGauge repLorentz massWeightPoly)

/-!

## A. Integer Higgs against half-integer fermion

The signs the two factors carry at the centre are already proved: the Higgs derivative
submodules carry `+1`, being Lorentz scalars with inert derivative slots, and the fermion
ones carry `-1`, the Weyl-spinor value index doing the work. The Lorentz action on `B` is
by algebra maps, so the sign of a product is the product of the signs, and each of the
products surviving below weight eight has exactly one fermion factor. The term with two
Higgs factors multiplies twice, `+1` against `+1` staying `+1` before the fermion turns the
total `-1`.

-/

/-- A Higgs derivative submodule against a fermion one is of half-integer spin: `+1` times
  `-1`. -/
private lemma higgsFermion_le_centreEigenspace (a b : ℕ) :
    h.isHiggsSector.derivSubmodule a * h.isFermionSector.derivSubmodule b
      ≤ centreEigenspace repLorentz (-1) := by
  simpa using mul_le_centreEigenspace h.repLorentz_mul
    (h.isHiggsSector.derivSubmodule_le_centreEigenspace a)
    (h.isFermionSector.derivSubmodule_le_centreEigenspace b)

/-- Two Higgs derivative submodules against a fermion one is of half-integer spin: `+1`
  times `+1` times `-1`. -/
private lemma higgsSqFermion_le_centreEigenspace (a b c : ℕ) :
    h.isHiggsSector.derivSubmodule a * h.isHiggsSector.derivSubmodule b
        * h.isFermionSector.derivSubmodule c
      ≤ centreEigenspace repLorentz (-1) := by
  simpa using mul_le_centreEigenspace h.repLorentz_mul
    (mul_le_centreEigenspace h.repLorentz_mul
      (h.isHiggsSector.derivSubmodule_le_centreEigenspace a)
      (h.isHiggsSector.derivSubmodule_le_centreEigenspace b))
    (h.isFermionSector.derivSubmodule_le_centreEigenspace c)

/-!

## B. Mass weights five and seven

Weight five is a single product, the Higgs field against the underived fermion towers.
Weight seven is a join of three: the Higgs field against the once-derived towers, the
once-derived Higgs field against the underived ones, and two Higgs fields against the
underived ones. Each of the four has exactly one fermion factor, so section A gives all of
them the sign `-1`, the join included, and the invariant is left in `S`.

-/

/-- Mass weight five carries no Lorentz invariant modulo a Lorentz-stable submodule: a
  Lorentz invariant of `sectorMassWeight {higgs, fermion} 5 ⊔ S` lies in `S`. The weight is
  one Higgs field against the underived fermion towers, of half-integer spin. -/
theorem mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_five_sup (S : Submodule ℂ B)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 5 ⊔ S)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  rw [h.sectorMassWeight_higgs_fermion_five] at hx
  exact mem_of_invariant_of_mem_sup_centreEigenspace_neg_one
    (h.higgsFermion_le_centreEigenspace 0 0) S hSL hx hL

/-- Mass weight seven carries no Lorentz invariant modulo a Lorentz-stable submodule: a
  Lorentz invariant of `sectorMassWeight {higgs, fermion} 7 ⊔ S` lies in `S`. Each of the
  three products making up the weight has a single fermion factor, so each is of
  half-integer spin and so is their join. -/
theorem mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_seven_sup
    (S : Submodule ℂ B) (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 7 ⊔ S)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  rw [h.sectorMassWeight_higgs_fermion_seven] at hx
  exact mem_of_invariant_of_mem_sup_centreEigenspace_neg_one
    (sup_le (sup_le (h.higgsFermion_le_centreEigenspace 0 1)
      (h.higgsFermion_le_centreEigenspace 1 0))
      (h.higgsSqFermion_le_centreEigenspace 0 0 0)) S hSL hx hL

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

/-- Below mass weight eight the Yukawa sector carries no Lorentz invariant: a Lorentz
  invariant of `sectorMassWeight {higgs, fermion} w ⊔ S` for `w < 8` lies in `S`. Weights
  below five and weight six are trivial submodules, and weights five and seven are section
  B. -/
theorem mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_lt_eight_sup (w : ℕ)
    (hw : w < 8) (S : Submodule ℂ B)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} w ⊔ S)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  rcases lt_or_ge w 5 with hw5 | hw5
  · rwa [h.sectorMassWeight_higgs_fermion_eq_bot_of_lt_five hw5, bot_sup_eq] at hx
  interval_cases w
  · exact h.mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_five_sup S hSL hx hL
  · rwa [h.sectorMassWeight_higgs_fermion_six, bot_sup_eq] at hx
  · exact h.mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_seven_sup S hSL hx hL

set_option linter.unusedVariables false in
/-- The classification below mass weight eight as an equivalence, in the shape of the
  gauge-sector statement `mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff`:
  an element of `sectorMassWeight {higgs, fermion} w ⊔ S` for `w < 8` is fixed by both
  groups exactly when it is itself an element of `S` fixed by both groups. Gauge stability
  of `S` is not needed, and neither is gauge invariance of `x`: the forward direction is
  the spin parity argument, which uses the Lorentz group alone. -/
theorem mem_sectorMassWeight_higgs_fermion_lt_eight_sup_and_gauge_lorentz_invariant_iff
    (w : ℕ) (hw : w < 8) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} w ⊔ S
        ∧ (∀ g : GaugeGroupI, repGauge g x = x) ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x = y := by
  constructor
  · rintro ⟨hx, hG, hL⟩
    exact ⟨x, h.mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_lt_eight_sup w hw S
      hSL hx hL, hG, hL, rfl⟩
  · rintro ⟨y, hyS, hyG, hyL, rfl⟩
    exact ⟨Submodule.mem_sup_right hyS, hyG, hyL⟩

set_option linter.unusedVariables false in
/-- The same classification without the existential: below mass weight eight an element of
  `sectorMassWeight {higgs, fermion} w ⊔ S` fixed by both groups is an element of `S` fixed
  by both groups, and conversely. -/
theorem mem_sectorMassWeight_higgs_fermion_lt_eight_sup_and_gauge_lorentz_invariant_iff_mem
    (w : ℕ) (hw : w < 8) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} w ⊔ S
        ∧ (∀ g : GaugeGroupI, repGauge g x = x) ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ (x ∈ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentz g x = x) :=
  ⟨fun hx => ⟨h.mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_lt_eight_sup w hw S
    hSL hx.1 hx.2.2, hx.2⟩, fun hx => ⟨Submodule.mem_sup_right hx.1, hx.2⟩⟩

end CovAlgebraRealization

end StandardModel
