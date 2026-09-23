/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.CovAlgebraRealization.FermionGaugeSector.Basic
public import Physlib.Particles.StandardModel.CovAlgebraRealization.YukawaSector.MassDimLTEight
public import Physlib.Particles.StandardModel.IsGaugeSector.DerivSubmodule.Centre
/-!
# The gauge-fermion invariants below mass weight nine

The mixed `{gauge, fermion}` sector is almost empty below weight nine, and what little
there is cannot be invariant. A field-strength tower weighs at least four and a fermion
tower at least three, so the sector vanishes below weight seven; at weight eight the two
splittings that arithmetic allows are `4 + 4` and `6 + 2`, and the fermion sector is
trivial at both four and two, so weight eight vanishes too. That leaves weight seven, the
single product `F ψ` of the underived field strength against the underived fermion towers.

Weight seven is barred from carrying an invariant by the same parity count on spin that
empties the Yukawa sector at weights five and seven. The field strength is of integer spin,
its two covector indices and its derivative slots all mixing by the Lorentz matrix and its
adjoint index not seeing the Lorentz group at all, while a fermion carries one Weyl-spinor
index. The one product at weight seven has exactly one fermion factor, so it is of
half-integer spin; and a half-integer spin carries no Lorentz invariant.

The machinery is the Yukawa sector's: `mul_le_centreEigenspace` multiplies the signs the
two factors carry at the centre of `SL(2,ℂ)`, and
`mem_of_invariant_of_mem_sup_centreEigenspace_neg_one` turns the sign `-1` into the absence
of invariants modulo a Lorentz-stable submodule. Only the left-hand factor changes: the
Higgs sign `+1` is replaced by the gauge one, which is `+1` for the same reason.

- A. Integer field strength against half-integer fermion
- B. Mass weight seven
- C. The classification below mass weight nine

The bound is `w < 9` rather than `w < 8`: weight eight is as empty as the weights below
seven, so nothing is gained by stopping short of the first weight the sector can occupy.

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

## A. Integer field strength against half-integer fermion

The signs the two factors carry at the centre are already proved: the field-strength
derivative submodules carry `+1`, every one of their indices being inert there, and the
fermion ones carry `-1`, the Weyl-spinor value index doing the work. The Lorentz action on
`B` is by algebra maps, so the product carries `+1` times `-1`.

-/

/-- A field-strength derivative submodule against a fermion one is of half-integer spin:
  `+1` times `-1`. -/
private lemma gaugeFermion_le_centreEigenspace (a b : ℕ) :
    h.isGaugeSector.derivSubmodule a * h.isFermionSector.derivSubmodule b
      ≤ centreEigenspace repLorentz (-1) := by
  simpa using mul_le_centreEigenspace h.repLorentz_mul
    (h.isGaugeSector.derivSubmodule_le_centreEigenspace a)
    (h.isFermionSector.derivSubmodule_le_centreEigenspace b)

/-!

## B. Mass weight seven

Weight seven is the single product `F ψ`, the underived field strength against the
underived fermion towers. It has exactly one fermion factor, so section A gives it the sign
`-1`, and a subspace of sign `-1` carries no invariant modulo a Lorentz-stable submodule.

-/

/-- Mass weight seven carries no Lorentz invariant modulo a Lorentz-stable submodule: a
  Lorentz invariant of `sectorMassWeight {gauge, fermion} 7 ⊔ S` lies in `S`. The weight is
  the underived field strength against the underived fermion towers, of half-integer
  spin. -/
theorem mem_of_lorentz_invariant_sectorMassWeight_gauge_fermion_seven_sup (S : Submodule ℂ B)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.fermion} 7 ⊔ S)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  rw [h.sectorMassWeight_gauge_fermion_seven] at hx
  exact mem_of_invariant_of_mem_sup_centreEigenspace_neg_one
    (h.gaugeFermion_le_centreEigenspace 0 0) S hSL hx hL

/-!

## C. The classification below mass weight nine

The nine weights below nine are now settled: the sector vanishes below weight seven and
again at weight eight, and weight seven is section B. So below weight nine the
gauge-fermion sector supplies no invariant beyond what `S` already carries, and the
equivalences record it in the shape the other sectors carry, so that all of them can be
combined.

No lower bound on the weight is needed. The sector is the two-class sector of the gauge
and fermion generators, so both classes must be present with a non-zero weight and the
sector is already trivial at weight zero; the scalars, which force `0 < w` in the
gauge-sector statement, never appear.

-/

/-- Below mass weight nine the gauge-fermion sector carries no Lorentz invariant: a
  Lorentz invariant of `sectorMassWeight {gauge, fermion} w ⊔ S` for `w < 9` lies in `S`.
  Weights below seven and weight eight are trivial submodules, and weight seven is section
  B. -/
theorem mem_of_invariant_sectorMassWeight_gauge_fermion_lt_nine_sup (w : ℕ) (hw : w < 9)
    (S : Submodule ℂ B) (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.fermion} w ⊔ S)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  rcases lt_or_ge w 7 with hw7 | hw7
  · rwa [h.sectorMassWeight_gauge_fermion_eq_bot_of_lt_seven hw7, bot_sup_eq] at hx
  interval_cases w
  · exact h.mem_of_lorentz_invariant_sectorMassWeight_gauge_fermion_seven_sup S hSL hx hL
  · rwa [h.sectorMassWeight_gauge_fermion_eight, bot_sup_eq] at hx

set_option linter.unusedVariables false in
/-- The classification below mass weight nine as an equivalence, in the shape of the gauge-
  and Yukawa-sector statements: an element of `sectorMassWeight {gauge, fermion} w ⊔ S` for
  `w < 9` is fixed by both groups exactly when it is itself an element of `S` fixed by both
  groups. Gauge stability of `S` is not needed, and neither is gauge invariance of `x`: the
  forward direction is the boost-weight parity argument, which uses the Lorentz group
  alone. -/
theorem mem_sectorMassWeight_gauge_fermion_lt_nine_sup_and_gauge_lorentz_invariant_iff
    (w : ℕ) (hw : w < 9) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.fermion} w ⊔ S
        ∧ (∀ g : GaugeGroupI, repGauge g x = x) ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x = y := by
  constructor
  · rintro ⟨hx, hG, hL⟩
    exact ⟨x, h.mem_of_invariant_sectorMassWeight_gauge_fermion_lt_nine_sup w hw S hSL hx hL,
      hG, hL, rfl⟩
  · rintro ⟨y, hyS, hyG, hyL, rfl⟩
    exact ⟨Submodule.mem_sup_right hyS, hyG, hyL⟩

set_option linter.unusedVariables false in
/-- The same classification without the existential: below mass weight nine an element of
  `sectorMassWeight {gauge, fermion} w ⊔ S` fixed by both groups is an element of `S` fixed
  by both groups, and conversely. -/
theorem mem_sectorMassWeight_gauge_fermion_lt_nine_sup_and_gauge_lorentz_invariant_iff_mem
    (w : ℕ) (hw : w < 9) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.fermion} w ⊔ S
        ∧ (∀ g : GaugeGroupI, repGauge g x = x) ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ (x ∈ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentz g x = x) :=
  ⟨fun hx => ⟨h.mem_of_invariant_sectorMassWeight_gauge_fermion_lt_nine_sup w hw S hSL
    hx.1 hx.2.2, hx.2⟩, fun hx => ⟨Submodule.mem_sup_right hx.1, hx.2⟩⟩

end CovAlgebraRealization

end StandardModel
