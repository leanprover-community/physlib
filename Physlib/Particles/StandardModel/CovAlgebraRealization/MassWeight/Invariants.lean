/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.CovAlgebraRealization.FermionGaugeSector.MassWeight
public import Physlib.Particles.StandardModel.CovAlgebraRealization.GaugeHiggsSector.MassWeight
public import Physlib.Particles.StandardModel.CovAlgebraRealization.MixedSector.Basic
public import Physlib.Particles.StandardModel.CovAlgebraRealization.YukawaSector.MassDimEight
public import Physlib.Particles.StandardModel.IsFermionSector.MassWeight.MassDimEight
public import Physlib.Particles.StandardModel.IsFermionSector.MassWeight.MassDimLTEight
public import Physlib.Particles.StandardModel.IsGaugeSector.MassWeight.MassDimEight
public import Physlib.Particles.StandardModel.AlgebraRealization.HiggsAlgebraCovRealization.MassWeight.MassDimEight
/-!
# The invariant content of the Standard Model

This is where the classification of the Standard Model closes. A word in the covariant
generators realises a set of generator classes — gauge, Higgs, fermion — and the eight
class sets cut the field algebra into eight sectors, each of which has been classified
separately at every mass weight up to eight, that is at every mass dimension up to four.
This file joins the eight.

At mass dimension four the gauge- and Lorentz-invariant content is spanned by the four
Lorentz contractions of each of the three `F·F` trace families and of the twice-derived
hypercharge field strength, which include the gauge kinetic and theta terms of the three
gauge groups; the Higgs kinetic term with its quartic potential and its two box terms; the
kinetic terms of the ten fermion species over the nine family pairs; and the six Yukawa
couplings over the nine family pairs. Below mass dimension four there is a single term, the
Higgs mass term `H† H` at mass weight four; below that, nothing.

The statement is about formal expressions, the elements of the field algebra with complex
coefficients. It is a spanning statement: the listed generators are not shown to be
independent or nonzero. No reality condition is imposed, and nothing is identified modulo
total derivatives or the equations of motion, so both box terms, both placements of each
fermion derivative and the theta terms all appear.

The join is the delicate step. `massWeightSubmodule_eq_iSup_sectorMassWeight` writes the
weight-`w` submodule as the join of the eight sectors' weight-`w` parts, but reading off
from an invariant of the whole that its eight pieces are separately invariant would need
the pieces to be determined by their sum — the independence of the sectors, which does
not follow from `CovAlgebraRealization` (compare `sector_invariant_of_iSupIndep`).

Nothing here uses it. Each sector's classification is a reduction `ReducesInvariantsTo σ V W`
of `Physlib.Mathematics.InvariantReduction` — every `σ`-invariant of `V ⊔ S` lies in
`W ⊔ S`, for every `σ`-stable `S` — and that relation is closed under joins in its source.
Joining the sectors therefore asks only that each of them be carried into itself by the two
groups, which they are (`repGauge_mem_sectorMassWeight`, `repLorentz_mem_sectorMassWeight`).
The eight are taken one at a time, each in turn joining the error term of the others, and
independence never enters.

Section A collects the surviving spans of the eight sectors into `standardModelSpan`, and
section B checks that it is made of invariants of the right mass weight, which is both the
easy direction of the classification and the stability the reduction asks of its target.
Section C restricts each sector's reduction to its weight part, section D joins them, and
sections E and F read off the equivalence, through
`ReducesInvariantsTo.mem_sup_and_gauge_lorentz_invariant_iff`, and its consequence at mass
dimension four.

- A. The span of the Standard Model Lagrangian
- B. The span is made of invariants of the right weight
- C. Each sector reduces to the span
- D. Joining the eight sectors
- E. The classification at mass dimension at most four
- F. The Standard Model Lagrangian

The weight is bounded below as well as above. At weight zero the field algebra contains
the scalars, which are fixed by both groups and lie in no given `S`; every one of the
sector classifications combined here excludes that weight for the same reason.

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

namespace CovAlgebraRealization

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : CovAlgebraRealization B repGauge repLorentz massWeightPoly)

/-!

## A. The span of the Standard Model Lagrangian

-/

/-- The gauge- and Lorentz-invariant content of the Standard Model at mass weight `w`:
  the join of the surviving spans of the eight sectors. At weight eight it is the gauge
  sector's four Lorentz contractions of each of its four families, among them the kinetic
  and theta terms of the three gauge groups, together with the Higgs sector's two box
  terms, kinetic term and quartic potential, the fermion sector's ten kinetic terms over the
  nine family pairs, and the six Yukawa couplings over the nine family pairs. Below weight
  eight only the Higgs sector survives, and only at weight four, where it contributes the
  Higgs mass term. -/
noncomputable def standardModelSpan (w : ℕ) : Submodule ℂ B :=
  if w = 8 then
    h.isGaugeSector.lorentzContractionEightSpan
        ⊔ h.isHiggsSector.lorentzContractionEightSpan
      ⊔ (h.isFermionSector.kineticSpan ⊔ h.yukawaSpan)
  else h.isHiggsSector.lorentzContractionLTEightSpan w

/-- At mass weight eight the span is the gauge, Higgs, fermion and Yukawa spans
  together. -/
lemma standardModelSpan_eight :
    h.standardModelSpan 8 = h.isGaugeSector.lorentzContractionEightSpan
        ⊔ h.isHiggsSector.lorentzContractionEightSpan
      ⊔ (h.isFermionSector.kineticSpan ⊔ h.yukawaSpan) :=
  ite_eq_left rfl

/-- At mass weight four the span is the line through the Higgs mass term `H† H`, the one
  invariant of the Standard Model below mass dimension four. -/
lemma standardModelSpan_four : h.standardModelSpan 4 = h.isHiggsSector.dotSpan 0 0 := by
  rw [standardModelSpan, ite_eq_right (by norm_num), HiggsAlgebraCovRealization.lorentzContractionLTEightSpan,
    ite_eq_left rfl]

/-- At every mass weight other than four and eight the span is trivial: apart from the
  Higgs mass term there is no Standard-Model term below mass dimension four. -/
lemma standardModelSpan_eq_bot {w : ℕ} (hw : w ≠ 8) (hw4 : w ≠ 4) :
    h.standardModelSpan w = ⊥ := by
  rw [standardModelSpan, ite_eq_right hw, HiggsAlgebraCovRealization.lorentzContractionLTEightSpan,
    ite_eq_right hw4]

/-!

## B. The span is made of invariants of the right weight

-/

/-- At a non-zero weight the gauge sector's mass-weight submodule sits inside the
  covariant model's, being the `{gauge}` piece of the sector decomposition there. -/
lemma isGaugeSector_massWeightSubmodule_le {w : ℕ} (hw : w ≠ 0) :
    h.isGaugeSector.massWeightSubmodule w ≤ h.massWeightSubmodule w := by
  rw [← h.sectorMassWeight_gauge_eq hw]
  exact h.sectorMassWeight_le_massWeightSubmodule _ w

/-- At a non-zero weight the Higgs sector's mass-weight submodule sits inside the
  covariant model's. -/
lemma isHiggsSector_massWeightSubmodule_le {w : ℕ} (hw : w ≠ 0) :
    h.isHiggsSector.massWeightSubmodule w ≤ h.massWeightSubmodule w := by
  rw [← h.sectorMassWeight_higgs_eq hw]
  exact h.sectorMassWeight_le_massWeightSubmodule _ w

/-- At a non-zero weight the fermion sector's mass-weight submodule sits inside the
  covariant model's. -/
lemma isFermionSector_massWeightSubmodule_le {w : ℕ} (hw : w ≠ 0) :
    h.isFermionSector.massWeightSubmodule w ≤ h.massWeightSubmodule w := by
  rw [← h.sectorMassWeight_fermion_eq hw]
  exact h.sectorMassWeight_le_massWeightSubmodule _ w

/-- The span at weight `w` has mass weight `w`: each of its contributions is a
  combination of words of that weight. -/
lemma standardModelSpan_le_massWeightSubmodule (w : ℕ) :
    h.standardModelSpan w ≤ h.massWeightSubmodule w := by
  rw [standardModelSpan]
  split_ifs with hw
  · subst hw
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact h.isGaugeSector.lorentzContractionEightSpan_le_massWeightSubmodule.trans
        (h.isGaugeSector_massWeightSubmodule_le (by norm_num))
    · exact h.isHiggsSector.lorentzContractionEightSpan_le_massWeightSubmodule.trans
        (h.isHiggsSector_massWeightSubmodule_le (by norm_num))
    · exact h.isFermionSector.kineticSpan_le_massWeightSubmodule.trans
        (h.isFermionSector_massWeightSubmodule_le (by norm_num))
    · exact h.yukawaSpan_le_inf.trans (le_trans inf_le_left (le_trans inf_le_left
        (h.sectorMassWeight_le_massWeightSubmodule _ 8)))
  · by_cases hw4 : w = 4
    · subst hw4
      exact (h.isHiggsSector.lorentzContractionLTEightSpan_le_massWeightSubmodule 4).trans
        (h.isHiggsSector_massWeightSubmodule_le (by norm_num))
    · rw [HiggsAlgebraCovRealization.lorentzContractionLTEightSpan, ite_eq_right hw4]
      exact bot_le

/-- The span at weight `w` is fixed pointwise by the gauge and Lorentz groups together:
  every one of its contributions is a span of invariants. This is the easy direction of
  the classification, and it is also what supplies the stability the reduction asks of its
  target. -/
lemma isFixedBy_standardModelSpan (w : ℕ) :
    IsFixedBy (gaugeLorentzMaps repGauge repLorentz) (h.standardModelSpan w) := by
  rw [standardModelSpan]
  split_ifs with hw
  · exact (h.isGaugeSector.isFixedBy_lorentzContractionEightSpan.sup
      h.isHiggsSector.isFixedBy_lorentzContractionEightSpan).sup
      (h.isFermionSector.isFixedBy_kineticSpan.sup h.isFixedBy_yukawaSpan)
  · exact h.isHiggsSector.isFixedBy_lorentzContractionLTEightSpan w

/-- Every element of the span at weight `w` is a gauge invariant. -/
lemma repGauge_of_mem_standardModelSpan (w : ℕ) (g : GaugeGroupI) {y : B}
    (hy : y ∈ h.standardModelSpan w) : repGauge g y = y :=
  h.isFixedBy_standardModelSpan w (Sum.inl g) y hy

/-- Every element of the span at weight `w` is a Lorentz invariant. -/
lemma repLorentz_of_mem_standardModelSpan (w : ℕ) (Λ : SL(2,ℂ)) {y : B}
    (hy : y ∈ h.standardModelSpan w) : repLorentz Λ y = y :=
  h.isFixedBy_standardModelSpan w (Sum.inr Λ) y hy

/-!

## C. Each sector reduces to the span

-/

/-- The empty sector reduces to the span: away from weight zero it is trivial, its only word
  being the empty one. -/
lemma reducesInvariantsTo_sectorMassWeight_empty {w : ℕ} (hw : w ≠ 0) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (h.sectorMassWeight ∅ w)
      (h.standardModelSpan w) := by
  rw [h.sectorMassWeight_empty_of_ne_zero hw]
  exact reducesInvariantsTo_of_le bot_le

/-- The gauge sector reduces to the span: at weight eight to the four Lorentz contractions of
  its four families, below it to nothing at all. -/
lemma reducesInvariantsTo_sectorMassWeight_gauge {w : ℕ} (hw0 : 0 < w) (hw : w ≤ 8) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (h.sectorMassWeight {GeneratorClass.gauge} w) (h.standardModelSpan w) := by
  refine ReducesInvariantsTo.mono_left ?_ (h.sectorMassWeight_gauge_le w)
  rcases eq_or_lt_of_le hw with rfl | hw8
  · rw [h.standardModelSpan_eight]
    exact h.isGaugeSector.reducesInvariantsTo_lorentzContractionEightSpan.mono_right
      (le_sup_of_le_left le_sup_left)
  · exact (ReducesInvariantsTo.ofLorentz (W := ⊥) fun S hS x hx hL => Submodule.mem_sup_right
      (h.isGaugeSector.mem_of_lorentz_invariant_massWeightSubmodule_lt_eight_sup w hw0 hw8 S hS
        hx hL)).mono_right bot_le

/-- The Higgs sector reduces to the span: at weight eight to the two box terms, the kinetic
  term and the quartic potential, at weight four to the Higgs mass term, and elsewhere to
  nothing. -/
lemma reducesInvariantsTo_sectorMassWeight_higgs {w : ℕ} (hw0 : 0 < w) (hw : w ≤ 8) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (h.sectorMassWeight {GeneratorClass.higgs} w) (h.standardModelSpan w) := by
  refine ReducesInvariantsTo.mono_left ?_ (h.sectorMassWeight_higgs_le w)
  rcases eq_or_lt_of_le hw with rfl | hw8
  · rw [h.standardModelSpan_eight]
    exact h.isHiggsSector.reducesInvariantsTo_lorentzContractionEightSpan.mono_right
      (le_sup_of_le_left le_sup_right)
  · rw [standardModelSpan, ite_eq_right (by omega)]
    exact h.isHiggsSector.reducesInvariantsTo_lorentzContractionLTEightSpan hw0 hw8

/-- The fermion sector reduces to the span: at weight eight to the ten kinetic terms over the
  nine family pairs, below it to nothing — there is no Dirac mass term. -/
lemma reducesInvariantsTo_sectorMassWeight_fermion {w : ℕ} (hw0 : 0 < w) (hw : w ≤ 8) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (h.sectorMassWeight {GeneratorClass.fermion} w) (h.standardModelSpan w) := by
  refine ReducesInvariantsTo.mono_left ?_ (h.sectorMassWeight_fermion_le w)
  rcases eq_or_lt_of_le hw with rfl | hw8
  · rw [h.standardModelSpan_eight]
    exact h.isFermionSector.reducesInvariantsTo_kineticSpan.mono_right
      (le_sup_of_le_right le_sup_left)
  · refine ReducesInvariantsTo.mono_right (W' := ⊥) (fun S hS x hx hinv => ?_) bot_le
    obtain ⟨hSG, hSL⟩ := isStableUnder_gaugeLorentzMaps_iff.1 hS
    obtain ⟨hG, hL⟩ := forall_gaugeLorentzMaps_eq_self_iff.1 hinv
    exact Submodule.mem_sup_right
      (h.isFermionSector.mem_of_invariant_massWeightSubmodule_lt_eight_sup w hw0 hw8 S hSG hSL
        hx hG hL)

/-- The Yukawa sector reduces to the span: at weight eight to the six Yukawa couplings over the
  nine family pairs, below it to nothing. -/
lemma reducesInvariantsTo_sectorMassWeight_higgs_fermion {w : ℕ} (hw : w ≤ 8) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} w)
      (h.standardModelSpan w) := by
  rcases eq_or_lt_of_le hw with rfl | hw8
  · rw [h.standardModelSpan_eight]
    exact h.reducesInvariantsTo_sectorMassWeight_higgs_fermion_eight.mono_right
      (le_sup_of_le_right le_sup_right)
  · exact (ReducesInvariantsTo.ofLorentz (W := ⊥) fun S hS x hx hL => Submodule.mem_sup_right
      (h.mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_lt_eight_sup w hw8 S hS hx
        hL)).mono_right bot_le

/-- The gauge-Higgs sector reduces to nothing: it carries no Lorentz invariant below weight
  nine. -/
lemma reducesInvariantsTo_sectorMassWeight_gauge_higgs {w : ℕ} (hw : w ≤ 8) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.higgs} w)
      (h.standardModelSpan w) :=
  (ReducesInvariantsTo.ofLorentz (W := ⊥) fun S hS x hx hL => Submodule.mem_sup_right
    (h.mem_of_invariant_sectorMassWeight_gauge_higgs_lt_nine_sup w (by omega) S hS hx
      hL)).mono_right bot_le

/-- The gauge-fermion sector reduces to nothing: it carries no Lorentz invariant below weight
  nine. -/
lemma reducesInvariantsTo_sectorMassWeight_gauge_fermion {w : ℕ} (hw : w ≤ 8) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.fermion} w)
      (h.standardModelSpan w) :=
  (ReducesInvariantsTo.ofLorentz (W := ⊥) fun S hS x hx hL => Submodule.mem_sup_right
    (h.mem_of_invariant_sectorMassWeight_gauge_fermion_lt_nine_sup w (by omega) S hS hx
      hL)).mono_right bot_le

/-- The mixed sector reduces to nothing: it is trivial below weight nine. -/
lemma reducesInvariantsTo_sectorMassWeight_mixed {w : ℕ} (hw : w ≤ 8) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz)
      (h.sectorMassWeight
        {GeneratorClass.gauge, GeneratorClass.higgs, GeneratorClass.fermion} w)
      (h.standardModelSpan w) := fun S _ x hx _ =>
  Submodule.mem_sup_right
    (h.mem_of_invariant_sectorMassWeight_mixed_lt_nine_sup w (by omega) S hx)

/-!

## D. Joining the eight sectors

-/

/-- Every weight part of every sector is carried into itself by both groups: the stability
  the join of the reductions asks of its summands. -/
lemma isStableUnder_sectorMassWeight (T : Finset GeneratorClass) (w : ℕ) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.sectorMassWeight T w) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨fun g _ hy => h.repGauge_mem_sectorMassWeight g hy,
      fun Λ _ hy => h.repLorentz_mem_sectorMassWeight Λ hy⟩

/-- Every sector reduces to the span, at every weight from one to eight. The three
  constructors of `GeneratorClass` give eight class sets, and section C treats each. -/
lemma reducesInvariantsTo_sectorMassWeight {w : ℕ} (hw0 : 0 < w) (hw : w ≤ 8)
    (T : Finset GeneratorClass) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (h.sectorMassWeight T w)
      (h.standardModelSpan w) := by
  have hT : T = ∅ ∨ T = {GeneratorClass.gauge} ∨ T = {GeneratorClass.higgs}
      ∨ T = {GeneratorClass.fermion} ∨ T = {GeneratorClass.gauge, GeneratorClass.higgs}
      ∨ T = {GeneratorClass.gauge, GeneratorClass.fermion}
      ∨ T = {GeneratorClass.higgs, GeneratorClass.fermion}
      ∨ T = {GeneratorClass.gauge, GeneratorClass.higgs, GeneratorClass.fermion} := by
    revert T
    decide
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.reducesInvariantsTo_sectorMassWeight_empty (by omega)
  · exact h.reducesInvariantsTo_sectorMassWeight_gauge hw0 hw
  · exact h.reducesInvariantsTo_sectorMassWeight_higgs hw0 hw
  · exact h.reducesInvariantsTo_sectorMassWeight_fermion hw0 hw
  · exact h.reducesInvariantsTo_sectorMassWeight_gauge_higgs hw
  · exact h.reducesInvariantsTo_sectorMassWeight_gauge_fermion hw
  · exact h.reducesInvariantsTo_sectorMassWeight_higgs_fermion hw
  · exact h.reducesInvariantsTo_sectorMassWeight_mixed hw

/-- The whole weight-`w` submodule reduces to the span, for `w` from one to eight. The
  mass-weight submodule is the join of the eight sectors' weight-`w` parts, each of them
  stable under both groups, and `ReducesInvariantsTo` is closed under joins in its source: the
  sectors are taken one at a time, each in turn joining the error term of the others. No
  independence of the sectors is used, and none is available. -/
lemma reducesInvariantsTo_massWeightSubmodule {w : ℕ} (hw0 : 0 < w) (hw : w ≤ 8) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) (h.massWeightSubmodule w)
      (h.standardModelSpan w) := by
  rw [h.massWeightSubmodule_eq_iSup_sectorMassWeight w]
  exact ReducesInvariantsTo.iSup (fun T => h.reducesInvariantsTo_sectorMassWeight hw0 hw T)
    (fun T => h.isStableUnder_sectorMassWeight T w)
    (h.isFixedBy_standardModelSpan w).isStableUnder

/-!

## E. The classification at mass dimension at most four

-/

/-- The classification of the Standard Model at mass dimension at most four as an
  equivalence, in the shape every sector uses: an element of `massWeightSubmodule w ⊔ S`
  for `0 < w ≤ 8`, with `S` stable under both groups, is fixed by both groups exactly when
  it is a combination of the Standard-Model terms of weight `w` up to a remainder in `S`
  fixed by both groups. Forwards this is the reduction of section D; backwards it uses
  that the span is made of invariants of weight `w`, section B. The weight-four Higgs mass
  term is what makes the span, rather than the bare equation `x = y`, the right form of
  the statement. -/
theorem mem_massWeightSubmodule_sup_and_gauge_lorentz_invariant_iff (w : ℕ) (hw0 : 0 < w)
    (hw : w ≤ 8) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmodule w ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x - y ∈ h.standardModelSpan w :=
  ReducesInvariantsTo.mem_sup_and_gauge_lorentz_invariant_iff
    (h.reducesInvariantsTo_massWeightSubmodule hw0 hw)
    (h.standardModelSpan_le_massWeightSubmodule w) (h.isFixedBy_standardModelSpan w) hS hSL x

/-- The gauge and Lorentz invariants of mass weight `w` for `0 < w ≤ 8`, modulo a
  submodule `S` stable under both groups: such an invariant is a combination of the
  Standard-Model terms of that weight plus a remainder in `S`, and the remainder is fixed
  by both groups as well, being the difference of two invariants. -/
theorem exists_mem_standardModelSpan_of_gauge_and_lorentz_invariant (w : ℕ)
    (hw0 : 0 < w) (hw : w ≤ 8) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmodule w ⊔ S)
    (hG : ∀ g : GaugeGroupI, repGauge g x = x)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
      ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
      ∧ x - y ∈ h.standardModelSpan w :=
  (h.mem_massWeightSubmodule_sup_and_gauge_lorentz_invariant_iff w hw0 hw S hS hSL x).1
    ⟨hx, hG, hL⟩

/-- The same classification without the existential: at every weight from one to eight an
  element of `massWeightSubmodule w ⊔ S` fixed by both groups is an element of the
  Standard-Model span joined with `S` fixed by both groups, and conversely. -/
theorem mem_massWeightSubmodule_sup_and_gauge_lorentz_invariant_iff_mem (w : ℕ)
    (hw0 : 0 < w) (hw : w ≤ 8) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmodule w ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ (x ∈ h.standardModelSpan w ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentz g x = x) :=
  ⟨fun hx => ⟨h.reducesInvariantsTo_massWeightSubmodule hw0 hw S
      (isStableUnder_gaugeLorentzMaps_iff.2 ⟨hS, hSL⟩) x hx.1
      (forall_gaugeLorentzMaps_eq_self_iff.2 hx.2), hx.2⟩,
    fun hx => ⟨sup_le_sup_right (h.standardModelSpan_le_massWeightSubmodule w) S hx.1, hx.2⟩⟩

/-!

## F. The Standard Model Lagrangian

-/

/-- The invariant content of the Standard Model at mass dimension four. An element of
  `massWeightSubmodule 8 ⊔ S`, for `S` a submodule stable under both groups, is fixed by
  the gauge group and the Lorentz group exactly when it is a combination of
  the four Lorentz contractions of the three `F·F` trace families and of the twice-derived
  hypercharge field strength, among them the gauge kinetic and theta terms
  (`IsGaugeSector.lorentzContractionEightSpan`),
  the Higgs kinetic term, its quartic potential and its two box terms
  (`HiggsAlgebraCovRealization.lorentzContractionEightSpan`),
  the kinetic terms of the ten fermion species over the nine family pairs
  (`IsFermionSector.kineticSpan`),
  and the six Yukawa couplings over the nine family pairs (`yukawaSpan`),
  up to a remainder in `S` fixed by both groups — and nothing else. The generators span;
  they are not shown to be independent, and no quotient by total derivatives is taken. -/
theorem mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff_lagrangian
    (S : Submodule ℂ B) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmodule 8 ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x - y ∈ h.isGaugeSector.lorentzContractionEightSpan
                ⊔ h.isHiggsSector.lorentzContractionEightSpan
              ⊔ (h.isFermionSector.kineticSpan ⊔ h.yukawaSpan) := by
  rw [← h.standardModelSpan_eight]
  exact h.mem_massWeightSubmodule_sup_and_gauge_lorentz_invariant_iff 8 (by norm_num)
    le_rfl S hS hSL x

/-- Below mass dimension two there is nothing at all, and at mass dimension two only the
  Higgs mass term: at every weight from one to seven other than four an element of
  `massWeightSubmodule w ⊔ S` fixed by both groups already lies in `S`. -/
theorem mem_of_gauge_and_lorentz_invariant_massWeightSubmodule_sup (w : ℕ) (hw0 : 0 < w)
    (hw : w < 8) (hw4 : w ≠ 4) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmodule w ⊔ S)
    (hG : ∀ g : GaugeGroupI, repGauge g x = x)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  have hmem := ((h.mem_massWeightSubmodule_sup_and_gauge_lorentz_invariant_iff_mem w hw0
    (by omega) S hS hSL x).1 ⟨hx, hG, hL⟩).1
  rwa [h.standardModelSpan_eq_bot (by omega) hw4, bot_sup_eq] at hmem

/-- At mass dimension two the only invariant of the Standard Model is the Higgs mass term
  `H† H`: an element of `massWeightSubmodule 4 ⊔ S` fixed by both groups is a multiple of
  it up to a remainder in `S` fixed by both groups. -/
theorem mem_massWeightSubmodule_four_sup_and_gauge_lorentz_invariant_iff_higgsMass
    (S : Submodule ℂ B) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmodule 4 ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x - y ∈ h.isHiggsSector.dotSpan 0 0 := by
  rw [← h.standardModelSpan_four]
  exact h.mem_massWeightSubmodule_sup_and_gauge_lorentz_invariant_iff 4 (by norm_num)
    (by norm_num) S hS hSL x

end CovAlgebraRealization

end StandardModel
