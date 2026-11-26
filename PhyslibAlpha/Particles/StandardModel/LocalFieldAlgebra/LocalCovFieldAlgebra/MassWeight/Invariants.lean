/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.FermionGaugeSector.MassWeight
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.GaugeHiggsSector.MassWeight
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.MixedSector.Basic
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.YukawaSector.MassDimEight
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.FermionSector.MassWeight.MassDimEight
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.GaugeSector.MassWeight.MassDimEight
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.ScalarSector.MassWeight.MassDimEight
/-!
# The invariant content of the Standard Model

The gauge and Lorentz invariants of the Standard Model at each mass weight from one to eight,
obtained by joining the classifications of the eight sectors.

## i. Overview

This is where the classification of the Standard Model closes. A product of covariant
generators realises a set of kinds (gauge, scalar, fermion), and the eight sets of kinds cut the
field algebra into eight sectors `fieldData.sectorMassWeight A w`, each of which has been classified
separately at every mass weight up to eight, that is at every mass dimension up to four.
This file joins the eight.

At mass dimension four the gauge- and Lorentz-invariant content is spanned by the four
Lorentz contractions of each of the three `F·F` trace families and of the twice-derived
hypercharge field strength. The antisymmetry of the field strength cuts these to two of each
(`GaugeSector.lorentzContractionEightSpan_eq`), and the two of the twice-derived hypercharge
field strength vanish, its covariant derivatives being ordinary ones (A.1). What is left is the
kinetic-shape and theta-shape contractions of the three gauge groups. Beside them stand the
Higgs kinetic term with its quartic potential and its two box terms; the kinetic terms of the
ten fermion species over the nine family pairs; and the six Yukawa couplings over the nine
family pairs. Below mass dimension four there is a single term, the Higgs mass term `H† H` at
mass weight four; below that, nothing.

The statement is about formal expressions, the elements of the field algebra with complex
coefficients. It is a spanning statement, and the listed generators are not shown to be
independent or nonzero. No reality condition is imposed, and nothing is identified modulo
total derivatives or the equations of motion, so both box terms, both placements of each
fermion derivative and the theta terms all appear.

The join is the delicate step. `massWeightSubmodule_eq_iSup_sectorMassWeight` writes the
weight-`w` submodule as the join of the eight sectors' weight-`w` parts, but reading off
from an invariant of the whole that its eight pieces are separately invariant would need
the pieces to be determined by their sum — the independence of the sectors, which does
not follow from the structure of the covariant field algebra of the Standard Model used here.

Nothing here uses it. Each sector's classification is a reduction `ReducesInvariantsTo σ V W`
of `PhyslibAlpha.Mathematics.InvariantReduction` — every `σ`-invariant of `V ⊔ S` lies in
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

The weight is bounded below as well as above. At weight zero the field algebra contains
the scalars, which are fixed by both groups and lie in no given `S`; every one of the
sector classifications combined here excludes that weight for the same reason.

## ii. Key results

In the namespace `StandardModel.LocalCovFieldAlgebra`:

- `standardModelSpan` : the gauge- and Lorentz-invariant content of the Standard Model at mass
  weight `w`, the join of the surviving spans of the eight sectors.
- `reducesInvariantsTo_massWeightSubmodule` : the weight-`w` submodule reduces to the span, for
  `w` from one to eight.
- `mem_massWeightSubmodule_sup_and_gauge_lorentz_invariant_iff` : the classification at each
  mass weight from one to eight.
- `mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff_lagrangian` : the invariant
  content at mass dimension four, written out term by term.

## iii. Table of contents

- A. The span of the Standard Model Lagrangian
  - A.1. The twice-derived hypercharge contractions vanish
- B. The span is made of invariants of the right weight
- C. Each sector reduces to the span
- D. Joining the eight sectors
- E. The classification at mass dimension at most four
- F. The Standard Model Lagrangian

## iv. References

* None.

-/

@[expose] public section

open TensorSpecies

namespace StandardModel

open GaugeFieldData (FieldKind)

open TensorProduct Matrix MatrixGroups Lorentz

namespace LocalCovFieldAlgebra

/-!

## A. The span of the Standard Model Lagrangian

-/

/-- The gauge- and Lorentz-invariant content of the Standard Model at mass weight `w`, the join of
  the surviving spans of the eight sectors. At weight eight it is the gauge sector's four Lorentz
  contractions of each of its four families, two of which already span for each family
  (`GaugeSector.lorentzContractionEightSpan_eq`), and the two of the twice-derived hypercharge field
  strength vanish, leaving the two contractions of each of the three trace families
  (`gaugeSector_lorentzContractionEightSpan_eq_traceFamilies`). These are the kinetic-shape and
  theta-shape contractions of the three gauge groups. Together with these come the Higgs sector's
  two box terms, kinetic term and quartic potential, the fermion sector's ten kinetic terms over the
  nine family pairs, and the six Yukawa couplings over the nine family pairs. Below weight eight
  only the Higgs sector survives, and only at weight four, where it contributes the Higgs mass
  term. -/
noncomputable def standardModelSpan (w : ℕ) : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  if w = 8 then
    GaugeSector.lorentzContractionEightSpan
        ⊔ ScalarSector.lorentzContractionEightSpan
      ⊔ (FermionSector.kineticSpan ⊔ yukawaSpan)
  else ScalarSector.lorentzContractionLTEightSpan w

/-- At mass weight eight the span is the gauge, Higgs, fermion and Yukawa spans
  together. -/
lemma standardModelSpan_eight :
    standardModelSpan 8 = GaugeSector.lorentzContractionEightSpan
        ⊔ ScalarSector.lorentzContractionEightSpan
      ⊔ (FermionSector.kineticSpan ⊔ yukawaSpan) :=
  ite_eq_left rfl

/-- At mass weight four the span is the line through the Higgs mass term `H† H`, the one
  invariant of the Standard Model below mass dimension four. -/
lemma standardModelSpan_four : standardModelSpan 4 = ScalarSector.dotSpan 0 0 := by
  rw [standardModelSpan, ite_eq_right (by norm_num),
    ScalarSector.lorentzContractionLTEightSpan,
    ite_eq_left rfl]

/-- At every mass weight other than four and eight the span is trivial. Apart from the
  Higgs mass term there is no Standard-Model term below mass dimension four. -/
lemma standardModelSpan_eq_bot {w : ℕ} (hw : w ≠ 8) (hw4 : w ≠ 4) :
    standardModelSpan w = ⊥ := by
  rw [standardModelSpan, ite_eq_right hw, ScalarSector.lorentzContractionLTEightSpan,
    ite_eq_right hw4]

/-!

### A.1. The twice-derived hypercharge contractions vanish

The hypercharge coordinate kills brackets, so the covariant derivatives of the hypercharge
field strength are ordinary derivatives, which commute (`covF_comp_perm_of_map_lie` with
`GaugeAlgebra.stdBasis_coord_inr_inr_lie`). The twice-derived hypercharge family is therefore
symmetric in its two derivative slots as well as antisymmetric in its two field-strength slots,
and `RankFour` sends both of its remaining contractions to zero. So six generators span the
gauge contribution: for each of the gluon, `W` and hypercharge trace families, the `(0,2)(1,3)`
metric contraction `η^{μρ} η^{νσ} F_{μν} F_{ρσ}` and the Levi-Civita contraction
`ε^{μνρσ} F_{μν} F_{ρσ}`, gauge index summed, as the plain component sums of `RankFour` with no
further normalisation. These are identities of local expressions; no integration by parts,
total-derivative quotient or equation of motion is involved.

The derivative symmetry is not a law of `GaugeSector`, which relates no derivative slots. It
holds here because the covariant derivatives of the field strength in the covariant field algebra of
the Standard Model are ordinary ones. Nothing is said about the
gluon and `W` components, whose covariant derivatives do not commute.

-/

/-- The twice-derived hypercharge field strengths are symmetric in their two derivative
  slots. -/
lemma hyperchargeDeriv_comp_swap_zero_one (d : GaugeSector.EightIdx) :
    GaugeSector.hyperchargeDeriv (d ∘ Equiv.swap 0 1) = GaugeSector.hyperchargeDeriv d := by
  have hl : (![d 1, d 0] : Fin 2 → Fin 1 ⊕ Fin 3) = ![d 0, d 1] ∘ Equiv.swap 0 1 := by
    funext i
    fin_cases i <;> rfl
  have h2 : Equiv.swap (0 : Fin 4) 1 2 = 2 := by decide
  have h3 : Equiv.swap (0 : Fin 4) 1 3 = 3 := by decide
  simp only [GaugeSector.hyperchargeDeriv, GaugeSector.hyperchargeField, Function.comp_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right, h2, h3]
  rw [hl]
  exact covF_comp_perm_of_map_lie (GaugeAlgebra.stdBasis_coord_inr_inr_lie 0) _ _ _ _

/-- The metric contraction `η^{μρ} η^{νσ} ∇_μ ∇_ν B_{ρσ}` vanishes, a symmetric pair of
  derivatives being contracted against the antisymmetric pair of field-strength indices. -/
lemma hyperchargeDeriv_contractionTensor_one :
    liftComponents GaugeSector.hyperchargeDeriv (RankFour.contractionTensor 1) = 0 :=
  RankFour.apply_contractionTensor_one_of_symm_of_antisymm
    (liftComponents_comp_permT_eq_self _ _ hyperchargeDeriv_comp_swap_zero_one)
    (liftComponents_comp_permT_eq_neg _ _ GaugeSector.hyperchargeDeriv_comp_swap_two_three)

/-- The Levi-Civita contraction `ε^{μνρσ} ∇_μ ∇_ν B_{ρσ}` vanishes, a symmetric pair of
  derivatives being contracted against the antisymmetric symbol. -/
lemma hyperchargeDeriv_contractionTensor_three :
    liftComponents GaugeSector.hyperchargeDeriv (RankFour.contractionTensor 3) = 0 :=
  RankFour.apply_contractionTensor_three_of_symm
    (liftComponents_comp_permT_eq_self _ _ hyperchargeDeriv_comp_swap_zero_one)

open RankFour in
/-- The gauge contribution at mass weight eight is spanned by the Lorentz contractions of the
  three trace families alone. For each of `gluonTrace`, `wTrace` and `hyperchargeTrace` these are
  the `(0,2)(1,3)` metric contraction `η^{μρ} η^{νσ} F_{μν} F_{ρσ}` and the Levi-Civita contraction
  `ε^{μνρσ} F_{μν} F_{ρσ}`, as plain component sums. The two twice-derived hypercharge
  generators of `GaugeSector.lorentzContractionEightSpan_eq` vanish. The six span; they are
  not shown to be independent or nonzero. -/
lemma gaugeSector_lorentzContractionEightSpan_eq_traceFamilies :
    GaugeSector.lorentzContractionEightSpan
      = Submodule.span ℂ {liftComponents GaugeSector.gluonTrace (contractionTensor 1),
          liftComponents GaugeSector.gluonTrace (contractionTensor 3)}
        ⊔ (Submodule.span ℂ {liftComponents GaugeSector.wTrace (contractionTensor 1),
            liftComponents GaugeSector.wTrace (contractionTensor 3)}
          ⊔ Submodule.span ℂ {liftComponents GaugeSector.hyperchargeTrace (contractionTensor 1),
            liftComponents GaugeSector.hyperchargeTrace (contractionTensor 3)}) := by
  rw [GaugeSector.lorentzContractionEightSpan_eq, hyperchargeDeriv_contractionTensor_one,
    hyperchargeDeriv_contractionTensor_three]
  simp

/-!

## B. The span is made of invariants of the right weight

-/

/-- At a non-zero weight the gauge sector's mass-weight submodule sits inside that of the
  covariant field algebra, being the `{gauge}` piece of the sector decomposition there. -/
lemma gaugeSector_massWeightSubmodule_le {w : ℕ} (hw : w ≠ 0) :
    GaugeSector.massWeightSubmodule w ≤ massWeightSubmodule w := by
  rw [← sectorMassWeight_gauge_eq hw]
  exact GaugeFieldData.sectorMassWeight_le_massWeightSubmodule isMassWeightPoly _ w

/-- At a non-zero weight the Higgs sector's mass-weight submodule sits inside that of the
  covariant field algebra. -/
lemma scalarSector_massWeightSubmodule_le {w : ℕ} (hw : w ≠ 0) :
    ScalarSector.massWeightSubmodule w ≤ massWeightSubmodule w := by
  rw [← sectorMassWeight_higgs_eq hw]
  exact GaugeFieldData.sectorMassWeight_le_massWeightSubmodule isMassWeightPoly _ w

/-- At a non-zero weight the fermion sector's mass-weight submodule sits inside that of the
  covariant field algebra. -/
lemma fermionSector_massWeightSubmodule_le {w : ℕ} (hw : w ≠ 0) :
    FermionSector.massWeightSubmodule w ≤ massWeightSubmodule w := by
  rw [← sectorMassWeight_fermion_eq hw]
  exact GaugeFieldData.sectorMassWeight_le_massWeightSubmodule isMassWeightPoly _ w

/-- The span at weight `w` has mass weight `w`, each of its contributions is a
  combination of words of that weight. -/
lemma standardModelSpan_le_massWeightSubmodule (w : ℕ) :
    standardModelSpan w ≤ massWeightSubmodule w := by
  rw [standardModelSpan]
  split_ifs with hw
  · subst hw
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact GaugeSector.lorentzContractionEightSpan_le_massWeightSubmodule.trans
        (gaugeSector_massWeightSubmodule_le (by norm_num))
    · exact ScalarSector.lorentzContractionEightSpan_le_massWeightSubmodule.trans
        (scalarSector_massWeightSubmodule_le (by norm_num))
    · exact FermionSector.kineticSpan_le_massWeightSubmodule.trans
        (fermionSector_massWeightSubmodule_le (by norm_num))
    · exact yukawaSpan_le_inf.trans (le_trans inf_le_left (le_trans inf_le_left
        (GaugeFieldData.sectorMassWeight_le_massWeightSubmodule isMassWeightPoly _ 8)))
  · by_cases hw4 : w = 4
    · subst hw4
      exact (ScalarSector.lorentzContractionLTEightSpan_le_massWeightSubmodule 4).trans
        (scalarSector_massWeightSubmodule_le (by norm_num))
    · rw [ScalarSector.lorentzContractionLTEightSpan, ite_eq_right hw4]
      exact bot_le

/-- The span at weight `w` is fixed pointwise by the gauge and Lorentz groups together, since
  every one of its contributions is a span of invariants. This is the easy direction of
  the classification, and it is also what supplies the stability the reduction asks of its
  target. -/
lemma isFixedBy_standardModelSpan (w : ℕ) :
    IsFixedBy (gaugeLorentzMaps repGaugeGroupI repLorentzGroup) (standardModelSpan w) := by
  rw [standardModelSpan]
  split_ifs with hw
  · exact (GaugeSector.isFixedBy_lorentzContractionEightSpan.sup
      ScalarSector.isFixedBy_lorentzContractionEightSpan).sup
      (FermionSector.isFixedBy_kineticSpan.sup isFixedBy_yukawaSpan)
  · exact ScalarSector.isFixedBy_lorentzContractionLTEightSpan w

/-!

## C. Each sector reduces to the span

-/

/-- The empty sector reduces to the span. Away from weight zero it is trivial, its only word
  being the empty one. -/
lemma reducesInvariantsTo_sectorMassWeight_empty {w : ℕ} (hw : w ≠ 0) :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (fieldData.sectorMassWeight ∅ w) (standardModelSpan w) := by
  rw [GaugeFieldData.sectorMassWeight_empty_of_ne_zero hw]
  exact reducesInvariantsTo_of_le bot_le

/-- The gauge sector reduces to the span, at weight eight to the four Lorentz contractions of
  its four families, two of each spanning, below it to nothing at all. -/
lemma reducesInvariantsTo_sectorMassWeight_gauge {w : ℕ} (hw0 : 0 < w) (hw : w ≤ 8) :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (fieldData.sectorMassWeight {FieldKind.gauge} w) (standardModelSpan w) := by
  refine ReducesInvariantsTo.mono_left ?_ (sectorMassWeight_gauge_le w)
  rcases eq_or_lt_of_le hw with rfl | hw8
  · rw [standardModelSpan_eight]
    exact GaugeSector.reducesInvariantsTo_lorentzContractionEightSpan.mono_right
      (le_sup_of_le_left le_sup_left)
  · exact (ReducesInvariantsTo.ofLorentz (W := ⊥) fun S hS x hx hL => Submodule.mem_sup_right
      (GaugeSector.mem_of_lorentz_invariant_massWeightSubmodule_lt_eight_sup w hw0 hw8 S hS
        hx hL)).mono_right bot_le

/-- The Higgs sector reduces to the span, at weight eight to the two box terms, the kinetic
  term and the quartic potential, at weight four to the Higgs mass term, and elsewhere to
  nothing. -/
lemma reducesInvariantsTo_sectorMassWeight_higgs {w : ℕ} (hw0 : 0 < w) (hw : w ≤ 8) :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (fieldData.sectorMassWeight {FieldKind.scalar} w) (standardModelSpan w) := by
  refine ReducesInvariantsTo.mono_left ?_ (sectorMassWeight_higgs_le w)
  rcases eq_or_lt_of_le hw with rfl | hw8
  · rw [standardModelSpan_eight]
    exact ScalarSector.reducesInvariantsTo_lorentzContractionEightSpan.mono_right
      (le_sup_of_le_left le_sup_right)
  · rw [standardModelSpan, ite_eq_right (by omega)]
    exact ScalarSector.reducesInvariantsTo_lorentzContractionLTEightSpan hw0 hw8

/-- The fermion sector reduces to the span, at weight eight to the ten kinetic terms over the
  nine family pairs and below it to nothing. There is no Dirac mass term. -/
lemma reducesInvariantsTo_sectorMassWeight_fermion {w : ℕ} (hw0 : 0 < w) (hw : w ≤ 8) :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (fieldData.sectorMassWeight {FieldKind.fermion} w) (standardModelSpan w) := by
  refine ReducesInvariantsTo.mono_left ?_ (sectorMassWeight_fermion_le w)
  rcases eq_or_lt_of_le hw with rfl | hw8
  · rw [standardModelSpan_eight]
    exact FermionSector.reducesInvariantsTo_kineticSpan.mono_right
      (le_sup_of_le_right le_sup_left)
  · refine ReducesInvariantsTo.mono_right (W' := ⊥) (fun S hS x hx hinv => ?_) bot_le
    obtain ⟨hSG, hSL⟩ := isStableUnder_gaugeLorentzMaps_iff.1 hS
    obtain ⟨hG, hL⟩ := forall_gaugeLorentzMaps_eq_self_iff.1 hinv
    exact Submodule.mem_sup_right
      (FermionSector.mem_of_invariant_massWeightSubmodule_lt_eight_sup w hw0 hw8 S hSG hSL
        hx hG hL)

/-- The Yukawa sector reduces to the span, at weight eight to the six Yukawa couplings over the
  nine family pairs, below it to nothing. -/
lemma reducesInvariantsTo_sectorMassWeight_higgs_fermion {w : ℕ} (hw : w ≤ 8) :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (fieldData.sectorMassWeight {FieldKind.scalar, FieldKind.fermion} w)
      (standardModelSpan w) := by
  rcases eq_or_lt_of_le hw with rfl | hw8
  · rw [standardModelSpan_eight]
    exact reducesInvariantsTo_sectorMassWeight_higgs_fermion_eight.mono_right
      (le_sup_of_le_right le_sup_right)
  · exact (ReducesInvariantsTo.ofLorentz (W := ⊥) fun S hS x hx hL => Submodule.mem_sup_right
      (mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_lt_eight_sup w hw8 S hS hx
        hL)).mono_right bot_le

/-- The gauge-Higgs sector reduces to nothing, as it carries no Lorentz invariant below weight
  nine. -/
lemma reducesInvariantsTo_sectorMassWeight_gauge_higgs {w : ℕ} (hw : w ≤ 8) :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.scalar} w)
      (standardModelSpan w) :=
  (ReducesInvariantsTo.ofLorentz (W := ⊥) fun S hS x hx hL => Submodule.mem_sup_right
    (mem_of_invariant_sectorMassWeight_gauge_higgs_lt_nine_sup w (by omega) S hS hx
      hL)).mono_right bot_le

/-- The gauge-fermion sector reduces to nothing, as it carries no Lorentz invariant below weight
  nine. -/
lemma reducesInvariantsTo_sectorMassWeight_gauge_fermion {w : ℕ} (hw : w ≤ 8) :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (fieldData.sectorMassWeight {FieldKind.gauge, FieldKind.fermion} w)
      (standardModelSpan w) :=
  (ReducesInvariantsTo.ofLorentz (W := ⊥) fun S hS x hx hL => Submodule.mem_sup_right
    (mem_of_invariant_sectorMassWeight_gauge_fermion_lt_nine_sup w (by omega) S hS hx
      hL)).mono_right bot_le

/-- The mixed sector reduces to nothing, as it is trivial below weight nine. -/
lemma reducesInvariantsTo_sectorMassWeight_mixed {w : ℕ} (hw : w ≤ 8) :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (fieldData.sectorMassWeight
        {FieldKind.gauge, FieldKind.scalar, FieldKind.fermion} w)
      (standardModelSpan w) := fun S _ x hx _ =>
  Submodule.mem_sup_right
    (mem_of_invariant_sectorMassWeight_mixed_lt_nine_sup w (by omega) S hx)

/-!

## D. Joining the eight sectors

-/

/-- Every weight part of every sector is carried into itself by both groups. This is the
  stability the join of the reductions asks of its summands. -/
lemma isStableUnder_sectorMassWeight (T : Finset FieldKind) (w : ℕ) :
    IsStableUnder (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (fieldData.sectorMassWeight T w) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨fun g _ hy => repGauge_mem_sectorMassWeight g hy,
      fun Λ _ hy => repLorentz_mem_sectorMassWeight Λ hy⟩

/-- Every sector reduces to the span, at every weight from one to eight. The three
  constructors of `GaugeFieldData.FieldKind` give eight sets of kinds, and section C treats
  each. -/
lemma reducesInvariantsTo_sectorMassWeight {w : ℕ} (hw0 : 0 < w) (hw : w ≤ 8)
    (T : Finset FieldKind) :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (fieldData.sectorMassWeight T w) (standardModelSpan w) := by
  have hT : T = ∅ ∨ T = {FieldKind.gauge} ∨ T = {FieldKind.scalar}
      ∨ T = {FieldKind.fermion} ∨ T = {FieldKind.gauge, FieldKind.scalar}
      ∨ T = {FieldKind.gauge, FieldKind.fermion}
      ∨ T = {FieldKind.scalar, FieldKind.fermion}
      ∨ T = {FieldKind.gauge, FieldKind.scalar, FieldKind.fermion} := by
    revert T
    decide
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reducesInvariantsTo_sectorMassWeight_empty (by omega)
  · exact reducesInvariantsTo_sectorMassWeight_gauge hw0 hw
  · exact reducesInvariantsTo_sectorMassWeight_higgs hw0 hw
  · exact reducesInvariantsTo_sectorMassWeight_fermion hw0 hw
  · exact reducesInvariantsTo_sectorMassWeight_gauge_higgs hw
  · exact reducesInvariantsTo_sectorMassWeight_gauge_fermion hw
  · exact reducesInvariantsTo_sectorMassWeight_higgs_fermion hw
  · exact reducesInvariantsTo_sectorMassWeight_mixed hw

/-- The whole weight-`w` submodule reduces to the span, for `w` from one to eight. The
  mass-weight submodule is the join of the eight sectors' weight-`w` parts, each of them
  stable under both groups, and `ReducesInvariantsTo` is closed under joins in its source. The
  sectors are taken one at a time, each in turn joining the error term of the others. No
  independence of the sectors is used, and none is available. -/
lemma reducesInvariantsTo_massWeightSubmodule {w : ℕ} (hw0 : 0 < w) (hw : w ≤ 8) :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI repLorentzGroup) (massWeightSubmodule w)
      (standardModelSpan w) := by
  rw [massWeightSubmodule_eq_iSup_sectorMassWeight w]
  exact ReducesInvariantsTo.iSup (fun T => reducesInvariantsTo_sectorMassWeight hw0 hw T)
    (fun T => isStableUnder_sectorMassWeight T w)
    (isFixedBy_standardModelSpan w).isStableUnder

/-!

## E. The classification at mass dimension at most four

-/

/-- The classification of the Standard Model at mass dimension at most four as an
  equivalence, in the shape every sector uses. An element of `massWeightSubmodule w ⊔ S`
  for `0 < w ≤ 8`, with `S` stable under both groups, is fixed by both groups exactly when
  it is a combination of the Standard-Model terms of weight `w` up to a remainder in `S`
  fixed by both groups. Forwards this is the reduction of section D; backwards it uses
  that the span is made of invariants of weight `w`, section B. The weight-four Higgs mass
  term is what makes the span, rather than the bare equation `x = y`, the right form of
  the statement. -/
lemma mem_massWeightSubmodule_sup_and_gauge_lorentz_invariant_iff (w : ℕ) (hw0 : 0 < w)
    (hw : w ≤ 8) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmodule w ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGaugeGroupI g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentzGroup g y = y)
          ∧ x - y ∈ standardModelSpan w :=
  ReducesInvariantsTo.mem_sup_and_gauge_lorentz_invariant_iff
    (reducesInvariantsTo_massWeightSubmodule hw0 hw)
    (standardModelSpan_le_massWeightSubmodule w) (isFixedBy_standardModelSpan w) hS hSL x

/-- The gauge and Lorentz invariants of mass weight `w` for `0 < w ≤ 8`, modulo a
  submodule `S` stable under both groups. Such an invariant is a combination of the
  Standard-Model terms of that weight plus a remainder in `S`, and the remainder is fixed
  by both groups as well, being the difference of two invariants. -/
lemma exists_mem_standardModelSpan_of_gauge_and_lorentz_invariant (w : ℕ)
    (hw0 : 0 < w) (hw : w ≤ 8) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ massWeightSubmodule w ⊔ S)
    (hG : ∀ g : GaugeGroupI, repGaugeGroupI g x = x)
    (hL : ∀ g : SL(2,ℂ), repLorentzGroup g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, repGaugeGroupI g y = y)
      ∧ (∀ g : SL(2,ℂ), repLorentzGroup g y = y)
      ∧ x - y ∈ standardModelSpan w :=
  (mem_massWeightSubmodule_sup_and_gauge_lorentz_invariant_iff w hw0 hw S hS hSL x).1
    ⟨hx, hG, hL⟩

/-- The same classification without the existential. At every weight from one to eight an
  element of `massWeightSubmodule w ⊔ S` fixed by both groups is an element of the
  Standard-Model span joined with `S` fixed by both groups, and conversely. -/
lemma mem_massWeightSubmodule_sup_and_gauge_lorentz_invariant_iff_mem (w : ℕ)
    (hw0 : 0 < w) (hw : w ≤ 8) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmodule w ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x)
      ↔ (x ∈ standardModelSpan w ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x) :=
  ⟨fun hx => ⟨reducesInvariantsTo_massWeightSubmodule hw0 hw S
      (isStableUnder_gaugeLorentzMaps_iff.2 ⟨hS, hSL⟩) x hx.1
      (forall_gaugeLorentzMaps_eq_self_iff.2 hx.2), hx.2⟩,
    fun hx => ⟨sup_le_sup_right (standardModelSpan_le_massWeightSubmodule w) S hx.1, hx.2⟩⟩

/-!

## F. The Standard Model Lagrangian

-/

/-- The invariant content of the Standard Model at mass dimension four. An element of
  `massWeightSubmodule 8 ⊔ S`, for `S` a submodule stable under both groups, is fixed by
  the gauge group and the Lorentz group exactly when it is a combination of
  the four Lorentz contractions of the three `F·F` trace families and of the twice-derived
  hypercharge field strength (`GaugeSector.lorentzContractionEightSpan`), two of each
  spanning by `GaugeSector.lorentzContractionEightSpan_eq` (the kinetic-shape and
  theta-shape contractions of the three gauge groups and two contractions of the
  twice-derived hypercharge field strength, which vanish
  (`mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff_lagrangian_traceFamilies`)),
  the Higgs kinetic term, its quartic potential and its two box terms
  (`ScalarSector.lorentzContractionEightSpan`),
  the kinetic terms of the ten fermion species over the nine family pairs
  (`FermionSector.kineticSpan`),
  and the six Yukawa couplings over the nine family pairs (`yukawaSpan`),
  up to a remainder in `S` fixed by both groups — and nothing else. The generators span;
  they are not shown to be independent, and no quotient by total derivatives is taken. -/
lemma mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff_lagrangian
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmodule 8 ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGaugeGroupI g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentzGroup g y = y)
          ∧ x - y ∈ GaugeSector.lorentzContractionEightSpan
                ⊔ ScalarSector.lorentzContractionEightSpan
              ⊔ (FermionSector.kineticSpan ⊔ yukawaSpan) := by
  rw [← standardModelSpan_eight]
  exact mem_massWeightSubmodule_sup_and_gauge_lorentz_invariant_iff 8 (by norm_num)
    le_rfl S hS hSL x

open RankFour in
/-- The invariant content of the Standard Model at mass dimension four with the gauge
  contribution written through the Lorentz contractions of the three trace families alone,
  the `(0,2)(1,3)` metric contraction and the Levi-Civita contraction of each of `gluonTrace`,
  `wTrace` and `hyperchargeTrace` (`gaugeSector_lorentzContractionEightSpan_eq_traceFamilies`).
  The Higgs, fermion and Yukawa contributions are as in
  `mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff_lagrangian`. The
  generators span; they are not shown to be independent or nonzero. -/
lemma mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff_lagrangian_traceFamilies
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmodule 8 ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGaugeGroupI g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentzGroup g y = y)
          ∧ x - y ∈ (Submodule.span ℂ
                {liftComponents GaugeSector.gluonTrace (contractionTensor 1),
                  liftComponents GaugeSector.gluonTrace (contractionTensor 3)}
              ⊔ (Submodule.span ℂ {liftComponents GaugeSector.wTrace (contractionTensor 1),
                  liftComponents GaugeSector.wTrace (contractionTensor 3)}
                ⊔ Submodule.span ℂ
                  {liftComponents GaugeSector.hyperchargeTrace (contractionTensor 1),
                    liftComponents GaugeSector.hyperchargeTrace (contractionTensor 3)}))
                ⊔ ScalarSector.lorentzContractionEightSpan
              ⊔ (FermionSector.kineticSpan ⊔ yukawaSpan) := by
  rw [← gaugeSector_lorentzContractionEightSpan_eq_traceFamilies]
  exact mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff_lagrangian S hS hSL x

/-- Below mass dimension two there is nothing at all, and at mass dimension two only the
  Higgs mass term. At every weight from one to seven other than four an element of
  `massWeightSubmodule w ⊔ S` fixed by both groups already lies in `S`. -/
lemma mem_of_gauge_and_lorentz_invariant_massWeightSubmodule_sup (w : ℕ) (hw0 : 0 < w)
    (hw : w < 8) (hw4 : w ≠ 4) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ massWeightSubmodule w ⊔ S)
    (hG : ∀ g : GaugeGroupI, repGaugeGroupI g x = x)
    (hL : ∀ g : SL(2,ℂ), repLorentzGroup g x = x) : x ∈ S := by
  have hmem := ((mem_massWeightSubmodule_sup_and_gauge_lorentz_invariant_iff_mem w hw0
    (by omega) S hS hSL x).1 ⟨hx, hG, hL⟩).1
  rwa [standardModelSpan_eq_bot (by omega) hw4, bot_sup_eq] at hmem

/-- At mass dimension two the only invariant of the Standard Model is the Higgs mass term
  `H† H`. An element of `massWeightSubmodule 4 ⊔ S` fixed by both groups is a multiple of
  it up to a remainder in `S` fixed by both groups. -/
lemma mem_massWeightSubmodule_four_sup_and_gauge_lorentz_invariant_iff_higgsMass
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmodule 4 ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGaugeGroupI g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentzGroup g y = y)
          ∧ x - y ∈ ScalarSector.dotSpan 0 0 := by
  rw [← standardModelSpan_four]
  exact mem_massWeightSubmodule_sup_and_gauge_lorentz_invariant_iff 4 (by norm_num)
    (by norm_num) S hS hSL x

end LocalCovFieldAlgebra

end StandardModel
