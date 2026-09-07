/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsCovStandardModel.FermionGaugeSector.MassWeight
public import Physlib.Particles.StandardModel.IsCovStandardModel.GaugeHiggsSector.MassWeight
public import Physlib.Particles.StandardModel.IsCovStandardModel.MixedSector.Basic
public import Physlib.Particles.StandardModel.IsCovStandardModel.YukawaSector.MassDimEight
public import Physlib.Particles.StandardModel.IsFermionSector.MassWeight.MassDimEight
public import Physlib.Particles.StandardModel.IsFermionSector.MassWeight.MassDimLTEight
public import Physlib.Particles.StandardModel.IsGaugeSector.MassWeight.MassDimEight
public import Physlib.Particles.StandardModel.IsHiggsSector.MassWeight.MassDimEight
/-!
# The invariant content of the Standard Model

This is where the classification of the Standard Model closes. A word in the covariant
generators realises a set of generator classes — gauge, Higgs, fermion — and the eight
class sets cut the field algebra into eight sectors, each of which has been classified
separately at every mass weight up to eight, that is at every mass dimension up to four.
This file joins the eight, and the answer is the Standard Model Lagrangian:

**at mass dimension four the gauge- and Lorentz-invariant content of the Standard Model
is the gauge kinetic and theta terms of the three gauge groups, the Higgs kinetic term
with its quartic potential and its two box terms, the kinetic terms of the ten fermion
species over the nine family pairs, and the six Yukawa couplings over the nine family
pairs — and nothing else.**

Below mass dimension four there is a single term, the Higgs mass term `H† H` at mass
weight four; below that, nothing.

The join is the delicate step. `massWeightSubmodule_eq_iSup_sectorMassWeight` writes the
weight-`w` submodule as the join of the eight sectors' weight-`w` parts, but reading off
from an invariant of the whole that its eight pieces are separately invariant would need
the pieces to be determined by their sum — the independence of the sectors, which does
not follow from `IsCovStandardModel` and is deliberately left open in `Sectors.lean`.

Nothing here uses it. The classifications are carried in the shared form `Peels σ V W` of
`Peeling.lean` — every `σ`-invariant of `V ⊔ S` lies in `W ⊔ S`, for every `σ`-stable `S`
— and that relation is closed under joins in its source. Joining the sectors therefore
asks only that each of them be carried into itself by the two groups, which they are
(`repGauge_mem_sectorMassWeight`, `repLorentz_mem_sectorMassWeight`). The eight are taken
one at a time, each in turn joining the error term of the others, and independence never
enters.

Section A collects the surviving spans of the eight sectors into `standardModelSpan`, and
section B checks that it is made of invariants of the right mass weight, which is both the
easy direction of the classification and the stability the peeling asks of its target.
Section C converts each sector's classification into a peeling, section D joins them, and
sections E and F read off the equivalence and its consequence at mass dimension four.

- A. The span of the Standard Model Lagrangian
- B. The span is made of invariants of the right weight
- C. Each sector peels to the span
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

namespace IsCovStandardModel

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  {H : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ HiggsVec →ₗ[ℂ] B}
  {barH : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B}
  {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
  {d : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ DownSinglet →ₗ[ℂ] B}
  {bard : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B}
  {u : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ UpSinglet →ₗ[ℂ] B}
  {baru : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B}
  {Q : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B}
  {barQ : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B}
  {L : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B}
  {barL : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B}
  {e : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B}
  {bare : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B}
  (h : IsCovStandardModel B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
    massWeightPoly H barH F d bard u baru Q barQ L barL e bare)

/-!

## A. The span of the Standard Model Lagrangian

-/

/-- The gauge- and Lorentz-invariant content of the Standard Model at mass weight `w`:
  the join of the surviving spans of the eight sectors. At weight eight it is the gauge
  sector's four Lorentz contractions — the kinetic and theta terms of the three gauge
  groups — together with the Higgs sector's two box terms, kinetic term and quartic
  potential, the fermion sector's ten kinetic terms over the nine family pairs, and the
  six Yukawa couplings over the nine family pairs. Below weight eight only the Higgs
  sector survives, and only at weight four, where it contributes the Higgs mass term. -/
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
  if_pos rfl

/-- At mass weight four the span is the line through the Higgs mass term `H† H`, the one
  invariant of the Standard Model below mass dimension four. -/
lemma standardModelSpan_four : h.standardModelSpan 4 = h.isHiggsSector.dotSpan 0 0 := by
  rw [standardModelSpan, if_neg (by norm_num), IsHiggsSector.lorentzContractionLTEightSpan,
    if_pos rfl]

/-- At every mass weight other than four and eight the span is trivial: apart from the
  Higgs mass term there is no Standard-Model term below mass dimension four. -/
lemma standardModelSpan_eq_bot {w : ℕ} (hw : w ≠ 8) (hw4 : w ≠ 4) :
    h.standardModelSpan w = ⊥ := by
  rw [standardModelSpan, if_neg hw, IsHiggsSector.lorentzContractionLTEightSpan,
    if_neg hw4]

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
    · rw [IsHiggsSector.lorentzContractionLTEightSpan, if_neg hw4]
      exact bot_le

/-- The span at weight `w` is fixed pointwise by the gauge and Lorentz groups together:
  every one of its contributions is a span of invariants. This is the easy direction of
  the classification, and it is also what supplies the stability the peeling asks of its
  target. -/
lemma isFixedBy_standardModelSpan (w : ℕ) :
    IsFixedBy (gaugeLorentzMaps repGauge repLorentz) (h.standardModelSpan w) := by
  have key : ∀ V : Submodule ℂ B, (∀ g : GaugeGroupI, ∀ y ∈ V, repGauge g y = y) →
      (∀ Λ : SL(2,ℂ), ∀ y ∈ V, repLorentz Λ y = y) →
      IsFixedBy (gaugeLorentzMaps repGauge repLorentz) V := by
    rintro V hG hL (g | Λ) y hy
    · exact hG g y hy
    · exact hL Λ y hy
  rw [standardModelSpan]
  split_ifs with hw
  · refine IsFixedBy.sup (IsFixedBy.sup (key _ (fun g y hy => ?_) (fun Λ y hy => ?_))
      (key _ (fun g y hy => ?_) (fun Λ y hy => ?_)))
      (IsFixedBy.sup (key _ (fun g y hy => ?_) (fun Λ y hy => ?_)) ?_)
    · exact (Representation.mem_invariants _ _).1
        (h.isGaugeSector.lorentzContractionEightSpan_le_invariants hy) g
    · exact (Representation.mem_invariants _ _).1
        (h.isGaugeSector.lorentzContractionEightSpan_le_lorentzInvariants hy) Λ
    · exact h.isHiggsSector.rep_of_mem_lorentzContractionEightSpan g hy
    · exact h.isHiggsSector.repLorentz_of_mem_lorentzContractionEightSpan Λ hy
    · exact (Representation.mem_invariants _ _).1
        (h.isFermionSector.kineticSpan_le_invariants hy) g
    · exact (Representation.mem_invariants _ _).1
        (h.isFermionSector.kineticSpan_le_lorentzInvariants hy) Λ
    · exact h.isFixedBy_yukawaSpan
  · exact key _
      (fun g y hy => h.isHiggsSector.rep_of_mem_lorentzContractionLTEightSpan w g hy)
      (fun Λ y hy => h.isHiggsSector.repLorentz_of_mem_lorentzContractionLTEightSpan w Λ hy)

/-- Every element of the span at weight `w` is a gauge invariant. -/
lemma repGauge_of_mem_standardModelSpan (w : ℕ) (g : GaugeGroupI) {y : B}
    (hy : y ∈ h.standardModelSpan w) : repGauge g y = y :=
  h.isFixedBy_standardModelSpan w (Sum.inl g) y hy

/-- Every element of the span at weight `w` is a Lorentz invariant. -/
lemma repLorentz_of_mem_standardModelSpan (w : ℕ) (Λ : SL(2,ℂ)) {y : B}
    (hy : y ∈ h.standardModelSpan w) : repLorentz Λ y = y :=
  h.isFixedBy_standardModelSpan w (Sum.inr Λ) y hy

/-!

## C. Each sector peels to the span

-/

/-- The empty sector peels: away from weight zero it is trivial, its only word being the
  empty one. -/
lemma peels_sectorMassWeight_empty {w : ℕ} (hw : w ≠ 0) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.sectorMassWeight ∅ w)
      (h.standardModelSpan w) := by
  rw [h.sectorMassWeight_empty_of_ne_zero hw]
  exact peels_of_le bot_le

/-- The gauge sector peels: at weight eight to its four Lorentz contractions, below it to
  nothing at all. -/
lemma peels_sectorMassWeight_gauge {w : ℕ} (hw0 : 0 < w) (hw : w ≤ 8) :
    Peels (gaugeLorentzMaps repGauge repLorentz)
      (h.sectorMassWeight {GeneratorClass.gauge} w) (h.standardModelSpan w) := by
  intro S hS x hx hinv
  obtain ⟨hSG, hSL⟩ := isStableUnder_gaugeLorentzMaps_iff.1 hS
  obtain ⟨hG, hL⟩ := forall_gaugeLorentzMaps_eq_self_iff.1 hinv
  have hx' : x ∈ h.isGaugeSector.massWeightSubmodule w ⊔ S :=
    sup_le_sup_right (h.sectorMassWeight_gauge_le w) S hx
  rcases eq_or_lt_of_le hw with rfl | hw8
  · obtain ⟨y, hyS, -, -, hxy⟩ :=
      h.isGaugeSector.exists_mem_of_gauge_and_lorentz_invariant S hSG hSL hx' hG hL
    refine Submodule.mem_sup.2 ⟨x - y, ?_, y, hyS, by abel⟩
    rw [h.standardModelSpan_eight]
    exact Submodule.mem_sup_left (Submodule.mem_sup_left hxy)
  · exact Submodule.mem_sup_right
      (h.isGaugeSector.mem_of_lorentz_invariant_massWeightSubmodule_lt_eight_sup w hw0 hw8
        S hSL hx' hL)

/-- The Higgs sector peels: at weight eight to the two box terms, the kinetic term and the
  quartic potential, at weight four to the Higgs mass term, and elsewhere to nothing. -/
lemma peels_sectorMassWeight_higgs {w : ℕ} (hw0 : 0 < w) (hw : w ≤ 8) :
    Peels (gaugeLorentzMaps repGauge repLorentz)
      (h.sectorMassWeight {GeneratorClass.higgs} w) (h.standardModelSpan w) := by
  intro S hS x hx hinv
  obtain ⟨hSG, hSL⟩ := isStableUnder_gaugeLorentzMaps_iff.1 hS
  obtain ⟨hG, hL⟩ := forall_gaugeLorentzMaps_eq_self_iff.1 hinv
  have hx' : x ∈ h.isHiggsSector.massWeightSubmodule w ⊔ S :=
    sup_le_sup_right (h.sectorMassWeight_higgs_le w) S hx
  rcases eq_or_lt_of_le hw with rfl | hw8
  · obtain ⟨y, hyS, -, -, hxy⟩ :=
      h.isHiggsSector.exists_mem_of_gauge_and_lorentz_invariant S hSG hSL hx' hG hL
    refine Submodule.mem_sup.2 ⟨x - y, ?_, y, hyS, by abel⟩
    rw [h.standardModelSpan_eight]
    exact Submodule.mem_sup_left (Submodule.mem_sup_right hxy)
  · obtain ⟨y, hyS, -, -, hxy⟩ :=
      h.isHiggsSector.exists_mem_of_gauge_lorentz_invariant_massWeightSubmodule_lt_eight_sup
        w hw0 hw8 S hSG hSL hx' hG hL
    refine Submodule.mem_sup.2 ⟨x - y, ?_, y, hyS, by abel⟩
    rwa [standardModelSpan, if_neg (by omega)]

/-- The fermion sector peels: at weight eight to the ten kinetic terms over the nine
  family pairs, below it to nothing — there is no Dirac mass term. -/
lemma peels_sectorMassWeight_fermion {w : ℕ} (hw0 : 0 < w) (hw : w ≤ 8) :
    Peels (gaugeLorentzMaps repGauge repLorentz)
      (h.sectorMassWeight {GeneratorClass.fermion} w) (h.standardModelSpan w) := by
  intro S hS x hx hinv
  obtain ⟨hSG, hSL⟩ := isStableUnder_gaugeLorentzMaps_iff.1 hS
  obtain ⟨hG, hL⟩ := forall_gaugeLorentzMaps_eq_self_iff.1 hinv
  have hx' : x ∈ h.isFermionSector.massWeightSubmodule w ⊔ S :=
    sup_le_sup_right (h.sectorMassWeight_fermion_le w) S hx
  rcases eq_or_lt_of_le hw with rfl | hw8
  · obtain ⟨y, hyS, -, -, hxy⟩ :=
      h.isFermionSector.exists_mem_of_gauge_and_lorentz_invariant S hSG hSL hx' hG hL
    refine Submodule.mem_sup.2 ⟨x - y, ?_, y, hyS, by abel⟩
    rw [h.standardModelSpan_eight]
    exact Submodule.mem_sup_right (Submodule.mem_sup_left hxy)
  · exact Submodule.mem_sup_right
      (h.isFermionSector.mem_of_invariant_massWeightSubmodule_lt_eight_sup w hw0 hw8 S hSG
        hSL hx' hG hL)

/-- The Yukawa sector peels: at weight eight to the six Yukawa couplings over the nine
  family pairs, below it to nothing. -/
lemma peels_sectorMassWeight_higgs_fermion {w : ℕ} (hw : w ≤ 8) :
    Peels (gaugeLorentzMaps repGauge repLorentz)
      (h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} w)
      (h.standardModelSpan w) := by
  intro S hS x hx hinv
  obtain ⟨hSG, hSL⟩ := isStableUnder_gaugeLorentzMaps_iff.1 hS
  obtain ⟨hG, hL⟩ := forall_gaugeLorentzMaps_eq_self_iff.1 hinv
  rcases eq_or_lt_of_le hw with rfl | hw8
  · refine sup_le_sup_right ?_ S
      (h.mem_yukawaSpan_sup_of_gauge_and_lorentz_invariant S hSG hSL hx hG hL)
    rw [h.standardModelSpan_eight]
    exact le_sup_right.trans le_sup_right
  · exact Submodule.mem_sup_right
      (h.mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_lt_eight_sup w hw8 S hSL
        hx hL)

/-- The gauge-Higgs sector peels to nothing: it carries no invariant below weight nine. -/
lemma peels_sectorMassWeight_gauge_higgs {w : ℕ} (hw : w ≤ 8) :
    Peels (gaugeLorentzMaps repGauge repLorentz)
      (h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.higgs} w)
      (h.standardModelSpan w) := by
  intro S hS x hx hinv
  obtain ⟨-, hSL⟩ := isStableUnder_gaugeLorentzMaps_iff.1 hS
  obtain ⟨-, hL⟩ := forall_gaugeLorentzMaps_eq_self_iff.1 hinv
  exact Submodule.mem_sup_right
    (h.mem_of_invariant_sectorMassWeight_gauge_higgs_lt_nine_sup w (by omega) S hSL hx hL)

/-- The gauge-fermion sector peels to nothing: it carries no invariant below weight
  nine. -/
lemma peels_sectorMassWeight_gauge_fermion {w : ℕ} (hw : w ≤ 8) :
    Peels (gaugeLorentzMaps repGauge repLorentz)
      (h.sectorMassWeight {GeneratorClass.gauge, GeneratorClass.fermion} w)
      (h.standardModelSpan w) := by
  intro S hS x hx hinv
  obtain ⟨-, hSL⟩ := isStableUnder_gaugeLorentzMaps_iff.1 hS
  obtain ⟨-, hL⟩ := forall_gaugeLorentzMaps_eq_self_iff.1 hinv
  exact Submodule.mem_sup_right
    (h.mem_of_invariant_sectorMassWeight_gauge_fermion_lt_nine_sup w (by omega) S hSL hx hL)

/-- The mixed sector peels to nothing: it is trivial below weight nine. -/
lemma peels_sectorMassWeight_mixed {w : ℕ} (hw : w ≤ 8) :
    Peels (gaugeLorentzMaps repGauge repLorentz)
      (h.sectorMassWeight
        {GeneratorClass.gauge, GeneratorClass.higgs, GeneratorClass.fermion} w)
      (h.standardModelSpan w) := fun S _ x hx _ =>
  Submodule.mem_sup_right
    (h.mem_of_invariant_sectorMassWeight_mixed_lt_nine_sup w (by omega) S hx)

/-!

## D. Joining the eight sectors

-/

/-- Every weight part of every sector is carried into itself by both groups: the stability
  the join of the peelings asks of its summands. -/
lemma isStableUnder_sectorMassWeight (T : Finset GeneratorClass) (w : ℕ) :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) (h.sectorMassWeight T w) :=
  isStableUnder_gaugeLorentzMaps_iff.2
    ⟨fun g _ hy => h.repGauge_mem_sectorMassWeight g hy,
      fun Λ _ hy => h.repLorentz_mem_sectorMassWeight Λ hy⟩

/-- Every sector peels to the span, at every weight from one to eight. The three
  constructors of `GeneratorClass` give eight class sets, and section C treats each. -/
lemma peels_sectorMassWeight {w : ℕ} (hw0 : 0 < w) (hw : w ≤ 8)
    (T : Finset GeneratorClass) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.sectorMassWeight T w)
      (h.standardModelSpan w) := by
  have hT : T = ∅ ∨ T = {GeneratorClass.gauge} ∨ T = {GeneratorClass.higgs}
      ∨ T = {GeneratorClass.fermion} ∨ T = {GeneratorClass.gauge, GeneratorClass.higgs}
      ∨ T = {GeneratorClass.gauge, GeneratorClass.fermion}
      ∨ T = {GeneratorClass.higgs, GeneratorClass.fermion}
      ∨ T = {GeneratorClass.gauge, GeneratorClass.higgs, GeneratorClass.fermion} := by
    revert T
    decide
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.peels_sectorMassWeight_empty (by omega)
  · exact h.peels_sectorMassWeight_gauge hw0 hw
  · exact h.peels_sectorMassWeight_higgs hw0 hw
  · exact h.peels_sectorMassWeight_fermion hw0 hw
  · exact h.peels_sectorMassWeight_gauge_higgs hw
  · exact h.peels_sectorMassWeight_gauge_fermion hw
  · exact h.peels_sectorMassWeight_higgs_fermion hw
  · exact h.peels_sectorMassWeight_mixed hw

/-- The whole weight-`w` submodule peels to the span, for `w` from one to eight. The
  mass-weight submodule is the join of the eight sectors' weight-`w` parts, each of them
  stable under both groups, and `Peels` is closed under joins in its source: the sectors
  are taken one at a time, each in turn joining the error term of the others. No
  independence of the sectors is used, and none is available. -/
lemma peels_massWeightSubmodule {w : ℕ} (hw0 : 0 < w) (hw : w ≤ 8) :
    Peels (gaugeLorentzMaps repGauge repLorentz) (h.massWeightSubmodule w)
      (h.standardModelSpan w) := by
  rw [h.massWeightSubmodule_eq_iSup_sectorMassWeight w]
  exact Peels.iSup (fun T => h.peels_sectorMassWeight hw0 hw T)
    (fun T => h.isStableUnder_sectorMassWeight T w)
    (h.isFixedBy_standardModelSpan w).isStableUnder

/-!

## E. The classification at mass dimension at most four

-/

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
      ∧ x - y ∈ h.standardModelSpan w := by
  obtain ⟨z, hz, y, hy, rfl⟩ := Submodule.mem_sup.1
    (h.peels_massWeightSubmodule hw0 hw S (isStableUnder_gaugeLorentzMaps_iff.2 ⟨hS, hSL⟩)
      x hx (forall_gaugeLorentzMaps_eq_self_iff.2 ⟨hG, hL⟩))
  refine ⟨y, hy, fun g => ?_, fun g => ?_, by simpa using hz⟩
  · have hstep := hG g
    rw [map_add, h.repGauge_of_mem_standardModelSpan w g hz, add_right_inj] at hstep
    exact hstep
  · have hstep := hL g
    rw [map_add, h.repLorentz_of_mem_standardModelSpan w g hz, add_right_inj] at hstep
    exact hstep

/-- The classification of the Standard Model at mass dimension at most four as an
  equivalence, in the shape every sector uses: an element of `massWeightSubmodule w ⊔ S`
  for `0 < w ≤ 8`, with `S` stable under both groups, is fixed by both groups exactly when
  it is a combination of the Standard-Model terms of weight `w` up to a remainder in `S`
  fixed by both groups. Forwards this is
  `exists_mem_standardModelSpan_of_gauge_and_lorentz_invariant`; backwards it splits `x`
  as `(x - y) + y`, the first summand an invariant of weight `w`
  by section B. The weight-four Higgs mass term is what makes the span, rather than the
  bare equation `x = y`, the right form of the statement. -/
theorem mem_massWeightSubmodule_sup_and_gauge_lorentz_invariant_iff (w : ℕ) (hw0 : 0 < w)
    (hw : w ≤ 8) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmodule w ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x - y ∈ h.standardModelSpan w := by
  refine ⟨fun hx => h.exists_mem_standardModelSpan_of_gauge_and_lorentz_invariant w hw0 hw
    S hS hSL hx.1 hx.2.1 hx.2.2, ?_⟩
  rintro ⟨y, hyS, hyG, hyL, hxy⟩
  refine ⟨?_, fun g => ?_, fun g => ?_⟩
  · have hsum : x - y + y ∈ h.massWeightSubmodule w ⊔ S :=
      Submodule.add_mem _
        (Submodule.mem_sup_left (h.standardModelSpan_le_massWeightSubmodule w hxy))
        (Submodule.mem_sup_right hyS)
    simpa using hsum
  · have hstep : repGauge g (x - y + y) = x - y + y := by
      rw [map_add, h.repGauge_of_mem_standardModelSpan w g hxy, hyG g]
    simpa using hstep
  · have hstep : repLorentz g (x - y + y) = x - y + y := by
      rw [map_add, h.repLorentz_of_mem_standardModelSpan w g hxy, hyL g]
    simpa using hstep

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
          ∧ ∀ g : SL(2,ℂ), repLorentz g x = x) := by
  constructor
  · rintro ⟨hxm, hG, hL⟩
    obtain ⟨y, hyS, -, -, hxy⟩ :=
      h.exists_mem_standardModelSpan_of_gauge_and_lorentz_invariant w hw0 hw S hS hSL hxm hG hL
    refine ⟨?_, hG, hL⟩
    have hsum : x - y + y ∈ h.standardModelSpan w ⊔ S :=
      Submodule.add_mem _ (Submodule.mem_sup_left hxy) (Submodule.mem_sup_right hyS)
    simpa using hsum
  · rintro ⟨hxm, hG, hL⟩
    exact ⟨sup_le_sup_right (h.standardModelSpan_le_massWeightSubmodule w) S hxm, hG, hL⟩

/-!

## F. The Standard Model Lagrangian

-/

/-- The invariant content of the Standard Model at mass dimension four. An element of
  `massWeightSubmodule 8 ⊔ S`, for `S` a submodule stable under both groups, is fixed by
  the gauge group and the Lorentz group exactly when it is a combination of
  the gauge kinetic and theta terms of the three gauge groups
  (`IsGaugeSector.lorentzContractionEightSpan`),
  the Higgs kinetic term, its quartic potential and its two box terms
  (`IsHiggsSector.lorentzContractionEightSpan`),
  the kinetic terms of the ten fermion species over the nine family pairs
  (`IsFermionSector.kineticSpan`),
  and the six Yukawa couplings over the nine family pairs (`yukawaSpan`),
  up to a remainder in `S` fixed by both groups — and nothing else. This is the
  Standard-Model Lagrangian, and the whole of it. -/
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

end IsCovStandardModel

end StandardModel
