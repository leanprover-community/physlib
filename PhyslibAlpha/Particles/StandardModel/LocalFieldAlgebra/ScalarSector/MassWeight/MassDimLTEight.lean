/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.ScalarSector.MassWeight.GaugeWeight
public import PhyslibAlpha.Relativity.Bispinors.ComplexifiedAction
public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.InvariantReduction
/-!
# The Higgs invariants below mass weight eight

The gauge and Lorentz invariants of the scalar sector below mass weight eight, the Higgs mass
term alone.

## i. Overview

The scalar sector is the one sector of the Standard Model already carrying an invariant
below mass weight eight, and it is the most familiar of all: the mass term `H† H`, of mass
weight four.  Everything else below weight eight dies, and for three different reasons.

The odd weights are trivial submodules, every Higgs tower carrying even mass weight.
Weight two dies on hypercharge. A single Higgs symbol carries `6Y = ∓3`, so nothing at that
weight is neutral, which is the gauge classification of
`reducesInvariantsTo_massWeightSubmodule_two`.  Weight six dies on Lorentz counting.  Its
gauge invariants are the isospin contractions with one derivative, `∂_μ H† H` and
`H† ∂_μ H`, and a single covector index admits no invariant contraction at all — the metric
ties two indices and the Levi-Civita symbol four — which is
`complexLorentzTensor.invariants_up_pow_eq_bot_of_odd` at one index.

Weight four survives because the Higgs is a Lorentz scalar.  Its gauge invariants are the
multiples of `H† H`, and with no derivative slot there is no Lorentz index to contract, so
the Lorentz group fixes the contraction outright and the whole line survives.  That is why
the conclusion here is membership in a span rather than in `S`, unlike the gauge and Yukawa
sectors. The surviving span is the Higgs mass term at weight four and trivial at every
other weight below eight.

As in the gauge sector the final statement needs `0 < w` as well as `w < 8`. At `w = 0` the
mass-weight submodule contains the scalars, so `1` is an invariant of weight zero lying in
no `S`.

## ii. Key results

- `isEquivariant_up_rankOne_dotGaugeHiggs_left` and its `_right` companion : the isospin
  contractions with one derivative are Lorentz vectors.
- `lorentzContractionLTEightSpan` : the surviving span below mass weight eight, the line through
  the Higgs mass term at weight four.
- `mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff` : the classification
  below mass weight eight.

## iii. Table of contents

- A. The isospin contractions with one derivative as Lorentz vectors
- B. The underived isospin contraction as a Lorentz scalar
- C. Mass weight six
- D. The classification below mass weight eight

## iv. References

* None.

-/

@[expose] public section

open TensorSpecies

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz ComplexConjugate
open LocalCovFieldAlgebra (repGaugeGroupI repLorentzGroup massWeightPoly)

namespace ScalarSector

/-!

## A. The isospin contractions with one derivative as Lorentz vectors

At mass weight six the gauge classification leaves the isospin contractions carrying one
derivative, on either of the two towers.  The Higgs is a Lorentz scalar, so the only
Lorentz index such a contraction has is that derivative slot, and read as a family indexed
by it the contraction is a Lorentz vector.  `invariants_up_pow_eq_bot_of_odd` says that one index
admits no invariant contraction, so the span of such a family reduces to `⊥`
(`ComplexVector.reducesInvariantsTo_bot_of_odd`); the spans are themselves stable, so
`ReducesInvariantsTo.sup` joins the two.

-/

/-- The isospin contraction of a once-derived Higgs tower against an underived conjugate
  tower, read as a family indexed by its derivative slot, is a Lorentz vector. -/
lemma isEquivariant_up_rankOne_dotGaugeHiggs_left :
    complexLorentzTensor.IsEquivariant (fun _ : Fin 1 => .up) repLorentzGroup
      (liftComponents fun d : Fin 1 → Fin 1 ⊕ Fin 3 => dotGaugeHiggs d ![]) := by
  refine (isEquivariant_liftComponents_up_iff _).2 fun g l => ?_
  rw [repLorentz_dotGaugeHiggs g l (![] : Fin 0 → Fin 1 ⊕ Fin 3)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_pi_fin_zero, Fin.prod_univ_zero, mul_one]

/-- The isospin contraction of an underived Higgs tower against a once-derived conjugate
  tower is a Lorentz vector in the same way. -/
lemma isEquivariant_up_rankOne_dotGaugeHiggs_right :
    complexLorentzTensor.IsEquivariant (fun _ : Fin 1 => .up) repLorentzGroup
      (liftComponents fun d : Fin 1 → Fin 1 ⊕ Fin 3 => dotGaugeHiggs ![] d) := by
  refine (isEquivariant_liftComponents_up_iff _).2 fun g l => ?_
  rw [repLorentz_dotGaugeHiggs g (![] : Fin 0 → Fin 1 ⊕ Fin 3) l, sum_pi_fin_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.prod_univ_zero, one_mul]

/-- The span of the isospin contractions with one derivative on the Higgs tower is the
  span of the components of the corresponding Lorentz vector. -/
lemma dotSpan_one_zero_eq :
    dotSpan 1 0
      = Submodule.span ℂ (Set.range fun d : Fin 1 → Fin 1 ⊕ Fin 3 => dotGaugeHiggs d ![]) := by
  rw [dotSpan, Submodule.span_range_eq_iSup]
  refine iSup_congr fun d => le_antisymm (iSup_le fun d' => ?_) (le_iSup_of_le ![] le_rfl)
  rw [Subsingleton.elim d' (![] : Fin 0 → Fin 1 ⊕ Fin 3)]

/-- The span of the isospin contractions with one derivative on the conjugate tower is the
  span of the components of the corresponding Lorentz vector. -/
lemma dotSpan_zero_one_eq :
    dotSpan 0 1
      = Submodule.span ℂ (Set.range fun d : Fin 1 → Fin 1 ⊕ Fin 3 => dotGaugeHiggs ![] d) := by
  rw [dotSpan, Submodule.span_range_eq_iSup]
  refine le_antisymm (iSup_le fun d => iSup_le fun d' => le_iSup_of_le d' ?_)
    (iSup_le fun d => le_iSup_of_le ![] (le_iSup_of_le d le_rfl))
  rw [Subsingleton.elim d (![] : Fin 0 → Fin 1 ⊕ Fin 3)]

/-!

## B. The underived isospin contraction as a Lorentz scalar

At mass weight four the gauge classification leaves the multiples of `H† H`.  An underived
Higgs symbol carries no derivative slot, so the Lorentz group moves it by an empty product
of Lorentz matrix entries, that is not at all, and the contraction and the whole line
through it are fixed.  Nothing peels off here; the line is the answer.

-/

/-- The underived isospin contraction is a Lorentz scalar. -/
lemma repLorentz_dotGaugeHiggs_zero (g : SL(2,ℂ)) :
    repLorentzGroup g (dotGaugeHiggs (![] : Fin 0 → Fin 1 ⊕ Fin 3) ![])
      = dotGaugeHiggs ![] ![] := by
  rw [repLorentz_dotGaugeHiggs, sum_pi_fin_zero, sum_pi_fin_zero]
  simp

/-- The span of the underived isospin contractions is the line through the mass term. -/
lemma dotSpan_zero_zero_eq :
    dotSpan 0 0 = ℂ ∙ dotGaugeHiggs (![] : Fin 0 → Fin 1 ⊕ Fin 3) ![] := by
  rw [dotSpan]
  refine le_antisymm (iSup_le fun d => iSup_le fun d' => ?_)
    (le_iSup_of_le ![] (le_iSup_of_le ![] le_rfl))
  rw [Subsingleton.elim d (![] : Fin 0 → Fin 1 ⊕ Fin 3),
    Subsingleton.elim d' (![] : Fin 0 → Fin 1 ⊕ Fin 3)]

/-- Every element of the line through the underived isospin contraction is a Lorentz
  invariant. -/
lemma repLorentz_of_mem_dotSpan_zero_zero (g : SL(2,ℂ)) {y : fieldData.LocalCovFieldAlgebra}
    (hy : y ∈ dotSpan 0 0) :
    repLorentzGroup g y = y := by
  rw [dotSpan_zero_zero_eq] at hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rw [map_smul, repLorentz_dotGaugeHiggs_zero]

/-- Every element of a span of isospin contractions is a gauge invariant. -/
lemma rep_of_mem_dotSpan {n m : ℕ} (g : GaugeGroupI) {y : fieldData.LocalCovFieldAlgebra}
    (hy : y ∈ dotSpan n m) :
    repGaugeGroupI g y = y :=
  isFixedBy_dotSpan n m g y hy

/-- The line through the underived isospin contraction lies in mass weight four. -/
lemma dotSpan_zero_zero_le_massWeightSubmodule :
    dotSpan 0 0 ≤ massWeightSubmodule 4 := by
  rw [dotSpan]
  refine iSup_le fun d => iSup_le fun d' => ?_
  rw [Submodule.span_singleton_le_iff_mem]
  exact dotGaugeHiggs_mem_massWeightSubmodule d d'

/-!

## C. Mass weight six

The gauge classification leaves, at mass weight six, the two spans of once-derived isospin
contractions (`reducesInvariantsTo_massWeightSubmodule_six`). Section A reduces each to `⊥`
for the Lorentz group, since a single covector index carries no invariant contraction, and
`ReducesInvariantsTo.sup` joins them: nothing is left behind.

-/

/-- The once-derived isospin contractions reduce to `⊥` for the Lorentz group. Each span is
  spanned by a Lorentz vector, and a single covector index carries no invariant. -/
lemma reducesInvariantsTo_dotSpan_one_zero_sup_zero_one :
    ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentzGroup g) (dotSpan 1 0 ⊔ dotSpan 0 1) ⊥ := by
  rw [dotSpan_one_zero_eq, dotSpan_zero_one_eq,
    ← range_liftComponents (S := complexLorentzTensor) (c := fun _ : Fin 1 => .up),
    ← range_liftComponents (S := complexLorentzTensor) (c := fun _ : Fin 1 => .up)]
  exact (ComplexVector.reducesInvariantsTo_bot_of_odd odd_one
      isEquivariant_up_rankOne_dotGaugeHiggs_left).sup
    (ComplexVector.reducesInvariantsTo_bot_of_odd odd_one
        isEquivariant_up_rankOne_dotGaugeHiggs_right)
    isEquivariant_up_rankOne_dotGaugeHiggs_right.isStableUnder_range isStableUnder_bot

/-!

## D. The classification below mass weight eight

The seven weights between zero and eight are now settled: weights one, three, five and
seven are trivial submodules, weight two is killed by hypercharge, weight six by section C,
and weight four leaves the line through the mass term.  `lorentzContractionLTEightSpan`
records that answer as a single submodule depending on the weight, and
`reducesInvariantsTo_lorentzContractionLTEightSpan` reduces each weight to it, so the
statement has the shape of the weight-eight one and of the other sectors' below-eight ones,
whose spans happen to be trivial.

-/

/-- The gauge and Lorentz invariants of the scalar sector at mass weight `w` for
  `0 < w < 8`, the line through the Higgs mass term at weight four, and nothing at any
  other weight. -/
noncomputable def lorentzContractionLTEightSpan
    (w : ℕ) : Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  if w = 4 then dotSpan 0 0 else ⊥

/-- The surviving span at weight `w` lies in the mass-weight submodule of weight `w`. -/
lemma lorentzContractionLTEightSpan_le_massWeightSubmodule (w : ℕ) :
    lorentzContractionLTEightSpan w ≤ massWeightSubmodule w := by
  rw [lorentzContractionLTEightSpan]
  split_ifs with hw
  · subst hw
    exact dotSpan_zero_zero_le_massWeightSubmodule
  · exact bot_le

/-- Every element of the surviving span is a gauge invariant. -/
lemma rep_of_mem_lorentzContractionLTEightSpan (w : ℕ) (g : GaugeGroupI)
    {y : fieldData.LocalCovFieldAlgebra}
    (hy : y ∈ lorentzContractionLTEightSpan w) : repGaugeGroupI g y = y := by
  rw [lorentzContractionLTEightSpan] at hy
  split_ifs at hy with hw
  · exact rep_of_mem_dotSpan g hy
  · rw [Submodule.mem_bot] at hy
    rw [hy, map_zero]

/-- Every element of the surviving span is a Lorentz invariant. -/
lemma repLorentz_of_mem_lorentzContractionLTEightSpan (w : ℕ) (g : SL(2,ℂ))
    {y : fieldData.LocalCovFieldAlgebra}
    (hy : y ∈ lorentzContractionLTEightSpan w) : repLorentzGroup g y = y := by
  rw [lorentzContractionLTEightSpan] at hy
  split_ifs at hy with hw
  · exact repLorentz_of_mem_dotSpan_zero_zero g hy
  · rw [Submodule.mem_bot] at hy
    rw [hy, map_zero]

/-- The surviving span below weight eight is fixed pointwise by both groups. -/
lemma isFixedBy_lorentzContractionLTEightSpan (w : ℕ) :
    IsFixedBy (gaugeLorentzMaps repGaugeGroupI repLorentzGroup) (lorentzContractionLTEightSpan w) :=
  isFixedBy_gaugeLorentzMaps_iff.2
    ⟨fun g _ hy => rep_of_mem_lorentzContractionLTEightSpan w g hy,
      fun Λ _ hy => repLorentz_of_mem_lorentzContractionLTEightSpan w Λ hy⟩

/-- Below mass weight eight the scalar sector reduces, for the gauge and Lorentz groups
  together, to the surviving span. The four odd weights are trivial submodules, weight two
  dies on hypercharge, weight four leaves the Higgs mass term, which the Lorentz group fixes,
  and at weight six the gauge group leaves the once-derived contractions and the Lorentz
  group nothing. -/
lemma reducesInvariantsTo_lorentzContractionLTEightSpan {w : ℕ} (hw0 : 0 < w) (hw : w < 8) :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI repLorentzGroup) (massWeightSubmodule w)
      (lorentzContractionLTEightSpan w) := by
  have hodd : ∀ n, Odd n → ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI repLorentzGroup)
      (massWeightSubmodule n) (lorentzContractionLTEightSpan n) := fun n hn => by
    rw [massWeightSubmodule_odd_eq_bot n hn]
    exact reducesInvariantsTo_of_le bot_le
  interval_cases w
  · exact hodd 1 (by decide)
  · exact (ReducesInvariantsTo.ofGauge reducesInvariantsTo_massWeightSubmodule_two).mono_right
      bot_le
  · exact hodd 3 (by decide)
  · rw [lorentzContractionLTEightSpan, ite_eq_left rfl]
    exact ReducesInvariantsTo.ofGauge reducesInvariantsTo_massWeightSubmodule_four
  · exact hodd 5 (by decide)
  · refine ((ReducesInvariantsTo.ofGauge reducesInvariantsTo_massWeightSubmodule_six).trans
      (ReducesInvariantsTo.ofLorentz ?_)).mono_right bot_le
    exact reducesInvariantsTo_dotSpan_one_zero_sup_zero_one
  · exact hodd 7 (by decide)

/-- The classification below mass weight eight as an equivalence, in the shape of
  `mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff`. An element of
  `massWeightSubmodule w ⊔ S` for `0 < w < 8` is fixed by both groups exactly when it is an
  element of the surviving span up to a remainder in `S` fixed by both groups.  That span
  is the line through the Higgs mass term at weight four and trivial elsewhere, so at every
  weight but four this says `x = y`, as in the gauge and Yukawa sectors. -/
lemma mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff (w : ℕ)
    (hw0 : 0 < w) (hw : w < 8) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmodule w ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGaugeGroupI g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentzGroup g y = y)
          ∧ x - y ∈ lorentzContractionLTEightSpan w :=
  ReducesInvariantsTo.mem_sup_and_gauge_lorentz_invariant_iff
    (reducesInvariantsTo_lorentzContractionLTEightSpan hw0 hw)
    (lorentzContractionLTEightSpan_le_massWeightSubmodule w)
    (isFixedBy_lorentzContractionLTEightSpan w) hS hSL x

/-- The same classification without the existential. Below mass weight eight an element of
  `massWeightSubmodule w ⊔ S` fixed by both groups is an element of the surviving span
  joined with `S` fixed by both groups, and conversely. -/
lemma mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff_mem (w : ℕ)
    (hw0 : 0 < w) (hw : w < 8) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmodule w ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x)
      ↔ (x ∈ lorentzContractionLTEightSpan w ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x) :=
  ⟨fun hx => ⟨reducesInvariantsTo_lorentzContractionLTEightSpan hw0 hw S
      (isStableUnder_gaugeLorentzMaps_iff.2 ⟨hS, hSL⟩) x hx.1
      (forall_gaugeLorentzMaps_eq_self_iff.2 hx.2), hx.2⟩,
    fun hx => ⟨sup_le_sup_right (lorentzContractionLTEightSpan_le_massWeightSubmodule w) S
      hx.1, hx.2⟩⟩

end ScalarSector

end StandardModel
