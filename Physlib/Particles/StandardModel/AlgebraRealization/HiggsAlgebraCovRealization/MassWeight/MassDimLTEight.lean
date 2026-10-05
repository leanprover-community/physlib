/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.AlgebraRealization.HiggsAlgebraCovRealization.MassWeight.GaugeWeightDecomposition
public import Physlib.Relativity.LorentzGroup.Invariants.RankOne
public import Physlib.Particles.StandardModel.InvariantReduction
/-!
# The Higgs invariants below mass weight eight

The Higgs sector is the one sector of the Standard Model already carrying an invariant
below mass weight eight, and it is the most familiar of all: the mass term `H† H`, of mass
weight four.  Everything else below weight eight dies, and for three different reasons.

The odd weights are trivial submodules, every Higgs tower carrying even mass weight.
Weight two dies on hypercharge: a single Higgs symbol carries `6Y = ∓3`, so nothing at that
weight is neutral, which is the gauge classification of
`reducesInvariantsTo_massWeightSubmodule_two`.  Weight six dies on Lorentz counting.  Its
gauge invariants are the isospin contractions with one derivative, `∂_μ H† H` and
`H† ∂_μ H`, and a single covector index admits no invariant contraction at all — the metric
ties two indices and the Levi-Civita symbol four — which is `RankOne`.

Weight four survives because the Higgs is a Lorentz scalar.  Its gauge invariants are the
multiples of `H† H`, and with no derivative slot there is no Lorentz index to contract, so
the Lorentz group fixes the contraction outright and the whole line survives.  That is why
the conclusion here is membership in a span rather than in `S`, unlike the gauge and Yukawa
sectors: the surviving span is the Higgs mass term at weight four and trivial at every
other weight below eight.

- A. Sums over the empty tuple of covector indices
- B. The isospin contractions with one derivative as Lorentz vectors
- C. The underived isospin contraction as a Lorentz scalar
- D. Mass weight six
- E. The classification below mass weight eight

As in the gauge sector the final statement needs `0 < w` as well as `w < 8`: at `w = 0` the
mass-weight submodule contains the scalars, so `1` is an invariant of weight zero lying in
no `S`.

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz ComplexConjugate

namespace HiggsAlgebraCovRealization

set_option linter.unusedVariables false

variable {B : Type} [Ring B] [Algebra ℂ B]
  {rep : Representation ℂ GaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : HiggsAlgebraCovRealization B rep repLorentz massWeightPoly)

/-!

## A. Sums over the empty tuple of covector indices

An underived tower is indexed by the empty tuple of covector indices, of which there is
exactly one, so the Lorentz transformation law of such a tower collapses: the sum over its
derivative indices has a single term and the product of Lorentz matrix entries over its
slots is empty.  Both collapses are this one lemma.

-/

/-- A sum over families of no covector indices is its single term. -/
lemma sum_cov_zero {M : Type*} [AddCommMonoid M] (f : (Fin 0 → Fin 1 ⊕ Fin 3) → M) :
    ∑ d : Fin 0 → Fin 1 ⊕ Fin 3, f d = f ![] :=
  Finset.sum_eq_single (![] : Fin 0 → Fin 1 ⊕ Fin 3)
    (fun b _ hb => absurd (Subsingleton.elim b ![]) hb)
    (fun hb => absurd (Finset.mem_univ _) hb)

/-!

## B. The isospin contractions with one derivative as Lorentz vectors

At mass weight six the gauge classification leaves the isospin contractions carrying one
derivative, on either of the two towers.  The Higgs is a Lorentz scalar, so the only
Lorentz index such a contraction has is that derivative slot, and read as a family indexed
by it the contraction is a Lorentz vector.  `RankOne` says that one covector index
admits no invariant contraction, so the span of such a family reduces to `⊥`
(`RankOne.reducesInvariantsTo_bot`); the spans are themselves stable, so
`ReducesInvariantsTo.sup` joins the two.

-/

include h in
/-- The isospin contraction of a once-derived Higgs tower against an underived conjugate
  tower, read as a family indexed by its derivative slot, is a Lorentz vector. -/
lemma isLorentzCovariant_rankOne_dotGaugeHiggs_left :
    IsLorentzCovariant 1 B repLorentz
      (ofComponents fun d : Fin 1 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs d ![]) := by
  refine (isLorentzCovariant_ofComponents_iff _).2 fun g l => ?_
  rw [h.repLorentz_dotGaugeHiggs g l (![] : Fin 0 → Fin 1 ⊕ Fin 3)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_cov_zero, Fin.prod_univ_zero, mul_one]

include h in
/-- The isospin contraction of an underived Higgs tower against a once-derived conjugate
  tower is a Lorentz vector in the same way. -/
lemma isLorentzCovariant_rankOne_dotGaugeHiggs_right :
    IsLorentzCovariant 1 B repLorentz
      (ofComponents fun d : Fin 1 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs ![] d) := by
  refine (isLorentzCovariant_ofComponents_iff _).2 fun g l => ?_
  rw [h.repLorentz_dotGaugeHiggs g (![] : Fin 0 → Fin 1 ⊕ Fin 3) l, sum_cov_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.prod_univ_zero, one_mul]

/-- The span of the isospin contractions with one derivative on the Higgs tower is the
  span of the components of the corresponding Lorentz vector. -/
lemma dotSpan_one_zero_eq :
    h.dotSpan 1 0
      = Submodule.span ℂ (Set.range fun d : Fin 1 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs d ![]) := by
  rw [dotSpan, Submodule.span_range_eq_iSup]
  refine iSup_congr fun d => le_antisymm (iSup_le fun d' => ?_) (le_iSup_of_le ![] le_rfl)
  rw [Subsingleton.elim d' (![] : Fin 0 → Fin 1 ⊕ Fin 3)]

/-- The span of the isospin contractions with one derivative on the conjugate tower is the
  span of the components of the corresponding Lorentz vector. -/
lemma dotSpan_zero_one_eq :
    h.dotSpan 0 1
      = Submodule.span ℂ (Set.range fun d : Fin 1 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs ![] d) := by
  rw [dotSpan, Submodule.span_range_eq_iSup]
  refine le_antisymm (iSup_le fun d => iSup_le fun d' => le_iSup_of_le d' ?_)
    (iSup_le fun d => le_iSup_of_le ![] (le_iSup_of_le d le_rfl))
  rw [Subsingleton.elim d (![] : Fin 0 → Fin 1 ⊕ Fin 3)]

/-!

## C. The underived isospin contraction as a Lorentz scalar

At mass weight four the gauge classification leaves the multiples of `H† H`.  An underived
Higgs symbol carries no derivative slot, so the Lorentz group moves it by an empty product
of Lorentz matrix entries, that is not at all, and the contraction and the whole line
through it are fixed.  Nothing peels off here; the line is the answer.

-/

include h in
/-- The underived isospin contraction is a Lorentz scalar. -/
lemma repLorentz_dotGaugeHiggs_zero (g : SL(2,ℂ)) :
    repLorentz g (h.dotGaugeHiggs (![] : Fin 0 → Fin 1 ⊕ Fin 3) ![])
      = h.dotGaugeHiggs ![] ![] := by
  rw [h.repLorentz_dotGaugeHiggs, sum_cov_zero, sum_cov_zero]
  simp

/-- The span of the underived isospin contractions is the line through the mass term. -/
lemma dotSpan_zero_zero_eq :
    h.dotSpan 0 0 = ℂ ∙ h.dotGaugeHiggs (![] : Fin 0 → Fin 1 ⊕ Fin 3) ![] := by
  rw [dotSpan]
  refine le_antisymm (iSup_le fun d => iSup_le fun d' => ?_)
    (le_iSup_of_le ![] (le_iSup_of_le ![] le_rfl))
  rw [Subsingleton.elim d (![] : Fin 0 → Fin 1 ⊕ Fin 3),
    Subsingleton.elim d' (![] : Fin 0 → Fin 1 ⊕ Fin 3)]

include h in
/-- Every element of the line through the underived isospin contraction is a Lorentz
  invariant. -/
lemma repLorentz_of_mem_dotSpan_zero_zero (g : SL(2,ℂ)) {y : B} (hy : y ∈ h.dotSpan 0 0) :
    repLorentz g y = y := by
  rw [h.dotSpan_zero_zero_eq] at hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rw [map_smul, h.repLorentz_dotGaugeHiggs_zero]

include h in
/-- Every element of a span of isospin contractions is a gauge invariant. -/
lemma rep_of_mem_dotSpan {n m : ℕ} (g : GaugeGroupI) {y : B} (hy : y ∈ h.dotSpan n m) :
    rep g y = y :=
  h.isFixedBy_dotSpan n m g y hy

include h in
/-- The line through the underived isospin contraction lies in mass weight four. -/
lemma dotSpan_zero_zero_le_massWeightSubmodule :
    h.dotSpan 0 0 ≤ h.massWeightSubmodule 4 := by
  rw [dotSpan]
  refine iSup_le fun d => iSup_le fun d' => ?_
  rw [Submodule.span_singleton_le_iff_mem]
  exact h.dotGaugeHiggs_mem_massWeightSubmodule d d'

/-!

## D. Mass weight six

The gauge classification leaves, at mass weight six, the two spans of once-derived isospin
contractions (`reducesInvariantsTo_massWeightSubmodule_six`). Section B reduces each to `⊥`
for the Lorentz group, since a single covector index carries no invariant contraction, and
`ReducesInvariantsTo.sup` joins them: nothing is left behind.

-/

include h in
/-- The once-derived isospin contractions reduce to `⊥` for the Lorentz group: each span is
  spanned by a Lorentz vector, and a single covector index carries no invariant. -/
lemma reducesInvariantsTo_dotSpan_one_zero_sup_zero_one :
    ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentz g) (h.dotSpan 1 0 ⊔ h.dotSpan 0 1) ⊥ := by
  rw [h.dotSpan_one_zero_eq, h.dotSpan_zero_one_eq, ← range_ofComponents, ← range_ofComponents]
  exact (RankOne.reducesInvariantsTo_bot h.isLorentzCovariant_rankOne_dotGaugeHiggs_left).sup
    (RankOne.reducesInvariantsTo_bot h.isLorentzCovariant_rankOne_dotGaugeHiggs_right)
    h.isLorentzCovariant_rankOne_dotGaugeHiggs_right.isStableUnder_range isStableUnder_bot

/-!

## E. The classification below mass weight eight

The seven weights between zero and eight are now settled: weights one, three, five and
seven are trivial submodules, weight two is killed by hypercharge, weight six by section D,
and weight four leaves the line through the mass term.  `lorentzContractionLTEightSpan`
records that answer as a single submodule depending on the weight, and
`reducesInvariantsTo_lorentzContractionLTEightSpan` reduces each weight to it, so the
statement has the shape of the weight-eight one and of the other sectors' below-eight ones,
whose spans happen to be trivial.

-/

/-- The gauge and Lorentz invariants of the Higgs sector at mass weight `w` for
  `0 < w < 8`: the line through the Higgs mass term at weight four, and nothing at any
  other weight. -/
noncomputable def lorentzContractionLTEightSpan
    (h : HiggsAlgebraCovRealization B rep repLorentz massWeightPoly)
    (w : ℕ) : Submodule ℂ B :=
  if w = 4 then h.dotSpan 0 0 else ⊥

include h in
/-- The surviving span at weight `w` lies in the mass-weight submodule of weight `w`. -/
lemma lorentzContractionLTEightSpan_le_massWeightSubmodule (w : ℕ) :
    h.lorentzContractionLTEightSpan w ≤ h.massWeightSubmodule w := by
  rw [lorentzContractionLTEightSpan]
  split_ifs with hw
  · subst hw
    exact h.dotSpan_zero_zero_le_massWeightSubmodule
  · exact bot_le

include h in
/-- Every element of the surviving span is a gauge invariant. -/
lemma rep_of_mem_lorentzContractionLTEightSpan (w : ℕ) (g : GaugeGroupI) {y : B}
    (hy : y ∈ h.lorentzContractionLTEightSpan w) : rep g y = y := by
  rw [lorentzContractionLTEightSpan] at hy
  split_ifs at hy with hw
  · exact h.rep_of_mem_dotSpan g hy
  · rw [Submodule.mem_bot] at hy
    rw [hy, map_zero]

include h in
/-- Every element of the surviving span is a Lorentz invariant. -/
lemma repLorentz_of_mem_lorentzContractionLTEightSpan (w : ℕ) (g : SL(2,ℂ)) {y : B}
    (hy : y ∈ h.lorentzContractionLTEightSpan w) : repLorentz g y = y := by
  rw [lorentzContractionLTEightSpan] at hy
  split_ifs at hy with hw
  · exact h.repLorentz_of_mem_dotSpan_zero_zero g hy
  · rw [Submodule.mem_bot] at hy
    rw [hy, map_zero]

include h in
/-- The surviving span below weight eight is fixed pointwise by both groups. -/
lemma isFixedBy_lorentzContractionLTEightSpan (w : ℕ) :
    IsFixedBy (gaugeLorentzMaps rep repLorentz) (h.lorentzContractionLTEightSpan w) :=
  isFixedBy_gaugeLorentzMaps_iff.2
    ⟨fun g _ hy => h.rep_of_mem_lorentzContractionLTEightSpan w g hy,
      fun Λ _ hy => h.repLorentz_of_mem_lorentzContractionLTEightSpan w Λ hy⟩

include h in
/-- Below mass weight eight the Higgs sector reduces, for the gauge and Lorentz groups
  together, to the surviving span. The four odd weights are trivial submodules, weight two
  dies on hypercharge, weight four leaves the Higgs mass term, which the Lorentz group fixes,
  and at weight six the gauge group leaves the once-derived contractions and the Lorentz
  group nothing. -/
lemma reducesInvariantsTo_lorentzContractionLTEightSpan {w : ℕ} (hw0 : 0 < w) (hw : w < 8) :
    ReducesInvariantsTo (gaugeLorentzMaps rep repLorentz) (h.massWeightSubmodule w)
      (h.lorentzContractionLTEightSpan w) := by
  have hodd : ∀ n, Odd n → ReducesInvariantsTo (gaugeLorentzMaps rep repLorentz)
      (h.massWeightSubmodule n) (h.lorentzContractionLTEightSpan n) := fun n hn => by
    rw [h.massWeightSubmodule_odd_eq_bot n hn]
    exact reducesInvariantsTo_of_le bot_le
  interval_cases w
  · exact hodd 1 (by decide)
  · exact (ReducesInvariantsTo.ofGauge h.reducesInvariantsTo_massWeightSubmodule_two).mono_right
      bot_le
  · exact hodd 3 (by decide)
  · rw [lorentzContractionLTEightSpan, ite_eq_left rfl]
    exact ReducesInvariantsTo.ofGauge h.reducesInvariantsTo_massWeightSubmodule_four
  · exact hodd 5 (by decide)
  · refine ((ReducesInvariantsTo.ofGauge h.reducesInvariantsTo_massWeightSubmodule_six).trans
      (ReducesInvariantsTo.ofLorentz ?_)).mono_right bot_le
    exact h.reducesInvariantsTo_dotSpan_one_zero_sup_zero_one
  · exact hodd 7 (by decide)

include h in
/-- The classification below mass weight eight as an equivalence, in the shape of
  `mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff`: an element of
  `massWeightSubmodule w ⊔ S` for `0 < w < 8` is fixed by both groups exactly when it is an
  element of the surviving span up to a remainder in `S` fixed by both groups.  That span
  is the line through the Higgs mass term at weight four and trivial elsewhere, so at every
  weight but four this says `x = y`, as in the gauge and Yukawa sectors. -/
theorem mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff (w : ℕ)
    (hw0 : 0 < w) (hw : w < 8) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, rep g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmodule w ⊔ S ∧ (∀ g : GaugeGroupI, rep g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, rep g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x - y ∈ h.lorentzContractionLTEightSpan w :=
  ReducesInvariantsTo.mem_sup_and_gauge_lorentz_invariant_iff
    (h.reducesInvariantsTo_lorentzContractionLTEightSpan hw0 hw)
    (h.lorentzContractionLTEightSpan_le_massWeightSubmodule w)
    (h.isFixedBy_lorentzContractionLTEightSpan w) hS hSL x

include h in
/-- The same classification without the existential: below mass weight eight an element of
  `massWeightSubmodule w ⊔ S` fixed by both groups is an element of the surviving span
  joined with `S` fixed by both groups, and conversely. -/
theorem mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff_mem (w : ℕ)
    (hw0 : 0 < w) (hw : w < 8) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, rep g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmodule w ⊔ S ∧ (∀ g : GaugeGroupI, rep g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ (x ∈ h.lorentzContractionLTEightSpan w ⊔ S ∧ (∀ g : GaugeGroupI, rep g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentz g x = x) :=
  ⟨fun hx => ⟨h.reducesInvariantsTo_lorentzContractionLTEightSpan hw0 hw S
      (isStableUnder_gaugeLorentzMaps_iff.2 ⟨hS, hSL⟩) x hx.1
      (forall_gaugeLorentzMaps_eq_self_iff.2 hx.2), hx.2⟩,
    fun hx => ⟨sup_le_sup_right (h.lorentzContractionLTEightSpan_le_massWeightSubmodule w) S
      hx.1, hx.2⟩⟩

end HiggsAlgebraCovRealization

end StandardModel
