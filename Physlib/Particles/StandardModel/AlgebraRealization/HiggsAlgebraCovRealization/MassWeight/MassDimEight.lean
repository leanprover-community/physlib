/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.AlgebraRealization.HiggsAlgebraCovRealization.MassWeight.MassDimLTEight
public import Physlib.Relativity.LorentzGroup.Invariants.RankTwo
/-!
# The Higgs invariants of mass weight eight

Mass weight eight is where the Higgs sector says what it is for.  The gauge classification
of `reducesInvariantsTo_massWeightSubmodule_eight` leaves four things: the isospin
contractions carrying two derivatives on one tower or one on each, and the square of the
underived contraction.  The Lorentz classification then contracts the derivative indices.

The Higgs is a Lorentz scalar, so the only covector indices at this weight are the two
derivative slots, and two covector indices admit exactly one invariant contraction, the
metric trace, which is `RankTwo`.  Contracting the mixed family gives the kinetic term
`∂^μ H† ∂_μ H`; contracting the two families carrying both derivatives on one tower gives
`□H† H` and `H† □H`.  The square of the underived contraction has no index to contract and
survives as it stands: it is the quartic potential `(H† H)²`.

So the four surviving terms are the quartic potential, the kinetic term and the two
box terms, and `lorentzContractionEightSpan` is their span.

- A. Sums over pairs of covector indices
- B. The isospin contractions with two derivatives as bi-Lorentz tensors
- C. The metric contraction is fixed by both groups
- D. The invariants of mass weight eight
- E. The span consists of invariants of mass weight eight
- F. The classification

Everything is stated modulo a submodule `S` stable under both groups, which is what lets
the other sectors be carried along.

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

## A. Sums over pairs of covector indices

A bi-Lorentz family is indexed by a pair of covector indices, while the transformation law
of the Higgs tower presents its sums one derivative slot at a time.  `sum_cov_one` and,
for a pair, `Lorentz.sum_pi_fin_two` turn a sum over tuples into an iterated sum and back.

-/

/-- A sum over families of one covector index is a single sum. -/
lemma sum_cov_one {M : Type*} [AddCommMonoid M] (f : (Fin 1 → Fin 1 ⊕ Fin 3) → M) :
    ∑ d : Fin 1 → Fin 1 ⊕ Fin 3, f d = ∑ x : Fin 1 ⊕ Fin 3, f ![x] :=
  Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 1 ⊕ Fin 3)) _ _ fun d => by
    congr 1
    funext i
    fin_cases i
    simp

/-- A family of one covector index is the tuple of its own entry. -/
lemma etaExpand_cov_one (l : Fin 1 → Fin 1 ⊕ Fin 3) : ![l 0] = l := by
  funext i
  fin_cases i
  rfl

/-!

## B. The isospin contractions with two derivatives as bi-Lorentz tensors

Two derivatives can sit both on the Higgs tower, both on the conjugate tower, or one on
each.  In each case the isospin contraction is a Lorentz scalar carrying two derivative
slots, so read as a family indexed by those two slots it is a bi-Lorentz tensor, the
Lorentz group moving each slot by the Lorentz matrix of the `SL(2,ℂ)` element.

-/

include h in
/-- Both derivatives on the Higgs tower: a bi-Lorentz tensor in the two derivative
  slots. -/
lemma isLorentzCovariant_rankTwo_dotGaugeHiggs_left :
    IsLorentzCovariant 2 B repLorentz
      (ofComponents fun d : Fin 2 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs d ![]) := by
  refine (isLorentzCovariant_ofComponents_iff _).2 fun g l => ?_
  rw [h.repLorentz_dotGaugeHiggs g l (![] : Fin 0 → Fin 1 ⊕ Fin 3)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_cov_zero, Fin.prod_univ_zero, mul_one]

include h in
/-- Both derivatives on the conjugate tower: a bi-Lorentz tensor in the same way. -/
lemma isLorentzCovariant_rankTwo_dotGaugeHiggs_right :
    IsLorentzCovariant 2 B repLorentz
      (ofComponents fun d : Fin 2 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs ![] d) := by
  refine (isLorentzCovariant_ofComponents_iff _).2 fun g l => ?_
  rw [h.repLorentz_dotGaugeHiggs g (![] : Fin 0 → Fin 1 ⊕ Fin 3) l, sum_cov_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.prod_univ_zero, one_mul]

include h in
/-- One derivative on each tower: the family whose metric contraction is the kinetic
  term. -/
lemma isLorentzCovariant_rankTwo_dotGaugeHiggs_mixed :
    IsLorentzCovariant 2 B repLorentz
      (ofComponents fun d : Fin 2 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs ![d 0] ![d 1]) := by
  refine (isLorentzCovariant_ofComponents_iff _).2 fun g l => ?_
  rw [h.repLorentz_dotGaugeHiggs g ![l 0] ![l 1], sum_cov_one, sum_pi_fin_two]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sum_cov_one]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Fin.prod_univ_one, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]

/-- The span of the isospin contractions with both derivatives on the Higgs tower is the
  span of the components of the corresponding bi-Lorentz tensor. -/
lemma dotSpan_two_zero_eq :
    h.dotSpan 2 0
      = Submodule.span ℂ (Set.range fun d : Fin 2 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs d ![]) := by
  rw [dotSpan, Submodule.span_range_eq_iSup]
  refine iSup_congr fun d => le_antisymm (iSup_le fun d' => ?_) (le_iSup_of_le ![] le_rfl)
  rw [Subsingleton.elim d' (![] : Fin 0 → Fin 1 ⊕ Fin 3)]

/-- The span of the isospin contractions with both derivatives on the conjugate tower is
  the span of the components of the corresponding bi-Lorentz tensor. -/
lemma dotSpan_zero_two_eq :
    h.dotSpan 0 2
      = Submodule.span ℂ (Set.range fun d : Fin 2 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs ![] d) := by
  rw [dotSpan, Submodule.span_range_eq_iSup]
  refine le_antisymm (iSup_le fun d => iSup_le fun d' => le_iSup_of_le d' ?_)
    (iSup_le fun d => le_iSup_of_le ![] (le_iSup_of_le d le_rfl))
  rw [Subsingleton.elim d (![] : Fin 0 → Fin 1 ⊕ Fin 3)]

/-- The span of the isospin contractions with one derivative on each tower is the span of
  the components of the mixed bi-Lorentz tensor. -/
lemma dotSpan_one_one_eq :
    h.dotSpan 1 1
      = Submodule.span ℂ
        (Set.range fun d : Fin 2 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs ![d 0] ![d 1]) := by
  rw [dotSpan, Submodule.span_range_eq_iSup]
  refine le_antisymm (iSup_le fun d => iSup_le fun d' => le_iSup_of_le ![d 0, d' 0] ?_)
    (iSup_le fun d => le_iSup_of_le ![d 0] (le_iSup_of_le ![d 1] le_rfl))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, etaExpand_cov_one]
  exact le_rfl

/-!

## C. The metric contraction is fixed by both groups

Two covector indices admit one invariant contraction, the metric trace, and the metric is
carried to itself by a Lorentz matrix — that is the defining property of the Lorentz group,
recorded as `LorentzGroup.sum_minkowskiMatrixZ_mul` — so the trace of a bi-Lorentz family is a
Lorentz invariant, `RankTwo.metric_invariant`.  It is a gauge invariant too whenever
the components are, and the components here are isospin contractions, which the gauge group
fixes.

-/

/-- The metric trace of a family of gauge invariants is a gauge invariant. -/
lemma rep_ofComponents_metric {T : (Fin 2 → Fin 1 ⊕ Fin 3) → B}
    (hTG : ∀ (g : GaugeGroupI) (d : Fin 2 → Fin 1 ⊕ Fin 3), rep g (T d) = T d)
    (g : GaugeGroupI) :
    rep g (ofComponents T RankTwo.metric) = ofComponents T RankTwo.metric := by
  rw [RankTwo.ofComponents_metric, map_sum]
  exact Finset.sum_congr rfl fun d _ => by rw [map_smul, hTG g d]

/-!

## D. The invariants of mass weight eight

The gauge classification reduces mass weight eight to the three spans of twice-derived
isospin contractions and the line through the square of the underived one.  Each of the
three spans is spanned by a bi-Lorentz tensor and reduces, for the Lorentz group, to the
line through its metric trace (`RankTwo.reducesInvariantsTo_span_metric`); the
line through the square is fixed and reduces to itself.  What is left is a combination of
the three metric traces and the square: the two box terms, the kinetic term and the quartic
potential.

-/

/-- The gauge and Lorentz invariants of the Higgs sector at mass weight eight: the two box
  terms `□H† H` and `H† □H`, the kinetic term `∂^μ H† ∂_μ H`, and the quartic potential
  `(H† H)²`. -/
noncomputable def lorentzContractionEightSpan
    (h : HiggsAlgebraCovRealization B rep repLorentz massWeightPoly) :
    Submodule ℂ B :=
  ℂ ∙ ofComponents (fun d : Fin 2 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs d ![]) RankTwo.metric
    ⊔ (ℂ ∙ ofComponents (fun d : Fin 2 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs ![] d) RankTwo.metric
      ⊔ (ℂ ∙ ofComponents (fun d : Fin 2 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs ![d 0] ![d 1])
          RankTwo.metric
        ⊔ ℂ ∙ (h.dotGaugeHiggs ![] ![] * h.dotGaugeHiggs ![] ![])))

include h in
/-- The square of the underived isospin contraction is fixed by both groups: it is a
  product of two invariants and both representations are multiplicative. -/
lemma invariant_dotGaugeHiggs_sq :
    (∀ g : SL(2,ℂ), repLorentz g (h.dotGaugeHiggs (![] : Fin 0 → Fin 1 ⊕ Fin 3) ![]
        * h.dotGaugeHiggs ![] ![])
      = h.dotGaugeHiggs ![] ![] * h.dotGaugeHiggs ![] ![])
    ∧ ∀ g : GaugeGroupI, rep g (h.dotGaugeHiggs (![] : Fin 0 → Fin 1 ⊕ Fin 3) ![]
        * h.dotGaugeHiggs ![] ![])
      = h.dotGaugeHiggs ![] ![] * h.dotGaugeHiggs ![] ![] :=
  ⟨fun g => by rw [h.repLorentz_mul, h.repLorentz_dotGaugeHiggs_zero],
    fun g => by rw [h.rep_mul, h.rep_dotGaugeHiggs_invariant]⟩

/-!

## E. The span consists of invariants of mass weight eight

The reduction of section F is one-directional, and the converse is easy:
each of the four generators is built from isospin contractions of the right mass weight,
which both groups fix, so the span is made of invariants of mass weight eight already.
The metric trace inherits the mass weight of the components and both invariances from
section C, and the square of the underived contraction is a product of two invariants of
mass weight four.

-/

include h in
/-- The metric trace of a family of elements of mass weight eight has mass weight
  eight. -/
lemma ofComponents_metric_mem_massWeightSubmodule {T : (Fin 2 → Fin 1 ⊕ Fin 3) → B}
    (hT : ∀ d, T d ∈ h.massWeightSubmodule 8) :
    ofComponents T RankTwo.metric ∈ h.massWeightSubmodule 8 := by
  rw [RankTwo.ofComponents_metric]
  exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (hT d)

include h in
/-- The weight-eight span lies in the mass-weight submodule of weight eight. -/
lemma lorentzContractionEightSpan_le_massWeightSubmodule :
    h.lorentzContractionEightSpan ≤ h.massWeightSubmodule 8 := by
  rw [lorentzContractionEightSpan]
  refine sup_le ?_ (sup_le ?_ (sup_le ?_ ?_)) <;>
    rw [Submodule.span_singleton_le_iff_mem]
  · exact h.ofComponents_metric_mem_massWeightSubmodule fun d =>
      h.dotGaugeHiggs_mem_massWeightSubmodule d ![]
  · exact h.ofComponents_metric_mem_massWeightSubmodule fun d =>
      h.dotGaugeHiggs_mem_massWeightSubmodule ![] d
  · exact h.ofComponents_metric_mem_massWeightSubmodule fun d =>
      h.dotGaugeHiggs_mem_massWeightSubmodule ![d 0] ![d 1]
  · exact h.massWeightSubmodule_mul_le 4 4 (Submodule.mul_mem_mul
      (h.dotGaugeHiggs_mem_massWeightSubmodule ![] ![])
      (h.dotGaugeHiggs_mem_massWeightSubmodule ![] ![]))

include h in
/-- Every element of the weight-eight span is a gauge invariant. -/
lemma rep_of_mem_lorentzContractionEightSpan (g : GaugeGroupI) {y : B}
    (hy : y ∈ h.lorentzContractionEightSpan) : rep g y = y := by
  have key : h.lorentzContractionEightSpan ≤ LinearMap.ker (rep g - LinearMap.id) := by
    rw [lorentzContractionEightSpan]
    refine sup_le ?_ (sup_le ?_ (sup_le ?_ ?_)) <;>
      rw [Submodule.span_singleton_le_iff_mem] <;>
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    · exact rep_ofComponents_metric (fun k d => h.rep_dotGaugeHiggs_invariant k d ![]) g
    · exact rep_ofComponents_metric (fun k d => h.rep_dotGaugeHiggs_invariant k ![] d) g
    · exact rep_ofComponents_metric
        (fun k d => h.rep_dotGaugeHiggs_invariant k ![d 0] ![d 1]) g
    · exact h.invariant_dotGaugeHiggs_sq.2 g
  have hy' := key hy
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hy'
  exact hy'

include h in
/-- Every element of the weight-eight span is a Lorentz invariant. -/
lemma repLorentz_of_mem_lorentzContractionEightSpan (g : SL(2,ℂ)) {y : B}
    (hy : y ∈ h.lorentzContractionEightSpan) : repLorentz g y = y := by
  have key : h.lorentzContractionEightSpan
      ≤ LinearMap.ker (repLorentz g - LinearMap.id) := by
    rw [lorentzContractionEightSpan]
    refine sup_le ?_ (sup_le ?_ (sup_le ?_ ?_)) <;>
      rw [Submodule.span_singleton_le_iff_mem] <;>
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    · exact h.isLorentzCovariant_rankTwo_dotGaugeHiggs_left.rep_map_of_invariant
        RankTwo.metric_invariant g
    · exact h.isLorentzCovariant_rankTwo_dotGaugeHiggs_right.rep_map_of_invariant
        RankTwo.metric_invariant g
    · exact h.isLorentzCovariant_rankTwo_dotGaugeHiggs_mixed.rep_map_of_invariant
        RankTwo.metric_invariant g
    · exact h.invariant_dotGaugeHiggs_sq.1 g
  have hy' := key hy
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hy'
  exact hy'

/-!

## F. The classification

The gauge classification and the Lorentz classification compose: the first reduces mass
weight eight to the gauge invariants of section D, the second reduces those to the span,
and neither step needs the intermediate span to be fixed by the other group. Section E
says the span is made of invariants of mass weight eight, which turns the reduction into
an equivalence.

-/

include h in
/-- The weight-eight span is fixed pointwise by both groups. -/
lemma isFixedBy_lorentzContractionEightSpan :
    IsFixedBy (gaugeLorentzMaps rep repLorentz) h.lorentzContractionEightSpan :=
  isFixedBy_gaugeLorentzMaps_iff.2
    ⟨fun g _ hy => h.rep_of_mem_lorentzContractionEightSpan g hy,
      fun Λ _ hy => h.repLorentz_of_mem_lorentzContractionEightSpan Λ hy⟩

include h in
/-- The Higgs sector at mass weight eight reduces, for the gauge and Lorentz groups
  together, to the two box terms, the kinetic term and the quartic potential. The gauge group
  leaves the isospin contractions with two derivatives and the square of the underived one;
  the Lorentz group contracts the two derivative slots of each family with the metric, and
  the square, which carries no index, is fixed. -/
lemma reducesInvariantsTo_lorentzContractionEightSpan :
    ReducesInvariantsTo (gaugeLorentzMaps rep repLorentz) (h.massWeightSubmodule 8)
      h.lorentzContractionEightSpan := by
  have hW : IsStableUnder (fun g : SL(2,ℂ) => repLorentz g) h.lorentzContractionEightSpan :=
    fun g _ hy => by rw [h.repLorentz_of_mem_lorentzContractionEightSpan g hy]; exact hy
  have hQ := (isFixedBy_span_singleton (σ := fun g : SL(2,ℂ) => repLorentz g)
    fun g => h.invariant_dotGaugeHiggs_sq.1 g).isStableUnder
  -- the Lorentz stage: each bi-Lorentz span to the line through its metric trace
  have hlorentz : ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentz g)
      (h.dotSpan 2 0 ⊔ h.dotSpan 0 2 ⊔ h.dotSpan 1 1
        ⊔ ℂ ∙ (h.dotGaugeHiggs ![] ![] * h.dotGaugeHiggs ![] ![]))
      h.lorentzContractionEightSpan := by
    rw [h.dotSpan_two_zero_eq, h.dotSpan_zero_two_eq, h.dotSpan_one_one_eq,
      ← range_ofComponents, ← range_ofComponents, ← range_ofComponents]
    refine ((((RankTwo.reducesInvariantsTo_span_metric
      h.isLorentzCovariant_rankTwo_dotGaugeHiggs_left).mono_right le_sup_left).sup
      ((RankTwo.reducesInvariantsTo_span_metric
        h.isLorentzCovariant_rankTwo_dotGaugeHiggs_right).mono_right
          (le_sup_of_le_right le_sup_left))
      h.isLorentzCovariant_rankTwo_dotGaugeHiggs_right.isStableUnder_range hW).sup
      ((RankTwo.reducesInvariantsTo_span_metric
        h.isLorentzCovariant_rankTwo_dotGaugeHiggs_mixed).mono_right
          (le_sup_of_le_right (le_sup_of_le_right le_sup_left)))
      h.isLorentzCovariant_rankTwo_dotGaugeHiggs_mixed.isStableUnder_range hW).sup
      (reducesInvariantsTo_of_le (le_sup_of_le_right (le_sup_of_le_right le_sup_right))) hQ hW
  exact (ReducesInvariantsTo.ofGauge h.reducesInvariantsTo_massWeightSubmodule_eight).trans
    (ReducesInvariantsTo.ofLorentz hlorentz)

include h in
/-- The gauge and Lorentz classification of mass weight eight as an equivalence: an element
  of `massWeightSubmodule 8 ⊔ S` is fixed by both groups exactly when it is a combination of
  the two box terms, the kinetic term and the quartic potential, up to a remainder in `S`
  fixed by both groups. -/
theorem mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff
    (S : Submodule ℂ B) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, rep g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmodule 8 ⊔ S ∧ (∀ g : GaugeGroupI, rep g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, rep g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x - y ∈ h.lorentzContractionEightSpan :=
  ReducesInvariantsTo.mem_sup_and_gauge_lorentz_invariant_iff
    h.reducesInvariantsTo_lorentzContractionEightSpan
    h.lorentzContractionEightSpan_le_massWeightSubmodule h.isFixedBy_lorentzContractionEightSpan
    hS hSL x

end HiggsAlgebraCovRealization

end StandardModel
