/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.ScalarSector.MassWeight.MassDimLTEight
public import PhyslibAlpha.Relativity.Tensors.ComplexTensor.Metrics.Basic
/-!
# The Higgs invariants of mass weight eight

The gauge and Lorentz invariants of the scalar sector at mass weight eight, the kinetic term,
the two box terms and the quartic potential.

## i. Overview

Mass weight eight is where the scalar sector says what it is for.  The gauge classification
of `reducesInvariantsTo_massWeightSubmodule_eight` leaves four things: the isospin
contractions carrying two derivatives on one tower or one on each, and the square of the
underived contraction.  The Lorentz classification then contracts the derivative indices.

The Higgs is a Lorentz scalar, so the only covector indices at this weight are the two
derivative slots, and two covector indices admit exactly one invariant contraction, the
metric trace, `RankTwo.metric`.  Contracting the mixed family gives the kinetic term
`∂^μ H† ∂_μ H`; contracting the two families carrying both derivatives on one tower gives
`□H† H` and `H† □H`.  The square of the underived contraction has no index to contract and
survives as it stands as the quartic potential `(H† H)²`.

So the four surviving terms are the quartic potential, the kinetic term and the two
box terms, and `lorentzContractionEightSpan` is their span.

Everything is stated modulo a submodule `S` stable under both groups, which is what lets
the other sectors be carried along.

## ii. Key results

- `lorentzContractionEightSpan` : the gauge and Lorentz invariants of the scalar sector at mass
  weight eight, the two box terms `□H† H` and `H† □H`, the kinetic term `∂^μ H† ∂_μ H`, and the
  quartic potential `(H† H)²`.
- `reducesInvariantsTo_lorentzContractionEightSpan` : mass weight eight reduces to that span for
  the gauge and Lorentz groups together.
- `mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff` : the classification at
  mass weight eight as an equivalence.

## iii. Table of contents

- A. The isospin contractions with two derivatives as bi-Lorentz tensors
- B. The metric contraction is fixed by both groups
- C. The invariants of mass weight eight
- D. The span consists of invariants of mass weight eight
- E. The classification

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

## A. The isospin contractions with two derivatives as bi-Lorentz tensors

Two derivatives can sit both on the Higgs tower, both on the conjugate tower, or one on
each.  In each case the isospin contraction is a Lorentz scalar carrying two derivative
slots, so read as a family indexed by those two slots it is a bi-Lorentz tensor, the
Lorentz group moving each slot by the Lorentz matrix of the `SL(2,ℂ)` element.

-/

/-- Both derivatives on the Higgs tower, a bi-Lorentz tensor in the two derivative
  slots. -/
lemma isEquivariant_up_rankTwo_dotGaugeHiggs_left :
    complexLorentzTensor.IsEquivariant (fun _ : Fin 2 => .up) repLorentzGroup
      (liftComponents fun d : Fin 2 → Fin 1 ⊕ Fin 3 => dotGaugeHiggs d ![]) := by
  refine (isEquivariant_liftComponents_up_iff _).2 fun g l => ?_
  rw [repLorentz_dotGaugeHiggs g l (![] : Fin 0 → Fin 1 ⊕ Fin 3)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_pi_fin_zero, Fin.prod_univ_zero, mul_one]

/-- Both derivatives on the conjugate tower, a bi-Lorentz tensor in the same way. -/
lemma isEquivariant_up_rankTwo_dotGaugeHiggs_right :
    complexLorentzTensor.IsEquivariant (fun _ : Fin 2 => .up) repLorentzGroup
      (liftComponents fun d : Fin 2 → Fin 1 ⊕ Fin 3 => dotGaugeHiggs ![] d) := by
  refine (isEquivariant_liftComponents_up_iff _).2 fun g l => ?_
  rw [repLorentz_dotGaugeHiggs g (![] : Fin 0 → Fin 1 ⊕ Fin 3) l, sum_pi_fin_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.prod_univ_zero, one_mul]

/-- One derivative on each tower, the family whose metric contraction is the kinetic
  term. -/
lemma isEquivariant_up_rankTwo_dotGaugeHiggs_mixed :
    complexLorentzTensor.IsEquivariant (fun _ : Fin 2 => .up) repLorentzGroup
      (liftComponents fun d : Fin 2 → Fin 1 ⊕ Fin 3 => dotGaugeHiggs ![d 0] ![d 1]) := by
  refine (isEquivariant_liftComponents_up_iff _).2 fun g l => ?_
  rw [repLorentz_dotGaugeHiggs g ![l 0] ![l 1], sum_pi_fin_one, sum_pi_fin_two]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sum_pi_fin_one]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Fin.prod_univ_one, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]

/-- The span of the isospin contractions with both derivatives on the Higgs tower is the
  span of the components of the corresponding bi-Lorentz tensor. -/
lemma dotSpan_two_zero_eq :
    dotSpan 2 0
      = Submodule.span ℂ (Set.range fun d : Fin 2 → Fin 1 ⊕ Fin 3 => dotGaugeHiggs d ![]) := by
  rw [dotSpan, Submodule.span_range_eq_iSup]
  refine iSup_congr fun d => le_antisymm (iSup_le fun d' => ?_) (le_iSup_of_le ![] le_rfl)
  rw [Subsingleton.elim d' (![] : Fin 0 → Fin 1 ⊕ Fin 3)]

/-- The span of the isospin contractions with both derivatives on the conjugate tower is
  the span of the components of the corresponding bi-Lorentz tensor. -/
lemma dotSpan_zero_two_eq :
    dotSpan 0 2
      = Submodule.span ℂ (Set.range fun d : Fin 2 → Fin 1 ⊕ Fin 3 => dotGaugeHiggs ![] d) := by
  rw [dotSpan, Submodule.span_range_eq_iSup]
  refine le_antisymm (iSup_le fun d => iSup_le fun d' => le_iSup_of_le d' ?_)
    (iSup_le fun d => le_iSup_of_le ![] (le_iSup_of_le d le_rfl))
  rw [Subsingleton.elim d (![] : Fin 0 → Fin 1 ⊕ Fin 3)]

/-- The span of the isospin contractions with one derivative on each tower is the span of
  the components of the mixed bi-Lorentz tensor. -/
lemma dotSpan_one_one_eq :
    dotSpan 1 1
      = Submodule.span ℂ
        (Set.range fun d : Fin 2 → Fin 1 ⊕ Fin 3 => dotGaugeHiggs ![d 0] ![d 1]) := by
  rw [dotSpan, Submodule.span_range_eq_iSup]
  refine le_antisymm (iSup_le fun d => iSup_le fun d' => le_iSup_of_le ![d 0, d' 0] ?_)
    (iSup_le fun d => le_iSup_of_le ![d 0] (le_iSup_of_le ![d 1] le_rfl))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, vecCons_fin_one_eta]
  exact le_rfl

/-!

## B. The metric contraction is fixed by both groups

Two covector indices admit one invariant contraction, the metric trace, and the metric is
carried to itself by a Lorentz matrix — that is the defining property of the Lorentz group,
recorded as `LorentzGroup.sum_minkowskiMatrixZ_mul` — so the trace of a bi-Lorentz family is a
Lorentz invariant, `RankTwo.metric_invariant`.  It is a gauge invariant too whenever
the components are, and the components here are isospin contractions, which the gauge group
fixes.

-/

/-- The metric trace of a family of gauge invariants is a gauge invariant. -/
lemma rep_liftComponents_metric {T : (Fin 2 → Fin 1 ⊕ Fin 3) → fieldData.LocalCovFieldAlgebra}
    (hTG : ∀ (g : GaugeGroupI) (d : Fin 2 → Fin 1 ⊕ Fin 3), repGaugeGroupI g (T d) = T d)
    (g : GaugeGroupI) :
    repGaugeGroupI g (liftComponents T RankTwo.metric) = liftComponents T RankTwo.metric := by
  rw [RankTwo.liftComponents_metric, map_sum]
  exact Finset.sum_congr rfl fun d _ => by rw [map_smul, hTG g d]

/-!

## C. The invariants of mass weight eight

The gauge classification reduces mass weight eight to the three spans of twice-derived
isospin contractions and the line through the square of the underived one.  Each of the
three spans is spanned by a bi-Lorentz tensor and reduces, for the Lorentz group, to the
line through its metric trace (`ComplexVector.reducesInvariantsTo_span_metric`); the
line through the square is fixed and reduces to itself.  What is left is a combination of
the three metric traces and the square: the two box terms, the kinetic term and the quartic
potential.

-/

/-- The gauge and Lorentz invariants of the scalar sector at mass weight eight, the two box
  terms `□H† H` and `H† □H`, the kinetic term `∂^μ H† ∂_μ H`, and the quartic potential
  `(H† H)²`. -/
noncomputable def lorentzContractionEightSpan :
    Submodule ℂ fieldData.LocalCovFieldAlgebra :=
  ℂ ∙ liftComponents (fun d : Fin 2 → Fin 1 ⊕ Fin 3 => dotGaugeHiggs d ![]) RankTwo.metric
    ⊔ (ℂ ∙ liftComponents (fun d : Fin 2 → Fin 1 ⊕ Fin 3 => dotGaugeHiggs ![] d) RankTwo.metric
      ⊔ (ℂ ∙ liftComponents (fun d : Fin 2 → Fin 1 ⊕ Fin 3 => dotGaugeHiggs ![d 0] ![d 1])
          RankTwo.metric
        ⊔ ℂ ∙ (dotGaugeHiggs ![] ![] * dotGaugeHiggs ![] ![])))

/-- The square of the underived isospin contraction is fixed by both groups, being a
  product of two invariants and both representations are multiplicative. -/
lemma invariant_dotGaugeHiggs_sq :
    (∀ g : SL(2,ℂ), repLorentzGroup g (dotGaugeHiggs (![] : Fin 0 → Fin 1 ⊕ Fin 3) ![]
        * dotGaugeHiggs ![] ![])
      = dotGaugeHiggs ![] ![] * dotGaugeHiggs ![] ![])
    ∧ ∀ g : GaugeGroupI, repGaugeGroupI g (dotGaugeHiggs (![] : Fin 0 → Fin 1 ⊕ Fin 3) ![]
        * dotGaugeHiggs ![] ![])
      = dotGaugeHiggs ![] ![] * dotGaugeHiggs ![] ![] :=
  ⟨fun g => by rw [LocalCovFieldAlgebra.repLorentzGroup_mul, repLorentz_dotGaugeHiggs_zero],
    fun g => by rw [LocalCovFieldAlgebra.repGaugeGroupI_mul, rep_dotGaugeHiggs_invariant]⟩

/-!

## D. The span consists of invariants of mass weight eight

The reduction of section E is one-directional, and the converse is easy:
each of the four generators is built from isospin contractions of the right mass weight,
which both groups fix, so the span is made of invariants of mass weight eight already.
The metric trace inherits the mass weight of the components and both invariances from
section B, and the square of the underived contraction is a product of two invariants of
mass weight four.

-/

/-- The metric trace of a family of elements of mass weight eight has mass weight
  eight. -/
lemma liftComponents_metric_mem_massWeightSubmodule
    {T : (Fin 2 → Fin 1 ⊕ Fin 3) → fieldData.LocalCovFieldAlgebra}
    (hT : ∀ d, T d ∈ massWeightSubmodule 8) :
    liftComponents T RankTwo.metric ∈ massWeightSubmodule 8 := by
  rw [RankTwo.liftComponents_metric]
  exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (hT d)

/-- The weight-eight span lies in the mass-weight submodule of weight eight. -/
lemma lorentzContractionEightSpan_le_massWeightSubmodule :
    lorentzContractionEightSpan ≤ massWeightSubmodule 8 := by
  rw [lorentzContractionEightSpan]
  refine sup_le ?_ (sup_le ?_ (sup_le ?_ ?_)) <;>
    rw [Submodule.span_singleton_le_iff_mem]
  · exact liftComponents_metric_mem_massWeightSubmodule fun d =>
      dotGaugeHiggs_mem_massWeightSubmodule d ![]
  · exact liftComponents_metric_mem_massWeightSubmodule fun d =>
      dotGaugeHiggs_mem_massWeightSubmodule ![] d
  · exact liftComponents_metric_mem_massWeightSubmodule fun d =>
      dotGaugeHiggs_mem_massWeightSubmodule ![d 0] ![d 1]
  · exact massWeightSubmodule_mul_le 4 4 (Submodule.mul_mem_mul
      (dotGaugeHiggs_mem_massWeightSubmodule ![] ![])
      (dotGaugeHiggs_mem_massWeightSubmodule ![] ![]))

/-- Every element of the weight-eight span is a gauge invariant. -/
lemma rep_of_mem_lorentzContractionEightSpan (g : GaugeGroupI) {y : fieldData.LocalCovFieldAlgebra}
    (hy : y ∈ lorentzContractionEightSpan) : repGaugeGroupI g y = y := by
  have key : lorentzContractionEightSpan ≤ LinearMap.ker (repGaugeGroupI g - LinearMap.id) := by
    rw [lorentzContractionEightSpan]
    refine sup_le ?_ (sup_le ?_ (sup_le ?_ ?_)) <;>
      rw [Submodule.span_singleton_le_iff_mem] <;>
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    · exact rep_liftComponents_metric (fun k d => rep_dotGaugeHiggs_invariant k d ![]) g
    · exact rep_liftComponents_metric (fun k d => rep_dotGaugeHiggs_invariant k ![] d) g
    · exact rep_liftComponents_metric
        (fun k d => rep_dotGaugeHiggs_invariant k ![d 0] ![d 1]) g
    · exact invariant_dotGaugeHiggs_sq.2 g
  have hy' := key hy
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hy'
  exact hy'

/-- Every element of the weight-eight span is a Lorentz invariant. -/
lemma repLorentz_of_mem_lorentzContractionEightSpan (g : SL(2,ℂ))
    {y : fieldData.LocalCovFieldAlgebra}
    (hy : y ∈ lorentzContractionEightSpan) : repLorentzGroup g y = y := by
  have key : lorentzContractionEightSpan
      ≤ LinearMap.ker (repLorentzGroup g - LinearMap.id) := by
    rw [lorentzContractionEightSpan]
    refine sup_le ?_ (sup_le ?_ (sup_le ?_ ?_)) <;>
      rw [Submodule.span_singleton_le_iff_mem] <;>
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    · exact isEquivariant_up_rankTwo_dotGaugeHiggs_left.rep_map_of_invariant
        RankTwo.metric_invariant g
    · exact isEquivariant_up_rankTwo_dotGaugeHiggs_right.rep_map_of_invariant
        RankTwo.metric_invariant g
    · exact isEquivariant_up_rankTwo_dotGaugeHiggs_mixed.rep_map_of_invariant
        RankTwo.metric_invariant g
    · exact invariant_dotGaugeHiggs_sq.1 g
  have hy' := key hy
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hy'
  exact hy'

/-!

## E. The classification

The gauge classification and the Lorentz classification compose: the first reduces mass
weight eight to the gauge invariants of section C, the second reduces those to the span,
and neither step needs the intermediate span to be fixed by the other group. Section D
says the span is made of invariants of mass weight eight, which turns the reduction into
an equivalence.

-/

/-- The weight-eight span is fixed pointwise by both groups. -/
lemma isFixedBy_lorentzContractionEightSpan :
    IsFixedBy (gaugeLorentzMaps repGaugeGroupI repLorentzGroup) lorentzContractionEightSpan :=
  isFixedBy_gaugeLorentzMaps_iff.2
    ⟨fun g _ hy => rep_of_mem_lorentzContractionEightSpan g hy,
      fun Λ _ hy => repLorentz_of_mem_lorentzContractionEightSpan Λ hy⟩

/-- The scalar sector at mass weight eight reduces, for the gauge and Lorentz groups
  together, to the two box terms, the kinetic term and the quartic potential. The gauge group
  leaves the isospin contractions with two derivatives and the square of the underived one;
  the Lorentz group contracts the two derivative slots of each family with the metric, and
  the square, which carries no index, is fixed. -/
lemma reducesInvariantsTo_lorentzContractionEightSpan :
    ReducesInvariantsTo (gaugeLorentzMaps repGaugeGroupI repLorentzGroup) (massWeightSubmodule 8)
      lorentzContractionEightSpan := by
  have hW : IsStableUnder (fun g : SL(2,ℂ) => repLorentzGroup g) lorentzContractionEightSpan :=
    fun g _ hy => by rw [repLorentz_of_mem_lorentzContractionEightSpan g hy]; exact hy
  have hQ := (isFixedBy_span_singleton (σ := fun g : SL(2,ℂ) => repLorentzGroup g)
    fun g => invariant_dotGaugeHiggs_sq.1 g).isStableUnder
  -- the Lorentz stage: each bi-Lorentz span to the line through its metric trace
  have hlorentz : ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentzGroup g)
      (dotSpan 2 0 ⊔ dotSpan 0 2 ⊔ dotSpan 1 1
        ⊔ ℂ ∙ (dotGaugeHiggs ![] ![] * dotGaugeHiggs ![] ![]))
      lorentzContractionEightSpan := by
    rw [dotSpan_two_zero_eq, dotSpan_zero_two_eq, dotSpan_one_one_eq,
      ← range_liftComponents (S := complexLorentzTensor) (c := fun _ : Fin 2 => .up),
      ← range_liftComponents (S := complexLorentzTensor) (c := fun _ : Fin 2 => .up),
      ← range_liftComponents (S := complexLorentzTensor) (c := fun _ : Fin 2 => .up)]
    refine ((((ComplexVector.reducesInvariantsTo_span_metric
      isEquivariant_up_rankTwo_dotGaugeHiggs_left).mono_right le_sup_left).sup
      ((ComplexVector.reducesInvariantsTo_span_metric
        isEquivariant_up_rankTwo_dotGaugeHiggs_right).mono_right
          (le_sup_of_le_right le_sup_left))
      isEquivariant_up_rankTwo_dotGaugeHiggs_right.isStableUnder_range hW).sup
      ((ComplexVector.reducesInvariantsTo_span_metric
        isEquivariant_up_rankTwo_dotGaugeHiggs_mixed).mono_right
          (le_sup_of_le_right (le_sup_of_le_right le_sup_left)))
      isEquivariant_up_rankTwo_dotGaugeHiggs_mixed.isStableUnder_range hW).sup
      (reducesInvariantsTo_of_le (le_sup_of_le_right (le_sup_of_le_right le_sup_right))) hQ hW
  exact (ReducesInvariantsTo.ofGauge reducesInvariantsTo_massWeightSubmodule_eight).trans
    (ReducesInvariantsTo.ofLorentz hlorentz)

/-- The gauge and Lorentz classification of mass weight eight as an equivalence. An element
  of `massWeightSubmodule 8 ⊔ S` is fixed by both groups exactly when it is a combination of
  the two box terms, the kinetic term and the quartic potential, up to a remainder in `S`
  fixed by both groups. -/
lemma mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGaugeGroupI g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmodule 8 ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGaugeGroupI g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentzGroup g y = y)
          ∧ x - y ∈ lorentzContractionEightSpan :=
  ReducesInvariantsTo.mem_sup_and_gauge_lorentz_invariant_iff
    reducesInvariantsTo_lorentzContractionEightSpan
    lorentzContractionEightSpan_le_massWeightSubmodule isFixedBy_lorentzContractionEightSpan
    hS hSL x

end ScalarSector

end StandardModel
