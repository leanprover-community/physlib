/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.LocalFieldAlgebra.GaugeSector.MassWeight.Basic
public import PhyslibAlpha.Relativity.Tensors.ComplexTensor.Metrics.Basic
public import PhyslibAlpha.Relativity.Bispinors.ComplexifiedAction
/-!
# The invariants below mass weight eight

The gauge sector carries no gauge and Lorentz invariant between mass weight zero and mass
weight eight.

## i. Overview

Mass weight eight is the first weight of the gauge sector carrying a gauge and Lorentz
invariant. Below it there is nothing. The odd weights and weight two are trivial
submodules, weight four is a single underived field strength and weight six a single
once-derived one, and neither of those two carries an invariant.

Weight four fails on parity of a different kind. An underived field strength carries two
covector indices and one adjoint index, so at a fixed gauge direction it is a bi-Lorentz
tensor, whose only invariant contraction is the metric trace. That trace vanishes, the
metric being symmetric in the pair of indices in which `GaugeSector.F_antisymm` says
the field strength is antisymmetric. Weight six fails on counting. A once-derived field
strength carries three covector indices, and three indices admit no invariant contraction
at all, the metric tying two and the Levi-Civita symbol four.

Neither argument needs the gauge group. The vanishing at weight four holds at every gauge
direction separately, the colour and isospin ones included, so no appeal to
the adjoint classifications `ColourAdj` or `IsospinAdj` is required and Lorentz invariance alone
does the work. What the gauge algebra does contribute is finiteness: a field-strength symbol is
evaluated on a covector of the gauge algebra, and expanding that covector in the dual of
the standard basis writes each derivative submodule inside a finite join of Lorentz
spans, one for each of the twelve basis directions, which is what the peeling arguments
consume.

The final statement `mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff`
needs `0 < w` as well as `w < 8`. At `w = 0` the mass-weight submodule contains the
scalars, so `1` is an invariant of weight zero lying in no `S`.

## ii. Key results

- `mem_of_lorentz_invariant_massWeightSubmodule_four_sup`,
  `mem_of_lorentz_invariant_massWeightSubmodule_six_sup` : mass weights four and six carry no
  Lorentz invariant modulo a Lorentz-stable submodule.
- `mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff` : the classification below
  mass weight eight as an equivalence. An element of `massWeightSubmodule w ⊔ S` for `0 < w < 8`
  is fixed by both groups exactly when it is itself an element of `S` fixed by both groups.

## iii. Table of contents

- A. The symbols on the standard basis of the gauge algebra
- B. The field-strength symbols as Lorentz families
- C. The vanishing of the metric trace of an antisymmetric family
- D. Peeling Lorentz spans off a stable submodule
- E. Mass weight four
- F. Mass weight six
- G. The classification below mass weight eight

## iv. References

* None.

-/

@[expose] public section

open TensorSpecies

namespace StandardModel

open Matrix MatrixGroups Lorentz
open LocalCovFieldAlgebra

namespace GaugeSector

/-!

## A. The symbols on the standard basis of the gauge algebra

The gauge algebra is finite dimensional, so a covector on it is the combination of the
coordinates of the standard basis with its own values on that basis. A field-strength
symbol evaluated on an arbitrary covector is therefore a combination of the twelve
symbols evaluated on those coordinates.

-/

/-- A field-strength symbol lies in the span of the twelve symbols evaluated on the
  coordinates of the standard basis of the gauge algebra. -/
lemma F_mem_iSup_span_coord {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    gaugeFieldStrength l μ ν φ ∈ ⨆ c : Fin 8 ⊕ Fin 3 ⊕ Fin 1,
      ℂ ∙ gaugeFieldStrength l μ ν (GaugeAlgebra.stdBasis.coord c) := by
  have hF : gaugeFieldStrength l μ ν φ
      = ∑ c : Fin 8 ⊕ Fin 3 ⊕ Fin 1,
        φ (GaugeAlgebra.stdBasis c) • gaugeFieldStrength l μ ν (GaugeAlgebra.stdBasis.coord c) := by
    conv_lhs => rw [← GaugeAlgebra.stdBasis.sum_dual_apply_smul_coord φ]
    rw [map_sum]
    exact Finset.sum_congr rfl fun c _ => map_smul _ _ _
  rw [hF]
  refine Submodule.sum_mem _ fun c _ => ?_
  exact Submodule.mem_iSup_of_mem c
    (Submodule.smul_of_tower_mem _ _ (Submodule.mem_span_singleton_self _))

/-!

## B. The field-strength symbols as Lorentz families

An underived field-strength symbol carries two covector indices and nothing else, and a
once-derived one carries three, its derivative slot included. Read as families indexed by
those indices they are a bi-Lorentz and a triple Lorentz tensor, the transformation law
`repLorentz_F` moving every index by the Lorentz matrix of the `SL(2,ℂ)` element.

-/

/-- An underived field-strength symbol, viewed as a family indexed by its two covector
  indices, is a bi-Lorentz tensor. -/
lemma isEquivariant_up_F_underived (φ : Module.Dual ℝ GaugeAlgebra) :
    complexLorentzTensor.IsEquivariant (fun _ : Fin 2 => .up) repLorentzGroup
      (liftComponents fun d : Fin 2 → Fin 1 ⊕ Fin 3 => gaugeFieldStrength ![] (d 0) (d 1) φ) := by
  refine (isEquivariant_liftComponents_up_iff _).2 fun g l => ?_
  rw [repLorentz_F g 0 ![] (l 0) (l 1) φ,
    Finset.sum_eq_single (![] : Fin 0 → Fin 1 ⊕ Fin 3)
      (fun b _ hb => absurd (Subsingleton.elim b ![]) hb)
      (fun hb => absurd (Finset.mem_univ _) hb),
    Fin.prod_univ_zero, one_smul, sum_pi_fin_two]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- A once-derived field-strength symbol, viewed as a family indexed by its derivative
  slot and its two covector indices, is a triple Lorentz tensor. -/
lemma isEquivariant_up_F_deriv_one (φ : Module.Dual ℝ GaugeAlgebra) :
    complexLorentzTensor.IsEquivariant (fun _ : Fin 3 => .up) repLorentzGroup
      (liftComponents fun d : Fin 3 → Fin 1 ⊕ Fin 3 =>
        gaugeFieldStrength ![d 0] (d 1) (d 2) φ) := by
  refine (isEquivariant_liftComponents_up_iff _).2 fun g l => ?_
  rw [repLorentz_F g 1 ![l 0] (l 1) (l 2) φ, sum_pi_fin_one, sum_pi_fin_three]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [smul_smul]
  simp only [Fin.prod_univ_one, Fin.prod_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-!

## C. The vanishing of the metric trace of an antisymmetric family

Two covector indices admit a single invariant contraction, the metric trace, and the
metric is diagonal, so that trace is the sum of the components on the diagonal. A family
antisymmetric in its two indices has every diagonal component equal to its own negative,
hence zero, and the trace vanishes with them.

-/

/-- The metric trace of a bi-Lorentz family antisymmetric in its two indices vanishes, since the
  metric is diagonal, and the diagonal components of such a family are zero. -/
lemma liftComponents_metric_eq_zero_of_antisymm
    {T : (Fin 2 → Fin 1 ⊕ Fin 3) → fieldData.LocalCovFieldAlgebra}
    (hswap : ∀ x y : Fin 1 ⊕ Fin 3, T ![y, x] = - T ![x, y]) :
    liftComponents T RankTwo.metric = 0 := by
  rw [RankTwo.liftComponents_metric]
  refine Finset.sum_eq_zero fun d _ => ?_
  rcases eq_or_ne (d 0) (d 1) with heq | hne
  · have hs := hswap (d 0) (d 1)
    rw [heq] at hs
    have hexp : (![d 1, d 1] : Fin 2 → Fin 1 ⊕ Fin 3) = d := by
      funext i
      fin_cases i <;> simp [heq]
    rw [hexp] at hs
    have htwo : (2 : ℂ) • T d = 0 := by
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.2 hs
    rw [show T d = 0 from by simpa using htwo, smul_zero]
  · rw [show minkowskiMatrixZ (d 0) (d 1) = 0 from by simp [minkowskiMatrixZ, hne]]
    simp

/-!

## D. Peeling Lorentz spans off a stable submodule

Both classifications come in a form relative to a Lorentz-stable submodule `S`. An
invariant of the span of a family together with `S` is a contraction of the family up to
a remainder in `S`. When the contraction vanishes, or when there is none, the span of the
family reduces to `⊥`, and the invariant lies in `S` outright. The spans themselves are
Lorentz stable, so `ReducesInvariantsTo.biSup` combines these reductions over a finite
join of them.

-/

/-- A finite join of the spans of bi-Lorentz families with vanishing metric traces carries
  no Lorentz invariant modulo a Lorentz-stable submodule. A Lorentz invariant of the join
  together with `S` lies in `S`. Each span reduces to the line through its metric
  contraction, which is zero, and `ReducesInvariantsTo.biSup` combines the reductions. -/
lemma mem_of_lorentz_invariant_biSup_rankTwo_span {ι : Type} [DecidableEq ι]
    {T : ι → (Fin 2 → Fin 1 ⊕ Fin 3) → fieldData.LocalCovFieldAlgebra}
    (hT : ∀ i, complexLorentzTensor.IsEquivariant (fun _ : Fin 2 => .up) repLorentzGroup
      (liftComponents (T i)))
    (hzero : ∀ i, liftComponents (T i) RankTwo.metric = 0)
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (s : Finset ι)
    {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ (⨆ i ∈ s, Submodule.span ℂ (Set.range (T i))) ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentzGroup g x = x) : x ∈ S := by
  simp_rw [← range_liftComponents (S := complexLorentzTensor) (c := fun _ : Fin 2 => .up)] at hx
  simpa using ReducesInvariantsTo.biSup
    (fun i => (ComplexVector.reducesInvariantsTo_span_metric (hT i)).mono_right
      (Submodule.span_singleton_eq_bot.2 (hzero i)).le)
    (fun i => (hT i).isStableUnder_range) isStableUnder_bot s S hS x hx hinv

/-- A finite join of the spans of triple Lorentz families carries no Lorentz invariant
  modulo a Lorentz-stable submodule, since three covector indices carry no invariant contraction
  at all, so each span reduces to `⊥`, and `ReducesInvariantsTo.biSup` combines the
  reductions. -/
lemma mem_of_lorentz_invariant_biSup_rankThree_span {ι : Type} [DecidableEq ι]
    {T : ι → (Fin 3 → Fin 1 ⊕ Fin 3) → fieldData.LocalCovFieldAlgebra}
    (hT : ∀ i, complexLorentzTensor.IsEquivariant (fun _ : Fin 3 => .up) repLorentzGroup
      (liftComponents (T i)))
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (s : Finset ι)
    {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ (⨆ i ∈ s, Submodule.span ℂ (Set.range (T i))) ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentzGroup g x = x) : x ∈ S := by
  simp_rw [← range_liftComponents (S := complexLorentzTensor) (c := fun _ : Fin 3 => .up)] at hx
  simpa using ReducesInvariantsTo.biSup
    (fun i => ComplexVector.reducesInvariantsTo_bot_of_odd ⟨1, rfl⟩ (hT i))
    (fun i => (hT i).isStableUnder_range) isStableUnder_bot s S hS x hx hinv

/-!

## E. Mass weight four

Mass weight four is the underived field strength. At each of the twelve directions of the
standard basis of the gauge algebra it is a bi-Lorentz family, whose metric trace vanishes
by the antisymmetry of the field strength in its two covector indices, so section D peels
the twelve spans off and leaves nothing behind. No gauge hypothesis enters: the vanishing
holds at the colour and isospin directions just as at the hypercharge one.

-/

/-- The metric trace of the underived field-strength symbols at a fixed direction of the
  gauge algebra vanishes, the symbol being antisymmetric in its two covector indices. -/
lemma liftComponents_F_underived_metric_eq_zero (φ : Module.Dual ℝ GaugeAlgebra) :
    liftComponents (fun d : Fin 2 → Fin 1 ⊕ Fin 3 => gaugeFieldStrength ![] (d 0) (d 1) φ)
      RankTwo.metric = 0 :=
  liftComponents_metric_eq_zero_of_antisymm fun x y => by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact F_antisymm ![] x y φ

/-- The underived field strengths lie in the join, over the twelve directions of the
  standard basis of the gauge algebra, of the spans of the bi-Lorentz families they
  form. -/
lemma derivSubmodule_zero_le_iSup_span :
    derivSubmodule 0 ≤ ⨆ c : Fin 8 ⊕ Fin 3 ⊕ Fin 1,
      Submodule.span ℂ (Set.range fun d : Fin 2 → Fin 1 ⊕ Fin 3 =>
        gaugeFieldStrength ![] (d 0) (d 1) (GaugeAlgebra.stdBasis.coord c)) := by
  rw [derivSubmodule]
  refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => ?_
  rw [Submodule.span_le]
  rintro x ⟨φ, rfl⟩
  rw [SetLike.mem_coe, Subsingleton.elim l ![]]
  have hle : (⨆ c : Fin 8 ⊕ Fin 3 ⊕ Fin 1,
        ℂ ∙ gaugeFieldStrength ![] μ ν (GaugeAlgebra.stdBasis.coord c))
      ≤ ⨆ c : Fin 8 ⊕ Fin 3 ⊕ Fin 1,
        Submodule.span ℂ (Set.range fun d : Fin 2 → Fin 1 ⊕ Fin 3 =>
        gaugeFieldStrength ![] (d 0) (d 1) (GaugeAlgebra.stdBasis.coord c)) := by
    refine iSup_mono fun c => ?_
    rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span ⟨![μ, ν], by simp⟩
  exact hle (F_mem_iSup_span_coord ![] μ ν φ)

/-- Mass weight four carries no Lorentz invariant modulo a Lorentz-stable submodule. A
  Lorentz invariant of `massWeightSubmodule 4 ⊔ S` lies in `S`. -/
lemma mem_of_lorentz_invariant_massWeightSubmodule_four_sup
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ massWeightSubmodule 4 ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentzGroup g x = x) : x ∈ S := by
  refine mem_of_lorentz_invariant_biSup_rankTwo_span
    (fun c => isEquivariant_up_F_underived (GaugeAlgebra.stdBasis.coord c))
    (fun c => liftComponents_F_underived_metric_eq_zero _) S hSL Finset.univ ?_ hinv
  rw [massWeightSubmodule_four_eq] at hx
  refine sup_le_sup_right ?_ S hx
  simpa using derivSubmodule_zero_le_iSup_span

/-!

## F. Mass weight six

Mass weight six is the once-derived field strength, a triple Lorentz family at each
direction of the standard basis. Three covector indices carry no invariant contraction at
all, so the rank-three classification needs no antisymmetry and no gauge input either. The
twelve spans peel off and the invariant is left in `S`.

-/

/-- The once-derived field strengths lie in the join, over the twelve directions of the
  standard basis of the gauge algebra, of the spans of the triple Lorentz families they
  form. -/
lemma derivSubmodule_one_le_iSup_span :
    derivSubmodule 1 ≤ ⨆ c : Fin 8 ⊕ Fin 3 ⊕ Fin 1,
      Submodule.span ℂ (Set.range fun d : Fin 3 → Fin 1 ⊕ Fin 3 =>
        gaugeFieldStrength ![d 0] (d 1) (d 2) (GaugeAlgebra.stdBasis.coord c)) := by
  rw [derivSubmodule]
  refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => ?_
  rw [Submodule.span_le]
  rintro x ⟨φ, rfl⟩
  rw [SetLike.mem_coe]
  have hle : (⨆ c : Fin 8 ⊕ Fin 3 ⊕ Fin 1,
        ℂ ∙ gaugeFieldStrength l μ ν (GaugeAlgebra.stdBasis.coord c))
      ≤ ⨆ c : Fin 8 ⊕ Fin 3 ⊕ Fin 1,
        Submodule.span ℂ (Set.range fun d : Fin 3 → Fin 1 ⊕ Fin 3 =>
        gaugeFieldStrength ![d 0] (d 1) (d 2) (GaugeAlgebra.stdBasis.coord c)) := by
    refine iSup_mono fun c => ?_
    rw [Submodule.span_singleton_le_iff_mem]
    refine Submodule.subset_span ⟨![l 0, μ, ν], ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, vecCons_fin_one_eta]
  exact hle (F_mem_iSup_span_coord l μ ν φ)

/-- Mass weight six carries no Lorentz invariant modulo a Lorentz-stable submodule. A
  Lorentz invariant of `massWeightSubmodule 6 ⊔ S` lies in `S`. -/
lemma mem_of_lorentz_invariant_massWeightSubmodule_six_sup
    (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ massWeightSubmodule 6 ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentzGroup g x = x) : x ∈ S := by
  refine mem_of_lorentz_invariant_biSup_rankThree_span
    (fun c => isEquivariant_up_F_deriv_one (GaugeAlgebra.stdBasis.coord c))
    S hSL Finset.univ ?_ hinv
  rw [massWeightSubmodule_six_eq] at hx
  refine sup_le_sup_right ?_ S hx
  simpa using derivSubmodule_one_le_iSup_span

/-!

## G. The classification below mass weight eight

The seven weights between zero and eight are now settled. Weights one, two, three, five
and seven are trivial submodules, weight four is section E and weight six section F. So
between weight zero and weight eight there is no invariant beyond what `S` already
supplies, and the equivalence records it.

The lower bound `0 < w` cannot be dropped. Weight zero contains the scalars by
`one_le_massWeightSubmodule_zero`, and `1` is fixed by both groups, the two
representations being multiplicative, without lying in any given `S`.

-/

/-- Between mass weight zero and mass weight eight there is no Lorentz invariant. A
  Lorentz invariant of `massWeightSubmodule w ⊔ S` for `0 < w < 8` lies in `S`. The five
  odd or small weights are trivial submodules, and weights four and six are sections E
  and F. -/
lemma mem_of_lorentz_invariant_massWeightSubmodule_lt_eight_sup (w : ℕ) (hw0 : 0 < w)
    (hw : w < 8) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) {x : fieldData.LocalCovFieldAlgebra}
    (hx : x ∈ massWeightSubmodule w ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentzGroup g x = x) : x ∈ S := by
  interval_cases w
  · rwa [massWeightSubmodule_one_eq, bot_sup_eq] at hx
  · rwa [massWeightSubmodule_two_eq, bot_sup_eq] at hx
  · rwa [massWeightSubmodule_three_eq, bot_sup_eq] at hx
  · exact mem_of_lorentz_invariant_massWeightSubmodule_four_sup S hSL hx hinv
  · rwa [massWeightSubmodule_five_eq, bot_sup_eq] at hx
  · exact mem_of_lorentz_invariant_massWeightSubmodule_six_sup S hSL hx hinv
  · rwa [massWeightSubmodule_seven_eq, bot_sup_eq] at hx

/-- The classification below mass weight eight as an equivalence, in the shape of
  `mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff`. An element of
  `massWeightSubmodule w ⊔ S` for `0 < w < 8` is fixed by both groups exactly when it is
  itself an element of `S` fixed by both groups. The span of invariants that the weight
  eight statement leaves over is here the trivial one, so `x - y` lies in it exactly when
  `x = y`. Gauge stability of `S` is not needed, and neither is gauge invariance of `x`,
  since the forward direction is
  `mem_of_lorentz_invariant_massWeightSubmodule_lt_eight_sup`, which uses the Lorentz
  group alone. -/
lemma mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff (w : ℕ)
    (hw0 : 0 < w) (hw : w < 8) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmodule w ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGaugeGroupI g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentzGroup g y = y)
          ∧ x = y := by
  constructor
  · rintro ⟨hx, hG, hL⟩
    exact ⟨x, mem_of_lorentz_invariant_massWeightSubmodule_lt_eight_sup w hw0 hw S hSL
      hx hL, hG, hL, rfl⟩
  · rintro ⟨y, hyS, hyG, hyL, rfl⟩
    exact ⟨Submodule.mem_sup_right hyS, hyG, hyL⟩

/-- The same classification without the existential. Below mass weight eight an element
  of `massWeightSubmodule w ⊔ S` fixed by both groups is an element of `S` fixed by both
  groups, and conversely. -/
lemma mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff_mem (w : ℕ)
    (hw0 : 0 < w) (hw : w < 8) (S : Submodule ℂ fieldData.LocalCovFieldAlgebra)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup g y ∈ S) (x : fieldData.LocalCovFieldAlgebra) :
    (x ∈ massWeightSubmodule w ⊔ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x)
      ↔ (x ∈ S ∧ (∀ g : GaugeGroupI, repGaugeGroupI g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentzGroup g x = x) := by
  refine ⟨fun hx => ⟨mem_of_lorentz_invariant_massWeightSubmodule_lt_eight_sup w hw0 hw
    S hSL hx.1 hx.2.2, hx.2⟩, fun hx => ⟨Submodule.mem_sup_right hx.1, hx.2⟩⟩

end GaugeSector

end StandardModel
