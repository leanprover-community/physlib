/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsHiggsSector.MassWeight.GaugeWeightDecomposition
public import Physlib.Relativity.LorentzGroup.Invariants.IsSingleLorentz
/-!
# The Higgs invariants below mass weight eight

The Higgs sector is the one sector of the Standard Model already carrying an invariant
below mass weight eight, and it is the most familiar of all: the mass term `H† H`, of mass
weight four.  Everything else below weight eight dies, and for three different reasons.

The odd weights are trivial submodules, every Higgs tower carrying even mass weight.
Weight two dies on hypercharge: a single Higgs symbol carries `6Y = ∓3`, so nothing at that
weight is neutral, which is the gauge classification of
`mem_of_invariant_massWeightSubmodule_two_sup`.  Weight six dies on Lorentz counting.  Its
gauge invariants are the isospin contractions with one derivative, `∂_μ H† H` and
`H† ∂_μ H`, and a single covector index admits no invariant contraction at all — the metric
ties two indices and the Levi-Civita symbol four — which is `IsSingleLorentz`.

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

namespace IsHiggsSector

set_option linter.unusedVariables false

variable {B : Type} [Ring B] [Algebra ℂ B]
  {rep : Representation ℂ GaugeGroupI B}
  {hrep_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B), rep g (b₁ * b₂) = rep g b₁ * rep g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {H : (n : ℕ) → (Fin n → (Fin 1 ⊕ Fin 3)) → Module.Dual ℂ HiggsVec →ₗ[ℂ] B}
  {barH : (n : ℕ) → (Fin n → (Fin 1 ⊕ Fin 3)) →
    Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsHiggsSector B rep hrep_mul repLorentz hrepLorentz_mul H barH massWeightPoly)

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
by it the contraction is a Lorentz vector.  `IsSingleLorentz` says that one covector index
admits no invariant contraction, so a Lorentz invariant of the span together with a stable
submodule already lies in the submodule; the spans are themselves stable, so the two of
them peel off one after the other.

-/

include h in
/-- The isospin contraction of a once-derived Higgs tower against an underived conjugate
  tower, read as a family indexed by its derivative slot, is a Lorentz vector. -/
lemma isSingleLorentz_dotGaugeHiggs_left :
    IsSingleLorentz B repLorentz
      (fun d : Fin 1 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs d ![]) where
  repLorentz_T g l := by
    rw [h.repLorentz_dotGaugeHiggs g l (![] : Fin 0 → Fin 1 ⊕ Fin 3)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_cov_zero, Fin.prod_univ_zero, mul_one]

include h in
/-- The isospin contraction of an underived Higgs tower against a once-derived conjugate
  tower is a Lorentz vector in the same way. -/
lemma isSingleLorentz_dotGaugeHiggs_right :
    IsSingleLorentz B repLorentz
      (fun d : Fin 1 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs ![] d) where
  repLorentz_T g l := by
    rw [h.repLorentz_dotGaugeHiggs g (![] : Fin 0 → Fin 1 ⊕ Fin 3) l, sum_cov_zero]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.prod_univ_zero, one_mul]

/-- The span of the isospin contractions with one derivative on the Higgs tower is the
  span of the components of the corresponding Lorentz vector. -/
lemma dotSpan_one_zero_eq :
    h.dotSpan 1 0 = (h.isSingleLorentz_dotGaugeHiggs_left).span := by
  rw [dotSpan, IsSingleLorentz.span]
  refine iSup_congr fun d => le_antisymm (iSup_le fun d' => ?_) (le_iSup_of_le ![] le_rfl)
  rw [Subsingleton.elim d' (![] : Fin 0 → Fin 1 ⊕ Fin 3)]

/-- The span of the isospin contractions with one derivative on the conjugate tower is the
  span of the components of the corresponding Lorentz vector. -/
lemma dotSpan_zero_one_eq :
    h.dotSpan 0 1 = (h.isSingleLorentz_dotGaugeHiggs_right).span := by
  rw [dotSpan, IsSingleLorentz.span]
  refine le_antisymm (iSup_le fun d => iSup_le fun d' => le_iSup_of_le d' ?_)
    (iSup_le fun d => le_iSup_of_le ![] (le_iSup_of_le d le_rfl))
  rw [Subsingleton.elim d (![] : Fin 0 → Fin 1 ⊕ Fin 3)]

/-- The span of the components of a Lorentz vector is stable under the Lorentz group:
  each component goes to a combination of components. -/
lemma isSingleLorentz_span_stable {T : (Fin 1 → Fin 1 ⊕ Fin 3) → B}
    (hT : IsSingleLorentz B repLorentz T) (g : SL(2,ℂ)) {y : B} (hy : y ∈ hT.span) :
    repLorentz g y ∈ hT.span := by
  obtain ⟨c, rfl⟩ := (hT.mem_span_iff y).1 hy
  rw [map_sum]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [map_smul, hT.repLorentz_T g d]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem a (Submodule.mem_span_singleton_self _)))

/-- A join of two Lorentz-stable submodules is Lorentz stable. -/
lemma stable_sup_lorentz {S₁ S₂ : Submodule ℂ B}
    (h₁ : ∀ g : SL(2,ℂ), ∀ y ∈ S₁, repLorentz g y ∈ S₁)
    (h₂ : ∀ g : SL(2,ℂ), ∀ y ∈ S₂, repLorentz g y ∈ S₂) :
    ∀ g : SL(2,ℂ), ∀ y ∈ S₁ ⊔ S₂, repLorentz g y ∈ S₁ ⊔ S₂ := by
  intro g y hy
  have key : (S₁ ⊔ S₂) ≤ Submodule.comap (repLorentz g) (S₁ ⊔ S₂) :=
    sup_le (fun z hz => Submodule.mem_sup_left (h₁ g z hz))
      (fun z hz => Submodule.mem_sup_right (h₂ g z hz))
  exact key hy

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
    rep g y = y := by
  have key : h.dotSpan n m ≤ LinearMap.ker (rep g - LinearMap.id) := by
    rw [dotSpan]
    refine iSup_le fun d => iSup_le fun d' => ?_
    rw [Submodule.span_singleton_le_iff_mem]
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    exact h.rep_dotGaugeHiggs_invariant g d d'
  have hy' := key hy
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hy'
  exact hy'

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

The gauge classification puts a gauge invariant of mass weight six in the two spans of
once-derived isospin contractions up to a remainder in `S`, so the element itself lies in
those two spans joined with `S`.  Section B then peels them off one after the other, and
since a single covector index carries no invariant contraction nothing is left behind: the
invariant lies in `S`.

-/

include h in
/-- Mass weight six carries no gauge and Lorentz invariant modulo a stable submodule: such
  an invariant of `massWeightSubmodule 6 ⊔ S` lies in `S`. -/
theorem mem_of_gauge_lorentz_invariant_massWeightSubmodule_six_sup (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, rep g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmodule 6 ⊔ S) (hG : ∀ g : GaugeGroupI, rep g x = x)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  obtain ⟨y₀, hy₀S, hy₀G, hxy₀⟩ :=
    h.exists_mem_of_invariant_massWeightSubmodule_six_sup S hS hx hG
  have hxmem : x ∈ (h.dotSpan 1 0 ⊔ h.dotSpan 0 1) ⊔ S := by
    rw [show x = (x - y₀) + y₀ from by abel]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hxy₀) (Submodule.mem_sup_right hy₀S)
  have hstab : ∀ g : SL(2,ℂ), ∀ y ∈ h.dotSpan 0 1 ⊔ S,
      repLorentz g y ∈ h.dotSpan 0 1 ⊔ S := by
    refine stable_sup_lorentz (fun g y hy => ?_) hSL
    rw [h.dotSpan_zero_one_eq] at hy ⊢
    exact isSingleLorentz_span_stable _ g hy
  have hstep : x ∈ (h.isSingleLorentz_dotGaugeHiggs_left).span ⊔ (h.dotSpan 0 1 ⊔ S) := by
    rw [← h.dotSpan_one_zero_eq, ← sup_assoc]
    exact hxmem
  have hnext := (h.isSingleLorentz_dotGaugeHiggs_left).mem_of_invariant_of_mem_sup _
    hstab hstep hL
  rw [h.dotSpan_zero_one_eq] at hnext
  exact (h.isSingleLorentz_dotGaugeHiggs_right).mem_of_invariant_of_mem_sup S hSL hnext hL

/-!

## E. The classification below mass weight eight

The seven weights between zero and eight are now settled: weights one, three, five and
seven are trivial submodules, weight two is killed by hypercharge, weight six by section D,
and weight four leaves the line through the mass term.  `lorentzContractionLTEightSpan`
records that answer as a single submodule depending on the weight, so the statement has the
shape of the weight-eight one and of the other sectors' below-eight ones, whose spans
happen to be trivial.

-/

/-- The gauge and Lorentz invariants of the Higgs sector at mass weight `w` for
  `0 < w < 8`: the line through the Higgs mass term at weight four, and nothing at any
  other weight. -/
noncomputable def lorentzContractionLTEightSpan
    (h : IsHiggsSector B rep hrep_mul repLorentz hrepLorentz_mul H barH massWeightPoly)
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
/-- Below mass weight eight a gauge and Lorentz invariant of `massWeightSubmodule w ⊔ S`
  is an element of the surviving span up to a remainder in `S` fixed by both groups.  The
  four odd weights are trivial submodules, weight two dies on hypercharge, weight six is
  section D, and weight four leaves the Higgs mass term. -/
theorem exists_mem_of_gauge_lorentz_invariant_massWeightSubmodule_lt_eight_sup (w : ℕ)
    (hw0 : 0 < w) (hw : w < 8) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, rep g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmodule w ⊔ S) (hG : ∀ g : GaugeGroupI, rep g x = x)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, rep g y = y) ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
      ∧ x - y ∈ h.lorentzContractionLTEightSpan w := by
  have htriv : ∀ v : ℕ, x ∈ S → ∃ y ∈ S, (∀ g : GaugeGroupI, rep g y = y)
      ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
      ∧ x - y ∈ h.lorentzContractionLTEightSpan v := fun v hxS =>
    ⟨x, hxS, hG, hL, by rw [sub_self]; exact Submodule.zero_mem _⟩
  interval_cases w
  · exact htriv 1 (by rwa [h.massWeightSubmodule_odd_eq_bot 1 (by decide), bot_sup_eq] at hx)
  · exact htriv 2 (h.mem_of_invariant_massWeightSubmodule_two_sup S hS hx hG)
  · exact htriv 3 (by rwa [h.massWeightSubmodule_odd_eq_bot 3 (by decide), bot_sup_eq] at hx)
  · obtain ⟨y, hyS, hyG, hxy⟩ :=
      h.exists_mem_of_invariant_massWeightSubmodule_four_sup S hS hx hG
    have hxy' : x - y ∈ h.lorentzContractionLTEightSpan 4 := by
      rw [lorentzContractionLTEightSpan, if_pos rfl]
      exact hxy
    refine ⟨y, hyS, hyG, fun g => ?_, hxy'⟩
    have hfix : repLorentz g (x - y) = x - y :=
      h.repLorentz_of_mem_dotSpan_zero_zero g hxy
    rw [map_sub, hL g] at hfix
    exact sub_right_injective hfix
  · exact htriv 5 (by rwa [h.massWeightSubmodule_odd_eq_bot 5 (by decide), bot_sup_eq] at hx)
  · exact htriv 6
      (h.mem_of_gauge_lorentz_invariant_massWeightSubmodule_six_sup S hS hSL hx hG hL)
  · exact htriv 7 (by rwa [h.massWeightSubmodule_odd_eq_bot 7 (by decide), bot_sup_eq] at hx)

set_option linter.unusedVariables false in
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
          ∧ x - y ∈ h.lorentzContractionLTEightSpan w := by
  constructor
  · rintro ⟨hxm, hG, hL⟩
    exact h.exists_mem_of_gauge_lorentz_invariant_massWeightSubmodule_lt_eight_sup w hw0 hw
      S hS hSL hxm hG hL
  · rintro ⟨y, hyS, hyG, hyL, hxy⟩
    refine ⟨?_, fun g => ?_, fun g => ?_⟩
    · have hsum : x - y + y ∈ h.massWeightSubmodule w ⊔ S :=
        Submodule.add_mem _
          (Submodule.mem_sup_left (h.lorentzContractionLTEightSpan_le_massWeightSubmodule
            w hxy))
          (Submodule.mem_sup_right hyS)
      simpa using hsum
    · have hstep : rep g (x - y + y) = x - y + y := by
        rw [map_add, h.rep_of_mem_lorentzContractionLTEightSpan w g hxy, hyG g]
      simpa using hstep
    · have hstep : repLorentz g (x - y + y) = x - y + y := by
        rw [map_add, h.repLorentz_of_mem_lorentzContractionLTEightSpan w g hxy, hyL g]
      simpa using hstep

set_option linter.unusedVariables false in
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
          ∧ ∀ g : SL(2,ℂ), repLorentz g x = x) := by
  constructor
  · rintro ⟨hxm, hG, hL⟩
    obtain ⟨y, hyS, -, -, hxy⟩ :=
      h.exists_mem_of_gauge_lorentz_invariant_massWeightSubmodule_lt_eight_sup w hw0 hw S
        hS hSL hxm hG hL
    refine ⟨?_, hG, hL⟩
    have hsum : x - y + y ∈ h.lorentzContractionLTEightSpan w ⊔ S :=
      Submodule.add_mem _ (Submodule.mem_sup_left hxy) (Submodule.mem_sup_right hyS)
    simpa using hsum
  · rintro ⟨hxm, hG, hL⟩
    exact ⟨sup_le_sup_right (h.lorentzContractionLTEightSpan_le_massWeightSubmodule w) S
      hxm, hG, hL⟩

end IsHiggsSector

end StandardModel
