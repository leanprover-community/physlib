/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsHiggsSector.MassWeight.MassDimLTEight
public import Physlib.Relativity.LorentzGroup.Invariants.IsBiLorentz
/-!
# The Higgs invariants of mass weight eight

Mass weight eight is where the Higgs sector says what it is for.  The gauge classification
of `exists_mem_of_invariant_massWeightSubmodule_eight_sup` leaves four things: the isospin
contractions carrying two derivatives on one tower or one on each, and the square of the
underived contraction.  The Lorentz classification then contracts the derivative indices.

The Higgs is a Lorentz scalar, so the only covector indices at this weight are the two
derivative slots, and two covector indices admit exactly one invariant contraction, the
metric trace, which is `IsBiLorentz`.  Contracting the mixed family gives the kinetic term
`∂^μ H† ∂_μ H`; contracting the two families carrying both derivatives on one tower gives
`□H† H` and `H† □H`.  The square of the underived contraction has no index to contract and
survives as it stands: it is the quartic potential `(H† H)²`.

So the four surviving terms are the quartic potential, the kinetic term and the two
box terms, and `lorentzContractionEightSpan` is their span.

- A. Sums over pairs of covector indices
- B. The isospin contractions with two derivatives as bi-Lorentz tensors
- C. The metric contraction is fixed by both groups
- D. Peeling a bi-Lorentz span off a stable submodule
- E. The invariants of mass weight eight
- F. The span consists of invariants of mass weight eight
- G. The classification as an equivalence

Everything is stated modulo a submodule `S` stable under both groups, which is what lets
the other sectors be carried along.

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

## A. Sums over pairs of covector indices

A bi-Lorentz family is indexed by a pair of covector indices, while the transformation law
of the Higgs tower presents its sums one derivative slot at a time.  These two lemmas turn
a sum over pairs into an iterated sum and back.

-/

/-- A sum over families of one covector index is a single sum. -/
lemma sum_cov_one {M : Type*} [AddCommMonoid M] (f : (Fin 1 → Fin 1 ⊕ Fin 3) → M) :
    ∑ d : Fin 1 → Fin 1 ⊕ Fin 3, f d = ∑ x : Fin 1 ⊕ Fin 3, f ![x] :=
  Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 1 ⊕ Fin 3)) _ _ fun d => by
    congr 1
    funext i
    fin_cases i
    simp

/-- A sum over families of two covector indices is a double sum. -/
lemma sum_cov_two {M : Type*} [AddCommMonoid M] (f : (Fin 2 → Fin 1 ⊕ Fin 3) → M) :
    ∑ d : Fin 2 → Fin 1 ⊕ Fin 3, f d
      = ∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3, f ![x, y] := by
  rw [show (∑ d : Fin 2 → Fin 1 ⊕ Fin 3, f d)
      = ∑ p : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3), f ![p.1, p.2] from
      Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 1 ⊕ Fin 3) _ _ fun d => by
        congr 1
        funext i
        fin_cases i <;> simp,
    Fintype.sum_prod_type]

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
lemma isBiLorentz_dotGaugeHiggs_left :
    IsBiLorentz B repLorentz
      (fun d : Fin 2 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs d ![]) where
  repLorentz_T g l := by
    rw [h.repLorentz_dotGaugeHiggs g l (![] : Fin 0 → Fin 1 ⊕ Fin 3)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_cov_zero, Fin.prod_univ_zero, mul_one]

include h in
/-- Both derivatives on the conjugate tower: a bi-Lorentz tensor in the same way. -/
lemma isBiLorentz_dotGaugeHiggs_right :
    IsBiLorentz B repLorentz
      (fun d : Fin 2 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs ![] d) where
  repLorentz_T g l := by
    rw [h.repLorentz_dotGaugeHiggs g (![] : Fin 0 → Fin 1 ⊕ Fin 3) l, sum_cov_zero]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.prod_univ_zero, one_mul]

include h in
/-- One derivative on each tower: the family whose metric contraction is the kinetic
  term. -/
lemma isBiLorentz_dotGaugeHiggs_mixed :
    IsBiLorentz B repLorentz
      (fun d : Fin 2 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs ![d 0] ![d 1]) where
  repLorentz_T g l := by
    rw [h.repLorentz_dotGaugeHiggs g ![l 0] ![l 1], sum_cov_one, sum_cov_two]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [sum_cov_one]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Fin.prod_univ_one, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]

/-- The span of the isospin contractions with both derivatives on the Higgs tower is the
  span of the components of the corresponding bi-Lorentz tensor. -/
lemma dotSpan_two_zero_eq :
    h.dotSpan 2 0 = (h.isBiLorentz_dotGaugeHiggs_left).span := by
  rw [dotSpan, IsBiLorentz.span]
  refine iSup_congr fun d => le_antisymm (iSup_le fun d' => ?_) (le_iSup_of_le ![] le_rfl)
  rw [Subsingleton.elim d' (![] : Fin 0 → Fin 1 ⊕ Fin 3)]

/-- The span of the isospin contractions with both derivatives on the conjugate tower is
  the span of the components of the corresponding bi-Lorentz tensor. -/
lemma dotSpan_zero_two_eq :
    h.dotSpan 0 2 = (h.isBiLorentz_dotGaugeHiggs_right).span := by
  rw [dotSpan, IsBiLorentz.span]
  refine le_antisymm (iSup_le fun d => iSup_le fun d' => le_iSup_of_le d' ?_)
    (iSup_le fun d => le_iSup_of_le ![] (le_iSup_of_le d le_rfl))
  rw [Subsingleton.elim d (![] : Fin 0 → Fin 1 ⊕ Fin 3)]

/-- The span of the isospin contractions with one derivative on each tower is the span of
  the components of the mixed bi-Lorentz tensor. -/
lemma dotSpan_one_one_eq :
    h.dotSpan 1 1 = (h.isBiLorentz_dotGaugeHiggs_mixed).span := by
  rw [dotSpan, IsBiLorentz.span]
  refine le_antisymm (iSup_le fun d => iSup_le fun d' => le_iSup_of_le ![d 0, d' 0] ?_)
    (iSup_le fun d => le_iSup_of_le ![d 0] (le_iSup_of_le ![d 1] le_rfl))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, etaExpand_cov_one]
  exact le_rfl

/-!

## C. The metric contraction is fixed by both groups

Two covector indices admit one invariant contraction, the metric trace, and the metric is
carried to itself by a Lorentz matrix — that is the defining property of the Lorentz group,
recorded as `sum_minkowskiMatrixZ_mul` — so the trace of a bi-Lorentz family is a Lorentz
invariant.  It is a gauge invariant too whenever the components are, and the components
here are isospin contractions, which the gauge group fixes.

-/

/-- The metric trace of a bi-Lorentz family is a Lorentz invariant. -/
lemma repLorentz_metricContraction {T : (Fin 2 → Fin 1 ⊕ Fin 3) → B}
    (hT : IsBiLorentz B repLorentz T) (g : SL(2,ℂ)) :
    repLorentz g (IsBiLorentz.metricContraction (T := T))
      = IsBiLorentz.metricContraction (T := T) := by
  rw [IsBiLorentz.metricContraction, map_sum]
  have step : ∀ d : Fin 2 → Fin 1 ⊕ Fin 3,
      repLorentz g (((minkowskiMatrixZ (d 0) (d 1) : ℤ) : ℂ) • T d)
        = ∑ a : Fin 2 → Fin 1 ⊕ Fin 3,
          (((minkowskiMatrixZ (d 0) (d 1) : ℤ) : ℂ)
            * ∏ i : Fin 2, (((SL2C.toLorentzGroup g).1 (a i) (d i) : ℝ) : ℂ)) • T a := by
    intro d
    rw [map_smul, hT.repLorentz_T g d, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_smul]
  rw [Finset.sum_congr rfl fun d _ => step d, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rw [sum_cov_two]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact IsQuadLorentz.sum_minkowskiMatrixZ_mul (SL2C.toLorentzGroup g) (a 0) (a 1)

/-- The metric trace of a family of gauge invariants is a gauge invariant. -/
lemma rep_metricContraction {T : (Fin 2 → Fin 1 ⊕ Fin 3) → B}
    (hTG : ∀ (g : GaugeGroupI) (d : Fin 2 → Fin 1 ⊕ Fin 3), rep g (T d) = T d)
    (g : GaugeGroupI) :
    rep g (IsBiLorentz.metricContraction (T := T))
      = IsBiLorentz.metricContraction (T := T) := by
  rw [IsBiLorentz.metricContraction, map_sum]
  exact Finset.sum_congr rfl fun d _ => by rw [map_smul, hTG g d]

/-!

## D. Peeling a bi-Lorentz span off a stable submodule

`IsBiLorentz.exists_smul_metricContraction_of_invariant_subset` removes one family at a
time from a join, leaving a multiple of the metric trace and a remainder in the stable
submodule.  Section C makes that multiple fixed by both groups, so the remainder inherits
both invariances from the element peeled and the peeling can be iterated.  A submodule of
vectors already fixed by both groups needs no classification at all and is removed by the
same bookkeeping.

-/

/-- The span of the components of a bi-Lorentz family is stable under the Lorentz group:
  each component goes to a combination of components. -/
lemma isBiLorentz_span_stable {T : (Fin 2 → Fin 1 ⊕ Fin 3) → B}
    (hT : IsBiLorentz B repLorentz T) (g : SL(2,ℂ)) {y : B} (hy : y ∈ hT.span) :
    repLorentz g y ∈ hT.span := by
  obtain ⟨c, rfl⟩ := (hT.mem_span_iff y).1 hy
  rw [map_sum]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [map_smul, hT.repLorentz_T g d]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem a (Submodule.mem_span_singleton_self _)))

/-- Peeling one bi-Lorentz span off a Lorentz-stable submodule: an element of the span
  together with `S` fixed by both groups is a multiple of the metric trace plus a remainder
  in `S` fixed by both groups. -/
lemma exists_mem_of_invariant_isBiLorentz_span_sup {T : (Fin 2 → Fin 1 ⊕ Fin 3) → B}
    (hT : IsBiLorentz B repLorentz T)
    (hTG : ∀ (g : GaugeGroupI) (d : Fin 2 → Fin 1 ⊕ Fin 3), rep g (T d) = T d)
    (S : Submodule ℂ B) (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ hT.span ⊔ S) (hL : ∀ g : SL(2,ℂ), repLorentz g x = x)
    (hG : ∀ g : GaugeGroupI, rep g x = x) :
    ∃ y ∈ S, (∀ g : SL(2,ℂ), repLorentz g y = y) ∧ (∀ g : GaugeGroupI, rep g y = y)
      ∧ x - y ∈ ℂ ∙ IsBiLorentz.metricContraction (T := T) := by
  obtain ⟨a, y, hyS, hxy⟩ :=
    hT.exists_smul_metricContraction_of_invariant_subset S hS hx hL
  have hmem : x - y ∈ ℂ ∙ IsBiLorentz.metricContraction (T := T) := by
    rw [hxy, add_sub_cancel_right]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine ⟨y, hyS, fun g => ?_, fun g => ?_, hmem⟩
  · have hfix : repLorentz g (x - y) = x - y := by
      rw [hxy, add_sub_cancel_right, map_smul, repLorentz_metricContraction hT]
    rw [map_sub, hL g] at hfix
    exact sub_right_injective hfix
  · have hfix : rep g (x - y) = x - y := by
      rw [hxy, add_sub_cancel_right, map_smul, rep_metricContraction hTG]
    rw [map_sub, hG g] at hfix
    exact sub_right_injective hfix

/-- Peeling off a submodule of vectors already fixed by both groups: no classification is
  needed, only the splitting of the join. -/
lemma exists_mem_of_invariant_sup_fixed (V S : Submodule ℂ B)
    (hVL : ∀ g : SL(2,ℂ), ∀ v ∈ V, repLorentz g v = v)
    (hVG : ∀ g : GaugeGroupI, ∀ v ∈ V, rep g v = v) {x : B} (hx : x ∈ V ⊔ S)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) (hG : ∀ g : GaugeGroupI, rep g x = x) :
    ∃ y ∈ S, (∀ g : SL(2,ℂ), repLorentz g y = y) ∧ (∀ g : GaugeGroupI, rep g y = y)
      ∧ x - y ∈ V := by
  obtain ⟨v, hv, s, hs, rfl⟩ := Submodule.mem_sup.1 hx
  refine ⟨s, hs, fun g => ?_, fun g => ?_, by simpa using hv⟩
  · have hg := hL g
    rw [map_add, hVL g v hv, add_right_inj] at hg
    exact hg
  · have hg := hG g
    rw [map_add, hVG g v hv, add_right_inj] at hg
    exact hg

/-!

## E. The invariants of mass weight eight

The gauge classification puts a gauge invariant of mass weight eight in the three spans of
twice-derived isospin contractions and the line through the square of the underived one, up
to a remainder in `S`.  Section D peels the three spans off in turn, each time with the
spans not yet peeled adjoined to `S`, and the line through the square needs no peeling.
What is left is a combination of the three metric traces and the square: the two box terms,
the kinetic term and the quartic potential.

-/

/-- The gauge and Lorentz invariants of the Higgs sector at mass weight eight: the two box
  terms `□H† H` and `H† □H`, the kinetic term `∂^μ H† ∂_μ H`, and the quartic potential
  `(H† H)²`. -/
noncomputable def lorentzContractionEightSpan
    (h : IsHiggsSector B rep hrep_mul repLorentz hrepLorentz_mul H barH massWeightPoly) :
    Submodule ℂ B :=
  ℂ ∙ IsBiLorentz.metricContraction
      (T := fun d : Fin 2 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs d ![])
    ⊔ (ℂ ∙ IsBiLorentz.metricContraction
        (T := fun d : Fin 2 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs ![] d)
      ⊔ (ℂ ∙ IsBiLorentz.metricContraction
          (T := fun d : Fin 2 → Fin 1 ⊕ Fin 3 => h.dotGaugeHiggs ![d 0] ![d 1])
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

include h in
/-- The gauge and Lorentz invariants of mass weight eight, modulo a submodule `S` stable
  under both groups: such an invariant is a combination of the two box terms, the kinetic
  term and the quartic potential, plus a remainder in `S` fixed by both groups. -/
theorem exists_mem_of_gauge_and_lorentz_invariant (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, rep g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmodule 8 ⊔ S) (hG : ∀ g : GaugeGroupI, rep g x = x)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ y ∈ S, (∀ g : GaugeGroupI, rep g y = y) ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
      ∧ x - y ∈ h.lorentzContractionEightSpan := by
  obtain ⟨y₀, hy₀S, hy₀G, hxy₀⟩ :=
    h.exists_mem_of_invariant_massWeightSubmodule_eight_sup S hS hx hG
  set Q : Submodule ℂ B := ℂ ∙ (h.dotGaugeHiggs (![] : Fin 0 → Fin 1 ⊕ Fin 3) ![]
    * h.dotGaugeHiggs ![] ![]) with hQdef
  have hQL : ∀ g : SL(2,ℂ), ∀ v ∈ Q, repLorentz g v = v := by
    intro g v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [map_smul, h.invariant_dotGaugeHiggs_sq.1 g]
  have hQG : ∀ g : GaugeGroupI, ∀ v ∈ Q, rep g v = v := by
    intro g v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [map_smul, h.invariant_dotGaugeHiggs_sq.2 g]
  set S₃ : Submodule ℂ B := Q ⊔ S with hS₃def
  set S₂ : Submodule ℂ B := h.dotSpan 1 1 ⊔ S₃ with hS₂def
  set S₁ : Submodule ℂ B := h.dotSpan 0 2 ⊔ S₂ with hS₁def
  have hS₃L : ∀ g : SL(2,ℂ), ∀ y ∈ S₃, repLorentz g y ∈ S₃ :=
    stable_sup_lorentz (fun g v hv => by rw [hQL g v hv]; exact hv) hSL
  have hS₂L : ∀ g : SL(2,ℂ), ∀ y ∈ S₂, repLorentz g y ∈ S₂ := by
    refine stable_sup_lorentz (fun g y hy => ?_) hS₃L
    rw [h.dotSpan_one_one_eq] at hy ⊢
    exact isBiLorentz_span_stable _ g hy
  have hS₁L : ∀ g : SL(2,ℂ), ∀ y ∈ S₁, repLorentz g y ∈ S₁ := by
    refine stable_sup_lorentz (fun g y hy => ?_) hS₂L
    rw [h.dotSpan_zero_two_eq] at hy ⊢
    exact isBiLorentz_span_stable _ g hy
  have hx₁ : x ∈ (h.isBiLorentz_dotGaugeHiggs_left).span ⊔ S₁ := by
    rw [← h.dotSpan_two_zero_eq, hS₁def, hS₂def, hS₃def]
    have hstep : x ∈ (h.dotSpan 2 0 ⊔ h.dotSpan 0 2 ⊔ h.dotSpan 1 1 ⊔ Q) ⊔ S := by
      rw [show x = (x - y₀) + y₀ from by abel]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hxy₀)
        (Submodule.mem_sup_right hy₀S)
    have hle : (h.dotSpan 2 0 ⊔ h.dotSpan 0 2 ⊔ h.dotSpan 1 1 ⊔ Q) ⊔ S
        ≤ h.dotSpan 2 0 ⊔ (h.dotSpan 0 2 ⊔ (h.dotSpan 1 1 ⊔ (Q ⊔ S))) :=
      sup_le (sup_le (sup_le (sup_le le_sup_left (le_sup_of_le_right le_sup_left))
        (le_sup_of_le_right (le_sup_of_le_right le_sup_left)))
        (le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right le_sup_left))))
        (le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right le_sup_right)))
    exact hle hstep
  obtain ⟨y₁, hy₁, hy₁L, hy₁G, hxy₁⟩ :=
    exists_mem_of_invariant_isBiLorentz_span_sup h.isBiLorentz_dotGaugeHiggs_left
      (fun g d => h.rep_dotGaugeHiggs_invariant g d ![]) S₁ hS₁L hx₁ hL hG
  rw [hS₁def, h.dotSpan_zero_two_eq] at hy₁
  obtain ⟨y₂, hy₂, hy₂L, hy₂G, hxy₂⟩ :=
    exists_mem_of_invariant_isBiLorentz_span_sup h.isBiLorentz_dotGaugeHiggs_right
      (fun g d => h.rep_dotGaugeHiggs_invariant g ![] d) S₂ hS₂L hy₁ hy₁L hy₁G
  rw [hS₂def, h.dotSpan_one_one_eq] at hy₂
  obtain ⟨y₃, hy₃, hy₃L, hy₃G, hxy₃⟩ :=
    exists_mem_of_invariant_isBiLorentz_span_sup h.isBiLorentz_dotGaugeHiggs_mixed
      (fun g d => h.rep_dotGaugeHiggs_invariant g ![d 0] ![d 1]) S₃ hS₃L hy₂ hy₂L hy₂G
  obtain ⟨y, hyS, hyL, hyG, hxy⟩ :=
    exists_mem_of_invariant_sup_fixed Q S hQL hQG hy₃ hy₃L hy₃G
  refine ⟨y, hyS, hyG, hyL, ?_⟩
  rw [show x - y = (x - y₁) + ((y₁ - y₂) + ((y₂ - y₃) + (y₃ - y))) from by abel,
    lorentzContractionEightSpan]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hxy₁)
    (Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mem_sup_left hxy₂))
      (Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mem_sup_right
          (Submodule.mem_sup_left hxy₃)))
        (Submodule.mem_sup_right (Submodule.mem_sup_right
          (Submodule.mem_sup_right hxy)))))

/-!

## F. The span consists of invariants of mass weight eight

The classification of section E is one-directional as stated, and the converse is easy:
each of the four generators is built from isospin contractions of the right mass weight,
which both groups fix, so the span is made of invariants of mass weight eight already.
The metric trace inherits the mass weight of the components and both invariances from
section C, and the square of the underived contraction is a product of two invariants of
mass weight four.

-/

include h in
/-- The metric trace of a family of elements of mass weight eight has mass weight
  eight. -/
lemma metricContraction_mem_massWeightSubmodule {T : (Fin 2 → Fin 1 ⊕ Fin 3) → B}
    (hT : ∀ d, T d ∈ h.massWeightSubmodule 8) :
    IsBiLorentz.metricContraction (T := T) ∈ h.massWeightSubmodule 8 := by
  rw [IsBiLorentz.metricContraction]
  exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (hT d)

include h in
/-- The weight-eight span lies in the mass-weight submodule of weight eight. -/
lemma lorentzContractionEightSpan_le_massWeightSubmodule :
    h.lorentzContractionEightSpan ≤ h.massWeightSubmodule 8 := by
  rw [lorentzContractionEightSpan]
  refine sup_le ?_ (sup_le ?_ (sup_le ?_ ?_)) <;>
    rw [Submodule.span_singleton_le_iff_mem]
  · exact h.metricContraction_mem_massWeightSubmodule fun d =>
      h.dotGaugeHiggs_mem_massWeightSubmodule d ![]
  · exact h.metricContraction_mem_massWeightSubmodule fun d =>
      h.dotGaugeHiggs_mem_massWeightSubmodule ![] d
  · exact h.metricContraction_mem_massWeightSubmodule fun d =>
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
    · exact rep_metricContraction (fun k d => h.rep_dotGaugeHiggs_invariant k d ![]) g
    · exact rep_metricContraction (fun k d => h.rep_dotGaugeHiggs_invariant k ![] d) g
    · exact rep_metricContraction
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
    · exact repLorentz_metricContraction h.isBiLorentz_dotGaugeHiggs_left g
    · exact repLorentz_metricContraction h.isBiLorentz_dotGaugeHiggs_right g
    · exact repLorentz_metricContraction h.isBiLorentz_dotGaugeHiggs_mixed g
    · exact h.invariant_dotGaugeHiggs_sq.1 g
  have hy' := key hy
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hy'
  exact hy'

/-!

## G. The classification as an equivalence

The two directions meet.  Forwards, section E puts an invariant of mass weight eight in the
span up to a remainder in `S`; backwards, section F says the span is made of such
invariants, so the remainder plus the span element is one again.  Splitting `x` as
`(x - y) + y` is all the backward direction takes.

-/

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
          ∧ x - y ∈ h.lorentzContractionEightSpan := by
  refine ⟨fun hx =>
    h.exists_mem_of_gauge_and_lorentz_invariant S hS hSL hx.1 hx.2.1 hx.2.2, ?_⟩
  rintro ⟨y, hyS, hyG, hyL, hxy⟩
  refine ⟨?_, fun g => ?_, fun g => ?_⟩
  · have hsum : x - y + y ∈ h.massWeightSubmodule 8 ⊔ S :=
      Submodule.add_mem _
        (Submodule.mem_sup_left (h.lorentzContractionEightSpan_le_massWeightSubmodule hxy))
        (Submodule.mem_sup_right hyS)
    simpa using hsum
  · have hstep : rep g (x - y + y) = x - y + y := by
      rw [map_add, h.rep_of_mem_lorentzContractionEightSpan g hxy, hyG g]
    simpa using hstep
  · have hstep : repLorentz g (x - y + y) = x - y + y := by
      rw [map_add, h.repLorentz_of_mem_lorentzContractionEightSpan g hxy, hyL g]
    simpa using hstep

end IsHiggsSector

end StandardModel
