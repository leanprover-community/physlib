/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsGaugeSector.MassWeight.Basic
public import Physlib.Relativity.LorentzGroup.Invariants.IsBiLorentz
public import Physlib.Relativity.LorentzGroup.Invariants.IsTriLorentz
/-!
# The invariants below mass weight eight

Mass weight eight is the first weight of the gauge sector carrying a gauge and Lorentz
invariant. Below it there is nothing: the odd weights and weight two are trivial
submodules, weight four is a single underived field strength and weight six a single
once-derived one, and neither of those two carries an invariant.

Weight four fails on parity of a different kind. An underived field strength carries two
covector indices and one adjoint index, so at a fixed gauge direction it is a bi-Lorentz
tensor, whose only invariant contraction is the metric trace. That trace vanishes, the
metric being symmetric in the pair of indices in which `IsGaugeSector.F_antisymm` says
the field strength is antisymmetric. Weight six fails on counting: a once-derived field
strength carries three covector indices, and three indices admit no invariant contraction
at all, the metric tying two and the Levi-Civita symbol four.

Neither argument needs the gauge group. The vanishing at weight four holds at every gauge
direction separately, the colour and isospin ones included, so no appeal to
`IsSU3Adjoint` or `IsSU2Adjoint` is required and Lorentz invariance alone does the work.
What the gauge algebra does contribute is finiteness: a field-strength symbol is
evaluated on a covector of the gauge algebra, and expanding that covector in the dual of
the standard basis writes each derivative submodule inside a finite join of Lorentz
spans, one for each of the twelve basis directions, which is what the peeling arguments
consume.

- A. The symbols on the standard basis of the gauge algebra
- B. Sums over tuples of covector indices
- C. The field-strength symbols as Lorentz families
- D. The vanishing of the metric trace of an antisymmetric family
- E. Peeling Lorentz spans off a stable submodule
- F. Mass weight four
- G. Mass weight six
- H. The classification below mass weight eight

The final statement `mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff`
needs `0 < w` as well as `w < 8`: at `w = 0` the mass-weight submodule contains the
scalars, so `1` is an invariant of weight zero lying in no `S`.

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups Lorentz

namespace IsGaugeSector

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsGaugeSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
      F massWeightPoly)

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
    F l μ ν φ ∈ ⨆ c : Fin 8 ⊕ Fin 3 ⊕ Fin 1,
      ℂ ∙ F l μ ν (GaugeAlgebra.stdBasis.coord c) := by
  have hF : F l μ ν φ
      = ∑ c : Fin 8 ⊕ Fin 3 ⊕ Fin 1,
        φ (GaugeAlgebra.stdBasis c) • F l μ ν (GaugeAlgebra.stdBasis.coord c) := by
    conv_lhs => rw [← GaugeAlgebra.stdBasis.sum_dual_apply_smul_coord φ]
    rw [map_sum]
    exact Finset.sum_congr rfl fun c _ => map_smul _ _ _
  rw [hF]
  refine Submodule.sum_mem _ fun c _ => ?_
  exact Submodule.mem_iSup_of_mem c
    (Submodule.smul_of_tower_mem _ _ (Submodule.mem_span_singleton_self _))

/-!

## B. Sums over tuples of covector indices

A Lorentz family is indexed by a tuple of covector indices, while the transformation law
of `IsGaugeSector` presents its sums one index at a time. These three lemmas turn a sum
over tuples into an iterated sum and back.

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

/-- A sum over families of three covector indices is a triple sum. -/
lemma sum_cov_three {M : Type*} [AddCommMonoid M] (f : (Fin 3 → Fin 1 ⊕ Fin 3) → M) :
    ∑ d : Fin 3 → Fin 1 ⊕ Fin 3, f d
      = ∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3, ∑ z : Fin 1 ⊕ Fin 3, f ![x, y, z] := by
  rw [show (∑ d : Fin 3 → Fin 1 ⊕ Fin 3, f d)
      = ∑ p : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3),
        f ![p.1, p.2.1, p.2.2] from
      Fintype.sum_equiv
        { toFun := fun d => (d 0, d 1, d 2)
          invFun := fun p => ![p.1, p.2.1, p.2.2]
          left_inv := fun d => by funext i; fin_cases i <;> simp
          right_inv := fun p => by simp } _ _ fun d => by
        congr 1
        funext i
        fin_cases i <;> simp]
  simp only [Fintype.sum_prod_type]

/-!

## C. The field-strength symbols as Lorentz families

An underived field-strength symbol carries two covector indices and nothing else, and a
once-derived one carries three, its derivative slot included. Read as families indexed by
those indices they are a bi-Lorentz and a triple Lorentz tensor, the transformation law
of `IsGaugeSector` moving every index by the Lorentz matrix of the `SL(2,ℂ)` element.

-/

include h in
/-- An underived field-strength symbol, viewed as a family indexed by its two covector
  indices, is a bi-Lorentz tensor. -/
lemma isBiLorentz_F_underived (φ : Module.Dual ℝ GaugeAlgebra) :
    IsBiLorentz B repLorentz
      (fun d : Fin 2 → Fin 1 ⊕ Fin 3 => F ![] (d 0) (d 1) φ) where
  repLorentz_T g l := by
    rw [h.repLorentz_F g 0 ![] (l 0) (l 1) φ,
      Finset.sum_eq_single (![] : Fin 0 → Fin 1 ⊕ Fin 3)
        (fun b _ hb => absurd (Subsingleton.elim b ![]) hb)
        (fun hb => absurd (Finset.mem_univ _) hb),
      Fin.prod_univ_zero, one_smul, sum_cov_two]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [smul_smul]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

include h in
/-- A once-derived field-strength symbol, viewed as a family indexed by its derivative
  slot and its two covector indices, is a triple Lorentz tensor. -/
lemma isTriLorentz_F_deriv_one (φ : Module.Dual ℝ GaugeAlgebra) :
    IsTriLorentz B repLorentz
      (fun d : Fin 3 → Fin 1 ⊕ Fin 3 => F ![d 0] (d 1) (d 2) φ) where
  repLorentz_T g l := by
    rw [h.repLorentz_F g 1 ![l 0] (l 1) (l 2) φ, sum_cov_one, sum_cov_three]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [smul_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [smul_smul]
    simp only [Fin.prod_univ_one, Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-!

## D. The vanishing of the metric trace of an antisymmetric family

Two covector indices admit a single invariant contraction, the metric trace, and the
metric is diagonal, so that trace is the sum of the components on the diagonal. A family
antisymmetric in its two indices has every diagonal component equal to its own negative,
hence zero, and the trace vanishes with them.

-/

/-- The metric trace of a bi-Lorentz family antisymmetric in its two indices vanishes:
  the metric is diagonal, and the diagonal components of such a family are zero. -/
lemma metricContraction_eq_zero_of_antisymm {T : (Fin 2 → Fin 1 ⊕ Fin 3) → B}
    (hswap : ∀ x y : Fin 1 ⊕ Fin 3, T ![y, x] = - T ![x, y]) :
    IsBiLorentz.metricContraction (T := T) = 0 := by
  rw [IsBiLorentz.metricContraction]
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

## E. Peeling Lorentz spans off a stable submodule

Both classifications come in a form relative to a Lorentz-stable submodule `S`: an
invariant of the span of a family together with `S` is a contraction of the family up to
a remainder in `S`. When the contraction vanishes, or when there is none, the invariant
lies in `S` outright. The spans themselves are Lorentz stable, so a finite join of them
can be peeled one summand at a time, each step enlarging `S` by the summands not yet
peeled.

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

/-- The span of the components of a triple Lorentz family is stable under the Lorentz
  group. -/
lemma isTriLorentz_span_stable {T : (Fin 3 → Fin 1 ⊕ Fin 3) → B}
    (hT : IsTriLorentz B repLorentz T) (g : SL(2,ℂ)) {y : B} (hy : y ∈ hT.span) :
    repLorentz g y ∈ hT.span := by
  obtain ⟨c, rfl⟩ := (hT.mem_span_iff y).1 hy
  rw [map_sum]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [map_smul, hT.repLorentz_T g d]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem a (Submodule.mem_span_singleton_self _)))

/-- A Lorentz invariant of the span of a bi-Lorentz family with vanishing metric trace,
  together with a Lorentz-stable submodule, already lies in that submodule. -/
lemma mem_of_lorentz_invariant_isBiLorentz_span_sup {T : (Fin 2 → Fin 1 ⊕ Fin 3) → B}
    (hT : IsBiLorentz B repLorentz T)
    (hzero : IsBiLorentz.metricContraction (T := T) = 0) (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B} (hx : x ∈ hT.span ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  obtain ⟨a, y, hy, hxy⟩ :=
    hT.exists_smul_metricContraction_of_invariant_subset S hS hx hinv
  rwa [hxy, hzero, smul_zero, zero_add]

/-- Peeling a finite join of the spans of bi-Lorentz families with vanishing metric
  traces off a Lorentz-stable submodule: a Lorentz invariant of the join together with
  `S` lies in `S`. -/
lemma mem_of_lorentz_invariant_biSup_isBiLorentz_span {ι : Type} [DecidableEq ι]
    {T : ι → (Fin 2 → Fin 1 ⊕ Fin 3) → B} (hT : ∀ i, IsBiLorentz B repLorentz (T i))
    (hzero : ∀ i, IsBiLorentz.metricContraction (T := T i) = 0) (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (s : Finset ι) {x : B}
    (hx : x ∈ (⨆ i ∈ s, (hT i).span) ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  induction s using Finset.induction_on generalizing x with
  | empty =>
    rw [show (⨆ i ∈ (∅ : Finset ι), (hT i).span) = ⊥ from by simp, bot_sup_eq] at hx
    exact hx
  | insert a s ha ih =>
    rw [Finset.iSup_insert, sup_assoc] at hx
    have hstab : ∀ g : SL(2,ℂ), ∀ y ∈ (⨆ i ∈ s, (hT i).span) ⊔ S,
        repLorentz g y ∈ (⨆ i ∈ s, (hT i).span) ⊔ S := by
      intro g y hy
      have key : ((⨆ i ∈ s, (hT i).span) ⊔ S)
          ≤ Submodule.comap (repLorentz g) ((⨆ i ∈ s, (hT i).span) ⊔ S) :=
        sup_le (iSup_le fun i => iSup_le fun hi => fun z hz =>
            Submodule.mem_sup_left (Submodule.mem_iSup_of_mem i
              (Submodule.mem_iSup_of_mem hi (isBiLorentz_span_stable (hT i) g hz))))
          fun z hz => Submodule.mem_sup_right (hS g z hz)
      exact key hy
    exact ih (mem_of_lorentz_invariant_isBiLorentz_span_sup (hT a) (hzero a) _ hstab hx
      hinv) hinv

/-- Peeling a finite join of the spans of triple Lorentz families off a Lorentz-stable
  submodule: three covector indices carry no invariant contraction at all, so a Lorentz
  invariant of the join together with `S` lies in `S`. -/
lemma mem_of_lorentz_invariant_biSup_isTriLorentz_span {ι : Type} [DecidableEq ι]
    {T : ι → (Fin 3 → Fin 1 ⊕ Fin 3) → B} (hT : ∀ i, IsTriLorentz B repLorentz (T i))
    (S : Submodule ℂ B) (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (s : Finset ι)
    {x : B} (hx : x ∈ (⨆ i ∈ s, (hT i).span) ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  induction s using Finset.induction_on generalizing x with
  | empty =>
    rw [show (⨆ i ∈ (∅ : Finset ι), (hT i).span) = ⊥ from by simp, bot_sup_eq] at hx
    exact hx
  | insert a s ha ih =>
    rw [Finset.iSup_insert, sup_assoc] at hx
    have hstab : ∀ g : SL(2,ℂ), ∀ y ∈ (⨆ i ∈ s, (hT i).span) ⊔ S,
        repLorentz g y ∈ (⨆ i ∈ s, (hT i).span) ⊔ S := by
      intro g y hy
      have key : ((⨆ i ∈ s, (hT i).span) ⊔ S)
          ≤ Submodule.comap (repLorentz g) ((⨆ i ∈ s, (hT i).span) ⊔ S) :=
        sup_le (iSup_le fun i => iSup_le fun hi => fun z hz =>
            Submodule.mem_sup_left (Submodule.mem_iSup_of_mem i
              (Submodule.mem_iSup_of_mem hi (isTriLorentz_span_stable (hT i) g hz))))
          fun z hz => Submodule.mem_sup_right (hS g z hz)
      exact key hy
    exact ih ((hT a).mem_of_invariant_of_mem_sup _ hstab hx hinv) hinv

/-- A join over a finite index type is the join over its universal finite set. -/
lemma iSup_eq_biSup_univ {ι : Type} [Fintype ι] (f : ι → Submodule ℂ B) :
    ⨆ i, f i = ⨆ i ∈ (Finset.univ : Finset ι), f i := by simp

/-!

## F. Mass weight four

Mass weight four is the underived field strength. At each of the twelve directions of the
standard basis of the gauge algebra it is a bi-Lorentz family, whose metric trace vanishes
by the antisymmetry of the field strength in its two covector indices, so section E peels
the twelve spans off and leaves nothing behind. No gauge hypothesis enters: the vanishing
holds at the colour and isospin directions just as at the hypercharge one.

-/

include h in
/-- The metric trace of the underived field-strength symbols at a fixed direction of the
  gauge algebra vanishes, the symbol being antisymmetric in its two covector indices. -/
lemma metricContraction_F_underived_eq_zero (φ : Module.Dual ℝ GaugeAlgebra) :
    IsBiLorentz.metricContraction
      (T := fun d : Fin 2 → Fin 1 ⊕ Fin 3 => F ![] (d 0) (d 1) φ) = 0 :=
  metricContraction_eq_zero_of_antisymm fun x y => by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact h.F_antisymm ![] x y φ

include h in
/-- The underived field strengths lie in the join, over the twelve directions of the
  standard basis of the gauge algebra, of the spans of the bi-Lorentz families they
  form. -/
lemma derivSubmodule_zero_le_iSup_span :
    h.derivSubmodule 0 ≤ ⨆ c : Fin 8 ⊕ Fin 3 ⊕ Fin 1,
      (h.isBiLorentz_F_underived (GaugeAlgebra.stdBasis.coord c)).span := by
  rw [derivSubmodule]
  refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => ?_
  rw [Submodule.span_le]
  rintro x ⟨φ, rfl⟩
  rw [SetLike.mem_coe, Subsingleton.elim l ![]]
  have hle : (⨆ c : Fin 8 ⊕ Fin 3 ⊕ Fin 1,
        ℂ ∙ F ![] μ ν (GaugeAlgebra.stdBasis.coord c))
      ≤ ⨆ c : Fin 8 ⊕ Fin 3 ⊕ Fin 1,
        (h.isBiLorentz_F_underived (GaugeAlgebra.stdBasis.coord c)).span := by
    refine iSup_mono fun c => ?_
    rw [Submodule.span_singleton_le_iff_mem]
    refine Submodule.mem_iSup_of_mem ![μ, ν] ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact Submodule.mem_span_singleton_self _
  exact hle (F_mem_iSup_span_coord ![] μ ν φ)

include h in
/-- Mass weight four carries no Lorentz invariant modulo a Lorentz-stable submodule: a
  Lorentz invariant of `massWeightSubmodule 4 ⊔ S` lies in `S`. -/
theorem mem_of_lorentz_invariant_massWeightSubmodule_four_sup (S : Submodule ℂ B)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmodule 4 ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  refine mem_of_lorentz_invariant_biSup_isBiLorentz_span
    (fun c => h.isBiLorentz_F_underived (GaugeAlgebra.stdBasis.coord c))
    (fun c => h.metricContraction_F_underived_eq_zero _) S hSL Finset.univ ?_ hinv
  rw [h.massWeightSubmodule_four_eq] at hx
  refine sup_le_sup_right ?_ S hx
  rw [← iSup_eq_biSup_univ]
  exact h.derivSubmodule_zero_le_iSup_span

/-!

## G. Mass weight six

Mass weight six is the once-derived field strength, a triple Lorentz family at each
direction of the standard basis. Three covector indices carry no invariant contraction at
all, so `IsTriLorentz` needs no antisymmetry and no gauge input either: the twelve spans
peel off and the invariant is left in `S`.

-/

/-- A family of one covector index is the tuple of its own entry. -/
lemma etaExpand_cov_one (l : Fin 1 → Fin 1 ⊕ Fin 3) : ![l 0] = l := by
  funext i
  fin_cases i
  rfl

include h in
/-- The once-derived field strengths lie in the join, over the twelve directions of the
  standard basis of the gauge algebra, of the spans of the triple Lorentz families they
  form. -/
lemma derivSubmodule_one_le_iSup_span :
    h.derivSubmodule 1 ≤ ⨆ c : Fin 8 ⊕ Fin 3 ⊕ Fin 1,
      (h.isTriLorentz_F_deriv_one (GaugeAlgebra.stdBasis.coord c)).span := by
  rw [derivSubmodule]
  refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => ?_
  rw [Submodule.span_le]
  rintro x ⟨φ, rfl⟩
  rw [SetLike.mem_coe]
  have hle : (⨆ c : Fin 8 ⊕ Fin 3 ⊕ Fin 1,
        ℂ ∙ F l μ ν (GaugeAlgebra.stdBasis.coord c))
      ≤ ⨆ c : Fin 8 ⊕ Fin 3 ⊕ Fin 1,
        (h.isTriLorentz_F_deriv_one (GaugeAlgebra.stdBasis.coord c)).span := by
    refine iSup_mono fun c => ?_
    rw [Submodule.span_singleton_le_iff_mem]
    refine Submodule.mem_iSup_of_mem ![l 0, μ, ν] ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, etaExpand_cov_one]
    exact Submodule.mem_span_singleton_self _
  exact hle (F_mem_iSup_span_coord l μ ν φ)

include h in
/-- Mass weight six carries no Lorentz invariant modulo a Lorentz-stable submodule: a
  Lorentz invariant of `massWeightSubmodule 6 ⊔ S` lies in `S`. -/
theorem mem_of_lorentz_invariant_massWeightSubmodule_six_sup (S : Submodule ℂ B)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmodule 6 ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  refine mem_of_lorentz_invariant_biSup_isTriLorentz_span
    (fun c => h.isTriLorentz_F_deriv_one (GaugeAlgebra.stdBasis.coord c))
    S hSL Finset.univ ?_ hinv
  rw [h.massWeightSubmodule_six_eq] at hx
  refine sup_le_sup_right ?_ S hx
  rw [← iSup_eq_biSup_univ]
  exact h.derivSubmodule_one_le_iSup_span

/-!

## H. The classification below mass weight eight

The seven weights between zero and eight are now settled: weights one, two, three, five
and seven are trivial submodules, weight four is section F and weight six section G. So
between weight zero and weight eight there is no invariant beyond what `S` already
supplies, and the equivalence records it.

The lower bound `0 < w` cannot be dropped. Weight zero contains the scalars by
`one_le_massWeightSubmodule_zero`, and `1` is fixed by both groups, the two
representations being multiplicative, without lying in any given `S`.

-/

include h in
/-- Between mass weight zero and mass weight eight there is no Lorentz invariant: a
  Lorentz invariant of `massWeightSubmodule w ⊔ S` for `0 < w < 8` lies in `S`. The five
  odd or small weights are trivial submodules, and weights four and six are sections F
  and G. -/
theorem mem_of_lorentz_invariant_massWeightSubmodule_lt_eight_sup (w : ℕ) (hw0 : 0 < w)
    (hw : w < 8) (S : Submodule ℂ B)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.massWeightSubmodule w ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  interval_cases w
  · rwa [h.massWeightSubmodule_one_eq, bot_sup_eq] at hx
  · rwa [h.massWeightSubmodule_two_eq, bot_sup_eq] at hx
  · rwa [h.massWeightSubmodule_three_eq, bot_sup_eq] at hx
  · exact h.mem_of_lorentz_invariant_massWeightSubmodule_four_sup S hSL hx hinv
  · rwa [h.massWeightSubmodule_five_eq, bot_sup_eq] at hx
  · exact h.mem_of_lorentz_invariant_massWeightSubmodule_six_sup S hSL hx hinv
  · rwa [h.massWeightSubmodule_seven_eq, bot_sup_eq] at hx

set_option linter.unusedVariables false in
/-- The classification below mass weight eight as an equivalence, in the shape of
  `mem_massWeightSubmodule_eight_sup_and_gauge_lorentz_invariant_iff`: an element of
  `massWeightSubmodule w ⊔ S` for `0 < w < 8` is fixed by both groups exactly when it is
  itself an element of `S` fixed by both groups. The span of invariants that the weight
  eight statement leaves over is here the trivial one, so `x - y` lies in it exactly when
  `x = y`. Gauge stability of `S` is not needed, and neither is gauge invariance of `x`:
  the forward direction is
  `mem_of_lorentz_invariant_massWeightSubmodule_lt_eight_sup`, which uses the Lorentz
  group alone. -/
theorem mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff (w : ℕ)
    (hw0 : 0 < w) (hw : w < 8) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmodule w ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x = y := by
  constructor
  · rintro ⟨hx, hG, hL⟩
    exact ⟨x, h.mem_of_lorentz_invariant_massWeightSubmodule_lt_eight_sup w hw0 hw S hSL
      hx hL, hG, hL, rfl⟩
  · rintro ⟨y, hyS, hyG, hyL, rfl⟩
    exact ⟨Submodule.mem_sup_right hyS, hyG, hyL⟩

set_option linter.unusedVariables false in
/-- The same classification without the existential: below mass weight eight an element
  of `massWeightSubmodule w ⊔ S` fixed by both groups is an element of `S` fixed by both
  groups, and conversely. -/
theorem mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff_mem (w : ℕ)
    (hw0 : 0 < w) (hw : w < 8) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.massWeightSubmodule w ⊔ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
        ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ (x ∈ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentz g x = x) := by
  refine ⟨fun hx => ⟨h.mem_of_lorentz_invariant_massWeightSubmodule_lt_eight_sup w hw0 hw
    S hSL hx.1 hx.2.2, hx.2⟩, fun hx => ⟨Submodule.mem_sup_right hx.1, hx.2⟩⟩

end IsGaugeSector

end StandardModel
