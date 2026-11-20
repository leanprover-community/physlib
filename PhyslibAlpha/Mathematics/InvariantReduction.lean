/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RepresentationTheory.Basic
public import PhyslibAlpha.Mathematics.LinearCombination
/-!
# Reducing invariants modulo a stable submodule

Classifying the invariants of a family of linear maps one stable submodule at a time.

## i. Overview

Let `σ : G → B →ₗ[R] B` be a family of linear maps, indexed by an arbitrary type. No group or
representation law is assumed. An element `x` is invariant when `σ g x = x` for every `g`, and
a submodule is stable when every `σ g` carries it into itself.

The relation `ReducesInvariantsTo σ V W` says: for every stable submodule `S`, every invariant
of `V ⊔ S` lies in `W ⊔ S`. It is transitive, antitone in the source, monotone in the target
and, for stable sources and a stable target, closed under joins of the source. Since an element
of a join lies in a join over finitely many summands, the index type need not be finite:
`ReducesInvariantsTo.iSup_of_biSup`, and with it `ReducesInvariantsTo.iSup`. A classification
of the invariants of a family can therefore be applied one family at a time, the other families
being kept in the stable remainder `S`. A submodule on which one map of the family acts by a
scalar other than `1` reduces to `⊥`: `reducesInvariantsTo_bot_of_apply_eq_smul`.

Such a reduction is usually proved in the quotient `B ⧸ S`. If every invariant of the image of
`V` in `B ⧸ S` lies in the image of `W`, then every invariant of `V ⊔ S` lies in `W ⊔ S`, and
when `W` is pointwise fixed the remainder in `S` is itself invariant:
`IsStableUnder.exists_add_of_quotient`. The quotient hypothesis is not implied by a
classification of the invariants of `V` alone, since the invariants of `B ⧸ S` are the classes
`x` with `σ g x - x ∈ S`. For a pointwise-fixed `W ≤ V` a reduction describes the invariants
of `V ⊔ S` exactly, as the elements of `W` plus an invariant element of `S`:
`ReducesInvariantsTo.mem_sup_and_forall_eq_self_iff`.

`InvariantReductionToSpan σ V` packages a reduction of `V` to the span of one fixed vector,
the form in which the classification theorems are applied.

A representation of a group `H` and a representation of `SL(2,ℂ)` on the same module are read as
one family, `gaugeLorentzMaps`, indexed by `H ⊕ SL(2,ℂ)`. Its invariants and stable submodules
are those of both groups, and a reduction for either group alone is a reduction for the family.

## ii. Key results

- `ReducesInvariantsTo.iSup_of_biSup` : a reduction of every join over a finite set of indices is a
  reduction of the join over the whole index type, which may be infinite: an element of the join
  lies in the join over finitely many of the summands
- `ReducesInvariantsTo.iSup` : reductions of stable submodules to a common stable target combine
  over any index type, finite or not: `biSup` combines them over every finite set of indices, and
  `iSup_of_biSup` passes to the whole join
- `reducesInvariantsTo_bot_of_apply_eq_smul` : a submodule on which one map of the family acts by a
  scalar `μ ≠ 1` reduces to `⊥`
- `ReducesInvariantsTo.mem_sup_and_forall_eq_self_iff` : for a pointwise-fixed target inside the
  source, the invariants of `V ⊔ S` are the elements of `W` plus an invariant element of `S`
- `IsStableUnder.exists_add_of_quotient` : quotient to remainder: when every invariant of the image
  of `V` in `B ⧸ S` lies in the image of a pointwise-fixed `W`, an invariant of `V ⊔ S` is an
  element of `W` plus an invariant element of `S`
- `ReducesInvariantsTo.mem_sup_and_gauge_lorentz_invariant_iff` : the classification endpoint for
  a group `H` and the Lorentz group together, with the two invariances stated separately

## iii. Table of contents

- A. Stable and fixed submodules
- B. Reducing invariants
- C. Reduction through a quotient
- D. Reduction to the span of one vector
- E. A group together with the Lorentz group

## iv. References

* None.

-/

@[expose] public section

/-!

## A. Stable and fixed submodules

-/

section Stability

variable {R B G : Type*} [Semiring R] [AddCommMonoid B] [Module R B]

/-- A submodule carried into itself by every map of the family `σ`. -/
def IsStableUnder (σ : G → B →ₗ[R] B) (V : Submodule R B) : Prop :=
  ∀ g, ∀ y ∈ V, σ g y ∈ V

/-- A submodule fixed pointwise by every map of the family `σ`. -/
def IsFixedBy (σ : G → B →ₗ[R] B) (V : Submodule R B) : Prop :=
  ∀ g, ∀ y ∈ V, σ g y = y

variable {σ : G → B →ₗ[R] B}

/-- Stability as an inclusion of images. -/
lemma isStableUnder_iff_map {V : Submodule R B} :
    IsStableUnder σ V ↔ ∀ g, Submodule.map (σ g) V ≤ V := by
  constructor
  · rintro hV g _ ⟨y, hy, rfl⟩
    exact hV g y hy
  · exact fun hV g y hy => hV g ⟨y, hy, rfl⟩

/-- A pointwise-fixed submodule is stable. -/
lemma IsFixedBy.isStableUnder {V : Submodule R B} (hV : IsFixedBy σ V) : IsStableUnder σ V :=
  fun g y hy => by rw [hV g y hy]; exact hy

/-- A join of two pointwise-fixed submodules is pointwise fixed. -/
lemma IsFixedBy.sup {V V' : Submodule R B} (hV : IsFixedBy σ V) (hV' : IsFixedBy σ V') :
    IsFixedBy σ (V ⊔ V') := by
  intro g y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add, hV g a ha, hV' g b hb]

/-- The zero submodule is stable. -/
lemma isStableUnder_bot : IsStableUnder σ (⊥ : Submodule R B) := by
  intro g y hy
  rw [Submodule.mem_bot] at hy
  simp [hy]

/-- A join of two stable submodules is stable. -/
lemma IsStableUnder.sup {V V' : Submodule R B} (hV : IsStableUnder σ V)
    (hV' : IsStableUnder σ V') : IsStableUnder σ (V ⊔ V') :=
  isStableUnder_iff_map.2 fun g => by
    rw [Submodule.map_sup]
    exact sup_le_sup (isStableUnder_iff_map.1 hV g) (isStableUnder_iff_map.1 hV' g)

/-- An indexed join of stable submodules is stable. The index is a `Sort`, so this covers
  the bounded join `⨆ i ∈ s, V i`. -/
lemma isStableUnder_iSup {ι : Sort*} {V : ι → Submodule R B}
    (hV : ∀ i, IsStableUnder σ (V i)) : IsStableUnder σ (⨆ i, V i) :=
  isStableUnder_iff_map.2 fun g => by
    rw [Submodule.map_iSup]
    exact iSup_mono fun i => isStableUnder_iff_map.1 (hV i) g

/-- The span of a fixed vector is pointwise fixed. -/
lemma isFixedBy_span_singleton {b : B} (hb : ∀ g, σ g b = b) : IsFixedBy σ (R ∙ b) := by
  intro g y hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rw [map_smul, hb]

/-- An indexed join of pointwise-fixed submodules is pointwise fixed. -/
lemma isFixedBy_iSup {ι : Sort*} {V : ι → Submodule R B} (hV : ∀ i, IsFixedBy σ (V i)) :
    IsFixedBy σ (⨆ i, V i) := by
  intro g y hy
  refine Submodule.iSup_induction (motive := fun z => σ g z = z) V hy (fun i z hz => hV i g z hz)
    (map_zero _) fun z z' hz hz' => by rw [map_add, hz, hz']

/-- The span of a family of fixed vectors is pointwise fixed. -/
lemma isFixedBy_span_range {ι : Sort*} {T : ι → B} (hT : ∀ i g, σ g (T i) = T i) :
    IsFixedBy σ (Submodule.span R (Set.range T)) := fun g _ hy =>
  (Submodule.span_le (p := LinearMap.eqLocus (σ g) LinearMap.id)).2
    (Set.range_subset_iff.2 fun i => hT i g) hy

/-- The span of a family is stable when each map sends each member into the span. -/
lemma isStableUnder_span_range {ι : Sort*} {T : ι → B}
    (hT : ∀ g i, σ g (T i) ∈ Submodule.span R (Set.range T)) :
    IsStableUnder σ (Submodule.span R (Set.range T)) :=
  isStableUnder_iff_map.2 fun g => by
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le, Set.range_subset_iff]
    exact hT g

/-- The span of a finite family is stable when each map sends each member to a combination
  of the family. -/
lemma isStableUnder_span_range_of_sum {ι : Type*} [Fintype ι] {T : ι → B}
    (hT : ∀ g i, ∃ c : ι → R, σ g (T i) = ∑ a, c a • T a) :
    IsStableUnder σ (Submodule.span R (Set.range T)) :=
  isStableUnder_span_range fun g i => by
    obtain ⟨c, hc⟩ := hT g i
    exact (Submodule.mem_span_range_iff_exists_fun R).2 ⟨c, hc.symm⟩

/-- A product of two stable submodules of an algebra is stable under maps respecting
  multiplication. -/
lemma IsStableUnder.mul {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {σ : G → A →ₗ[R] A} (hσ : ∀ g (a b : A), σ g (a * b) = σ g a * σ g b)
    {V V' : Submodule R A} (hV : IsStableUnder σ V) (hV' : IsStableUnder σ V') :
    IsStableUnder σ (V * V') :=
  isStableUnder_iff_map.2 fun g => by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.mul_le.2 fun a ha b hb => ?_
    show σ g (a * b) ∈ V * V'
    rw [hσ]
    exact Submodule.mul_mem_mul (hV g a ha) (hV' g b hb)

end Stability

/-!

## B. Reducing invariants

To reduce `V₁ ⊔ V₂` to `W`, the summand `V₂` is first moved into the remainder, which needs `V₂`
stable; the result lies in `W ⊔ (V₂ ⊔ S)`, and reducing `V₂` from there needs `W` stable.

-/

section Reduction

variable {R B G : Type*} [Semiring R] [AddCommMonoid B] [Module R B] {σ : G → B →ₗ[R] B}

/-- Every invariant of `V ⊔ S`, for `S` a `σ`-stable submodule, lies in `W ⊔ S`. -/
def ReducesInvariantsTo (σ : G → B →ₗ[R] B) (V W : Submodule R B) : Prop :=
  ∀ S : Submodule R B, IsStableUnder σ S → ∀ x ∈ V ⊔ S, (∀ g, σ g x = x) → x ∈ W ⊔ S

/-- A submodule reduces to any submodule containing it. -/
lemma reducesInvariantsTo_of_le {V W : Submodule R B} (hVW : V ≤ W) :
    ReducesInvariantsTo σ V W :=
  fun S _ _ hx _ => sup_le_sup_right hVW S hx

/-- A reduction restricts to a smaller source. -/
lemma ReducesInvariantsTo.mono_left {V V' W : Submodule R B} (hP : ReducesInvariantsTo σ V' W)
    (hV : V ≤ V') : ReducesInvariantsTo σ V W :=
  fun S hS x hx hinv => hP S hS x (sup_le_sup_right hV S hx) hinv

/-- A reduction extends to a larger target. -/
lemma ReducesInvariantsTo.mono_right {V W W' : Submodule R B}
    (hP : ReducesInvariantsTo σ V W') (hW : W' ≤ W) : ReducesInvariantsTo σ V W :=
  fun S hS x hx hinv => sup_le_sup_right hW S (hP S hS x hx hinv)

/-- Successive reductions compose. -/
lemma ReducesInvariantsTo.trans {V W W' : Submodule R B} (hP : ReducesInvariantsTo σ V W)
    (hQ : ReducesInvariantsTo σ W W') : ReducesInvariantsTo σ V W' :=
  fun S hS x hx hinv => hQ S hS x (hP S hS x hx hinv) hinv

/-- Reductions of `V` and of a stable `V'` to a common stable target combine to a reduction of
  `V ⊔ V'`. -/
lemma ReducesInvariantsTo.sup {V V' W : Submodule R B} (hP : ReducesInvariantsTo σ V W)
    (hQ : ReducesInvariantsTo σ V' W) (hV' : IsStableUnder σ V') (hW : IsStableUnder σ W) :
    ReducesInvariantsTo σ (V ⊔ V') W := by
  intro S hS x hx hinv
  have h : x ∈ W ⊔ (V' ⊔ S) := hP (V' ⊔ S) (hV'.sup hS) x (by rwa [← sup_assoc]) hinv
  rw [sup_left_comm] at h
  have h' := hQ (W ⊔ S) (hW.sup hS) x h hinv
  rwa [← sup_assoc, sup_idem] at h'

/-- Reductions of stable submodules to a common stable target combine over a finite set. -/
lemma ReducesInvariantsTo.biSup {ι : Type*} [DecidableEq ι] {V : ι → Submodule R B}
    {W : Submodule R B} (hP : ∀ i, ReducesInvariantsTo σ (V i) W)
    (hV : ∀ i, IsStableUnder σ (V i)) (hW : IsStableUnder σ W) (s : Finset ι) :
    ReducesInvariantsTo σ (⨆ i ∈ s, V i) W := by
  induction s using Finset.induction_on with
  | empty => exact reducesInvariantsTo_of_le (by simp)
  | @insert a s _ ih =>
    rw [Finset.iSup_insert]
    exact (hP a).sup ih (isStableUnder_iSup fun i => isStableUnder_iSup fun _ => hV i) hW

/-- A reduction of every join over a finite set of indices is a reduction of the join over the
  whole index type, which may be infinite. An element of the join lies in the join over finitely
  many of the summands. No stability is assumed of the summands or of the target; the remainder
  is stable, as in every reduction. -/
lemma ReducesInvariantsTo.iSup_of_biSup {ι : Type*} {V : ι → Submodule R B} {W : Submodule R B}
    (hP : ∀ s : Finset ι, ReducesInvariantsTo σ (⨆ i ∈ s, V i) W) :
    ReducesInvariantsTo σ (⨆ i, V i) W := by
  intro S hS x hx hinv
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hu
  exact hP s S hS _ (Submodule.add_mem_sup hs hz) hinv

/-- Reductions of stable submodules to a common stable target combine over any index type,
  finite or not. `biSup` combines them over every finite set of indices, and
  `iSup_of_biSup` passes to the whole join. -/
lemma ReducesInvariantsTo.iSup {ι : Type*} {V : ι → Submodule R B} {W : Submodule R B}
    (hP : ∀ i, ReducesInvariantsTo σ (V i) W) (hV : ∀ i, IsStableUnder σ (V i))
    (hW : IsStableUnder σ W) : ReducesInvariantsTo σ (⨆ i, V i) W := by
  classical
  exact ReducesInvariantsTo.iSup_of_biSup (ReducesInvariantsTo.biSup hP hV hW)

/-- A reduction for the subfamily `σ ∘ ι` is a reduction for `σ`. An invariant of `σ` is an
  invariant of the subfamily, and a `σ`-stable submodule is stable under the subfamily. -/
lemma ReducesInvariantsTo.comp {G' : Type*} (ι : G' → G) {V W : Submodule R B}
    (hP : ReducesInvariantsTo (fun g' => σ (ι g')) V W) : ReducesInvariantsTo σ V W :=
  fun S hS x hx hinv => hP S (fun g' y hy => hS (ι g') y hy) x hx fun g' => hinv (ι g')

end Reduction

section Eigenvalue

variable {K B G : Type*} [Field K] [AddCommGroup B] [Module K B] {σ : G → B →ₗ[K] B}

/-- A submodule on which one map of the family acts by a scalar `μ ≠ 1` reduces to `⊥`. An
  invariant `v + s` of `V ⊔ S` has `(μ - 1) • v = s - σ g s`, which lies in `S`, and so does
  `v`. Of the stability of `S` only stability under `σ g` is used. -/
lemma reducesInvariantsTo_bot_of_apply_eq_smul (g : G) {μ : K} (hμ : μ ≠ 1)
    {V : Submodule K B} (hV : ∀ v ∈ V, σ g v = μ • v) : ReducesInvariantsTo σ V ⊥ := by
  intro S hS x hx hinv
  obtain ⟨v, hv, s, hs, rfl⟩ := Submodule.mem_sup.1 hx
  have hkey : (μ - 1) • v = s - σ g s := by
    have h := hinv g
    rw [map_add, hV v hv] at h
    linear_combination (norm := module) h
  have hvS : v ∈ S := by
    have h1 : (μ - 1) • v ∈ S := hkey ▸ S.sub_mem hs (hS g s hs)
    simpa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hμ)] using S.smul_mem (μ - 1)⁻¹ h1
  simpa using S.add_mem hvS hs

end Eigenvalue

/-!

## C. Reduction through a quotient

For a `σ`-stable `S`, the maps `S.mapQ S (σ g) _` act on `B ⧸ S`. The hypotheses below classify
invariants of that action on the image of the source, which is where a classification valid in
every module is applied.

-/

section Quotient

variable {R B G : Type*} [Ring R] [AddCommGroup B] [Module R B] {σ : G → B →ₗ[R] B}
  {S V W : Submodule R B}

/-- An invariant of `V ⊔ S` lies in `W ⊔ S` when every invariant of the image of `V` in
  `B ⧸ S` lies in the image of `W`. -/
lemma IsStableUnder.mem_sup_of_quotient (hS : IsStableUnder σ S)
    (hclass : ∀ x ∈ V.map S.mkQ, (∀ g, S.mapQ S (σ g) (hS g) x = x) → x ∈ W.map S.mkQ)
    {x : B} (hx : x ∈ V ⊔ S) (hinv : ∀ g, σ g x = x) : x ∈ W ⊔ S := by
  rw [sup_comm, ← Submodule.comap_map_mkQ, Submodule.mem_comap] at hx ⊢
  exact hclass _ hx fun g => by rw [Submodule.mkQ_apply, Submodule.mapQ_apply, hinv]

/-- `V` reduces to `W` when, for every stable `S`, every invariant of the image of `V` in
  `B ⧸ S` lies in the image of `W`. -/
lemma reducesInvariantsTo_of_quotient
    (hclass : ∀ S : Submodule R B, ∀ hS : IsStableUnder σ S, ∀ x ∈ V.map S.mkQ,
      (∀ g, S.mapQ S (σ g) (hS g) x = x) → x ∈ W.map S.mkQ) :
    ReducesInvariantsTo σ V W :=
  fun S hS _ hx hinv => hS.mem_sup_of_quotient (hclass S hS) hx hinv

/-- An invariant of `W ⊔ S`, for `W` pointwise fixed, is an element of `W` plus an invariant
  element of `S`. -/
lemma IsFixedBy.exists_add_of_mem_sup (hW : IsFixedBy σ W) {x : B} (hx : x ∈ W ⊔ S)
    (hinv : ∀ g, σ g x = x) : ∃ w ∈ W, ∃ y ∈ S, x = w + y ∧ ∀ g, σ g y = y := by
  obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
  refine ⟨w, hw, y, hy, rfl, fun g => add_left_cancel (a := w) ?_⟩
  have h := hinv g
  rwa [map_add, hW g w hw] at h

/-- A reduction of `V` to a pointwise-fixed `W ≤ V` describes the invariants of `V ⊔ S`, for
  `S` stable, exactly. They are the elements of `W` plus an invariant element of `S`. This is
  the form in which a classification is stated. -/
lemma ReducesInvariantsTo.mem_sup_and_forall_eq_self_iff (hP : ReducesInvariantsTo σ V W)
    (hWV : W ≤ V) (hW : IsFixedBy σ W) (hS : IsStableUnder σ S) (x : B) :
    (x ∈ V ⊔ S ∧ ∀ g, σ g x = x) ↔ ∃ y ∈ S, (∀ g, σ g y = y) ∧ x - y ∈ W := by
  constructor
  · rintro ⟨hx, hinv⟩
    obtain ⟨w, hw, y, hy, rfl, hyinv⟩ := hW.exists_add_of_mem_sup (hP S hS x hx hinv) hinv
    exact ⟨y, hy, hyinv, by simpa using hw⟩
  · rintro ⟨y, hy, hyinv, hxy⟩
    refine ⟨by simpa using Submodule.add_mem_sup (hWV hxy) hy, fun g => ?_⟩
    rw [← sub_add_cancel x y, map_add, hW g _ hxy, hyinv g]

/-- Quotient to remainder. When every invariant of the image of `V` in `B ⧸ S` lies in the
  image of a pointwise-fixed `W`, an invariant of `V ⊔ S` is an element of `W` plus an
  invariant element of `S`. -/
lemma IsStableUnder.exists_add_of_quotient (hS : IsStableUnder σ S) (hW : IsFixedBy σ W)
    (hclass : ∀ x ∈ V.map S.mkQ, (∀ g, S.mapQ S (σ g) (hS g) x = x) → x ∈ W.map S.mkQ)
    {x : B} (hx : x ∈ V ⊔ S) (hinv : ∀ g, σ g x = x) :
    ∃ w ∈ W, ∃ y ∈ S, x = w + y ∧ ∀ g, σ g y = y :=
  hW.exists_add_of_mem_sup (hS.mem_sup_of_quotient hclass hx hinv) hinv

end Quotient

/-!

## D. Reduction to the span of one vector

-/

section Span

variable {R B G : Type*} [Semiring R] [AddCommMonoid B] [Module R B] {σ : G → B →ₗ[R] B}

/-- A stable submodule `V` together with a fixed vector such that, for every stable `S`, every
  invariant of `V ⊔ S` is a multiple of that vector plus an element of `S`. The vector need not
  be nonzero or lie in `V`. -/
structure InvariantReductionToSpan (σ : G → B →ₗ[R] B) (V : Submodule R B) where
  /-- The vector whose span receives the invariants of `V`. -/
  spanningVector : B
  /-- The submodule is stable. -/
  stable : IsStableUnder σ V
  /-- The spanning vector is invariant. -/
  spanningVector_fixed : ∀ g, σ g spanningVector = spanningVector
  /-- An invariant of `V ⊔ S`, for `S` stable, is a multiple of the spanning vector plus an
    element of `S`. -/
  reduce : ∀ S : Submodule R B, IsStableUnder σ S → ∀ x ∈ V ⊔ S, (∀ g, σ g x = x) →
    ∃ c : R, ∃ y ∈ S, x = c • spanningVector + y

namespace InvariantReductionToSpan

variable {V : Submodule R B}

/-- The submodule reduces to the span of the spanning vector. -/
lemma reducesInvariantsTo (r : InvariantReductionToSpan σ V) :
    ReducesInvariantsTo σ V (R ∙ r.spanningVector) := by
  intro S hS x hx hinv
  obtain ⟨c, y, hy, rfl⟩ := r.reduce S hS x hx hinv
  exact Submodule.add_mem_sup (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)) hy

/-- A family of reductions to spans, over any index type, reduces the join of the submodules to
  the span of the spanning vectors. -/
lemma reducesInvariantsTo_iSup {κ : Type*} {V : κ → Submodule R B}
    (r : ∀ k, InvariantReductionToSpan σ (V k)) :
    ReducesInvariantsTo σ (⨆ k, V k)
      (Submodule.span R (Set.range fun k => (r k).spanningVector)) :=
  ReducesInvariantsTo.iSup
    (fun k => (r k).reducesInvariantsTo.mono_right
      (Submodule.span_mono (Set.singleton_subset_iff.2 ⟨k, rfl⟩)))
    (fun k => (r k).stable)
    (isFixedBy_span_range fun k => (r k).spanningVector_fixed).isStableUnder

/-- The span of a fixed vector reduces to itself. -/
def ofFixed (b : B) (hb : ∀ g, σ g b = b) :
    InvariantReductionToSpan σ (R ∙ b) where
  spanningVector := b
  stable := (isFixedBy_span_singleton hb).isStableUnder
  spanningVector_fixed := hb
  reduce S _ x hx _ := by
    obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
    exact ⟨c, y, hy, rfl⟩

/-- The span of a nonempty family whose members all equal one fixed vector reduces to the
  span of that vector. -/
def ofFixedFamily {ι : Type*} [Nonempty ι] {T : ι → B} (b : B)
    (hTb : ∀ i, T i = b) (hb : ∀ g, σ g b = b) :
    InvariantReductionToSpan σ (Submodule.span R (Set.range T)) :=
  have hspan : Submodule.span R (Set.range T) = R ∙ b := by
    rw [show T = fun _ => b from funext hTb, Set.range_const]
  { spanningVector := b
    stable := hspan ▸ (ofFixed b hb).stable
    spanningVector_fixed := hb
    reduce := hspan ▸ (ofFixed b hb).reduce }

end InvariantReductionToSpan

end Span

/-!

## E. A group together with the Lorentz group

A representation of a group `H` and a representation of `SL(2,ℂ)` on the same module are read
as a single family of linear maps, `gaugeLorentzMaps`, indexed by the disjoint union
`H ⊕ SL(2,ℂ)`. Its invariants are the elements fixed by both groups, and its stable submodules
are those stable under both. A reduction for `H` or for the Lorentz group alone is a reduction
for the family by `ReducesInvariantsTo.comp`.

-/

section BothGroups

open MatrixGroups

variable {H B : Type*} [Group H] [AddCommGroup B] [Module ℂ B]
  (repGauge : Representation ℂ H B) (repLorentz : Representation ℂ SL(2,ℂ) B)

/-- A representation of `H` and one of `SL(2,ℂ)` on the same module, read as a single family of
  linear maps indexed by the disjoint union of the two groups. -/
def gaugeLorentzMaps : H ⊕ SL(2,ℂ) → B →ₗ[ℂ] B :=
  Sum.elim (fun g => repGauge g) (fun Λ => repLorentz Λ)

variable {repGauge repLorentz}

/-- A submodule stable under both groups is stable under the combined family, and
  conversely. -/
lemma isStableUnder_gaugeLorentzMaps_iff {V : Submodule ℂ B} :
    IsStableUnder (gaugeLorentzMaps repGauge repLorentz) V
      ↔ (∀ g : H, ∀ y ∈ V, repGauge g y ∈ V) ∧ ∀ Λ : SL(2,ℂ), ∀ y ∈ V, repLorentz Λ y ∈ V := by
  constructor
  · exact fun hV => ⟨fun g => hV (Sum.inl g), fun Λ => hV (Sum.inr Λ)⟩
  · rintro ⟨hg, hL⟩ (g | Λ)
    · exact hg g
    · exact hL Λ

/-- An element fixed by both groups is fixed by the combined family, and conversely. -/
lemma forall_gaugeLorentzMaps_eq_self_iff {x : B} :
    (∀ p, gaugeLorentzMaps repGauge repLorentz p x = x)
      ↔ (∀ g : H, repGauge g x = x) ∧ ∀ Λ : SL(2,ℂ), repLorentz Λ x = x := by
  constructor
  · exact fun hx => ⟨fun g => hx (Sum.inl g), fun Λ => hx (Sum.inr Λ)⟩
  · rintro ⟨hg, hL⟩ (g | Λ)
    · exact hg g
    · exact hL Λ

/-- A submodule fixed pointwise by both groups is fixed pointwise by the combined family, and
  conversely. -/
lemma isFixedBy_gaugeLorentzMaps_iff {V : Submodule ℂ B} :
    IsFixedBy (gaugeLorentzMaps repGauge repLorentz) V
      ↔ (∀ g : H, ∀ y ∈ V, repGauge g y = y) ∧ ∀ Λ : SL(2,ℂ), ∀ y ∈ V, repLorentz Λ y = y := by
  constructor
  · exact fun hV => ⟨fun g => hV (Sum.inl g), fun Λ => hV (Sum.inr Λ)⟩
  · rintro ⟨hg, hL⟩ (g | Λ)
    · exact hg g
    · exact hL Λ

/-- The endpoint `ReducesInvariantsTo.mem_sup_and_forall_eq_self_iff` for the two groups
  together, with the two invariances and the two stabilities stated separately. -/
lemma ReducesInvariantsTo.mem_sup_and_gauge_lorentz_invariant_iff {V W S : Submodule ℂ B}
    (hP : ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) V W) (hWV : W ≤ V)
    (hW : IsFixedBy (gaugeLorentzMaps repGauge repLorentz) W)
    (hS : ∀ g : H, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ Λ : SL(2,ℂ), ∀ y ∈ S, repLorentz Λ y ∈ S) (x : B) :
    (x ∈ V ⊔ S ∧ (∀ g : H, repGauge g x = x) ∧ ∀ Λ : SL(2,ℂ), repLorentz Λ x = x)
      ↔ ∃ y ∈ S, (∀ g : H, repGauge g y = y)
          ∧ (∀ Λ : SL(2,ℂ), repLorentz Λ y = y) ∧ x - y ∈ W := by
  simpa only [forall_gaugeLorentzMaps_eq_self_iff, and_assoc] using
    hP.mem_sup_and_forall_eq_self_iff hWV hW (isStableUnder_gaugeLorentzMaps_iff.2 ⟨hS, hSL⟩) x

/-- A reduction for `H` is a reduction for the two groups together. -/
lemma ReducesInvariantsTo.ofGauge {V W : Submodule ℂ B}
    (hP : ReducesInvariantsTo (fun g : H => repGauge g) V W) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) V W :=
  ReducesInvariantsTo.comp (Sum.inl (β := SL(2,ℂ))) hP

/-- A Lorentz reduction is a reduction for the two groups together. -/
lemma ReducesInvariantsTo.ofLorentz {V W : Submodule ℂ B}
    (hP : ReducesInvariantsTo (fun Λ : SL(2,ℂ) => repLorentz Λ) V W) :
    ReducesInvariantsTo (gaugeLorentzMaps repGauge repLorentz) V W :=
  ReducesInvariantsTo.comp (Sum.inr (α := H)) hP

end BothGroups

section Multiplicative

open MatrixGroups

variable {H B : Type*} [Group H] [Ring B] [Algebra ℂ B] {repGauge : Representation ℂ H B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- The two groups read as one family of maps respect multiplication, each of the two
  representations doing so. -/
lemma gaugeLorentzMaps_mul
    (hG : ∀ (g : H) (b₁ b₂ : B), repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂)
    (hL : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
      repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂)
    (p : H ⊕ SL(2,ℂ)) (a b : B) :
    gaugeLorentzMaps repGauge repLorentz p (a * b)
      = gaugeLorentzMaps repGauge repLorentz p a * gaugeLorentzMaps repGauge repLorentz p b := by
  cases p with
  | inl g => exact hG g a b
  | inr Λ => exact hL Λ a b

end Multiplicative
