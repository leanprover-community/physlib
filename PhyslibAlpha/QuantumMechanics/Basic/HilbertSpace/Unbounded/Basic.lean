/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Operators.SpectralTheory.SpectralMeasure
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology

/-!

# Weak-operator-topology spectral measures

`Physlib.QuantumMechanics.Operators.SpectralTheory.SpectralMeasure` already gives a
star-projection-valued measure `Set α → H →L[ℂ] H`, σ-additive in the *norm* topology on bounded
operators. That norm additivity is too strong a requirement for the spectral measures produced by
the (still-to-come) unbounded spectral theorem: an unbounded self-adjoint operator's spectral
projections need only add up weakly, on each pair of test vectors, not in operator norm. This file
gives that weaker notion its own type, `WOTSpectralMeasure`, valued in Mathlib's weak-operator-
topology copy of the bounded operators, `H →WOT[ℂ] H` (`Mathlib.Analysis.InnerProductSpace.
WeakOperatorTopology`).

`WOTSpectralMeasure` is otherwise a verbatim analogue of `SpectralMeasure`: same structure shape
(`VectorMeasure` plus "every value is a star projection" plus "`univ ↦ 1`"), same basic algebra
(idempotence, orthogonality on disjoint sets, intersection multiplicativity, commutativity). The
two cannot share a definition because they are literally valued in different types (`H →L[ℂ] H`
vs. `H →WOT[ℂ] H` carry the same ring structure but different topologies, hence different
`VectorMeasure` targets) — but `SpectralMeasure.toWOT`, at the end of this file, is the coercion
that turns any norm-continuous `SpectralMeasure` into a `WOTSpectralMeasure` for free, so nothing
built on `SpectralMeasure` elsewhere in this codebase needs re-deriving to be usable here.

This file also records the covariance of the type under a measurable pushforward of the
underlying measurable space (`map`) — needed to move a spectral measure along a change of
spectral variable, e.g. through the Cayley transform.

## Main definitions

- `WOTSpectralMeasure` : a star-projection-valued measure, σ-additive in the weak-operator
  topology.
- `comp_eq_of_inter` : `μS A * μS B = μS (A ∩ B)` for measurable `A`, `B`.
- `map` : pushing a weak spectral measure forward along a measurable function.
- `SpectralMeasure.toWOT` : a norm-continuous spectral measure, viewed weakly.

-/

@[expose] public section

noncomputable section

open scoped Topology InnerProductSpace Function
open ContinuousLinearMap ContinuousLinearMapWOT MeasureTheory Set

namespace QuantumMechanics

@[nolint unusedArguments]
instance (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    IsAddTorsionFree (H →WOT[ℂ] H) where
  nsmul_right_injective n hn := by
    refine Function.HasLeftInverse.injective ⟨fun f ↦ (n : ℂ)⁻¹ • f, fun x ↦ ?_⟩
    simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_ne_zero (R := ℂ), hn]

/-!
## A. The structure and its basic algebra
-/

/-- A projection-valued measure with weak-operator σ-additivity: like `SpectralMeasure`, but the
underlying `VectorMeasure` is valued in the weak-operator-topology copy `H →WOT[ℂ] H` of the
bounded operators rather than in `H →L[ℂ] H` with its norm topology. -/
structure WOTSpectralMeasure
    (α : Type*) [MeasurableSpace α]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    extends VectorMeasure α (H →WOT[ℂ] H) where
  isStarProjection' : ∀ A, IsStarProjection (measureOf' A)
  univ' : measureOf' univ = 1

namespace WOTSpectralMeasure

variable {α : Type*} [MeasurableSpace α]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μS : WOTSpectralMeasure α H)

attribute [coe] toVectorMeasure

instance instCoeVectorMeasure : Coe (WOTSpectralMeasure α H)
    (VectorMeasure α (H →WOT[ℂ] H)) := ⟨toVectorMeasure⟩

instance instCoeFun : CoeFun (WOTSpectralMeasure α H) fun _ ↦ Set α → H →WOT[ℂ] H :=
  ⟨fun μS ↦ ⇑μS.toVectorMeasure⟩

lemma isStarProjection (A : Set α) : IsStarProjection (μS A) := μS.isStarProjection' A

@[simp]
lemma univ : μS univ = 1 := μS.univ'

lemma apply_eq_zero_of_not_measurableSet {A : Set α} (hA : ¬MeasurableSet A) : μS A = 0 :=
  μS.not_measurable' hA

lemma comp_self (A : Set α) : μS A * μS A = μS A :=
  (μS.isStarProjection A).isIdempotentElem

lemma comp_of_disjoint {A B : Set α} (h : Disjoint A B) (hA : MeasurableSet A)
    (hB : MeasurableSet B) : μS A * μS B = 0 := by
  have hp : μS A * μS (A ∪ B) = μS A := by
    refine (IsStarProjection.sub_iff_mul_eq_left (μS.isStarProjection A)
      (μS.isStarProjection (A ∪ B))).mp ?_
    simpa [μS.of_union h hA hB] using μS.isStarProjection B
  rw [μS.of_union h hA hB, mul_add, μS.comp_self] at hp
  apply add_left_cancel (a := μS A)
  simpa using hp

lemma comp_eq_of_inter {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μS A * μS B = μS (A ∩ B) := by
  nth_rw 1 [← inter_union_sdiff B A, ← inter_union_sdiff A B]
  simp only [μS.of_union, hA.inter hB, hB.inter hA, hA.diff hB, hB.diff hA,
    disjoint_sdiff_inter.symm, add_mul, mul_add]
  rw [inter_comm B A, μS.comp_of_disjoint disjoint_sdiff_inter (hA.diff hB) (hA.inter hB),
    inter_comm A B, μS.comp_of_disjoint disjoint_sdiff_inter.symm (hB.inter hA) (hB.diff hA)]
  simp [μS.comp_self, μS.comp_of_disjoint disjoint_sdiff_sdiff (hA.diff hB) (hB.diff hA)]

lemma commute (A B : Set α) : Commute (μS A) (μS B) := by
  by_cases hAB : MeasurableSet A ∧ MeasurableSet B
  · simp [commute_iff_eq, comp_eq_of_inter, hAB, inter_comm]
  · rcases not_and_or.mp hAB with hA | hB <;> simp [*]

/-! ## B. Pushforward along a measurable map -/

/-- Push a weak spectral measure forward along a measurable change of spectral variable. -/
def map {β : Type*} [MeasurableSpace β] (f : α → β) (hf : Measurable f) :
    WOTSpectralMeasure β H where
  toVectorMeasure := μS.toVectorMeasure.map f
  isStarProjection' S := by
    change IsStarProjection ((μS.toVectorMeasure.map f) S)
    by_cases hS : MeasurableSet S
    · rw [MeasureTheory.VectorMeasure.map_apply _ hf hS]
      exact μS.isStarProjection _
    · simp [MeasureTheory.VectorMeasure.map, hf, hS]
  univ' := by
    change (μS.toVectorMeasure.map f) Set.univ = 1
    rw [MeasureTheory.VectorMeasure.map_apply _ hf MeasurableSet.univ]
    simp

@[simp]
lemma map_apply {β : Type*} [MeasurableSpace β] (f : α → β) (hf : Measurable f)
    {S : Set β} (hS : MeasurableSet S) :
    μS.map f hf S = μS (f ⁻¹' S) := by
    change (μS.toVectorMeasure.map f) S = μS (f ⁻¹' S)
    exact MeasureTheory.VectorMeasure.map_apply _ hf hS

lemma map_map_apply {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (f : α → β) (g : β → γ) (hf : Measurable f) (hg : Measurable g)
    {S : Set γ} (hS : MeasurableSet S) :
    (μS.map f hf).map g hg S = μS ((g ∘ f) ⁻¹' S) := by
  rw [(μS.map f hf).map_apply g hg hS, μS.map_apply f hf (hg hS)]
  rfl

theorem map_map {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (f : α → β) (g : β → γ) (hf : Measurable f) (hg : Measurable g) :
    (μS.map f hf).map g hg = μS.map (g ∘ f) (hg.comp hf) := by
  rw [WOTSpectralMeasure.mk.injEq]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  rw [μS.map_map_apply f g hf hg hS, μS.map_apply (g ∘ f) (hg.comp hf) hS]

theorem map_id : μS.map id measurable_id = μS := by
  rw [WOTSpectralMeasure.mk.injEq]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  rw [μS.map_apply id measurable_id hS]
  rfl

/-- The σ-additivity statement seen by vectors and test vectors. This is often more convenient
than mentioning the `WOT` type directly when proving spectral formulas. -/
lemma hasSum_inner {f : ℕ → Set α} (hf : ∀ i, MeasurableSet (f i))
    (hdisj : Pairwise (Disjoint on f)) (x y : H) :
    HasSum (fun i ↦ ⟪y, μS (f i) x⟫_ℂ) ⟪y, μS (⋃ i, f i) x⟫_ℂ := by
  have h := μS.toVectorMeasure.m_iUnion hf hdisj
  let g : (H →WOT[ℂ] H) →+ ℂ :=
    { toFun := fun T ↦ ⟪y, T x⟫_ℂ
      map_zero' := by simp
      map_add' := by
        intro T U
        change ⟪y, T x + U x⟫_ℂ = _
        rw [inner_add_right] }
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  change HasSum (fun i ↦ g (μS (f i))) (g (μS (⋃ i, f i)))
  exact h.map g hg

end WOTSpectralMeasure

end QuantumMechanics

/-!
## C. Coming from a norm-continuous `SpectralMeasure`
-/

namespace SpectralMeasure

open QuantumMechanics

variable {α : Type*} [MeasurableSpace α]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Forgetting norm σ-additivity and retaining weak-operator σ-additivity. -/
def toWOTMap : (H →L[ℂ] H) →+ (H →WOT[ℂ] H) :=
  { toFun := ContinuousLinearMapWOT.ofCLM
    map_zero' := by simp
    map_add' := by intro S T; simp }

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma continuous_toWOTMap : Continuous (toWOTMap (H := H)) := by
  change Continuous (ContinuousLinearMapWOT.ofCLM :
    (H →L[ℂ] H) → (H →WOT[ℂ] H))
  exact ContinuousLinearMapWOT.continuous_ofCLM

/-- A `SpectralMeasure`, viewed in the weak-operator-topology type `H →WOT[ℂ] H`. -/
def toWOT (μS : SpectralMeasure α H) : WOTSpectralMeasure α H where
  toVectorMeasure := by
    exact μS.toVectorMeasure.mapRange (toWOTMap (H := H))
      (continuous_toWOTMap (H := H))
  isStarProjection' A := by
    change IsStarProjection (ContinuousLinearMapWOT.ofCLM (μS A))
    refine ⟨?_, ?_⟩
    · change ContinuousLinearMapWOT.ofCLM (μS A) *
        ContinuousLinearMapWOT.ofCLM (μS A) = ContinuousLinearMapWOT.ofCLM (μS A)
      rw [← ContinuousLinearMapWOT.ofCLM_mul]
      exact congrArg ContinuousLinearMapWOT.ofCLM
        (μS.isStarProjection A).isIdempotentElem
    · apply ContinuousLinearMapWOT.toCLM_injective
      change star (μS A) = μS A
      exact (μS.isStarProjection A).isSelfAdjoint
  univ' := by
    change ContinuousLinearMapWOT.ofCLM (μS Set.univ) = 1
    rw [SpectralMeasure.univ μS]
    simp

@[simp]
lemma toWOT_apply (μS : SpectralMeasure α H) (A : Set α) : μS.toWOT A =
    ContinuousLinearMapWOT.ofCLM (μS A) := by
  change (μS.toVectorMeasure.mapRange (toWOTMap (H := H))
      (continuous_toWOTMap (H := H))) A = _
  rw [MeasureTheory.VectorMeasure.mapRange_apply]
  rfl

end SpectralMeasure

end
