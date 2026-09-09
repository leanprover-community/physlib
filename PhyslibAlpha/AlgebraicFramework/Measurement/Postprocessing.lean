/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.Measurement.FiniteOutcome

/-!

# Postprocessing a finite-outcome measurement

A classical channel that relabels, coarse-grains, or adds noise to the outcomes of a measurement
— from raw outcomes `ι` to coarse outcomes `κ` — is, in the same Heisenberg convention as every
other channel here, a positive unital linear map `K : (κ → ℝ) →ₚ₁[ℝ] (ι → ℝ)`: it pulls functions
of the coarse outcome back to functions of the raw one. Given a measurement `M : (ι → ℝ) →ₚ₁[ℝ] E`,
its postprocessing through `K` is `M.comp K`, already meaningful with no new definition needed —
this is the entire point of presenting measurements as channels (`FiniteOutcome.lean`):
postprocessing is composition.

`stochasticMatrixEquiv` identifies such classical channels concretely: `ι → ℝ` is itself a
classical order-unit space (`ClassicalSystem.lean`), so `channelEquiv` applies to it verbatim, and
uncurrying its family of effects turns a classical channel into exactly what one would expect —
a row-stochastic matrix, a probability distribution over `κ` for every raw outcome in `ι`.

A deterministic relabeling `f : κ → ι` of outcomes — no randomness, just reading off `f k` — gives
the simplest classical channel of all, `classicalPullback f`; `Compatibility.lean` builds the
coordinate projections of a product outcome type out of it.

## Main definitions

- `Measurement.postprocess`, `Measurement.postprocess_postprocess`
- `Measurement.stochasticMatrixEquiv`
- `Measurement.classicalPullback`

-/

@[expose] public section

variable {E ι κ : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [PosSMulMono ℝ E] [One E] [IsOrderUnit E]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

namespace Measurement

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] in
/-- Postprocessing a measurement through a classical channel `κ → ι` is just composition: reading
measurements as channels makes postprocessing free, with no separate notion to build. -/
def postprocess (M : (ι → ℝ) →ₚ₁[ℝ] E) (K : (κ → ℝ) →ₚ₁[ℝ] (ι → ℝ)) : (κ → ℝ) →ₚ₁[ℝ] E :=
  M.comp K

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] in
@[simp]
lemma postprocess_apply (M : (ι → ℝ) →ₚ₁[ℝ] E) (K : (κ → ℝ) →ₚ₁[ℝ] (ι → ℝ)) (f : κ → ℝ) :
    postprocess M K f = M (K f) :=
  rfl

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] [Fintype ι] [DecidableEq ι] in
/-- Postprocessing through the identity channel changes nothing. -/
@[simp]
lemma postprocess_id (M : (ι → ℝ) →ₚ₁[ℝ] E) :
    postprocess M (.id ℝ (ι → ℝ)) = M :=
  UnitalPositiveLinearMap.comp_id M

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] in
/-- Postprocessing twice, through `K` then `L`, is postprocessing once through their composite:
postprocessing is a genuine (contravariant) action of classical channels on measurements. -/
lemma postprocess_postprocess {μ : Type*}
    (M : (ι → ℝ) →ₚ₁[ℝ] E) (K : (κ → ℝ) →ₚ₁[ℝ] (ι → ℝ)) (L : (μ → ℝ) →ₚ₁[ℝ] (κ → ℝ)) :
    postprocess (postprocess M K) L = postprocess M (K.comp L) :=
  UnitalPositiveLinearMap.ext fun _ => rfl

/-- Uncurrying a `κ`-indexed family of effects in the classical system `ι → ℝ` summing to `1`
into a row-stochastic matrix: `packEquiv` just swaps which index is bundled into the effect and
which is left free, so both directions are `rfl` once unfolded. -/
def packEquiv :
    {e : κ → Effect (ι → ℝ) // ∑ k, (e k : ι → ℝ) = 1} ≃
      {P : ι → κ → ℝ // ∀ i, (∀ k, 0 ≤ P i k) ∧ ∑ k, P i k = 1} where
  toFun p := ⟨fun i k => (p.1 k : ι → ℝ) i,
    fun i => ⟨fun k => (p.1 k).2.1 i, by simpa using congrFun p.2 i⟩⟩
  invFun P := ⟨fun k => ⟨fun i => P.1 i k, fun i => (P.2 i).1 k,
      fun i => (Finset.single_le_sum (fun k _ => (P.2 i).1 k) (Finset.mem_univ k)).trans_eq
        (P.2 i).2⟩,
    by
      funext i
      simp only [Finset.sum_apply, Pi.one_apply]
      exact (P.2 i).2⟩
  left_inv p := by apply Subtype.ext; funext k; exact Subtype.ext rfl
  right_inv P := by apply Subtype.ext; funext i k; rfl

/-- A classical channel from raw outcomes `ι` to coarse outcomes `κ` is exactly a row-stochastic
matrix: for every raw outcome `i`, a probability distribution `k ↦ P i k` over `κ`. This
specializes `channelEquiv` to the classical system `ι → ℝ` in place of a general `E`, then
uncurries the resulting family of effects into a matrix via `packEquiv`. -/
noncomputable def stochasticMatrixEquiv :
    ((κ → ℝ) →ₚ₁[ℝ] (ι → ℝ)) ≃ {P : ι → κ → ℝ // ∀ i, (∀ k, 0 ≤ P i k) ∧ ∑ k, P i k = 1} :=
  (channelEquiv (ι := κ) (E := ι → ℝ)).trans packEquiv

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] in
/-- The deterministic classical channel reading off outcome `f k`: pulling a function of the
coarse outcome `ι` back along `f : κ → ι` to a function of the raw outcome `κ`. The corresponding
stochastic matrix is the one-hot family `P i k = if f k = i then 1 else 0`. -/
def classicalPullback (f : κ → ι) : (ι → ℝ) →ₚ₁[ℝ] (κ → ℝ) :=
  UnitalPositiveLinearMap.ofLinearMap (LinearMap.funLeft ℝ ℝ f) (fun _ hg k => hg (f k)) rfl

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] in
@[simp]
lemma classicalPullback_id :
    classicalPullback (id : ι → ι) = UnitalPositiveLinearMap.id ℝ (ι → ℝ) :=
  UnitalPositiveLinearMap.ext fun _ => rfl

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] in
/-- Pulling back along `f` then along `g` is pulling back along `f ∘ g` once: `classicalPullback`
is a contravariant functor from outcome types and relabelings to classical channels. -/
lemma classicalPullback_comp {μ : Type*} (f : κ → ι) (g : μ → κ) :
    (classicalPullback g).comp (classicalPullback f) = classicalPullback (f ∘ g) :=
  UnitalPositiveLinearMap.ext fun _ => rfl

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] in
@[simp]
lemma classicalPullback_apply (f : κ → ι) (g : ι → ℝ) (k : κ) :
    classicalPullback f g k = g (f k) :=
  rfl

end Measurement
