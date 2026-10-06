/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Classical.BauerSimplex
public import PhyslibAlpha.Mathematics.Geometry.Simplex

/-!
# Finite classical systems

A finite-dimensional system is classical exactly when its state space is a geometric simplex.

## i. Overview

A system with finitely many independent observables is classical exactly when its state space is a
geometric simplex. A geometric simplex is the convex hull of finitely many affinely independent
points, its corners. The corners are the pure states. Every state is a mixture of them with unique
weights, its barycentric coordinates.

One direction is direct. Finitely many pure states form a closed set, so every state has a pure
decomposition, and affine independence fixes the weights. For the other direction, refinement of
ensembles makes the pure states affinely independent. In finite dimension there are then only
finitely many of them, and by the Krein–Milman theorem they span the state space.

## ii. Key results

- `PureState.isSimplexStateSpace_of_isSimplex` proves that a geometric simplex of states is
  classical.
- `EnsemblesRefine.affineIndependent_extremePoints` proves that, when ensembles refine, the pure
  states are affinely independent.
- `isSimplexStateSpace_iff_isSimplex` proves that a finite system is classical exactly when its
  state space is a geometric simplex.

## iii. Table of contents

- A. Geometric simplices decompose uniquely
- B. Simplices are geometric simplices

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

open StateSpace

open MeasureTheory ArchimedeanOrderUnitSpace Set
open scoped NNReal

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

/-!

## A. Geometric simplices decompose uniquely

-/

namespace PureState

variable (h : IsSimplex (stateSpace E))
include h

/-- If the state space is a geometric simplex, there are finitely many pure states. -/
lemma finite_setOf_isPure : {φ : stateSpace E | (toState φ).IsPure}.Finite :=
  (h.finite.preimage Subtype.val_injective.injOn).subset fun φ hφ =>
    (StateSpace.isPure_iff_mem_extremePoints φ).1 hφ

/-- If the state space is a geometric simplex, its pure states are affinely independent. -/
lemma affineIndependent_of_isSimplex :
    AffineIndependent ℝ fun k : PureState E => (k.1 : WeakDual ℝ E) := by
  let f : PureState E ↪ (stateSpace E).extremePoints ℝ :=
    ⟨fun k => ⟨(k.1 : WeakDual ℝ E), (StateSpace.isPure_iff_mem_extremePoints k.1).1 k.2⟩,
      fun k l hkl => Subtype.ext (Subtype.ext (congrArg Subtype.val hkl :))⟩
  exact h.affineIndependent.comp_embedding f

omit h in
/-- A probability measure on finitely many pure states writes its barycenter as the mixture of the
pure states weighted by their masses. -/
lemma affineCombination_measureReal [Fintype (PureState E)] {μ : Measure (PureState E)}
    [IsProbabilityMeasure μ] {ω : 𝓢[ℝ, E]} (hμ : ∀ f, ∫ k, toState k.1 f ∂μ = ω f) :
    Finset.univ.affineCombination ℝ (fun k : PureState E => (k.1 : WeakDual ℝ E))
        (fun k => μ.real {k}) =
      ((StateSpace.ofState ω) : WeakDual ℝ E) := by
  rw [Finset.affineCombination_eq_linear_combination _ _ _
    (by rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ])]
  refine DFunLike.ext _ _ fun f => ?_
  change (∑ k : PureState E, μ.real {k} • (toState k.1).toStrongDual) f = ω f
  rw [← hμ f, integral_fintype (PureState.integrable μ f)]
  simp [UnitalPositiveLinearMap.toStrongDual_apply]

/-- On a geometric simplex, a state has at most one decomposition into pure states. -/
lemma eq_of_isSimplex [Fintype (PureState E)] {μ ν : Measure (PureState E)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {ω : 𝓢[ℝ, E]}
    (hμ : ∀ f, ∫ k, toState k.1 f ∂μ = ω f) (hν : ∀ f, ∫ k, toState k.1 f ∂ν = ω f) : μ = ν := by
  have hw := (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ _).1
    (affineIndependent_of_isSimplex h) (fun k => μ.real {k}) (fun k => ν.real {k})
    (by rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ])
    (by rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ])
    ((affineCombination_measureReal hμ).trans (affineCombination_measureReal hν).symm)
  refine Measure.ext_iff_singleton.2 fun k => ?_
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 (congrFun hw k)

/-- **A geometric simplex of states is a simplex**: every state decomposes uniquely into pure
states. -/
lemma isSimplexStateSpace_of_isSimplex : IsSimplexStateSpace E := fun ω => by
  have : CompactSpace (PureState E) :=
    isCompact_iff_compactSpace.1 (finite_setOf_isPure h).isCompact
  have : Finite (PureState E) := (finite_setOf_isPure h).to_subtype
  have := Fintype.ofFinite (PureState E)
  obtain ⟨μ, hμr, hμp, hμ⟩ := hasPureDecomposition ω
  exact ⟨μ, ⟨hμr, hμp, hμ⟩, fun ν ⟨_, hνp, hν⟩ => eq_of_isSimplex h hν hμ⟩

end PureState

/-!

## B. Simplices are geometric simplices

-/

/-- Equal mixtures of states in the weak dual are equal mixtures of weighted states. -/
lemma sum_weighted_eq_of_sum_smul_eq {ι : Type*} {s : Finset ι} {φ : ι → stateSpace E}
    {w₁ w₂ : ι → ℝ} (h₁ : ∀ i ∈ s, 0 ≤ w₁ i) (h₂ : ∀ i ∈ s, 0 ≤ w₂ i)
    (hw : ∑ i ∈ s, w₁ i • ((φ i) : WeakDual ℝ E) = ∑ i ∈ s, w₂ i • ((φ i) : WeakDual ℝ E)) :
    ∑ i : s, (toState (φ i)).weighted ⟨w₁ i, h₁ i i.2⟩ =
      ∑ i : s, (toState (φ i)).weighted ⟨w₂ i, h₂ i i.2⟩ := by
  refine PositiveLinearMap.ext fun f => ?_
  have := congrArg (fun x : WeakDual ℝ E => x f) hw
  change (∑ i ∈ s, w₁ i • (toState (φ i)).toStrongDual) f =
    (∑ i ∈ s, w₂ i • (toState (φ i)).toStrongDual) f at this
  simp only [sum_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    UnitalPositiveLinearMap.toStrongDual_apply] at this
  rw [sum_apply, sum_apply]
  change ∑ i : s, w₁ i * toState (φ i) f = ∑ i : s, w₂ i * toState (φ i) f
  rwa [Finset.sum_coe_sort s fun i => w₁ i * toState (φ i) f,
    Finset.sum_coe_sort s fun i => w₂ i * toState (φ i) f]

/-- When ensembles refine, the pure states are affinely independent. -/
lemma EnsemblesRefine.affineIndependent_extremePoints (hE : EnsemblesRefine E) :
    AffineIndependent ℝ
      (Subtype.val : (stateSpace E).extremePoints ℝ → WeakDual ℝ E) := by
  let φ (x : (stateSpace E).extremePoints ℝ) : stateSpace E := ⟨x, x.2.1⟩
  refine affineIndependent_of_convexCombination_eq fun s w₁ w₂ h₁ h₂ _ _ hw i hi => ?_
  have hinj : Function.Injective fun x : s => toState (φ x.1) := fun x y hxy =>
    Subtype.ext (Subtype.ext (congrArg Subtype.val (StateSpace.toState_injective hxy) :))
  have := hE.eq_of_sum_weighted_eq
    (fun x : s => (StateSpace.isPure_iff_mem_extremePoints (φ x.1)).2 x.1.2) hinj
    (sum_weighted_eq_of_sum_smul_eq (φ := φ) h₁ h₂ hw)
  exact congrArg (fun a => (a ⟨i, hi⟩ : ℝ)) this

/-- On a simplex with finitely many independent observables, the state space is a geometric
simplex. -/
lemma IsSimplexStateSpace.isSimplex [FiniteDimensional ℝ E] (h : IsSimplexStateSpace E) :
    IsSimplex (stateSpace E) := by
  have hind := h.ensemblesRefine.affineIndependent_extremePoints
  have : FiniteDimensional ℝ (WeakDual ℝ E) :=
    inferInstanceAs (FiniteDimensional ℝ (StrongDual ℝ E))
  have hfin := (finiteDimensional_iff_setFinite ℝ hind).1 inferInstance
  have : LocallyConvexSpace ℝ (WeakDual ℝ E) := WeakBilin.locallyConvexSpace
  refine ⟨hfin, ?_, hind⟩
  have hc : IsClosed (convexHull ℝ ((stateSpace E).extremePoints ℝ)) :=
    (hfin.isCompact_convexHull ℝ).isClosed
  rw [← hc.closure_eq]
  exact (closure_convexHull_extremePoints isCompact_stateSpace
    convex_stateSpace).symm

/-- **Finite simplices**: for finitely many independent observables, the state space is a simplex
exactly when it is the convex hull of finitely many affinely independent pure states. -/
lemma isSimplexStateSpace_iff_isSimplex [FiniteDimensional ℝ E] :
    IsSimplexStateSpace E ↔ IsSimplex (stateSpace E) :=
  ⟨IsSimplexStateSpace.isSimplex, PureState.isSimplexStateSpace_of_isSimplex⟩

/-- A state space affinely equivalent to a standard simplex is a simplex. -/
lemma isSimplexStateSpace_of_affineEquiv_stdSimplexSet {ι : Type*} [Fintype ι]
    (e : WeakDual ℝ E ≃ᵃ[ℝ] (ι → ℝ)) (he : e '' stateSpace E = stdSimplexSet ι) :
    IsSimplexStateSpace E :=
  PureState.isSimplexStateSpace_of_isSimplex (isSimplex_of_affineEquiv_stdSimplexSet e he)

end ProbabilisticTheory
