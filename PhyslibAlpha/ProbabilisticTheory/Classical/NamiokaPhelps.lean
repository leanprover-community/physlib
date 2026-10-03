/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Classical.Basic
public import PhyslibAlpha.ProbabilisticTheory.Examples.Square
public import PhyslibAlpha.ProbabilisticTheory.Classical.Compatibility

/-!
# Classical theories compose uniquely with the square

Namioka–Phelps square test: classical exactly when composition with the square is unique.

## i. Overview

When a system is combined with another, the parts do not decide which composite observables are
nonnegative. The minimal choice admits only sums of products of nonnegative observables; the maximal
choice admits everything that local preparations keep nonnegative. For a classical system the two
coincide: there is only one way to compose it.

It suffices to test composition with the square, the simplest nonclassical state space. A composite
observable of `E` with the square is given by its four vertex values in `E`. It is in the maximal
cone when all four values are nonnegative, and in the minimal cone when the values are the facet
sums of four nonnegative observables of `E`. Solving for these four observables is exactly a Riesz
decomposition in `E`. So composition with the square is unique exactly when `E` has the Riesz
decomposition; for complete observables this means that the state space is a Choquet simplex, and
that every two yes/no measurements are compatible.

## ii. Key results

- `IsNuclear.isClassical` : a nuclear system is classical.
- `minTensorCone_eq_maxTensorCone_square_iff` : composition with the square is unique exactly when
  the observables have the Riesz decomposition.
- `isClassical_of_minTensorCone_eq_square` : if composition with the square is unique, the
  positive functionals form a lattice.
- `isClassical_iff_minTensorCone_eq_square` : **Namioka–Phelps square test**: on a complete
  Archimedean order-unit space, the state space is a Choquet simplex exactly when composition with
  the square is unique.
- `jointlyMeasurable_iff_minTensorCone_eq_square` : every two yes/no measurements are compatible
  exactly when composition with the square is unique.

## iii. Table of contents

- A. Facet coordinates of the minimal cone
- B. Nuclear systems are classical
- C. The square test
- D. Classicality

## iv. References

- I. Namioka and R. R. Phelps, *Tensor products of compact convex sets*, Pacific J. Math. 31 (1969),
  469–480.

-/

@[expose] public section

namespace ProbabilisticTheory

open TensorProduct Square

variable {E : Type*} [OrderUnitSpace E]

/-! ## A. Facet coordinates of the minimal cone -/

/-- Vertex values that are the facet sums of four nonnegative observables. -/
def IsFacetSum (A : Fin 4 → E) : Prop :=
  ∃ X : Fin 4 → E, (∀ j, 0 ≤ X j) ∧ A = ![X 2 + X 3, X 0 + X 3, X 1 + X 2, X 0 + X 1]

lemma vals_sum_tmul_facet (X : Fin 4 → E) :
    vals (∑ j, X j ⊗ₜ[ℝ] facet j) = ![X 2 + X 3, X 0 + X 3, X 1 + X 2, X 0 + X 1] := by
  ext i
  fin_cases i <;> simp [Fin.sum_univ_four, facet, add_comm]

/-- The vertex values of a composite observable in the minimal cone are facet sums. -/
lemma isFacetSum_vals {z : E ⊗[ℝ] Square} (hz : z ∈ minTensorCone E Square) :
    IsFacetSum (vals z) := by
  refine minTensorCone_induction (p := fun z => IsFacetSum (vals z)) hz ?_ ?_ ?_ ?_
  · intro x q hx hq
    obtain ⟨c, hc, rfl⟩ := exists_eq_sum_facet hq
    refine ⟨fun j => c j • x, fun j => smul_nonneg (hc j) hx, ?_⟩
    rw [← vals_sum_tmul_facet (fun j => c j • x), tmul_sum]
    simp only [tmul_smul, smul_tmul']
  · exact ⟨0, fun _ => le_rfl, by ext i; fin_cases i <;> simp⟩
  · rintro _ _ ⟨X, hX, hX'⟩ ⟨Y, hY, hY'⟩
    refine ⟨X + Y, fun j => add_nonneg (hX j) (hY j), ?_⟩
    rw [map_add, hX', hY']
    ext i; fin_cases i <;> simp <;> abel
  · rintro c hc _ ⟨X, hX, hX'⟩
    refine ⟨c • X, fun j => smul_nonneg hc (hX j), ?_⟩
    rw [map_smul, hX']
    ext i; fin_cases i <;> simp [smul_add]

/-- A composite observable whose vertex values are facet sums is in the minimal cone. -/
lemma mem_minTensorCone_of_isFacetSum {z : E ⊗[ℝ] Square} (hz : IsFacetSum (vals z)) :
    z ∈ minTensorCone E Square := by
  obtain ⟨X, hX, hXz⟩ := hz
  obtain rfl : z = ∑ j, X j ⊗ₜ[ℝ] facet j := vals_injective (hXz.trans (vals_sum_tmul_facet X).symm)
  exact sum_mem fun j _ => tmul_mem_minTensorCone (hX j) (facet_nonneg j)

/-! ## B. Nuclear systems are classical -/

/-- If the maximal cone of the composite with the square lies in the closure of the minimal cone,
every two effects have joint effects up to any error: the composite observable with vertex values
`f, e, 1 - e, 1 - f` is in the maximal cone, and the facet coordinates of a nearby minimal-cone
observable give the joint effect. -/
lemma exists_isApproxBinaryJointEffect
    (h : (maxTensorCone E Square : Set (E ⊗[ℝ] Square)) ⊆ minTensorClosure E Square)
    (e f : Effect E) {δ : ℝ} (hδ : 0 < δ) : ∃ g : E, Effect.IsApproxBinaryJointEffect e f δ g := by
  set A : Fin 4 → E := ![f, e, 1 - e, 1 - f]
  have hvals := vals_ofVals (A := A) (by simp [A])
  have hmax : ofVals A ∈ maxTensorCone E Square :=
    mem_maxTensorCone_of_vals_nonneg fun i => by
      rw [hvals]; fin_cases i <;> simp [A, e.2.1, f.2.1, e.2.2, f.2.2]
  obtain ⟨X, hX, hXA⟩ := isFacetSum_vals (h hmax δ hδ)
  rw [map_add, hvals, smul_tmul', vals_tmul] at hXA
  have h₀ := congrFun hXA 0; have h₁ := congrFun hXA 1; have h₃ := congrFun hXA 3
  simp only [A, Pi.add_apply, val_one, one_smul, Matrix.cons_val] at h₀ h₁ h₃
  have hδ1 : (0 : E) ≤ δ • 1 := smul_nonneg hδ.le OrderUnitSpace.one_nonneg
  refine ⟨X 3, (neg_nonpos.2 hδ1).trans (hX 3), ?_, ?_, ?_⟩
  · rw [h₁]; exact le_add_of_nonneg_left (hX 0)
  · rw [h₀]; exact le_add_of_nonneg_left (hX 2)
  · calc (e : E) + f - 1 = (e + δ • 1) - (1 - f + δ • 1) := by abel
      _ = (X 0 + X 3) - (X 0 + X 1) := by rw [h₁, h₃]
      _ ≤ X 3 := by rw [add_sub_add_left_eq_sub]; exact sub_le_self _ (hX 1)
      _ ≤ X 3 + δ • 1 := le_add_of_nonneg_right hδ1

/-- **Nuclear systems are classical.** If composition with every Archimedean system is unique, the
positive functionals form a lattice: the state space is a Choquet simplex. -/
lemma IsNuclear.isClassical (h : IsNuclear E) : IsClassical E :=
  isClassical_of_approxJoint fun e f _ hδ =>
    exists_isApproxBinaryJointEffect (h Square) e f hδ

/-! ## C. The square test -/

section Archimedean

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

/-- If composition with the square is unique, observables have the Riesz decomposition: the
composite observable with vertex values `f₁, g, f₁ + f₂ - g, f₂` is in the maximal cone, and its
facet coordinates split `g`. -/
lemma hasRieszDecomposition_of_minTensorCone_eq_square
    (h : minTensorCone E Square = maxTensorCone E Square) : HasRieszDecomposition E := by
  intro f₁ f₂ g hf₁ hf₂ hg
  have hvals := vals_ofVals (A := ![f₁, g, f₁ + f₂ - g, f₂]) (by simp)
  have hmax : ofVals ![f₁, g, f₁ + f₂ - g, f₂] ∈ maxTensorCone E Square :=
    mem_maxTensorCone_of_vals_nonneg fun i => by
      rw [hvals]; fin_cases i <;> simp [hf₁, hf₂, hg.1, hg.2]
  obtain ⟨X, hX, hXA⟩ := isFacetSum_vals (h ▸ hmax)
  rw [hvals] at hXA
  have h₀ := congrFun hXA 0; have h₁ := congrFun hXA 1; have h₃ := congrFun hXA 3
  simp only [Matrix.cons_val] at h₀ h₁ h₃
  refine ⟨X 3, ⟨hX 3, h₀ ▸ le_add_of_nonneg_left (hX 2)⟩, ?_⟩
  rw [h₁, add_sub_cancel_right, h₃]
  exact ⟨hX 0, le_add_of_nonneg_right (hX 1)⟩

/-- With the Riesz decomposition, every composite observable with the square in the maximal cone
is in the minimal cone. -/
lemma _root_.HasRieszDecomposition.maxTensorCone_subset_square (hE : HasRieszDecomposition E) :
    maxTensorCone E Square ≤ minTensorCone E Square := fun z hz => by
  have hA := mem_maxTensorCone_iff.1 hz
  have hd := vals_diagonal z
  obtain ⟨g₁, hg₁, hg₂⟩ := hE (hA 0) (hA 3)
    ⟨hA 1, by rw [hd]; exact le_add_of_nonneg_right (hA 2)⟩
  refine mem_minTensorCone_of_isFacetSum ⟨![vals z 1 - g₁, vals z 3 - (vals z 1 - g₁),
    vals z 0 - g₁, g₁], fun j => ?_, ?_⟩
  · fin_cases j <;> simp [sub_nonneg, hg₁.1, hg₁.2, hg₂.1, hg₂.2]
  · ext i; fin_cases i <;> simp
    rw [show vals z 2 = vals z 0 + vals z 3 - vals z 1 by rw [hd]; abel]; abel

/-- **Square test.** Composition with the square is unique exactly when the observables have the
Riesz decomposition. -/
lemma minTensorCone_eq_maxTensorCone_square_iff :
    minTensorCone E Square = maxTensorCone E Square ↔ HasRieszDecomposition E :=
  ⟨hasRieszDecomposition_of_minTensorCone_eq_square, fun hE =>
    minTensorCone_le_maxTensorCone.antisymm hE.maxTensorCone_subset_square⟩

/-! ## D. Classicality -/

/-- If composition with the square is unique, the positive functionals form a lattice: the state
space is a Choquet simplex. -/
lemma isClassical_of_minTensorCone_eq_square
    (h : minTensorCone E Square = maxTensorCone E Square) : IsClassical E :=
  (hasRieszDecomposition_of_minTensorCone_eq_square h).hasLatticeDualCone

section Complete

open scoped ArchimedeanOrderUnitSpace

variable [CompleteSpace E]

/-- **Namioka–Phelps square test.** On a complete Archimedean order-unit space, the state space is
a Choquet simplex exactly when composition with the square is unique. -/
lemma isClassical_iff_minTensorCone_eq_square :
    IsClassical E ↔ minTensorCone E Square = maxTensorCone E Square :=
  ⟨fun h => minTensorCone_eq_maxTensorCone_square_iff.2 h.hasRieszDecomposition,
    isClassical_of_minTensorCone_eq_square⟩

/-- **Two probes of classicality.** On a complete Archimedean order-unit space, every two yes/no
measurements are compatible exactly when composition with the square is unique. -/
lemma jointlyMeasurable_iff_minTensorCone_eq_square :
    (∀ e f : Effect E, Measurement.JointlyMeasurable (Effect.binaryMeasurement e)
      (Effect.binaryMeasurement f)) ↔ minTensorCone E Square = maxTensorCone E Square :=
  isClassical_iff_jointlyMeasurable.symm.trans isClassical_iff_minTensorCone_eq_square

end Complete

end Archimedean

end ProbabilisticTheory
