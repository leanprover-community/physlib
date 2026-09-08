/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Defs

/-!
# Lorentzian manifolds

A Lorentzian metric is a pseudo-Riemannian metric with exactly one positive direction: signature
`(+, -, …, -)`. This is Physlib's `+---` convention, the one used by
`Lorentz.Vector.minkowskiProduct`, so it is stated through `PseudoRiemannian.coindex`, the number
of positive directions. In the opposite "mostly plus" convention the same metric is the negative
of this one, with `index` and `coindex` exchanged.

The coindex is locally constant, so on a connected manifold the condition need only be checked at
one point; see `PseudoRiemannian.isLorentzian_of_coindex_eq_one`.

## Main definitions

* `PseudoRiemannian.IsLorentzian I M`: the coindex is `1` everywhere.

## Main results

* `PseudoRiemannian.finiteDimensional_of_isLorentzian`: coindex `1` already forces the model to be
  finite-dimensional, so the class needs no such hypothesis.

## Tags

Lorentzian, pseudo-Riemannian, coindex, signature, spacetime
-/

@[expose] public section

open Bundle Module
open scoped Manifold Bundle ContDiff

namespace PseudoRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  [∀ x : M, PseudoInnerProductSpace (TangentSpace I x)]

variable (I M) in
/-- The metric is Lorentzian: exactly one positive direction at every point, i.e. signature
`(+, -, …, -)` in Physlib's `+---` convention. -/
class IsLorentzian : Prop where
  coindex_eq_one : ∀ x : M, coindex I x = 1

@[simp]
lemma coindex_eq_one [IsLorentzian I M] (x : M) : coindex I x = 1 :=
  IsLorentzian.coindex_eq_one x

/-- Coindex `1` is unattainable in infinite dimensions, where `QuadraticForm.sigPos` is `0`, so a
Lorentzian metric forces a finite-dimensional model. -/
lemma finiteDimensional_of_isLorentzian [IsLorentzian I M] (x : M) : FiniteDimensional ℝ E :=
  PseudoInnerProductSpace.finiteDimensional_of_coindex_pos (E := TangentSpace I x)
    (by rw [show PseudoInnerProductSpace.coindex (TangentSpace I x) = 1 from coindex_eq_one x]
        norm_num)

/-- A Lorentzian metric has `dim M - 1` negative directions. -/
lemma index_eq [IsLorentzian I M] [FiniteDimensional ℝ E] (x : M) :
    index I x + 1 = finrank ℝ E := by
  have := coindex_add_index_eq_finrank (I := I) x
  rw [coindex_eq_one] at this
  omega

variable [IsManifold I 1 M] [FiniteDimensional ℝ E]

/-- On a connected manifold, being Lorentzian can be checked at a single point. -/
lemma isLorentzian_of_coindex_eq_one (n : ℕ∞ω) [PreconnectedSpace M]
    [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)] {x₀ : M}
    (h : coindex I x₀ = 1) : IsLorentzian I M :=
  ⟨fun x ↦ ((isLocallyConstant_coindex (I := I) n).apply_eq_of_preconnectedSpace x x₀).trans h⟩

end PseudoRiemannian
