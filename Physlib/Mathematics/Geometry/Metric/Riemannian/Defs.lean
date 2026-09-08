/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Defs

/-!
# Riemannian manifolds as the index-zero pseudo-Riemannian manifolds

Riemannian geometry is a special case of the pseudo-Riemannian development, not a parallel one:
Mathlib's Riemannian hypotheses already discharge the pseudo-Riemannian ones, as the `example`
below checks. This file records the invariant separating the two cases.

## Main definitions

* `PseudoRiemannian.IsRiemannian I M`: the metric is positive definite everywhere.

## Main results

* `PseudoRiemannian.instIsRiemannianOfRiemannianBundle`: Mathlib's `RiemannianBundle` discharges
  it, so the two notions of "Riemannian" are one.
* `PseudoRiemannian.index_eq_zero`: in finite dimension, being Riemannian means index `0`; on a
  Mathlib `RiemannianBundle` this is now automatic.

## Tags

Riemannian, pseudo-Riemannian, index
-/

@[expose] public section

open Bundle
open scoped Manifold Bundle ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}

namespace PseudoRiemannian

section Pseudo

variable [∀ x : M, PseudoInnerProductSpace (TangentSpace I x)]

variable (I M) in
/-- The metric is Riemannian: positive definite at every point.

Stated by positive definiteness rather than by `index I x = 0`, which in infinite dimensions is
vacuous, `QuadraticForm.sigNeg` being `0` there by definition. -/
class IsRiemannian : Prop where
  posDef : ∀ x : M, (PseudoInnerProductSpace.toQuadraticForm (TangentSpace I x)).PosDef

variable [FiniteDimensional ℝ E]

@[simp]
lemma index_eq_zero [IsRiemannian I M] (x : M) : index I x = 0 :=
  PseudoInnerProductSpace.index_eq_zero_of_posDef (IsRiemannian.posDef x)

lemma isRiemannian_iff_index_eq_zero : IsRiemannian I M ↔ ∀ x : M, index I x = 0 :=
  ⟨fun _ ↦ index_eq_zero, fun h ↦
    ⟨fun x ↦ (PseudoInnerProductSpace.index_eq_zero_iff_posDef (TangentSpace I x)).mp (h x)⟩⟩

end Pseudo

section RiemannianBundle

variable [RiemannianBundle (TangentSpace I : M → Type _)]

/-- Transparency check: a Riemannian manifold satisfies the pseudo-Riemannian hypotheses with no
adapter. -/
example [IsManifold I 1 M] [IsContMDiffRiemannianBundle I n E (TangentSpace I : M → Type _)] :
    IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _) := inferInstance

/-- **Mathlib's Riemannian manifolds are Riemannian.** No finite-dimensionality is needed, since
the class is stated by positive definiteness. -/
instance instIsRiemannianOfRiemannianBundle : IsRiemannian I M :=
  ⟨fun _ v hv ↦ by
    show (0 : ℝ) < pseudoInner v v
    rw [PseudoInnerProductSpace.pseudoInner_eq_inner]
    exact real_inner_self_pos.mpr hv⟩

end RiemannianBundle

end PseudoRiemannian
