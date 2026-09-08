/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.CovariantDerivative
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# Uniqueness of the Levi-Civita connection

A connection on the tangent bundle compatible with a pseudo-inner product and torsion-free is
unique. Positivity plays no role, so this covers Lorentzian and arbitrary pseudo-Riemannian
signatures, with the Riemannian statement as the special case: `RiemannianBundle` supplies
`PseudoInnerProductSpace`, hence `IsContMDiffPseudoRiemannianBundle`, and the theorem applies
with no adapter.

The argument is classical. The difference of two connections is a tensor
(`CovariantDerivative.difference`); equal torsions make it symmetric, metric compatibility makes
it antisymmetric against the form, and `PseudoInnerProductSpace.eq_zero_of_symm_of_antisymm`
forces it to vanish.

## Main results

* `CovariantDerivative.difference_symm_of_torsion_eq_zero` and
  `difference_antisymm_of_isPseudoMetricCompatible`: the two halves of the argument.
* `CovariantDerivative.eq_of_isPseudoMetricCompatible_of_torsion_eq_zero`

## Implementation notes

Going through Mathlib's `IsMetricCompatible` on the tangent bundle instead is worse behaved:
`RiemannianBundle` installs a norm whose derived `AddCommGroup` and `TopologicalSpace` on
`TangentSpace I x` are only defeq, not syntactically equal, to the tangent space's own, so
`CovariantDerivative` fails to unify. A `PseudoInnerProductSpace` determines no topology and
avoids that. The two compatibility notions are therefore compared for an abstract bundle, in
`CovariantDerivative.isMetricCompatible_iff_isPseudoMetricCompatible`.

## Tags

Levi-Civita, connection, torsion, metric connection, pseudo-Riemannian
-/

@[expose] public section

open Bundle NormedSpace PseudoInnerProductSpace Set FiberBundle
open scoped Manifold ContDiff

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

namespace CovariantDerivative

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- The bundled counterpart of `IsCovariantDerivativeOn.difference_apply`. -/
@[simp]
lemma difference_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    (cov cov' : CovariantDerivative I F V) {x : M} {σ : Π y : M, V y}
    (hσ : MDiffAt (T% σ) x) :
    difference cov cov' x (σ x) = cov σ x - cov' σ x :=
  IsCovariantDerivativeOn.difference_apply _ _ (mem_univ x) hσ

section General

variable [∀ x : M, PseudoInnerProductSpace (TangentSpace I x)]
  [IsContMDiffPseudoRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  {cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _)}

omit [IsManifold I 2 M] [∀ x : M, PseudoInnerProductSpace (TangentSpace I x)]
  [IsContMDiffPseudoRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
lemma difference_extend {x : M} (v : TangentSpace I x) :
    difference cov cov' x v = cov (extend E v) x - cov' (extend E v) x := by
  have h := difference_apply cov cov' (σ := extend E v) (mdifferentiableAt_extend I E v)
  rwa [extend_apply_self] at h

omit [∀ x : M, PseudoInnerProductSpace (TangentSpace I x)]
  [IsContMDiffPseudoRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Two torsion-free connections have a symmetric difference tensor. -/
lemma difference_symm_of_torsion_eq_zero (ht : cov.torsion = 0) (ht' : cov'.torsion = 0) {x : M}
    (u v : TangentSpace I x) : difference cov cov' x v u = difference cov cov' x u v := by
  have hu := mdifferentiableAt_extend I E u
  have hv := mdifferentiableAt_extend I E v
  have h := cov.torsion_eq_zero_iff.mp ht hu hv
  have h' := cov'.torsion_eq_zero_iff.mp ht' hu hv
  rw [extend_apply_self, extend_apply_self] at h h'
  have hsub : (cov (extend E v) x u - cov' (extend E v) x u)
      - (cov (extend E u) x v - cov' (extend E u) x v) = 0 := by
    rw [sub_sub_sub_comm, h, h', sub_self]
  have hv' := difference_extend (cov := cov) (cov' := cov') v
  have hu' := difference_extend (cov := cov) (cov' := cov') u
  have := sub_eq_zero.mp hsub
  simpa [hv', hu'] using this

omit [IsManifold I 2 M] in
/-- Two metric connections have a difference tensor that is antisymmetric against the form. -/
lemma difference_antisymm_of_isPseudoMetricCompatible (hm : cov.IsPseudoMetricCompatible)
    (hm' : cov'.IsPseudoMetricCompatible) {x : M} (u v w : TangentSpace I x) :
    pseudoInner (difference cov cov' x u v) w = -pseudoInner (difference cov cov' x w v) u := by
  have hu := mdifferentiableAt_extend I E u
  have hw := mdifferentiableAt_extend I E w
  have h := hm.mvfderiv_pseudoInner_eq (extend E v) hu hw
  have h' := hm'.mvfderiv_pseudoInner_eq (extend E v) hu hw
  simp only [extend_apply_self] at h h'
  rw [h'] at h
  have hu' := difference_extend (cov := cov) (cov' := cov') u
  have hw' := difference_extend (cov := cov) (cov' := cov') w
  have key : pseudoInner (difference cov cov' x u v) w
      + pseudoInner u (difference cov cov' x w v) = 0 := by
    simp only [hu', hw', sub_apply, pseudoInner_sub_left,
      pseudoInner_sub_right]
    linarith
  rw [pseudoInner_comm u (difference cov cov' x w v)] at key
  linarith

/-- **Uniqueness of the Levi-Civita connection.** Two connections on the tangent bundle that are
compatible with the pseudo-inner product and torsion-free agree on differentiable vector fields.

No positivity is used, so this covers Lorentzian and general pseudo-Riemannian signatures. -/
theorem eq_of_isPseudoMetricCompatible_of_torsion_eq_zero
    (hm : cov.IsPseudoMetricCompatible) (hm' : cov'.IsPseudoMetricCompatible)
    (ht : cov.torsion = 0) (ht' : cov'.torsion = 0)
    {x : M} {Y : Π y : M, TangentSpace I y} (hY : MDiffAt (T% Y) x) :
    cov Y x = cov' Y x := by
  have hzero : ∀ u v : TangentSpace I x, difference cov cov' x u v = 0 :=
    eq_zero_of_symm_of_antisymm (fun u v ↦ difference_symm_of_torsion_eq_zero ht ht' v u)
      (difference_antisymm_of_isPseudoMetricCompatible hm hm')
  have hYzero : difference cov cov' x (Y x) = 0 := by ext v; exact hzero (Y x) v
  rw [difference_apply cov cov' hY] at hYzero
  exact sub_eq_zero.mp hYzero

end General

end CovariantDerivative
