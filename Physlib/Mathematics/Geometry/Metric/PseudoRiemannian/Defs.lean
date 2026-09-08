/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Basic

/-!
# Pseudo-Riemannian manifolds

A pseudo-Riemannian metric on `M` is a pseudo-Riemannian structure on its tangent bundle, so this
file only specializes `Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Basic`. To say "let
`M` be a pseudo-Riemannian manifold", write
```
variable [∀ x : M, PseudoInnerProductSpace (TangentSpace I x)]
  [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)]
```
which Mathlib's `RiemannianBundle` together with `IsContMDiffRiemannianBundle` implies. No
`ofCoreOfTopology` detour is needed, since an indefinite form determines no norm.

## Main definitions

* `PseudoRiemannianMetric I n M`: metric data on `M`; theorems are stated with the typeclasses.
* `PseudoRiemannian.index I x` and `coindex I x`: the numbers of negative and positive
  directions of the metric at `x`.

## Main results

* `PseudoRiemannian.isLocallyConstant_index` and `index_eq_of_preconnectedSpace`: signature
  constancy is a theorem, so no metric carries it as data.
* `instIsContMDiffPseudoRiemannianBundleSelf`: a vector space with a pseudo-inner product is a
  pseudo-Riemannian manifold.

## Implementation notes

The musical isomorphisms are inherited: at `x` they are
`PseudoInnerProductSpace.flatEquiv (TangentSpace I x)` and `sharpEquiv (TangentSpace I x)`. The
`TangentSpace` instances below are what make them apply.

## Acknowledgements

The design follows Sébastien Gouëzel's proposal on [Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/The.20future.20of.20pseudo-Riemannian.20manifolds/with/619509253).

## References

* Barrett O'Neill, *Semi-Riemannian Geometry with Applications to Relativity*, Academic
  Press (1983).

## Tags

pseudo-Riemannian, Lorentzian, metric tensor, index, musical isomorphisms
-/

@[expose] public section

open Bundle Module
open scoped Manifold Bundle Topology ContDiff

section TangentSpaceInstances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

/-- A tangent space is Hausdorff, being a copy of the model space. `TangentSpace` is not
reducible, so this must be provided explicitly; the musical isomorphisms need it. -/
instance TangentSpace.instT2Space : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)

instance TangentSpace.instFiniteDimensional [FiniteDimensional ℝ E] :
    FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

/-- The tangent spaces of a vector space, viewed as a manifold modelled on itself, inherit its
pseudo-inner product.

Deliberately a `def`: as an instance it would outrank `InnerProductSpace.toPseudoInnerProductSpace`
on a `RiemannianBundle` whose base is a normed space modelled on itself, silently replacing the
Riemannian form by this one. Introduce it with `letI`. -/
@[reducible] noncomputable def TangentSpace.pseudoInnerProductSpace {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [PseudoInnerProductSpace V] (x : V) :
    PseudoInnerProductSpace (TangentSpace 𝓘(ℝ, V) x) :=
  inferInstanceAs (PseudoInnerProductSpace V)

set_option backward.isDefEq.respectTransparency false in
/-- **A vector space with a pseudo-inner product is a pseudo-Riemannian manifold**, with constant
metric. Together with `Lorentz.Vector.minkowskiPseudoInner` this is what makes the indefinite half
of the theory non-vacuous. -/
lemma isContMDiffPseudoRiemannianBundle_self {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [PseudoInnerProductSpace V] (n : ℕ∞ω) :
    letI := TangentSpace.pseudoInnerProductSpace (V := V)
    IsContMDiffPseudoRiemannianBundle 𝓘(ℝ, V) n V (TangentSpace 𝓘(ℝ, V) : V → Type _) := by
  letI := TangentSpace.pseudoInnerProductSpace (V := V)
  refine ⟨fun _ ↦ PseudoInnerProductSpace.pseudoInnerSL, fun x ↦ ?_, fun _ _ _ ↦ rfl⟩
  simp only [contMDiffAt_section]
  convert! contMDiffAt_const (c := PseudoInnerProductSpace.pseudoInnerSL (E := V))
  refine ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ ?_
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]
  rfl

end TangentSpaceInstances

/-- A `C^n` pseudo-Riemannian metric on `M`: the tangent-bundle case of
`Bundle.ContMDiffPseudoRiemannianMetric`. Use it to produce the instances that theorems are
stated with. -/
abbrev PseudoRiemannianMetric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (n : WithTop ℕ∞)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :=
  Bundle.ContMDiffPseudoRiemannianMetric (IB := I) (n := n) (F := E)
    (E := fun x : M ↦ TangentSpace I x)

namespace PseudoRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}
  [∀ x : M, PseudoInnerProductSpace (TangentSpace I x)]

variable (I) in
/-- The index of the metric at `x`: the number of negative directions. Index `0` is Riemannian. -/
noncomputable def index (x : M) : ℕ := PseudoInnerProductSpace.index (TangentSpace I x)

variable (I) in
/-- The coindex of the metric at `x`: the number of positive directions. Coindex `1` is
Lorentzian in Physlib's `+---` convention. -/
noncomputable def coindex (x : M) : ℕ := PseudoInnerProductSpace.coindex (TangentSpace I x)

lemma coindex_add_index_eq_finrank [FiniteDimensional ℝ E] (x : M) :
    coindex I x + index I x = Module.finrank ℝ E :=
  PseudoInnerProductSpace.coindex_add_index_eq_finrank (TangentSpace I x)

variable [IsManifold I 1 M] [FiniteDimensional ℝ E]

/-- **The index is locally constant.** Smoothness and pointwise nondegeneracy already force
signature constancy, so it is nowhere assumed. -/
theorem isLocallyConstant_index (n : ℕ∞ω)
    [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)] :
    IsLocallyConstant (index I : M → ℕ) :=
  Bundle.isLocallyConstant_index (IB := I) n (F := E)
    (E := fun x : M ↦ TangentSpace I x)

/-- The coindex is locally constant too, the two summing to the dimension. -/
theorem isLocallyConstant_coindex (n : ℕ∞ω)
    [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)] :
    IsLocallyConstant (coindex I : M → ℕ) := by
  have heq : (coindex I : M → ℕ) = (fun k ↦ finrank ℝ E - k) ∘ (index I) := by
    funext x
    have := coindex_add_index_eq_finrank (I := I) x
    simp only [Function.comp_apply]
    omega
  rw [heq]
  exact (isLocallyConstant_index (I := I) n).comp _

lemma index_eq_of_isPreconnected (n : ℕ∞ω)
    [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)] {s : Set M}
    (hs : IsPreconnected s) {x y : M} (hx : x ∈ s) (hy : y ∈ s) : index I x = index I y :=
  (isLocallyConstant_index (I := I) n).apply_eq_of_isPreconnected hs hx hy

lemma index_eq_of_preconnectedSpace (n : ℕ∞ω) [PreconnectedSpace M]
    [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)] (x y : M) :
    index I x = index I y :=
  (isLocallyConstant_index (I := I) n).apply_eq_of_preconnectedSpace x y

lemma index_eq_of_mem_connectedComponent (n : ℕ∞ω)
    [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)] {x y : M}
    (hy : y ∈ connectedComponent x) : index I y = index I x :=
  index_eq_of_isPreconnected n isConnected_connectedComponent.isPreconnected hy
    mem_connectedComponent

end PseudoRiemannian
