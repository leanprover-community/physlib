/-
Copyright (c) 2026 Nicola Bernini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Bernini, Nathaneal Sajan
-/
module

public import Physlib.SpaceAndTime.Space.Basic
public import Physlib.Meta.TODO.Basic

/-!
# Configuration space of the harmonic oscillator

## i. Overview

The configuration space `Q` of the one-dimensional harmonic oscillator is the space of
possible positions of the oscillator, formalised here as a one-dimensional smooth manifold.

`Q` carries a single chosen global coordinate, modeled by `EuclideanSpace ℝ (Fin 1)`. This
coordinate supplies the topology and the smooth-manifold structure through a single global
chart.

The global coordinate also identifies each tangent space with the same Euclidean model. The
map `tangentCoord q` records the coordinate representative of a tangent vector at `q`; this
tangent-coordinate infrastructure is used by later geometric constructions on the oscillator.

## ii. Key results

- `ConfigurationSpace` : the configuration manifold `Q` of the harmonic oscillator, wrapping
  the chosen `EuclideanSpace ℝ (Fin 1)` coordinate.
- `ConfigurationSpace.valEquiv` : the coordinate equivalence identifying `Q` with its
  `EuclideanSpace ℝ (Fin 1)` model.
- `ConfigurationSpace.valHomeomorphism` : the global coordinate homeomorphism underlying the
  manifold chart.
- `ConfigurationSpace.valDiffeomorph` : the global coordinate chart as an analytic
  diffeomorphism, upgrading `valHomeomorphism` to a smooth identification of `Q` with its model.
- the `ChartedSpace` and `IsManifold` instances, exhibiting `Q` as a one-dimensional analytic
  manifold modeled on `EuclideanSpace ℝ (Fin 1)`.
- `tangentCoord` : the chart-induced continuous linear equivalence from the tangent space at a
  configuration to `EuclideanSpace ℝ (Fin 1)`.
- `instNormedAddCommGroupTangent` and `instNormedSpaceTangent` : the normed real vector-space
  structure on tangent spaces, supplied through the global coordinate model.
- `instFiniteDimensionalTangent` : finite-dimensionality of each tangent space, transported
  through `tangentCoord`.
- `ConfigurationSpace.toSpace` : the point of physical `Space 1` determined by a
  configuration.

## iii. Table of contents

- A. The configuration space type
- B. Topology and coordinate homeomorphism
- C. Smooth manifold structure
- D. The coordinate diffeomorphism
- E. Tangent-coordinate infrastructure
- F. Map to physical space

## iv. References

* Ivo Terek, Introductory Variational Calculus on Manifolds, page 1 (Section 1, Basic definitions
  and examples). [ref: terek_variational_manifolds]
-/

@[expose] public section

namespace ClassicalMechanics

namespace HarmonicOscillator

open scoped Manifold

TODO "The API around the configuration space
    should be improved to allow further development of a proper
    geometric model of the Harmonic Oscillator."

/-!
## A. The configuration space type

`ConfigurationSpace` wraps a single chosen global coordinate valued in
`EuclideanSpace ℝ (Fin 1)`. We record extensionality in this coordinate together with a
function-like coordinate access mirroring that of `EuclideanSpace ℝ (Fin 1)`.
-/

/-- The one-dimensional configuration space `Q` of the harmonic oscillator: the space of
possible positions of the oscillator, equipped with a single chosen global coordinate
modeled by `EuclideanSpace ℝ (Fin 1)`. -/
structure ConfigurationSpace where
  /-- The chosen global coordinate of the configuration, valued in
  `EuclideanSpace ℝ (Fin 1)`. -/
  val : EuclideanSpace ℝ (Fin 1)

namespace ConfigurationSpace

/-- Two configurations are equal when their chosen global coordinates are equal. -/
@[ext]
lemma ext {x y : ConfigurationSpace} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  subst h
  rfl

/-- A configuration may be applied like a function `Fin 1 → ℝ`, evaluating its
underlying coordinate. This mirrors the function-like use of `EuclideanSpace ℝ (Fin 1)`. -/
instance : CoeFun ConfigurationSpace (fun _ => Fin 1 → ℝ) where
  coe x := fun i => x.val i

/-- Applying a configuration as a function reads the corresponding component of its global
coordinate. -/
lemma coe_apply (x : ConfigurationSpace) (i : Fin 1) : x i = x.val i := rfl

/-!
## B. Topology and coordinate homeomorphism

`ConfigurationSpace` carries the topology induced by its chosen coordinate
`ConfigurationSpace.val`: a set of configurations is open exactly when it is the preimage of
an open set under `val`. The wrapper/unwrapper pair is the coordinate equivalence `valEquiv`,
which is a homeomorphism `valHomeomorphism` for this induced topology — its continuity in
both directions is just the universal property of the induced topology. We transport Hausdorffness
and second countability across it from the model space, so `Q` is a well-behaved topological
manifold.
-/

/-- The topology on configuration space, induced by the chosen coordinate
`ConfigurationSpace.val` into `EuclideanSpace ℝ (Fin 1)`. -/
instance : TopologicalSpace ConfigurationSpace :=
  TopologicalSpace.induced ConfigurationSpace.val inferInstance

/-- The coordinate equivalence between configuration space and its `EuclideanSpace ℝ (Fin 1)`
model, given by `ConfigurationSpace.val` with its wrapper inverse. -/
def valEquiv : ConfigurationSpace ≃ EuclideanSpace ℝ (Fin 1) where
  toFun := ConfigurationSpace.val
  invFun v := ⟨v⟩
  left_inv x := by cases x; rfl
  right_inv v := rfl

/-- The global coordinate homeomorphism between configuration space and its
`EuclideanSpace ℝ (Fin 1)` model. Continuity in both directions is exactly the universal
property of the induced topology, so no norm or isometry structure is involved. This
homeomorphism underlies the single global chart used for the smooth-manifold structure. -/
def valHomeomorphism : ConfigurationSpace ≃ₜ EuclideanSpace ℝ (Fin 1) where
  toEquiv := valEquiv
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    exact continuous_id

/-- Configuration space is Hausdorff, transported from `EuclideanSpace ℝ (Fin 1)` across the
coordinate homeomorphism. -/
instance : T2Space ConfigurationSpace := valHomeomorphism.symm.t2Space

/-- Configuration space is second countable, transported from `EuclideanSpace ℝ (Fin 1)`
across the coordinate homeomorphism. -/
instance : SecondCountableTopology ConfigurationSpace :=
  valHomeomorphism.secondCountableTopology

/-!
## C. Smooth manifold structure

`ConfigurationSpace` is an analytic manifold modeled on `EuclideanSpace ℝ (Fin 1)`, via the
single global chart `valHomeomorphism`. With one chart the only coordinate change is the
chart's self-transition, which is analytic, so chart compatibility is immediate.
-/

/-- The structure of a charted space on `ConfigurationSpace`, modeled on its
`EuclideanSpace ℝ (Fin 1)` coordinate via the single global chart `valHomeomorphism`. -/
instance : ChartedSpace (EuclideanSpace ℝ (Fin 1)) ConfigurationSpace where
  atlas := { valHomeomorphism.toOpenPartialHomeomorph }
  chartAt _ := valHomeomorphism.toOpenPartialHomeomorph
  mem_chart_source := by
    simp
  chart_mem_atlas := by
    intro x
    simp

open Manifold ContDiff

/-- The structure of a smooth (indeed analytic) manifold on `ConfigurationSpace`. With a
single global chart, the only coordinate change is the chart's self-transition, which is
analytic. -/
instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ω ConfigurationSpace where
  compatible := by
    intro e1 e2 h1 h2
    simp [atlas, ChartedSpace.atlas] at h1 h2
    subst h1 h2
    exact symm_trans_mem_contDiffGroupoid valHomeomorphism.toOpenPartialHomeomorph

/-!
## D. The coordinate diffeomorphism

The single global chart is an analytic diffeomorphism, not merely a homeomorphism, so `Q` is
identified with its `EuclideanSpace ℝ (Fin 1)` model as a smooth manifold. With one chart this
is immediate: the only transition is the analytic self-transition already recorded in the
manifold structure. This smooth identification is what lets smoothness of maps to or from `Q`
be tested in the chosen global coordinate, the device used for trajectories and their velocities.
-/

/-- The global coordinate chart as an analytic diffeomorphism between `ConfigurationSpace` and
its `EuclideanSpace ℝ (Fin 1)` model, upgrading `valHomeomorphism` to a smooth identification. -/
def valDiffeomorph :
    ConfigurationSpace ≃ₘ^ω⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 1)), 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))⟯
      EuclideanSpace ℝ (Fin 1) where
  toEquiv := valEquiv
  contMDiff_toFun := by
    have h := contMDiffOn_chart (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) (n := ω)
      (x := (⟨0⟩ : ConfigurationSpace))
    rw [show (chartAt (EuclideanSpace ℝ (Fin 1)) (⟨0⟩ : ConfigurationSpace)).source = Set.univ
        from rfl, contMDiffOn_univ] at h
    exact h
  contMDiff_invFun := by
    have h := contMDiffOn_chart_symm (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) (n := ω)
      (x := (⟨0⟩ : ConfigurationSpace))
    rw [show (chartAt (EuclideanSpace ℝ (Fin 1)) (⟨0⟩ : ConfigurationSpace)).target = Set.univ
        from rfl, contMDiffOn_univ] at h
    exact h

end ConfigurationSpace

/-!
## E. Tangent-coordinate infrastructure

The global coordinate on `ConfigurationSpace` also gives a coordinate representative for tangent
vectors. The tangent spaces inherit their normed real vector-space structure from the Euclidean
coordinate model, and `tangentCoord q` records the resulting continuous linear equivalence.
-/

noncomputable section

-- Let Lean use the definitional tangent/model identification used by `tangentCoord`.
set_option backward.isDefEq.respectTransparency false

/-- The model-space normed additive group structure on tangent spaces. -/
instance instNormedAddCommGroupTangent (q : ConfigurationSpace) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q) :=
  inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin 1)))

/-- The model-space real normed vector space structure on tangent spaces. -/
instance instNormedSpaceTangent (q : ConfigurationSpace) :
    NormedSpace ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q) :=
  inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin 1)))

/-- The chart-induced continuous linear equivalence from the tangent space at `q` to the
Euclidean coordinate model `EuclideanSpace ℝ (Fin 1)`. -/
def tangentCoord (q : ConfigurationSpace) :
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q ≃L[ℝ] EuclideanSpace ℝ (Fin 1) where
  toFun v := v
  invFun v := v
  map_add' := by simp
  map_smul' := by simp

/-- Each tangent space is finite-dimensional because it is linearly equivalent to
`EuclideanSpace ℝ (Fin 1)` through `tangentCoord`. -/
instance instFiniteDimensionalTangent (q : ConfigurationSpace) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q) :=
  LinearEquiv.finiteDimensional (tangentCoord q).symm.toLinearEquiv

end

namespace ConfigurationSpace

/-!
## F. Map to physical space

The point of one-dimensional physical `Space 1` determined by a configuration, obtained by
reading off the underlying coordinate. This links the abstract configuration manifold to the
concrete coordinate model.
-/

/-- The position in one-dimensional space associated to the configuration. -/
def toSpace (q : ConfigurationSpace) : Space 1 := ⟨fun i => q.val i⟩

/-- The physical-space coordinate associated to a configuration is its chosen global
coordinate. -/
lemma toSpace_apply (q : ConfigurationSpace) (i : Fin 1) : q.toSpace i = q.val i := rfl

end ConfigurationSpace

end HarmonicOscillator

end ClassicalMechanics
