/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
public import Physlib.ClassicalMechanics.HarmonicOscillator.Geometric.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Geometric kinetic energy of the harmonic oscillator

## i. Overview

The configuration space of the geometric harmonic oscillator is `ConfigurationSpace`.
At a configuration `q`, velocities are tangent vectors in
`TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q`.

The oscillator mass determines a Riemannian metric on `ConfigurationSpace`. At each
configuration `q`, the metric is the mass-scaled Euclidean inner product on tangent
vectors, recorded by `massMetricVal S q`.

The kinetic energy associated with this mass metric is
`geometricKineticEnergy S q v = (1 / 2 : ℝ) * S.massRiemannianMetric.inner q v v`.
In coordinates this gives the standard expression
`(1 / 2 : ℝ) * S.m * ⟪tangentCoord q v, tangentCoord q v⟫_ℝ`.

## ii. Key results

- `massRiemannianMetric` : the mass-scaled Euclidean inner product as a Riemannian metric
  on `ConfigurationSpace`.
- `geometricKineticEnergy` : the geometric kinetic-energy function associated to the
  oscillator mass metric.
- `massRiemannianMetric_inner_apply` : evaluation of the mass metric in global tangent
  coordinates.
- `massRiemannianMetric_pos` : positive definiteness of the mass Riemannian metric.
- `geometricKineticEnergy_massMetric_eq` : the metric-induced kinetic energy for
  the oscillator mass metric is the mass-scaled coordinate kinetic energy.

## iii. Table of contents

- A. Pointwise mass metric
- B. Riemannian mass metric
- C. Geometric kinetic energy
- D. Coordinate formula

## iv. References

* Ivo Terek, Introductory Variational Calculus on Manifolds, pages 1-2.
  [ref: terek_variational_manifolds]
-/

@[expose] public section

namespace ClassicalMechanics

namespace HarmonicOscillator

open scoped Manifold
open Bundle Bornology
open Manifold ContDiff
open InnerProductSpace

noncomputable section

-- Let Lean use the definitional tangent-coordinate identification in the metric proofs.
set_option backward.isDefEq.respectTransparency false

/-!
## A. Pointwise mass metric

The pointwise mass metric is the mass-scaled Euclidean inner product in global tangent
coordinates. Its positivity, boundedness, and smoothness properties are established here
before assembling the Riemannian metric.
-/

/-- The value of the oscillator mass metric at `q`. It is the mass-scaled pullback of the
Euclidean inner product along `tangentCoord q`, so
`massMetricVal S q v w = S.m * ⟪tangentCoord q v, tangentCoord q w⟫_ℝ`. -/
noncomputable def massMetricVal (S : HarmonicOscillator) (q : ConfigurationSpace) :
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q →L[ℝ]
      TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q →L[ℝ] ℝ :=
  S.m • (innerSL ℝ :
    EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)

/-- Applying the mass metric value to two tangent vectors gives the mass-scaled Euclidean
inner product of their coordinate representatives. -/
lemma massMetricVal_apply
    (S : HarmonicOscillator) (q : ConfigurationSpace)
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q) :
    massMetricVal S q v w = S.m * ⟪tangentCoord q v, tangentCoord q w⟫_ℝ := by
  rfl

/-- A nonzero tangent vector has nonzero coordinate representative under `tangentCoord`. -/
lemma tangentCoord_ne_zero {q : ConfigurationSpace}
    {v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q}
    (hv : v ≠ 0) : tangentCoord q v ≠ 0 := by
  intro h
  apply hv
  exact (tangentCoord q).injective (by simpa using h)

/-- The oscillator mass metric is positive on nonzero tangent vectors. -/
lemma massMetricVal_pos
    (S : HarmonicOscillator) (q : ConfigurationSpace)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q) (hv : v ≠ 0) :
    0 < massMetricVal S q v v := by
  rw [massMetricVal_apply]
  exact mul_pos S.m_pos (real_inner_self_pos.mpr (tangentCoord_ne_zero hv))

/-- The mass metric unit ball is bounded in the model norm. -/
lemma massMetricVal_isVonNBounded
    (S : HarmonicOscillator) (q : ConfigurationSpace) :
    IsVonNBounded ℝ
      {v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q | massMetricVal S q v v < 1} := by
  change IsVonNBounded ℝ
    {v : EuclideanSpace ℝ (Fin 1) | S.m * ⟪v, v⟫_ℝ < 1}
  rw [NormedSpace.isVonNBounded_iff']
  refine ⟨Real.sqrt (1 / S.m), ?_⟩
  intro v hv
  have hv' : S.m * ⟪v, v⟫_ℝ < 1 := by simpa using hv
  rw [real_inner_self_eq_norm_sq] at hv'
  have hmul : S.m * ‖v‖ ^ 2 < 1 := hv'
  have hsq_le : ‖v‖ ^ 2 ≤ 1 / S.m := by
    have hsq_lt : ‖v‖ ^ 2 < 1 / S.m := by
      rw [lt_div_iff₀ S.m_pos]
      nlinarith [hmul]
    exact hsq_lt.le
  exact Real.le_sqrt_of_sq_le hsq_le

/-- The oscillator mass metric is constant in the global tangent-bundle chart. -/
lemma massMetricVal_contMDiff (S : HarmonicOscillator) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 1)).prod
        𝓘(ℝ, EuclideanSpace ℝ (Fin 1) →L[ℝ]
          EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)) ω
      (fun q : ConfigurationSpace =>
        TotalSpace.mk'
          (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)
          (E := fun q : ConfigurationSpace =>
            TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q →L[ℝ]
              TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q →L[ℝ] ℝ)
          q (massMetricVal S q)) := by
  intro x
  rw [Bundle.contMDiffAt_section_iff]
  convert! contMDiffAt_const (c := S.m • (innerSL ℝ :
    EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ))
  ext v w
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, massMetricVal, TangentSpace]

/-!
## B. Riemannian mass metric

The pointwise bilinear forms assemble into a `ContMDiffRiemannianMetric` on the oscillator
configuration space.
-/

/-- The mass-scaled Euclidean inner product as a Riemannian metric on the oscillator
configuration space. -/
noncomputable def massRiemannianMetric (S : HarmonicOscillator) :
    ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ω
      (EuclideanSpace ℝ (Fin 1))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) : ConfigurationSpace → Type _) where
  inner q := massMetricVal S q
  symm q v w := by
    rw [massMetricVal_apply, massMetricVal_apply, real_inner_comm]
  pos q v hv := massMetricVal_pos S q v hv
  isVonNBounded q := massMetricVal_isVonNBounded S q
  contMDiff := massMetricVal_contMDiff S

/-!
## C. Geometric kinetic energy

The geometric kinetic energy is defined directly from the oscillator's mass Riemannian
metric.
-/

/-- The defining formula for the oscillator geometric kinetic energy. -/
noncomputable def geometricKineticEnergy
    (S : HarmonicOscillator) (q : ConfigurationSpace)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q) : ℝ :=
  (1 / 2 : ℝ) * S.massRiemannianMetric.inner q v v

/-- The geometric kinetic energy is one half the mass Riemannian metric applied to `v`
twice. -/
lemma geometricKineticEnergy_eq
    (S : HarmonicOscillator) (q : ConfigurationSpace)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q) :
    geometricKineticEnergy S q v =
      (1 / 2 : ℝ) * S.massRiemannianMetric.inner q v v := by
  rfl

/-!
## D. Coordinate formula

The coordinate identities below recover the usual mass-scaled formula for kinetic energy.
-/

/-- The oscillator mass Riemannian metric is positive definite. -/
lemma massRiemannianMetric_pos
    (S : HarmonicOscillator) (q : ConfigurationSpace)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q)
    (hv : v ≠ 0) :
    0 < S.massRiemannianMetric.inner q v v :=
  massMetricVal_pos S q v hv

/-- In the global coordinate, the oscillator mass metric is the mass-scaled Euclidean inner
product of coordinate representatives. -/
lemma massRiemannianMetric_inner_apply
    (S : HarmonicOscillator) (q : ConfigurationSpace)
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q) :
    S.massRiemannianMetric.inner q v w =
      S.m * ⟪tangentCoord q v, tangentCoord q w⟫_ℝ := by
  exact massMetricVal_apply S q v w

/-- The metric-induced kinetic energy for the mass metric has the standard
harmonic-oscillator coordinate form. -/
lemma geometricKineticEnergy_massMetric_eq
    (S : HarmonicOscillator) (q : ConfigurationSpace)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q) :
    geometricKineticEnergy S q v =
      (1 / 2 : ℝ) * S.m * ⟪tangentCoord q v, tangentCoord q v⟫_ℝ := by
  rw [geometricKineticEnergy_eq, massRiemannianMetric_inner_apply]
  ring

end

end HarmonicOscillator

end ClassicalMechanics
