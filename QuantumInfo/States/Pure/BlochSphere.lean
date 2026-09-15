/-
Copyright (c) 2026 Anand Nambakam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Nambakam
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Bloch Sphere

The Bloch sphere is the unit sphere S² in ℝ³, used to represent
pure states of a two-level quantum system (qubit). Each point on the
sphere corresponds to a qubit state up to global phase.

This file defines the Bloch sphere type and its angular parameterization,
then builds the solid angle and dot product API on sphere points.

## Important definitions
 * `BlochSphere`: the unit sphere `Metric.sphere 0 1` in `EuclideanSpace ℝ (Fin 3)`
 * `blochPoint`: point on the Bloch sphere from polar angle α and azimuthal angle θ
 * `solidAngle`: solid angle of a geodesic triangle via Van Vleck formula

## Important results
 * `blochPoint_norm`: the Bloch vector has unit norm
 * `dot_blochPoint`: dot product of Bloch vectors in terms of angle differences

## References

* S. Pancharatnam, Generalized theory of interference, and its applications, Proc. Indian Acad.
  Sci. A 44, 247–262 (1956). [ref: pancharatnam1956]
* M. V. Berry, Quantal phase factors accompanying adiabatic changes, Proc. R. Soc. London A 392,
  45–57 (1984). [ref: berry1984]
-/

open Complex Matrix

noncomputable section

/-- The Bloch sphere: unit sphere in `EuclideanSpace ℝ (Fin 3)`. -/
abbrev BlochSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

namespace BlochSphere

/-- The raw Bloch vector for angles (α, θ). Internal helper for `blochPoint`. -/
private def blochVecRaw (α θ : ℝ) : Fin 3 → ℝ :=
  ![Real.sin α * Real.cos θ, Real.sin α * Real.sin θ, Real.cos α]

/-- The Bloch vector has unit norm: sin²α(cos²θ + sin²θ) + cos²α = 1. -/
private lemma blochVecRaw_norm (α θ : ℝ) :
    Real.sqrt ((blochVecRaw α θ 0) ^ 2 + (blochVecRaw α θ 1) ^ 2 +
      (blochVecRaw α θ 2) ^ 2) = 1 := by
  have : (blochVecRaw α θ 0) ^ 2 + (blochVecRaw α θ 1) ^ 2 +
    (blochVecRaw α θ 2) ^ 2 = 1 := by
    simp [blochVecRaw]
    have h1 := Real.sin_sq_add_cos_sq α
    have h2 := Real.sin_sq_add_cos_sq θ
    nlinarith [sq_nonneg (Real.sin α * Real.cos θ),
      sq_nonneg (Real.sin α * Real.sin θ), sq_nonneg (Real.cos α),
      sq_abs (Real.sin α), sq_abs (Real.cos θ)]
  rw [this, Real.sqrt_one]

/-- A point on the Bloch sphere parameterized by polar angle `α` and
    azimuthal angle `θ`. -/
def blochPoint (α θ : ℝ) : BlochSphere :=
  ⟨(WithLp.equiv 2 _).symm (blochVecRaw α θ), by
    rw [Metric.mem_sphere, dist_comm, EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_three, blochVecRaw_norm α θ]⟩

/-- The underlying vector of a `blochPoint`. -/
lemma blochPoint_val (α θ : ℝ) :
    (blochPoint α θ : EuclideanSpace ℝ (Fin 3)) =
    (WithLp.equiv 2 _).symm (blochVecRaw α θ) := rfl

/-! ## Solid angle via Van Vleck formula -/

/-- Solid angle of a geodesic triangle on the Bloch sphere, computed via
    the Van Vleck formula using `Complex.arg` for full-quadrant support.

    `Ω = 2 · arg(den + num · i)` where
    `den = 1 + n₁·n₂ + n₂·n₃ + n₃·n₁` and `num = n₁ · (n₂ × n₃)`. -/
def solidAngle (p₁ p₂ p₃ : BlochSphere) : ℝ :=
  let n₁ := (p₁ : EuclideanSpace ℝ (Fin 3))
  let n₂ := (p₂ : EuclideanSpace ℝ (Fin 3))
  let n₃ := (p₃ : EuclideanSpace ℝ (Fin 3))
  let num := n₁ ⬝ᵥ n₂ ⨯₃ n₃
  let den := 1 + n₁ ⬝ᵥ n₂ + n₂ ⬝ᵥ n₃ + n₃ ⬝ᵥ n₁
  2 * Complex.arg ((den : ℝ) + (num : ℝ) * Complex.I)

/-! ## Dot product of Bloch vectors -/

/-- The dot product of two Bloch points expressed in angle differences. -/
lemma dot_blochPoint (α₁ θ₁ α₂ θ₂ : ℝ) :
    (blochPoint α₁ θ₁ : EuclideanSpace ℝ (Fin 3)) ⬝ᵥ
    (blochPoint α₂ θ₂ : EuclideanSpace ℝ (Fin 3)) =
    Real.sin α₁ * Real.sin α₂ * Real.cos (θ₂ - θ₁) +
    Real.cos α₁ * Real.cos α₂ := by
  simp [blochPoint_val, dotProduct, blochVecRaw, Fin.sum_univ_three, WithLp.equiv]
  rw [show Real.cos (θ₂ - θ₁) = Real.cos θ₁ * Real.cos θ₂ +
    Real.sin θ₁ * Real.sin θ₂ from by rw [Real.cos_sub]; ring]
  ring

end BlochSphere
