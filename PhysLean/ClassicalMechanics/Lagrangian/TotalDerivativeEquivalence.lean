/-
Copyright (c) 2025 Rein Zustand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rein Zustand
-/
import PhysLean.Mathematics.VariationalCalculus.HasVarGradient
/-!

# Equivalent Lagrangians under Total Derivatives

## i. Overview

Two Lagrangians are physically equivalent if they differ by a total time derivative
d/dt F(q, t). This is because the Euler-Lagrange equations depend only on extremizing
the action integral, and total derivatives don't affect which paths are extremal.

This module defines the key concept of a function being a total time derivative,
which is essential for analyzing symmetries like Galilean invariance.

Note: Some authors call this "gauge equivalence" by analogy with gauge transformations
in field theory, but we avoid that terminology here since no gauge fields are involved.

## ii. Key insight

A general function δL(r, v, t) is a total time derivative if there exists a function
F(r, t) (independent of velocity) such that:
  δL(r, v, t) = d/dt F(r, t) = fderiv ℝ F (r, t) (v, 1)

By the chain rule, this expands to:
  δL(r, v, t) = ∂F/∂t + ⟨∇ᵣF, v⟩

For the special case where δL depends only on velocity v (not position or time),
this implies a strong constraint:
  δL(v) = ⟨g, v⟩ for some constant vector g

This is because:
1. d/dt F(r, t) = ∂F/∂t + ⟨∇F, v⟩
2. For δL to be r-independent, ∇F must be r-independent
3. For δL to be t-independent, the time-dependent part must vanish
4. The result is δL = ⟨g, v⟩ for constant g

## iii. Key definitions

- `IsTotalTimeDerivative`: General case for δL(r, v, t)
- `IsTotalTimeDerivativeVelocity`: Velocity-only case, equivalent to δL(v) = ⟨g, v⟩

## iv. References

- Landau & Lifshitz, "Mechanics", §2 (The principle of least action)
- Landau & Lifshitz, "Mechanics", §4 (The Lagrangian for a free particle)

-/

namespace ClassicalMechanics

open InnerProductSpace

namespace Lagrangian

/-!

## A. General Total Time Derivative

-/

/-- A function δL(r, v, t) is a total time derivative if it can be written as d/dt F(r, t)
    for some function F that depends on position and time but not velocity.

    Mathematically: δL(r, v, t) = fderiv ℝ F (r, t) (v, 1)

    By the chain rule, this equals ∂F/∂t(r, t) + ⟨∇ᵣF(r, t), v⟩.

    This is the most general form of Lagrangian equivalence under total derivatives.
    The key point is that F must be independent of velocity. -/
def IsTotalTimeDerivative {n : ℕ}
    (δL : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ → ℝ) : Prop :=
  ∃ (F : EuclideanSpace ℝ (Fin n) × ℝ → ℝ) (_ : Differentiable ℝ F),
    ∀ r v t, δL r v t = fderiv ℝ F (r, t) (v, 1)

/-!

## B. Velocity-Only Total Time Derivative

When δL depends only on velocity (the free particle case), the condition simplifies.

-/

/-- A velocity-only function that is a total time derivative must be linear in velocity.

    If δL depends only on velocity and equals d/dt F(r, t) for some F,
    then δL(v) = ⟨g, v⟩ for some constant vector g.

    This characterization comes from the requirement that:
    - d/dt F(r, t) = ∂F/∂t + ⟨∇F, ṙ⟩ = ∂F/∂t + ⟨∇F, v⟩
    - For the result to be independent of r and t, we need ∇F = g (constant) and ∂F/∂t = 0
    - Thus δL(v) = ⟨g, v⟩

    WLOG, we assume `δL 0 = 0` since constants are total derivatives (c = d/dt(c·t))
    and can be absorbed without affecting the equations of motion. -/
lemma isTotalTimeDerivativeVelocity {n : ℕ}
    (δL : EuclideanSpace ℝ (Fin n) → ℝ)
    (hδL0 : δL 0 = 0)
    (h : IsTotalTimeDerivative (fun _ v _ => δL v)) :
    ∃ g : EuclideanSpace ℝ (Fin n), ∀ v, δL v = ⟪g, v⟫_ℝ := by
  classical
  rcases h with ⟨F, hFdiff, hEq⟩

  -- Derivative of F at (0,0)
  let dF : (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ] ℝ :=
    fderiv ℝ F ((0 : EuclideanSpace ℝ (Fin n)), (0 : ℝ))

  -- The "time-direction" derivative must vanish because δL 0 = 0.
  have h_time : dF ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)) = 0 := by
    have h0 :
        δL (0 : EuclideanSpace ℝ (Fin n)) =
          fderiv ℝ F ((0 : EuclideanSpace ℝ (Fin n)), (0 : ℝ))
            ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)) := by
      simpa using (hEq (0 : EuclideanSpace ℝ (Fin n))
        (0 : EuclideanSpace ℝ (Fin n)) (0 : ℝ))
    have : dF ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)) =
        δL (0 : EuclideanSpace ℝ (Fin n)) := by
      simpa [dF] using h0.symm
    simpa [hδL0] using this

  -- Induced continuous linear functional on velocity: v ↦ dF (v,0).
  let φ : (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
    dF.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) ℝ)

  -- Show δL v = φ v for all v.
  have hφ : ∀ v : EuclideanSpace ℝ (Fin n), δL v = φ v := by
    intro v
    have hv :
        δL v =
          fderiv ℝ F ((0 : EuclideanSpace ℝ (Fin n)), (0 : ℝ))
            (v, (1 : ℝ)) := by
      simpa using (hEq (0 : EuclideanSpace ℝ (Fin n)) v (0 : ℝ))
    have hv' : δL v = dF (v, (1 : ℝ)) := by
      simpa [dF] using hv
    calc
      δL v = dF (v, (1 : ℝ)) := hv'
      _ = dF ((v, (0 : ℝ)) + ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ))) := by
        simp
      _ = dF (v, (0 : ℝ)) + dF ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)) := by
        simpa using
          (dF.map_add (v, (0 : ℝ)) ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)))
      _ = dF (v, (0 : ℝ)) := by
        simp [h_time]
      _ = φ v := by
        simp [φ]

  -- Frechet–Riesz: represent φ as inner product with some g.
  refine ⟨(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm φ, ?_⟩
  intro v
  have hinner :
      ⟪(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm φ, v⟫_ℝ = φ v := by
    rw [InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)
        (E := EuclideanSpace ℝ (Fin n)) (x := v) (y := φ)]
  calc
    δL v = φ v := hφ v
    _ = ⟪(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm φ, v⟫_ℝ := by
      rw [hinner.symm]

end Lagrangian

end ClassicalMechanics
