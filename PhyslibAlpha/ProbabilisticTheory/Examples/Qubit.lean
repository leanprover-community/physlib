/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Examples.NormCone
public import PhyslibAlpha.Mathematics.Geometry.Simplex
public import Mathlib.Analysis.Convex.Strict.Extreme
public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The qubit, in Bloch-vector coordinates

The qubit as the Euclidean norm cone over `ℝ³`: its states form the Bloch ball, not a simplex.

## i. Overview

A qubit state is a density matrix `ρ = ½(r • I + x · σ)`, given by a number `r` and a Bloch
vector `x ∈ ℝ³`, and `ρ` is positive exactly when `‖x‖ ≤ r`. So in Bloch coordinates the qubit is
the norm cone over Euclidean `ℝ³`. Its states form the Bloch ball and every point of the Bloch
sphere is a pure state. With infinitely many pure states, the state space is not a simplex: the
qubit is not classical.

## ii. Key results

- `ProbabilisticTheory.Qubit` : the qubit in Bloch coordinates.
- `ProbabilisticTheory.Qubit.stateEquiv` : the states are the Bloch ball.
- `ProbabilisticTheory.Qubit.isPure_purePoint` : unit Bloch vectors give pure states.
- `ProbabilisticTheory.Qubit.not_isSimplex_stateSpace` : the state space is not a simplex.

## iii. Table of contents

- A. The qubit as a norm cone
- B. Infinitely many pure states

## iv. References

- J. Barrett, *Information processing in generalized probabilistic theories*, Phys. Rev. A 75,
  032304 (2007).
- P. Janotta and H. Lal, *Generalized probabilistic theories without the no-restriction
  hypothesis*, Phys. Rev. A 87, 052131 (2013).

-/

@[expose] public section

namespace ProbabilisticTheory

/-!

## A. The qubit as a norm cone

-/

/-- The qubit in Bloch coordinates: `ℝ × ℝ³` ordered by the Lorentz cone. -/
abbrev Qubit : Type := NormCone (EuclideanSpace ℝ (Fin 3))

namespace Qubit

open NormCone

/-- The states of the qubit are the Bloch ball. -/
noncomputable def stateEquiv :
    𝓢[ℝ, Qubit] ≃ {a : Fin 3 → ℝ // ∑ i, |a i| ^ (2 : ℝ) ≤ 1} :=
  lpStateEquiv (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis Real.HolderConjugate.two_two
    (fun v => by
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_rpow]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
        Real.rpow_two, Real.norm_eq_abs, sq_abs])

/-!

## B. Infinitely many pure states

-/

/-- The Riesz isomorphism between `EuclideanSpace ℝ (Fin 3)` and its dual. -/
noncomputable def toDualEquiv :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :=
  InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 3))

/-- The Bloch vector `(t, √(1 - t²), 0)`, a unit vector for `t ∈ [0, 1]`. -/
noncomputable def blochVec (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![t, Real.sqrt (1 - t ^ 2), 0]

lemma norm_blochVec {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ‖blochVec t‖ = 1 := by
  rw [blochVec, EuclideanSpace.norm_eq]
  have heq : ∑ i, ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm
      (![t, Real.sqrt (1 - t ^ 2), 0] : Fin 3 → ℝ) i‖ ^ 2 =
      ∑ i, ‖(![t, Real.sqrt (1 - t ^ 2), 0] : Fin 3 → ℝ) i‖ ^ 2 := rfl
  rw [heq, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Real.norm_eq_abs, sq_abs]
  have h1t2 : (0 : ℝ) ≤ 1 - t ^ 2 := by nlinarith
  rw [Real.sq_sqrt h1t2, show t ^ 2 + (1 - t ^ 2) + (0 : ℝ) ^ 2 = 1 from by ring]
  exact Real.sqrt_one

lemma blochVec_injective : Function.Injective fun t : Set.Icc (0 : ℝ) 1 => blochVec t := by
  intro t1 t2 h
  have h' := congrArg (EuclideanSpace.equiv (Fin 3) ℝ) h
  simp only [blochVec] at h'
  have := congrFun h' 0
  simpa using Subtype.ext this

/-- The pure state dual to the Bloch vector at parameter `t ∈ [0, 1]`. -/
noncomputable def purePoint (t : Set.Icc (0 : ℝ) 1) : 𝓢[ℝ, Qubit] :=
  NormCone.stateOfDual (toDualEquiv (blochVec t)) (by
    rw [toDualEquiv, LinearIsometryEquiv.norm_map, norm_blochVec t.2.1 t.2.2])

lemma image_toDualEquiv_closedBall :
    toDualEquiv '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 = {g | ‖g‖ ≤ 1} := by
  ext g
  refine ⟨?_, fun hg => ⟨toDualEquiv.symm g, by simpa using hg, by simp⟩⟩
  rintro ⟨v, hv, rfl⟩
  simpa using hv

/-- Every state `purePoint t` is pure: its Bloch vector lies on the sphere, and the sphere
consists of extreme points of the ball. -/
lemma isPure_purePoint (t : Set.Icc (0 : ℝ) 1) : (purePoint t).IsPure := by
  rw [purePoint, NormCone.isPure_stateOfDual_iff, ← image_toDualEquiv_closedBall,
    ← image_extremePoints]
  exact ⟨_, StrictConvexSpace.sphere_subset_extremePoints_closedBall _ one_ne_zero
    (by simpa using norm_blochVec t.2.1 t.2.2), rfl⟩

lemma purePoint_injective : Function.Injective purePoint := fun _ _ h =>
  blochVec_injective (toDualEquiv.injective (by simpa [purePoint] using congrArg dualOf h))

/-- **The qubit is not classical**: it has infinitely many pure states, while a simplex has
finitely many extreme points. -/
lemma not_isSimplex_stateSpace :
    ¬ IsSimplex (UnitalPositiveLinearMap.algebraicStateSpace (E := Qubit)) := fun h => by
  have : Infinite (Set.Icc (0 : ℝ) 1) := Set.Icc.infinite (by norm_num)
  exact Set.infinite_range_of_injective (f := fun t => (purePoint t).toLinearMap)
    (fun _ _ hp => purePoint_injective (UnitalPositiveLinearMap.toLinearMap_injective hp))
    (h.finite.subset (Set.range_subset_iff.2 isPure_purePoint))

end Qubit

end ProbabilisticTheory
