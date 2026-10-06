/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Examples.NormCone
public import PhyslibAlpha.Mathematics.Convex.LpBall
public import PhyslibAlpha.Mathematics.Geometry.Simplex
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The generalized bit

The generalized bit: the sup-norm cone over `ℝ³`, with an octahedral, non-simplex state space.

## i. Overview

The generalized bit is the norm cone over `ℝ³` with the sup norm in place of the Euclidean norm
of the qubit. Its states form an octahedron with `6` pure states, its vertices. That is finitely
many, but too many for a simplex in a `4`-dimensional space. So the gbit is not classical, and
not a qubit either: the shape of the cone matters, not just the dimension.

## ii. Key results

- `GBit` : the generalized bit.
- `GBit.stateEquiv` : the states are the octahedron.
- `GBit.isPure_purePoint` : the vertices of the octahedron are pure states.
- `GBit.not_isSimplex_stateSpace` : the state space is not a simplex.

## iii. Table of contents

- A. The gbit as a norm cone
- B. Too many pure states

## iv. References

- J. Barrett, *Information processing in generalized probabilistic theories*, Phys. Rev. A 75,
  032304 (2007).
- P. Janotta and H. Lal, *Generalized probabilistic theories without the no-restriction
  hypothesis*, Phys. Rev. A 87, 052131 (2013).

-/

@[expose] public section

namespace ProbabilisticTheory

/-!

## A. The gbit as a norm cone

-/

/-- The generalized bit: `ℝ × ℝ³` ordered by the sup-norm cone. -/
abbrev GBit : Type := NormCone (Fin 3 → ℝ)

namespace GBit

open NormCone HolderDual LpBall

/-- The states of the gbit are the octahedron `∑ i, |a i| ≤ 1`. -/
noncomputable def stateEquiv : 𝓢[ℝ, GBit] ≃ {a : Fin 3 → ℝ // ∑ i, |a i| ≤ 1} := supStateEquiv

/-!

## B. Too many pure states

-/

/-- A functional on `Fin 3 → ℝ` is its vector of values on the standard basis. -/
noncomputable abbrev dualEquiv : ((Fin 3 → ℝ) →L[ℝ] ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  coeffEquiv (Pi.basisFun ℝ (Fin 3))

lemma dualEquiv_symm_image_ball :
    dualEquiv.symm '' {a : Fin 3 → ℝ | ∑ i, |a i| ≤ 1} = {f | ‖f‖ ≤ 1} := by
  rw [← image_coeffEquiv_ball _ norm_eq_sum_abs_basisFun, Set.image_image]
  simp

/-- The pure state whose functional is `±1` times a coordinate. -/
noncomputable def purePoint (j : Fin 3 × Bool) : 𝓢[ℝ, GBit] :=
  stateOfDual (dualEquiv.symm (signedVertex j))
    (by
      rw [norm_eq_sum_abs_basisFun]
      simp only [coeffEquiv_symm_apply_basis]
      exact signedVertex_mem_l1Ball j)

lemma isPure_purePoint (j : Fin 3 × Bool) : (purePoint j).IsPure := by
  rw [purePoint, isPure_stateOfDual_iff, ← dualEquiv_symm_image_ball, ← image_extremePoints]
  exact ⟨_, signedVertex_isExtreme j, rfl⟩

lemma purePoint_injective : Function.Injective purePoint := fun j j' h =>
  signedVertex_injective (by simpa [purePoint] using congrArg dualOf h)

lemma finrank_eq_four : Module.finrank ℝ GBit = 4 := by
  change Module.finrank ℝ (ℝ × (Fin 3 → ℝ)) = 4
  simp [Module.finrank_prod]

/-- **The gbit is not classical**: it has `6` pure states in a `4`-dimensional space, too many
for a simplex. -/
lemma not_isSimplex_stateSpace :
    ¬ IsSimplex (UnitalPositiveLinearMap.algebraicStateSpace (E := GBit)) :=
  fun h => by
    have := h.card_le_finrank_add_one_of_mapsTo (p := fun j => (purePoint j).toLinearMap)
      (fun _ _ hp => purePoint_injective (UnitalPositiveLinearMap.toLinearMap_injective hp))
      isPure_purePoint
    simp [finrank_eq_four] at this

end GBit

end ProbabilisticTheory
