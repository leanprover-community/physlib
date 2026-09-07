/-
Copyright (c) 2026 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
module

public import PhyslibAlpha.ClassicalMechanics.NortonDome.NewtonianSystem
public import PhyslibAlpha.ClassicalMechanics.NortonDome.Solution
/-!

# The Norton dome and the determinism of Newtonian mechanics

## i. Overview

A particle at rest on the apex of the Norton dome may stay there forever or slide off at any
instant, in obedience to Newton's second law with a continuous force. This file states what
that does and does not show, in the terms of `NortonDome.NewtonianSystem`.

The dome is such a system (`toNewtonianSystem`). It is not deterministic
(`not_isDeterministic`) and it violates the first law (`not_satisfiesFirstLaw`). Since a locally
Lipschitz force gives determinism, the dome must fail that hypothesis and everything implying
it, and it does (`not_hasLocallyLipschitzForce`, `not_hasLipschitzForce`, `not_hasC2Potential`).
Its force `m √r` is continuous but has infinite slope at the apex, and its potential is `C¹`
but not `C²`.

Put together, this is `exists_continuous_force_not_isDeterministic`: a continuous force does
not make a Newtonian system deterministic, while a locally Lipschitz force, or a `C²`
potential, does. Newton's laws do not say which requirement, if any, belongs in the definition
of a Newtonian system. The theorems say what each requirement buys and that the dome is what
each excludes, and leave the choice open. Malament's proposal, a regularity condition on the
constraint surface in physical space rather than on the potential, is not formulated here. With
Peano's theorem, whose proof is pending in Mathlib, the dome has solutions from every initial
datum (`hasLocalSolutions`), so its failure is one of uniqueness alone.

## ii. Key results

- `NortonDome.not_isDeterministic`: the dome is not deterministic.
- `NortonDome.not_satisfiesFirstLaw`: the dome violates the first law.
- `NortonDome.exists_continuous_force_not_isDeterministic`: Norton's claim, a Newtonian
  system with a continuous force that is not deterministic.
- `NortonDome.not_hasLocallyLipschitzForce`, `NortonDome.not_hasLipschitzForce` and
  `NortonDome.not_hasC2Potential`: the dome satisfies none of the regularity conditions.
- `NortonDome.toNewtonianSystem` is the dome as a Newtonian system, with
  `toNewtonianSystem_force`, `toNewtonianSystem_equationOfMotion_iff` and
  `toNewtonianSystem_isSolution_iff` identifying its force, equation of motion and solutions
  with those of `NortonDome.Basic`.
- `NortonDome.hasLocalSolutions` and `NortonDome.exists_hasLocalSolutions_not_isDeterministic`:
  the dome has local solutions from every initial datum, by Peano's theorem, so its failure of
  determinism is a failure of uniqueness alone (pending the upstream proof).

## iii. Table of contents

- A. The dome as a Newtonian system
- B. The properties the dome fails
  - B.1. Determinism and the first law
  - B.2. The regularity conditions
- C. Norton's claim
- D. Existence without uniqueness

## iv. References

- Norton, J. D., *The dome: an unexpectedly simple failure of determinism*, Philosophy of
  Science 75 (2008), 786–798.
- Malament, D. B., *Norton's slippery slope*, Philosophy of Science 75 (2008), 799–816.

-/

@[expose] public section

namespace ClassicalMechanics.NortonDome
open Real InnerProductSpace Time

variable (S : NortonDome)

/-!

## A. The dome as a Newtonian system

The dome has a differentiable potential, so it is a Newtonian system whose force, equation of
motion and solutions are by definition those of `NortonDome.Basic`.

-/

/-- The Norton dome as a conservative Newtonian system on the Euclidean lift of the arc
  length. -/
noncomputable def toNewtonianSystem : NewtonianSystem (EuclideanSpace ℝ (Fin 1)) where
  m := S.m
  potential := S.potentialEnergy
  m_pos := S.m_pos
  potential_differentiable := S.differentiable_potentialEnergy

/-- The force of the dome as a Newtonian system is its force. -/
lemma toNewtonianSystem_force : S.toNewtonianSystem.force = S.force := rfl

/-- The equation of motion of the dome as a Newtonian system is its equation of motion. -/
lemma toNewtonianSystem_equationOfMotion_iff (r : Time → EuclideanSpace ℝ (Fin 1)) :
    S.toNewtonianSystem.EquationOfMotion r ↔ S.EquationOfMotion r := Iff.rfl

/-- The solutions of the dome as a Newtonian system are its solutions. -/
lemma toNewtonianSystem_isSolution_iff (r : Time → EuclideanSpace ℝ (Fin 1)) :
    S.toNewtonianSystem.IsSolution r ↔ S.IsSolution r := Iff.rfl

/-!

## B. The properties the dome fails

-/

/-!

### B.1. Determinism and the first law

Determinism fails by the non-uniqueness proved in `NortonDome.Solution`. The first law fails
along the motion leaving the apex at the instant `1`: at the instant `0` it is at rest at the
apex, where the force vanishes, and at the instant `2` it is off the apex.

-/

/-- The Norton dome is not deterministic. -/
lemma not_isDeterministic : ¬ S.toNewtonianSystem.IsDeterministic := by
  intro h
  obtain ⟨x, y, hx, hy, h0, hv, hne⟩ := S.exists_isSolution_ne
  exact hne (h x y hx hy 0 h0 hv)

/-- The Norton dome violates Newton's first law, read as a statement about intervals of time:
  a particle at rest at the apex, where the force vanishes, need not stay there. -/
lemma not_satisfiesFirstLaw : ¬ S.toNewtonianSystem.SatisfiesFirstLaw := by
  intro h
  have h2 := h (solution 1) (S.solution_isSolution 1) 0
    (by rw [toNewtonianSystem_force, solution_zero zero_le_one, force_zero])
    (deriv_solution_zero zero_le_one) ((2 : ℝ) : Time)
  have hpos := solution_apply_pos 1 (t := ((2 : ℝ) : Time)) (by rw [Time.realCast_val]; norm_num)
  rw [h2, solution_zero zero_le_one] at hpos
  simp at hpos

/-!

### B.2. The regularity conditions

The force is not Lipschitz on any closed ball about the apex, `not_lipschitzOnWith_force`,
hence not locally Lipschitz; the two stronger conditions imply a locally Lipschitz force, so
they fail too.

-/

/-- The force of the Norton dome is not locally Lipschitz: it is not Lipschitz on any
  neighbourhood of the apex. -/
lemma not_hasLocallyLipschitzForce : ¬ S.toNewtonianSystem.HasLocallyLipschitzForce := by
  intro h
  obtain ⟨K, t, ht, hKt⟩ := h 0
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht
  exact S.not_lipschitzOnWith_force K (half_pos hε)
    (hKt.mono ((Metric.closedBall_subset_ball (by linarith)).trans hball))

/-- The force of the Norton dome is not Lipschitz. -/
lemma not_hasLipschitzForce : ¬ S.toNewtonianSystem.HasLipschitzForce :=
  fun h => S.not_hasLocallyLipschitzForce h.hasLocallyLipschitzForce

/-- The potential of the Norton dome is not `C²`. -/
lemma not_hasC2Potential : ¬ S.toNewtonianSystem.HasC2Potential :=
  fun h => S.not_hasLocallyLipschitzForce h.hasLocallyLipschitzForce

/-!

## C. Norton's claim

-/

/-- Norton's claim: there is a conservative Newtonian system, with a continuous force,
  which is not deterministic. The witness is the dome with unit mass and unit gravitational
  acceleration. -/
lemma exists_continuous_force_not_isDeterministic :
    ∃ N : NewtonianSystem (EuclideanSpace ℝ (Fin 1)), Continuous N.force ∧ ¬ N.IsDeterministic :=
  ⟨(⟨1, 1, one_pos, one_pos⟩ : NortonDome).toNewtonianSystem, force_continuous _,
    not_isDeterministic _⟩

/-!

## D. Existence without uniqueness

The force is continuous and the configuration space is finite-dimensional, so by Peano's
theorem, `NewtonianSystem.hasLocalSolutions_of_continuous_force`, every initial datum has a
local solution: the failure of determinism is purely one of uniqueness. Pending the proof of
Peano's theorem in Mathlib, these results are marked `@[sorryful]`.

-/

/-- The Norton dome has local solutions from every initial position and velocity. Pending the
  proof of Peano's theorem in Mathlib. -/
@[sorryful]
lemma hasLocalSolutions : S.toNewtonianSystem.HasLocalSolutions :=
  NewtonianSystem.hasLocalSolutions_of_continuous_force _ S.force_continuous

/-- Norton's claim, sharpened: there is a Newtonian system with a continuous force which has
  local solutions from every initial datum and is not deterministic. Pending the proof of
  Peano's theorem in Mathlib. -/
@[sorryful]
lemma exists_hasLocalSolutions_not_isDeterministic :
    ∃ N : NewtonianSystem (EuclideanSpace ℝ (Fin 1)),
      Continuous N.force ∧ N.HasLocalSolutions ∧ ¬ N.IsDeterministic :=
  ⟨(⟨1, 1, one_pos, one_pos⟩ : NortonDome).toNewtonianSystem, force_continuous _,
    hasLocalSolutions _, not_isDeterministic _⟩

end ClassicalMechanics.NortonDome

end
