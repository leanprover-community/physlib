/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.LocalNet.QuasilocalOrder
public import Physlib.ProbabilisticTheory.State.Basic

/-!
# States of a local net

Compatible subsystem states and states of the whole system.

## i. Overview

An observable of a smaller subsystem can also be measured in a larger one. A state of the larger
subsystem therefore determines a state of the smaller one: assign each smaller observable the
expectation it has when viewed in the larger system. This operation is called restriction.
Observable inclusions point from smaller to larger subsystems, state restrictions point the other
way.

In a tensor product system, including an observable means letting it act as the identity on the
additional factors. Restricting a density-matrix state then amounts to tracing out those factors.
A `LocalNet.CompatibleStates` assigns a state to every subsystem, with the requirement that a
smaller subsystem's state agrees with the restriction of any larger subsystem's state. Thus the
expectation of an observable does not depend on which containing subsystem is used to evaluate
it.

For a nonempty directed family, local positivity defines an order on the quasilocal observables.
Every compatible family then defines a unique state of the whole system. Conversely, a quasilocal
state restricts to a compatible family of subsystem states.

## ii. Key results

- `LocalNet.restrict`: precomposition with the observable inclusion map.
- `LocalNet.CompatibleStates`: a compatible family of states on the subsystems.
- `LocalNet.CompatibleStates.compat_apply`: compatible states agree on included observables.
- `LocalNet.Quasilocal.toState`: the quasilocal state defined by a compatible family.
- `LocalNet.Quasilocal.stateEquiv`: quasilocal states correspond to compatible local states.

## iii. Table of contents

- A. Restriction of states
- B. Compatible local states
- C. States of the whole system

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

open UnitalPositiveLinearMap

variable {R : Type*} [Preorder R] {A : R → Type*} [∀ X, OrderUnitSpace (A X)]

/-! ## A. Restriction of states -/

namespace LocalNet

variable (N : LocalNet R A) {X Y Z : R}

/-- Restrict a state of `Y` to `X` by pulling it back along the observable inclusion channel. -/
def restrict (h : X ≤ Y) (ω : 𝓢[ℝ, A Y]) : 𝓢[ℝ, A X] := comap (N.incl h) ω

/-- Restriction evaluates an observable through its inclusion into the larger subsystem. -/
@[simp]
lemma restrict_apply (h : X ≤ Y) (ω : 𝓢[ℝ, A Y]) (a : A X) :
    N.restrict h ω a = ω (N.incl h a) := rfl

/-- Restriction to the same subsystem is the identity. -/
@[simp]
lemma restrict_refl (ω : 𝓢[ℝ, A X]) : N.restrict (le_refl X) ω = ω := by
  ext a
  exact congrArg ω (N.incl_refl_apply _ a)

/-- Successive restrictions agree with direct restriction. -/
lemma restrict_restrict (h₁ : X ≤ Y) (h₂ : Y ≤ Z) (h₃ : X ≤ Z) (ω : 𝓢[ℝ, A Z]) :
    N.restrict h₁ (N.restrict h₂ ω) = N.restrict h₃ ω := by
  ext a
  exact congrArg ω (N.incl_trans_apply h₁ h₂ h₃ a).symm

/-!
## B. Compatible local states

A compatible family assigns a state to every local subsystem. Whenever one subsystem is contained
in another, its state must agree with the restriction of the larger subsystem's state. This
ensures that local observables have consistent expectation values, even in infinite systems with
correlations and entanglement.
-/

/-- A state on each subsystem whose restrictions agree with the states of smaller subsystems. -/
@[ext]
structure CompatibleStates (N : LocalNet R A) where
  /-- The state of the subsystem `X`. -/
  state : ∀ X, 𝓢[ℝ, A X]
  /-- The state of `X` is the restriction of the state of any larger subsystem `Y`. -/
  compat : ∀ {X Y : R} (h : X ≤ Y), N.restrict h (state Y) = state X

/-- An observable has the same expectation in every subsystem containing it. -/
lemma CompatibleStates.compat_apply {N : LocalNet R A} (ω : N.CompatibleStates)
    {X Y : R} (h : X ≤ Y) (a : A X) :
    ω.state Y (N.incl h a) = ω.state X a := DFunLike.congr_fun (ω.compat h) a

end LocalNet

namespace LocalNet.Quasilocal

variable {N : LocalNet R A}

/-- Decidable equality used internally by the direct-limit construction. -/
noncomputable local instance : DecidableEq R := Classical.decEq R

/-!
## C. States of the whole system

A quasilocal observable has a local representative. A compatible family evaluates that
representative in its subsystem; compatibility makes the result independent of the representative.
-/

/-- The expectation functional of `LocalNet.CompatibleStates` on the whole system. -/
noncomputable def lift (σ : N.CompatibleStates) : N.Quasilocal →ₗ[ℝ] ℝ := by
  unfold Quasilocal
  refine Module.DirectLimit.lift ℝ R A N.inclLin ?_ ?_
  · intro i
    exact (σ.state i).toLinearMap
  · intro i j hij x
    exact σ.compat_apply hij x

/-- The expectation functional of `LocalNet.CompatibleStates` evaluates a quasilocal observable
in any subsystem representing it. -/
lemma lift_apply (σ : N.CompatibleStates) (i : R) (a : A i) :
    lift σ (toQuasilocal N i a) = σ.state i a := by
  unfold lift toQuasilocal
  exact Module.DirectLimit.lift_of _ _ a

variable [IsDirectedOrder R] [Nonempty R]

/-- The state of the whole system defined by `LocalNet.CompatibleStates`. -/
noncomputable def toState (σ : N.CompatibleStates) : 𝓢[ℝ, N.Quasilocal] := by
  refine ofLinearMap (lift σ) ?_ ?_
  · intro x hx
    obtain ⟨i, a, ha, rfl⟩ := nonneg_iff.1 hx
    rw [lift_apply]
    exact map_nonneg (σ.state i) ha
  · obtain ⟨i⟩ := ‹Nonempty R›
    rw [← toQuasilocal_one i, lift_apply]
    exact map_one _

/-- On a quasilocal observable represented in the subsystem `i`, `toState σ` is the state of `i`. -/
lemma toState_apply (σ : N.CompatibleStates) (i : R) (a : A i) :
    toState σ (toQuasilocal N i a) = σ.state i a :=
  lift_apply σ i a

/-- **A state of the whole system is the same as `LocalNet.CompatibleStates`.** -/
noncomputable def stateEquiv : 𝓢[ℝ, N.Quasilocal] ≃ N.CompatibleStates where
  toFun ω :=
    { state i := comap (toQuasilocalChannel N i) ω
      compat h := by
        ext a
        exact congrArg ω (toQuasilocal_incl h a) }
  invFun σ := toState σ
  left_inv ω := by
    ext x
    obtain ⟨i, a, rfl⟩ := exists_toQuasilocal_eq x
    exact toState_apply _ i a
  right_inv σ := by
    ext i a
    exact toState_apply σ i a

end LocalNet.Quasilocal

end ProbabilisticTheory
