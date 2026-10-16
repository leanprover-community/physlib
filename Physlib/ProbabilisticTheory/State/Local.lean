/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.LocalNet.GlobalOrder
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
A `LocalNet.State` assigns a state to every subsystem, with the requirement that a smaller
subsystem's state agrees with the restriction of any larger subsystem's state. Thus the
expectation of an observable does not depend on which containing subsystem is used to evaluate
it.

For a nonempty directed family, local positivity defines an order on the global observables.
Every compatible family then defines a unique state of the whole system. Conversely, a global
state restricts to a compatible family of subsystem states.

## ii. Key results

- `LocalNet.restrict`: precomposition with the observable inclusion map.
- `LocalNet.State`: a compatible family of states on the subsystems.
- `LocalNet.State.compat_apply`: compatible states agree on included observables.
- `LocalNet.Global.ofState`: the global state defined by a compatible family.
- `LocalNet.Global.stateEquiv`: global states correspond to compatible local states.

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
def restrict (h : X ≤ Y) (ω : 𝓢[ℝ, A Y]) : 𝓢[ℝ, A X] := pullback (N.incl h) ω

/-- Restriction evaluates an observable through its inclusion into the larger subsystem. -/
@[simp]
lemma restrict_apply (h : X ≤ Y) (ω : 𝓢[ℝ, A Y]) (a : A X) :
    N.restrict h ω a = ω (N.incl h a) := rfl

/-- Restriction to the same subsystem is the identity. -/
@[simp]
lemma restrict_refl (ω : 𝓢[ℝ, A X]) : N.restrict (le_refl X) ω = ω :=
  DFunLike.ext _ _ fun a => congrArg ω (N.incl_refl _ a)

/-- Successive restrictions agree with direct restriction. -/
lemma restrict_restrict (h₁ : X ≤ Y) (h₂ : Y ≤ Z) (ω : 𝓢[ℝ, A Z]) :
    N.restrict h₁ (N.restrict h₂ ω) = N.restrict (h₁.trans h₂) ω :=
  DFunLike.ext _ _ fun a => congrArg ω (N.incl_trans h₁ h₂ a).symm

/-!
## B. Compatible local states

A compatible family assigns a state to every local subsystem. Whenever one subsystem is contained
in another, its state must agree with the restriction of the larger subsystem's state. This
ensures that local observables have consistent expectation values, even in infinite systems with
correlations and entanglement.
-/

/-- A state on each subsystem whose restrictions agree with the states of smaller subsystems. -/
@[ext]
structure State (N : LocalNet R A) where
  /-- The state of the subsystem `X`. -/
  state : ∀ X, 𝓢[ℝ, A X]
  /-- The state of `X` is the restriction of the state of any larger subsystem `Y`. -/
  compat : ∀ {X Y : R} (h : X ≤ Y), N.restrict h (state Y) = state X

/-- An observable has the same expectation in every subsystem containing it. -/
lemma State.compat_apply {N : LocalNet R A} (ω : N.State) {X Y : R} (h : X ≤ Y) (a : A X) :
    ω.state Y (N.incl h a) = ω.state X a := DFunLike.congr_fun (ω.compat h) a

end LocalNet

namespace LocalNet.Global

variable [DecidableEq R] {N : LocalNet R A}

/-!
## C. States of the whole system

A global observable has a local representative. A compatible family evaluates that representative
in its subsystem; compatibility makes the result independent of the representative.
-/

/-- The expectation functional of a `LocalNet.State` on the observables of the whole system. -/
noncomputable def lift (σ : N.State) : N.Global →ₗ[ℝ] ℝ :=
  Module.DirectLimit.lift ℝ R A N.inclLin
    (fun i => (σ.state i).toLinearMap) (fun _ _ hij x => σ.compat_apply hij x)

/-- The expectation functional of a `LocalNet.State` evaluates a global observable in any
subsystem representing it. -/
lemma lift_of (σ : N.State) (i : R) (a : A i) : lift σ (of N i a) = σ.state i a :=
  Module.DirectLimit.lift_of _ _ a

variable [IsDirectedOrder R] [Nonempty R]

/-- The state of the whole system defined by a `LocalNet.State`. -/
noncomputable def ofState (σ : N.State) : 𝓢[ℝ, N.Global] :=
  ofLinearMap (lift σ)
    (fun x hx => by
      obtain ⟨i, a, ha, rfl⟩ := nonneg_iff.1 hx
      rw [lift_of]
      exact map_nonneg (σ.state i) ha)
    (by rw [← of_one (Classical.arbitrary R), lift_of]; exact map_one _)

/-- On a global observable represented in the subsystem `i`, `ofState σ` is the state of `i`. -/
lemma ofState_of (σ : N.State) (i : R) (a : A i) : ofState σ (of N i a) = σ.state i a :=
  lift_of σ i a

/-- **A state of the whole system is the same as a `LocalNet.State`.** -/
noncomputable def stateEquiv : 𝓢[ℝ, N.Global] ≃ N.State where
  toFun ω :=
    { state i := pullback (ofChannel N i) ω
      compat h := DFunLike.ext _ _ fun a => congrArg ω (of_incl h a) }
  invFun σ := ofState σ
  left_inv _ := DFunLike.ext _ _ fun x =>
    Module.DirectLimit.induction_on x fun i a => ofState_of _ i a
  right_inv σ := LocalNet.State.ext (funext fun i => DFunLike.ext _ _ fun a => ofState_of σ i a)

end LocalNet.Global

end ProbabilisticTheory
