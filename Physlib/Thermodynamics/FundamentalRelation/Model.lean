/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Thermodynamics.Foundation.Entropy
public import Physlib.Thermodynamics.FundamentalRelation.Basic

/-!
# The thermodynamic bridge

## i. Overview

A `ThermoModel Φ` is a model of a smooth coordinate fundamental relation `Φ`
(Callen's `S = S(U, V, N)`) as a concrete abstract thermodynamic core.
It supplies a single system `Γ`, a map `stateOf` from positive extensive states into the
abstract state space, an entropy representation, and two linking
hypotheses - `entropy_agrees` (the coordinate entropy equals the abstract entropy on mapped
states) and `comparison` (the Lieb-Yngvason Comparison Hypothesis on `Γ`).

From these we *derive* the **Entropy Principle** for the model via `entropyPrinciple`: on mapped
states, the coordinate entropy order coincides with adiabatic accessibility,
`Φ.S e₁ ≤ Φ.S e₂ ↔ stateOf e₁ ≺ stateOf e₂`.

## ii. Key results

- `ThermoModel` — a model of `Φ`, bundling a core, a coordinate map, an entropy representation,
  and the two linking hypotheses `entropy_agrees` and `comparison`.
- `ThermoModel.entropyPrinciple` — the derived Entropy Principle: entropy order coincides with
  adiabatic accessibility on mapped states.

## iii. Table of contents

- A. The model
- B. The entropy principle

## iv. References

- E.H. Lieb and J. Yngvason, *The Physics and Mathematics of the Second Law of
  Thermodynamics*, Physics Reports **310** (1999).
- H.B. Callen, *Thermodynamics and an Introduction to Thermostatistics*, 2nd ed., Wiley
  (1985).
-/

@[expose] public section

namespace Thermodynamics

universe u

/-! ## A. The model

`ThermoModel Φ` links the smooth coordinate fundamental relation `Φ` to the abstract
accessibility-and-entropy interface. It bundles a thermodynamic core with a distinguished
system `Γ` and an entropy representation, a map `stateOf` from positive extensive states
into `Γ`, and two hypotheses relating the two descriptions. One, `entropy_agrees`, says that
`Φ.S` equals the abstract entropy of the mapped state, and the other, `comparison`, is the
Comparison Hypothesis on `Γ`. From these, `entropyPrinciple` identifies the coordinate
entropy order with adiabatic accessibility on mapped states. -/

/-- A model of the smooth coordinate fundamental relation `Φ` inside the abstract
accessibility-and-entropy interface. -/
structure ThermoModel (Φ : FundamentalRelation) where
  /-- The abstract type of thermodynamic systems used by this model. -/
  {System : Type u}
  /-- The operational thermodynamic core. -/
  core : ThermoSystemCore System
  /-- The single abstract system the coordinate states map into. -/
  Γ : System
  /-- The abstract entropy representation associated to the core. -/
  entropy : @EntropyRepresentation System core
  /-- The abstract state of a coordinate state: sends each positive extensive state `(U, V, N)`
  to its state in the abstract system `Γ`. -/
  stateOf : ExtensiveState → core.State Γ
  /-- The coordinate entropy agrees with the abstract entropy on mapped states:
  `Φ.S e = entropy.S ⟨Γ, stateOf e⟩`. Equivalently, `stateOf` is entropy-preserving. -/
  entropy_agrees : ∀ e : ExtensiveState,
    Φ.S e.U e.V e.N = entropy.S ⟨Γ, stateOf e⟩
  /-- The Comparison Hypothesis on the system `Γ`: any two states of `Γ` are adiabatically
  comparable. -/
  comparison : ComparisonHypothesis (T := core) Γ

namespace ThermoModel

/-! ## B. The entropy principle

This section states the Entropy Principle for the model. On states in the image of
`stateOf`, the order given by the coordinate entropy `Φ.S` coincides with adiabatic
accessibility in the core. -/

/-- The **Entropy Principle** for the model. On mapped states, the coordinate-entropy order
coincides with adiabatic accessibility, `Φ.S e₁ ≤ Φ.S e₂ ↔ stateOf e₁ ≺ stateOf e₂`. -/
lemma entropyPrinciple {Φ : FundamentalRelation} (M : ThermoModel Φ) (e₁ e₂ : ExtensiveState) :
    (Φ.S e₁.U e₁.V e₁.N ≤ Φ.S e₂.U e₂.V e₂.N) ↔
      M.core.le (M.stateOf e₁) (M.stateOf e₂) := by
  letI := M.core
  rw [M.entropy_agrees e₁, M.entropy_agrees e₂]
  exact (M.entropy.Monotonicity (M.stateOf e₁) (M.stateOf e₂)
    (M.comparison (M.stateOf e₁) (M.stateOf e₂))).symm

end ThermoModel

end Thermodynamics
