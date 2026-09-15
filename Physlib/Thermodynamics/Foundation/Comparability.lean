/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Thermodynamics.Foundation.Core

/-!
# Comparability of thermodynamic states

## i. Overview

Two states are *comparable* when at least one is adiabatically accessible from the other.
They are *adiabatically equivalent* when accessibility holds in both directions. When it
holds in only one direction, one state *strictly precedes* the other - this is what makes
a process irreversible.

Lieb-Yngvason's **comparison hypothesis** (CH) asserts that any two states of one state
space are comparable. Crucially, CH is a *hypothesis*, and one of the aims of the paper is
to *derive* it for simple systems from the thermal axioms, so we keep it as a named `Prop`
that later entropy constructions carry as a separate assumption.

The hypothesis comes in a strictly ordered hierarchy of scopes: `ComparisonHypothesis Γ`,
comparing only the states of one system, is strictly weaker than CH restricted to all
two-fold scaled products `(1−λ)Γ × λΓ`, which in turn is strictly weaker than
`GlobalComparisonHypothesis`, comparing states across every pair of systems.

## ii. Key results

- `Comparable` — either state is accessible from the other.
- `ComparisonHypothesis` — CH for a single system, the weakest tier of the scope
  hierarchy above.
- `GlobalComparisonHypothesis` — any two states of any two systems are comparable.
- `StrictlyPrecedes` (`≺≺`) — irreversible accessibility.
- `Comparable.symm` — comparability is symmetric.

## iii. Table of contents

- A. Comparability

## iv. References

- E.H. Lieb and J. Yngvason, *The Physics and Mathematics of the Second Law of
  Thermodynamics*, Physics Reports **310** (1999) 1-96.
-/

@[expose] public section

namespace Thermodynamics

universe u

/-! ## A. Comparability

The comparability vocabulary over a bare operational core. -/

section Core

variable {System : Type u} [T : ThermoSystemCore System]

/-- Two states are comparable if either is adiabatically accessible from the other,
`X ≺ Y ∨ Y ≺ X`. -/
def Comparable {Γ₁ Γ₂ : System} (X : T.State Γ₁) (Y : T.State Γ₂) : Prop :=
  T.le X Y ∨ T.le Y X

/-- The comparison hypothesis for a single system: any two of its states are comparable.
This is the weakest tier of the scope hierarchy described in the module overview. -/
def ComparisonHypothesis (Γ : System) : Prop :=
  ∀ X Y : T.State Γ, Comparable (T := T) X Y

/-- The global comparison hypothesis: any two states, possibly of different systems, are
comparable. The strongest tier of the scope hierarchy described in the module
overview. -/
def GlobalComparisonHypothesis (System : Type u) [T : ThermoSystemCore System] : Prop :=
  ∀ {Γ₁ Γ₂ : System} (X : T.State Γ₁) (Y : T.State Γ₂), Comparable (T := T) X Y

/-- Strict adiabatic accessibility `X ≺≺ Y`: `X ≺ Y` but not `Y ≺ X`. These are the
irreversible processes, the ones with strictly increasing entropy. -/
def StrictlyPrecedes {Γ₁ Γ₂ : System} (X : T.State Γ₁) (Y : T.State Γ₂) : Prop :=
  T.le X Y ∧ ¬ T.le Y X

namespace Comparable

/-- Comparability is symmetric. -/
lemma symm {Γ₁ Γ₂ : System} {X : T.State Γ₁} {Y : T.State Γ₂}
    (h : Comparable (T := T) X Y) : Comparable (T := T) Y X :=
  Or.symm h

end Comparable

end Core

end Thermodynamics
