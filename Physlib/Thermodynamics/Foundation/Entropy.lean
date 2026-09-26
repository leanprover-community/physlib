/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Thermodynamics.Foundation.Comparability

/-!
# Entropy representations

## i. Overview

The **Entropy Principle** asks for a single real-valued function `S` on all states of all systems
that encodes the adiabatic-accessibility preorder `≺`: monotone (`X ≺ Y ⟺ S(X) ≤ S(Y)` on
comparable states), additive under composition, and extensive under scaling.
`EntropyRepresentation` bundles `S` together with exactly these three properties.
Lieb-Yngvason build such an `S` explicitly as `S(X) = sup {t | R_t ≺ X}`, where
`R_t = ((1-t)•X₀, t•X₁)` mixes two fixed reference states `X₀ ≺≺ X₁`; the accessibility axioms
A1-A6 are what make that supremum well-defined, monotone, additive and extensive.

The `Monotonicity` field is conditioned on `Comparable` and the equivalence
`X ≺ Y ↔ S(X) ≤ S(Y)` is asserted only when `X` and `Y` are comparable. This follows
Lieb-Yngvason, who state the equivalence only in that case, and it keeps to the design
choice that comparison hypotheses are carried as explicit assumptions rather than built
into the accessibility relation `≺`

## ii. Key results

- `AllStates` — the sigma-typed domain: every state packaged with its system.
- `EntropyRepresentation` — entropy `S` bundled with monotonicity, additivity, extensivity.
- `entropy_equiv_iff_eq` / `entropy_strict_iff_lt` — the equivalence and strict forms of
  monotonicity.
- `AffineUniqueness` — the statement (not a field, not proved here) that any two
  representations agree up to a positive affine recalibration `S ↦ aS + b`.

## iii. Table of contents

- A. The domain of entropy
- B. Entropy as an order representation
- C. Consequences of the entropy principle
- D. Essential uniqueness

## iv. References

- E.H. Lieb and J. Yngvason, *The Physics and Mathematics of the Second Law of
  Thermodynamics*, Physics Reports **310** (1999)
- E.H. Lieb and J. Yngvason, *The Mathematical Structure of the Second Law of
  Thermodynamics*, Current Developments in Mathematics **2001** (2002)
-/

@[expose] public section

namespace Thermodynamics

universe u

/-! ## A. The domain of entropy

An entropy function must range over *all* states of *all* systems at once, compound
systems included, so that additivity `S(X, Y) = S(X) + S(Y)` can even be stated across
systems. We package a state together with the system it belongs to as a sigma type. -/

/-- The type of all states of all systems in a thermodynamic core: a state packaged with
the system it belongs to. This sigma type is the domain of an entropy representation. -/
def AllStates (System : Type u) [T : ThermoSystemCore System] :=
  Σ Γ : System, T.State Γ

/-! ## B. Entropy as an order representation

This section turns the Entropy Principle into the structure `EntropyRepresentation`: an `S`
on `AllStates` bundling monotonicity, additivity, and extensivity.

Extensivity can almost be derived from additivity, which makes the small gap between them
one of the more interesting features of the entropy principle. For rational scaling factors
there is no gap at all: given the recombination axiom A5, which lets equal samples of a
state be combined into a scaled copy, additivity already forces `S(t • X) = t · S(X)`
whenever `t` is rational. Extensivity earns its independence at the irrational factors. By
the axiom of choice, through a Hamel-basis construction, any `S` satisfying monotonicity and
additivity can be altered so that extensivity fails at some irrational `t`. So extensivity
is never quite redundant, even when A5 holds, and here, where the structure is only a bare
`ThermoSystemCore` without A5, it must be assumed outright for every factor. -/

/-- An entropy representation of a thermodynamic core: a real-valued `S` on `AllStates` with
monotonicity, additivity, and extensivity as its fields. -/
structure EntropyRepresentation (System : Type u) [T : ThermoSystemCore System] where
  /-- The entropy of an arbitrary state, packaged with its system. -/
  S : AllStates System → ℝ
  /-- Monotonicity: for comparable states, accessibility is equivalent to entropy
  increase, `X ≺ Y ↔ S(X) ≤ S(Y)`. Conditioned on `Comparable` because the equivalence is
  claimed only for comparable states. -/
  Monotonicity {Γ₁ Γ₂ : System} (X : T.State Γ₁) (Y : T.State Γ₂) :
    Comparable (T := T) X Y → (T.le X Y ↔ S ⟨Γ₁, X⟩ ≤ S ⟨Γ₂, Y⟩)
  /-- Additivity: `S(X, Y) = S(X) + S(Y)` across a composition. -/
  Additivity {Γ₁ Γ₂ : System} (X : T.State Γ₁) (Y : T.State Γ₂) :
    S ⟨T.comp Γ₁ Γ₂, T.state_of_comp_equiv.symm (X, Y)⟩ =
      S ⟨Γ₁, X⟩ + S ⟨Γ₂, Y⟩
  /-- Extensivity: `S(t • X) = t · S(X)` for `t > 0`. -/
  Extensivity {Γ : System} (X : T.State Γ) {t : ℝ} (ht : 0 < t) :
    S ⟨T.scale t Γ, (T.state_of_scale_equiv (ne_of_gt ht)).symm X⟩ =
      t * S ⟨Γ, X⟩

/-! ## C. Consequences of the entropy principle

Monotonicity has two immediate corollaries. On comparable states, adiabatic equivalence is
equality of entropy and strict accessibility is strict entropy increase. These are the
"entropy increases in an irreversible process" readings of `S`. -/

section Consequences

variable {System : Type u} [T : ThermoSystemCore System]

local infix:50 " ≺ " => T.le
local notation:50 X " ≈ " Y => X ≺ Y ∧ Y ≺ X
local infix:50 " ≺≺ " => StrictlyPrecedes (T := T)

/-- For comparable states, adiabatic equivalence is equality of entropy `X ≈ Y ↔ S(X) = S(Y)`. -/
lemma entropy_equiv_iff_eq {E : EntropyRepresentation System} {Γ₁ Γ₂ : System}
    (X : T.State Γ₁) (Y : T.State Γ₂) (h_comp : Comparable (T := T) X Y) :
    (X ≈ Y) ↔ E.S ⟨Γ₁, X⟩ = E.S ⟨Γ₂, Y⟩ := by
  rw [E.Monotonicity X Y h_comp]
  have h_comp_symm : Comparable (T := T) Y X := Comparable.symm h_comp
  rw [E.Monotonicity Y X h_comp_symm]
  exact le_antisymm_iff.symm

/-- For comparable states, strict accessibility is strict entropy increase:
`X ≺≺ Y ↔ S(X) < S(Y)`. -/
lemma entropy_strict_iff_lt {E : EntropyRepresentation System} {Γ₁ Γ₂ : System}
    (X : T.State Γ₁) (Y : T.State Γ₂) (h_comp : Comparable (T := T) X Y) :
    X ≺≺ Y ↔ E.S ⟨Γ₁, X⟩ < E.S ⟨Γ₂, Y⟩ := by
  rw [StrictlyPrecedes]
  rw [E.Monotonicity X Y h_comp]
  have h_comp_symm : Comparable (T := T) Y X := Comparable.symm h_comp
  rw [E.Monotonicity Y X h_comp_symm]
  exact Iff.symm lt_iff_le_not_ge

end Consequences

/-! ## D. Essential uniqueness

Lieb-Yngvason's entropy is unique only up to a positive affine change of scale
`S ↦ aS + b`. We record that statement as a `Prop`. -/

/-- Essential affine uniqueness of entropy representations: any two
representations agree up to a positive affine recalibration `S ↦ a * S + b` (`a > 0`). -/
def AffineUniqueness (System : Type u) [T : ThermoSystemCore System] : Prop :=
  ∀ E E' : EntropyRepresentation System,
    ∃ a b : ℝ, 0 < a ∧ ∀ x, E'.S x = a * E.S x + b

end Thermodynamics
