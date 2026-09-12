/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Logic.Equiv.Defs

/-!
# The operational core of thermodynamics

## i. Overview

This module fixes the operational vocabulary of the abstract Lieb-Yngvason accessibility
foundation, with no axioms attached.

The primitive is a relation `≺` of **adiabatic accessibility** between equilibrium
states: `X ≺ Y` means `Y` can be reached from `X` by an interaction with a device and a
weight, the device returning to its initial state while the weight may change height. The
eventual goal is an entropy `S` with `X ≺ Y ↔ S(X) ≤ S(Y)` on comparable states, additive
and extensive, unique up to affine rescaling `S ↦ aS + B` (`a > 0`).

A `ThermoSystemCore` records, for each *system*, its space of equilibrium *states*. Two
operations build new systems from old ones: composition `⊗`, which places two systems
side by side, and scaling `•`, which takes a `t`-sized copy of one. The zero system and
the primitive relation `≺` complete the vocabulary.

## ii. Key results

- `ThermoSystemCore` — the operational vocabulary: systems, states, composition, scaling,
  the zero system, and `≺`.
- `comp_state`, `scale_state` — the states of composed and scaled systems associated to
  component states.
- `instInhabitedZState` — the zero-system state space is inhabited.

## iii. Table of contents

- A. Operational core (`ThermoSystemCore`)
- B. Core API

## iv. References

- E.H. Lieb and J. Yngvason, *The Physics and Mathematics of the Second Law of
  Thermodynamics*, Physics Reports **310** (1999).
- E.H. Lieb and J. Yngvason, *The Mathematical Structure of the Second Law of
  Thermodynamics*, Current Developments in Mathematics **2001** (2002).
-/

@[expose] public section

namespace Thermodynamics

universe u v

/-! ## A. Operational core

The operational vocabulary of thermodynamics, with no axioms attached. The
`AccessibilityAxioms` class states the order axioms directly on this signature, and
`ThermoWorld` bundles them with the system-algebra and cast-coherence layers. The fields
are the primitive relation `≺`, the two system constructors `Γ₁ ⊗ Γ₂` and `t • Γ` with the
identification of their state spaces, and the zero system.

`comp` and `scale` build compound and scaled systems; `state_of_comp_equiv` and
`state_of_scale_equiv` identify their state spaces, and axioms A3-A5 need these
identifications to quantify over composed pairs `(X, Y)` and scaled states `tX`.

`ZSystem` must be given directly rather than built from `scale`: `state_of_scale_equiv`
only identifies state spaces for `t ≠ 0`, so nothing here pins down `scale 0 Γ`. The
`SystemAlgebra` layer later characterizes `ZSystem` as exactly `scale 0 Γ` for every `Γ`
(`scale_zero_is_ZSystem`); its unique state gives `instInhabitedZState`, the only
state-space inhabitation this core guarantees. -/

/-- The operational core of a thermodynamic accessibility structure: a state space for each
system, composition `comp`, scaling `scale`, a zero system `ZSystem`, and the primitive
adiabatic-accessibility relation `le` (`≺`). -/
class ThermoSystemCore (System : Type u) where
  /-- The state space associated to a thermodynamic system. -/
  State : System → Type v
  /-- Composition of thermodynamic systems. -/
  comp : System → System → System
  /-- Extensive scaling of thermodynamic systems by a real parameter. -/
  scale : ℝ → System → System
  /-- Primitive adiabatic accessibility `X ≺ Y`. -/
  le {Γ₁ Γ₂ : System} : State Γ₁ → State Γ₂ → Prop
  /-- The zero system. -/
  ZSystem : System
  /-- The zero system has a unique state. -/
  State_ZSystem_is_Unit : Unique (State ZSystem)
  /-- A state of a composed system is represented by a pair of states of the components. -/
  state_of_comp_equiv {Γ₁ Γ₂ : System} : State (comp Γ₁ Γ₂) ≃ (State Γ₁ × State Γ₂)
  /-- A state of a nonzero-scaled system is represented by a state of the original system. -/
  state_of_scale_equiv {t : ℝ} (ht : t ≠ 0) {Γ : System} : State (scale t Γ) ≃ State Γ

/-! ## B. Core API

Small constructions built directly from the `ThermoSystemCore` fields.
`comp_state` and `scale_state` name the reverse direction of `state_of_comp_equiv` and
`state_of_scale_equiv`: building a composite or scaled state out of its components, which
is the direction most call sites need. `instInhabitedZState` turns the zero system's
unique state into an `Inhabited` instance for typeclass search. -/

section Core

variable {System : Type u} [T : ThermoSystemCore System]

/-- The state of a composed system associated to a pair of component states. -/
def comp_state {Γ₁ Γ₂ : System} (p : T.State Γ₁ × T.State Γ₂) :
    T.State (T.comp Γ₁ Γ₂) :=
  T.state_of_comp_equiv.symm p

/-- The state of a nonzero-scaled system associated to a state of the original system. -/
def scale_state {t : ℝ} (ht : t ≠ 0) {Γ : System} (X : T.State Γ) :
    T.State (T.scale t Γ) :=
  (T.state_of_scale_equiv ht).symm X

/-- The zero-system state space is inhabited. -/
instance instInhabitedZState (System : Type u) [T : ThermoSystemCore System] :
    Inhabited (T.State T.ZSystem) :=
  ⟨T.State_ZSystem_is_Unit.default⟩

end Core

end Thermodynamics
