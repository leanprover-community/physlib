/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Logic.Equiv.Defs

/-!
# Extensive states of a simple thermodynamic system

## i. Overview

An **extensive state** of a single-component simple system is a triple `(U, V, N)` of
internal energy, volume, and particle number, all strictly positive. This module defines the
coordinate domain `posOrthant`, the state type `ExtensiveState` as the subtype of
`ℝ × ℝ × ℝ` cut out by it, and the accessors and constructor used by the rest of the
fundamental-relation development.

## ii. Key results

- `posOrthant` - the open positive orthant of `ℝ × ℝ × ℝ`, the coordinate domain on which a
  fundamental relation is regular.
- `ExtensiveState` - a positive extensive state `(U, V, N)`, as a subtype of `posOrthant`.
- `ExtensiveState.U`/`V`/`N`, `hU`/`hV`/`hN`, `mem_posOrthant` - the read API of coordinate
  accessors, their positivity, and membership in the coordinate domain.
- `ExtensiveState.mk`, `ExtensiveState.ext` - constructor from coordinates with positivity
  proofs, and extensionality from the three coordinates alone.

## iii. Table of contents

- A. The coordinate domain
- B. Extensive states
- C. Accessors and constructor
- D. Extensionality

## iv. References

- H.B. Callen, *Thermodynamics and an Introduction to Thermostatistics*, 2nd ed., Wiley
  (1985). -/

@[expose] public section

namespace Thermodynamics

/-! ## A. The coordinate domain

The calculus in `Intensive.lean` (`ContDiffOn`, `fderivWithin`, `IsOpen.mem_nhds`)
predicates over a *set* in the normed space `ℝ × ℝ × ℝ`, so the regularity domain must be
carried as such a set; smoothness cannot be stated "over `ExtensiveState`" directly. The set
is open because differentiability at a state needs a neighborhood inside the domain, and the
inequalities are strict because the entropy formulas divide by and take logs of the
coordinates. -/

/-- The open positive orthant of `ℝ × ℝ × ℝ`, the coordinate domain on which a
`FundamentalRelation` is regular. -/
def posOrthant : Set (ℝ × ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2}

/-! ## B. Extensive states

The three coordinates completely characterize an equilibrium state of a simple system
(Postulate I) and are mutually independent, no coordinate being a function of the other two.
The state type is the subtype of `ℝ × ℝ × ℝ` cut out by `posOrthant`, so a state's positivity
is its membership in the coordinate domain. -/

/-- A positive **extensive state** `(U, V, N)` of a simple system, the internal energy,
volume, and particle number, all strictly positive. This is the physical domain over which a
`FundamentalRelation` is smooth, homogeneous, and monotone. -/
def ExtensiveState := {p : ℝ × ℝ × ℝ // p ∈ posOrthant}

namespace ExtensiveState

/-! ## C. Accessors and constructor

Thin accessors give the coordinate read API. Here `e.U` reduces definitionally, and `e.hU`
derives positivity from the subtype property. -/

/-- The internal energy of an extensive state. -/
def U (e : ExtensiveState) : ℝ := e.1.1

/-- The volume of an extensive state. -/
def V (e : ExtensiveState) : ℝ := e.1.2.1

/-- The particle number of an extensive state. -/
def N (e : ExtensiveState) : ℝ := e.1.2.2

/-- Positivity of the internal energy, from the subtype property. -/
lemma hU (e : ExtensiveState) : 0 < e.U := e.2.1

/-- Positivity of the volume, from the subtype property. -/
lemma hV (e : ExtensiveState) : 0 < e.V := e.2.2.1

/-- Positivity of the particle number, from the subtype property. -/
lemma hN (e : ExtensiveState) : 0 < e.N := e.2.2.2

/-- An extensive state's coordinates lie in the positive orthant. This is the subtype
property itself. -/
lemma mem_posOrthant (e : ExtensiveState) : (e.U, e.V, e.N) ∈ posOrthant := e.2

/-- Construct an extensive state from its coordinates and their positivity. -/
def mk (U V N : ℝ) (hU : 0 < U) (hV : 0 < V) (hN : 0 < N) : ExtensiveState :=
  ⟨(U, V, N), hU, hV, hN⟩

/-- The energy coordinate of a state built by `mk`. -/
@[simp] lemma U_mk (U V N : ℝ) (hU : 0 < U) (hV : 0 < V) (hN : 0 < N) :
    (mk U V N hU hV hN).U = U := rfl

/-- The volume coordinate of a state built by `mk`. -/
@[simp] lemma V_mk (U V N : ℝ) (hU : 0 < U) (hV : 0 < V) (hN : 0 < N) :
    (mk U V N hU hV hN).V = V := rfl

/-- The particle-number coordinate of a state built by `mk`. -/
@[simp] lemma N_mk (U V N : ℝ) (hU : 0 < U) (hV : 0 < V) (hN : 0 < N) :
    (mk U V N hU hV hN).N = N := rfl

/-! ## D. Extensionality

Extensionality needs only the three coordinates, since the positivity proof is
proof-irrelevant. -/

/-- Two extensive states with the same coordinates are equal, so `(U, V, N)` alone determine
the state. -/
@[ext] lemma ext {e₁ e₂ : ExtensiveState}
    (hU : e₁.U = e₂.U) (hV : e₁.V = e₂.V) (hN : e₁.N = e₂.N) : e₁ = e₂ := by
  apply Subtype.ext
  exact Prod.ext hU (Prod.ext hV hN)

end ExtensiveState

end Thermodynamics
