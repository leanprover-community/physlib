/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Physlib.Thermodynamics.Foundation.Comparability

/-!
# Lieb-Yngvason worlds

## i. Overview

A `ThermoWorld` extends the operational core (`Core.lean`) with the assumptions
Lieb-Yngvason place on the adiabatic-accessibility relation `≺`. These fall into three
groups, each carried by its own class so it can be assumed or discharged independently:
`SystemAlgebra`, the algebraic identities making composition an associative, commutative
operation on which scaling acts compatibly; `AccessibilityAxioms`, the six accessibility
axioms A1-A6; and `CastCoherence`, the coherence axioms relating states across *equal*
systems.

The coherence group has no Lieb-Yngvason axiom number. The paper treats identities like
`(Γ₁ ⊗ Γ₂) = (Γ₂ ⊗ Γ₁)` as strict equalities of state spaces and uses them silently, but
in Lean equal systems yield state spaces that are only propositionally equal. So each
identity is paired with a statement that transporting a state along it lands on an
adiabatically-equivalent state, a state `Y` with `X ≈ Y` (`X ≺ Y` and `Y ≺ X`).

## ii. Key results

- `SystemAlgebra` — the algebraic identities of composition and scaling.
- `AccessibilityAxioms` — the six accessibility axioms A1-A6 on `≺`.
- `CastCoherence` — the coherence-of-casts assumptions.
- `ThermoWorld` — the abstract interface bundling all three.
- `thermo_le_refl`, `thermo_le_trans`, `thermo_equiv_refl`, `thermo_equiv_symm`,
  `calcTransThermoLe` — the preorder API exposing A1/A2 for calculation.
- `state_equiv_coherence`, `scale_eq_coherence` — cast-coherence facts derived from A1
  rather than assumed as fields.

## iii. Table of contents

- A. System algebra
- B. Accessibility axioms
- C. Coherence of casts
- D. Lieb-Yngvason worlds
- E. World API

## iv. References

- E.H. Lieb and J. Yngvason, *The Physics and Mathematics of the Second Law of
  Thermodynamics*, Physics Reports **310** (1999)
- E.H. Lieb and J. Yngvason, *The Mathematical Structure of the Second Law of
  Thermodynamics*, Current Developments in Mathematics **2001** (2002)
-/

@[expose] public section

namespace Thermodynamics

universe u v

/-! ## A. System algebra

These identities of systems are used silently in informal treatments, where equal systems
are treated as literally the same. Each is paired with a coherence field in `CastCoherence`
below, which discharges the induced cast on state spaces. -/

/-- `SystemAlgebra` records the algebraic identities of the system constructors: composition
is associative and commutative, scaling distributes over it and composes multiplicatively,
scaling by one is trivial, and scaling by zero gives the zero system. -/
class SystemAlgebra (System : Type u) extends ThermoSystemCore System where
  /-- Scaling by zero gives the zero system. -/
  scale_zero_is_ZSystem (Γ : System) : scale 0 Γ = ZSystem

  /-- Composition of systems is associative, up to equality of systems. -/
  comp_assoc (Γ₁ Γ₂ Γ₃ : System) : comp (comp Γ₁ Γ₂) Γ₃ = comp Γ₁ (comp Γ₂ Γ₃)
  /-- Composition of systems is commutative, up to equality of systems. -/
  comp_comm (Γ₁ Γ₂ : System) : comp Γ₁ Γ₂ = comp Γ₂ Γ₁
  /-- Scaling distributes over composition of systems. -/
  scale_distrib_comp (t : ℝ) (Γ₁ Γ₂ : System) :
    scale t (comp Γ₁ Γ₂) = comp (scale t Γ₁) (scale t Γ₂)
  /-- Successive scalings multiply their scale factors. -/
  smul_smul (t s : ℝ) (Γ : System) : scale (t * s) Γ = scale t (scale s Γ)
  /-- Scaling by one leaves the system unchanged. -/
  one_smul (Γ : System) : scale 1 Γ = Γ

/-! ## B. Accessibility axioms

The fields `A1`-`A6` are reflexivity, transitivity, consistency, scaling invariance,
splitting/recombination (bidirectional, as `≈`), and stability (with an explicit
sequence); none is derivable from the others.

Stability (A6) says accessibility cannot be manufactured from an infinitesimal side
effect: if `(X, εₙ • Z₀) ≺ (Y, εₙ • Z₁)` holds along some sequence `εₙ → 0`, for auxiliary
states `Z₀, Z₁`, then `X ≺ Y` outright, with no auxiliary system needed. It implies the
cancellation law by Theorem 2.1, which is what makes `≺` entropy-representable. -/

/-- `AccessibilityAxioms` bundles the six Lieb-Yngvason axioms A1-A6 on the
adiabatic-accessibility relation `≺`: reflexivity, transitivity, consistency, scaling
invariance, splitting/recombination, and stability. It assumes only the operational core. -/
class AccessibilityAxioms (System : Type u) extends ThermoSystemCore System where
  /-- A1, reflexivity: every state is accessible from itself, `X ≺ X`. -/
  A1 {Γ : System} (X : State Γ) : le X X
  /-- A2, transitivity: `X ≺ Y` and `Y ≺ Z` give `X ≺ Z`. -/
  A2 {Γ₁ Γ₂ Γ₃ : System} {X : State Γ₁} {Y : State Γ₂} {Z : State Γ₃} :
    le X Y → le Y Z → le X Z
  /-- A3, consistency: accessibility is preserved by composition —
  `X₁ ≺ Y₁` and `X₂ ≺ Y₂` give `(X₁, X₂) ≺ (Y₁, Y₂)`. -/
  A3 {Γ₁ Γ₂ Γ₃ Γ₄ : System}
      {X₁ : State Γ₁} {X₂ : State Γ₂} {Y₁ : State Γ₃} {Y₂ : State Γ₄} :
    le X₁ Y₁ → le X₂ Y₂ →
      le (state_of_comp_equiv.symm (X₁, X₂)) (state_of_comp_equiv.symm (Y₁, Y₂))
  /-- A4, scaling invariance: if `X ≺ Y` then `t • X ≺ t • Y` for every `t > 0`. -/
  A4 {Γ₁ Γ₂ : System} {X : State Γ₁} {Y : State Γ₂} {t : ℝ} (ht : 0 < t) :
    le X Y → le ((state_of_scale_equiv ht.ne.symm).symm X)
      ((state_of_scale_equiv ht.ne.symm).symm Y)
  /-- A5, splitting and recombination: for `0 < t < 1` a state is adiabatically equivalent
  to its split into a `t`-copy and a `(1−t)`-copy, `X ≈ (t • X, (1−t) • X)`. -/
  A5 {Γ : System} (X : State Γ) {t : ℝ} (ht : 0 < t ∧ t < 1) :
    le X
      (state_of_comp_equiv.symm
        (((state_of_scale_equiv ht.1.ne').symm X),
          ((state_of_scale_equiv (t := 1 - t) (by
              have hpos : 0 < 1 - t := sub_pos.mpr ht.2
              exact hpos.ne')).symm X))) ∧
    le (state_of_comp_equiv.symm
        (((state_of_scale_equiv ht.1.ne').symm X),
          ((state_of_scale_equiv (t := 1 - t) (by
              have hpos : 0 < 1 - t := sub_pos.mpr ht.2
              exact hpos.ne')).symm X))) X
  /-- A6, stability: accessibility cannot be created by an infinitesimal perturbation.
  If `(X, epsilon_n Z₀)` is adiabatically accessible to `(Y, epsilon_n Z₁)` for some states
  `Z₀, Z₁` along a positive sequence `epsilon_n` tending to zero, then `X` is adiabatically
  accessible to `Y`. -/
  A6_seq {ΓX ΓY ΓZ₀ ΓZ₁ : System} (X : State ΓX) (Y : State ΓY)
      (Z₀ : State ΓZ₀) (Z₁ : State ΓZ₁) :
    (∃ (ε_seq : ℕ → ℝ) (hpos : ∀ n, 0 < ε_seq n),
      Filter.Tendsto ε_seq Filter.atTop (nhds 0) ∧
      (∀ n,
        le
          (state_of_comp_equiv.symm
            (X, (state_of_scale_equiv (ne_of_gt (hpos n))).symm Z₀))
          (state_of_comp_equiv.symm
            (Y, (state_of_scale_equiv (ne_of_gt (hpos n))).symm Z₁)))) → le X Y

/-! ## C. Coherence of casts

Each coherence field relates two *different* constructions (distinct equiv applications, or
`(X, Y)` versus `(Y, X)`) and is not derivable from A1-A6. Every transport is phrased
against a `SystemAlgebra` identity — each `h_eq` is one of `smul_smul`, `one_smul`,
`scale_distrib_comp`, `comp_comm`, `comp_assoc` — which is why this class extends
`SystemAlgebra` rather than the bare core. The two coherence statements that *are* derivable
are provided instead as the lemmas `state_equiv_coherence` and `scale_eq_coherence`;
`comp_ZSystem_is_identity` is the only field making `ZSystem` a composition identity at the
state level. -/

/-- `CastCoherence` supplies the coherence assumptions relating states across *equal* systems:
transporting a state along a `SystemAlgebra` identity lands on an adiabatically-equivalent
state. -/
class CastCoherence (System : Type u) extends SystemAlgebra System where
  /-- Coherence of composing with the zero system: composing a state with the zero system's
  unique state is adiabatically neutral. -/
  comp_ZSystem_is_identity (Γ : System) (X : State Γ) :
    le (state_of_comp_equiv.symm (X, State_ZSystem_is_Unit.default)) X ∧
    le X (state_of_comp_equiv.symm (X, State_ZSystem_is_Unit.default))
  /-- Coherence of successive scaling: `t` applied to `s` applied to `X` agrees with `(t * s)`
  applied to `X`, up to adiabatic equivalence after the system cast. -/
  scale_coherence {t s : ℝ} (ht : t ≠ 0) (hs : s ≠ 0) {Γ : System} (X : State Γ) :
    let X_s := (state_of_scale_equiv hs).symm X
    let X_ts := (state_of_scale_equiv ht).symm X_s
    let X_mul := (state_of_scale_equiv (mul_ne_zero ht hs)).symm X
    let h_eq := smul_smul t s Γ
    le (Equiv.cast (congrArg State h_eq) X_mul) X_ts ∧
    le X_ts (Equiv.cast (congrArg State h_eq) X_mul)
  /-- Coherence of scaling by one. -/
  one_smul_coherence {Γ : System} (X : State Γ) :
    let X_1 := (state_of_scale_equiv (show (1 : ℝ) ≠ 0 from one_ne_zero)).symm X
    let h_eq := one_smul Γ
    le (Equiv.cast (congrArg State h_eq) X_1) X ∧
    le X (Equiv.cast (congrArg State h_eq) X_1)
  /-- Coherence of scaling a composed state. -/
  scale_comp_coherence {t : ℝ} (ht : t ≠ 0) {Γ₁ Γ₂ : System}
      (X : State Γ₁) (Y : State Γ₂) :
    let XY := state_of_comp_equiv.symm (X, Y)
    let tXY := (state_of_scale_equiv ht).symm XY
    let tX := (state_of_scale_equiv ht).symm X
    let tY := (state_of_scale_equiv ht).symm Y
    let tXtY := state_of_comp_equiv.symm (tX, tY)
    let h_eq := scale_distrib_comp t Γ₁ Γ₂
    le (Equiv.cast (congrArg State h_eq) tXY) tXtY ∧
    le tXtY (Equiv.cast (congrArg State h_eq) tXY)
  /-- Coherence of commutativity of composition. -/
  comp_comm_coherence {Γ₁ Γ₂ : System} (X : State Γ₁) (Y : State Γ₂) :
    let XY := state_of_comp_equiv.symm (X, Y)
    let YX := state_of_comp_equiv.symm (Y, X)
    let h_eq := comp_comm Γ₁ Γ₂
    le (Equiv.cast (congrArg State h_eq.symm) YX) XY ∧
    le XY (Equiv.cast (congrArg State h_eq.symm) YX)
  /-- Coherence of associativity of composition. -/
  comp_assoc_coherence {Γ₁ Γ₂ Γ₃ : System} (X : State Γ₁) (Y : State Γ₂)
      (Z : State Γ₃) :
    let XY := state_of_comp_equiv.symm (X, Y)
    let XYZ_L := state_of_comp_equiv.symm (XY, Z)
    let YZ := state_of_comp_equiv.symm (Y, Z)
    let XYZ_R := state_of_comp_equiv.symm (X, YZ)
    let h_eq := comp_assoc Γ₁ Γ₂ Γ₃
    le (Equiv.cast (congrArg State h_eq) XYZ_L) XYZ_R ∧
    le XYZ_R (Equiv.cast (congrArg State h_eq) XYZ_L)

/-! ## D. Lieb-Yngvason worlds

`ThermoWorld` combines the three assumption groups into the single abstract interface used
throughout the development. Every field, `A1`-`A6`, the algebra identities, and the
coherence fields are then available on an instance by plain dot notation. -/

/-- `ThermoWorld` is the abstract Lieb-Yngvason interface, bundling the accessibility axioms
(`AccessibilityAxioms`) with the cast-coherence layer (`CastCoherence`, which carries the
`SystemAlgebra` identities). -/
class ThermoWorld (System : Type u) extends
    AccessibilityAxioms System, CastCoherence System

/-! ## E. World API

Notation (`≺`, `≈`, `⊗`, `•`, `≺≺`) and the preorder lemmas exposing axioms A1 and A2 as
reflexivity and transitivity, plus a `Trans` instance so accessibility chains compose in
`calc` blocks. The section also proves the two cast-coherence statements that need no axiom
of their own: `state_equiv_coherence` and `scale_eq_coherence` each relate a state to its
own transport along a `subst`-able equality, so A1 suffices. -/

section World

variable {System : Type u} [TW : ThermoWorld System]

local infix:50 " ≺ " => TW.le
local notation:50 X " ≈ " Y => X ≺ Y ∧ Y ≺ X
local infixr:70 " ⊗ " => TW.comp
local infixr:80 " • " => TW.scale
local infix:50 " ≺≺ " => StrictlyPrecedes (T := TW)

/-- Reflexivity of adiabatic accessibility, exposed as a lemma from A1. -/
lemma thermo_le_refl {Γ : System} (X : TW.State Γ) : X ≺ X :=
  TW.A1 X

/-- Transitivity of adiabatic accessibility, exposed as a lemma from A2. -/
lemma thermo_le_trans {Γ₁ Γ₂ Γ₃ : System} {X : TW.State Γ₁} {Y : TW.State Γ₂}
    {Z : TW.State Γ₃} (hXY : X ≺ Y) (hYZ : Y ≺ Z) : X ≺ Z :=
  TW.A2 hXY hYZ

/-- Adiabatic equivalence is reflexive. -/
lemma thermo_equiv_refl {Γ : System} (X : TW.State Γ) : X ≈ X :=
  ⟨thermo_le_refl X, thermo_le_refl X⟩

/-- Adiabatic equivalence is symmetric. -/
lemma thermo_equiv_symm {Γ₁ Γ₂ : System} {X : TW.State Γ₁} {Y : TW.State Γ₂}
    (h : X ≈ Y) : Y ≈ X :=
  And.symm h

/-- A `Trans` instance for calculations with adiabatic accessibility. -/
instance calcTransThermoLe {Γ₁ Γ₂ Γ₃ : System} :
    Trans (TW.le : TW.State Γ₁ → TW.State Γ₂ → Prop)
      (TW.le : TW.State Γ₂ → TW.State Γ₃ → Prop)
      (TW.le : TW.State Γ₁ → TW.State Γ₃ → Prop) where
  trans := TW.A2

/-- Coherence of casting along an equality of systems: transporting a state along the
equality yields an adiabatically-equivalent state. Derivable from A1: substituting the
equality reduces the cast to the identity. -/
lemma state_equiv_coherence {Γ₁ Γ₂ : System} (h_sys : Γ₁ = Γ₂) (X : TW.State Γ₁) :
    TW.le X (Equiv.cast (congrArg TW.State h_sys) X) ∧
    TW.le (Equiv.cast (congrArg TW.State h_sys) X) X := by
  subst h_sys
  exact ⟨TW.A1 X, TW.A1 X⟩

/-- Coherence of equal scaling factors: equal factors give the same scaled state up to a
cast along the induced equality of systems. Derivable from A1: substituting `t₁ = t₂`
reduces the cast to the identity. -/
lemma scale_eq_coherence {t₁ t₂ : ℝ} (h_eq : t₁ = t₂) (ht₁ : t₁ ≠ 0) {Γ : System}
    (X : TW.State Γ) :
    let ht₂ : t₂ ≠ 0 := h_eq ▸ ht₁
    let X₁ := (TW.state_of_scale_equiv ht₁).symm X
    let X₂ := (TW.state_of_scale_equiv ht₂).symm X
    let h_sys_eq := congrArg (fun r => TW.scale r Γ) h_eq
    TW.le (Equiv.cast (congrArg TW.State h_sys_eq) X₁) X₂ ∧
    TW.le X₂ (Equiv.cast (congrArg TW.State h_sys_eq) X₁) := by
  subst h_eq
  exact ⟨TW.A1 _, TW.A1 _⟩

end World

end Thermodynamics
