/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Physlib.ClassicalMechanics.HamiltonianMechanics.PoissonBracket
/-!

# Liouville integrable systems

Liouville integrability on an open dense domain and conservation along Hamiltonian trajectories.

## i. Overview

A Hamiltonian system on a `2d`-dimensional phase space is *Liouville integrable* when it carries
`d` conserved quantities, one per degree of freedom, that are

- smooth,
- pairwise Poisson-commuting ("in involution"), and
- functionally independent, i.e. their phase-space gradients are linearly independent.

Functional independence need not hold at every point of phase space: the
gradient of the Hamiltonian of the harmonic oscillator vanishes at the equilibrium, and the Kepler
Hamiltonian is singular at the origin of position space. The definition therefore asks for the
conditions on an open *domain* `U` of phase space, which must be dense so that the conditions hold
generically. Without density the empty domain would make every Hamiltonian integrable.

These are the integrability conditions used in the Liouville–Arnold theorem. Its conclusions about
invariant tori and action-angle coordinates require further hypotheses on common level sets and
are not formalized here (see the `TODO` below). What is formalized is the definition itself and its
consequence: each of the `d` conserved quantities really is conserved along the Hamiltonian flow
inside `U`, by reducing to `deriv_comp_eq_poissonBracket` from
`Physlib.ClassicalMechanics.HamiltonianMechanics.PoissonBracket`.

With one degree of freedom the conditions collapse: the Hamiltonian is the only conserved quantity,
involution is automatic, and independence says only that the gradient of the Hamiltonian does not
vanish. `LiouvilleIntegrableOn.oneDegreeOfFreedom` records this, and is how the harmonic oscillator
and the simple pendulum are shown to be integrable.

Following the convention of `poissonBracket`, a phase-space function `f : X → X → ℝ` is read as
`f p q` for a momentum `p` and a position `q`. Since PhysLib has no existing precedent for a
`FiniteDimensional`/`Module.finrank` hypothesis on an abstract phase space, position space is fixed
concretely as `EuclideanSpace ℝ (Fin d)` for an explicit `d : ℕ`, matching the indexing convention
already used for e.g. `RigidBody (d : ℕ)`.

## ii. Key results

- `LiouvilleIntegrableOn` : the structure of a Liouville integrable system for a Hamiltonian `H`
  on an open dense domain `U` of phase space.
- `LiouvilleIntegrableOn.deriv_comp_eq_zero` : each conserved quantity has zero time derivative
  along a solution of Hamilton's equations for `H` which stays in `U`.
- `LiouvilleIntegrableOn.oneDegreeOfFreedom` : a system with one degree of freedom is Liouville
  integrable wherever its Hamiltonian is smooth with non-vanishing gradient.

## iii. Table of contents

- A. The definition of Liouville integrability
- B. Conservation along the flow
- C. Systems with one degree of freedom

## iv. References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd edition, Chapter 10.
-/

@[expose] public section

namespace ClassicalMechanics

open Time
open scoped ContDiff

TODO "Formalize the conclusion of the Liouville–Arnold theorem (action-angle coordinates,
    invariant tori) — the definition here is only its hypothesis."

/-!

## A. The definition of Liouville integrability

-/

/-- A Liouville integrable system for a Hamiltonian `H` on an open dense domain `U` of the
`2d`-dimensional phase space `EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)`, whose points
are read as `(p, q)`: `d` smooth conserved quantities, one per degree of freedom, that are pairwise
in involution and functionally independent at every point of `U`. -/
structure LiouvilleIntegrableOn {d : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
    (H : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ) where
  /-- The domain on which the system is integrable is open. -/
  isOpen : IsOpen U
  /-- The domain on which the system is integrable is dense, i.e. integrability holds
  generically. -/
  dense : Dense U
  /-- The `d` conserved quantities, one per degree of freedom. -/
  f : Fin d → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ
  /-- The conserved quantities are smooth on `U`. -/
  contDiffOn : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (f i)) U
  /-- The Hamiltonian itself is one of the conserved quantities. -/
  exists_hamiltonian : ∃ i, f i = H
  /-- The conserved quantities pairwise Poisson-commute on `U`, i.e. are in involution. -/
  involutive : ∀ i j, ∀ x ∈ U, poissonBracket (f i) (f j) x.1 x.2 = 0
  /-- The conserved quantities are functionally independent on `U`: their phase-space gradients
  (the `p`- and `q`-partials together) are linearly independent. -/
  independent : ∀ x ∈ U, LinearIndependent ℝ
    (fun i => (gradient (fun p' => f i p' x.2) x.1, gradient (fun q' => f i x.1 q') x.2))

/-!

## B. Conservation along the flow

-/

/-- Each conserved quantity of a Liouville integrable system has zero time derivative along a
solution of Hamilton's equations for `H` which lies in the domain `U` at time `t`. -/
lemma LiouvilleIntegrableOn.deriv_comp_eq_zero {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))}
    {H : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ}
    (LI : LiouvilleIntegrableOn U H)
    (p q : Time → EuclideanSpace ℝ (Fin d)) (t : Time) (i : Fin d)
    (heq : hamiltonEqOp (fun _ => H) p q = 0)
    (hp : DifferentiableAt ℝ p t) (hq : DifferentiableAt ℝ q t) (hU : (p t, q t) ∈ U) :
    ∂ₜ (fun t => LI.f i (p t) (q t)) t = 0 := by
  obtain ⟨i₀, hi₀⟩ := LI.exists_hamiltonian
  have hf : DifferentiableAt ℝ (Function.uncurry (LI.f i)) (p t, q t) :=
    ((LI.contDiffOn i).contDiffAt (LI.isOpen.mem_nhds hU)).differentiableAt (by simp)
  have hderiv := deriv_comp_eq_poissonBracket (fun _ => H) p q (LI.f i) t heq hp hq hf
  have hinv := LI.involutive i i₀ (p t, q t) hU
  rw [hi₀] at hinv
  rw [hderiv]
  exact hinv

/-!

## C. Systems with one degree of freedom

-/

/-- A Hamiltonian system with one degree of freedom is Liouville integrable, with the Hamiltonian as
its single conserved quantity, on any open dense domain on which the Hamiltonian is smooth and has
non-vanishing phase-space gradient. -/
def LiouvilleIntegrableOn.oneDegreeOfFreedom
    {U : Set (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))}
    {H : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) → ℝ}
    (hU : IsOpen U) (hdense : Dense U) (hH : ContDiffOn ℝ ∞ (Function.uncurry H) U)
    (hgrad : ∀ x ∈ U,
      (gradient (fun p' => H p' x.2) x.1, gradient (fun q' => H x.1 q') x.2) ≠ 0) :
    LiouvilleIntegrableOn U H where
  isOpen := hU
  dense := hdense
  f := fun _ => H
  contDiffOn := fun _ => hH
  exists_hamiltonian := ⟨0, rfl⟩
  involutive := fun _ _ _ _ => poissonBracket_self _ _ _
  independent := fun x hx => linearIndependent_unique_iff.mpr (hgrad x hx)

end ClassicalMechanics
