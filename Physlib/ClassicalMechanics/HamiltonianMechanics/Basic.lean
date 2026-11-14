/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

public import Physlib.ClassicalMechanics.PhaseSpace.Basic
public import Physlib.SpaceAndTime.Time.Basic

/-!
# Hamiltonian systems

Smooth time-dependent Hamiltonians on open domains of cotangent phase space.

## i. Overview

A Hamiltonian system specifies a Hamiltonian and an open domain in the phase space of a
configuration space. Smoothness is required on that domain, allowing potentials which are
singular elsewhere, as in central-force systems away from the centre of force.

The coordinate constructors use the global phase-space diffeomorphisms. They preserve the
momentum-first convention `(p, q)` of the existing Hamilton equations and Poisson brackets.
Time retains its affine manifold structure, so constructing a system does not choose a time origin.

## ii. Key results

- `HamiltonianSystem` : a smooth Hamiltonian with an open phase-space domain.
- `HamiltonianSystem.ofCoordinates` : a system from global phase-space coordinates.
- `HamiltonianSystem.ofNormedSpace` : a system from covector-position coordinates.
- `HamiltonianSystem.ofInnerProductSpace` : a system from momentum-vector-position coordinates.

## iii. Table of contents

- A. Hamiltonian systems and their domains
- B. Coordinate constructors

## iv. References

* V. I. Arnold, Mathematical Methods of Classical Mechanics. [ref: arnold_mechanics]
-/

@[expose] public noncomputable section

namespace ClassicalMechanics

open scoped Manifold ContDiff

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  (I : ModelWithCorners ℝ E M) (Q : ConfigurationSpace I)

/-!
## A. Hamiltonian systems and their domains
-/

/-- A time-dependent Hamiltonian smooth on an open domain of the cotangent phase space.
The Hamiltonian is represented by a total function, with smoothness required on the domain. -/
structure HamiltonianSystem where
  /-- The phase-space domain on which the system is defined. -/
  domain : Set (PhaseSpace I Q)
  /-- The phase-space domain is open. -/
  isOpen_domain : IsOpen domain
  /-- The Hamiltonian as a function of time and phase-space state. -/
  hamiltonian : Time × PhaseSpace I Q → ℝ
  /-- The Hamiltonian is smooth in time and state on its domain. -/
  contMDiffOn_hamiltonian : ContMDiffOn
    (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))) 𝓘(ℝ, ℝ) ∞ hamiltonian (Set.univ ×ˢ domain)

end

namespace HamiltonianSystem

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  {I : ModelWithCorners ℝ E M} {Q : ConfigurationSpace I}

/-!
## B. Coordinate constructors
-/

/-- Pull a Hamiltonian and its domain back along global phase-space coordinates. -/
def ofCoordinates {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (e : PhaseSpace I Q ≃ₘ^∞ ⟮I.prod 𝓘(ℝ, E →L[ℝ] ℝ), 𝓘(ℝ, P)⟯ P)
    (U : Set P) (hU : IsOpen U) (H : Time × P → ℝ)
    (hH : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, ℝ) ∞ H (Set.univ ×ˢ U)) :
    HamiltonianSystem I Q where
  domain := e ⁻¹' U
  isOpen_domain := hU.preimage e.contMDiff.continuous
  hamiltonian x := H (x.1, e x.2)
  contMDiffOn_hamiltonian := hH.comp
    (contMDiff_fst.prodMk (e.contMDiff.comp contMDiff_snd)).contMDiffOn
    (fun _ hx ↦ ⟨Set.mem_univ _, hx.2⟩)

variable (U : Set ((E →L[ℝ] ℝ) × E)) (hU : IsOpen U)
  (H : Time × (E →L[ℝ] ℝ) × E → ℝ)
  (hH : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, (E →L[ℝ] ℝ) × E)) 𝓘(ℝ, ℝ) ∞ H
    (Set.univ ×ˢ U))

/-- The Hamiltonian system on a normed space given by `H(t, p, q)` on an open domain `U`,
with momentum `p` in the continuous dual. -/
def ofNormedSpace : HamiltonianSystem 𝓘(ℝ, E) ⟨E⟩ :=
  ofCoordinates (PhaseSpace.normedSpaceDiffeomorph E) U hU H hH

/-- The coordinate constructor preserves membership in the Hamiltonian's domain. -/
@[simp]
lemma mem_domain_ofNormedSpace (p : E →L[ℝ] ℝ) (q : E) :
    PhaseSpace.ofNormedSpace p q ∈ (ofNormedSpace U hU H hH).domain ↔ (p, q) ∈ U := by
  change PhaseSpace.normedSpaceDiffeomorph E
    ((PhaseSpace.normedSpaceDiffeomorph E).symm (p, q)) ∈ U ↔ _
  rw [(PhaseSpace.normedSpaceDiffeomorph E).apply_symm_apply]

/-- The coordinate constructor preserves the value of the Hamiltonian. -/
@[simp]
lemma hamiltonian_ofNormedSpace (t : Time) (p : E →L[ℝ] ℝ) (q : E) :
    (ofNormedSpace U hU H hH).hamiltonian (t, PhaseSpace.ofNormedSpace p q) = H (t, p, q) := by
  change H (t, PhaseSpace.normedSpaceDiffeomorph E
    ((PhaseSpace.normedSpaceDiffeomorph E).symm (p, q))) = _
  rw [(PhaseSpace.normedSpaceDiffeomorph E).apply_symm_apply]

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (U : Set (E × E)) (hU : IsOpen U) (H : Time × E × E → ℝ)
  (hH : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × E)) 𝓘(ℝ, ℝ) ∞ H (Set.univ ×ˢ U))

/-- The Hamiltonian system on a real Hilbert space given by `H(t, p, q)` on an open domain `U`,
with momentum represented by a vector using the Riesz map. -/
def ofInnerProductSpace : HamiltonianSystem 𝓘(ℝ, E) ⟨E⟩ :=
  ofCoordinates (PhaseSpace.innerProductSpaceDiffeomorph E) U hU H hH

/-- The vector-coordinate constructor preserves membership in the Hamiltonian's domain. -/
@[simp]
lemma mem_domain_ofInnerProductSpace (p q : E) :
    PhaseSpace.ofInnerProductSpace p q ∈ (ofInnerProductSpace U hU H hH).domain ↔ (p, q) ∈ U := by
  change PhaseSpace.innerProductSpaceDiffeomorph E
    ((PhaseSpace.innerProductSpaceDiffeomorph E).symm (p, q)) ∈ U ↔ _
  rw [(PhaseSpace.innerProductSpaceDiffeomorph E).apply_symm_apply]

/-- The vector-coordinate constructor preserves the value of the Hamiltonian. -/
@[simp]
lemma hamiltonian_ofInnerProductSpace (t : Time) (p q : E) :
    (ofInnerProductSpace U hU H hH).hamiltonian (t, PhaseSpace.ofInnerProductSpace p q) =
      H (t, p, q) := by
  change H (t, PhaseSpace.innerProductSpaceDiffeomorph E
    ((PhaseSpace.innerProductSpaceDiffeomorph E).symm (p, q))) = _
  rw [(PhaseSpace.innerProductSpaceDiffeomorph E).apply_symm_apply]

end InnerProductSpace

end HamiltonianSystem

end ClassicalMechanics
