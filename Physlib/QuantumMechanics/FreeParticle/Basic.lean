/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.Meta.Informal.Basic
public import Physlib.QuantumMechanics.Operators.Momentum
/-!

# The free particle on `Space d`

## i. Overview

The free quantum particle is one of the simplest quantum systems.
States for a particle of mass `m` are elements of `SpaceDHilbertSpace d` and evolve according
to the Hamiltonian `p²/2m` with no potential.

## ii. Key results

## iii. Table of contents

- A. Basic properties
- B. Hilbert space
- C. Hamiltonian
- D. As a quantum system

## iv. References

* None.
-/

@[expose] public section

noncomputable section
namespace QuantumMechanics

/-- A free, spinless quantum particle with mass `m > 0` in `Space d`. -/
structure FreeParticle (d : ℕ) where
  /-- The mass (positive). -/
  m : ℝ
  hm : 0 < m

variable {d : ℕ} (Q : FreeParticle d)

namespace FreeParticle

/-!
## A. Basic properties
-/

@[simp]
lemma m_pos : 0 < Q.m := Q.hm

@[simp]
lemma m_nonneg : 0 ≤ Q.m := Q.hm.le

@[simp]
lemma m_ne_zero : Q.m ≠ 0 := Q.hm.ne'

/-!
## B. Hilbert space
-/

/-- The Hilbert space for the free particle. -/
@[nolint unusedArguments]
abbrev HS (_ : FreeParticle d) : Type _ := SpaceDHilbertSpace d

/-!
## C. Hamiltonian
-/

/-- The Hamiltonian, `p²/(2m)`. -/
def hamiltonian : Q.HS →ₗ.[ℂ] Q.HS := (2 * Q.m)⁻¹ • momentumSqOperator

/-- The Hamiltonian for the free particle is essentially self-adjoint.
  This follows immediately from the ess. self-adjointness of the momentum-square operator. -/
informal_lemma hamiltonian_essentially_self_adjoint where
  deps := [``FreeParticle]
  tag := "QM-FP-hamESA"

/-!
## D. As a quantum system
-/

/-- The free particle as a quantum system (self-adjoint Hamiltonian acting on a Hilbert space). -/
informal_definition toQuantumSystem where
  deps := [``FreeParticle]
  tag := "QM-FP-sys"

end FreeParticle
end QuantumMechanics
end
