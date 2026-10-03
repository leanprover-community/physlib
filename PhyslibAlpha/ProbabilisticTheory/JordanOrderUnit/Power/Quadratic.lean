/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.Power.Associative

/-!

# Quadratic representations of powers

The quadratic representation on powers: `U_{aᵐ} aⁿ = a²ᵐ⁺ⁿ`.

## i. Overview

On powers the quadratic representation acts by `U_{aᵐ} aⁿ = a²ᵐ⁺ⁿ`.

## ii. Key results

- `JordanAlgebra.quadRep_jpow_jpow` : `U_{aᵐ} aⁿ = a²ᵐ⁺ⁿ`.

## iii. Table of contents

- A. Quadratic action on powers

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace JordanAlgebra

variable {E : Type*} [NonAssocCommRing E] [Module ℝ E] [SMulCommClass ℝ E E]
  [IsCommJordan E]

open scoped JordanAlgebra

/-! ## A. Quadratic action on powers -/

/-- `U_{aᵐ} aⁿ = a²ᵐ⁺ⁿ`. -/
lemma quadRep_jpow_jpow (a : E) (m n : ℕ) :
    U (a ^[m]) (a ^[n]) = a ^[2 * m + n] := by
  rw [quadRep_apply]
  have h₁ : a ^[m] * (a ^[m] * a ^[n]) = a ^[m + (m + n)] := by
    rw [pow_add, pow_add]
  have h₂ : (a ^[m]) ^[2] * a ^[n] = a ^[m + m + n] := by
    rw [jpow_two, pow_add, pow_add]
  rw [h₁, h₂]
  have hdegree₁ : m + (m + n) = 2 * m + n := by omega
  have hdegree₂ : m + m + n = 2 * m + n := by omega
  rw [hdegree₁, hdegree₂]
  module

/-- A single outer factor raises the degree of a power by two. -/
lemma quadRep_jpow (a : E) (n : ℕ) : U a (a ^[n]) = a ^[n + 2] := by
  simpa [jpow_one, Nat.add_comm] using quadRep_jpow_jpow a 1 n

/-- The quadratic representation of a power at the order unit is its even power. -/
lemma quadRep_jpow_one (a : E) (m : ℕ) : U (a ^[m]) (1 : E) = a ^[2 * m] := by
  simpa using quadRep_jpow_jpow a m 0

/-- Quadratic representations compose additively on powers of a common element. -/
lemma quadRep_jpow_comp_jpow (a : E) (m n k : ℕ) :
    U (a ^[m]) (U (a ^[n]) (a ^[k])) = a ^[2 * m + 2 * n + k] := by
  rw [quadRep_jpow_jpow a n k, quadRep_jpow_jpow a m (2 * n + k)]
  congr 1
  omega

end JordanAlgebra

end ProbabilisticTheory
