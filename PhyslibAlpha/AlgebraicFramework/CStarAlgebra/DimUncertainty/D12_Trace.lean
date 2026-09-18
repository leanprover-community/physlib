/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Trace obstruction to a scalar commutator in finite dimension

Algebraic complement to the construction of `T_d`, `P_d` in
`D3_GrafoCamino.lean`: in finite dimension no matrix commutator can
equal a nonzero scalar multiple of the identity, while exact
anticommuting unitary pairs do exist.

Two independent statements:

1. Every matrix commutator `[Q,P] = QP - PQ` has trace zero
   (`Matrix.trace_mul_comm`), so it can never equal `c • 1` for
   `c ≠ 0` (`no_nonzero_scalar_exact_commutator`).
2. That obstruction is on the additive commutator; it does not prevent
   multiplicative non-commutativity: the `2×2` matrix pair
   `W₁ = !![0,1;1,0]`, `W₂ = !![1,0;0,-1]` satisfies exactly
   `W₂ W₁ = -(W₁ W₂)` (`parWeyl_anticonmuta`).
-/

@[expose] public section

noncomputable section

namespace ConmutadorEscalarFinito

/-- Matrix commutator. -/
def commutator {d : ℕ}
    (Q P : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Q * P - P * Q

/-- The trace of every finite matrix commutator is zero. -/
theorem trace_commutator_zero {d : ℕ}
    (Q P : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (commutator Q P) = 0 := by
  rw [commutator, Matrix.trace_sub, Matrix.trace_mul_comm Q P, sub_self]

/-- In positive finite dimension, a commutator cannot be a nonzero
scalar multiple of the identity. -/
theorem no_nonzero_scalar_exact_commutator {d : ℕ} (hd : 0 < d)
    (Q P : Matrix (Fin d) (Fin d) ℂ) (c : ℂ) (hc : c ≠ 0) :
    commutator Q P ≠ c • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  intro h
  have ht := congrArg Matrix.trace h
  have hleft : Matrix.trace (commutator Q P) = 0 :=
    trace_commutator_zero Q P
  have hright : Matrix.trace (c • (1 : Matrix (Fin d) (Fin d) ℂ)) = c * d := by
    simp
  rw [hleft, hright] at ht
  have hd0 : (d : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)
  exact (mul_ne_zero hc hd0) ht.symm

/-- Corollary: in particular, the commutator cannot equal an imaginary
multiple `i·c` of the identity for any real `c ≠ 0`. -/
theorem commutador_ne_escalar_imaginario {d : ℕ} (hd : 0 < d)
    (Q P : Matrix (Fin d) (Fin d) ℂ) (c : ℝ) (hc : c ≠ 0) :
    commutator Q P ≠ (Complex.I * (c : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  apply no_nonzero_scalar_exact_commutator hd Q P
  exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hc)

/-! ## An exact Weyl pair in dimension two -/

/-- First matrix of the `2×2` Weyl pair. -/
def W1 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- Second matrix of the `2×2` Weyl pair. -/
def W2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- Exact Weyl relation: `W₂ W₁ = -(W₁ W₂)`. The trace obstruction
above is on the *additive* commutator; it does not prevent this exact
*multiplicative* anticommutation in finite dimension. -/
theorem parWeyl_anticonmuta : W2 * W1 = -(W1 * W2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [W1, W2, Matrix.mul_apply, Fin.sum_univ_two]

/-- In particular, `W₁` and `W₂` do not commute. -/
theorem parWeyl_no_conmuta : W2 * W1 ≠ W1 * W2 := by
  intro h
  have hij := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  norm_num [W1, W2, Matrix.mul_apply, Fin.sum_univ_two] at hij

end ConmutadorEscalarFinito
