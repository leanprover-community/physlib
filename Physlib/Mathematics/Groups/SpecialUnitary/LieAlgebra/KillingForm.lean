/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.Algebra.Lie.TraceForm
public import Physlib.Mathematics.Groups.SpecialUnitary.LieAlgebra.Adjoint
/-!

# The Killing form of `su(n)`

The Killing form of `su(n)` and its complexification, and its relation to the adjoint contraction.

## i. Overview

The Killing form `K(A, B) = tr (ad A ∘ ad B)` of the complexification is computed by transporting
`ad A ∘ ad B` to the matrices, where it is `M ↦ -[A, [B, M]]`, the sign coming from the factor `i`
in the bracket. Its trace is `-2n tr (A B)` (A).

The contractions `adjointℂContr` and `adjointContr` of adjoint indices are therefore `-1 / (2n)`
times the Killing forms of the complexification and of `su(n)` (B).

## ii. Key results

- `SULieAlgebra.killingForm_eq_trace` : the Killing form of the complexification is `-2n` times
  the trace form.
- `SULieAlgebra.adjointℂContr_eq_killingForm` : the complex contraction is `-1 / (2n)` times the
  Killing form.
- `SULieAlgebra.adjointContr_eq_killingForm` : the real contraction is `-1 / (2n)` times the
  Killing form.

## iii. Table of contents

- A. The Killing form as a trace
- B. The contraction as the Killing form

## iv. References

* None.

-/

@[expose] public section

open Matrix TensorProduct Kronecker LieAlgebra

namespace SULieAlgebra

/-!

## A. The Killing form as a trace

-/

/-- The Killing form of the complexification is the trace form of the matrices,
  `K(A, B) = -2n tr (A B)`. The sign comes from the factor `i` in the bracket, which makes
  `ad A ∘ ad B` the map `M ↦ -[A, [B, M]]`. -/
lemma killingForm_eq_trace {n : ℕ} (A B : Complexification n) :
    killingForm ℂ (Complexification n) A B = - (2 * n) * (toMatrixℂ A * toMatrixℂ B).trace := by
  let e : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] (Fin n × Fin n → ℂ) :=
    .ofBijective ⟨⟨vec, vec_add⟩, vec_smul⟩ vec_bijective
  let F := e.symm.conj <| toLin' <| -(1 ⊗ₖ (toMatrixℂ A * toMatrixℂ B)
    - (toMatrixℂ B)ᵀ ⊗ₖ toMatrixℂ A - (toMatrixℂ A)ᵀ ⊗ₖ toMatrixℂ B
    + (toMatrixℂ B * toMatrixℂ A)ᵀ ⊗ₖ 1)
  have hF (M) : F M = -(toMatrixℂ A * (toMatrixℂ B * M - M * toMatrixℂ B)
      - (toMatrixℂ B * M - M * toMatrixℂ B) * toMatrixℂ A) := e.symm_apply_eq.2 <| by
    simp [e, kronecker_mulVec_vec, ← vec_sub, ← vec_add, ← vec_neg, vec_inj]
    noncomm_ring
  have hF' (M) : F M ∈ LinearMap.ker (traceLinearMap (Fin n) ℂ ℂ) := by
    simp [hF, trace_mul_comm (toMatrixℂ A)]
  have h1 : equivTraceKer.conj (ad ℂ _ A ∘ₗ ad ℂ _ B) = F.restrict fun M _ => hF' M :=
    LinearMap.ext fun M => Subtype.ext <| by
      simp [hF, toMatrixℂ_lie, ← smul_sub, smul_smul]
  rw [killingForm_apply_apply, ← LinearMap.trace_conj' _ equivTraceKer, h1,
    LinearMap.trace_restrict_eq_of_forall_mem _ _ hF']
  simp [F, trace_kronecker, -transpose_mul, trace_mul_comm (toMatrixℂ B), trace_toMatrixℂ]
  ring

/-!

## B. The contraction as the Killing form

-/

/-- The contraction is the Killing form on the complexified Lie
  algebra, up to a factor of `-1/(2n)`. -/
lemma adjointℂContr_eq_killingForm {n : ℕ} (A B : Complexification n) :
    adjointℂContr (A ⊗ₜ B) = -(1 / (2 * (n : ℂ))) * killingForm ℂ (Complexification n) A B := by
  rw [killingForm_eq_trace, adjointℂContr_tmul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Matrix.trace]
  · have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp

/-- The contraction is the Killing form on the Lie algebra, up to a factor of `-1/(2n)`. -/
lemma adjointContr_eq_killingForm {n : ℕ} (x y : SULieAlgebra n ℂ) :
    adjointContr (x ⊗ₜ y) = -(1 / (2 * (n : ℝ))) * killingForm ℝ (SULieAlgebra n ℂ) x y := by
  have h := adjointℂContr_eq_killingForm (1 ⊗ₜ x) (1 ⊗ₜ y)
  rw [adjointℂContr_one_tmul, killingForm, LieModule.traceForm_baseChange,
    LinearMap.BilinForm.baseChange_tmul, mul_one, Complex.real_smul, mul_one] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

end SULieAlgebra
