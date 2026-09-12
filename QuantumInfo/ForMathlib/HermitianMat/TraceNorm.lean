/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.Proj
public import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

/-! # The trace norm of a Hermitian matrix

The Jordan decomposition `A = A⁺ - A⁻` splits a Hermitian matrix into two positive semidefinite
pieces with orthogonal supports, so the trace norm — the sum of the absolute values of the
eigenvalues — is the sum of their traces.
-/

@[expose] public section

namespace HermitianMat

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The trace norm of a Hermitian matrix is the sum of the traces of its positive and negative
parts. -/
theorem traceNorm_eq_trace_posPart_add_negPart (A : HermitianMat d ℂ) :
    A.mat.traceNorm = A⁺.trace + A⁻.trace := by
  rw [Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues A.H, posPart_eq_cfc_max,
    negPart_eq_cfc_min, trace_cfc_eq, trace_cfc_eq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ (max_zero_add_max_neg_zero_eq_abs_self _).symm

end HermitianMat
