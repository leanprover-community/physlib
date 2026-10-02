/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.TraceClass.TraceAlgebra
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.TraceClass.Banach

/-!

# The trace pairing

## i. Overview

A bounded operator `A` defines a bounded functional `T ↦ Tr (A T)` on the trace-class operators, of
norm at most `‖A‖`. The assignment `A ↦ Tr (A ·)` is itself a bounded linear map from bounded
operators to the dual of `𝒮₁(H)`.

## ii. Key results

- `norm_trace_le` : `‖Tr T‖ ≤ ‖T‖₁`.
- `TraceClass.tracePairing` : the functional `T ↦ Tr (A T)`.
- `TraceClass.norm_tracePairing_le` : its norm is at most `‖A‖`.
- `TraceClass.tracePairingContinuousLinearMap` : the trace pairing as a bounded linear map into the
  dual.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open scoped ComplexOrder InnerProductSpace

namespace TraceClass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The trace is dominated by the trace norm**, for an arbitrary (not necessarily positive or
self-adjoint) trace-class operator. Proved from the duality bound
`tsum_norm_inner_contraction_le_traceNorm` at the identity contraction. -/
lemma norm_trace_le {T : H →L[ℂ] H} (hT : IsTraceClass T) : ‖trace T hT‖ ≤ traceNorm T hT := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [trace_eq_of_hilbertBasis hT b]
  have h1 : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hnsum : Summable (fun i : w => ‖⟪(1 : H →L[ℂ] H) (b i), T (b i)⟫_ℂ‖) :=
    summable_norm_inner_contraction_of_isTraceClass hT h1 b
  have hnsum' : Summable (fun i : w => ‖⟪b i, T (b i)⟫_ℂ‖) := by simpa using hnsum
  calc
    ‖∑' i : w, ⟪b i, T (b i)⟫_ℂ‖ ≤ ∑' i : w, ‖⟪b i, T (b i)⟫_ℂ‖ := norm_tsum_le_tsum_norm hnsum'
    _ = ∑' i : w, ‖⟪(1 : H →L[ℂ] H) (b i), T (b i)⟫_ℂ‖ := by simp
    _ ≤ traceNorm T hT := tsum_norm_inner_contraction_le_traceNorm hT h1 b

/-- Transporting `trace` across an equality of the underlying operator. Needed because `rw` cannot
rewrite `trace`'s operator argument directly (the motive depends on the witness proof). -/
lemma trace_transport {X Y : H →L[ℂ] H} (hEq : X = Y) (hX : IsTraceClass X) :
    trace X hX = trace Y (hEq ▸ hX) := by
  subst hEq; rfl

/-- Every trace-class `T.1` sandwiched by a bounded `A` on the left (and `1` on the right) is
trace class: the general two-sided ideal estimate, specialized. -/
lemma isTraceClass_mul_coe (A : H →L[ℂ] H) (T : TraceClass H) : IsTraceClass (A * T.1) := by
  have h := isTraceClass_mul_mul (A := A) (B := (1 : H →L[ℂ] H)) (isTraceClass_coe T)
  simpa using h

/-- **The trace pairing at a fixed bounded operator `A`**, `T ↦ Tr(A T)`, as a `ℂ`-linear map on
the trace-class Banach space. -/
def tracePairingLinearMap (A : H →L[ℂ] H) : TraceClass H →ₗ[ℂ] ℂ where
  toFun T := trace (A * T.1) (isTraceClass_mul_coe A T)
  map_add' T T' := by
    have hcoe : (T + T').1 = T.1 + T'.1 := rfl
    have hsum : A * (T + T').1 = A * T.1 + A * T'.1 := by rw [hcoe, mul_add]
    calc
      trace (A * (T + T').1) (isTraceClass_mul_coe A (T + T')) =
          trace (A * T.1 + A * T'.1)
            (hsum ▸ isTraceClass_mul_coe A (T + T')) := trace_transport hsum _
      _ = trace (A * T.1) (isTraceClass_mul_coe A T) +
          trace (A * T'.1) (isTraceClass_mul_coe A T') := by
        rw [trace_add (isTraceClass_mul_coe A T) (isTraceClass_mul_coe A T')]
  map_smul' c T := by
    have hsmul : A * (c • T).1 = c • (A * T.1) := by
      show A * (c • T.1) = c • (A * T.1)
      rw [mul_smul_comm]
    calc
      trace (A * (c • T).1) (isTraceClass_mul_coe A (c • T)) =
          trace (c • (A * T.1)) (hsmul ▸ isTraceClass_mul_coe A (c • T)) :=
        trace_transport hsmul _
      _ = c * trace (A * T.1) (isTraceClass_mul_coe A T) := by
        rw [trace_smul c (isTraceClass_mul_coe A T)]
      _ = (RingHom.id ℂ) c • trace (A * T.1) (isTraceClass_mul_coe A T) := by
        simp

lemma tracePairingLinearMap_apply (A : H →L[ℂ] H) (T : TraceClass H) :
    tracePairingLinearMap A T = trace (A * T.1) (isTraceClass_mul_coe A T) := rfl

/-- **The trace pairing is bounded**: `‖φ_A T‖ ≤ ‖A‖ ‖T‖₁`. Combines `norm_trace_le` with the
general two-sided ideal norm estimate `traceNorm_mul_mul_le`. -/
lemma norm_tracePairingLinearMap_apply_le (A : H →L[ℂ] H) (T : TraceClass H) :
    ‖tracePairingLinearMap A T‖ ≤ ‖A‖ * ‖T‖ := by
  rw [tracePairingLinearMap_apply]
  set hAT := isTraceClass_mul_coe A T
  calc
    ‖trace (A * T.1) hAT‖ ≤ traceNorm (A * T.1) hAT := norm_trace_le hAT
    _ ≤ ‖A‖ * traceNorm T.1 (isTraceClass_coe T) * ‖(1 : H →L[ℂ] H)‖ := by
        have h := traceNorm_mul_mul_le (A := A) (B := (1 : H →L[ℂ] H)) (isTraceClass_coe T) hAT
        simpa using h
    _ ≤ ‖A‖ * traceNorm T.1 (isTraceClass_coe T) * 1 := by
        gcongr
        · exact mul_nonneg (norm_nonneg A) (traceNorm_nonneg _ _)
        · exact ContinuousLinearMap.norm_id_le
    _ = ‖A‖ * ‖T‖ := by rw [mul_one]; rfl

/-- **The trace pairing `T ↦ Tr(A T)`, as a continuous (bounded) linear functional** on the
trace-class Banach space. -/
def tracePairing (A : H →L[ℂ] H) : TraceClass H →L[ℂ] ℂ :=
  (tracePairingLinearMap A).mkContinuous ‖A‖ (norm_tracePairingLinearMap_apply_le A)

lemma tracePairing_apply (A : H →L[ℂ] H) (T : TraceClass H) :
    tracePairing A T = trace (A * T.1) (isTraceClass_mul_coe A T) := rfl

/-- The trace pairing's operator norm is bounded by `‖A‖`. -/
lemma norm_tracePairing_le (A : H →L[ℂ] H) : ‖tracePairing A‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg A) _

/-- **`A ↦ φ_A` is itself a `ℂ`-linear map** from `H →L[ℂ] H` into the strong dual of the
trace-class Banach space. -/
def tracePairingLinear : (H →L[ℂ] H) →ₗ[ℂ] (TraceClass H →L[ℂ] ℂ) where
  toFun := tracePairing
  map_add' A A' := by
    ext T
    have hsum : (A + A') * T.1 = A * T.1 + A' * T.1 := add_mul A A' T.1
    rw [add_apply, tracePairing_apply, tracePairing_apply, tracePairing_apply]
    calc
      trace ((A + A') * T.1) (isTraceClass_mul_coe (A + A') T) =
          trace (A * T.1 + A' * T.1) (hsum ▸ isTraceClass_mul_coe (A + A') T) :=
        trace_transport hsum _
      _ = trace (A * T.1) (isTraceClass_mul_coe A T) +
          trace (A' * T.1) (isTraceClass_mul_coe A' T) :=
        trace_add (isTraceClass_mul_coe A T) (isTraceClass_mul_coe A' T)
  map_smul' c A := by
    ext T
    have hsmul : (c • A) * T.1 = c • (A * T.1) := smul_mul_assoc c A T.1
    rw [smul_apply, tracePairing_apply, tracePairing_apply]
    calc
      trace ((c • A) * T.1) (isTraceClass_mul_coe (c • A) T) =
          trace (c • (A * T.1)) (hsmul ▸ isTraceClass_mul_coe (c • A) T) :=
        trace_transport hsmul _
      _ = c • trace (A * T.1) (isTraceClass_mul_coe A T) := trace_smul c (isTraceClass_mul_coe A T)

/-- The trace pairing `A ↦ (T ↦ Tr (A T))`, as a bounded linear map from bounded operators to the
dual of the trace-class operators. -/
def tracePairingContinuousLinearMap : (H →L[ℂ] H) →L[ℂ] (TraceClass H →L[ℂ] ℂ) :=
  tracePairingLinear.mkContinuous 1 (fun A => by
    have h := norm_tracePairing_le A
    show ‖tracePairing A‖ ≤ 1 * ‖A‖
    rwa [one_mul])

lemma tracePairingContinuousLinearMap_apply (A : H →L[ℂ] H) :
    tracePairingContinuousLinearMap A = tracePairing A := rfl

end TraceClass

end ProbabilisticTheory
