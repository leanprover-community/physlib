/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.TraceClass.IdealNorm
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.TraceClass.Banach

/-!
# Elementary algebra of the unconditional trace

Ported from `unbounded-alpha-public`'s `TraceClass/TraceAlgebra.lean` (only the three facts
actually needed downstream by the concrete `B(H)` trace-pairing construction: `trace_smul`,
`trace_add`, and the bounded-factor cyclicity `trace_mul_cycle`; the source file's Hilbert–Schmidt
cycle and `trace_star`/`traceNorm_add_le_via_diagonal` facts are not needed here and are not
ported — this repo's `IdealNorm.lean` already supplies `traceNorm_add_le` by a different route).

The witness proof in `IsTraceClass` is proof-irrelevant, while the diagonal trace itself is now
known to be basis independent (`GeneralIdeal.lean`'s `trace_eq_of_hilbertBasis`). This file records
the linear scalar law and cyclicity in a form the trace-pairing construction can use without
reopening the witness basis.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Scalar homogeneity of the trace, with the canonical trace-class proof for the scaled
operator. -/
theorem trace_smul {T : H →L[ℂ] H} (c : ℂ) (hT : IsTraceClass T) :
    trace (c • T) (isTraceClass_smul c hT) = c * trace T hT := by
  let hT' : IsTraceClass (c • T) := isTraceClass_smul c hT
  let w : Set H := hT.choose
  let b : HilbertBasis w ℂ H := hT.choose_spec.choose
  have hleft := trace_eq_of_hilbertBasis hT' b
  have hright := trace_eq_of_hilbertBasis hT b
  rw [hleft, hright]
  calc
    (∑' i : w, ⟪b i, (c • T) (b i)⟫_ℂ) =
        ∑' i : w, c * ⟪b i, T (b i)⟫_ℂ := by
      apply tsum_congr
      intro i
      simp [inner_smul_right]
    _ = c * ∑' i : w, ⟪b i, T (b i)⟫_ℂ := tsum_mul_left

/-! ### Additivity and cyclicity -/

/-- Additivity of the unconditional trace. -/
theorem trace_add {T T' : H →L[ℂ] H} (hT : IsTraceClass T) (hT' : IsTraceClass T') :
    trace (T + T') (isTraceClass_add hT hT') = trace T hT + trace T' hT' := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hsum : IsTraceClass (T + T') := isTraceClass_add hT hT'
  rw [trace_eq_of_hilbertBasis hsum b, trace_eq_of_hilbertBasis hT b,
    trace_eq_of_hilbertBasis hT' b]
  calc
    (∑' i : w, ⟪b i, (T + T') (b i)⟫_ℂ) =
        ∑' i : w, (⟪b i, T (b i)⟫_ℂ + ⟪b i, T' (b i)⟫_ℂ) := by
      apply tsum_congr
      intro i
      simp [inner_add_right]
    _ = (∑' i : w, ⟪b i, T (b i)⟫_ℂ) +
        ∑' i : w, ⟪b i, T' (b i)⟫_ℂ :=
      (summable_trace_diagonal_of_isTraceClass hT b).tsum_add
        (summable_trace_diagonal_of_isTraceClass hT' b)

/-- Cyclicity of the trace across a bounded factor and a trace-class factor. -/
theorem trace_mul_cycle {A T : H →L[ℂ] H} (hT : IsTraceClass T) :
    trace (A * T) (isTraceClass_mul_mul (A := A) (B := 1) hT) =
      trace (T * A) (isTraceClass_mul_mul (A := 1) (B := A) hT) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  obtain ⟨hR, hS, hfactor⟩ :=
    isHilbertSchmidt_polarFactor_mul_sqrt_abs_and_sqrt_abs hT
  let R : H →L[ℂ] H := Polar.polarFactor T * CFC.sqrt (CFC.abs T)
  let S : H →L[ℂ] H := CFC.sqrt (CFC.abs T)
  have hfactor' : R * S = T := by simpa [R, S] using hfactor
  have hAR : IsHilbertSchmidt (A * R) :=
    HilbertSchmidt.isHilbertSchmidt_mul_left hR
  have hSA : IsHilbertSchmidt (S * A) :=
    HilbertSchmidt.isHilbertSchmidt_mul_right hS
  have h₁ := HilbertSchmidt.tsum_diagonal_mul_eq_tsum_diagonal_swap
    (R := A * R) (S := S) b b hAR hS
  have h₂ := HilbertSchmidt.tsum_diagonal_mul_eq_tsum_diagonal_swap
    (R := S * A) (S := R) b b hSA hR
  have h₃ : A * T = (A * R) * S := by
    rw [show T = R * S from hfactor'.symm]
    simp only [mul_assoc]
  have h₄ : T * A = R * (S * A) := by
    rw [show T = R * S from hfactor'.symm]
    simp only [mul_assoc]
  let hAT : IsTraceClass (A * T) := by
    simpa using (isTraceClass_mul_mul (A := A) (B := 1) hT)
  let hTA : IsTraceClass (T * A) := by
    simpa using (isTraceClass_mul_mul (A := 1) (B := A) hT)
  rw [trace_eq_of_hilbertBasis hAT b, trace_eq_of_hilbertBasis hTA b]
  calc
    (∑' i : w, ⟪b i, (A * T) (b i)⟫_ℂ) =
        ∑' i : w, ⟪b i, ((A * R) * S) (b i)⟫_ℂ := by
          rw [h₃]
    _ =
        ∑' i : w, ⟪b i, (S * (A * R)) (b i)⟫_ℂ := h₁
    _ = ∑' i : w, ⟪b i, ((S * A) * R) (b i)⟫_ℂ := by
          apply tsum_congr
          intro i
          simp only [mul_assoc]
    _ = ∑' i : w, ⟪b i, (R * (S * A)) (b i)⟫_ℂ := h₂
    _ = ∑' i : w, ⟪b i, (T * A) (b i)⟫_ℂ := by
          rw [h₄]
