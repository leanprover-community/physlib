/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.TraceClass.Polar
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.TraceClass.HilbertSchmidt

/-!

# Basis independence of the trace

## i. Overview

For a trace-class operator `T`, `√|T|` is Hilbert–Schmidt, so the diagonal of `T = (U √|T|) √|T|` is
a diagonal of a product of Hilbert–Schmidt operators. This shows that the trace of every trace-class
operator is an absolutely convergent sum whose value does not depend on the basis.

## ii. Key results

- `isHilbertSchmidt_sqrt_abs_of_isTraceClass` : `√|T|` is Hilbert–Schmidt.
- `summable_trace_diagonal_of_isTraceClass` : the diagonal of a trace-class operator is absolutely
  summable.
- `trace_eq_of_hilbertBasis` : the trace does not depend on the basis.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open scoped ComplexOrder InnerProductSpace
open HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma sqrt_abs_diagonal_eq_norm_sq {T : H →L[ℂ] H} {w : Set H} (b : HilbertBasis w ℂ H)
    (i : w) :
    (⟪b i, CFC.abs T (b i)⟫_ℂ).re = ‖(CFC.sqrt (CFC.abs T)) (b i)‖ ^ 2 := by
  let A : H →L[ℂ] H := CFC.abs T
  let S : H →L[ℂ] H := CFC.sqrt A
  have hAnonneg : 0 ≤ A := CFC.abs_nonneg T
  have hSself : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg A)
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hAnonneg
  have hinner : ⟪b i, A (b i)⟫_ℂ = ⟪S (b i), S (b i)⟫_ℂ := by
    have hSstar : ContinuousLinearMap.adjoint S = S :=
      (ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself
    rw [← hSS]
    show ⟪b i, (S * S) (b i)⟫_ℂ = _
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.adjoint_inner_left S (S (b i)) (b i), hSstar]
  rw [show CFC.abs T = A from rfl, hinner, inner_self_eq_norm_sq_to_K]
  norm_cast

lemma isHilbertSchmidt_sqrt_abs_of_isTraceClass {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsHilbertSchmidt (CFC.sqrt (CFC.abs T)) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  refine ⟨w, b, ?_⟩
  have hdiag : Summable (fun i : w => (⟪b i, CFC.abs T (b i)⟫_ℂ).re) := isTraceClass_iff.mp hT w b
  exact hdiag.congr (fun i => sqrt_abs_diagonal_eq_norm_sq b i)

lemma summable_trace_diagonal_of_isTraceClass {T : H →L[ℂ] H} (hT : IsTraceClass T)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    Summable (fun i : w => ⟪b i, T (b i)⟫_ℂ) := by
  let S : H →L[ℂ] H := CFC.sqrt (CFC.abs T)
  let U : H →L[ℂ] H := Polar.polarFactor T
  have hS : IsHilbertSchmidt S := isHilbertSchmidt_sqrt_abs_of_isTraceClass hT
  have hU : ‖U‖ ≤ 1 := Polar.polarFactor_opNorm_le T
  have hUS : IsHilbertSchmidt (U * S) := isHilbertSchmidt_mul_left_of_opNorm_le_one hU hS
  have hdiag := summable_diagonal_of_hilbertSchmidt b hUS hS
  have hSS : S * S = CFC.abs T := CFC.sqrt_mul_sqrt_self (CFC.abs T) (CFC.abs_nonneg T)
  have hfactor : (U * S) * S = T := by
    rw [mul_assoc, hSS]; exact Polar.polarFactor_mul_absOperator T
  simpa only [hfactor] using hdiag

lemma tsum_diagonal_eq_of_isTraceClass {T : H →L[ℂ] H} (hT : IsTraceClass T)
    {w w' : Set H} (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H) :
    (∑' i : w, ⟪b i, T (b i)⟫_ℂ) = ∑' j : w', ⟪c j, T (c j)⟫_ℂ := by
  let S : H →L[ℂ] H := CFC.sqrt (CFC.abs T)
  let U : H →L[ℂ] H := Polar.polarFactor T
  have hS : IsHilbertSchmidt S := isHilbertSchmidt_sqrt_abs_of_isTraceClass hT
  have hUS : IsHilbertSchmidt (U * S) :=
    isHilbertSchmidt_mul_left_of_opNorm_le_one (Polar.polarFactor_opNorm_le T) hS
  have hSS : S * S = CFC.abs T := CFC.sqrt_mul_sqrt_self (CFC.abs T) (CFC.abs_nonneg T)
  have hfactor : (U * S) * S = T := by
    rw [mul_assoc, hSS]; exact Polar.polarFactor_mul_absOperator T
  have h₁ := HilbertSchmidt.tsum_diagonal_mul_eq_tsum_diagonal_swap (R := U * S) (S := S) b c hUS hS
  have h₂ := HilbertSchmidt.tsum_diagonal_mul_eq_tsum_diagonal_swap (R := S) (S := U * S) c c hS hUS
  rw [hfactor] at h₁ h₂
  calc
    (∑' i : w, ⟪b i, T (b i)⟫_ℂ) = ∑' j : w', ⟪c j, (S * (U * S)) (c j)⟫_ℂ := h₁
    _ = ∑' j : w', ⟪c j, T (c j)⟫_ℂ := h₂

lemma trace_eq_of_hilbertBasis_unconditional {T : H →L[ℂ] H} (hT : IsTraceClass T) {w : Set H}
    (b : HilbertBasis w ℂ H) :
    trace T hT = ∑' i : w, ⟪b i, T (b i)⟫_ℂ := by
  let w₀ : Set H := hT.choose
  let b₀ : HilbertBasis w₀ ℂ H := hT.choose_spec.choose
  change (∑' i : w₀, ⟪b₀ i, T (b₀ i)⟫_ℂ) = ∑' i : w, ⟪b i, T (b i)⟫_ℂ
  exact tsum_diagonal_eq_of_isTraceClass hT b₀ b

/-- **Basis-independent trace evaluation for an arbitrary trace-class operator.** Unlike the
witness-basis definition, this requires no self-adjointness/positivity hypothesis. -/
lemma trace_eq_of_hilbertBasis {T : H →L[ℂ] H} (hT : IsTraceClass T) {w : Set H}
    (b : HilbertBasis w ℂ H) :
    trace T hT = ∑' i : w, ⟪b i, T (b i)⟫_ℂ :=
  trace_eq_of_hilbertBasis_unconditional hT b

end ProbabilisticTheory

end
