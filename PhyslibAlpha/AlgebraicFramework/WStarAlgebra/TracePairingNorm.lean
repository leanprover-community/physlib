/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.TraceClass.Pairing
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.TraceClass.RankOne

/-!
# Rank-one tests for the trace pairing

Ported from `unbounded-alpha-public`'s `WStarAlgebra/TracePairingNorm.lean`. This is the first
concrete step toward the infinite-dimensional predual of `H →L[ℂ] H`. `TraceClass/Pairing.lean`
already proves `‖Tr (A ·)‖ ≤ ‖A‖`; here we prove the converse. The proof is deliberately independent
of any predual or von Neumann algebra instance: rank-one operators test the norm of a bounded
operator, and their trace is computed directly from Parseval. Consequently the trace pairing is an
isometry before the surjectivity part of the predual theorem is constructed.
-/

set_option maxHeartbeats 1000000

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace TraceClass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem isTraceClass_rankOne (x y : H) :
    IsTraceClass (InnerProductSpace.rankOne ℂ x y) := by
  by_cases hy : y = 0
  · subst hy
    have hz : InnerProductSpace.rankOne ℂ x (0 : H) = 0 := by
      ext z
      simp
    rw [hz]
    exact isTraceClass_zero
  · have hyy : IsTraceClass (InnerProductSpace.rankOne ℂ y y) :=
      isTraceClass_rankOne_self y
    have hprod : IsTraceClass
        (InnerProductSpace.rankOne ℂ x y * InnerProductSpace.rankOne ℂ y y) := by
      simpa using (isTraceClass_mul_mul (A := InnerProductSpace.rankOne ℂ x y)
        (B := (1 : H →L[ℂ] H)) hyy)
    have hnorm : (‖y‖ ^ 2 : ℂ) ≠ 0 := by
      exact_mod_cast (pow_ne_zero 2 (norm_ne_zero_iff.mpr hy))
    have heq : (‖y‖ ^ 2 : ℂ)⁻¹ •
        (InnerProductSpace.rankOne ℂ x y * InnerProductSpace.rankOne ℂ y y) =
          InnerProductSpace.rankOne ℂ x y := by
      change (‖y‖ ^ 2 : ℂ)⁻¹ •
          (InnerProductSpace.rankOne ℂ x y ∘L InnerProductSpace.rankOne ℂ y y) = _
      rw [InnerProductSpace.rankOne_comp_rankOne]
      rw [inner_self_eq_norm_sq_to_K]
      rw [smul_smul]
      have hscalar : (‖y‖ ^ 2 : ℂ)⁻¹ * (‖y‖ ^ 2 : ℂ) = 1 := inv_mul_cancel₀ hnorm
      exact hscalar ▸ one_smul ℂ (InnerProductSpace.rankOne ℂ x y)
    rw [← heq]
    exact isTraceClass_smul _ hprod

private theorem trace_rankOne (x y : H) :
    trace (InnerProductSpace.rankOne ℂ x y) (isTraceClass_rankOne x y) =
      ⟪y, x⟫_ℂ := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [trace_eq_of_hilbertBasis (isTraceClass_rankOne x y) b]
  have hsum := b.hasSum_inner_mul_inner y x
  have hterm : (fun i : w =>
      ⟪b i, (InnerProductSpace.rankOne ℂ x y) (b i)⟫_ℂ) =
      (fun i : w => ⟪y, b i⟫_ℂ * ⟪b i, x⟫_ℂ) := by
    funext i
    simp only [InnerProductSpace.rankOne_apply, inner_smul_right]
  rw [hterm]
  exact hsum.tsum_eq

private theorem tracePairing_rankOne (A : H →L[ℂ] H) (x y : H) :
    tracePairing A (ofOperator (InnerProductSpace.rankOne ℂ x y) (isTraceClass_rankOne x y)) =
      ⟪y, A x⟫_ℂ := by
  rw [tracePairing_apply]
  have hcomp : A * InnerProductSpace.rankOne ℂ x y =
      InnerProductSpace.rankOne ℂ (A x) y := by
    rw [show A * InnerProductSpace.rankOne ℂ x y =
        A ∘L InnerProductSpace.rankOne ℂ x y by rfl]
    exact InnerProductSpace.comp_rankOne x y A
  calc
    trace (A * (ofOperator (InnerProductSpace.rankOne ℂ x y)
        (isTraceClass_rankOne x y)).1)
        (isTraceClass_mul_coe A (ofOperator
          (InnerProductSpace.rankOne ℂ x y) (isTraceClass_rankOne x y))) =
        trace (InnerProductSpace.rankOne ℂ (A x) y)
          (hcomp ▸ isTraceClass_mul_coe A (ofOperator
            (InnerProductSpace.rankOne ℂ x y) (isTraceClass_rankOne x y))) :=
      trace_transport hcomp _
    _ = trace (InnerProductSpace.rankOne ℂ (A x) y)
        (isTraceClass_rankOne (A x) y) := by
      congr 1
    _ = ⟪y, A x⟫_ℂ := trace_rankOne (A x) y

/- The trace pairing has the sharp lower bound `‖A‖ ≤ ‖Tr (A ·)‖`. -/
set_option maxHeartbeats 1000000 in
theorem norm_le_tracePairing (A : H →L[ℂ] H) :
    ‖A‖ ≤ ‖tracePairing A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound A (norm_nonneg (tracePairing A))
  intro x
  by_cases hx : A x = 0
  · simpa [hx] using mul_nonneg (norm_nonneg (tracePairing A)) (norm_nonneg x)
  · let y : H := (‖A x‖ : ℂ)⁻¹ • A x
    have hx0 : x ≠ 0 := by
      intro hx0
      apply hx
      simp [hx0]
    let : Nontrivial H := ⟨⟨x, 0, hx0⟩⟩
    have hy : ‖y‖ = 1 := by
      dsimp [y]
      rw [norm_smul, norm_inv, Complex.norm_real]
      simp only [norm_norm]
      field_simp [norm_ne_zero_iff.mpr hx]
    have hpair : ‖tracePairing A
        (ofOperator (InnerProductSpace.rankOne ℂ x y) (isTraceClass_rankOne x y))‖ = ‖A x‖ := by
      rw [tracePairing_rankOne]
      dsimp [y]
      rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
      simp [map_inv₀, Complex.norm_real, norm_inv]
      field_simp [norm_ne_zero_iff.mpr hx]
    have hR : ‖(ofOperator (InnerProductSpace.rankOne ℂ x y)
        (isTraceClass_rankOne x y) : TraceClass H)‖ ≤ ‖x‖ := by
      rw [TraceClass.norm_eq_traceNorm]
      let P : H →L[ℂ] H := InnerProductSpace.rankOne ℂ y y
      have hP : IsTraceClass P := isTraceClass_rankOne_self y
      have hprod : IsTraceClass
          (InnerProductSpace.rankOne ℂ x y * P * (1 : H →L[ℂ] H)) := by
        simpa [P] using (isTraceClass_mul_mul
          (A := InnerProductSpace.rankOne ℂ x y) (B := (1 : H →L[ℂ] H)) hP)
      have heq : InnerProductSpace.rankOne ℂ x y * P =
          InnerProductSpace.rankOne ℂ x y := by
        change InnerProductSpace.rankOne ℂ x y ∘L P = _
        rw [show P = InnerProductSpace.rankOne ℂ y y by rfl,
          InnerProductSpace.rankOne_comp_rankOne]
        rw [inner_self_eq_norm_sq_to_K]
        norm_num [hy]
      have hbound := traceNorm_mul_mul_le
        (A := InnerProductSpace.rankOne ℂ x y) (B := (1 : H →L[ℂ] H)) hP hprod
      have heq' : InnerProductSpace.rankOne ℂ x y * P * (1 : H →L[ℂ] H) =
          InnerProductSpace.rankOne ℂ x y := by
        simpa using heq
      have hPnorm : traceNorm P hP = 1 := by
        simpa [P, hy] using traceNorm_rankOne_self y
      have htransport : traceNorm
          (InnerProductSpace.rankOne ℂ x y * P * (1 : H →L[ℂ] H)) hprod =
          traceNorm (InnerProductSpace.rankOne ℂ x y)
            (isTraceClass_rankOne x y) := by
        simpa using traceNorm_transport heq' hprod
      calc
        traceNorm (InnerProductSpace.rankOne ℂ x y)
            (isTraceClass_rankOne x y) =
            traceNorm (InnerProductSpace.rankOne ℂ x y * P * (1 : H →L[ℂ] H)) hprod :=
          htransport.symm
        _ ≤ ‖InnerProductSpace.rankOne ℂ x y‖ * traceNorm P hP * ‖(1 : H →L[ℂ] H)‖ :=
          hbound
        _ = ‖x‖ := by
          rw [hPnorm]
          simp [InnerProductSpace.norm_rankOne, hy, norm_one]
    calc
      ‖A x‖ = ‖tracePairing A
          (ofOperator (InnerProductSpace.rankOne ℂ x y) (isTraceClass_rankOne x y))‖ := hpair.symm
      _ ≤ ‖tracePairing A‖ *
          ‖(ofOperator (InnerProductSpace.rankOne ℂ x y)
            (isTraceClass_rankOne x y) : TraceClass H)‖ :=
        (tracePairing A).le_opNorm _
      _ ≤ ‖tracePairing A‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left hR (norm_nonneg _)

/-- The concrete trace pairing is isometric; this is the norm half of the `H →L[ℂ] H` predual
theorem. -/
theorem norm_tracePairing (A : H →L[ℂ] H) :
    ‖tracePairing A‖ = ‖A‖ :=
  le_antisymm (norm_tracePairing_le A) (norm_le_tracePairing A)

/-- The operator-to-functional map has the same norm as the operator. -/
theorem norm_tracePairingContinuousLinearMap (A : H →L[ℂ] H) :
    ‖tracePairingContinuousLinearMap A‖ = ‖A‖ := by
  rw [tracePairingContinuousLinearMap_apply, norm_tracePairing]

/--
The trace pairing, packaged as an isometric linear embedding of bounded operators into the
continuous dual of the trace class.

Surjectivity is intentionally a separate theorem (`WStarAlgebra/TracePairingSurjectivity.lean`): it
is the genuinely substantive predual construction, whereas this map and its norm preservation are
available directly from rank-one tests.
-/
def tracePairingLinearIsometry :
    (H →L[ℂ] H) →ₗᵢ[ℂ] (TraceClass H →L[ℂ] ℂ) :=
  { toLinearMap := (tracePairingContinuousLinearMap :
      (H →L[ℂ] H) →L[ℂ] (TraceClass H →L[ℂ] ℂ))
    norm_map' := fun A => norm_tracePairingContinuousLinearMap (H := H) A }

@[simp] theorem tracePairingLinearIsometry_apply (A : H →L[ℂ] H) :
    tracePairingLinearIsometry A = tracePairing A := rfl

theorem tracePairingLinearIsometry_norm (A : H →L[ℂ] H) :
    ‖tracePairingLinearIsometry A‖ = ‖A‖ :=
  (tracePairingLinearIsometry : (H →L[ℂ] H) →ₗᵢ[ℂ] (TraceClass H →L[ℂ] ℂ)).norm_map' A

end TraceClass
