/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.TraceClass.GeneralProduct

/-!
# Quantitative trace-norm estimates

Ported from `unbounded-alpha-public`'s `TraceClass/IdealNorm.lean`. This file promotes the
qualitative general ideal theory of `GeneralProduct.lean` to quantitative inequalities: the trace
norm is subadditive (`Banach.lean`'s `traceNorm_add_le` gap) and satisfies the two-sided ideal
estimate `‖A T B‖₁ ≤ ‖A‖ ‖T‖₁ ‖B‖` (`HilbertSpaceInstance.lean`'s `traceNorm_mul_mul_le` gap). The
common engine is a single "duality" bound: for trace-class `A`, any contraction `W`, and any
Hilbert basis, the pairing `∑ᵢ ‖⟪W eᵢ, A eᵢ⟫‖` never exceeds `‖A‖₁`; specializing `W` to the
identity gives `HilbertSpaceInstance.lean`'s `norm_trace_le` gap directly.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Transporting `traceNorm` across an equality of the underlying operator. A small generic helper
needed because `rw` cannot rewrite the operator argument of `traceNorm X hX` directly (its motive
depends on `hX`'s own type). -/
private lemma traceNorm_transport {X Y : H →L[ℂ] H} (hEq : X = Y) (hX : IsTraceClass X) :
    traceNorm X hX = traceNorm Y (hEq ▸ hX) := by
  subst hEq; rfl

/-- The Hilbert–Schmidt square sum of `√|A|` computes the trace norm, in every basis. -/
theorem tsum_sqrt_abs_norm_sq_eq_traceNorm {A : H →L[ℂ] H} (hA : IsTraceClass A) {w : Set H}
    (b : HilbertBasis w ℂ H) :
    (∑' i : w, ‖CFC.sqrt (CFC.abs A) (b i)‖ ^ 2) = traceNorm A hA := by
  rw [traceNorm_eq_of_hilbertBasis hA b]
  refine tsum_congr (fun i => ?_)
  set S : H →L[ℂ] H := CFC.sqrt (CFC.abs A) with hSdef
  have hSself : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg (CFC.abs A))
  have hSS : S * S = CFC.abs A := CFC.sqrt_mul_sqrt_self (CFC.abs A) (CFC.abs_nonneg A)
  have hinner : ⟪b i, CFC.abs A (b i)⟫_ℂ = ⟪S (b i), S (b i)⟫_ℂ := by
    have hSstar : ContinuousLinearMap.adjoint S = S :=
      (ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself
    rw [← hSS, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.adjoint_inner_left S (S (b i)) (b i), hSstar]
  rw [hinner, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The contraction pairing `i ↦ ⟪W eᵢ, A eᵢ⟫` is absolutely summable, for trace-class `A` and any
contraction `W`. -/
theorem summable_norm_inner_contraction_of_isTraceClass {A W : H →L[ℂ] H} (hA : IsTraceClass A)
    (hW : ‖W‖ ≤ 1) {w : Set H} (b : HilbertBasis w ℂ H) :
    Summable (fun i : w => ‖⟪W (b i), A (b i)⟫_ℂ‖) := by
  obtain ⟨hUS, hS, hfactor⟩ := isHilbertSchmidt_polarFactor_mul_sqrt_abs_and_sqrt_abs hA
  set R : H →L[ℂ] H := Polar.polarFactor A * CFC.sqrt (CFC.abs A) with hRdef
  set S : H →L[ℂ] H := CFC.sqrt (CFC.abs A) with hSdef
  have hRstar : IsHilbertSchmidt (ContinuousLinearMap.adjoint R) := by
    rcases hUS with ⟨w₀, b₀, hb₀⟩
    exact ⟨w₀, b₀, summable_norm_sq_adjoint_of_summable_norm_sq b₀ hb₀⟩
  have hRWb : Summable (fun i : w => ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b
      (isHilbertSchmidt_mul_right_of_opNorm_le_one hW hRstar)
  have hSb : Summable (fun i : w => ‖S (b i)‖ ^ 2) := summable_norm_sq_apply_of_hilbertBasis w b hS
  have hpoint : ∀ i : w, ⟪W (b i), A (b i)⟫_ℂ =
      ⟪(ContinuousLinearMap.adjoint R * W) (b i), S (b i)⟫_ℂ := by
    intro i
    rw [show A = R * S from hfactor.symm, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_left R (S (b i)) (W (b i))]
  have hprod : Summable (fun i : w =>
      ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ * ‖S (b i)‖) :=
    summable_norm_mul_of_square_sums _ _ hRWb hSb (fun i => norm_nonneg _) (fun i => norm_nonneg _)
  apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) hprod
  rw [hpoint i]
  exact norm_inner_le_norm _ _

/-- **The duality bound**: for trace-class `A`, any contraction `W`, and any basis, the pairing
`∑ᵢ ‖⟪W eᵢ, A eᵢ⟫‖` never exceeds `‖A‖₁`. This is the single quantitative estimate feeding
subadditivity of the trace norm, and the general two-sided ideal estimate below. -/
theorem tsum_norm_inner_contraction_le_traceNorm {A W : H →L[ℂ] H} (hA : IsTraceClass A)
    (hW : ‖W‖ ≤ 1) {w : Set H} (b : HilbertBasis w ℂ H) :
    (∑' i : w, ‖⟪W (b i), A (b i)⟫_ℂ‖) ≤ traceNorm A hA := by
  obtain ⟨hUS, hS, hfactor⟩ := isHilbertSchmidt_polarFactor_mul_sqrt_abs_and_sqrt_abs hA
  set R : H →L[ℂ] H := Polar.polarFactor A * CFC.sqrt (CFC.abs A) with hRdef
  set S : H →L[ℂ] H := CFC.sqrt (CFC.abs A) with hSdef
  have hRstar : IsHilbertSchmidt (ContinuousLinearMap.adjoint R) := by
    rcases hUS with ⟨w₀, b₀, hb₀⟩
    exact ⟨w₀, b₀, summable_norm_sq_adjoint_of_summable_norm_sq b₀ hb₀⟩
  have hRWb : Summable (fun i : w => ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b
      (isHilbertSchmidt_mul_right_of_opNorm_le_one hW hRstar)
  have hSb : Summable (fun i : w => ‖S (b i)‖ ^ 2) := summable_norm_sq_apply_of_hilbertBasis w b hS
  have hUSb : Summable (fun i : w => ‖R (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hUS
  have hpoint : ∀ i : w, ⟪W (b i), A (b i)⟫_ℂ =
      ⟪(ContinuousLinearMap.adjoint R * W) (b i), S (b i)⟫_ℂ := by
    intro i
    rw [show A = R * S from hfactor.symm, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_left R (S (b i)) (W (b i))]
  have hprod : Summable (fun i : w =>
      ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ * ‖S (b i)‖) :=
    summable_norm_mul_of_square_sums _ _ hRWb hSb (fun i => norm_nonneg _) (fun i => norm_nonneg _)
  have hLHSsummable : Summable (fun i : w => ‖⟪W (b i), A (b i)⟫_ℂ‖) := by
    apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) hprod
    rw [hpoint i]; exact norm_inner_le_norm _ _
  have hle1 : (∑' i : w, ‖⟪W (b i), A (b i)⟫_ℂ‖) ≤
      ∑' i : w, ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ * ‖S (b i)‖ :=
    hLHSsummable.tsum_le_tsum (fun i => by rw [hpoint i]; exact norm_inner_le_norm _ _) hprod
  have hle2 : (∑' i : w, ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ * ‖S (b i)‖) ≤
      Real.sqrt (∑' i : w, ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ ^ 2) *
        Real.sqrt (∑' i : w, ‖S (b i)‖ ^ 2) :=
    tsum_mul_le_sqrt_mul_sqrt hRWb hSb (fun i => norm_nonneg _) (fun i => norm_nonneg _)
  have hRWSq : (∑' i : w, ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ ^ 2) ≤
      ∑' i : w, ‖R (b i)‖ ^ 2 := by
    have hstep := tsum_norm_sq_mul_right_le_of_opNorm_le_one (X := ContinuousLinearMap.adjoint R)
      hW hRstar b
    have hadjR : (∑' i : w, ‖(ContinuousLinearMap.adjoint R) (b i)‖ ^ 2) =
        ∑' i : w, ‖R (b i)‖ ^ 2 := (hasSum_norm_sq_apply_eq_adjoint b b hUSb).tsum_eq
    rwa [hadjR] at hstep
  have hRSq : (∑' i : w, ‖R (b i)‖ ^ 2) ≤ ∑' i : w, ‖S (b i)‖ ^ 2 := by
    have hpt : ∀ i : w, ‖R (b i)‖ ^ 2 ≤ ‖S (b i)‖ ^ 2 := by
      intro i
      have hle : ‖R (b i)‖ ≤ ‖S (b i)‖ := by
        rw [hRdef, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
        calc ‖Polar.polarFactor A (S (b i))‖ ≤ ‖Polar.polarFactor A‖ * ‖S (b i)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖S (b i)‖ :=
              mul_le_mul_of_nonneg_right (Polar.polarFactor_opNorm_le A) (norm_nonneg _)
          _ = ‖S (b i)‖ := one_mul _
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hle
    exact hUSb.tsum_le_tsum hpt hSb
  have hle3 : Real.sqrt (∑' i : w, ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ ^ 2) ≤
      Real.sqrt (∑' i : w, ‖S (b i)‖ ^ 2) := Real.sqrt_le_sqrt (hRWSq.trans hRSq)
  have hnonneg : (0:ℝ) ≤ Real.sqrt (∑' i : w, ‖S (b i)‖ ^ 2) := Real.sqrt_nonneg _
  calc
    (∑' i : w, ‖⟪W (b i), A (b i)⟫_ℂ‖) ≤ ∑' i : w,
        ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ * ‖S (b i)‖ := hle1
    _ ≤ Real.sqrt (∑' i : w, ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ ^ 2) *
        Real.sqrt (∑' i : w, ‖S (b i)‖ ^ 2) := hle2
    _ ≤ Real.sqrt (∑' i : w, ‖S (b i)‖ ^ 2) * Real.sqrt (∑' i : w, ‖S (b i)‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hle3 hnonneg
    _ = ∑' i : w, ‖S (b i)‖ ^ 2 := Real.mul_self_sqrt (tsum_nonneg (fun i => sq_nonneg _))
    _ = traceNorm A hA := tsum_sqrt_abs_norm_sq_eq_traceNorm hA b

/-- The trace-norm diagonal in the basis `b` equals the norm-diagonal pairing against `T`'s own
polar factor: `⟪eᵢ, |T| eᵢ⟫ = ⟪(polarFactor T) eᵢ, T eᵢ⟫` exactly, and the latter is already a
nonnegative real. -/
private lemma traceNorm_eq_tsum_norm_inner_polarFactor {T : H →L[ℂ] H} (hT : IsTraceClass T)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    traceNorm T hT = ∑' i : w, ‖⟪Polar.polarFactor T (b i), T (b i)⟫_ℂ‖ := by
  rw [traceNorm_eq_of_hilbertBasis hT b]
  refine tsum_congr (fun i => ?_)
  have hval : ⟪b i, CFC.abs T (b i)⟫_ℂ = ⟪Polar.polarFactor T (b i), T (b i)⟫_ℂ := by
    have habs : CFC.abs T = star (Polar.polarFactor T) * T := (Polar.star_polarFactor_mul_self
        T).symm
    rw [habs, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right (Polar.polarFactor T) (b i) (T (b i))]
  have hnonnegre : ‖⟪b i, CFC.abs T (b i)⟫_ℂ‖ = (⟪b i, CFC.abs T (b i)⟫_ℂ).re := by
    have hpos : (CFC.abs T).IsPositive := (CFC.abs T).nonneg_iff_isPositive.mp (CFC.abs_nonneg T)
    have hx := (ContinuousLinearMap.isPositive_iff_complex (CFC.abs T)).mp hpos (b i)
    have h1 : ⟪CFC.abs T (b i), b i⟫_ℂ = ((⟪CFC.abs T (b i), b i⟫_ℂ).re : ℂ) := hx.1.symm
    have hre : (⟪CFC.abs T (b i), b i⟫_ℂ).re = (⟪b i, CFC.abs T (b i)⟫_ℂ).re := by
      rw [← inner_conj_symm (CFC.abs T (b i)) (b i)]; exact Complex.conj_re _
    have heq : ⟪b i, CFC.abs T (b i)⟫_ℂ = ((⟪b i, CFC.abs T (b i)⟫_ℂ).re : ℂ) := by
      calc
        ⟪b i, CFC.abs T (b i)⟫_ℂ = (starRingEnd ℂ) ⟪CFC.abs T (b i), b i⟫_ℂ :=
          (inner_conj_symm (b i) (CFC.abs T (b i))).symm
        _ = (starRingEnd ℂ) ((⟪CFC.abs T (b i), b i⟫_ℂ).re : ℂ) := congrArg (starRingEnd ℂ) h1
        _ = ((⟪CFC.abs T (b i), b i⟫_ℂ).re : ℂ) := by simp
        _ = ((⟪b i, CFC.abs T (b i)⟫_ℂ).re : ℂ) := by rw [hre]
    have hnonneg : 0 ≤ (⟪b i, CFC.abs T (b i)⟫_ℂ).re := by rw [← hre]; exact hx.2
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    simp only [Complex.ofReal_re]
  rw [← hnonnegre, hval]

/-- **Subadditivity of the trace norm.** Closes `Banach.lean`'s `traceNorm_add_le` gap. Conjugating
`T + T'` by its own polar factor `W` splits additively, and each summand is controlled by the
duality bound applied to `T` and `T'` separately. -/
theorem traceNorm_add_le {T T' : H →L[ℂ] H} (hT : IsTraceClass T) (hT' : IsTraceClass T')
    (hTT' : IsTraceClass (T + T')) :
    traceNorm (T + T') hTT' ≤ traceNorm T hT + traceNorm T' hT' := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  set W : H →L[ℂ] H := Polar.polarFactor (T + T') with hWdef
  have hWnorm : ‖W‖ ≤ 1 := Polar.polarFactor_opNorm_le (T + T')
  have heq := traceNorm_eq_tsum_norm_inner_polarFactor hTT' b
  have hpt : ∀ i : w, ‖⟪W (b i), (T + T') (b i)⟫_ℂ‖ ≤
      ‖⟪W (b i), T (b i)⟫_ℂ‖ + ‖⟪W (b i), T' (b i)⟫_ℂ‖ := by
    intro i
    rw [add_apply, inner_add_right]
    exact norm_add_le _ _
  have hT1 : Summable (fun i : w => ‖⟪W (b i), T (b i)⟫_ℂ‖) :=
    summable_norm_inner_contraction_of_isTraceClass hT hWnorm b
  have hT2 : Summable (fun i : w => ‖⟪W (b i), T' (b i)⟫_ℂ‖) :=
    summable_norm_inner_contraction_of_isTraceClass hT' hWnorm b
  have hsum : Summable (fun i : w =>
      ‖⟪W (b i), T (b i)⟫_ℂ‖ + ‖⟪W (b i), T' (b i)⟫_ℂ‖) := hT1.add hT2
  have hTT'sum : Summable (fun i : w => ‖⟪W (b i), (T + T') (b i)⟫_ℂ‖) :=
    summable_norm_inner_contraction_of_isTraceClass hTT' hWnorm b
  calc
    traceNorm (T + T') hTT' = ∑' i : w, ‖⟪W (b i), (T + T') (b i)⟫_ℂ‖ := heq
    _ ≤ ∑' i : w, (‖⟪W (b i), T (b i)⟫_ℂ‖ + ‖⟪W (b i), T' (b i)⟫_ℂ‖) :=
      hTT'sum.tsum_le_tsum hpt hsum
    _ = (∑' i : w, ‖⟪W (b i), T (b i)⟫_ℂ‖) + ∑' i : w, ‖⟪W (b i), T' (b i)⟫_ℂ‖ :=
      hT1.tsum_add hT2
    _ ≤ traceNorm T hT + traceNorm T' hT' :=
      add_le_add (tsum_norm_inner_contraction_le_traceNorm hT hWnorm b)
        (tsum_norm_inner_contraction_le_traceNorm hT' hWnorm b)

/-- **Quantitative master lemma**: the trace norm of a product of two Hilbert–Schmidt operators is
bounded by the product of their Hilbert–Schmidt square-root sums, in any common basis. -/
theorem traceNorm_mul_le_of_isHilbertSchmidt {R S : H →L[ℂ] H} (hR : IsHilbertSchmidt R)
    (hS : IsHilbertSchmidt S) (hRS : IsTraceClass (R * S)) {w : Set H} (b : HilbertBasis w ℂ H) :
    traceNorm (R * S) hRS ≤
      Real.sqrt (∑' i : w, ‖R (b i)‖ ^ 2) * Real.sqrt (∑' i : w, ‖S (b i)‖ ^ 2) := by
  set W : H →L[ℂ] H := Polar.polarFactor (R * S) with hWdef
  have hWnorm : ‖W‖ ≤ 1 := Polar.polarFactor_opNorm_le (R * S)
  have hRstar : IsHilbertSchmidt (ContinuousLinearMap.adjoint R) := by
    rcases hR with ⟨w₀, b₀, hb₀⟩
    exact ⟨w₀, b₀, summable_norm_sq_adjoint_of_summable_norm_sq b₀ hb₀⟩
  have hRWb : Summable (fun i : w => ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b
      (isHilbertSchmidt_mul_right_of_opNorm_le_one hWnorm hRstar)
  have hSb : Summable (fun i : w => ‖S (b i)‖ ^ 2) := summable_norm_sq_apply_of_hilbertBasis w b hS
  have hRb : Summable (fun i : w => ‖R (b i)‖ ^ 2) := summable_norm_sq_apply_of_hilbertBasis w b hR
  have heq := traceNorm_eq_tsum_norm_inner_polarFactor hRS b
  have hpoint : ∀ i : w, ⟪W (b i), (R * S) (b i)⟫_ℂ =
      ⟪(ContinuousLinearMap.adjoint R * W) (b i), S (b i)⟫_ℂ := by
    intro i
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.adjoint_inner_left R (S (b i)) (W (b i))]
  have hprod : Summable (fun i : w =>
      ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ * ‖S (b i)‖) :=
    summable_norm_mul_of_square_sums _ _ hRWb hSb (fun i => norm_nonneg _) (fun i => norm_nonneg _)
  have hle1 : (∑' i : w, ‖⟪W (b i), (R * S) (b i)⟫_ℂ‖) ≤
      ∑' i : w, ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ * ‖S (b i)‖ := by
    apply Summable.tsum_le_tsum _ _ hprod
    · intro i; rw [hpoint i]; exact norm_inner_le_norm _ _
    · apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) hprod
      rw [hpoint i]; exact norm_inner_le_norm _ _
  have hle2 : (∑' i : w, ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ * ‖S (b i)‖) ≤
      Real.sqrt (∑' i : w, ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ ^ 2) *
        Real.sqrt (∑' i : w, ‖S (b i)‖ ^ 2) :=
    tsum_mul_le_sqrt_mul_sqrt hRWb hSb (fun i => norm_nonneg _) (fun i => norm_nonneg _)
  have hRWSq : (∑' i : w, ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ ^ 2) ≤
      ∑' i : w, ‖R (b i)‖ ^ 2 := by
    have hstep := tsum_norm_sq_mul_right_le_of_opNorm_le_one (X := ContinuousLinearMap.adjoint R)
      hWnorm hRstar b
    have hadjR : (∑' i : w, ‖(ContinuousLinearMap.adjoint R) (b i)‖ ^ 2) =
        ∑' i : w, ‖R (b i)‖ ^ 2 := (hasSum_norm_sq_apply_eq_adjoint b b hRb).tsum_eq
    rwa [hadjR] at hstep
  have hle3 : Real.sqrt (∑' i : w, ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ ^ 2) ≤
      Real.sqrt (∑' i : w, ‖R (b i)‖ ^ 2) := Real.sqrt_le_sqrt hRWSq
  calc
    traceNorm (R * S) hRS = ∑' i : w, ‖⟪W (b i), (R * S) (b i)⟫_ℂ‖ := heq
    _ ≤ ∑' i : w, ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ * ‖S (b i)‖ := hle1
    _ ≤ Real.sqrt (∑' i : w, ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ ^ 2) *
        Real.sqrt (∑' i : w, ‖S (b i)‖ ^ 2) := hle2
    _ ≤ Real.sqrt (∑' i : w, ‖R (b i)‖ ^ 2) * Real.sqrt (∑' i : w, ‖S (b i)‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hle3 (Real.sqrt_nonneg _)

/-- **The general two-sided trace-ideal norm estimate.** Closes `HilbertSpaceInstance.lean`'s
`traceNorm_mul_mul_le` gap. Sandwiching a trace-class `T` between bounded `A` and `B` scales the
trace norm by at most `‖A‖ * ‖B‖`. The proof factors `T = R * S` through its own Hilbert–Schmidt
factorization, absorbs `A`, `B` into `R`, `S` respectively, and applies the quantitative master
lemma. -/
theorem traceNorm_mul_mul_le {A B T : H →L[ℂ] H} (hT : IsTraceClass T)
    (hABT : IsTraceClass (A * T * B)) :
    traceNorm (A * T * B) hABT ≤ ‖A‖ * traceNorm T hT * ‖B‖ := by
  obtain ⟨_, hS, hfactor⟩ := isHilbertSchmidt_polarFactor_mul_sqrt_abs_and_sqrt_abs hT
  set R₀ : H →L[ℂ] H := Polar.polarFactor T * CFC.sqrt (CFC.abs T) with hR₀def
  set S₀ : H →L[ℂ] H := CFC.sqrt (CFC.abs T) with hS₀def
  have hUS : IsHilbertSchmidt R₀ :=
    isHilbertSchmidt_mul_left_of_opNorm_le_one (Polar.polarFactor_opNorm_le T) hS
  have hAR : IsHilbertSchmidt (A * R₀) := isHilbertSchmidt_mul_left hUS
  have hSB : IsHilbertSchmidt (S₀ * B) := isHilbertSchmidt_mul_right hS
  have heq : A * T * B = (A * R₀) * (S₀ * B) := by
    rw [show T = R₀ * S₀ from hfactor.symm]; simp only [mul_assoc]
  have hABT' : IsTraceClass ((A * R₀) * (S₀ * B)) := heq ▸ hABT
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hbound := traceNorm_mul_le_of_isHilbertSchmidt hAR hSB hABT' b
  have hARsq : (∑' i : w, ‖(A * R₀) (b i)‖ ^ 2) ≤ ‖A‖ ^ 2 * ∑' i : w, ‖R₀ (b i)‖ ^ 2 := by
    have hR₀b : Summable (fun i : w => ‖R₀ (b i)‖ ^ 2) :=
      summable_norm_sq_apply_of_hilbertBasis w b hUS
    have hpt : ∀ i : w, ‖(A * R₀) (b i)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖R₀ (b i)‖ ^ 2 := by
      intro i
      have hle : ‖(A * R₀) (b i)‖ ≤ ‖A‖ * ‖R₀ (b i)‖ := by
        rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
        exact ContinuousLinearMap.le_opNorm _ _
      calc ‖(A * R₀) (b i)‖ ^ 2 ≤ (‖A‖ * ‖R₀ (b i)‖) ^ 2 :=
            (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hle
        _ = ‖A‖ ^ 2 * ‖R₀ (b i)‖ ^ 2 := by ring
    calc (∑' i : w, ‖(A * R₀) (b i)‖ ^ 2) ≤ ∑' i : w, ‖A‖ ^ 2 * ‖R₀ (b i)‖ ^ 2 :=
          (summable_norm_sq_apply_of_hilbertBasis w b hAR).tsum_le_tsum hpt (hR₀b.mul_left _)
      _ = ‖A‖ ^ 2 * ∑' i : w, ‖R₀ (b i)‖ ^ 2 := tsum_mul_left
  have hSBsq : (∑' i : w, ‖(S₀ * B) (b i)‖ ^ 2) ≤ ‖B‖ ^ 2 * ∑' i : w, ‖S₀ (b i)‖ ^ 2 := by
    have hS₀b : Summable (fun i : w => ‖S₀ (b i)‖ ^ 2) :=
      summable_norm_sq_apply_of_hilbertBasis w b hS
    by_cases hB0 : ‖B‖ = 0
    · have hBzero : B = 0 := norm_eq_zero.mp hB0
      simp [hBzero]
    · have hBcontr : ‖(‖B‖⁻¹ : ℂ) • B‖ ≤ 1 := by
        rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg B),
          inv_mul_cancel₀ hB0]
      have hstep := tsum_norm_sq_mul_right_le_of_opNorm_le_one
        (X := S₀) (W := (‖B‖⁻¹ : ℂ) • B) hBcontr hS b
      have heqB : (fun i : w => ‖(S₀ * ((‖B‖⁻¹ : ℂ) • B)) (b i)‖ ^ 2) =
          fun i : w => ‖B‖⁻¹ ^ 2 * ‖(S₀ * B) (b i)‖ ^ 2 := by
        funext i
        have h1 : (S₀ * ((‖B‖⁻¹ : ℂ) • B)) (b i) = (‖B‖⁻¹ : ℂ) • (S₀ * B) (b i) := by
          rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
            smul_apply, map_smul, ContinuousLinearMap.mul_def,
            ContinuousLinearMap.comp_apply]
        rw [h1, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg B), mul_pow]
      rw [heqB] at hstep
      have htsum_smul : (∑' i : w, ‖B‖⁻¹ ^ 2 * ‖(S₀ * B) (b i)‖ ^ 2) =
          ‖B‖⁻¹ ^ 2 * ∑' i : w, ‖(S₀ * B) (b i)‖ ^ 2 := tsum_mul_left
      rw [htsum_smul] at hstep
      have hfinal : ‖B‖⁻¹ ^ 2 * (∑' i : w, ‖(S₀ * B) (b i)‖ ^ 2) ≤ ∑' i : w, ‖S₀ (b i)‖ ^ 2 := hstep
      calc (∑' i : w, ‖(S₀ * B) (b i)‖ ^ 2)
          = ‖B‖ ^ 2 * (‖B‖⁻¹ ^ 2 * ∑' i : w, ‖(S₀ * B) (b i)‖ ^ 2) := by field_simp
        _ ≤ ‖B‖ ^ 2 * ∑' i : w, ‖S₀ (b i)‖ ^ 2 := mul_le_mul_of_nonneg_left hfinal (sq_nonneg _)
  have hS₀Sq : (∑' i : w, ‖S₀ (b i)‖ ^ 2) = traceNorm T hT :=
    tsum_sqrt_abs_norm_sq_eq_traceNorm hT b
  calc
    traceNorm (A * T * B) hABT = traceNorm ((A * R₀) * (S₀ * B)) hABT' :=
      (traceNorm_transport heq hABT).trans traceNorm_congr
    _ ≤ Real.sqrt (∑' i : w, ‖(A * R₀) (b i)‖ ^ 2) * Real.sqrt (∑' i : w, ‖(S₀ * B) (b i)‖ ^ 2) :=
        hbound
    _ ≤ Real.sqrt (‖A‖ ^ 2 * ∑' i : w, ‖R₀ (b i)‖ ^ 2) *
        Real.sqrt (‖B‖ ^ 2 * ∑' i : w, ‖S₀ (b i)‖ ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt hARsq) (Real.sqrt_le_sqrt hSBsq) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = ‖A‖ * Real.sqrt (∑' i : w, ‖R₀ (b i)‖ ^ 2) *
        (‖B‖ * Real.sqrt (∑' i : w, ‖S₀ (b i)‖ ^ 2)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg A),
          Real.sqrt_sq (norm_nonneg B)]
    _ ≤ ‖A‖ * Real.sqrt (traceNorm T hT) * (‖B‖ * Real.sqrt (∑' i : w, ‖S₀ (b i)‖ ^ 2)) := by
        gcongr
        · calc (∑' i : w, ‖R₀ (b i)‖ ^ 2) ≤ ∑' i : w, ‖S₀ (b i)‖ ^ 2 := by
                have hS₀b : Summable (fun i : w => ‖S₀ (b i)‖ ^ 2) :=
                  summable_norm_sq_apply_of_hilbertBasis w b hS
                have hpt : ∀ i : w, ‖R₀ (b i)‖ ^ 2 ≤ ‖S₀ (b i)‖ ^ 2 := by
                  intro i
                  have hle : ‖R₀ (b i)‖ ≤ ‖S₀ (b i)‖ := by
                    rw [hR₀def, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
                    calc ‖Polar.polarFactor T (S₀ (b i))‖ ≤ ‖Polar.polarFactor T‖ * ‖S₀ (b i)‖ :=
                          ContinuousLinearMap.le_opNorm _ _
                      _ ≤ 1 * ‖S₀ (b i)‖ :=
                          mul_le_mul_of_nonneg_right (Polar.polarFactor_opNorm_le T)
                            (norm_nonneg _)
                      _ = ‖S₀ (b i)‖ := one_mul _
                  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hle
                exact (summable_norm_sq_apply_of_hilbertBasis w b hUS).tsum_le_tsum hpt hS₀b
            _ = traceNorm T hT := hS₀Sq
    _ = ‖A‖ * Real.sqrt (traceNorm T hT) * (‖B‖ * Real.sqrt (traceNorm T hT)) := by rw [hS₀Sq]
    _ = ‖A‖ * traceNorm T hT * ‖B‖ := by
        rw [show ‖A‖ * Real.sqrt (traceNorm T hT) * (‖B‖ * Real.sqrt (traceNorm T hT)) =
            ‖A‖ * ‖B‖ * (Real.sqrt (traceNorm T hT) * Real.sqrt (traceNorm T hT)) by ring,
          Real.mul_self_sqrt (traceNorm_nonneg T hT)]
        ring

end
