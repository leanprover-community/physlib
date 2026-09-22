/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.TraceClass.GeneralIdeal

/-!
# The product of two Hilbert–Schmidt operators is trace class

Ported from `unbounded-alpha-public`'s `TraceClass/GeneralProduct.lean`. This is the master lemma
that finally crosses the non-self-adjoint boundary honestly: given the general partial-isometry
identity `Polar.star_polarFactor_mul_self` (`star (polarFactor T) * T = |T|`, for *every* bounded
`T`), the diagonal of `|R * S|` for Hilbert–Schmidt `R`, `S` is exactly
`i ↦ ⟪(adjoint R * polarFactor (R*S)) eᵢ, S eᵢ⟫`, absolutely summable by the same Hilbert–Schmidt
Cauchy–Schwarz estimate used for the diagonal of a Hilbert–Schmidt product.

From this single theorem, the general (not necessarily positive or self-adjoint) trace-class ideal
structure follows: every trace-class operator is already `(polarFactor T * √|T|) * √|T|` (both
Hilbert–Schmidt factors), so this master lemma gives the two-sided ideal estimate and additive
closure of `IsTraceClass` for arbitrary operators, closing `Banach.lean`'s `isTraceClass_add` gap
and `HilbertSpaceInstance.lean`'s `isTraceClass_mul_coe` gap.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The diagonal of `star W * (R * S)` (for any contraction `W`) unwinds to a Hilbert–Schmidt
Cauchy–Schwarz pairing. This is the pointwise identity feeding both the master product theorem and
the general additive/ideal closure results below. -/
theorem diagonal_star_mul_eq_inner {R S W : H →L[ℂ] H} {w : Set H} (b : HilbertBasis w ℂ H)
    (i : w) :
    ⟪b i, (star W * (R * S)) (b i)⟫_ℂ = ⟪(ContinuousLinearMap.adjoint R * W) (b i), S (b i)⟫_ℂ := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right W (b i) (R (S (b i))),
    ← ContinuousLinearMap.adjoint_inner_left R (S (b i)) (W (b i)),
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]

/-- **Master lemma**: the product of two Hilbert–Schmidt operators is trace class. The proof
factors `|RS| = star (polarFactor (RS)) * (RS)` (the general partial-isometry identity, valid for
every bounded operator, not just this product) and bounds its diagonal by the Hilbert–Schmidt
Cauchy–Schwarz estimate `HilbertSchmidt.summable_norm_mul_of_square_sums`. -/
theorem isTraceClass_mul_of_isHilbertSchmidt {R S : H →L[ℂ] H}
    (hR : IsHilbertSchmidt R) (hS : IsHilbertSchmidt S) : IsTraceClass (R * S) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  refine ⟨w, b, ?_⟩
  set W : H →L[ℂ] H := Polar.polarFactor (R * S) with hWdef
  have hWnorm : ‖W‖ ≤ 1 := Polar.polarFactor_opNorm_le (R * S)
  have hRstar : IsHilbertSchmidt (ContinuousLinearMap.adjoint R) := by
    rcases hR with ⟨w₀, b₀, hb₀⟩
    exact ⟨w₀, b₀, summable_norm_sq_adjoint_of_summable_norm_sq b₀ hb₀⟩
  have hRW : IsHilbertSchmidt (ContinuousLinearMap.adjoint R * W) :=
    isHilbertSchmidt_mul_right_of_opNorm_le_one hWnorm hRstar
  have hRWb : Summable (fun i : w => ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hRW
  have hSb : Summable (fun i : w => ‖S (b i)‖ ^ 2) := summable_norm_sq_apply_of_hilbertBasis w b hS
  have hprod : Summable (fun i : w =>
      ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ * ‖S (b i)‖) :=
    summable_norm_mul_of_square_sums _ _ hRWb hSb (fun i => norm_nonneg _) (fun i => norm_nonneg _)
  have habs : Polar.absOperator (R * S) = star W * (R * S) := (Polar.star_polarFactor_mul_self
      (R * S)).symm
  have hpoint : ∀ i : w,
      ⟪b i, CFC.abs (R * S) (b i)⟫_ℂ = ⟪(ContinuousLinearMap.adjoint R * W) (b i), S (b i)⟫_ℂ := by
    intro i
    show ⟪b i, Polar.absOperator (R * S) (b i)⟫_ℂ = _
    rw [habs]
    exact diagonal_star_mul_eq_inner b i
  apply Summable.of_norm_bounded hprod
  intro i
  calc
    ‖(⟪b i, CFC.abs (R * S) (b i)⟫_ℂ).re‖ ≤ ‖⟪b i, CFC.abs (R * S) (b i)⟫_ℂ‖ :=
      Complex.abs_re_le_norm _
    _ = ‖⟪(ContinuousLinearMap.adjoint R * W) (b i), S (b i)⟫_ℂ‖ := by rw [hpoint i]
    _ ≤ ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ * ‖S (b i)‖ := norm_inner_le_norm _ _

/-- Every trace-class operator factors as a product of two Hilbert–Schmidt operators: the polar
factor composed with the Hilbert–Schmidt square root of `|T|`, and that same square root again. -/
theorem isHilbertSchmidt_polarFactor_mul_sqrt_abs_and_sqrt_abs {T : H →L[ℂ] H}
    (hT : IsTraceClass T) :
    IsHilbertSchmidt (Polar.polarFactor T * CFC.sqrt (CFC.abs T)) ∧
      IsHilbertSchmidt (CFC.sqrt (CFC.abs T)) ∧
      Polar.polarFactor T * CFC.sqrt (CFC.abs T) * CFC.sqrt (CFC.abs T) = T := by
  have hS : IsHilbertSchmidt (CFC.sqrt (CFC.abs T)) := isHilbertSchmidt_sqrt_abs_of_isTraceClass hT
  have hUS : IsHilbertSchmidt (Polar.polarFactor T * CFC.sqrt (CFC.abs T)) :=
    isHilbertSchmidt_mul_left_of_opNorm_le_one (Polar.polarFactor_opNorm_le T) hS
  refine ⟨hUS, hS, ?_⟩
  rw [mul_assoc, CFC.sqrt_mul_sqrt_self (CFC.abs T) (CFC.abs_nonneg T)]
  exact Polar.polarFactor_mul_absOperator T

/-- **General additive closure of `IsTraceClass`**, for arbitrary (not necessarily positive or
self-adjoint) trace-class operators. Closes `Banach.lean`'s `isTraceClass_add` gap. The proof
conjugates the sum by the *sum's own* polar factor `W`: `star W * (T + T') = star W * T + star W *
T'` splits additively, and each summand's diagonal is absolutely summable by the same
Hilbert–Schmidt Cauchy–Schwarz estimate used in the master lemma, applied to `T`'s and `T'`'s own
Hilbert–Schmidt factorizations. -/
theorem isTraceClass_add {T T' : H →L[ℂ] H} (hT : IsTraceClass T) (hT' : IsTraceClass T') :
    IsTraceClass (T + T') := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  refine ⟨w, b, ?_⟩
  set W : H →L[ℂ] H := Polar.polarFactor (T + T') with hWdef
  have hWnorm : ‖W‖ ≤ 1 := Polar.polarFactor_opNorm_le (T + T')
  have hsummable_conj : ∀ {X : H →L[ℂ] H}, IsTraceClass X →
      Summable (fun i : w => ⟪(b i : H), (star W * X) (b i)⟫_ℂ) := by
    intro X hX
    obtain ⟨hUS, hS, hfactor⟩ := isHilbertSchmidt_polarFactor_mul_sqrt_abs_and_sqrt_abs hX
    set R : H →L[ℂ] H := Polar.polarFactor X * CFC.sqrt (CFC.abs X) with hRdef
    set S : H →L[ℂ] H := CFC.sqrt (CFC.abs X) with hSdef
    have hRstar : IsHilbertSchmidt (ContinuousLinearMap.adjoint R) := by
      rcases hUS with ⟨w₀, b₀, hb₀⟩
      exact ⟨w₀, b₀, summable_norm_sq_adjoint_of_summable_norm_sq b₀ hb₀⟩
    have hRW : IsHilbertSchmidt (ContinuousLinearMap.adjoint R * W) :=
      isHilbertSchmidt_mul_right_of_opNorm_le_one hWnorm hRstar
    have hRWb : Summable (fun i : w => ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ ^ 2) :=
      summable_norm_sq_apply_of_hilbertBasis w b hRW
    have hSb : Summable (fun i : w => ‖S (b i)‖ ^ 2) :=
      summable_norm_sq_apply_of_hilbertBasis w b hS
    have hprod : Summable (fun i : w =>
        ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ * ‖S (b i)‖) :=
      summable_norm_mul_of_square_sums _ _ hRWb hSb
        (fun i => norm_nonneg _) (fun i => norm_nonneg _)
    have hpoint : ∀ i : w, ⟪b i, (star W * X) (b i)⟫_ℂ =
        ⟪(ContinuousLinearMap.adjoint R * W) (b i), S (b i)⟫_ℂ := by
      intro i
      rw [show X = R * S from hfactor.symm]
      exact diagonal_star_mul_eq_inner b i
    apply Summable.of_norm_bounded hprod
    intro i
    rw [hpoint i]
    exact norm_inner_le_norm _ _
  have hTsum := hsummable_conj hT
  have hT'sum := hsummable_conj hT'
  have habs : CFC.abs (T + T') = star W * (T + T') := (Polar.star_polarFactor_mul_self (T +
      T')).symm
  have hsplit : (fun i : w => ⟪b i, CFC.abs (T + T') (b i)⟫_ℂ) =
      (fun i : w => ⟪b i, (star W * T) (b i)⟫_ℂ + ⟪b i, (star W * T') (b i)⟫_ℂ) := by
    funext i
    rw [habs]
    show ⟪b i, (star W * (T + T')) (b i)⟫_ℂ = _
    have hstep : (star W * (T + T')) (b i) = (star W * T) (b i) + (star W * T') (b i) := by
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
        add_apply, map_add, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply]
    rw [hstep, inner_add_right]
  have hsum : Summable (fun i : w =>
      ⟪b i, (star W * T) (b i)⟫_ℂ + ⟪b i, (star W * T') (b i)⟫_ℂ) := hTsum.add hT'sum
  have hsum' : Summable (fun i : w =>
      (⟪b i, (star W * T) (b i)⟫_ℂ + ⟪b i, (star W * T') (b i)⟫_ℂ).re) := by
    convert (hsum.map Complex.reCLM.toAddMonoidHom Complex.reCLM.continuous) using 1
    ext i; rfl
  have hsplit' := congrArg (fun f : w → ℂ => fun i => (f i).re) hsplit
  rw [hsplit']
  exact hsum'

/-- **The general two-sided trace ideal estimate**: conjugating a trace-class operator by
arbitrary bounded operators on either side stays trace class. Closes `HilbertSpaceInstance.lean`'s
`isTraceClass_mul_coe` gap (specializing `B = 1`). Unlike a positive-only conjugation theorem, this
needs no positivity hypothesis on `T`: the two Hilbert–Schmidt factors of `T` absorb `A` and `B` on
either side, and the master lemma finishes the argument. -/
theorem isTraceClass_mul_mul {A B T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsTraceClass (A * T * B) := by
  obtain ⟨_, hS, hfactor⟩ := isHilbertSchmidt_polarFactor_mul_sqrt_abs_and_sqrt_abs hT
  set R : H →L[ℂ] H := Polar.polarFactor T * CFC.sqrt (CFC.abs T) with hRdef
  set S : H →L[ℂ] H := CFC.sqrt (CFC.abs T) with hSdef
  have hUS : IsHilbertSchmidt R :=
    isHilbertSchmidt_mul_left_of_opNorm_le_one (Polar.polarFactor_opNorm_le T) hS
  have hAR : IsHilbertSchmidt (A * R) := isHilbertSchmidt_mul_left hUS
  have hSB : IsHilbertSchmidt (S * B) := isHilbertSchmidt_mul_right hS
  have heq : A * T * B = (A * R) * (S * B) := by
    rw [show T = R * S from hfactor.symm]; simp only [mul_assoc]
  rw [heq]
  exact isTraceClass_mul_of_isHilbertSchmidt hAR hSB

/-- Taking the adjoint preserves trace class. -/
theorem isTraceClass_star {T : H →L[ℂ] H} (hT : IsTraceClass T) : IsTraceClass (star T) := by
  obtain ⟨hR, hS, hfactor⟩ := isHilbertSchmidt_polarFactor_mul_sqrt_abs_and_sqrt_abs hT
  have hstar : IsTraceClass (star (CFC.sqrt (CFC.abs T)) *
      star (Polar.polarFactor T * CFC.sqrt (CFC.abs T))) :=
    isTraceClass_mul_of_isHilbertSchmidt (isHilbertSchmidt_star hS) (isHilbertSchmidt_star hR)
  rw [← hfactor]
  simpa only [star_mul] using hstar

end
