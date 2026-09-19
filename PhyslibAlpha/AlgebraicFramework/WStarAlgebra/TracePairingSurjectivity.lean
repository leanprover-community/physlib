/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.WStarAlgebra.TracePairingNorm
public import PhyslibAlpha.AlgebraicFramework.WStarAlgebra.BoundedSesquilinearForm

/-!
# The Riesz half of trace-pairing surjectivity

Ported from `unbounded-alpha-public`'s `WStarAlgebra/TracePairingSurj.lean`. This module contains
the functional-analytic core of the converse trace-pairing theorem. A continuous functional on the
trace class is converted into a bounded sesquilinear form by testing it on rank-one operators, and
the Riesz theorem (`BoundedSesquilinearForm.lean`) turns that form into a bounded operator.

The density of the linear span of rank-one trace-class operators in the trace class is proved
directly below (`rankOneSpan_dense`) via a Hilbert–Schmidt truncation argument, rather than kept
as an external hypothesis: this repo's `TraceClass` files already supply every ingredient the
argument needs (`isHilbertSchmidt_polarFactor_mul_sqrt_abs_and_sqrt_abs`,
`traceNorm_mul_le_of_isHilbertSchmidt`).
-/

set_option maxHeartbeats 1000000

@[expose] public section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace Topology
open Filter Set Metric

namespace TraceClass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isTraceClass_rankOne (x y : H) :
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

/-- The rank-one operator `|x⟩⟨y|`, packaged as a trace-class operator. -/
def rankOneTraceClass (x y : H) : TraceClass H :=
  ofOperator (InnerProductSpace.rankOne ℂ x y) (isTraceClass_rankOne x y)

private theorem rankOneTraceClass_norm_le (x y : H) :
    ‖rankOneTraceClass x y‖ ≤ ‖x‖ * ‖y‖ := by
  by_cases hy : y = 0
  · subst hy
    have hzero : rankOneTraceClass x 0 = 0 := by
      apply Subtype.ext
      change InnerProductSpace.rankOne ℂ x 0 = 0
      ext v
      simp
    rw [hzero]
    simp
  · let : Nontrivial H := ⟨⟨y, 0, hy⟩⟩
    let P : H →L[ℂ] H := InnerProductSpace.rankOne ℂ y y
    have hP : IsTraceClass P := isTraceClass_rankOne_self y
    have hT : IsTraceClass (InnerProductSpace.rankOne ℂ x y) :=
      isTraceClass_rankOne x y
    have hprod : IsTraceClass
        (InnerProductSpace.rankOne ℂ x y * P * (1 : H →L[ℂ] H)) := by
      simpa [P] using (isTraceClass_mul_mul
        (A := InnerProductSpace.rankOne ℂ x y) (B := (1 : H →L[ℂ] H)) hP)
    have hscalar : (‖y‖ ^ 2 : ℂ) ≠ 0 := by
      exact_mod_cast (pow_ne_zero 2 (norm_ne_zero_iff.mpr hy))
    have heq : InnerProductSpace.rankOne ℂ x y * P * (1 : H →L[ℂ] H) =
        (‖y‖ ^ 2 : ℂ) • InnerProductSpace.rankOne ℂ x y := by
      change (InnerProductSpace.rankOne ℂ x y ∘L P) ∘L (1 : H →L[ℂ] H) = _
      rw [show P = InnerProductSpace.rankOne ℂ y y by rfl,
        InnerProductSpace.rankOne_comp_rankOne]
      rw [inner_self_eq_norm_sq_to_K]
      ext v
      simp
    have hbound := traceNorm_mul_mul_le
      (A := InnerProductSpace.rankOne ℂ x y) (B := (1 : H →L[ℂ] H)) hP hprod
    have hnormP : traceNorm P hP = ‖y‖ ^ 2 := by
      simpa [P] using traceNorm_rankOne_self y
    let c : ℂ := (‖y‖ ^ 2 : ℂ)
    have hc : c ≠ 0 := by
      dsimp [c]
      exact_mod_cast (pow_ne_zero 2 (norm_ne_zero_iff.mpr hy))
    have hinv : c⁻¹ •
        (InnerProductSpace.rankOne ℂ x y * P * (1 : H →L[ℂ] H)) =
        InnerProductSpace.rankOne ℂ x y := by
      rw [heq, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hInv : IsTraceClass (c⁻¹ •
        (InnerProductSpace.rankOne ℂ x y * P * (1 : H →L[ℂ] H))) :=
      isTraceClass_smul _ hprod
    rw [norm_eq_traceNorm]
    calc
      traceNorm (InnerProductSpace.rankOne ℂ x y) hT =
          traceNorm (c⁻¹ •
            (InnerProductSpace.rankOne ℂ x y * P * (1 : H →L[ℂ] H))) hInv := by
        exact (traceNorm_transport hinv hInv).symm
      _ = ‖c⁻¹‖ * traceNorm
          (InnerProductSpace.rankOne ℂ x y * P * (1 : H →L[ℂ] H)) hprod := by
        rw [traceNorm_smul]
      _ ≤ ‖c⁻¹‖ *
          (‖InnerProductSpace.rankOne ℂ x y‖ * traceNorm P hP *
            ‖(1 : H →L[ℂ] H)‖) := by
        gcongr
      _ = ‖x‖ * ‖y‖ := by
        rw [hnormP]
        dsimp [c]
        simp [norm_inv, norm_pow, Complex.norm_real, InnerProductSpace.norm_rankOne]
        field_simp

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

/-- The trace pairing evaluates a rank-one trace-class operator by the corresponding matrix
coefficient. This is the rank-one test used both for the norm equality and for the concrete normal
representation of `H →L[ℂ] H`. -/
theorem tracePairing_rankOne (A : H →L[ℂ] H) (x y : H) :
    tracePairing A (rankOneTraceClass x y) = ⟪y, A x⟫_ℂ := by
  rw [tracePairing_apply]
  have hcomp : A * InnerProductSpace.rankOne ℂ x y =
      InnerProductSpace.rankOne ℂ (A x) y := by
    rw [show A * InnerProductSpace.rankOne ℂ x y =
        A ∘L InnerProductSpace.rankOne ℂ x y by rfl]
    exact InnerProductSpace.comp_rankOne x y A
  calc
    trace (A * (rankOneTraceClass x y).1)
        (isTraceClass_mul_coe A (rankOneTraceClass x y)) =
        trace (InnerProductSpace.rankOne ℂ (A x) y)
          (hcomp ▸ isTraceClass_mul_coe A (rankOneTraceClass x y)) :=
      trace_transport hcomp _
    _ = trace (InnerProductSpace.rankOne ℂ (A x) y)
        (isTraceClass_rankOne (A x) y) := by congr 1
    _ = ⟪y, A x⟫_ℂ := trace_rankOne (A x) y

/-- The trace-class subspace generated by rank-one operators. -/
def rankOneSpan : Submodule ℂ (TraceClass H) :=
  Submodule.span ℂ {T | ∃ x y : H, T.1 = InnerProductSpace.rankOne ℂ x y}

private def sesquilinearFormOfFunctional
    (φ : TraceClass H →L[ℂ] ℂ) :
    BoundedSesquilinearForm H :=
  { form :=
      { toFun := fun x =>
          { toFun := fun y => starRingEnd ℂ (φ (rankOneTraceClass x y))
            map_add' := by
              intro y z
              have h : rankOneTraceClass x (y + z) =
                  rankOneTraceClass x y + rankOneTraceClass x z := by
                apply Subtype.ext
                change InnerProductSpace.rankOne ℂ x (y + z) =
                  InnerProductSpace.rankOne ℂ x y + InnerProductSpace.rankOne ℂ x z
                ext v
                simp [InnerProductSpace.rankOne_apply]
              rw [h, map_add]
              simp
            map_smul' := by
              intro c y
              have h : rankOneTraceClass x (c • y) =
                  (starRingEnd ℂ c) • rankOneTraceClass x y := by
                apply Subtype.ext
                change InnerProductSpace.rankOne ℂ x (c • y) =
                  (starRingEnd ℂ c) • InnerProductSpace.rankOne ℂ x y
                ext v
                simp [InnerProductSpace.rankOne_apply]
              rw [h, map_smul]
              simp }
        map_add' := by
          intro x z
          apply LinearMap.ext
          intro y
          change starRingEnd ℂ (φ (rankOneTraceClass (x + z) y)) = _
          have h : rankOneTraceClass (x + z) y =
              rankOneTraceClass x y + rankOneTraceClass z y := by
            apply Subtype.ext
            change InnerProductSpace.rankOne ℂ (x + z) y =
              InnerProductSpace.rankOne ℂ x y + InnerProductSpace.rankOne ℂ z y
            ext v
            simp [InnerProductSpace.rankOne_apply]
          rw [h, map_add]
          simp
        map_smul' := by
          intro c x
          apply LinearMap.ext
          intro y
          change starRingEnd ℂ (φ (rankOneTraceClass (c • x) y)) = _
          have h : rankOneTraceClass (c • x) y =
              c • rankOneTraceClass x y := by
            apply Subtype.ext
            change InnerProductSpace.rankOne ℂ (c • x) y =
              c • InnerProductSpace.rankOne ℂ x y
            ext v
            simp
          rw [h, map_smul]
          simp }
    bound := by
      refine ⟨‖φ‖, fun x y => ?_⟩
      change ‖starRingEnd ℂ (φ (rankOneTraceClass x y))‖ ≤
        ‖φ‖ * ‖x‖ * ‖y‖
      rw [← RCLike.star_def]
      rw [norm_star]
      calc
        ‖φ (rankOneTraceClass x y)‖ ≤
            ‖φ‖ * ‖rankOneTraceClass x y‖ := φ.le_opNorm _
        _ ≤ ‖φ‖ * ‖x‖ * ‖y‖ := by
          simpa only [mul_assoc] using
            (mul_le_mul_of_nonneg_left (rankOneTraceClass_norm_le x y)
              (norm_nonneg φ)) }

private theorem sesquilinearFormOfFunctional_apply
    (φ : TraceClass H →L[ℂ] ℂ) (x y : H) :
    (sesquilinearFormOfFunctional φ).form x y =
      starRingEnd ℂ (φ (rankOneTraceClass x y)) := rfl

private theorem pairing_eq_functional_on_rankOne
    (φ : TraceClass H →L[ℂ] ℂ) (x y : H) :
    tracePairing (sesquilinearFormOfFunctional φ).operator
        (rankOneTraceClass x y) = φ (rankOneTraceClass x y) := by
  rw [tracePairing_rankOne]
  rw [(sesquilinearFormOfFunctional φ).operator_inner]
  rw [sesquilinearFormOfFunctional_apply]
  simp

/--
If rank-one trace-class operators are dense, the concrete trace pairing is surjective.

The representing operator is constructed, rather than postulated: the functional is first made
into a bounded sesquilinear form, then `InnerProductSpace.continuousLinearMapOfBilin` supplies the
unique bounded operator represented by that form. Density is used only in the final extension from
rank-one operators to the whole trace class.
-/
theorem tracePairing_surjective_of_rankOneSpan_dense
    (hDense : Dense (rankOneSpan (H := H) : Set (TraceClass H))) :
    Function.Surjective
      (tracePairingLinearIsometry (H := H) :
        (H →L[ℂ] H) → TraceClass H →L[ℂ] ℂ) := by
  intro φ
  refine ⟨(sesquilinearFormOfFunctional φ).operator, ?_⟩
  apply ContinuousLinearMap.ext_on hDense
  rintro T ⟨x, y, hT⟩
  have hT' : T = rankOneTraceClass x y := by
    apply Subtype.ext
    exact hT
  rw [hT']
  change tracePairing
      (sesquilinearFormOfFunctional φ).operator (rankOneTraceClass x y) = _
  exact pairing_eq_functional_on_rankOne φ x y

/-! ## Hilbert–Schmidt finite truncations

The density theorem is obtained by truncating a Hilbert–Schmidt factor in a Hilbert basis. The
following definitions and identities are kept separate from the final topological argument so they
can also be reused for other trace-ideal approximation results.
-/

/-- The Hilbert-Schmidt partial sum `∑_{i ∈ F} |S bᵢ⟩⟨bᵢ|`. -/
def hilbertSchmidtPartial {w : Set H} (S : H →L[ℂ] H) (b : HilbertBasis w ℂ H)
    (F : Finset w) : H →L[ℂ] H :=
  ∑ i ∈ F, InnerProductSpace.rankOne ℂ (S (b i)) (b i)

@[simp, nolint unusedArguments]
theorem hilbertSchmidtPartial_apply {w : Set H} (S : H →L[ℂ] H)
    (b : HilbertBasis w ℂ H) (F : Finset w) (x : H) :
    hilbertSchmidtPartial S b F x =
      ∑ i ∈ F, ⟪b i, x⟫_ℂ • S (b i) := by
  simp [hilbertSchmidtPartial, InnerProductSpace.rankOne_apply]

theorem hilbertSchmidtPartial_apply_basis {w : Set H} (S : H →L[ℂ] H)
    (b : HilbertBasis w ℂ H) [DecidableEq w] (F : Finset w) (j : w) :
    hilbertSchmidtPartial S b F (b j) =
      if j ∈ F then S (b j) else 0 := by
  rw [hilbertSchmidtPartial_apply]
  classical
  by_cases hj : j ∈ F
  · rw [ite_eq_left hj]
    calc
      (∑ i ∈ F, ⟪b i, b j⟫_ℂ • S (b i)) =
          ∑ i ∈ F, (if i = j then 1 else 0) • S (b i) := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hij : i = j
            · subst hij
              simp [b.orthonormal.norm_eq_one]
            · rw [b.orthonormal.2 hij]
              simp [hij]
      _ = S (b j) := by simp [hj]
  · rw [ite_eq_right hj]
    calc
      (∑ i ∈ F, ⟪b i, b j⟫_ℂ • S (b i)) =
          ∑ i ∈ F, (if i = j then 1 else 0) • S (b i) := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hij : i = j
            · subst hij
              simp [b.orthonormal.norm_eq_one]
            · rw [b.orthonormal.2 hij]
              simp [hij]
      _ = 0 := by simp [hj]

theorem hilbertSchmidt_sub_partial_apply_basis {w : Set H} (S : H →L[ℂ] H)
    (b : HilbertBasis w ℂ H) [DecidableEq w] (F : Finset w) (j : w) :
    (S - hilbertSchmidtPartial S b F) (b j) =
      if j ∈ F then 0 else S (b j) := by
  rw [sub_apply, hilbertSchmidtPartial_apply_basis]
  by_cases hj : j ∈ F <;> simp [hj]

theorem hilbertSchmidt_sub_partial_isHilbertSchmidt
    {w : Set H} (S : H →L[ℂ] H) (b : HilbertBasis w ℂ H)
    [DecidableEq w] (F : Finset w) (hS : HilbertSchmidt.IsHilbertSchmidt S) :
    HilbertSchmidt.IsHilbertSchmidt (S - hilbertSchmidtPartial S b F) := by
  refine ⟨w, b, ?_⟩
  have hbase := HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hS
  have htail : Summable
      (({j : w | j ∉ F}).indicator (fun j => ‖S (b j)‖ ^ 2)) :=
    hbase.indicator _
  apply htail.congr
  intro j
  rw [hilbertSchmidt_sub_partial_apply_basis]
  by_cases hj : j ∈ F <;> simp [hj]

theorem hilbertSchmidt_sub_partial_tsum_norm_sq {w : Set H} (S : H →L[ℂ] H)
    (b : HilbertBasis w ℂ H) (F : Finset w)
    (hS : HilbertSchmidt.IsHilbertSchmidt S) :
    ∑' i : w, ‖(S - hilbertSchmidtPartial S b F) (b i)‖ ^ 2 =
      ∑' j : {j : w // j ∉ F}, ‖S (b j)‖ ^ 2 := by
  classical
  have hbase := HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hS
  have htail : Summable
      (({j : w | j ∉ F}).indicator (fun j => ‖S (b j)‖ ^ 2)) :=
    hbase.indicator _
  have hdiff : Summable
      (fun j : w => ‖(S - hilbertSchmidtPartial S b F) (b j)‖ ^ 2) := by
    apply htail.congr
    intro j
    rw [hilbertSchmidt_sub_partial_apply_basis]
    by_cases hj : j ∈ F <;> simp [hj]
  have hfin : ∑ i ∈ F,
      ‖(S - hilbertSchmidtPartial S b F) (b i)‖ ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hilbertSchmidt_sub_partial_apply_basis]
    simp [hi]
  have hdecomp := hdiff.sum_add_tsum_subtype_compl F
  rw [hfin, zero_add] at hdecomp
  calc
    ∑' i : w, ‖(S - hilbertSchmidtPartial S b F) (b i)‖ ^ 2 =
        ∑' j : {j : w // j ∉ F},
          ‖(S - hilbertSchmidtPartial S b F) (b j)‖ ^ 2 := hdecomp.symm
    _ = ∑' j : {j : w // j ∉ F}, ‖S (b j)‖ ^ 2 := by
      apply tsum_congr
      intro j
      rw [hilbertSchmidt_sub_partial_apply_basis]
      simp [j.property]

/-- The trace-class partial sum `∑_{i ∈ F} |R(S bᵢ)⟩⟨bᵢ|`. -/
def traceClassPartial {w : Set H} (R S : H →L[ℂ] H) (b : HilbertBasis w ℂ H)
    (F : Finset w) : TraceClass H :=
  ∑ i ∈ F, ofOperator (InnerProductSpace.rankOne ℂ (R (S (b i))) (b i))
    (isTraceClass_rankOne (R (S (b i))) (b i))

@[nolint unusedArguments]
private theorem mul_rankOne_apply_left {R : H →L[ℂ] H} (x y : H) :
    R * InnerProductSpace.rankOne ℂ x y =
      InnerProductSpace.rankOne ℂ (R x) y := by
  rw [show R * InnerProductSpace.rankOne ℂ x y =
      R ∘L InnerProductSpace.rankOne ℂ x y by rfl]
  exact InnerProductSpace.comp_rankOne x y R

@[simp] theorem traceClassPartial_coe {w : Set H} (R S : H →L[ℂ] H)
    (b : HilbertBasis w ℂ H) (F : Finset w) :
    (traceClassPartial R S b F).1 = R * hilbertSchmidtPartial S b F := by
  let f : w → traceClassSubmodule H := fun i =>
    ⟨InnerProductSpace.rankOne ℂ (R (S (b i))) (b i),
      isTraceClass_rankOne (R (S (b i))) (b i)⟩
  change (↑(∑ i ∈ F, f i) : H →L[ℂ] H) = _
  rw [Submodule.coe_sum (traceClassSubmodule H) f F]
  simp only [hilbertSchmidtPartial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_rankOne_apply_left]

theorem traceClassPartial_mem_rankOneSpan {w : Set H} (R S : H →L[ℂ] H)
    (b : HilbertBasis w ℂ H) (F : Finset w) :
    traceClassPartial R S b F ∈ rankOneSpan (H := H) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact (rankOneSpan (H := H)).zero_mem
  | @insert a F ha ih =>
      rw [show traceClassPartial R S b (insert a F) =
          ofOperator (InnerProductSpace.rankOne ℂ (R (S (b a))) (b a))
            (isTraceClass_rankOne (R (S (b a))) (b a)) +
            traceClassPartial R S b F by
          simp [traceClassPartial, ha]]
      apply (rankOneSpan (H := H)).add_mem
      apply Submodule.subset_span
      exact ⟨R (S (b a)), b a, rfl⟩
      exact ih

theorem norm_sub_traceClassPartial_le {T R S : H →L[ℂ] H} (hT : IsTraceClass T)
    (hfactor : R * S = T) (hR : HilbertSchmidt.IsHilbertSchmidt R)
    (hS : HilbertSchmidt.IsHilbertSchmidt S) {w : Set H}
    (b : HilbertBasis w ℂ H) (F : Finset w) :
    ‖ofOperator T hT - traceClassPartial R S b F‖ ≤
      Real.sqrt (∑' i : w, ‖R (b i)‖ ^ 2) *
        Real.sqrt (∑' i : w, ‖(S - hilbertSchmidtPartial S b F) (b i)‖ ^ 2) := by
  classical
  have hdiff := hilbertSchmidt_sub_partial_isHilbertSchmidt S b F hS
  have hprod : IsTraceClass (R * (S - hilbertSchmidtPartial S b F)) :=
    isTraceClass_mul_of_isHilbertSchmidt hR hdiff
  have heq : T - (traceClassPartial R S b F).1 =
      R * (S - hilbertSchmidtPartial S b F) := by
    rw [traceClassPartial_coe, ← hfactor]
    simp [mul_sub]
  calc
    ‖ofOperator T hT - traceClassPartial R S b F‖ =
        traceNorm (T - (traceClassPartial R S b F).1)
          (isTraceClass_coe (ofOperator T hT - traceClassPartial R S b F)) := rfl
    _ = traceNorm (R * (S - hilbertSchmidtPartial S b F)) hprod := by
      have htr := traceNorm_transport heq
        (isTraceClass_coe (ofOperator T hT - traceClassPartial R S b F))
      calc
        traceNorm (T - (traceClassPartial R S b F).1)
            (isTraceClass_coe (ofOperator T hT - traceClassPartial R S b F)) =
            traceNorm (R * (S - hilbertSchmidtPartial S b F))
              (heq ▸ isTraceClass_coe (ofOperator T hT - traceClassPartial R S b F)) := htr
        _ = traceNorm (R * (S - hilbertSchmidtPartial S b F)) hprod := traceNorm_congr
    _ ≤ Real.sqrt (∑' i : w, ‖R (b i)‖ ^ 2) *
        Real.sqrt (∑' i : w, ‖(S - hilbertSchmidtPartial S b F) (b i)‖ ^ 2) :=
      traceNorm_mul_le_of_isHilbertSchmidt hR hdiff hprod b

theorem rankOneSpan_dense :
    Dense (rankOneSpan (H := H) : Set (TraceClass H)) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro X
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  obtain ⟨hR₀, hS₀, hfactor₀⟩ :=
    isHilbertSchmidt_polarFactor_mul_sqrt_abs_and_sqrt_abs (isTraceClass_coe X)
  let R : H →L[ℂ] H := Polar.polarFactor X.1 * CFC.sqrt (CFC.abs X.1)
  let S : H →L[ℂ] H := CFC.sqrt (CFC.abs X.1)
  have hR : HilbertSchmidt.IsHilbertSchmidt R := by
    simpa [R] using hR₀
  have hS : HilbertSchmidt.IsHilbertSchmidt S := by
    simpa [S] using hS₀
  have hfactor : R * S = X.1 := by
    simpa [R, S, mul_assoc] using hfactor₀
  let f : w → ℝ := fun i => ‖S (b i)‖ ^ 2
  have hf : Summable f :=
    HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hS
  let tail : Finset w → ℝ := fun F =>
    ∑' j : {j : w // j ∉ F}, f j
  have htail : Tendsto tail atTop (𝓝 0) :=
    tendsto_tsum_compl_atTop_zero f
  have hsqrt : Tendsto (fun F : Finset w => Real.sqrt (tail F)) atTop (𝓝 0) := by
    change Tendsto ((fun x : ℝ => Real.sqrt x) ∘ tail) atTop (𝓝 0)
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp htail
  let c : ℝ := Real.sqrt (∑' i : w, ‖R (b i)‖ ^ 2)
  by_cases hc : c = 0
  · refine ⟨traceClassPartial R S b ∅, traceClassPartial_mem_rankOneSpan R S b ∅, ?_⟩
    have herr := norm_sub_traceClassPartial_le (isTraceClass_coe X) hfactor hR hS b ∅
    have hdist : dist X (traceClassPartial R S b ∅) =
        ‖ofOperator X.1 (isTraceClass_coe X) - traceClassPartial R S b ∅‖ := by
      rw [dist_eq_norm]
      rfl
    rw [hdist]
    have hle : ‖ofOperator X.1 (isTraceClass_coe X) - traceClassPartial R S b ∅‖ ≤ 0 := by
      calc
        ‖ofOperator X.1 (isTraceClass_coe X) - traceClassPartial R S b ∅‖ ≤
            c * Real.sqrt (∑' i : w,
              ‖(S - hilbertSchmidtPartial S b ∅) (b i)‖ ^ 2) := herr
        _ = 0 := by simp [hc]
    exact lt_of_le_of_lt hle hε
  · have hcpos : 0 < c := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hc)
    have hratio : 0 < ε / c := div_pos hε hcpos
    have hev : ∀ᶠ F : Finset w in atTop, Real.sqrt (tail F) < ε / c :=
      (tendsto_order.1 hsqrt).2 _ hratio
    obtain ⟨F, hF⟩ := Filter.eventually_atTop.1 hev
    refine ⟨traceClassPartial R S b F, traceClassPartial_mem_rankOneSpan R S b F, ?_⟩
    have herr := norm_sub_traceClassPartial_le (isTraceClass_coe X) hfactor hR hS b F
    have htail_eq := hilbertSchmidt_sub_partial_tsum_norm_sq S b F hS
    have hdist : dist X (traceClassPartial R S b F) =
        ‖ofOperator X.1 (isTraceClass_coe X) - traceClassPartial R S b F‖ := by
      rw [dist_eq_norm]
      rfl
    rw [hdist]
    calc
      ‖ofOperator X.1 (isTraceClass_coe X) - traceClassPartial R S b F‖ ≤
          c * Real.sqrt (∑' i : w,
            ‖(S - hilbertSchmidtPartial S b F) (b i)‖ ^ 2) := herr
      _ = c * Real.sqrt (tail F) := by rw [htail_eq]
      _ < c * (ε / c) := mul_lt_mul_of_pos_left (hF F le_rfl) hcpos
      _ = ε := by field_simp [hc]

/-- The density theorem discharges the only hypothesis in the Riesz/surjectivity argument. -/
theorem tracePairing_surjective_concrete :
    Function.Surjective
      (tracePairingLinearIsometry (H := H) :
        (H →L[ℂ] H) → TraceClass H →L[ℂ] ℂ) :=
  tracePairing_surjective_of_rankOneSpan_dense rankOneSpan_dense

end TraceClass
