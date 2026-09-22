/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.TraceClass.Basic
public import Mathlib.Analysis.MeanInequalities

/-!
# Hilbert–Schmidt operators

Ported from `unbounded-alpha-public`'s `TraceClass/{HilbertSchmidt,HSAlgebra,HSEstimate}.lean` and
the Cauchy–Schwarz estimates of `TraceClass/TraceProduct.lean`, restated against this repo's
`H →L[ℂ] H` (the source's `B(H)`) with no bundled subtype involved — the source's own top-level
`TraceClass.lean` already used the identical predicate-based `IsTraceClass`/`traceNorm`/`trace`
this repo's `Basic.lean` does, so no translation of the underlying convention was needed, only the
notation change and reuse of `Basic.lean`'s own (now-public) `hasSum_norm_sq_inner_basis` in place
of the source's private per-file copy of the same lemma.

A bounded operator `S` is **Hilbert–Schmidt** when `∑ᵢ ‖S eᵢ‖²` converges for some (equivalently,
by the basis-independence theorem below, every) Hilbert basis `{eᵢ}`. This is the reusable analytic
layer between plain boundedness and trace-classness: `S⋆S` is trace class whenever `S` is
Hilbert–Schmidt, a bounded contraction on either side preserves the predicate, and a product of two
Hilbert–Schmidt operators has an absolutely summable diagonal in every basis (the Cauchy–Schwarz
step consumed by the polar-decomposition argument in `GeneralProduct.lean`).
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace HilbertSchmidt

/-- A bounded operator is Hilbert–Schmidt when its squared norm sum is summable in one Hilbert
basis. The basis-independence theorem below shows this existential definition is equivalent to
using any basis. -/
def IsHilbertSchmidt (S : H →L[ℂ] H) : Prop :=
  ∃ (w : Set H) (b : HilbertBasis w ℂ H), Summable (fun i : w => ‖S (b i)‖ ^ 2)

/-- The Hilbert–Schmidt square sum of `S` in one basis equals the square sum of `S⋆` in a second
basis. This is the nonnegative double-sum identity; the usual basis-independence statement follows
by applying it twice. -/
lemma hasSum_norm_sq_apply_eq_adjoint {S : H →L[ℂ] H}
    {w w' : Set H} (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H)
    (hb : Summable (fun i : w => ‖S (b i)‖ ^ 2)) :
    HasSum (fun j : w' => ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2)
      (∑' i : w, ‖S (b i)‖ ^ 2) := by
  classical
  set F : w → w' → ℝ := fun i j => ‖⟪c j, S (b i)⟫_ℂ‖ ^ 2 with hFdef
  have hFnonneg : 0 ≤ Function.uncurry F := fun _ => sq_nonneg _
  have hrow : ∀ i : w, HasSum (F i) (‖S (b i)‖ ^ 2) := fun i =>
    hasSum_norm_sq_inner_basis c (S (b i))
  have hcol : ∀ j : w', HasSum (fun i : w => F i j)
      (‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2) := by
    intro j
    have e1 : ∀ i : w, ⟪c j, S (b i)⟫_ℂ =
        ⟪(ContinuousLinearMap.adjoint S) (c j), b i⟫_ℂ := fun i =>
      (ContinuousLinearMap.adjoint_inner_left S (b i) (c j)).symm
    have key : (fun i : w => F i j) = fun i : w =>
        ‖⟪b i, (ContinuousLinearMap.adjoint S) (c j)⟫_ℂ‖ ^ 2 := by
      funext i
      show ‖⟪c j, S (b i)⟫_ℂ‖ ^ 2 = _
      rw [e1 i, ← inner_conj_symm (b i) ((ContinuousLinearMap.adjoint S) (c j)),
        RCLike.norm_conj]
    rw [key]
    exact hasSum_norm_sq_inner_basis b ((ContinuousLinearMap.adjoint S) (c j))
  have hjoint : Summable (Function.uncurry F) := by
    rw [summable_prod_of_nonneg hFnonneg]
    refine ⟨fun i => (hrow i).summable, ?_⟩
    have heq : (fun i : w => ∑' j : w', F i j) = fun i : w => ‖S (b i)‖ ^ 2 :=
      funext fun i => (hrow i).tsum_eq
    show Summable fun i : w => ∑' j : w', F i j
    rwa [heq]
  have hswap := hjoint.tsum_comm' (fun i => (hrow i).summable) (fun j => (hcol j).summable)
  have hLHS : ∑' j : w', ∑' i : w, F i j = ∑' j : w', ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2 :=
    tsum_congr fun j => (hcol j).tsum_eq
  have hRHS : ∑' i : w, ∑' j : w', F i j = ∑' i : w, ‖S (b i)‖ ^ 2 :=
    tsum_congr fun i => (hrow i).tsum_eq
  have hEq : ∑' j : w', ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2 = ∑' i : w, ‖S (b i)‖ ^ 2 := by
    rw [← hLHS, ← hRHS]; exact hswap
  set G : w' → w → ℝ := fun j i => F i j with hGdef
  have hGnonneg : 0 ≤ Function.uncurry G := fun _ => sq_nonneg _
  have hjointG : Summable (Function.uncurry G) := by
    have hcomp : Function.uncurry G = Function.uncurry F ∘ (Equiv.prodComm w' w) := by
      funext p; simp [Function.uncurry, hGdef, Equiv.prodComm]
    rw [hcomp]
    exact (Equiv.prodComm w' w).summable_iff.mpr hjoint
  have hcolSummable : Summable
      (fun j : w' => ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2) := by
    have hpair := (summable_prod_of_nonneg hGnonneg).mp hjointG
    have h2 : Summable fun j : w' => ∑' i : w, G j i := hpair.2
    have heq2 : (fun j : w' => ∑' i : w, G j i) = fun j : w' =>
        ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2 :=
      funext fun j => (hcol j).tsum_eq
    rwa [heq2] at h2
  rw [← hEq]
  exact hcolSummable.hasSum

lemma summable_norm_sq_adjoint_of_summable_norm_sq {S : H →L[ℂ] H}
    {w : Set H} (b : HilbertBasis w ℂ H)
    (hb : Summable (fun i : w => ‖S (b i)‖ ^ 2)) :
    Summable (fun i : w => ‖(ContinuousLinearMap.adjoint S) (b i)‖ ^ 2) :=
  (hasSum_norm_sq_apply_eq_adjoint b b hb).summable

lemma hasSum_norm_sq_apply_of_basis {S : H →L[ℂ] H} {w w' : Set H}
    (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H)
    (hb : Summable (fun i : w => ‖S (b i)‖ ^ 2)) :
    HasSum (fun j : w' => ‖S (c j)‖ ^ 2) (∑' i : w, ‖S (b i)‖ ^ 2) := by
  have hfirst := hasSum_norm_sq_apply_eq_adjoint b c hb
  have hstarc : Summable (fun j : w' => ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2) :=
    hfirst.summable
  have hsecond := hasSum_norm_sq_apply_eq_adjoint (S := ContinuousLinearMap.adjoint S) c c hstarc
  have hsecond' : HasSum (fun j : w' => ‖S (c j)‖ ^ 2)
      (∑' j : w', ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2) := by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using hsecond
  rw [← hfirst.tsum_eq]
  exact hsecond'

theorem summable_norm_sq_apply_of_hilbertBasis {S : H →L[ℂ] H}
    (w : Set H) (b : HilbertBasis w ℂ H) (hS : IsHilbertSchmidt S) :
    Summable (fun i : w => ‖S (b i)‖ ^ 2) := by
  rcases hS with ⟨w₀, b₀, hb₀⟩
  exact (hasSum_norm_sq_apply_of_basis b₀ b hb₀).summable

/-! ## Elementary algebraic closure -/

theorem isHilbertSchmidt_zero : IsHilbertSchmidt (0 : H →L[ℂ] H) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  refine ⟨w, b, ?_⟩
  simp

omit [CompleteSpace H] in
theorem isHilbertSchmidt_smul {S : H →L[ℂ] H} (c : ℂ) (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (c • S) := by
  rcases hS with ⟨w, b, hb⟩
  refine ⟨w, b, ?_⟩
  have hmul := hb.mul_left (‖c‖ ^ 2)
  apply hmul.congr
  intro i
  rw [smul_apply, norm_smul]
  ring

theorem isHilbertSchmidt_add {R S : H →L[ℂ] H}
    (hR : IsHilbertSchmidt R) (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (R + S) := by
  rcases hR with ⟨w, b, hbR⟩
  have hSb : Summable (fun i : w => ‖S (b i)‖ ^ 2) := summable_norm_sq_apply_of_hilbertBasis w b hS
  refine ⟨w, b, ?_⟩
  apply Summable.of_nonneg_of_le (fun i => sq_nonneg _)
  · intro i
    have hnorm : ‖R (b i) + S (b i)‖ ≤ ‖R (b i)‖ + ‖S (b i)‖ := norm_add_le _ _
    have hsq : ‖R (b i) + S (b i)‖ ^ 2 ≤ (‖R (b i)‖ + ‖S (b i)‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
    calc
      ‖(R + S) (b i)‖ ^ 2 = ‖R (b i) + S (b i)‖ ^ 2 := by rfl
      _ ≤ (‖R (b i)‖ + ‖S (b i)‖) ^ 2 := hsq
      _ ≤ 2 * ‖R (b i)‖ ^ 2 + 2 * ‖S (b i)‖ ^ 2 := by
        nlinarith [sq_nonneg (‖R (b i)‖ - ‖S (b i)‖)]
  · exact (hbR.mul_left 2).add (hSb.mul_left 2)

theorem isHilbertSchmidt_sub {R S : H →L[ℂ] H}
    (hR : IsHilbertSchmidt R) (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (R - S) := by
  simpa [sub_eq_add_neg] using isHilbertSchmidt_add hR (isHilbertSchmidt_smul (-1 : ℂ) hS)

theorem isHilbertSchmidt_star {S : H →L[ℂ] H} (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (star S) := by
  rcases hS with ⟨w, b, hb⟩
  refine ⟨w, b, ?_⟩
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact summable_norm_sq_adjoint_of_summable_norm_sq b hb

omit [CompleteSpace H] in
theorem isHilbertSchmidt_mul_left_of_opNorm_le_one {U S : H →L[ℂ] H}
    (hU : ‖U‖ ≤ 1) (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (U * S) := by
  rcases hS with ⟨w, b, hb⟩
  refine ⟨w, b, ?_⟩
  apply Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) hb
  have hi : ‖U (S (b i))‖ ≤ ‖S (b i)‖ := by
    calc
      ‖U (S (b i))‖ ≤ ‖U‖ * ‖S (b i)‖ := U.le_opNorm _
      _ ≤ ‖S (b i)‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hU (norm_nonneg (S (b i)))
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hi

theorem isHilbertSchmidt_mul_right_of_opNorm_le_one {S U : H →L[ℂ] H}
    (hU : ‖U‖ ≤ 1) (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (S * U) := by
  have hU' : ‖star U‖ ≤ 1 := by simpa using hU
  have hleft : IsHilbertSchmidt (star U * star S) :=
    isHilbertSchmidt_mul_left_of_opNorm_le_one hU' (isHilbertSchmidt_star hS)
  have hdouble : IsHilbertSchmidt (star (star U * star S)) := isHilbertSchmidt_star hleft
  simpa only [star_mul, star_star] using hdouble

theorem isHilbertSchmidt_mul_left {U S : H →L[ℂ] H} (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (U * S) := by
  by_cases hU0 : ‖U‖ = 0
  · have hzero : U = 0 := norm_eq_zero.mp hU0
    simpa [hzero] using isHilbertSchmidt_zero (H := H)
  · let V : H →L[ℂ] H := (‖U‖ : ℂ)⁻¹ • U
    have hV : ‖V‖ ≤ 1 := by dsimp [V]; simp [norm_smul, norm_inv, hU0]
    have hVS : IsHilbertSchmidt (V * S) := isHilbertSchmidt_mul_left_of_opNorm_le_one hV hS
    have hscaled : IsHilbertSchmidt ((‖U‖ : ℂ) • (V * S)) := isHilbertSchmidt_smul (‖U‖ : ℂ) hVS
    have hVeq : (‖U‖ : ℂ) • V = U := by ext x; simp [V, hU0]
    rw [show (‖U‖ : ℂ) • (V * S) = ((‖U‖ : ℂ) • V) * S by simp] at hscaled
    rwa [hVeq] at hscaled

theorem isHilbertSchmidt_mul_right {S U : H →L[ℂ] H} (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (S * U) := by
  have hleft : IsHilbertSchmidt (star U * star S) :=
    isHilbertSchmidt_mul_left (U := star U) (isHilbertSchmidt_star hS)
  have hdouble : IsHilbertSchmidt (star (star U * star S)) := isHilbertSchmidt_star hleft
  simpa only [star_mul, star_star] using hdouble

/-- `S⋆S` is trace class whenever `S` is Hilbert–Schmidt. -/
theorem isTraceClass_star_mul_self_of_isHilbertSchmidt {S : H →L[ℂ] H}
    (hS : IsHilbertSchmidt S) : IsTraceClass (star S * S) := by
  apply isTraceClass_iff.mpr
  intro w b
  have hdiag : Summable (fun i : w => ‖S (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hS
  have hpos : 0 ≤ star S * S := star_mul_self_nonneg S
  have habs : CFC.abs (star S * S) = star S * S := CFC.abs_of_nonneg _ hpos
  apply hdiag.congr
  intro i
  rw [habs]
  have hinner : ⟪b i, (star S * S) (b i)⟫_ℂ = ⟪S (b i), S (b i)⟫_ℂ := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [hinner, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- `S S⋆` is trace class whenever `S` is Hilbert–Schmidt. -/
theorem isTraceClass_mul_star_of_isHilbertSchmidt {S : H →L[ℂ] H}
    (hS : IsHilbertSchmidt S) : IsTraceClass (S * star S) := by
  have hstar : IsHilbertSchmidt (star S) := isHilbertSchmidt_star hS
  simpa only [star_star] using isTraceClass_star_mul_self_of_isHilbertSchmidt hstar

/-! ## Cauchy–Schwarz estimates on Hilbert–Schmidt diagonals -/

private lemma holder_two_two : (2 : ℝ).HolderConjugate 2 := by
  rw [Real.holderConjugate_iff]; constructor <;> norm_num

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- The real `ℓ²` Cauchy–Schwarz estimate, in the tsum form needed for operator diagonal bounds. -/
@[nolint unusedArguments]
theorem tsum_mul_le_sqrt_mul_sqrt {w : Set H} {f g : w → ℝ}
    (hf : Summable (fun i => f i ^ 2)) (hg : Summable (fun i => g i ^ 2))
    (hf_nonneg : ∀ i, 0 ≤ f i) (hg_nonneg : ∀ i, 0 ≤ g i) :
    ∑' i : w, f i * g i ≤ Real.sqrt (∑' i : w, f i ^ 2) * Real.sqrt (∑' i : w, g i ^ 2) := by
  have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg (f := f) (g := g) holder_two_two
    hf_nonneg hg_nonneg (by convert hf using 1; ext i; norm_num [Real.rpow_natCast])
    (by convert hg using 1; ext i; norm_num [Real.rpow_natCast])
  have hf_eq : (∑' i : w, f i ^ (2 : ℝ)) = ∑' i : w, f i ^ 2 :=
    tsum_congr fun i => Real.rpow_natCast (f i) 2
  have hg_eq : (∑' i : w, g i ^ (2 : ℝ)) = ∑' i : w, g i ^ 2 :=
    tsum_congr fun i => Real.rpow_natCast (g i) 2
  rw [hf_eq, hg_eq] at h
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  simpa only [Real.rpow_natCast] using h

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
@[nolint unusedArguments]
lemma summable_norm_mul_of_square_sums {w : Set H}
    (f g : w → ℝ) (hf : Summable (fun i => f i ^ 2)) (hg : Summable (fun i => g i ^ 2))
    (hf_nonneg : ∀ i, 0 ≤ f i) (hg_nonneg : ∀ i, 0 ≤ g i) :
    Summable (fun i => f i * g i) := by
  apply Real.summable_mul_of_Lp_Lq_of_nonneg holder_two_two hf_nonneg hg_nonneg
  · convert hf using 1; ext i; norm_num [Real.rpow_natCast]
  · convert hg using 1; ext i; norm_num [Real.rpow_natCast]

omit [CompleteSpace H] in
theorem tsum_norm_inner_mul_inner_le {w : Set H} (b : HilbertBasis w ℂ H) (x y : H) :
    ∑' i : w, ‖⟪x, b i⟫_ℂ‖ * ‖⟪b i, y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := by
  have hx : HasSum (fun i : w => ‖⟪x, b i⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
    convert hasSum_norm_sq_inner_basis b x using 1
    funext i
    rw [← inner_conj_symm x (b i), RCLike.norm_conj]
  have hy : HasSum (fun i : w => ‖⟪b i, y⟫_ℂ‖ ^ 2) (‖y‖ ^ 2) := hasSum_norm_sq_inner_basis b y
  have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg
    (f := fun i : w => ‖⟪x, b i⟫_ℂ‖) (g := fun i : w => ‖⟪b i, y⟫_ℂ‖) holder_two_two
    (fun i => norm_nonneg _) (fun i => norm_nonneg _)
    (by convert hx.summable using 1; ext i; norm_num [Real.rpow_natCast])
    (by convert hy.summable using 1; ext i; norm_num [Real.rpow_natCast])
  have hxs : (∑' i : w, ‖⟪x, b i⟫_ℂ‖ ^ (2 : ℝ)) = ‖x‖ ^ 2 := by
    convert hx.tsum_eq using 1
    exact tsum_congr fun i => Real.rpow_natCast ‖⟪x, b i⟫_ℂ‖ 2
  have hys : (∑' i : w, ‖⟪b i, y⟫_ℂ‖ ^ (2 : ℝ)) = ‖y‖ ^ 2 := by
    convert hy.tsum_eq using 1
    exact tsum_congr fun i => Real.rpow_natCast ‖⟪b i, y⟫_ℂ‖ 2
  calc
    ∑' i : w, ‖⟪x, b i⟫_ℂ‖ * ‖⟪b i, y⟫_ℂ‖ ≤
        (∑' i : w, ‖⟪x, b i⟫_ℂ‖ ^ (2 : ℝ)) ^ (1 / 2) *
          (∑' i : w, ‖⟪b i, y⟫_ℂ‖ ^ (2 : ℝ)) ^ (1 / 2) :=
      h
    _ = ‖x‖ * ‖y‖ := by
      rw [hxs, hys, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _),
        Real.sqrt_sq (norm_nonneg _)]

omit [CompleteSpace H] in
private lemma summable_norm_inner_mul_inner {w : Set H} (b : HilbertBasis w ℂ H) (x y : H) :
    Summable (fun i : w => ‖⟪x, b i⟫_ℂ‖ * ‖⟪b i, y⟫_ℂ‖) := by
  apply Real.summable_mul_of_Lp_Lq_of_nonneg holder_two_two
    (fun i => norm_nonneg _) (fun i => norm_nonneg _)
  · have hx := (hasSum_norm_sq_inner_basis b x).summable
    convert hx using 1
    funext i
    rw [← inner_conj_symm x (b i), RCLike.norm_conj]
    exact Real.rpow_natCast ‖⟪b i, x⟫_ℂ‖ 2
  · have hy := (hasSum_norm_sq_inner_basis b y).summable
    convert hy using 1; ext i; norm_num [Real.rpow_natCast]

/-- The diagonal coefficients of a product of two Hilbert–Schmidt operators are absolutely
summable. -/
theorem summable_diagonal_of_hilbertSchmidt {R S : H →L[ℂ] H}
    {w : Set H} (b : HilbertBasis w ℂ H) (hR : IsHilbertSchmidt R) (hS : IsHilbertSchmidt S) :
    Summable (fun i : w => ⟪b i, (R * S) (b i)⟫_ℂ) := by
  have hRstar : IsHilbertSchmidt (ContinuousLinearMap.adjoint R) := by
    rcases hR with ⟨w₀, b₀, hb₀⟩
    exact ⟨w₀, b₀, summable_norm_sq_adjoint_of_summable_norm_sq b₀ hb₀⟩
  have hRb : Summable (fun i : w => ‖(ContinuousLinearMap.adjoint R) (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hRstar
  have hSb : Summable (fun i : w => ‖S (b i)‖ ^ 2) := summable_norm_sq_apply_of_hilbertBasis w b hS
  have hprod : Summable (fun i : w =>
      ‖(ContinuousLinearMap.adjoint R) (b i)‖ * ‖S (b i)‖) :=
    summable_norm_mul_of_square_sums _ _ hRb hSb (fun i => norm_nonneg _) (fun i => norm_nonneg _)
  apply Summable.of_norm_bounded hprod
  intro i
  have hi : ⟪b i, (R * S) (b i)⟫_ℂ = ⟪(ContinuousLinearMap.adjoint R) (b i), S (b i)⟫_ℂ :=
    (ContinuousLinearMap.adjoint_inner_left R (S (b i)) (b i)).symm
  rw [hi]
  simpa only [mul_apply_eq_comp] using
    norm_inner_le_norm ((ContinuousLinearMap.adjoint R) (b i)) (S (b i))

private lemma summable_matrix_of_hilbertSchmidt {R S : H →L[ℂ] H}
    {w w' : Set H} (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H)
    (hR : IsHilbertSchmidt R) (hS : IsHilbertSchmidt S) :
    Summable (Function.uncurry (fun (i : w) (j : w') =>
      ⟪(ContinuousLinearMap.adjoint R) (b i), c j⟫_ℂ * ⟪c j, S (b i)⟫_ℂ)) := by
  have hRstar : IsHilbertSchmidt (ContinuousLinearMap.adjoint R) := by
    rcases hR with ⟨w₀, b₀, hb₀⟩
    exact ⟨w₀, b₀, summable_norm_sq_adjoint_of_summable_norm_sq b₀ hb₀⟩
  have hRb : Summable (fun i : w => ‖(ContinuousLinearMap.adjoint R) (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hRstar
  have hSb : Summable (fun i : w => ‖S (b i)‖ ^ 2) := summable_norm_sq_apply_of_hilbertBasis w b hS
  have hprod : Summable (fun i : w =>
      ‖(ContinuousLinearMap.adjoint R) (b i)‖ * ‖S (b i)‖) :=
    summable_norm_mul_of_square_sums _ _ hRb hSb (fun i => norm_nonneg _) (fun i => norm_nonneg _)
  let F : w → w' → ℂ := fun i j => ⟪(ContinuousLinearMap.adjoint R) (b i), c j⟫_ℂ * ⟪c j, S (b i)⟫_ℂ
  let M : w → w' → ℝ := fun i j => ‖F i j‖
  have hMrow : ∀ i : w, Summable (M i) := by
    intro i
    have h := summable_norm_inner_mul_inner c ((ContinuousLinearMap.adjoint R) (b i)) (S (b i))
    simpa [M, F, norm_mul] using h
  have hMrow_bound : ∀ i : w, ∑' j : w', M i j ≤
      ‖(ContinuousLinearMap.adjoint R) (b i)‖ * ‖S (b i)‖ := by
    intro i
    simpa [M, F, norm_mul] using
      tsum_norm_inner_mul_inner_le c ((ContinuousLinearMap.adjoint R) (b i)) (S (b i))
  have hMrows : Summable (fun i : w => ∑' j : w', M i j) :=
    Summable.of_nonneg_of_le (fun i => tsum_nonneg fun j => norm_nonneg _) hMrow_bound hprod
  have hMnonneg : 0 ≤ Function.uncurry M := fun _ => norm_nonneg _
  have hM : Summable (Function.uncurry M) := by
    rw [summable_prod_of_nonneg hMnonneg]; exact ⟨hMrow, hMrows⟩
  apply Summable.of_norm_bounded hM
  rintro ⟨i, j⟩
  exact le_rfl

private lemma hasSum_matrix_row_of_hilbertSchmidt {R S : H →L[ℂ] H}
    {w w' : Set H} (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H) (i : w) :
    HasSum (fun j : w' => ⟪(ContinuousLinearMap.adjoint R) (b i), c j⟫_ℂ * ⟪c j, S (b i)⟫_ℂ)
      ⟪b i, (R * S) (b i)⟫_ℂ := by
  have h := c.hasSum_inner_mul_inner ((ContinuousLinearMap.adjoint R) (b i)) (S (b i))
  have hi : ⟪(ContinuousLinearMap.adjoint R) (b i), S (b i)⟫_ℂ = ⟪b i, (R * S) (b i)⟫_ℂ :=
    ContinuousLinearMap.adjoint_inner_left R (S (b i)) (b i)
  rwa [hi] at h

private lemma hasSum_matrix_col_of_hilbertSchmidt {R S : H →L[ℂ] H}
    {w w' : Set H} (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H) (j : w') :
    HasSum (fun i : w => ⟪(ContinuousLinearMap.adjoint R) (b i), c j⟫_ℂ * ⟪c j, S (b i)⟫_ℂ)
      ⟪c j, (S * R) (c j)⟫_ℂ := by
  have h := b.hasSum_inner_mul_inner ((ContinuousLinearMap.adjoint S) (c j)) (R (c j))
  have hR : ∀ i : w, ⟪(ContinuousLinearMap.adjoint R) (b i), c j⟫_ℂ = ⟪b i, R (c j)⟫_ℂ := fun i =>
    ContinuousLinearMap.adjoint_inner_left R (c j) (b i)
  have hS : ∀ i : w, ⟪c j, S (b i)⟫_ℂ = ⟪(ContinuousLinearMap.adjoint S) (c j), b i⟫_ℂ := fun i =>
    (ContinuousLinearMap.adjoint_inner_left S (b i) (c j)).symm
  have hpoint : (fun i : w => ⟪(ContinuousLinearMap.adjoint R) (b i), c j⟫_ℂ * ⟪c j, S (b i)⟫_ℂ) =
      (fun i : w => ⟪(ContinuousLinearMap.adjoint S) (c j), b i⟫_ℂ * ⟪b i, R (c j)⟫_ℂ) := by
    funext i; rw [hR i, hS i, mul_comm]
  have hSR : ⟪(ContinuousLinearMap.adjoint S) (c j), R (c j)⟫_ℂ = ⟪c j, (S * R) (c j)⟫_ℂ :=
    ContinuousLinearMap.adjoint_inner_left S (R (c j)) (c j)
  rw [hpoint, ← hSR]
  exact h

/-- **Basis-swap identity**: the diagonal sum of `R * S` in one basis equals the diagonal sum of
`S * R` in any other. This is the Hilbert–Schmidt Fubini step consumed by `GeneralIdeal.lean`'s
unconditional trace theorem and `GeneralProduct.lean`'s master lemma. -/
theorem tsum_diagonal_mul_eq_tsum_diagonal_swap {R S : H →L[ℂ] H}
    {w w' : Set H} (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H)
    (hR : IsHilbertSchmidt R) (hS : IsHilbertSchmidt S) :
    (∑' i : w, ⟪b i, (R * S) (b i)⟫_ℂ) = ∑' j : w', ⟪c j, (S * R) (c j)⟫_ℂ := by
  let F : w → w' → ℂ := fun i j => ⟪(ContinuousLinearMap.adjoint R) (b i), c j⟫_ℂ * ⟪c j, S (b i)⟫_ℂ
  have hF : Summable (Function.uncurry F) := summable_matrix_of_hilbertSchmidt b c hR hS
  have hrow : ∀ i : w, HasSum (F i) ⟪b i, (R * S) (b i)⟫_ℂ := fun i =>
    hasSum_matrix_row_of_hilbertSchmidt b c i
  have hcol : ∀ j : w', HasSum (fun i : w => F i j) ⟪c j, (S * R) (c j)⟫_ℂ := fun j =>
    hasSum_matrix_col_of_hilbertSchmidt b c j
  have hswap := hF.tsum_comm' (fun i => (hrow i).summable) (fun j => (hcol j).summable)
  calc
    ∑' i : w, ⟪b i, (R * S) (b i)⟫_ℂ = ∑' i : w, ∑' j : w', F i j :=
      tsum_congr fun i => (hrow i).tsum_eq.symm
    _ = ∑' j : w', ∑' i : w, F i j := hswap.symm
    _ = ∑' j : w', ⟪c j, (S * R) (c j)⟫_ℂ := tsum_congr fun j => (hcol j).tsum_eq

/-! ## Quantitative right-multiplication estimate -/

/-- **Quantitative right-multiplication-by-a-contraction bound**: for `X` and a contraction `W`,
the Hilbert–Schmidt square sum of `X * W` never exceeds that of `X` itself, in the same basis. -/
theorem tsum_norm_sq_mul_right_le_of_opNorm_le_one {X W : H →L[ℂ] H} (hW : ‖W‖ ≤ 1)
    (hX : IsHilbertSchmidt X) {w : Set H} (b : HilbertBasis w ℂ H) :
    (∑' i : w, ‖(X * W) (b i)‖ ^ 2) ≤ ∑' i : w, ‖X (b i)‖ ^ 2 := by
  have hXW : IsHilbertSchmidt (X * W) := isHilbertSchmidt_mul_right hX
  have hXstar : IsHilbertSchmidt (ContinuousLinearMap.adjoint X) := by
    rcases hX with ⟨w₀, b₀, hb₀⟩
    exact ⟨w₀, b₀, summable_norm_sq_adjoint_of_summable_norm_sq b₀ hb₀⟩
  have hXWb : Summable (fun i : w => ‖(X * W) (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hXW
  have hXb : Summable (fun i : w => ‖X (b i)‖ ^ 2) := summable_norm_sq_apply_of_hilbertBasis w b hX
  have hstep1 : (∑' i : w, ‖(X * W) (b i)‖ ^ 2) =
      ∑' i : w, ‖(ContinuousLinearMap.adjoint (X * W)) (b i)‖ ^ 2 :=
    (hasSum_norm_sq_apply_eq_adjoint b b hXWb).tsum_eq.symm
  have hadj : ContinuousLinearMap.adjoint (X * W) =
      ContinuousLinearMap.adjoint W * ContinuousLinearMap.adjoint X := by
    show ContinuousLinearMap.adjoint (X ∘L W) = _
    rw [ContinuousLinearMap.adjoint_comp]; rfl
  have hstep2 : ∀ i : w,
      ‖(ContinuousLinearMap.adjoint W * ContinuousLinearMap.adjoint X) (b i)‖ ≤
        ‖(ContinuousLinearMap.adjoint X) (b i)‖ := by
    intro i
    calc
      ‖(ContinuousLinearMap.adjoint W * ContinuousLinearMap.adjoint X) (b i)‖ =
          ‖(ContinuousLinearMap.adjoint W) ((ContinuousLinearMap.adjoint X) (b i))‖ := by
        rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      _ ≤ ‖ContinuousLinearMap.adjoint W‖ * ‖(ContinuousLinearMap.adjoint X) (b i)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖(ContinuousLinearMap.adjoint X) (b i)‖ := by
        have hWadj : ‖ContinuousLinearMap.adjoint W‖ ≤ 1 := by
          rw [(ContinuousLinearMap.adjoint).norm_map W]; exact hW
        calc ‖ContinuousLinearMap.adjoint W‖ * ‖(ContinuousLinearMap.adjoint X) (b i)‖ ≤
            1 * ‖(ContinuousLinearMap.adjoint X) (b i)‖ :=
              mul_le_mul_of_nonneg_right hWadj (norm_nonneg _)
          _ = ‖(ContinuousLinearMap.adjoint X) (b i)‖ := one_mul _
  have hXstarb : Summable (fun i : w => ‖(ContinuousLinearMap.adjoint X) (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hXstar
  have hcompareSummable : Summable (fun i : w =>
      ‖(ContinuousLinearMap.adjoint W * ContinuousLinearMap.adjoint X) (b i)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _)
      (fun i => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hstep2 i)) hXstarb
  have hcompare : (∑' i : w, ‖(ContinuousLinearMap.adjoint W * ContinuousLinearMap.adjoint X)
      (b i)‖ ^ 2) ≤ ∑' i : w, ‖(ContinuousLinearMap.adjoint X) (b i)‖ ^ 2 :=
    hcompareSummable.tsum_le_tsum
      (fun i => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hstep2 i)) hXstarb
  have hstep3 : (∑' i : w, ‖(ContinuousLinearMap.adjoint X) (b i)‖ ^ 2) = ∑' i : w, ‖X (b i)‖ ^ 2 :=
    (hasSum_norm_sq_apply_eq_adjoint b b hXb).tsum_eq
  calc
    (∑' i : w, ‖(X * W) (b i)‖ ^ 2) =
        ∑' i : w, ‖(ContinuousLinearMap.adjoint (X * W)) (b i)‖ ^ 2 := hstep1
    _ = ∑' i : w, ‖(ContinuousLinearMap.adjoint W * ContinuousLinearMap.adjoint X) (b i)‖ ^ 2 := by
      rw [hadj]
    _ ≤ ∑' i : w, ‖(ContinuousLinearMap.adjoint X) (b i)‖ ^ 2 := hcompare
    _ = ∑' i : w, ‖X (b i)‖ ^ 2 := hstep3

/-- The self-adjoint specialization of the right-multiplication bound, needed by
`GeneralIdeal.lean`/`PositiveIdeal`-style conjugation estimates. -/
theorem tsum_norm_sq_mul_right_le_of_selfAdjoint {S A : H →L[ℂ] H}
    (hSself : IsSelfAdjoint S) (hS : IsHilbertSchmidt S)
    {w w' : Set H} (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H) :
    (∑' i : w', ‖(S * A) (c i)‖ ^ 2) ≤ ‖A‖ ^ 2 * (∑' j : w, ‖S (b j)‖ ^ 2) := by
  let R : H →L[ℂ] H := S * A
  have hR : IsHilbertSchmidt R := isHilbertSchmidt_mul_right hS
  have hRc : Summable (fun i : w' => ‖R (c i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w' c hR
  have hEq : HasSum (fun j : w => ‖(ContinuousLinearMap.adjoint R) (b j)‖ ^ 2)
      (∑' i : w', ‖R (c i)‖ ^ 2) := hasSum_norm_sq_apply_eq_adjoint c b hRc
  have hAdjSummable : Summable (fun j : w => ‖(ContinuousLinearMap.adjoint R) (b j)‖ ^ 2) :=
    hEq.summable
  have hSb : Summable (fun j : w => ‖S (b j)‖ ^ 2) := summable_norm_sq_apply_of_hilbertBasis w b hS
  have hRstar : ContinuousLinearMap.adjoint R = ContinuousLinearMap.adjoint A * S := by
    rw [show R = S ∘SL A by rfl, ContinuousLinearMap.adjoint_comp]
    rw [← ContinuousLinearMap.mul_def, (ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself]
  have hpoint : ∀ j : w, ‖(ContinuousLinearMap.adjoint R) (b j)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖S (b j)‖ ^ 2 := by
    intro j
    rw [hRstar, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    have hnorm : ‖ContinuousLinearMap.adjoint A‖ = ‖A‖ := (ContinuousLinearMap.adjoint).norm_map A
    have hle : ‖ContinuousLinearMap.adjoint A (S (b j))‖ ≤ ‖A‖ * ‖S (b j)‖ := by
      rw [← hnorm]; exact ContinuousLinearMap.le_opNorm _ _
    calc
      ‖ContinuousLinearMap.adjoint A (S (b j))‖ ^ 2 ≤ (‖A‖ * ‖S (b j)‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hle
      _ = ‖A‖ ^ 2 * ‖S (b j)‖ ^ 2 := by ring
  have hscaled : Summable (fun j : w => ‖A‖ ^ 2 * ‖S (b j)‖ ^ 2) := hSb.mul_left (‖A‖ ^ 2)
  have hsum : (∑' j : w, ‖(ContinuousLinearMap.adjoint R) (b j)‖ ^ 2) ≤
      ∑' j : w, ‖A‖ ^ 2 * ‖S (b j)‖ ^ 2 := hAdjSummable.tsum_le_tsum hpoint hscaled
  calc
    ∑' i : w', ‖(S * A) (c i)‖ ^ 2 = ∑' j : w, ‖(ContinuousLinearMap.adjoint R) (b j)‖ ^ 2 :=
      hEq.tsum_eq.symm
    _ ≤ ∑' j : w, ‖A‖ ^ 2 * ‖S (b j)‖ ^ 2 := hsum
    _ = ‖A‖ ^ 2 * (∑' j : w, ‖S (b j)‖ ^ 2) := tsum_mul_left

end HilbertSchmidt

end
