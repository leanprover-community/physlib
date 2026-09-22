/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.JB.GeneratedByOne.CFC

/-!

# Uniqueness of the positive square root

## i. Overview

`jordanSqrt_eq_of_mem_closedGeneratedByOne` (`CFC.lean`) only proves
uniqueness of the canonical positive square root among roots already known to lie in
`ClosedGeneratedByOne a`. This file removes that restriction: it proves that **every** nonnegative
`b` with `b * b = a` equals `jordanSqrt a ha`, for `b` an arbitrary element of the ambient JB
algebra.

The genuinely multielement obstruction is that `b` is a priori unrelated to `ClosedGeneratedByOne
a`; it is not smuggled in by treating `a` and `b` as if they already lay in one common associative
algebra. The argument instead uses a single algebraic identity that is *ambient-independent*:
evaluating a real polynomial `p` at an element by repeated Jordan multiplication produces an
answer depending only on that element's value in `E`, never on which enveloping closed
one-generator algebra it is regarded as living in (`aevalCoe_eq_jordanPolyEval`). Consequently, for
every real polynomial `p`,

```text
jordanPolyEval b (p.comp (X ^ 2)) = jordanPolyEval (b * b) p = jordanPolyEval a p,
```

purely algebraically, with no reference to any spectral or order theory. The two sides are then
independently approximated: on the left, using only `b`'s own polynomial functional calculus and
`b ≥ 0`, `p.comp (X ^ 2)` evaluated at `b` approximates `b` itself; on the right, using only `a`'s
own calculus and `a ≥ 0`, `p` evaluated at `a` approximates `jordanSqrt a ha`. Because the exact
algebraic identity forces the two approximating quantities to coincide term by term, the two limits
coincide, giving `b = jordanSqrt a ha`.

## ii. Key definitions and results

- `NormedJordanAlgebra.jordanPolyEval`
- `NormedJordanAlgebra.aevalCoe_eq_jordanPolyEval`
- `NormedJordanAlgebra.jordanPolyEval_comp_sq`
- `NormedJordanAlgebra.jordanSqrt_eq_of_nonneg_of_mul_self`
- `NormedJordanAlgebra.eq_of_nonneg_of_mul_self_eq_mul_self`

## iii. Table of contents

- A. The ambient-independent polynomial evaluation
- B. Approximation of the polynomial calculus
- C. Uniform polynomial approximation of the square root
- D. Unrestricted uniqueness of the positive square root

-/

@[expose] public section

namespace NormedJordanAlgebra

open scoped JordanAlgebra

/-! ## A. The ambient-independent polynomial evaluation -/

variable {E : Type*} [NormedJordanAlgebra E]

/-- Evaluate a real polynomial at a Jordan element by repeated Jordan multiplication. Unlike
`Polynomial.aeval (closedGenerator x) p`, this definition makes no reference to any particular
closed one-generator algebra: it is visibly a function of `x` and `p` alone. -/
def jordanPolyEval (x : E) (p : Polynomial ℝ) : E :=
  ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • x ^[i]

/-- Polynomial evaluation inside *any* closed one-generator algebra containing `x` coerces to
`jordanPolyEval (x : E) p`. This is the ambient-independence lemma: the two sides of
`Polynomial.aeval x p = Polynomial.aeval y p` for `x`, `y` living in different closed
one-generator algebras but sharing the same ambient value are forced to agree, because both equal
the same `jordanPolyEval`. -/
theorem aevalCoe_eq_jordanPolyEval {u : E} (x : ClosedGeneratedByOne u) (p : Polynomial ℝ) :
    (Polynomial.aeval x p : E) = jordanPolyEval (x : E) p := by
  rw [Polynomial.aeval_eq_sum_range]
  unfold jordanPolyEval
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SetLike.val_smul, ClosedGeneratedByOne.pow_val]

/-- `jordanPolyEval` is additive in the polynomial argument. -/
theorem jordanPolyEval_add (x : E) (p q : Polynomial ℝ) :
    jordanPolyEval x (p + q) = jordanPolyEval x p + jordanPolyEval x q := by
  have h : ∀ (u : E) (r : Polynomial ℝ),
      jordanPolyEval u r = (Polynomial.aeval (closedGenerator u) r : E) := fun u r =>
    (aevalCoe_eq_jordanPolyEval (closedGenerator u) r).symm
  rw [h x p, h x q, h x (p + q), map_add]
  rfl

/-- The key algebraic identity behind square-root uniqueness: substituting `X ^ 2` before
evaluating at `v` agrees with evaluating directly at `v * v`. This is a purely algebraic identity,
with no order or norm hypothesis on `v`. -/
theorem jordanPolyEval_comp_sq (v : E) (p : Polynomial ℝ) :
    jordanPolyEval v (p.comp (Polynomial.X ^ 2)) = jordanPolyEval (v * v) p := by
  have h1 : jordanPolyEval v (p.comp (Polynomial.X ^ 2)) =
      (Polynomial.aeval (closedGenerator v) (p.comp (Polynomial.X ^ 2)) : E) :=
    (aevalCoe_eq_jordanPolyEval (closedGenerator v) _).symm
  rw [h1, Polynomial.aeval_comp]
  set w : ClosedGeneratedByOne v :=
      Polynomial.aeval (closedGenerator v) ((Polynomial.X : Polynomial ℝ) ^ 2)
    with hw
  have hwval : (w : E) = v * v := by
    rw [hw, Polynomial.aeval_X_pow, ClosedGeneratedByOne.pow_val, closedGenerator_val,
      JordanAlgebra.jpow_two]
  rw [aevalCoe_eq_jordanPolyEval w p, hwval]

/-! ## B. Approximation of the polynomial calculus -/

variable [JBAlgebra E]

/-- `jordanCfc` applied to a polynomial function is exactly `jordanPolyEval` at the same
polynomial. This connects the ambient-independent algebraic evaluation of §A to the intrinsic
continuous functional calculus. -/
theorem jordanCfc_toContinuousMapOnAlgHom [Nontrivial E] [PartialOrder E] [IsOrderedAddMonoid E]
    [IsArchimedeanOrderUnit E] [PosSMulMono ℝ E] [IsJBOrderUnit E] (a : E) (p : Polynomial ℝ) :
    jordanCfc a (Polynomial.toContinuousMapOnAlgHom (jordanSpectrum a) p) = jordanPolyEval a p := by
  have hmem : Polynomial.toContinuousMapOnAlgHom (jordanSpectrum a) p ∈
      (polynomialFunctions (jordanSpectrum a) : Set C(jordanSpectrum a, ℝ)) := by
    rw [polynomialFunctions_coe]
    exact ⟨p, rfl⟩
  let f : polynomialFunctions (jordanSpectrum a) :=
    ⟨Polynomial.toContinuousMapOnAlgHom (jordanSpectrum a) p, hmem⟩
  have hf : jordanCfc a (f : C(jordanSpectrum a, ℝ)) = jordanCfcLinear a f := rfl
  have heq : Polynomial.toContinuousMapOnAlgHom (jordanSpectrum a)
      (polynomialRepresentative a f) = Polynomial.toContinuousMapOnAlgHom (jordanSpectrum a) p :=
    toContinuousMapOn_polynomialRepresentative a f
  have haeval : Polynomial.aeval (closedGenerator a) (polynomialRepresentative a f) =
      Polynomial.aeval (closedGenerator a) p :=
    aeval_closedGenerator_eq_of_toContinuousMapOn_eq a heq
  show jordanCfc a (f : C(jordanSpectrum a, ℝ)) = jordanPolyEval a p
  rw [hf, jordanCfcLinear_eq_polynomialCfcLinearMap]
  show (Polynomial.aeval (closedGenerator a) (polynomialRepresentative a f) : E) =
    jordanPolyEval a p
  rw [haeval, aevalCoe_eq_jordanPolyEval, closedGenerator_val]

/-- Norm bound transporting a uniform polynomial approximation of a continuous target function
into a norm bound between `jordanPolyEval` and the intrinsic calculus. -/
theorem norm_jordanPolyEval_sub_jordanCfc_le [Nontrivial E] [PartialOrder E]
    [IsOrderedAddMonoid E] [IsArchimedeanOrderUnit E] [PosSMulMono ℝ E] [IsJBOrderUnit E]
    (a : E) (p : Polynomial ℝ) (F : C(jordanSpectrum a, ℝ)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ x : jordanSpectrum a, |p.eval (x : ℝ) - F x| ≤ δ) :
    ‖jordanPolyEval a p - jordanCfc a F‖ ≤ δ := by
  rw [← jordanCfc_toContinuousMapOnAlgHom a p, ← jordanCfc_sub]
  rw [show ‖jordanCfc a (Polynomial.toContinuousMapOnAlgHom (jordanSpectrum a) p - F)‖ =
      ‖Polynomial.toContinuousMapOnAlgHom (jordanSpectrum a) p - F‖ from norm_jordanCfc a _]
  rw [ContinuousMap.norm_le _ hδ]
  intro x
  have hval : (Polynomial.toContinuousMapOnAlgHom (jordanSpectrum a) p - F) x =
      p.eval (x : ℝ) - F x := by
    simp [Polynomial.toContinuousMapOnAlgHom_apply, Polynomial.toContinuousMapOn_apply,
      Polynomial.toContinuousMap_apply]
  rw [hval, Real.norm_eq_abs]
  exact hbound x

/-! ## C. Uniform polynomial approximation of the square root -/

/-- Every polynomial function on a compact real interval `[0, M]` extends to a global real
polynomial. This is the interval specialization of the general fact used for `jordanSpectrum`. -/
private theorem exists_polynomialRepresentative_of_mem {s : Set ℝ} {g : C(s, ℝ)}
    (hg : g ∈ (polynomialFunctions s : Set C(s, ℝ))) :
    ∃ p : Polynomial ℝ, Polynomial.toContinuousMapOnAlgHom s p = g := by
  rwa [polynomialFunctions_coe] at hg

/-- Classical uniform polynomial approximation of the real square root on a compact interval
`[0, M]`. This is ordinary Stone--Weierstrass applied on a fixed real interval, entirely
independent of any Jordan spectrum. -/
private theorem exists_polynomial_approx_sqrt (M : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, ∀ s ∈ Set.Icc (0 : ℝ) M, |p.eval s - Real.sqrt s| < ε := by
  have hcs : CompactSpace (Set.Icc (0 : ℝ) M) := isCompact_iff_compactSpace.mp isCompact_Icc
  set K : Set ℝ := Set.Icc (0 : ℝ) M with hK
  let f : C(K, ℝ) := ⟨fun x => Real.sqrt (x : ℝ), Real.continuous_sqrt.comp continuous_subtype_val⟩
  have hdense : Dense (polynomialFunctions K : Set C(K, ℝ)) := by
    rw [dense_iff_closure_eq]
    have h := congrArg (fun A : Subalgebra ℝ C(K, ℝ) => (A : Set C(K, ℝ)))
      (polynomialFunctions.topologicalClosure K)
    change closure ↑(polynomialFunctions K) = ((⊤ : Subalgebra ℝ C(K, ℝ)) : Set C(K, ℝ))
    simpa only [Subalgebra.topologicalClosure_coe] using h
  obtain ⟨g, hgmem, hgdist⟩ := Metric.mem_closure_iff.mp (hdense f) ε hε
  obtain ⟨p, hp⟩ := exists_polynomialRepresentative_of_mem hgmem
  refine ⟨p, fun s hs => ?_⟩
  have hlt : ‖f - g‖ < ε := by rwa [dist_eq_norm] at hgdist
  have hpt : ‖(f - g) (⟨s, hs⟩ : K)‖ < ε := lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm _ _) hlt
  have heval : g (⟨s, hs⟩ : K) = p.eval s := by
    rw [← hp]
    simp [Polynomial.toContinuousMapOnAlgHom_apply, Polynomial.toContinuousMapOn_apply,
      Polynomial.toContinuousMap_apply]
  have hval : (f - g) (⟨s, hs⟩ : K) = Real.sqrt s - p.eval s := by
    change f (⟨s, hs⟩ : K) - g (⟨s, hs⟩ : K) = Real.sqrt s - p.eval s
    rw [heval]
    rfl
  rw [hval, Real.norm_eq_abs, abs_sub_comm] at hpt
  exact hpt

/-! ## D. Unrestricted uniqueness of the positive square root -/

/-- **Uniqueness of the positive square root, among arbitrary nonnegative elements of the
ambient JB algebra.** This removes the restriction in
`jordanSqrt_eq_of_mem_closedGeneratedByOne`, which only handled roots already known to lie in
`ClosedGeneratedByOne a`. The proof is genuinely multielement: it relates `a` and `b` only through
the ambient-independent algebraic identity `jordanPolyEval_comp_sq`, then closes an `ε`-argument
using each element's own, separately constructed, polynomial functional calculus. -/
theorem jordanSqrt_eq_of_nonneg_of_mul_self [Nontrivial E] [PartialOrder E]
    [IsOrderedAddMonoid E] [IsArchimedeanOrderUnit E] [PosSMulMono ℝ E] [IsJBOrderUnit E]
    (a : E) (ha : 0 ≤ a) (b : E) (hb0 : 0 ≤ b) (hb : b * b = a) :
    b = jordanSqrt a ha := by
  rw [← sub_eq_zero, ← norm_eq_zero (E := E)]
  by_contra hne
  set δ₀ : ℝ := ‖b - jordanSqrt a ha‖ with hδ₀
  have hδpos : 0 < δ₀ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  set ε : ℝ := δ₀ / 3 with hεdef
  have hεpos : 0 < ε := by positivity
  set M : ℝ := ‖a‖ with hM
  have hMnonneg : 0 ≤ M := norm_nonneg a
  have hbsq : ‖b‖ * ‖b‖ = M := by
    rw [hM, ← hb, JBAlgebra.norm_mul_self b, sq]
  obtain ⟨p, hp⟩ := exists_polynomial_approx_sqrt M ε hεpos
  set q : Polynomial ℝ := p.comp (Polynomial.X ^ 2) with hq
  -- The two sides are algebraically identical.
  have halg : jordanPolyEval b q = jordanPolyEval a p := by
    rw [hq, jordanPolyEval_comp_sq, hb]
  -- The `b`-side approximates `b` itself, using only `b`'s own spectrum.
  have hbspec : ∀ x : jordanSpectrum b, 0 ≤ (x : ℝ) := fun x => nonneg_of_mem_jordanSpectrum hb0 x.2
  have hbnorm : ∀ x : jordanSpectrum b, |x.1| ≤ ‖b‖ := by
    intro x
    have hxmem : x.1 ∈ spectrum ℝ (closedGenerator b) := x.2
    have := spectrum.norm_le_norm_of_mem (𝕜 := ℝ) hxmem
    simpa using this
  have hbbound : ∀ x : jordanSpectrum b,
      |q.eval (x : ℝ) - (ContinuousMap.restrict (jordanSpectrum b) (.id ℝ)) x| ≤ ε := by
    intro x
    have hx0 : (0 : ℝ) ≤ (x : ℝ) := hbspec x
    have hxb : (x : ℝ) ≤ ‖b‖ := (abs_le.mp (hbnorm x)).2
    have hqx : q.eval (x : ℝ) = p.eval ((x : ℝ) ^ 2) := by
      simp [hq, Polynomial.eval_comp]
    have hxsq : (x : ℝ) ^ 2 ∈ Set.Icc (0 : ℝ) M := by
      refine ⟨by positivity, ?_⟩
      rw [← hbsq, sq]
      exact mul_le_mul hxb hxb hx0 (norm_nonneg b)
    have hlt := hp ((x : ℝ) ^ 2) hxsq
    have hsqrt : Real.sqrt ((x : ℝ) ^ 2) = (x : ℝ) := Real.sqrt_sq hx0
    have hidval : (ContinuousMap.restrict (jordanSpectrum b) (.id ℝ)) x = (x : ℝ) := rfl
    rw [hqx, hidval]
    rw [hsqrt] at hlt
    exact le_of_lt hlt
  have hbapprox : ‖jordanPolyEval b q -
      jordanCfc b (ContinuousMap.restrict (jordanSpectrum b) (.id ℝ))‖ ≤ ε :=
    norm_jordanPolyEval_sub_jordanCfc_le b q _ hεpos.le hbbound
  rw [jordanCfc_id] at hbapprox
  -- The `a`-side approximates `jordanSqrt a ha`, using only `a`'s own spectrum.
  have haspec : ∀ x : jordanSpectrum a, 0 ≤ (x : ℝ) := fun x => nonneg_of_mem_jordanSpectrum ha x.2
  have hanorm : ∀ x : jordanSpectrum a, |x.1| ≤ M := by
    intro x
    have hxmem : x.1 ∈ spectrum ℝ (closedGenerator a) := x.2
    have := spectrum.norm_le_norm_of_mem (𝕜 := ℝ) hxmem
    simpa [hM] using this
  have habound : ∀ x : jordanSpectrum a,
      |p.eval (x : ℝ) - jordanSpectrumSqrt a x| ≤ ε := by
    intro x
    have hx0 : (0 : ℝ) ≤ (x : ℝ) := haspec x
    have hxM : (x : ℝ) ≤ M := (abs_le.mp (hanorm x)).2
    have hxIcc : (x : ℝ) ∈ Set.Icc (0 : ℝ) M := ⟨hx0, hxM⟩
    have hlt := hp (x : ℝ) hxIcc
    have hidval : jordanSpectrumSqrt a x = Real.sqrt (x : ℝ) := rfl
    rw [hidval]
    exact le_of_lt hlt
  have haapprox : ‖jordanPolyEval a p - jordanCfc a (jordanSpectrumSqrt a)‖ ≤ ε :=
    norm_jordanPolyEval_sub_jordanCfc_le a p _ hεpos.le habound
  have hsqrtdef : jordanCfc a (jordanSpectrumSqrt a) = jordanSqrt a ha := rfl
  rw [hsqrtdef] at haapprox
  -- Combine: `b` and `jordanSqrt a ha` are each within `ε` of the same quantity.
  rw [← halg] at haapprox
  have htri : ‖b - jordanSqrt a ha‖ ≤
      ‖b - jordanPolyEval b q‖ + ‖jordanPolyEval b q - jordanSqrt a ha‖ := by
    have hsplit : b - jordanSqrt a ha =
        (b - jordanPolyEval b q) + (jordanPolyEval b q - jordanSqrt a ha) := by
      abel
    rw [hsplit]
    exact norm_add_le _ _
  have hb' : ‖b - jordanPolyEval b q‖ ≤ ε := by
    rwa [norm_sub_rev] at hbapprox
  have h2 : ‖jordanPolyEval b q - jordanSqrt a ha‖ ≤ ε := haapprox
  have hfinal : δ₀ ≤ ε + ε := hδ₀ ▸ le_trans htri (add_le_add hb' h2)
  rw [hεdef] at hfinal
  linarith

/-- Uniqueness of the positive square root, restated as equality of two arbitrary nonnegative
roots of the same element. -/
theorem eq_of_nonneg_of_mul_self_eq_mul_self [Nontrivial E] [PartialOrder E]
    [IsOrderedAddMonoid E] [IsArchimedeanOrderUnit E] [PosSMulMono ℝ E] [IsJBOrderUnit E]
    {a b c : E} (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hb : b * b = a) (hc : c * c = a) : b = c := by
  have ha : 0 ≤ a := hb ▸ IsJordanOrderUnit.mul_self_nonneg b
  rw [jordanSqrt_eq_of_nonneg_of_mul_self a ha b hb0 hb,
    jordanSqrt_eq_of_nonneg_of_mul_self a ha c hc0 hc]

end NormedJordanAlgebra
