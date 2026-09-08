/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

/-!

# Trace-class operators

For `T : H →L[ℂ] H` on a complex Hilbert space `H`, `|T| := CFC.abs T = √(T⋆T)` (Mathlib's
continuous functional calculus absolute value). `T` is **trace class** if `∑ᵢ ⟪eᵢ, |T| eᵢ⟫`
converges for some Hilbert basis `{eᵢ}`; the **trace norm** `‖T‖₁` is that sum, and the **trace**
`Tr T := ∑ᵢ ⟪eᵢ, T eᵢ⟫` (which converges whenever the trace norm does, via Cauchy–Schwarz). The
Hilbert basis is quantified over `w : Set H` rather than an arbitrary index type `Type*` (matching
Mathlib's own `exists_hilbertBasis`, which produces exactly such a `w`) — every Hilbert space has
a basis indexed this way, so nothing is lost, and it keeps every index type in `H`'s own universe
rather than introducing a genuinely polymorphic (and, for a bare `Prop`-valued `def`, awkward)
universe parameter.

## Relationship to `HilbertSpace/Trace.lean`

`Trace.lean`'s `ContinuousLinearMap.traceₚ` is the ordinary linear-algebra trace
(`LinearMap.trace ℂ H T.toLinearMap`), bundled as a positive linear map: it is defined on *every*
`T : H →L[ℂ] H`, but is only the actual trace when `H` is finite-dimensional (`LinearMap.trace` is
`0` by convention outside that case, via `Module.finrank`-based junk value machinery upstream in
Mathlib — nothing in `traceₚ` needs or uses that convention explicitly). `IsTraceClass`/`trace`
here are the general infinite-dimensional notion: which *bounded* operators have a well-defined
trace via a convergent diagonal sum, before knowing anything about positivity or finite rank.
`trace_eq_sum_inner_hilbertBasis_of_finiteDimensional` below is the connecting fact: in finite
dimension, `LinearMap.trace ℂ H T.toLinearMap` — i.e. `traceₚ T` — agrees with the diagonal sum in
any Hilbert basis, and `HasFiniteMultiplicity.trace_eq_finrank_range_of_finiteDimensional` uses
this explicitly to reduce the finite-dimensional case of the new `trace` to the old one. No general
(infinite-dimensional) theorem "`traceₚ` agrees with `trace` whenever both are defined" is proved
here: `traceₚ` has no trace-class hypothesis to begin with (it is total, using `LinearMap.trace`'s
own junk-value convention outside finite dimension), so such a theorem would need to first isolate
exactly when the *linear-algebra* trace of an infinite-dimensional operator happens to coincide
with its analytic trace-class trace — genuine, unattempted work, not forced here.

Genuinely well-defined trace-class theory needs one famous, hard fact:

> the value of `∑ᵢ ⟪eᵢ, |T| eᵢ⟫` (hence trace-class-ness itself, and the value of the trace) does
> not depend on the choice of Hilbert basis `{eᵢ}`.

The positive/self-adjoint part is proved below (`summable_inner_abs_of_hilbertBasis`) directly
from Mathlib's `HilbertBasis` API — **not** via the unbounded spectral theorem. The route is the
standard Hilbert–Schmidt double-sum/Fubini argument: for a self-adjoint `S`, write
`⟪eᵢ, S eᵢ⟫ = ‖√S eᵢ‖²` (continuous functional calculus square root), expand `‖√S eᵢ‖²` via
Parseval against a *second* basis `{fⱼ}`, and swap the resulting (unconditionally
Fubini-swappable, since all terms are nonnegative and the outer sum is controlled by the
trace-class hypothesis) double sum `∑ᵢ∑ⱼ = ∑ⱼ∑ᵢ`. `|T| = CFC.abs T` is always self-adjoint, so
this handles `summable_inner_abs_of_hilbertBasis` in full generality. For `trace_eq_of_hilbertBasis`
the positive case is now proved by the same square-root/Parseval argument
(`trace_eq_of_hilbertBasis_of_nonneg`), and the self-adjoint case is obtained by decomposing into
positive and negative parts (`trace_eq_of_hilbertBasis_of_isSelfAdjoint`). The general
non-self-adjoint case would go through
the polar decomposition `T = U|T|` instead, and packaging the trace-class operators themselves as
a Banach space `TraceClass H` is separate, genuinely harder work; neither is attempted here.

## Definitions

- `IsTraceClass` : `T` is trace class.
- `traceNorm`/`trace` : witness-basis definitions of the trace norm and trace.
- `HasFiniteMultiplicity` : a projection is trace class — the honest Murray–von Neumann finiteness
  condition for "isolated eigenvalue of finite multiplicity", which a purely topological account of
  discrete spectrum cannot express.

-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Trace class -/

/-- **`T` is trace class**: `∑ᵢ ⟪eᵢ, |T| eᵢ⟫` converges for some Hilbert basis `{eᵢ}` of `H`
(`|T| := CFC.abs T`, Mathlib's continuous functional calculus absolute value `√(T⋆T)`). By the
basis-independence theorem below, "some" is equivalent to "every". -/
def IsTraceClass (T : H →L[ℂ] H) : Prop :=
  ∃ (w : Set H) (b : HilbertBasis w ℂ H), Summable (fun i => (⟪b i, CFC.abs T (b i)⟫_ℂ).re)

/-! ### Basis-independence machinery

The two lemmas below are the honest analytic content: they need only completeness of `H`, the
continuous functional calculus square root, and Mathlib's `HilbertBasis` Parseval API
(`HilbertBasis.hasSum_inner_mul_inner`). No spectral theorem is used. -/

omit [CompleteSpace H] in
/-- **Parseval's identity**, in the form needed below: for a Hilbert basis `{eᵢ}` and any vector
`y`, `∑ᵢ |⟪eᵢ, y⟫|² = ‖y‖²`, unconditionally (`HasSum`, not merely `tsum`). -/
@[nolint unusedArguments]
private lemma hasSum_norm_sq_inner_basis {w : Set H} (b : HilbertBasis w ℂ H) (y : H) :
    HasSum (fun i : w => ‖⟪b i, y⟫_ℂ‖ ^ 2) (‖y‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner y y
  have hpt : ∀ i : w, ⟪y, b i⟫_ℂ * ⟪b i, y⟫_ℂ = ((‖⟪b i, y⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [← inner_conj_symm y (b i), RCLike.conj_mul]
    norm_cast
  have hval : ⟪y, y⟫_ℂ = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  simp_rw [hpt] at h
  rw [hval] at h
  exact Complex.hasSum_ofReal.mp h

/-- **Basis-independence of `∑ᵢ ‖S eᵢ‖²` for self-adjoint `S`.** This is the Hilbert–Schmidt
double-sum argument: expand `‖S bᵢ‖²` via Parseval against the *second* basis `c`, swap the
(nonnegative, hence unconditionally Fubini-swappable once the outer sum is known finite via `hb`)
double sum, and collapse the inner sum back via Parseval against `b`, using `S` self-adjoint to
turn the adjoint that appears back into `S` itself. -/
private lemma hasSum_norm_sq_apply_of_selfAdjoint {S : H →L[ℂ] H} (hS : IsSelfAdjoint S)
    {w w' : Set H} (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H)
    (hb : Summable (fun i : w => ‖S (b i)‖ ^ 2)) :
    HasSum (fun j : w' => ‖S (c j)‖ ^ 2) (∑' i : w, ‖S (b i)‖ ^ 2) := by
  classical
  set F : w → w' → ℝ := fun i j => ‖⟪c j, S (b i)⟫_ℂ‖ ^ 2 with hFdef
  have hFnonneg : 0 ≤ Function.uncurry F := fun _ => sq_nonneg _
  have hrow : ∀ i : w, HasSum (F i) (‖S (b i)‖ ^ 2) := fun i =>
    hasSum_norm_sq_inner_basis c (S (b i))
  have hSstar : ContinuousLinearMap.adjoint S = S := (ContinuousLinearMap.star_eq_adjoint
      S).symm.trans hS
  have hcol : ∀ j : w', HasSum (fun i : w => F i j) (‖S (c j)‖ ^ 2) := by
    intro j
    have e1 : ∀ i : w, ⟪c j, S (b i)⟫_ℂ = ⟪S (c j), b i⟫_ℂ := fun i => by
      have h1 := ContinuousLinearMap.adjoint_inner_left S (b i) (c j)
      rw [hSstar] at h1
      exact h1.symm
    have key : (fun i : w => F i j) = fun i : w => ‖⟪b i, S (c j)⟫_ℂ‖ ^ 2 := by
      funext i
      show ‖⟪c j, S (b i)⟫_ℂ‖ ^ 2 = _
      rw [e1 i, ← inner_conj_symm (b i) (S (c j)), RCLike.norm_conj]
    rw [key]
    exact hasSum_norm_sq_inner_basis b (S (c j))
  set G : w' → w → ℝ := fun j i => F i j with hGdef
  have hjoint : Summable (Function.uncurry F) := by
    rw [summable_prod_of_nonneg hFnonneg]
    refine ⟨fun i => (hrow i).summable, ?_⟩
    have heq : (fun i : w => ∑' j : w', F i j) = fun i : w => ‖S (b i)‖ ^ 2 :=
      funext fun i => (hrow i).tsum_eq
    show Summable fun i : w => ∑' j : w', F i j
    rwa [heq]
  have hswap := hjoint.tsum_comm' (fun i => (hrow i).summable) (fun j => (hcol j).summable)
  have hLHS : ∑' j : w', ∑' i : w, F i j = ∑' j : w', ‖S (c j)‖ ^ 2 :=
    tsum_congr fun j => (hcol j).tsum_eq
  have hRHS : ∑' i : w, ∑' j : w', F i j = ∑' i : w, ‖S (b i)‖ ^ 2 :=
    tsum_congr fun i => (hrow i).tsum_eq
  have hEq : ∑' j : w', ‖S (c j)‖ ^ 2 = ∑' i : w, ‖S (b i)‖ ^ 2 := by
    rw [← hLHS, ← hRHS]; exact hswap
  have hGnonneg : 0 ≤ Function.uncurry G := fun _ => sq_nonneg _
  have hjointG : Summable (Function.uncurry G) := by
    have hcomp : Function.uncurry G = Function.uncurry F ∘ (Equiv.prodComm w' w) := by
      funext p
      simp [Function.uncurry, hGdef, Equiv.prodComm]
    rw [hcomp]
    exact (Equiv.prodComm w' w).summable_iff.mpr hjoint
  have hcolSummable : Summable (fun j : w' => ‖S (c j)‖ ^ 2) := by
    have hpair := (summable_prod_of_nonneg hGnonneg).mp hjointG
    have h2 : Summable fun j : w' => ∑' i : w, G j i := by
      show Summable fun j : w' => ∑' i : w, Function.uncurry G (j, i)
      exact hpair.2
    have heq2 : (fun j : w' => ∑' i : w, G j i) = fun j : w' => ‖S (c j)‖ ^ 2 :=
      funext fun j => (hcol j).tsum_eq
    rwa [heq2] at h2
  rw [← hEq]
  exact hcolSummable.hasSum

/-- **Basis independence of trace-class-ness and the trace norm.** `|T| = CFC.abs T` is always
self-adjoint (`abs_nonneg` + `IsSelfAdjoint.of_nonneg`), so writing
`⟪eᵢ, |T| eᵢ⟫ = ‖√|T| eᵢ‖²` (`CFC.sqrt`, self-adjoint) reduces this directly to
`hasSum_norm_sq_apply_of_selfAdjoint`. -/
theorem summable_inner_abs_of_hilbertBasis {T : H →L[ℂ] H} (h : IsTraceClass T) {w : Set H}
    (b : HilbertBasis w ℂ H) :
    Summable (fun i => (⟪b i, CFC.abs T (b i)⟫_ℂ).re) := by
  obtain ⟨w₀, b₀, hb₀⟩ := h
  set A : H →L[ℂ] H := CFC.abs T with hAdef
  have hAnonneg : 0 ≤ A := CFC.abs_nonneg T
  have hAself : IsSelfAdjoint A := .of_nonneg hAnonneg
  set S : H →L[ℂ] H := CFC.sqrt A with hSdef
  have hSself : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg A)
  have hpt : ∀ {w' : Set H} (b' : HilbertBasis w' ℂ H) (i : w'),
      (⟪b' i, A (b' i)⟫_ℂ).re = ‖S (b' i)‖ ^ 2 := by
    intro w' b' i
    have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hAnonneg
    have : ⟪b' i, A (b' i)⟫_ℂ = ⟪S (b' i), S (b' i)⟫_ℂ := by
      have hSstar : ContinuousLinearMap.adjoint S = S := (ContinuousLinearMap.star_eq_adjoint
          S).symm.trans hSself
      rw [← hSS]
      show ⟪b' i, (S * S) (b' i)⟫_ℂ = _
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [← ContinuousLinearMap.adjoint_inner_left S (S (b' i)) (b' i), hSstar]
    have hval : ⟪S (b' i), S (b' i)⟫_ℂ = ((‖S (b' i)‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [this, hval, Complex.ofReal_re]
  have hb₀' : Summable (fun i : w₀ => ‖S (b₀ i)‖ ^ 2) := by
    simpa [hpt b₀] using hb₀
  have := hasSum_norm_sq_apply_of_selfAdjoint hSself b₀ b hb₀'
  simpa [hpt b] using this.summable

/-- The existential definition of trace class is equivalent to summability in every Hilbert
basis.  The forward implication is the basis-independence theorem above; the reverse implication
only needs one basis, whose existence is available for every complete Hilbert space.  This is the
form that downstream constructions should normally consume, since it avoids carrying the
particular witness selected by `IsTraceClass`. -/
theorem isTraceClass_iff {T : H →L[ℂ] H} :
    IsTraceClass T ↔
      ∀ (w : Set H) (b : HilbertBasis w ℂ H),
        Summable (fun i => (⟪b i, CFC.abs T (b i)⟫_ℂ).re) := by
  constructor
  · intro h w b
    exact summable_inner_abs_of_hilbertBasis h b
  · intro h
    obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
    exact ⟨w, b, h w b⟩

/-- Every bounded operator on a finite-dimensional Hilbert space is trace class.  The proof is
deliberately basis-level: a Hilbert basis exists, its carrier is finite by finite-dimensionality,
and the defining nonnegative series therefore has finite support.  This is the concrete
 finite-dimensional realization used by the corresponding `WStarAlgebra` instance. -/
theorem isTraceClass_of_finiteDimensional [FiniteDimensional ℂ H] (T : H →L[ℂ] H) :
    IsTraceClass T := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  let : Finite w := b.orthonormal.linearIndependent.finite
  let : Fintype w := Fintype.ofFinite w
  refine ⟨w, b, ?_⟩
  apply summable_of_hasFiniteSupport
  exact Set.finite_univ.subset (by intro i hi; trivial)

omit [CompleteSpace H] in
/-- The ordinary finite-dimensional trace is the diagonal sum in any Hilbert basis. -/
@[nolint unusedArguments]
theorem trace_eq_sum_inner_hilbertBasis_of_finiteDimensional
    [FiniteDimensional ℂ H] (T : H →L[ℂ] H) {w : Set H} (b : HilbertBasis w ℂ H) :
    LinearMap.trace ℂ H T.toLinearMap = ∑' i : w, ⟪b i, T (b i)⟫_ℂ := by
  let : Finite w := b.orthonormal.linearIndependent.finite
  let : Fintype w := Fintype.ofFinite w
  rw [tsum_fintype]
  simpa only [HilbertBasis.coe_toOrthonormalBasis, ContinuousLinearMap.coe_coe] using
    LinearMap.trace_eq_sum_inner T.toLinearMap b.toOrthonormalBasis

/-- The trace norm `‖T‖₁ := ∑ᵢ ⟪eᵢ, |T| eᵢ⟫`, computed via a chosen witness Hilbert basis (any
basis gives the same value, by `summable_inner_abs_of_hilbertBasis` — this definition just needs
*a* witness to compute with). -/
def traceNorm (T : H →L[ℂ] H) (h : IsTraceClass T) : ℝ :=
  ∑' i : h.choose, (⟪h.choose_spec.choose i, CFC.abs T (h.choose_spec.choose i)⟫_ℂ).re

/-- The witness proof argument of `traceNorm` is immaterial.  This small lemma is useful when
transporting a trace-class operator through a construction that produces a new proof of the same
proposition. -/
theorem traceNorm_congr {T : H →L[ℂ] H} {h₁ h₂ : IsTraceClass T} :
    traceNorm T h₁ = traceNorm T h₂ := by
  have hh : h₁ = h₂ := Subsingleton.elim _ _
  rw [hh]

/-- **The trace**, `Tr T := ∑ᵢ ⟪eᵢ, T eᵢ⟫`, for a trace-class `T`, computed via the same witness
basis as `traceNorm`. `tsum` is total (it evaluates to `0` on a non-summable family), so this
definition needs no convergence proof up front; the honest mathematical content — that the family
`i ↦ ⟪eᵢ, T eᵢ⟫` is *actually* summable for trace-class `T` (a standard Cauchy–Schwarz consequence
of `IsTraceClass`, via the sharp bound `∑ᵢ |⟪eᵢ, T eᵢ⟫| ≤ ∑ᵢ ⟪eᵢ, |T| eᵢ⟫` from the polar
decomposition `T = U|T|`), together with basis-independence, is left to the later trace-class
Banach space phase; the self-adjoint case is handled directly below without polar decomposition. -/
def trace (T : H →L[ℂ] H) (h : IsTraceClass T) : ℂ :=
  ∑' i : h.choose, ⟪h.choose_spec.choose i, T (h.choose_spec.choose i)⟫_ℂ

/-- The trace norm is independent of the witness basis used in `IsTraceClass`.  This is the
strong form of `summable_inner_abs_of_hilbertBasis`: the square-root/Parseval argument identifies
the actual sums, not merely their convergence. -/
theorem traceNorm_eq_of_hilbertBasis {T : H →L[ℂ] H} (h : IsTraceClass T) {w : Set H}
    (b : HilbertBasis w ℂ H) :
    traceNorm T h = ∑' i, (⟪b i, CFC.abs T (b i)⟫_ℂ).re := by
  let w₀ : Set H := h.choose
  let b₀ : HilbertBasis w₀ ℂ H := h.choose_spec.choose
  have hb₀ : Summable (fun i : w₀ => (⟪b₀ i, CFC.abs T (b₀ i)⟫_ℂ).re) :=
    h.choose_spec.choose_spec
  set A : H →L[ℂ] H := CFC.abs T with hAdef
  have hAnonneg : 0 ≤ A := CFC.abs_nonneg T
  have hAself : IsSelfAdjoint A := .of_nonneg hAnonneg
  set S : H →L[ℂ] H := CFC.sqrt A with hSdef
  have hSself : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg A)
  have hpt : ∀ {w' : Set H} (b' : HilbertBasis w' ℂ H) (i : w'),
      (⟪b' i, A (b' i)⟫_ℂ).re = ‖S (b' i)‖ ^ 2 := by
    intro w' b' i
    have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hAnonneg
    have hinner : ⟪b' i, A (b' i)⟫_ℂ = ⟪S (b' i), S (b' i)⟫_ℂ := by
      have hSstar : ContinuousLinearMap.adjoint S = S :=
        (ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself
      rw [← hSS]
      show ⟪b' i, (S * S) (b' i)⟫_ℂ = _
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [← ContinuousLinearMap.adjoint_inner_left S (S (b' i)) (b' i), hSstar]
    rw [hinner, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hb₀' : Summable (fun i : w₀ => ‖S (b₀ i)‖ ^ 2) := by
    apply hb₀.congr
    intro i
    rw [hAdef, hpt]
  have hnorm := hasSum_norm_sq_apply_of_selfAdjoint hSself b₀ b hb₀'
  calc
    traceNorm T h = ∑' i : w₀, (⟪b₀ i, A (b₀ i)⟫_ℂ).re := by
      rfl
    _ = ∑' i : w₀, ‖S (b₀ i)‖ ^ 2 := by
      apply tsum_congr
      intro i
      exact hpt b₀ i
    _ = ∑' i : w, ‖S (b i)‖ ^ 2 := hnorm.tsum_eq.symm
    _ = ∑' i : w, (⟪b i, A (b i)⟫_ℂ).re := by
      apply tsum_congr
      intro i
      exact (hpt b i).symm
    _ = ∑' i, (⟪b i, CFC.abs T (b i)⟫_ℂ).re := by
      rfl

omit [CompleteSpace H] in
private lemma real_inner_nonneg_of_nonneg {T : H →L[ℂ] H} (hT : 0 ≤ T) (x : H) :
    0 ≤ (⟪x, T x⟫_ℂ).re := by
  have hpos : T.IsPositive := T.nonneg_iff_isPositive.mp hT
  have hx := (ContinuousLinearMap.isPositive_iff_complex T).mp hpos x
  have heq : (⟪T x, x⟫_ℂ).re = (⟪x, T x⟫_ℂ).re := by
    rw [← inner_conj_symm (T x) x]
    exact Complex.conj_re _
  rw [← heq]
  exact hx.2

/-- The trace norm is nonnegative.  This is exposed separately from its basis-independence result
so norm estimates can use it without unpacking the chosen Hilbert-basis witness. -/
theorem traceNorm_nonneg (T : H →L[ℂ] H) (h : IsTraceClass T) : 0 ≤ traceNorm T h := by
  unfold traceNorm
  exact tsum_nonneg fun i => real_inner_nonneg_of_nonneg (CFC.abs_nonneg T)
    (h.choose_spec.choose i)

private lemma real_inner_mono_of_le {P Q : H →L[ℂ] H} (hPQ : P ≤ Q) (x : H) :
    (⟪x, P x⟫_ℂ).re ≤ (⟪x, Q x⟫_ℂ).re := by
  have hdiff : 0 ≤ Q - P := sub_nonneg.mpr hPQ
  have hpos : (Q - P).IsPositive := (Q - P).nonneg_iff_isPositive.mp hdiff
  have hx := (ContinuousLinearMap.isPositive_iff_complex (Q - P)).mp hpos x
  have heq : (⟪(Q - P) x, x⟫_ℂ).re = (⟪x, (Q - P) x⟫_ℂ).re := by
    rw [← inner_conj_symm ((Q - P) x) x]
    exact Complex.conj_re _
  have hx' : 0 ≤ (⟪x, (Q - P) x⟫_ℂ).re := by
    rw [← heq]
    exact hx.2
  simpa [sub_apply, inner_sub_right, map_sub] using hx'

private lemma isTraceClass_posPart_of_isSelfAdjoint {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    (h : IsTraceClass T) : IsTraceClass T⁺ := by
  obtain ⟨w, b, hb⟩ := h
  refine ⟨w, b, ?_⟩
  rw [CFC.abs_of_nonneg T⁺ (CFC.posPart_nonneg T)]
  apply Summable.of_nonneg_of_le
  · intro i
    exact real_inner_nonneg_of_nonneg (CFC.posPart_nonneg T) (b i)
  · intro i
    have habs : T⁺ + T⁻ = CFC.abs T := CFC.posPart_add_negPart T hT
    have hle : T⁺ ≤ CFC.abs T := by
      rw [← habs]
      exact le_add_of_nonneg_right (CFC.negPart_nonneg T)
    exact real_inner_mono_of_le hle (b i)
  · exact hb

private lemma isTraceClass_negPart_of_isSelfAdjoint {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    (h : IsTraceClass T) : IsTraceClass T⁻ := by
  obtain ⟨w, b, hb⟩ := h
  refine ⟨w, b, ?_⟩
  rw [CFC.abs_of_nonneg T⁻ (CFC.negPart_nonneg T)]
  apply Summable.of_nonneg_of_le
  · intro i
    exact real_inner_nonneg_of_nonneg (CFC.negPart_nonneg T) (b i)
  · intro i
    have habs : T⁺ + T⁻ = CFC.abs T := CFC.posPart_add_negPart T hT
    have hle : T⁻ ≤ CFC.abs T := by
      rw [← habs]
      exact le_add_of_nonneg_left (CFC.posPart_nonneg T)
    exact real_inner_mono_of_le hle (b i)
  · exact hb

private lemma summable_inner_of_nonneg {T : H →L[ℂ] H} (hT : 0 ≤ T) (h : IsTraceClass T)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    Summable (fun i => ⟪b i, T (b i)⟫_ℂ) := by
  have hr : Summable (fun i : w => (⟪b i, CFC.abs T (b i)⟫_ℂ).re) :=
    summable_inner_abs_of_hilbertBasis h b
  have habs : CFC.abs T = T := CFC.abs_of_nonneg T hT
  have heq (i : w) : ⟪b i, T (b i)⟫_ℂ =
      ((⟪b i, CFC.abs T (b i)⟫_ℂ).re : ℂ) := by
    rw [habs]
    have hpos : T.IsPositive := T.nonneg_iff_isPositive.mp hT
    have hx := (ContinuousLinearMap.isPositive_iff_complex T).mp hpos (b i)
    have hA : ⟪T (b i), b i⟫_ℂ = ((⟪T (b i), b i⟫_ℂ).re : ℂ) := hx.1.symm
    have hre : (⟪T (b i), b i⟫_ℂ).re = (⟪b i, T (b i)⟫_ℂ).re := by
      rw [← inner_conj_symm (T (b i)) (b i)]
      exact Complex.conj_re _
    have hinner : ⟪b i, T (b i)⟫_ℂ = ((⟪T (b i), b i⟫_ℂ).re : ℂ) := by
      calc
        ⟪b i, T (b i)⟫_ℂ = (starRingEnd ℂ) ⟪T (b i), b i⟫_ℂ :=
          (inner_conj_symm (b i) (T (b i))).symm
        _ = (starRingEnd ℂ) ((⟪T (b i), b i⟫_ℂ).re : ℂ) :=
          congrArg (starRingEnd ℂ) hA
        _ = ((⟪T (b i), b i⟫_ℂ).re : ℂ) := by simp
    exact hinner.trans (congrArg (fun r : ℝ => (r : ℂ)) hre)
  have hs : Summable (fun i : w => ((⟪b i, CFC.abs T (b i)⟫_ℂ).re : ℂ)) :=
    Complex.summable_ofReal.mpr hr
  exact hs.congr (fun i => (heq i).symm)

/-!
Basis-independent trace for positive trace-class operators.

For a positive operator the absolute value is the operator itself.  Taking its continuous-
functional-calculus square root turns every diagonal coefficient into a squared norm, so the
Parseval double-sum theorem already proved above gives the same sum in every Hilbert basis.  This
is the positive case needed by density operators and does not use polar decomposition.
-/
theorem trace_eq_of_hilbertBasis_of_nonneg {T : H →L[ℂ] H} (hT : 0 ≤ T)
    (h : IsTraceClass T) {w : Set H} (b : HilbertBasis w ℂ H) :
    trace T h = ∑' i, ⟪b i, T (b i)⟫_ℂ := by
  let S : H →L[ℂ] H := CFC.sqrt T
  have hSself : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg T)
  have hSS : S * S = T := CFC.sqrt_mul_sqrt_self T hT
  have hdiag : ∀ {w' : Set H} (b' : HilbertBasis w' ℂ H) (i : w'),
      ⟪b' i, T (b' i)⟫_ℂ = ((‖S (b' i)‖ ^ 2 : ℝ) : ℂ) := by
    intro w' b' i
    have hSstar : ContinuousLinearMap.adjoint S = S :=
      (ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself
    have hinner : ⟪b' i, T (b' i)⟫_ℂ = ⟪S (b' i), S (b' i)⟫_ℂ := by
      rw [← hSS]
      show ⟪b' i, (S * S) (b' i)⟫_ℂ = _
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [← ContinuousLinearMap.adjoint_inner_left S (S (b' i)) (b' i), hSstar]
    rw [hinner, inner_self_eq_norm_sq_to_K]
    norm_cast
  let w₀ : Set H := h.choose
  let b₀ : HilbertBasis w₀ ℂ H := h.choose_spec.choose
  have hWdiag : Summable (fun i : w₀ => ‖S (b₀ i)‖ ^ 2) := by
    have hbase : Summable (fun i : w₀ =>
        (⟪b₀ i, CFC.abs T (b₀ i)⟫_ℂ).re) := h.choose_spec.choose_spec
    have habs : CFC.abs T = T := CFC.abs_of_nonneg T hT
    apply hbase.congr
    intro i
    rw [habs, hdiag b₀ i]
    rfl
  have hnorm := hasSum_norm_sq_apply_of_selfAdjoint hSself b₀ b hWdiag
  calc
    trace T h = ∑' i : w₀, ⟪b₀ i, T (b₀ i)⟫_ℂ := by
      rfl
    _ = ∑' i : w₀, ((‖S (b₀ i)‖ ^ 2 : ℝ) : ℂ) := by
      apply tsum_congr
      intro i
      exact hdiag b₀ i
    _ = ((∑' i : w₀, ‖S (b₀ i)‖ ^ 2 : ℝ) : ℂ) :=
      (Complex.ofReal_tsum (fun i : w₀ => ‖S (b₀ i)‖ ^ 2)).symm
    _ = ((∑' i : w, ‖S (b i)‖ ^ 2 : ℝ) : ℂ) := by
      rw [hnorm.tsum_eq]
    _ = ∑' i : w, ⟪b i, T (b i)⟫_ℂ := by
      rw [Complex.ofReal_tsum]
      apply tsum_congr
      intro i
      exact (hdiag b i).symm

/-- Basis-independent trace for self-adjoint trace-class operators.  The proof reduces to the
positive theorem through the continuous-functional-calculus decomposition `T = T⁺ - T⁻`; no
polar decomposition is needed for this self-adjoint case. -/
theorem trace_eq_of_hilbertBasis_of_isSelfAdjoint {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    (h : IsTraceClass T) {w : Set H} (b : HilbertBasis w ℂ H) :
    trace T h = ∑' i, ⟪b i, T (b i)⟫_ℂ := by
  let P : H →L[ℂ] H := T⁺
  let N : H →L[ℂ] H := T⁻
  have hP : IsTraceClass P := isTraceClass_posPart_of_isSelfAdjoint hT h
  have hN : IsTraceClass N := isTraceClass_negPart_of_isSelfAdjoint hT h
  have hPnonneg : 0 ≤ P := CFC.posPart_nonneg T
  have hNnonneg : 0 ≤ N := CFC.negPart_nonneg T
  have hdecomp : P - N = T := CFC.posPart_sub_negPart T hT
  have hPsum : Summable (fun i : w => ⟪b i, P (b i)⟫_ℂ) :=
    summable_inner_of_nonneg hPnonneg hP b
  have hNsum : Summable (fun i : w => ⟪b i, N (b i)⟫_ℂ) :=
    summable_inner_of_nonneg hNnonneg hN b
  let w₀ : Set H := h.choose
  let b₀ : HilbertBasis w₀ ℂ H := h.choose_spec.choose
  have hPsum₀ : Summable (fun i : w₀ => ⟪b₀ i, P (b₀ i)⟫_ℂ) :=
    summable_inner_of_nonneg hPnonneg hP b₀
  have hNsum₀ : Summable (fun i : w₀ => ⟪b₀ i, N (b₀ i)⟫_ℂ) :=
    summable_inner_of_nonneg hNnonneg hN b₀
  have htrace_sub : trace T h = trace P hP - trace N hN := by
    calc
      trace T h = ∑' i : w₀, ⟪b₀ i, T (b₀ i)⟫_ℂ := by rfl
      _ = ∑' i : w₀, (⟪b₀ i, P (b₀ i)⟫_ℂ - ⟪b₀ i, N (b₀ i)⟫_ℂ) := by
        apply tsum_congr
        intro i
        rw [← hdecomp]
        simp [sub_apply, inner_sub_right]
      _ = (∑' i : w₀, ⟪b₀ i, P (b₀ i)⟫_ℂ) -
          (∑' i : w₀, ⟪b₀ i, N (b₀ i)⟫_ℂ) := hPsum₀.tsum_sub hNsum₀
      _ = trace P hP - trace N hN := by
        rw [trace_eq_of_hilbertBasis_of_nonneg hPnonneg hP b₀,
          trace_eq_of_hilbertBasis_of_nonneg hNnonneg hN b₀]
  calc
    trace T h = trace P hP - trace N hN := htrace_sub
    _ = (∑' i : w, ⟪b i, P (b i)⟫_ℂ) -
        (∑' i : w, ⟪b i, N (b i)⟫_ℂ) := by
      rw [trace_eq_of_hilbertBasis_of_nonneg hPnonneg hP b,
        trace_eq_of_hilbertBasis_of_nonneg hNnonneg hN b]
    _ = ∑' i : w, (⟪b i, P (b i)⟫_ℂ - ⟪b i, N (b i)⟫_ℂ) :=
      (hPsum.tsum_sub hNsum).symm
    _ = ∑' i : w, ⟪b i, T (b i)⟫_ℂ := by
      apply tsum_congr
      intro i
      rw [← hdecomp]
      simp [sub_apply, inner_sub_right]

/-! ## Honest finite multiplicity -/

/-- **The honest Murray–von Neumann finiteness condition**: a self-adjoint projection
`p : H →L[ℂ] H` has finite multiplicity iff it is trace class (equivalently, since a projection's
eigenvalues are `0`/`1`, iff its range is finite-dimensional). -/
def HasFiniteMultiplicity (p : H →L[ℂ] H) : Prop := IsStarProjection p ∧ IsTraceClass p

/-- A trace-class star projection has finite-dimensional range.  The proof uses the Hilbert basis
of the range and extends it to a Hilbert basis of `H`: on every range basis vector the projection
has diagonal coefficient `1`, so summability of the trace-class diagonal forces the range basis to
have a finite index type. -/
theorem HasFiniteMultiplicity.finiteDimensional_range {p : H →L[ℂ] H}
    (hp : HasFiniteMultiplicity p) :
    FiniteDimensional ℂ (LinearMap.range p.toLinearMap) := by
  let W : Submodule ℂ H := LinearMap.range p.toLinearMap
  have hpIdem : IsIdempotentElem p.toLinearMap :=
    (ContinuousLinearMap.isIdempotentElem_toLinearMap_iff).2 hp.1.isIdempotentElem
  let : CompleteSpace W := by
    change CompleteSpace p.range
    exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range
      hp.1.isIdempotentElem).completeSpace_coe
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ W
  have hbOrtho : Orthonormal ℂ (fun i : w => (b i : H)) := by
    exact b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  have hbInjective : Function.Injective (fun i : w => (b i : H)) :=
    hbOrtho.linearIndependent.injective
  let s : Set H := Set.range (fun i : w => (b i : H))
  have hsOrtho : Orthonormal ℂ ((↑) : s → H) := hbOrtho.toSubtypeRange
  obtain ⟨wH, bH, hsH, hbH⟩ := hsOrtho.exists_hilbertBasis_extension
  have hdiag : Summable (fun i : wH =>
      (⟪bH i, CFC.abs p (bH i)⟫_ℂ).re) :=
    summable_inner_abs_of_hilbertBasis hp.2 bH
  have habs : CFC.abs p = p := CFC.abs_of_nonneg p hp.1.nonneg
  let g : w → wH := fun i =>
    ⟨(b i : H), hsH (show (b i : H) ∈ s from ⟨i, rfl⟩)⟩
  have hgInjective : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun k : w => (k : W))
      (hbInjective (congrArg (fun z : wH => (z : H)) hij))
  have hconst : Summable (fun _ : w => (1 : ℝ)) := by
    have hcomp := hdiag.comp_injective hgInjective
    apply hcomp.congr
    intro i
    change (⟪bH (g i), CFC.abs p (bH (g i))⟫_ℂ).re = 1
    have hbi : bH (g i) = (b i : H) := by
      rw [hbH]
    rw [hbi, habs]
    have hfix : p (b i : H) = (b i : H) := by
      exact (LinearMap.IsIdempotentElem.mem_range_iff hpIdem).mp (b i).property
    rw [hfix]
    have hnorm : ‖(b i : H)‖ = 1 := by
      simpa using hbOrtho.1 i
    rw [show ⟪(b i : H), (b i : H)⟫_ℂ =
        ((‖(b i : H)‖ ^ 2 : ℝ) : ℂ) by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast]
    simp [hnorm]
  let : Finite w := Finite.of_summable_const zero_lt_one hconst
  let : Fintype w := Fintype.ofFinite w
  change FiniteDimensional ℂ W
  exact b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- A finite-multiplicity projection has the expected trace.  The basis calculation is finite-rank:
extend an orthonormal basis of the range to one of `H`; the projection vanishes on the complementary
basis vectors and is the identity on the range basis. -/
theorem HasFiniteMultiplicity.trace_eq_finrank_range
    {p : H →L[ℂ] H} (hp : HasFiniteMultiplicity p) :
    trace p hp.2 = (Module.finrank ℂ (LinearMap.range p.toLinearMap) : ℂ) := by
  have hp' : IsStarProjection p ∧ IsTraceClass p := hp
  let W : Submodule ℂ H := LinearMap.range p.toLinearMap
  let : FiniteDimensional ℂ W := by
    change FiniteDimensional ℂ (LinearMap.range p.toLinearMap)
    exact hp.finiteDimensional_range
  have hpIdem : IsIdempotentElem p.toLinearMap :=
    (ContinuousLinearMap.isIdempotentElem_toLinearMap_iff).2 hp.1.isIdempotentElem
  have hpAdj : ContinuousLinearMap.adjoint p = p := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hp.1.isSelfAdjoint
  let : CompleteSpace W := by
    change CompleteSpace p.range
    exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range
      hp.1.isIdempotentElem).completeSpace_coe
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ W
  let : Finite w := b.orthonormal.linearIndependent.finite
  let : Fintype w := Fintype.ofFinite w
  have hbOrtho : Orthonormal ℂ (fun i : w => (b i : H)) := by
    exact b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  have hbInjective : Function.Injective (fun i : w => (b i : H)) :=
    hbOrtho.linearIndependent.injective
  let s : Set H := Set.range (fun i : w => (b i : H))
  have hsOrtho : Orthonormal ℂ ((↑) : s → H) := hbOrtho.toSubtypeRange
  obtain ⟨wH, bH, hsH, hbH⟩ := hsOrtho.exists_hilbertBasis_extension
  let g : w → wH := fun i =>
    ⟨(b i : H), hsH (show (b i : H) ∈ s from ⟨i, rfl⟩)⟩
  have hgInjective : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun k : w => (k : W))
      (hbInjective (congrArg (fun z : wH => (z : H)) hij))
  have hbi (i : w) : bH (g i) = (b i : H) := by
    rw [hbH]
  have hfix (i : w) : p (b i : H) = (b i : H) := by
    exact (LinearMap.IsIdempotentElem.mem_range_iff hpIdem).mp (b i).property
  let f : wH → ℝ := fun j => (⟪bH j, CFC.abs p (bH j)⟫_ℂ).re
  have hdiag : Summable f := summable_inner_abs_of_hilbertBasis hp.2 bH
  have habs : CFC.abs p = p := CFC.abs_of_nonneg p hp.1.nonneg
  have hpdiag (x : H) : ⟪x, p x⟫_ℂ = ((‖p x‖ ^ 2 : ℝ) : ℂ) := by
    have hpp : p (p x) = p x := by
      have h := congrArg (fun q : H →L[ℂ] H => q x) hp.1.isIdempotentElem
      simpa [ContinuousLinearMap.mul_def] using h
    have h := ContinuousLinearMap.adjoint_inner_left p (p x) x
    rw [hpAdj, hpp] at h
    rw [← h]
    simp
  let w₀ : Set H := hp.2.choose
  let b₀ : HilbertBasis w₀ ℂ H := hp.2.choose_spec.choose
  have hWdiagBase : Summable (fun i : w₀ =>
      (⟪b₀ i, CFC.abs p (b₀ i)⟫_ℂ).re) := hp.2.choose_spec.choose_spec
  have hWdiag : Summable (fun i : w₀ => ‖p (b₀ i)‖ ^ 2) := by
    apply hWdiagBase.congr
    intro i
    rw [habs, hpdiag]
    rfl
  have hdiagC : Summable (fun j : wH => ⟪bH j, p (bH j)⟫_ℂ) := by
    have hreal : Summable (fun j : wH =>
        ((f j : ℝ) : ℂ)) := Complex.summable_ofReal.mpr hdiag
    apply hreal.congr
    intro j
    dsimp [f]
    rw [habs, hpdiag]
    change ((‖p (bH j)‖ ^ 2 : ℝ) : ℂ) = ((‖p (bH j)‖ ^ 2 : ℝ) : ℂ)
    rfl
  have hzero_of_not_mem_range (j : wH) (hj : j ∉ Set.range g) :
      p (bH j) = 0 := by
    have hjS : bH j ∉ s := by
      intro hjs
      rcases hjs with ⟨i, hi⟩
      apply hj
      refine ⟨i, Subtype.ext ?_⟩
      dsimp [g]
      simpa [hbH] using hi
    let y : W := ⟨p (bH j), LinearMap.mem_range_self p.toLinearMap (bH j)⟩
    have hyinner (i : w) : ⟪y, b i⟫_ℂ = 0 := by
      change ⟪p (bH j), (b i : H)⟫_ℂ = 0
      have horth : ⟪(bH j : H), (b i : H)⟫_ℂ = 0 := by
        have hne : j ≠ g i := by
          intro hij
          apply hj
          exact ⟨i, hij.symm⟩
        have h := bH.orthonormal.2 hne
        simpa [hbi i] using h
      have h := ContinuousLinearMap.adjoint_inner_right p (bH j) (b i : H)
      calc
        ⟪p (bH j), (b i : H)⟫_ℂ =
            ⟪(bH j : H), ContinuousLinearMap.adjoint p (b i : H)⟫_ℂ := h.symm
        _ = ⟪(bH j : H), p (b i : H)⟫_ℂ := by rw [hpAdj]
        _ = ⟪(bH j : H), (b i : H)⟫_ℂ := by rw [hfix i]
        _ = 0 := horth
    have hyzero : y = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℂ) (E := W)).mp
      rw [← (b.hasSum_inner_mul_inner y y).tsum_eq]
      simp_rw [hyinner]
      simp
    exact congrArg (fun z : W => (z : H)) hyzero
  have hfg (i : w) : f (g i) = 1 := by
    dsimp [f]
    rw [hbi i, habs, hfix i]
    have hnorm : ‖(b i : H)‖ = 1 := by
      simpa using hbOrtho.1 i
    rw [inner_self_eq_norm_sq_to_K]
    simp [hnorm]
  have hsupport : Function.support f ⊆ Set.range g := by
    intro j hj
    by_contra hj'
    exact hj (by
      dsimp [f]
      rw [habs, hzero_of_not_mem_range j hj']
      simp)
  have hsum_support : (∑' j : Set.range g, f j) = ∑' j : wH, f j :=
    tsum_subtype_eq_of_support_subset hsupport
  let e : w ≃ Set.range g := Equiv.ofInjective g hgInjective
  have he (i : w) : e i = ⟨g i, ⟨i, rfl⟩⟩ := by
    apply Subtype.ext
    rfl
  have hsum_reindex : (∑' i : w, f (g i)) = ∑' j : Set.range g, f j := by
    calc
      (∑' i : w, f (g i)) = ∑' i : w, f (e i) := by
        apply tsum_congr
        intro i
        rw [he i]
      _ = ∑' j : Set.range g, f (j : wH) :=
        e.tsum_eq (fun j : Set.range g => f (j : wH))
  have hnormSum : HasSum (fun j : wH => ‖p (bH j)‖ ^ 2)
      (∑' i : w₀, ‖p (b₀ i)‖ ^ 2) :=
    hasSum_norm_sq_apply_of_selfAdjoint hp'.1.isSelfAdjoint b₀ bH hWdiag
  have hsum_real : ∑' j : wH, f j = ∑' i : w, f (g i) := by
    calc
      (∑' j : wH, f j) = ∑' j : Set.range g, f j := hsum_support.symm
      _ = ∑' i : w, f (g i) := hsum_reindex.symm
  have htrace_real : trace p hp.2 = ((∑' j : wH, f j : ℝ) : ℂ) := by
    calc
      trace p hp.2 = ∑' i : w₀, ⟪b₀ i, p (b₀ i)⟫_ℂ := by
        rfl
      _ = ∑' i : w₀, ((‖p (b₀ i)‖ ^ 2 : ℝ) : ℂ) := by
        apply tsum_congr
        intro i
        exact hpdiag (b₀ i)
      _ = ((∑' i : w₀, ‖p (b₀ i)‖ ^ 2 : ℝ) : ℂ) :=
        (Complex.ofReal_tsum (fun i : w₀ => ‖p (b₀ i)‖ ^ 2)).symm
      _ = ((∑' j : wH, ‖p (bH j)‖ ^ 2 : ℝ) : ℂ) := by
        rw [hnormSum.tsum_eq]
      _ = ((∑' j : wH, f j : ℝ) : ℂ) := by
        congr 1
        apply tsum_congr
        intro j
        dsimp [f]
        rw [habs, hpdiag]
        rfl
  rw [htrace_real, hsum_real]
  rw [tsum_congr (fun i => hfg i), tsum_fintype]
  have hcard : Module.finrank ℂ W = Fintype.card w :=
    Module.finrank_eq_card_basis b.toOrthonormalBasis.toBasis
  rw [hcard]
  simp

/-- In finite dimension, the trace of a finite-multiplicity projection is the dimension of its
range.  The proof deliberately goes through the ordinary linear-map trace theorem; this gives a
fully proved finite-dimensional instance without hiding the genuinely harder infinite-dimensional
trace-class argument behind an axiom. -/
theorem HasFiniteMultiplicity.trace_eq_finrank_range_of_finiteDimensional
    [FiniteDimensional ℂ H] {p : H →L[ℂ] H} (hp : HasFiniteMultiplicity p) :
    trace p hp.2 = (Module.finrank ℂ (LinearMap.range p.toLinearMap) : ℂ) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  let : Finite w := b.orthonormal.linearIndependent.finite
  let : Fintype w := Fintype.ofFinite w
  have hpIdem : IsIdempotentElem p.toLinearMap :=
    (ContinuousLinearMap.isIdempotentElem_toLinearMap_iff).2 hp.1.isIdempotentElem
  calc
    trace p hp.2 = LinearMap.trace ℂ H p.toLinearMap := by
      unfold trace
      exact (trace_eq_sum_inner_hilbertBasis_of_finiteDimensional
        p hp.2.choose_spec.choose).symm
    _ = (Module.finrank ℂ (LinearMap.range p.toLinearMap) : ℂ) :=
      (LinearMap.IsIdempotentElem.isProj_range p.toLinearMap hpIdem).trace

end
