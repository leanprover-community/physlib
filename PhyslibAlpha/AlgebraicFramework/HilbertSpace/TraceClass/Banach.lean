/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.TraceClass.Basic
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.TraceClass.GeneralProduct
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.TraceClass.IdealNorm
public import Mathlib.Analysis.Normed.Group.Seminorm
public import Mathlib.Analysis.Normed.Group.Completeness

/-!
# The trace-class Banach space `𝒮₁(H)`

Ported from `unbounded-alpha-public`'s
`QuantumMechanics/Unbounded/OperatorAlgebra/TraceClass/Space.lean`, adapted to this repo's
predicate-based `IsTraceClass`/`traceNorm`/`trace` (`HilbertSpace/TraceClass/Basic.lean`) rather
than the source's own bundled `TraceClass H` subtype (which lived in a *different*, non-predicate
`IsTraceClass` universe with its own general-product/ideal-norm theory built up over ~150KB across
17 files: `GeneralProduct.lean`, `IdealNorm.lean`, `PositiveIdeal.lean`, `HilbertSchmidt.lean`,
`Polar.lean`, `TraceAlgebra.lean`, etc.). This file re-bundles this repo's own `IsTraceClass`
predicate into the same kind of submodule/Banach-space package the source built, but the *proofs*
of the arithmetic closure facts that package needs (trace-class is closed under `+`, the trace norm
is subadditive, scalar multiplication scales it exactly, completeness) are **not** re-derived here:
they are exactly the "genuinely harder work" this repo's own `Basic.lean` docstring says it leaves
to "the later trace-class Banach space phase" (see `Basic.lean`'s own module doc, third paragraph
under "Relationship to `HilbertSpace/Trace.lean`"). This file is the promised later phase, but
lands with those specific gaps still open rather than silently invoking them.

## What closes the arithmetic-closure gaps

**Fully sorry-free.** The Hilbert–Schmidt/polar-decomposition prerequisite stack
(`HilbertSpace/TraceClass/{HilbertSchmidt,Polar,GeneralIdeal,GeneralProduct,IdealNorm}.lean`,
restating `unbounded-alpha-public`'s
`TraceClass/{HilbertSchmidt,HSAlgebra,HSEstimate,Polar,GeneralIdeal,GeneralProduct,IdealNorm,
Completeness}.lean` directly against this repo's own `H →L[ℂ] H`/predicate-based `IsTraceClass` —
no bundled-subtype translation was needed, since the source's own top-level `TraceClass.lean`
already used the identical predicate convention this repo's `Basic.lean` does) supplies:

* `isTraceClass_add` / `traceNorm_add_le` — from `GeneralProduct.isTraceClass_add` and
  `IdealNorm.traceNorm_add_le`, both built on the master lemma that a product of two
  Hilbert–Schmidt operators is trace class (`GeneralProduct.isTraceClass_mul_of_isHilbertSchmidt`),
  itself resting on the general partial-isometry identity `Polar.star_polarFactor_mul_self : star
  (polarFactor T) * T = |T|` (valid for *every* bounded `T`, not just self-adjoint ones).
* `instCompleteSpace` — via the absolutely-convergent-series criterion
  (`NormedAddCommGroup.completeSpace_of_summable_imp_tendsto`), following
  `unbounded-alpha-public`'s `Completeness.lean` directly: partial sums of an absolutely convergent
  series are Cauchy in operator norm (operator norm ≤ trace norm, `opNorm_le_traceNorm`), hence
  converge in `H →L[ℂ] H`; the auxiliary lower-semicontinuity lemma
  `isTraceClass_of_tendsto_of_traceNorm_bounded` identifies the limit as trace class with a
  quantitative trace-norm bound, applied twice (once to the whole sequence, once to each shifted
  tail) to get the tail bound that is exactly trace-norm convergence.

`isTraceClass_smul`/`traceNorm_smul` follow from Mathlib's `CFC.abs_smul`, and `opNorm_le_traceNorm`
is the elementary "operator norm ≤ Hilbert–Schmidt norm" argument, using `Basic.lean`'s Parseval
lemma `hasSum_norm_sq_inner_basis`.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology Filter
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Arithmetic closure of `IsTraceClass` -/

theorem isTraceClass_zero : IsTraceClass (0 : H →L[ℂ] H) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  exact ⟨w, b, by simp [CFC.abs_zero]⟩

/-- **Gap (3), closed directly**: trace class is closed under scalar multiplication, via Mathlib's
`CFC.abs_smul : CFC.abs (c • T) = ‖c‖ • CFC.abs T`. -/
theorem isTraceClass_smul (c : ℂ) {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsTraceClass (c • T) := by
  obtain ⟨w, b, hb⟩ := hT
  refine ⟨w, b, ?_⟩
  have habs : CFC.abs (c • T) = ‖c‖ • CFC.abs T := CFC.abs_smul c T
  have heq : ∀ i : w, (⟪b i, CFC.abs (c • T) (b i)⟫_ℂ).re
      = ‖c‖ * (⟪b i, CFC.abs T (b i)⟫_ℂ).re := by
    intro i
    rw [habs, smul_apply,
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
    simp [Complex.mul_re]
  simpa only [heq] using hb.mul_left ‖c‖

-- Trace class is closed under addition: `isTraceClass_add`, ported into `GeneralProduct.lean`
-- from the polar-decomposition/Hilbert–Schmidt-factorization argument (see module docstring).
-- That theorem already has exactly the signature `IsTraceClass T → IsTraceClass T' →
-- IsTraceClass (T + T')`, so it is used directly (e.g. below, and in `traceClassSubmodule`)
-- rather than restated here.

theorem isTraceClass_neg {T : H →L[ℂ] H} (hT : IsTraceClass T) : IsTraceClass (-T) := by
  have h := isTraceClass_smul (-1 : ℂ) hT
  rwa [neg_one_smul] at h

/-- Transporting `traceNorm` across an equality of the underlying operator. Needed because `rw`
cannot rewrite `traceNorm`'s operator argument directly (the motive depends on the witness proof).
-/
theorem traceNorm_transport {X Y : H →L[ℂ] H} (hEq : X = Y) (hX : IsTraceClass X) :
    traceNorm X hX = traceNorm Y (hEq ▸ hX) := by
  subst hEq; rfl

theorem traceNorm_zero : traceNorm (0 : H →L[ℂ] H) isTraceClass_zero = 0 := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [traceNorm_eq_of_hilbertBasis isTraceClass_zero b]
  simp [CFC.abs_zero]

/-- **Gap (3), closed directly**: the trace norm scales exactly under scalar multiplication,
`‖c • T‖₁ = ‖c‖ * ‖T‖₁`, via `CFC.abs_smul` and `traceNorm_eq_of_hilbertBasis` (evaluated at `T`'s
own witness basis, where `traceNorm T hT` unfolds definitionally). -/
theorem traceNorm_smul (c : ℂ) {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    traceNorm (c • T) (isTraceClass_smul c hT) = ‖c‖ * traceNorm T hT := by
  set w₀ : Set H := hT.choose with hw₀
  set b₀ : HilbertBasis w₀ ℂ H := hT.choose_spec.choose with hb₀def
  have habs : CFC.abs (c • T) = ‖c‖ • CFC.abs T := CFC.abs_smul c T
  have heq : ∀ i : w₀, (⟪b₀ i, CFC.abs (c • T) (b₀ i)⟫_ℂ).re
      = ‖c‖ * (⟪b₀ i, CFC.abs T (b₀ i)⟫_ℂ).re := by
    intro i
    rw [habs, smul_apply,
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
    simp [Complex.mul_re]
  rw [traceNorm_eq_of_hilbertBasis (isTraceClass_smul c hT) b₀]
  calc ∑' i : w₀, (⟪b₀ i, CFC.abs (c • T) (b₀ i)⟫_ℂ).re
      = ∑' i : w₀, ‖c‖ * (⟪b₀ i, CFC.abs T (b₀ i)⟫_ℂ).re := tsum_congr heq
    _ = ‖c‖ * ∑' i : w₀, (⟪b₀ i, CFC.abs T (b₀ i)⟫_ℂ).re := tsum_mul_left
    _ = ‖c‖ * traceNorm T hT := rfl

theorem traceNorm_neg {T : H →L[ℂ] H} (hT : IsTraceClass T) (hnegT : IsTraceClass (-T)) :
    traceNorm (-T) hnegT = traceNorm T hT := by
  have h1 := traceNorm_smul (-1 : ℂ) hT
  have h2 := traceNorm_transport (neg_one_smul ℂ T) (isTraceClass_smul (-1) hT)
  calc
    traceNorm (-T) hnegT =
        traceNorm (-T) (neg_one_smul ℂ T ▸ isTraceClass_smul (-1) hT) := traceNorm_congr
    _ = traceNorm ((-1 : ℂ) • T) (isTraceClass_smul (-1) hT) := h2.symm
    _ = ‖(-1 : ℂ)‖ * traceNorm T hT := h1
    _ = traceNorm T hT := by norm_num

-- The trace norm is subadditive, `‖T + T'‖₁ ≤ ‖T‖₁ + ‖T'‖₁`: `traceNorm_add_le`, ported into
-- `IdealNorm.lean` from the duality-bound argument (see module docstring), already has exactly
-- this signature, so it is used directly (e.g. in `traceClassAddGroupNorm` below) rather than
-- restated here.

/-- **Gap (4), closed directly** (not from the source's `IdealNorm.lean:332`, which builds this
from the general duality/ideal-norm machinery): `‖T‖ ≤ ‖T‖₁`, proved instead by the elementary
"operator norm ≤ Hilbert–Schmidt norm" argument. Writing `A := |T|`, `S := √A` (self-adjoint,
`S*S = A`), for any unit `x`: `‖Sx‖² = ∑ᵢ‖⟪bᵢ,Sx⟫‖²` (Parseval) `= ∑ᵢ‖⟪Sbᵢ,x⟫‖²` (`S` self-adjoint)
`≤ ∑ᵢ‖Sbᵢ‖²‖x‖²` (Cauchy–Schwarz termwise) `= ‖T‖₁ ‖x‖²` (the trace-norm diagonal sum, in the same
basis). Hence `‖S‖ ≤ √‖T‖₁`, so `‖T‖ = ‖A‖ = ‖S*S‖ = ‖S‖² ≤ ‖T‖₁`. -/
theorem opNorm_le_traceNorm {T : H →L[ℂ] H} (hT : IsTraceClass T) : ‖T‖ ≤ traceNorm T hT := by
  set A : H →L[ℂ] H := CFC.abs T with hAdef
  have hAnonneg : 0 ≤ A := CFC.abs_nonneg T
  have hAself : IsSelfAdjoint A := .of_nonneg hAnonneg
  set S : H →L[ℂ] H := CFC.sqrt A with hSdef
  have hSself : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg A)
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hAnonneg
  have hTA : ‖T‖ = ‖A‖ := (CFC.norm_abs).symm
  have hAeq : ‖A‖ = ‖S‖ ^ 2 := by rw [← hSS]; exact hSself.norm_mul_self
  set w₀ : Set H := hT.choose with hw₀
  set b₀ : HilbertBasis w₀ ℂ H := hT.choose_spec.choose with hb₀def
  have hb₀ : Summable (fun i : w₀ => (⟪b₀ i, A (b₀ i)⟫_ℂ).re) := hT.choose_spec.choose_spec
  have hSstar : ContinuousLinearMap.adjoint S = S :=
    (ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself
  have hpt : ∀ i : w₀, (⟪b₀ i, A (b₀ i)⟫_ℂ).re = ‖S (b₀ i)‖ ^ 2 := by
    intro i
    have hinner : ⟪b₀ i, A (b₀ i)⟫_ℂ = ⟪S (b₀ i), S (b₀ i)⟫_ℂ := by
      rw [← hSS]
      show ⟪b₀ i, (S * S) (b₀ i)⟫_ℂ = _
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [← ContinuousLinearMap.adjoint_inner_left S (S (b₀ i)) (b₀ i), hSstar]
    rw [hinner, inner_self_eq_norm_sq_to_K]; norm_cast
  have hSum : Summable (fun i : w₀ => ‖S (b₀ i)‖ ^ 2) := hb₀.congr hpt
  have htrEq : traceNorm T hT = ∑' i : w₀, ‖S (b₀ i)‖ ^ 2 := tsum_congr hpt
  have htrNonneg : 0 ≤ traceNorm T hT := traceNorm_nonneg T hT
  have hbound : ∀ x : H, ‖S x‖ ^ 2 ≤ traceNorm T hT * ‖x‖ ^ 2 := by
    intro x
    have hpar : HasSum (fun i : w₀ => ‖⟪b₀ i, S x⟫_ℂ‖ ^ 2) (‖S x‖ ^ 2) :=
      hasSum_norm_sq_inner_basis b₀ (S x)
    have heq2 : ∀ i : w₀, ⟪b₀ i, S x⟫_ℂ = ⟪S (b₀ i), x⟫_ℂ := fun i => by
      have h := ContinuousLinearMap.adjoint_inner_left S x (b₀ i)
      rw [hSstar] at h
      exact h.symm
    have hpar' : HasSum (fun i : w₀ => ‖⟪S (b₀ i), x⟫_ℂ‖ ^ 2) (‖S x‖ ^ 2) := by
      simpa [heq2] using hpar
    have hCS : ∀ i : w₀, ‖⟪S (b₀ i), x⟫_ℂ‖ ^ 2 ≤ ‖S (b₀ i)‖ ^ 2 * ‖x‖ ^ 2 := fun i => by
      have h : ‖⟪S (b₀ i), x⟫_ℂ‖ ≤ ‖S (b₀ i)‖ * ‖x‖ := norm_inner_le_norm _ _
      calc ‖⟪S (b₀ i), x⟫_ℂ‖ ^ 2 ≤ (‖S (b₀ i)‖ * ‖x‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = ‖S (b₀ i)‖ ^ 2 * ‖x‖ ^ 2 := by ring
    have hdom : HasSum (fun i : w₀ => ‖S (b₀ i)‖ ^ 2 * ‖x‖ ^ 2) (traceNorm T hT * ‖x‖ ^ 2) := by
      rw [htrEq]; exact hSum.hasSum.mul_right (‖x‖ ^ 2)
    exact hasSum_le hCS hpar' hdom
  have hboundNorm : ∀ x : H, ‖S x‖ ≤ Real.sqrt (traceNorm T hT) * ‖x‖ := by
    intro x
    have h1 : ‖S x‖ ^ 2 ≤ traceNorm T hT * ‖x‖ ^ 2 := hbound x
    have h2 : Real.sqrt (‖S x‖ ^ 2) ≤ Real.sqrt (traceNorm T hT * ‖x‖ ^ 2) :=
      Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul htrNonneg,
      Real.sqrt_sq (norm_nonneg _)] at h2
  have hSnorm_le : ‖S‖ ≤ Real.sqrt (traceNorm T hT) :=
    S.opNorm_le_bound (Real.sqrt_nonneg _) hboundNorm
  have hSsq_le : ‖S‖ ^ 2 ≤ traceNorm T hT := by
    have h := pow_le_pow_left₀ (norm_nonneg S) hSnorm_le 2
    rwa [Real.sq_sqrt htrNonneg] at h
  rw [hTA, hAeq]
  exact hSsq_le

/-! ## The trace-class submodule and Banach space -/

/-- **The trace-class operators, as a `ℂ`-submodule of `H →L[ℂ] H`.** This is the concrete object
underlying the trace-class Banach space: its carrier type inherits `AddCommGroup`/`Module ℂ`
directly from the ambient `Submodule` API, so only the norm structure remains to be supplied.
Direct port of the source's `traceClassSubmodule`. -/
def traceClassSubmodule (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Submodule ℂ (H →L[ℂ] H) where
  carrier := {T | IsTraceClass T}
  zero_mem' := isTraceClass_zero
  add_mem' ha hb := isTraceClass_add ha hb
  smul_mem' c _ ha := isTraceClass_smul c ha

/-- **The trace-class Banach space `𝒮₁(H)`.** Deliberately a plain (semireducible) `def`, not an
`abbrev`, for the same reason as the source: the carrier of `traceClassSubmodule H` already has a
generic `Submodule`-induced `NormedAddCommGroup` instance coming from the ambient *operator* norm,
and marking `TraceClass H` reducible would let typeclass search find that competing instance
instead of the trace-norm one constructed below. -/
def TraceClass (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    Type _ :=
  traceClassSubmodule H

namespace TraceClass

noncomputable instance instAddCommGroup : AddCommGroup (TraceClass H) :=
  inferInstanceAs (AddCommGroup (traceClassSubmodule H))

noncomputable instance instModule : Module ℂ (TraceClass H) :=
  inferInstanceAs (Module ℂ (traceClassSubmodule H))

theorem mem_iff {T : H →L[ℂ] H} : T ∈ traceClassSubmodule H ↔ IsTraceClass T := Iff.rfl

/-- The trace-class witness carried by an element of `TraceClass H`. -/
theorem isTraceClass_coe (T : TraceClass H) : IsTraceClass T.1 := T.2

/-- Build an element of `TraceClass H` from an operator and its trace-class witness. A dedicated
constructor, rather than the anonymous `⟨T, hT⟩`, because `TraceClass H` is deliberately a plain
(semireducible) `def` (see above). -/
def ofOperator (T : H →L[ℂ] H) (hT : IsTraceClass T) : TraceClass H := ⟨T, hT⟩

@[simp] theorem ofOperator_coe (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    (ofOperator T hT).1 = T := rfl

/-- **The trace norm as an `AddGroupNorm`** on the trace-class submodule: nonnegativity, the
triangle inequality (`traceNorm_add_le`), invariance under negation, and the zero-detection
property (via `opNorm_le_traceNorm`). -/
noncomputable def traceClassAddGroupNorm : AddGroupNorm (TraceClass H) where
  toFun T := traceNorm T.1 (isTraceClass_coe T)
  map_zero' := traceNorm_zero
  neg' T := traceNorm_neg (isTraceClass_coe T) (isTraceClass_coe (-T))
  add_le' T T' := traceNorm_add_le (isTraceClass_coe T) (isTraceClass_coe T')
    (isTraceClass_coe (T + T'))
  eq_zero_of_map_eq_zero' T hT0 := by
    have hop : ‖T.1‖ ≤ traceNorm T.1 (isTraceClass_coe T) :=
      opNorm_le_traceNorm (isTraceClass_coe T)
    rw [hT0] at hop
    have : T.1 = 0 := norm_le_zero_iff.mp hop
    exact Subtype.ext this

/-- **The trace-class Banach space's `NormedAddCommGroup` instance**, with norm `traceNorm`. -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (TraceClass H) :=
  AddGroupNorm.toNormedAddCommGroup traceClassAddGroupNorm

theorem norm_eq_traceNorm (T : TraceClass H) :
    ‖T‖ = traceNorm T.1 (isTraceClass_coe T) := rfl

/-- **The trace-class Banach space's `NormedSpace ℂ` instance**: scalar multiplication scales the
trace norm exactly, by `traceNorm_smul`. -/
noncomputable instance instNormedSpace : NormedSpace ℂ (TraceClass H) where
  norm_smul_le c T := by
    rw [norm_eq_traceNorm, norm_eq_traceNorm]
    have hEq : ((c • T : TraceClass H)).1 = c • T.1 := rfl
    have h := traceNorm_transport hEq (isTraceClass_coe (c • T))
    rw [h]
    exact le_of_eq (traceNorm_smul c (isTraceClass_coe T))

/-- **Lower semicontinuity of the trace norm under operator-norm convergence.** If a sequence of
trace-class operators with uniformly bounded trace norm converges in operator norm, its limit is
trace class with the same bound. This is the single analytic fact needed for completeness: it lets
a trace-norm-Cauchy sequence's operator-norm limit be recognized as trace class, with a
quantitative tail bound. Ported from `unbounded-alpha-public`'s
`TraceClass/Completeness.lean`. -/
theorem isTraceClass_of_tendsto_of_traceNorm_bounded {Tn : ℕ → H →L[ℂ] H} {T : H →L[ℂ] H} {C : ℝ}
    (hTn : ∀ n, IsTraceClass (Tn n)) (hbound : ∀ n, traceNorm (Tn n) (hTn n) ≤ C)
    (htendsto : Tendsto Tn atTop (𝓝 T)) :
    ∃ hT : IsTraceClass T, traceNorm T hT ≤ C := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  set W : H →L[ℂ] H := Polar.polarFactor T with hWdef
  have hWnorm : ‖W‖ ≤ 1 := Polar.polarFactor_opNorm_le T
  have hcont : ∀ i : w, Tendsto (fun n => ‖⟪W (b i), Tn n (b i)⟫_ℂ‖) atTop
      (𝓝 ‖⟪W (b i), T (b i)⟫_ℂ‖) := by
    intro i
    have h1 : Tendsto (fun n => Tn n (b i)) atTop (𝓝 (T (b i))) := by
      have hev : Continuous (fun X : H →L[ℂ] H => X (b i)) :=
        (ContinuousLinearMap.apply ℂ H (b i : H)).continuous
      exact hev.continuousAt.tendsto.comp htendsto
    have h2 : Tendsto (fun n => ⟪W (b i), Tn n (b i)⟫_ℂ) atTop
        (𝓝 ⟪W (b i), T (b i)⟫_ℂ) :=
      ((continuous_const.inner continuous_id).continuousAt.tendsto.comp h1
        |>.congr (fun _ => rfl)).mono_left le_rfl
    exact continuous_norm.continuousAt.tendsto.comp h2
  have hFinset : ∀ u : Finset w, (∑ i ∈ u, ‖⟪W (b i), T (b i)⟫_ℂ‖) ≤ C := by
    intro u
    have hpt : ∀ n, (∑ i ∈ u, ‖⟪W (b i), Tn n (b i)⟫_ℂ‖) ≤ C := by
      intro n
      have hsum : Summable (fun i : w => ‖⟪W (b i), Tn n (b i)⟫_ℂ‖) :=
        summable_norm_inner_contraction_of_isTraceClass (hTn n) hWnorm b
      have hall : (∑' i : w, ‖⟪W (b i), Tn n (b i)⟫_ℂ‖) ≤ C :=
        (tsum_norm_inner_contraction_le_traceNorm (hTn n) hWnorm b).trans (hbound n)
      exact (hsum.sum_le_tsum u (fun i _ => norm_nonneg _)).trans hall
    have hlim : Tendsto (fun n => ∑ i ∈ u, ‖⟪W (b i), Tn n (b i)⟫_ℂ‖) atTop
        (𝓝 (∑ i ∈ u, ‖⟪W (b i), T (b i)⟫_ℂ‖)) :=
      tendsto_finsetSum u (fun i _ => hcont i)
    exact le_of_tendsto hlim (Eventually.of_forall hpt)
  have hsummable : Summable (fun i : w => ‖⟪W (b i), T (b i)⟫_ℂ‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) hFinset
  have htsum_le : (∑' i : w, ‖⟪W (b i), T (b i)⟫_ℂ‖) ≤ C :=
    Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) hFinset
  have hpoint : ∀ i : w, (⟪b i, CFC.abs T (b i)⟫_ℂ).re = ‖⟪W (b i), T (b i)⟫_ℂ‖ := by
    intro i
    have hval : ⟪b i, CFC.abs T (b i)⟫_ℂ = ⟪W (b i), T (b i)⟫_ℂ := by
      have habs : CFC.abs T = star W * T := (Polar.star_polarFactor_mul_self T).symm
      rw [habs, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_inner_right W (b i) (T (b i))]
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
    rw [show ‖⟪W (b i), T (b i)⟫_ℂ‖ = ‖⟪b i, CFC.abs T (b i)⟫_ℂ‖ from by rw [hval],
      heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg, Complex.ofReal_re]
  have hT : IsTraceClass T := ⟨w, b, by
    apply hsummable.congr
    exact fun i => (hpoint i).symm⟩
  refine ⟨hT, ?_⟩
  rw [traceNorm_eq_of_hilbertBasis hT b]
  calc
    (∑' i : w, (⟪b i, CFC.abs T (b i)⟫_ℂ).re) = ∑' i : w, ‖⟪W (b i), T (b i)⟫_ℂ‖ :=
      tsum_congr hpoint
    _ ≤ C := htsum_le

/-- **Completeness of the trace-class Banach space.** Given an absolutely convergent series `u`
(`Σ‖uₙ‖₁ < ∞`), its partial sums `Sₙ` are Cauchy in operator norm (since operator norm ≤ trace
norm), hence converge in `H →L[ℂ] H` to some `S`; the lower-semicontinuity lemma above identifies
`S` as trace class (bounded by the full sum `M`), and applied again to the shifted tail sequence
gives the quantitative tail bound `‖⟨S,·⟩ - Sₙ‖₁ ≤ M - Σᵢ₌₀ⁿ⁻¹‖uᵢ‖₁ → 0`, which is exactly
trace-norm convergence of `Sₙ` to `S`. Ported from `unbounded-alpha-public`'s
`TraceClass/Completeness.lean`. -/
noncomputable instance instCompleteSpace : CompleteSpace (TraceClass H) := by
  apply NormedAddCommGroup.completeSpace_of_summable_imp_tendsto
  intro u hu
  set psum : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, ‖u i‖ with hpartialdef
  set M : ℝ := ∑' n, ‖u n‖ with hMdef
  set Sn : ℕ → TraceClass H := fun n => ∑ i ∈ Finset.range n, u i with hSndef
  set Tn : ℕ → H →L[ℂ] H := fun n => (Sn n).1 with hTndef
  have hpartial_le_M : ∀ n, psum n ≤ M := fun n => hu.sum_le_tsum _ (fun i _ => norm_nonneg _)
  have hpartial_tendsto : Tendsto psum atTop (𝓝 M) := hu.hasSum.tendsto_sum_nat
  set tail : ℕ → ℝ := fun n => M - psum n with htaildef
  have htail_tendsto : Tendsto tail atTop (𝓝 0) := by
    have := hpartial_tendsto.const_sub M
    simpa [htaildef] using this
  have hSn_diff : ∀ n m : ℕ, n ≤ m → Sn m - Sn n = ∑ i ∈ Finset.Ico n m, u i := by
    intro n m hnm
    simp only [hSndef]
    rw [Finset.sum_Ico_eq_sub _ hnm]
  have hpsum_split : ∀ n m : ℕ, n ≤ m →
      (∑ i ∈ Finset.Ico n m, ‖u i‖) = psum m - psum n := by
    intro n m hnm
    simp only [hpartialdef]
    rw [Finset.sum_Ico_eq_sub _ hnm]
  have htrace_tail_bound : ∀ n m : ℕ, n ≤ m → ‖Sn m - Sn n‖ ≤ tail n := by
    intro n m hnm
    rw [hSn_diff n m hnm]
    calc ‖∑ i ∈ Finset.Ico n m, u i‖ ≤ ∑ i ∈ Finset.Ico n m, ‖u i‖ := norm_sum_le _ _
      _ = psum m - psum n := hpsum_split n m hnm
      _ ≤ tail n := by simp only [htaildef]; linarith [hpartial_le_M m]
  have hSn_diff_coe : ∀ n m : ℕ, ((Sn m - Sn n : TraceClass H)).1 = Tn m - Tn n :=
    fun n m => Submodule.coe_sub _ _ _
  have htn_cauchy : CauchySeq Tn := by
    apply cauchySeq_of_le_tendsto_0' tail _ htail_tendsto
    intro n m hnm
    rw [dist_eq_norm]
    have heqop : Tn n - Tn m = -(Tn m - Tn n) := by abel
    rw [heqop, norm_neg, ← hSn_diff_coe n m]
    calc ‖((Sn m - Sn n : TraceClass H)).1‖ ≤ ‖(Sn m - Sn n : TraceClass H)‖ :=
          opNorm_le_traceNorm (isTraceClass_coe (Sn m - Sn n))
      _ ≤ tail n := htrace_tail_bound n m hnm
  obtain ⟨S, hStendsto⟩ := cauchySeq_tendsto_of_complete htn_cauchy
  have hSn_bound : ∀ n, traceNorm (Sn n).1 (isTraceClass_coe (Sn n)) ≤ M := by
    intro n
    show ‖Sn n‖ ≤ M
    calc ‖Sn n‖ ≤ ∑ i ∈ Finset.range n, ‖u i‖ := by
          simp only [hSndef]; exact norm_sum_le _ _
      _ = psum n := rfl
      _ ≤ M := hpartial_le_M n
  obtain ⟨hS, -⟩ := isTraceClass_of_tendsto_of_traceNorm_bounded
    (fun n => isTraceClass_coe (Sn n)) hSn_bound hStendsto
  refine ⟨ofOperator S hS, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hbound_S : ∀ n, dist (Sn n) (ofOperator S hS : TraceClass H) ≤ tail n := by
    intro n
    rw [dist_eq_norm]
    have hVtrace : ∀ m, IsTraceClass (Tn (n + m) - Tn n) := by
      intro m
      rw [← hSn_diff_coe n (n + m)]
      exact isTraceClass_coe (Sn (n + m) - Sn n)
    have hVbound : ∀ m, traceNorm (Tn (n + m) - Tn n) (hVtrace m) ≤ tail n := by
      intro m
      have h1 : traceNorm (Tn (n + m) - Tn n) (hVtrace m) =
          traceNorm ((Sn (n + m) - Sn n : TraceClass H)).1
            (isTraceClass_coe (Sn (n + m) - Sn n)) := by
        have hEq : Tn (n + m) - Tn n = ((Sn (n + m) - Sn n : TraceClass H)).1 :=
          (hSn_diff_coe n (n + m)).symm
        exact traceNorm_transport hEq (hVtrace m)
      rw [h1]
      show ‖Sn (n + m) - Sn n‖ ≤ tail n
      exact htrace_tail_bound n (n + m) (Nat.le_add_right n m)
    have hVtendsto : Tendsto (fun m => Tn (n + m) - Tn n) atTop (𝓝 (S - Tn n)) := by
      have h1 : Tendsto (fun m => Tn (n + m)) atTop (𝓝 S) := by
        have h2 : Tendsto (fun m => Tn (m + n)) atTop (𝓝 S) :=
          hStendsto.comp (tendsto_add_atTop_nat n)
        simpa only [add_comm] using h2
      exact h1.sub tendsto_const_nhds
    obtain ⟨hSTn, hSTnbound⟩ := isTraceClass_of_tendsto_of_traceNorm_bounded hVtrace hVbound
      hVtendsto
    have heqfinal : ((ofOperator S hS : TraceClass H) - Sn n).1 = S - Tn n := rfl
    have hnorm_eq : ‖(ofOperator S hS : TraceClass H) - Sn n‖ = traceNorm (S - Tn n) hSTn := by
      have h3 : ‖(ofOperator S hS : TraceClass H) - Sn n‖ =
          traceNorm ((ofOperator S hS : TraceClass H) - Sn n).1
            (isTraceClass_coe ((ofOperator S hS : TraceClass H) - Sn n)) := rfl
      rw [h3]
      exact traceNorm_transport heqfinal (isTraceClass_coe ((ofOperator S hS : TraceClass H) - Sn
          n))
    rw [norm_sub_rev]
    rw [hnorm_eq]
    exact hSTnbound
  exact squeeze_zero (fun n => dist_nonneg) hbound_S htail_tendsto

end TraceClass

end
