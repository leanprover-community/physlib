/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import PhyslibAlpha.Mathematics.TauCeti.Analysis.InnerProductSpace.BasisSpan
public import PhyslibAlpha.Mathematics.TauCeti.LinearAlgebra.Dimension.Submodule

/-!
# Courant–Fischer min–max theorem and Weyl's inequality

For a finite-dimensional inner-product space over `ℝ` or `ℂ`, the min–max theorem characterizes the
decreasingly sorted eigenvalues of a symmetric endomorphism through its Rayleigh form.

## i. Overview

For a finite-dimensional inner-product space over `ℝ` or `ℂ`, the min–max theorem
characterizes the decreasingly sorted eigenvalues of a symmetric endomorphism
through its Rayleigh form.  The same argument gives monotonicity under quadratic-
form domination and Weyl's perturbation bound.

## ii. Key results

* `LinearMap.IsSymmetric.re_inner_apply_self_eq_sum_eigenvalues_mul_sq`:
  diagonal expansion of the Rayleigh form in an eigenbasis.
* `LinearMap.IsSymmetric.exists_unit_vector_re_inner_le_eigenvalue` and
  `LinearMap.IsSymmetric.exists_submodule_forall_unit_eigenvalue_le_re_inner`:
  the two min–max directions.
* `LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf_re_inner`:
  the Courant–Fischer equality.
* `LinearMap.IsSymmetric.eigenvalue_mono`:
  monotonicity of sorted eigenvalues under quadratic-form order.
* `LinearMap.IsSymmetric.abs_eigenvalue_sub_eigenvalue_le` and
  `LinearMap.IsSymmetric.abs_eigenvalue_sub_eigenvalue_le_norm`:
  Weyl's perturbation inequality.
* `LinearMap.IsSymmetric.eigenvalue_compression_le` and
  `LinearMap.IsSymmetric.eigenvalue_le_eigenvalue_compression`:
  Cauchy interlacing for an operator on a subspace with the same quadratic form, such as the
  compression `LinearMap.IsSymmetric.compression`.
* `LinearMap.IsSymmetric.eigenvalue_ascending_le_ritz`: the Hylleraas–Undheim–MacDonald
  bound, the `k`-th lowest Ritz value bounds the `k`-th lowest eigenvalue from above.

## iii. Table of contents

- A. Development
  - A.1. The quadratic form in the eigenbasis
  - A.2. Discrete Courant–Fischer directional bounds
  - A.3. The Courant–Fischer min-max equality
  - A.4. Sorted-eigenvalue uniqueness and Loewner monotonicity
  - A.5. Weyl's inequality
  - A.6. Courant–Fischer on subspaces of larger dimension
  - A.7. Cauchy interlacing and Rayleigh–Ritz bounds
  - A.8. The orthogonal compression

## iv. References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed.,
  Theorems 4.2.6 and 4.3.1.
* R. Bhatia, *Matrix Analysis*, Corollary III.2.6.
* E. A. Hylleraas and B. Undheim, *Numerische Berechnung der 2S-Terme von Ortho- und
  Par-Helium*, Z. Phys. 65 (1930) 759–772, pp. 763–764. [ref: hylleraas_undheim_1930]
* J. K. L. MacDonald, *Successive Approximations by the Rayleigh-Ritz Variation Method*,
  Phys. Rev. 43 (1933) 830–833, rule (1) and Corollary 1.1. [ref: macdonald_1933]

Provenance: Ported and adapted from
[`ForTauCeti/Analysis/InnerProductSpace/CourantFischer.lean`](https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/main/ForTauCeti/Analysis/InnerProductSpace/CourantFischer.lean)
in Kitware's DKPS formalization (Apache-2.0).  The original proof development
was by Claude Fable 5, with polishing by Claude Opus 4.8 and oversight by
Jon Crall.
-/

public section

/-! ## A. Development -/

open Module (finrank)
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}

/-- Parseval: in an orthonormal basis the squared norms of the coordinates sum
to the squared norm.  Thin wrapper around
`OrthonormalBasis.sum_sq_norm_inner_right`. -/
private lemma sum_sq_norm_repr_eq_sq_norm (b : OrthonormalBasis (Fin n) 𝕜 E) (x : E) :
    ∑ i : Fin n, ‖b.repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
  simp_rw [b.repr_apply_apply]
  exact b.sum_sq_norm_inner_right x


namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E}

omit [FiniteDimensional 𝕜 E] in
/-- Diagonalization of the quadratic form in any orthonormal eigenbasis: if
`S (w i) = μ i • w i` for all `i`, then
`re ⟪S x, x⟫ = ∑ i, μ i * ‖w.repr x i‖ ^ 2`. -/
lemma re_inner_apply_self_eq_sum_of_eigenbasis
    (hS : S.IsSymmetric) (w : OrthonormalBasis (Fin n) 𝕜 E) {μ : Fin n → ℝ}
    (hw : ∀ i, S (w i) = (μ i : 𝕜) • w i) (x : E) :
    RCLike.re ⟪S x, x⟫_𝕜 = ∑ i : Fin n, μ i * ‖w.repr x i‖ ^ 2 := by
  have hrepr : ∀ i, w.repr (S x) i = (μ i : 𝕜) * w.repr x i := by
    intro i
    rw [w.repr_apply_apply, w.repr_apply_apply, ← hS (w i) x, hw i, inner_smul_left,
      RCLike.conj_ofReal]
  have key : ⟪S x, x⟫_𝕜 = ((∑ i : Fin n, μ i * ‖w.repr x i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← w.repr.inner_map_map (S x) x, PiLp.inner_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.inner_apply, hrepr i, map_mul, RCLike.conj_ofReal, mul_left_comm,
      RCLike.mul_conj]
  rw [key, RCLike.ofReal_re]

omit [FiniteDimensional 𝕜 E] in
/-- On the span of the eigenvectors selected by `s`, the quadratic form is
bounded below by any lower bound on the selected values (general-eigenbasis
version of `le_re_inner_apply_self_of_mem_spanIndices`). -/
lemma le_re_inner_of_eigenbasis
    (hS : S.IsSymmetric) (w : OrthonormalBasis (Fin n) 𝕜 E) {μ : Fin n → ℝ}
    (hw : ∀ i, S (w i) = (μ i : 𝕜) • w i) {s : Set (Fin n)} {c : ℝ}
    (hc : ∀ i ∈ s, c ≤ μ i) {x : E} (hx : x ∈ w.spanIndices s) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪S x, x⟫_𝕜 := by
  rw [hS.re_inner_apply_self_eq_sum_of_eigenbasis w hw x,
    -- names the application so the norm bound applies to it directly.
    show c * ‖x‖ ^ 2 = ∑ i : Fin n, c * ‖w.repr x i‖ ^ 2 by
      rw [← Finset.mul_sum, sum_sq_norm_repr_eq_sq_norm]]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hp : i ∈ s
  · exact mul_le_mul_of_nonneg_right (hc i hp) (sq_nonneg _)
  · rw [w.repr_eq_zero_of_mem_spanIndices hx hp]; simp

omit [FiniteDimensional 𝕜 E] in
/-- Dual of `le_re_inner_of_eigenbasis`. -/
lemma re_inner_le_of_eigenbasis
    (hS : S.IsSymmetric) (w : OrthonormalBasis (Fin n) 𝕜 E) {μ : Fin n → ℝ}
    (hw : ∀ i, S (w i) = (μ i : 𝕜) • w i) {s : Set (Fin n)} {c : ℝ}
    (hc : ∀ i ∈ s, μ i ≤ c) {x : E} (hx : x ∈ w.spanIndices s) :
    RCLike.re ⟪S x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
  rw [hS.re_inner_apply_self_eq_sum_of_eigenbasis w hw x,
    -- names the application so the norm bound applies to it directly.
    show c * ‖x‖ ^ 2 = ∑ i : Fin n, c * ‖w.repr x i‖ ^ 2 by
      rw [← Finset.mul_sum, sum_sq_norm_repr_eq_sq_norm]]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hp : i ∈ s
  · exact mul_le_mul_of_nonneg_right (hc i hp) (sq_nonneg _)
  · rw [w.repr_eq_zero_of_mem_spanIndices hx hp]; simp


/-! ### A.1. The quadratic form in the eigenbasis -/

/-- The quadratic form `re ⟪T x, x⟫` of a symmetric operator `T` expressed in
its eigenbasis: it is the eigenvalue-weighted sum of the squared norms of the
coordinates of `x`.  This is the diagonalization of the quadratic form.  (For
symmetric `T` the inner product `⟪T x, x⟫` is real, so no information is lost
by taking the real part.) -/
lemma re_inner_apply_self_eq_sum_eigenvalues_mul_sq
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (x : E) :
    RCLike.re ⟪T x, x⟫_𝕜
      = ∑ i : Fin n, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  exact hT.re_inner_apply_self_eq_sum_of_eigenbasis
    (hT.eigenvectorBasis hn) (hT.apply_eigenvectorBasis hn) x

/-- On the span of a selected subfamily of the eigenbasis, the quadratic form
is bounded by any bound on the selected eigenvalues: if
`x ∈ b.spanIndices s` (so its coordinates vanish off `s`) and every selected
eigenvalue satisfies `λᵢ ≤ c`, then `re ⟪T x, x⟫ ≤ c ‖x‖²`. -/
lemma re_inner_apply_self_le_of_mem_spanIndices
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {s : Set (Fin n)} {c : ℝ}
    (hc : ∀ i ∈ s, hT.eigenvalues hn i ≤ c)
    {x : E} (hx : x ∈ (hT.eigenvectorBasis hn).spanIndices s) :
    RCLike.re ⟪T x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
  exact hT.re_inner_le_of_eigenbasis
    (hT.eigenvectorBasis hn) (hT.apply_eigenvectorBasis hn) hc hx

/-- Dual of `re_inner_apply_self_le_of_mem_spanIndices`: if
`x ∈ b.spanIndices s` and every selected eigenvalue satisfies `c ≤ λᵢ`, then
`c ‖x‖² ≤ re ⟪T x, x⟫`. -/
lemma le_re_inner_apply_self_of_mem_spanIndices
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {s : Set (Fin n)} {c : ℝ}
    (hc : ∀ i ∈ s, c ≤ hT.eigenvalues hn i)
    {x : E} (hx : x ∈ (hT.eigenvectorBasis hn).spanIndices s) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  exact hT.le_re_inner_of_eigenbasis
    (hT.eigenvectorBasis hn) (hT.apply_eigenvectorBasis hn) hc hx

/-! ### A.2. Discrete Courant–Fischer directional bounds -/

/-- **Courant–Fischer, upper direction.** On any subspace `V` of dimension
`k + 1` there is a unit vector `x` with `re ⟪T x, x⟫ ≤ λₖ(T)`, where `λ` is the
decreasing enumeration `LinearMap.IsSymmetric.eigenvalues` of the eigenvalues
of the symmetric operator `T`. -/
lemma exists_unit_vector_re_inner_le_eigenvalue
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n)
    (V : Submodule 𝕜 E) (hV : finrank 𝕜 V = (k : ℕ) + 1) :
    ∃ x ∈ V, ‖x‖ = 1 ∧ RCLike.re ⟪T x, x⟫_𝕜 ≤ hT.eigenvalues hn k := by
  set b := hT.eigenvectorBasis hn
  set W := b.spanIndices ↑(Finset.Ici k) with hW
  have hWdim : finrank 𝕜 W = n - (k : ℕ) := by
    rw [hW, b.finrank_spanIndices, Fin.card_Ici]
  -- Dimension counting: `finrank V + finrank W > finrank E`, so `V ⊓ W ≠ ⊥`.
  have hsum : finrank 𝕜 V + finrank 𝕜 W = n + 1 := by
    rw [hV, hWdim]
    have hk : (k : ℕ) < n := k.2
    omega
  have hinf : V ⊓ W ≠ ⊥ :=
    Submodule.inf_ne_bot_of_finrank_lt (by omega)
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  obtain ⟨hzV, hzW⟩ := Submodule.mem_inf.mp hz
  have hz0' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  set x := ((‖z‖⁻¹ : ℝ) : 𝕜) • z with hx
  have hnx : ‖x‖ = 1 := by
    rw [hx, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hz0']
  refine ⟨x, V.smul_mem _ hzV, hnx, ?_⟩
  -- The unit vector still lies in `W`; on `W` the selected eigenvalues are all `≤ λₖ`
  -- (antitone), so the spectral-subspace bound gives `re ⟪T x, x⟫ ≤ λₖ · ‖x‖² = λₖ`.
  have hxW : x ∈ W := W.smul_mem _ hzW
  calc RCLike.re ⟪T x, x⟫_𝕜
      ≤ hT.eigenvalues hn k * ‖x‖ ^ 2 :=
        hT.re_inner_apply_self_le_of_mem_spanIndices hn
          (fun _ hik => hT.eigenvalues_antitone hn (by simpa using hik)) hxW
    _ = hT.eigenvalues hn k := by rw [hnx]; ring

/-- **Courant–Fischer, lower direction.** There is a subspace `V` of dimension
`k + 1` on which every unit vector `x` satisfies `λₖ(T) ≤ re ⟪T x, x⟫`, where
`λ` is the decreasing enumeration `LinearMap.IsSymmetric.eigenvalues` of the
eigenvalues of the symmetric operator `T`.

Witness: `V = span {bᵢ : i ≤ k}`; on it the quadratic form is bounded below by
`λₖ` since all involved eigenvalues are `≥ λₖ`. -/
lemma exists_submodule_forall_unit_eigenvalue_le_re_inner
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n) :
    ∃ V : Submodule 𝕜 E, finrank 𝕜 V = (k : ℕ) + 1 ∧
      ∀ x ∈ V, ‖x‖ = 1 → hT.eigenvalues hn k ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  set b := hT.eigenvectorBasis hn
  refine ⟨b.spanIndices ↑(Finset.Iic k), ?_, ?_⟩
  · rw [b.finrank_spanIndices, Fin.card_Iic]
  · intro x hxV hnx
    -- On this subspace the selected eigenvalues are all `≥ λₖ` (antitone), so the dual
    -- spectral-subspace bound gives `λₖ = λₖ · ‖x‖² ≤ re ⟪T x, x⟫`.
    calc hT.eigenvalues hn k
        = hT.eigenvalues hn k * ‖x‖ ^ 2 := by rw [hnx]; ring
      _ ≤ RCLike.re ⟪T x, x⟫_𝕜 :=
          hT.le_re_inner_apply_self_of_mem_spanIndices hn
            (fun _ hik => hT.eigenvalues_antitone hn (by simpa using hik)) hxV

/-! ### A.3. The Courant–Fischer min-max equality -/

/-- **Courant–Fischer min-max equality.** The `k`-th (decreasingly sorted)
eigenvalue of a symmetric operator on a finite-dimensional inner product space
over `𝕜 = ℝ, ℂ` is the supremum, over the subspaces `V` of dimension `k + 1`,
of the infimum of the Rayleigh quotient `re ⟪T x, x⟫` over the unit vectors of
`V`.

Horn & Johnson, *Matrix Analysis* 2nd ed., Theorem 4.2.6. -/
lemma eigenvalues_eq_iSup_iInf_re_inner
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n) :
    hT.eigenvalues hn k =
      ⨆ V : {V : Submodule 𝕜 E // finrank 𝕜 V = (k : ℕ) + 1},
        ⨅ x : {x : E // x ∈ (V : Submodule 𝕜 E) ∧ ‖x‖ = 1},
          RCLike.re ⟪T (x : E), (x : E)⟫_𝕜 := by
  have hn0 : 0 < n := k.pos
  -- Uniform Rayleigh lower bound: every unit vector has quadratic form at least
  -- the smallest eigenvalue; this bounds every inner infimum below.
  set m : Fin n := ⟨n - 1, by omega⟩ with hm
  have hray : ∀ x : E, ‖x‖ = 1 →
      hT.eigenvalues hn m ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
    intro x hx
    rw [hT.re_inner_apply_self_eq_sum_eigenvalues_mul_sq hn x,
      -- states the goal with the definition unfolded, in the shape the next step needs;
      -- there is no `_apply` lemma to rewrite with here.
      show hT.eigenvalues hn m = ∑ i : Fin n,
          hT.eigenvalues hn m * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 by
        rw [← Finset.mul_sum, sum_sq_norm_repr_eq_sq_norm, hx]; ring]
    refine Finset.sum_le_sum fun i _ => ?_
    refine mul_le_mul_of_nonneg_right
      (hT.eigenvalues_antitone hn ?_) (sq_nonneg _)
    rw [Fin.le_def]
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change (i : ℕ) ≤ n - 1
    have := i.2
    omega
  have hbddB : ∀ V : {V : Submodule 𝕜 E // finrank 𝕜 V = (k : ℕ) + 1},
      BddBelow (Set.range fun x : {x : E // x ∈ (V : Submodule 𝕜 E) ∧ ‖x‖ = 1} =>
        RCLike.re ⟪T (x : E), (x : E)⟫_𝕜) := by
    intro V
    exact ⟨hT.eigenvalues hn m, by rintro _ ⟨x, rfl⟩; exact hray _ x.2.2⟩
  -- Every inner infimum is at most `λₖ` (upper direction).
  have hupper : ∀ V : {V : Submodule 𝕜 E // finrank 𝕜 V = (k : ℕ) + 1},
      (⨅ x : {x : E // x ∈ (V : Submodule 𝕜 E) ∧ ‖x‖ = 1},
        RCLike.re ⟪T (x : E), (x : E)⟫_𝕜) ≤ hT.eigenvalues hn k := by
    intro V
    obtain ⟨x, hxV, hx1, hxle⟩ :=
      hT.exists_unit_vector_re_inner_le_eigenvalue hn k V.1 V.2
    exact (ciInf_le (hbddB V) ⟨x, hxV, hx1⟩).trans hxle
  -- The lower-direction witness subspace attains `λₖ` from below.
  obtain ⟨V₀, hV₀dim, hV₀low⟩ :=
    hT.exists_submodule_forall_unit_eigenvalue_le_re_inner hn k
  have : Nonempty {V : Submodule 𝕜 E // finrank 𝕜 V = (k : ℕ) + 1} :=
    ⟨⟨V₀, hV₀dim⟩⟩
  obtain ⟨x₀, hx₀V, hx₀1, -⟩ :=
    hT.exists_unit_vector_re_inner_le_eigenvalue hn k V₀ hV₀dim
  refine le_antisymm ?_ (ciSup_le hupper)
  have hlow : hT.eigenvalues hn k ≤
      ⨅ x : {x : E // x ∈ ((⟨V₀, hV₀dim⟩ :
          {V : Submodule 𝕜 E // finrank 𝕜 V = (k : ℕ) + 1}) :
            Submodule 𝕜 E) ∧ ‖x‖ = 1},
        RCLike.re ⟪T (x : E), (x : E)⟫_𝕜 := by
    have : Nonempty {x : E // x ∈ V₀ ∧ ‖x‖ = 1} := ⟨⟨x₀, hx₀V, hx₀1⟩⟩
    exact le_ciInf fun x => hV₀low _ x.2.1 x.2.2
  have hbddA : BddAbove (Set.range
      fun V : {V : Submodule 𝕜 E // finrank 𝕜 V = (k : ℕ) + 1} =>
        ⨅ x : {x : E // x ∈ (V : Submodule 𝕜 E) ∧ ‖x‖ = 1},
          RCLike.re ⟪T (x : E), (x : E)⟫_𝕜) :=
    ⟨hT.eigenvalues hn k, by rintro _ ⟨V, rfl⟩; exact hupper V⟩
  exact hlow.trans (le_ciSup hbddA ⟨V₀, hV₀dim⟩)

/-! ### A.4. Sorted-eigenvalue uniqueness and Loewner monotonicity

Courant–Fischer consequences needed by the Ky Fan / unitarily-invariant-norm
development: an antitone list diagonalizing a symmetric operator in *some*
orthonormal basis is *the* sorted eigenvalue list, and the sorted eigenvalues
are monotone in the quadratic form (Loewner order). -/

/-- **Sorted-eigenvalue uniqueness.**  If an orthonormal basis `w`
diagonalizes the symmetric operator `S` with an *antitone* value list `μ`,
then `μ` is the sorted eigenvalue list: `hS.eigenvalues hn = μ`.
(Courant–Fischer: both lists satisfy the same minimax characterization.) -/
lemma eigenvalues_eq_of_eigenbasis
    (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) (w : OrthonormalBasis (Fin n) 𝕜 E)
    {μ : Fin n → ℝ} (hμ : Antitone μ) (hw : ∀ i, S (w i) = (μ i : 𝕜) • w i) :
    hS.eigenvalues hn = μ := by
  funext k
  refine le_antisymm ?_ ?_
  · -- `λₖ ≤ μₖ`: intersect the CF-lower witness with the `w`-tail span.
    obtain ⟨V, hVdim, hVlow⟩ :=
      hS.exists_submodule_forall_unit_eigenvalue_le_re_inner hn k
    set W := w.spanIndices ↑(Finset.Ici k) with hW
    have hWdim : finrank 𝕜 W = n - (k : ℕ) := by
      rw [hW, w.finrank_spanIndices, Fin.card_Ici]
    have hinf : V ⊓ W ≠ ⊥ :=
      Submodule.inf_ne_bot_of_finrank_lt (by have hk : (k : ℕ) < n := k.2; omega)
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
    obtain ⟨hzV, hzW⟩ := Submodule.mem_inf.mp hz
    have hz0' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
    set x := ((‖z‖⁻¹ : ℝ) : 𝕜) • z with hx
    have hnx : ‖x‖ = 1 := by
      rw [hx, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hz0']
    have hxW : x ∈ W := W.smul_mem _ hzW
    calc hS.eigenvalues hn k ≤ RCLike.re ⟪S x, x⟫_𝕜 := hVlow x (V.smul_mem _ hzV) hnx
      _ ≤ μ k * ‖x‖ ^ 2 :=
          re_inner_le_of_eigenbasis hS w hw (fun _ hik => hμ (by simpa using hik)) hxW
      _ = μ k := by rw [hnx]; ring
  · -- `μₖ ≤ λₖ`: test the CF-upper bound on the `w`-head span.
    set V := w.spanIndices ↑(Finset.Iic k) with hV
    have hVdim : finrank 𝕜 V = (k : ℕ) + 1 := by
      rw [hV, w.finrank_spanIndices, Fin.card_Iic]
    obtain ⟨x, hxV, hnx, hup⟩ :=
      hS.exists_unit_vector_re_inner_le_eigenvalue hn k V hVdim
    calc μ k = μ k * ‖x‖ ^ 2 := by rw [hnx]; ring
      _ ≤ RCLike.re ⟪S x, x⟫_𝕜 :=
          le_re_inner_of_eigenbasis hS w hw (fun _ hik => hμ (by simpa using hik)) hxV
      _ ≤ hS.eigenvalues hn k := hup

/-- **Loewner monotonicity of the sorted eigenvalues.**  If the quadratic form
of `T` is dominated by that of `S`, then so is every sorted eigenvalue. -/
lemma eigenvalue_mono
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (h : ∀ x, RCLike.re ⟪T x, x⟫_𝕜 ≤ RCLike.re ⟪S x, x⟫_𝕜) (k : Fin n) :
    hT.eigenvalues hn k ≤ hS.eigenvalues hn k := by
  obtain ⟨V, hVdim, hVlow⟩ :=
    hT.exists_submodule_forall_unit_eigenvalue_le_re_inner hn k
  obtain ⟨x, hxV, hnx, hup⟩ :=
    hS.exists_unit_vector_re_inner_le_eigenvalue hn k V hVdim
  calc hT.eigenvalues hn k ≤ RCLike.re ⟪T x, x⟫_𝕜 := hVlow x hxV hnx
    _ ≤ RCLike.re ⟪S x, x⟫_𝕜 := h x
    _ ≤ hS.eigenvalues hn k := hup

/-- The span of a selected subfamily of the eigenbasis of a symmetric operator
is invariant under the operator. -/
lemma map_mem_spanIndices (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (s : Set (Fin n)) {x : E}
    (hx : x ∈ (hT.eigenvectorBasis hn).spanIndices s) :
    T x ∈ (hT.eigenvectorBasis hn).spanIndices s := by
  rw [OrthonormalBasis.spanIndices_eq_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    rw [hT.apply_eigenvectorBasis hn j]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

end LinearMap.IsSymmetric

/-! ### A.5. Weyl's inequality -/

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E}

/-- One-sided Weyl bound: `λₖ(S) − λₖ(T) ≤ ‖S − T‖op`.  This is the core
estimate; Weyl's inequality follows by symmetry.

We take a witness subspace `V` of dimension `k + 1` on which
`λₖ(S) ≤ re ⟪S x, x⟫` (lower direction for `S`), then a unit vector `x ∈ V`
with `re ⟪T x, x⟫ ≤ λₖ(T)` (upper direction for `T`).  The difference is
controlled by Cauchy–Schwarz. -/
private lemma eigenvalues_sub_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) (k : Fin n) :
    hS.eigenvalues hn k - hT.eigenvalues hn k ≤ ε := by
  obtain ⟨V, hVdim, hVlow⟩ :=
    hS.exists_submodule_forall_unit_eigenvalue_le_re_inner hn k
  obtain ⟨x, hxV, hnx, hTup⟩ :=
    hT.exists_unit_vector_re_inner_le_eigenvalue hn k V hVdim
  have hSlow : hS.eigenvalues hn k ≤ RCLike.re ⟪S x, x⟫_𝕜 := hVlow x hxV hnx
  -- `λₖ(S) − λₖ(T) ≤ re ⟪Sx,x⟫ − re ⟪Tx,x⟫ = re ⟪(S−T)x,x⟫ ≤ ‖(S−T)x‖ ≤ ε`.
  have hdiff : RCLike.re ⟪S x, x⟫_𝕜 - RCLike.re ⟪T x, x⟫_𝕜
      = RCLike.re ⟪(S - T) x, x⟫_𝕜 := by
    rw [LinearMap.sub_apply, inner_sub_left, map_sub]
  have hcs : RCLike.re ⟪(S - T) x, x⟫_𝕜 ≤ ‖(S - T) x‖ * ‖x‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hbnd : ‖(S - T) x‖ * ‖x‖ ≤ ε := by
    simpa [hnx] using hε x
  calc hS.eigenvalues hn k - hT.eigenvalues hn k
      ≤ RCLike.re ⟪S x, x⟫_𝕜 - RCLike.re ⟪T x, x⟫_𝕜 := by linarith
    _ = RCLike.re ⟪(S - T) x, x⟫_𝕜 := hdiff
    _ ≤ ‖(S - T) x‖ * ‖x‖ := hcs
    _ ≤ ε := hbnd

/-- **Weyl's inequality** for symmetric operators on a finite-dimensional inner
product space over `𝕜 = ℝ, ℂ`: the `k`-th (decreasingly sorted) eigenvalues of
`T` and `S` differ by at most the operator norm of `T − S`.

At `LinearMap` level there is no operator norm, so the bound is supplied as the
pointwise hypothesis `∀ x, ‖(T − S) x‖ ≤ ε * ‖x‖`; see
`LinearMap.IsSymmetric.abs_eigenvalue_sub_eigenvalue_le_norm` for the continuous-linear-map
operator-norm form.

Horn & Johnson, *Matrix Analysis* 2nd ed., Theorem 4.3.1; Bhatia,
*Matrix Analysis*, Corollary III.2.6. -/
lemma abs_eigenvalue_sub_eigenvalue_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(T - S) x‖ ≤ ε * ‖x‖) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤ ε := by
  -- The two directions of `eigenvalues_sub_le`, with the roles of `T` and `S`
  -- swapped, using `‖(T − S) x‖ = ‖(S − T) x‖`.
  have hεsymm : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖ := by
    intro x
    have : (S - T) x = -((T - S) x) := by
      rw [LinearMap.sub_apply, LinearMap.sub_apply]; abel
    rw [this, norm_neg]; exact hε x
  rw [abs_le]
  constructor
  · have := eigenvalues_sub_le hT hS hn hεsymm k
    linarith
  · have := eigenvalues_sub_le hS hT hn hε k
    linarith

/-- **Weyl's inequality**, operator-norm form, for symmetric (equivalently,
self-adjoint) continuous linear maps on a finite-dimensional inner product
space: the `k`-th sorted eigenvalues of `T` and `S` differ by at most
`‖T − S‖`.  The symmetry hypotheses are stated on the underlying linear maps
so that the signature does not require the adjoint star structure (whose
instance needs `CompleteSpace E`, which `FiniteDimensional` deliberately does
not register as an instance).

The bound is expressed directly in the norm of a continuous linear map. -/
lemma abs_eigenvalue_sub_eigenvalue_le_norm
    {T S : E →L[𝕜] E}
    (hT : LinearMap.IsSymmetric (T : E →ₗ[𝕜] E))
    (hS : LinearMap.IsSymmetric (S : E →ₗ[𝕜] E))
    (hn : finrank 𝕜 E = n) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤ ‖T - S‖ := by
  refine abs_eigenvalue_sub_eigenvalue_le hT hS hn (fun x => ?_) k
  simpa using (T - S).le_opNorm x

/-- Weyl's inequality for linear maps, using the operator norm of the
corresponding continuous linear map.  Unlike the preceding theorem, the symmetry
hypotheses and eigenvalue enumeration are directly attached to `LinearMap`s. -/
lemma abs_eigenvalues_sub_le_opNorm
    {T S : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k|
      ≤ ‖LinearMap.toContinuousLinearMap (T - S)‖ := by
  refine abs_eigenvalue_sub_eigenvalue_le hT hS hn (fun x => ?_) k
  have hx := (LinearMap.toContinuousLinearMap (T - S)).le_opNorm x
  rwa [LinearMap.coe_toContinuousLinearMap'] at hx

/-- Sorted eigenvalues are congruent along an operator equality (the eigenvalue
enumeration depends only on the operator, not on the symmetry proof). -/
lemma eigenvalues_congr {S₁ S₂ : E →ₗ[𝕜] E} (h : S₁ = S₂)
    (hS₁ : S₁.IsSymmetric) (hS₂ : S₂.IsSymmetric) (hn : finrank 𝕜 E = n) :
    hS₁.eigenvalues hn = hS₂.eigenvalues hn := by
  subst h; rfl

/-- The eigenvalue enumeration does not depend on which witness of the dimension indexes
it: two witnesses `finrank 𝕜 E = m` and `finrank 𝕜 E = n` enumerate the same eigenvalues,
read across the induced `Fin m ≃ Fin n`.

Both spellings occur in practice.  A matrix over `Fin n` has
`Matrix.IsHermitian.eigenvalues₀` indexed by `Fin (Fintype.card (Fin n))`, while the
operator theory it is transported to indexes by `Fin n`; `Fintype.card (Fin n) = n` is a
theorem and not definitional, so the two index types are genuinely different. -/
lemma eigenvalues_cast {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {m : ℕ}
    (hm : finrank 𝕜 E = m) (hn : finrank 𝕜 E = n) (hmn : m = n) (i : Fin m) :
    hT.eigenvalues hm i = hT.eigenvalues hn (Fin.cast hmn i) := by
  subst hmn; rfl

/-! ### A.6. Courant–Fischer on subspaces of larger dimension -/

/-- **Courant–Fischer, upper direction, for large subspaces.** On any subspace `W` of dimension
at least `k + 1` there is a unit vector `x` with `re ⟪T x, x⟫ ≤ λₖ(T)`. -/
lemma exists_unit_vector_re_inner_le_eigenvalue_of_le
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n)
    (W : Submodule 𝕜 E) (hW : (k : ℕ) + 1 ≤ finrank 𝕜 W) :
    ∃ x ∈ W, ‖x‖ = 1 ∧ RCLike.re ⟪T x, x⟫_𝕜 ≤ hT.eigenvalues hn k := by
  set b := hT.eigenvectorBasis hn
  set U := b.spanIndices ↑(Finset.Ici k) with hU
  have hUdim : finrank 𝕜 U = n - (k : ℕ) := by
    rw [hU, b.finrank_spanIndices, Fin.card_Ici]
  have hk : (k : ℕ) < n := k.2
  have hinf : W ⊓ U ≠ ⊥ :=
    Submodule.inf_ne_bot_of_finrank_lt (by omega)
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  obtain ⟨hzW, hzU⟩ := Submodule.mem_inf.mp hz
  have hz0' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  set x := ((‖z‖⁻¹ : ℝ) : 𝕜) • z with hx
  have hnx : ‖x‖ = 1 := by
    rw [hx, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hz0']
  refine ⟨x, W.smul_mem _ hzW, hnx, ?_⟩
  have hxU : x ∈ U := U.smul_mem _ hzU
  calc RCLike.re ⟪T x, x⟫_𝕜
      ≤ hT.eigenvalues hn k * ‖x‖ ^ 2 :=
        hT.re_inner_apply_self_le_of_mem_spanIndices hn
          (fun _ hik => hT.eigenvalues_antitone hn (by simpa using hik)) hxU
    _ = hT.eigenvalues hn k := by rw [hnx]; ring

/-! ### A.7. Cauchy interlacing and Rayleigh–Ritz bounds -/

section Interlacing

variable {m : ℕ} {V : Submodule 𝕜 E} {A : V →ₗ[𝕜] V}

/-- **Upper Cauchy interlacing.** If the quadratic form of the symmetric operator `A` on `V`
agrees with that of `T`, then `μₖ(A) ≤ λₖ(T)` for every `k < m`. -/
lemma eigenvalue_compression_le
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (hA : A.IsSymmetric) (hm : finrank 𝕜 V = m)
    (hcomp : ∀ y : V, RCLike.re ⟪A y, y⟫_𝕜 = RCLike.re ⟪T y, y⟫_𝕜)
    (k : Fin m) (hk : (k : ℕ) < n) :
    hA.eigenvalues hm k ≤ hT.eigenvalues hn ⟨k, hk⟩ := by
  obtain ⟨W, hWdim, hWlow⟩ := hA.exists_submodule_forall_unit_eigenvalue_le_re_inner hm k
  obtain ⟨x, hxW, hnx, hx⟩ :=
    hT.exists_unit_vector_re_inner_le_eigenvalue hn ⟨k, hk⟩ (W.map V.subtype)
      (by rw [Submodule.finrank_map_subtype_eq, hWdim])
  obtain ⟨y, hyW, rfl⟩ := Submodule.mem_map.mp hxW
  have hny : ‖y‖ = 1 := by simpa using hnx
  calc hA.eigenvalues hm k ≤ RCLike.re ⟪A y, y⟫_𝕜 := hWlow y hyW hny
    _ = RCLike.re ⟪T y, y⟫_𝕜 := hcomp y
    _ ≤ hT.eigenvalues hn ⟨k, hk⟩ := hx

/-- **Lower Cauchy interlacing.** If the quadratic form of the symmetric operator `A` on `V`
agrees with that of `T`, then `λ_{k + (n - m)}(T) ≤ μₖ(A)` for every `k < m`. -/
lemma eigenvalue_le_eigenvalue_compression
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (hA : A.IsSymmetric) (hm : finrank 𝕜 V = m)
    (hcomp : ∀ y : V, RCLike.re ⟪A y, y⟫_𝕜 = RCLike.re ⟪T y, y⟫_𝕜)
    (k : Fin m) (hmn : m ≤ n) :
    hT.eigenvalues hn ⟨k + (n - m), by omega⟩ ≤ hA.eigenvalues hm k := by
  set j : Fin n := ⟨k + (n - m), by omega⟩ with hj
  obtain ⟨U, hUdim, hUlow⟩ := hT.exists_submodule_forall_unit_eigenvalue_le_re_inner hn j
  set W : Submodule 𝕜 V := (U ⊓ V).comap V.subtype with hW
  have hWdim : (k : ℕ) + 1 ≤ finrank 𝕜 W := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U V
    have h2 : finrank 𝕜 ↥(U ⊔ V) ≤ n := hn ▸ Submodule.finrank_le _
    have h3 : finrank 𝕜 W = finrank 𝕜 ↥(U ⊓ V) :=
      (Submodule.comapSubtypeEquivOfLe (inf_le_right : U ⊓ V ≤ V)).finrank_eq
    have h4 : (j : ℕ) = k + (n - m) := rfl
    have hkm : (k : ℕ) < m := k.2
    omega
  obtain ⟨y, hyW, hny, hy⟩ := hA.exists_unit_vector_re_inner_le_eigenvalue_of_le hm k W hWdim
  have hyU : (y : E) ∈ U := (Submodule.mem_inf.mp (Submodule.mem_comap.mp hyW)).1
  calc hT.eigenvalues hn j ≤ RCLike.re ⟪T y, y⟫_𝕜 := hUlow _ hyU (by simpa using hny)
    _ = RCLike.re ⟪A y, y⟫_𝕜 := (hcomp y).symm
    _ ≤ hA.eigenvalues hm k := hy

/-- **Hylleraas–Undheim–MacDonald.** In ascending order, the `k`-th lowest Ritz value is an upper
bound for the `k`-th lowest exact eigenvalue: `λ↑ₖ(T) ≤ μ↑ₖ(S)` for every `k < m`. -/
lemma eigenvalue_ascending_le_ritz
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (hA : A.IsSymmetric) (hm : finrank 𝕜 V = m)
    (hcomp : ∀ y : V, RCLike.re ⟪A y, y⟫_𝕜 = RCLike.re ⟪T y, y⟫_𝕜)
    (hmn : m ≤ n) (k : ℕ) (hk : k < m) :
    hT.eigenvalues hn ⟨n - 1 - k, by omega⟩ ≤ hA.eigenvalues hm ⟨m - 1 - k, by omega⟩ := by
  have h := hT.eigenvalue_le_eigenvalue_compression hn hA hm hcomp ⟨m - 1 - k, by omega⟩ hmn
  have hidx : (⟨n - 1 - k, by omega⟩ : Fin n) = ⟨(m - 1 - k) + (n - m), by omega⟩ := by
    ext; simp only; omega
  rw [hidx]
  exact h

/-- **Variational ground-state bound.** The lowest Ritz value bounds the lowest exact eigenvalue
from above. -/
lemma eigenvalue_min_le_ritz_min
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (hA : A.IsSymmetric) (hm : finrank 𝕜 V = m)
    (hcomp : ∀ y : V, RCLike.re ⟪A y, y⟫_𝕜 = RCLike.re ⟪T y, y⟫_𝕜)
    (hmn : m ≤ n) (hm0 : 0 < m) :
    hT.eigenvalues hn ⟨n - 1, by omega⟩ ≤ hA.eigenvalues hm ⟨m - 1, by omega⟩ := by
  simpa using hT.eigenvalue_ascending_le_ritz hn hA hm hcomp hmn 0 hm0

end Interlacing

/-! ### A.8. The orthogonal compression -/

/-- The compression `P_V ∘ T ∘ ι_V` of `T` to the subspace `V` (the Ritz operator). -/
noncomputable def compression (_hT : T.IsSymmetric) (V : Submodule 𝕜 E) : V →ₗ[𝕜] V :=
  (V.orthogonalProjectionOnto : E →ₗ[𝕜] V) ∘ₗ T ∘ₗ V.subtype

/-- The compression has the inner products of `T` against vectors of `V`. -/
lemma inner_compression_left (hT : T.IsSymmetric) (V : Submodule 𝕜 E) (y z : V) :
    ⟪hT.compression V y, z⟫_𝕜 = ⟪T y, z⟫_𝕜 := by
  simp [compression]

/-- The compression of a symmetric operator is symmetric. -/
lemma compression_isSymmetric (hT : T.IsSymmetric) (V : Submodule 𝕜 E) :
    (hT.compression V).IsSymmetric := by
  intro y z
  rw [inner_compression_left, hT]
  simp [compression]

/-- The compression has the quadratic form of `T` on `V`, as required by the interlacing
lemmas. -/
lemma re_inner_compression (hT : T.IsSymmetric) (V : Submodule 𝕜 E) (y : V) :
    RCLike.re ⟪hT.compression V y, y⟫_𝕜 = RCLike.re ⟪T y, y⟫_𝕜 := by
  rw [inner_compression_left]

end LinearMap.IsSymmetric

end
