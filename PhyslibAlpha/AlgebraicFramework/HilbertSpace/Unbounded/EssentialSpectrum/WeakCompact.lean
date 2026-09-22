/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem, Adam Bornemann
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Sequences

/-!

# Compact operators kill weakly-null sequences

Ported, essentially verbatim, from `adambornemann-glitch/Spectra`'s
`SpectralTheory/Essential/WeakCompact.lean` (Apache 2.0). Self-contained Hilbert-space facts, not
tied to any particular unbounded-operator type — the two analytic linchpins behind Weyl's theorem
on the essential spectrum (`Weyl.lean`):

* `Orthonormal.tendsto_inner_atTop_zero` — an orthonormal sequence is *weakly null*: for every
  fixed `g`, `⟪g, ψ n⟫ → 0`. This is Bessel's inequality plus "summable ⟹ terms → 0".

* `IsCompactOperator.tendsto_norm_apply_of_weaklyNull` — a **compact** operator maps a bounded
  weakly-null sequence to a norm-null sequence. This is the single fact that makes the
  perturbation argument work: a compact piece does not see the (weakly vanishing) approximate
  eigenvectors.

Both statements phrase weak convergence *concretely* (`∀ g, ⟪g, u n⟫ → 0`), never via the weak
topology — so the proofs use only `IsCompact.tendsto_subseq` and the continuity of the inner
product, avoiding Banach–Alaoglu entirely.

-/

@[expose] public section

noncomputable section

open Filter Topology
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- An orthonormal sequence is **weakly null**: for every fixed `g`, the inner products
`⟪g, ψ n⟫` tend to `0`. (Bessel's inequality makes `∑ ‖⟪ψ n, g⟫‖²` summable, so its terms — hence
`‖⟪g, ψ n⟫‖` — tend to `0`.) -/
theorem Orthonormal.tendsto_inner_atTop_zero {ψ : ℕ → H} (hψ : Orthonormal ℂ ψ) (g : H) :
    Tendsto (fun n => ⟪g, ψ n⟫_ℂ) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => ‖⟪ψ n, g⟫_ℂ‖ ^ 2) atTop (𝓝 0) :=
    (hψ.inner_products_summable g).tendsto_atTop_zero
  have hnorm : Tendsto (fun n => ‖⟪ψ n, g⟫_ℂ‖) atTop (𝓝 0) := by
    have key : (fun n => ‖⟪ψ n, g⟫_ℂ‖) = fun n => Real.sqrt (‖⟪ψ n, g⟫_ℂ‖ ^ 2) := by
      funext n; rw [Real.sqrt_sq (norm_nonneg _)]
    rw [key]
    exact Real.sqrt_zero ▸ (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have heq : (fun n => ‖⟪g, ψ n⟫_ℂ‖) = fun n => ‖⟪ψ n, g⟫_ℂ‖ :=
    funext fun n => norm_inner_symm g (ψ n)
  rw [heq]; exact hnorm

/-- A **compact** operator maps a bounded weakly-null sequence to a norm-null sequence.

`hbdd` bounds the sequence (`‖u n‖ ≤ C`); `hweak` is weak nullness stated concretely as
`∀ g, ⟪g, u n⟫ → 0`. The proof: if `‖K (u n)‖` does *not* tend to `0`, extract a subsequence on
which it stays `≥ ε`; it lands in the compact set `closure (K '' closedBall 0 C)`, so a further
subsequence converges in norm to some `a`; weak nullness (via the adjoint) forces `⟪a, a⟫ = 0`,
i.e. `a = 0`, contradicting `ε ≤ ‖a‖`. -/
theorem IsCompactOperator.tendsto_norm_apply_of_weaklyNull
    {K : H →L[ℂ] H} (hK : IsCompactOperator (K : H → H)) {u : ℕ → H} {C : ℝ}
    (hbdd : ∀ n, ‖u n‖ ≤ C)
    (hweak : ∀ g : H, Tendsto (fun n => ⟪g, u n⟫_ℂ) atTop (𝓝 0)) :
    Tendsto (fun n => ‖K (u n)‖) atTop (𝓝 0) := by
  by_contra hcon
  rw [Metric.tendsto_atTop] at hcon
  push Not at hcon
  obtain ⟨ε, hε, hfreq⟩ := hcon
  -- Frequently, `‖K (u n)‖ ≥ ε`.
  have hfreq' : ∃ᶠ n in atTop, ε ≤ ‖K (u n)‖ := by
    rw [frequently_atTop]
    intro N
    obtain ⟨n, hn, hdist⟩ := hfreq N
    exact ⟨n, hn, by rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hdist⟩
  obtain ⟨φ, hφ_mono, hφ⟩ := extraction_of_frequently_atTop hfreq'
  -- The tail lands in a fixed compact set.
  obtain ⟨S, hS_compact, hS_sub⟩ :=
    IsCompactOperator.image_closedBall_subset_compact (f := (K : H →ₗ[ℂ] H)) hK C
  have hmem : ∀ n, K (u (φ n)) ∈ S := by
    intro n
    apply hS_sub
    exact ⟨u (φ n), by simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hbdd (φ n), rfl⟩
  obtain ⟨a, _, ψ, hψ_mono, hψ_tend⟩ := hS_compact.tendsto_subseq hmem
  -- Weak nullness identifies the limit as `0`.
  have ha0 : a = 0 := by
    have h1 : Tendsto (fun n => ⟪a, K (u (φ (ψ n)))⟫_ℂ) atTop (𝓝 ⟪a, a⟫_ℂ) :=
      Tendsto.inner tendsto_const_nhds hψ_tend
    have h2 : Tendsto (fun n => ⟪a, K (u (φ (ψ n)))⟫_ℂ) atTop (𝓝 0) := by
      have hcomp : Tendsto (fun n => φ (ψ n)) atTop atTop :=
        (hφ_mono.comp hψ_mono).tendsto_atTop
      have hw : Tendsto (fun n => ⟪ContinuousLinearMap.adjoint K a, u (φ (ψ n))⟫_ℂ) atTop (𝓝 0) :=
        (hweak (ContinuousLinearMap.adjoint K a)).comp hcomp
      refine hw.congr (fun n => ?_)
      exact ContinuousLinearMap.adjoint_inner_left K (u (φ (ψ n))) a
    have hzero : ⟪a, a⟫_ℂ = 0 := tendsto_nhds_unique h1 h2
    exact inner_self_eq_zero.mp hzero
  -- But the norm along the subsequence stays `≥ ε`.
  have hnorm_tend : Tendsto (fun n => ‖K (u (φ (ψ n)))‖) atTop (𝓝 ‖a‖) := hψ_tend.norm
  have hε_le : ε ≤ ‖a‖ := ge_of_tendsto' hnorm_tend (fun n => hφ (ψ n))
  rw [ha0, norm_zero] at hε_le
  exact absurd hε_le (not_le.mpr hε)
