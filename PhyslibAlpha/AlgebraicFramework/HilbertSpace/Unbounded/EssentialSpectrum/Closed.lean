/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem, Adam Bornemann
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.EssentialSpectrum.Defs
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.SpecificLimits.Basic

/-!

# The essential spectrum is closed

Ported, essentially verbatim, from `adambornemann-glitch/Spectra`'s
`SpectralTheory/Essential/Closed.lean` (Apache 2.0).

`isClosed_essSpectrum` : for a self-adjoint operator `A`, `essSpectrum hA` is a closed subset
of `ℝ`.

The proof is the standard diagonal argument. Given `λ_k ∈ essSpectrum` with `λ_k → λ`, each `λ_k`
carries a singular sequence `(ψ_{k,n})_n`. All these vectors lie in a **separable** closed subspace
`K` (the closed span of the countable family), which has a countable dense subset `{d_j}`. Choosing
`n_k` so that `ψ_{k,n_k}` is simultaneously an approximate eigenvector of quality `1/(k+1)`,
approximately normalized, and almost orthogonal to `d_0,…,d_k`, the diagonal sequence
`φ_k := ψ_{k,n_k}` is a singular sequence for `λ` — weak nullness following from the orthogonal
projection onto `K` together with the dense subset.

-/

@[expose] public section

noncomputable section

open Filter Topology TopologicalSpace
open scoped InnerProductSpace

namespace QuantumMechanics.Essential

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The essential spectrum is closed. -/
theorem isClosed_essSpectrum {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    IsClosed (essSpectrum hA) := by
  rw [← isSeqClosed_iff_isClosed]
  intro lamSeq lamLim hmem hlim
  simp only [essSpectrum, Set.mem_ofPred_eq] at hmem
  choose ψ hψnorm hψweak hψeig using hmem
  -- The countable family of all vectors, and its separable closed span `K`.
  set S : Set H := Set.range (fun p : ℕ × ℕ => ((ψ p.1 p.2 : H))) with _hSdef
  have hScount : S.Countable := Set.countable_range _
  set K : Submodule ℂ H := (Submodule.span ℂ S).topologicalClosure with hKdef
  have hmemK : ∀ k n, ((ψ k n : H)) ∈ K :=
    fun k n => Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(k, n), rfl⟩)
  have hsep : IsSeparable (K : Set H) := by
    rw [hKdef, Submodule.topologicalClosure_coe]
    exact (hScount.isSeparable.span).closure
  obtain ⟨D, hDcount, hDsub⟩ := hsep
  have hDne : D.Nonempty :=
    closure_nonempty_iff.mp ⟨(0 : H), hDsub K.zero_mem⟩
  obtain ⟨d, hd⟩ := hDcount.exists_eq_range hDne
  -- Diagonal selection of indices `n_k`.
  have hchoose : ∀ k, ∃ n,
      ‖A (ψ k n) - (lamSeq k : ℂ) • (ψ k n : H)‖ < 1 / (k + 1) ∧
      |‖(ψ k n : H)‖ - 1| < 1 / (k + 1) ∧
      ∀ j ∈ Finset.range (k + 1), ‖⟪d j, (ψ k n : H)⟫_ℂ‖ < 1 / (k + 1) := by
    intro k
    have hpos : (0 : ℝ) < 1 / (k + 1) := by positivity
    have hlt : ∀ {f : ℕ → ℝ}, Tendsto f atTop (𝓝 0) → ∀ᶠ n in atTop, f n < 1 / (k + 1) :=
      fun {f} hf => (hf.eventually_mem (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hpos))).mono
        fun n hn => Set.mem_Iio.mp hn
    have E1 := hlt (hψeig k)
    have E2 : ∀ᶠ n in atTop, |‖(ψ k n : H)‖ - 1| < 1 / (k + 1) := by
      have h0 : Tendsto (fun n => |‖(ψ k n : H)‖ - 1|) atTop (𝓝 0) := by
        have := (hψnorm k).sub tendsto_const_nhds (b := (1 : ℝ))
        simpa using this.abs
      exact hlt h0
    have E3 : ∀ᶠ n in atTop, ∀ j ∈ Finset.range (k + 1),
        ‖⟪d j, (ψ k n : H)⟫_ℂ‖ < 1 / (k + 1) := by
      rw [eventually_all_finset]
      exact fun j _ => hlt (by simpa using (hψweak k (d j)).norm)
    obtain ⟨n, ⟨hn1, hn2⟩, hn3⟩ := ((E1.and E2).and E3).exists
    exact ⟨n, hn1, hn2, hn3⟩
  choose nidx hEig hNorm hWeak using hchoose
  -- The diagonal sequence.
  refine ⟨fun k => ψ k (nidx k), ?_, ?_, ?_⟩
  · -- `‖φ k‖ → 1`.
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hε))).exists_forall_of_atTop
    refine ⟨N, fun k hk => ?_⟩
    have := hNorm k
    rw [Real.dist_eq, abs_sub_comm]
    calc |1 - ‖(ψ k (nidx k) : H)‖| = |‖(ψ k (nidx k) : H)‖ - 1| := abs_sub_comm _ _
      _ < 1 / (k + 1) := this
      _ < ε := Set.mem_Iio.mp (hN k hk)
  · -- `φ` weakly null.
    intro g
    set pg : H := K.starProjection g with _hpgdef
    have hproj : ∀ k, ⟪g, (ψ k (nidx k) : H)⟫_ℂ = ⟪pg, (ψ k (nidx k) : H)⟫_ℂ := by
      intro k
      have h0 : ⟪g - pg, (ψ k (nidx k) : H)⟫_ℂ = 0 :=
        K.starProjection_inner_eq_zero g (ψ k (nidx k) : H) (hmemK k (nidx k))
      rw [inner_sub_left, sub_eq_zero] at h0
      exact h0
    have hpgK : pg ∈ closure D := hDsub (K.starProjection_apply_mem g)
    have hbound : ∀ k, ‖(ψ k (nidx k) : H)‖ ≤ 2 := by
      intro k
      have h := abs_lt.mp (hNorm k)
      have hle1 : (1 : ℝ) / (k + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ k := by positivity
        linarith
      linarith [h.2]
    rw [Metric.tendsto_atTop]
    intro ε hε
    rw [Metric.mem_closure_iff] at hpgK
    obtain ⟨y, hyD, hy⟩ := hpgK (ε / 4) (by positivity)
    rw [hd] at hyD
    obtain ⟨jj, rfl⟩ := hyD
    obtain ⟨N₁, hN₁⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (isOpen_Iio.mem_nhds
      (Set.mem_Iio.mpr (show (0 : ℝ) < ε / 2 by positivity)))).exists_forall_of_atTop
    refine ⟨max jj N₁, fun k hk => ?_⟩
    have hkj : jj ≤ k := le_of_max_le_left hk
    have hkN : N₁ ≤ k := le_of_max_le_right hk
    rw [dist_eq_norm, sub_zero, hproj k]
    have hsplit : ⟪pg, (ψ k (nidx k) : H)⟫_ℂ
        = ⟪d jj, (ψ k (nidx k) : H)⟫_ℂ + ⟪pg - d jj, (ψ k (nidx k) : H)⟫_ℂ := by
      rw [← inner_add_left]; congr 1; abel
    calc ‖⟪pg, (ψ k (nidx k) : H)⟫_ℂ‖
        ≤ ‖⟪d jj, (ψ k (nidx k) : H)⟫_ℂ‖ + ‖⟪pg - d jj, (ψ k (nidx k) : H)⟫_ℂ‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ ≤ 1 / (k + 1) + ‖pg - d jj‖ * ‖(ψ k (nidx k) : H)‖ := by
          gcongr
          · exact le_of_lt (hWeak k jj (Finset.mem_range.mpr (by omega)))
          · exact norm_inner_le_norm _ _
      _ < ε / 2 + ε / 4 * 2 := by
          have h1 : 1 / (k + 1) < ε / 2 := Set.mem_Iio.mp (hN₁ k hkN)
          have h2 : ‖pg - d jj‖ * ‖(ψ k (nidx k) : H)‖ ≤ ε / 4 * 2 := by
            apply mul_le_mul (le_of_lt _) (hbound k) (norm_nonneg _) (by positivity)
            rwa [← dist_eq_norm]
          linarith
      _ = ε := by ring
  · -- `(A − λ) φ k → 0`.
    have hbnd : ∀ k, ‖A (ψ k (nidx k)) - (lamLim : ℂ) • (ψ k (nidx k) : H)‖
        ≤ 1 / (k + 1) + |lamSeq k - lamLim| * (1 + 1 / (k + 1)) := by
      intro k
      have key : A (ψ k (nidx k)) - (lamLim : ℂ) • (ψ k (nidx k) : H)
          = (A (ψ k (nidx k)) - (lamSeq k : ℂ) • (ψ k (nidx k) : H))
            + ((lamSeq k : ℂ) - lamLim) • (ψ k (nidx k) : H) := by module
      rw [key]
      refine (norm_add_le _ _).trans ?_
      gcongr
      · exact le_of_lt (hEig k)
      · rw [norm_smul]
        have hnk := abs_lt.mp (hNorm k)
        have hcast : ‖((lamSeq k : ℂ) - (lamLim : ℂ))‖ = |lamSeq k - lamLim| := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        rw [hcast]
        gcongr
        linarith [hnk.2]
    have hrhs : Tendsto (fun k => 1 / (k + 1) + |lamSeq k - lamLim| * (1 + 1 / (k + 1)))
        atTop (𝓝 0) := by
      have ha : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hb : Tendsto (fun k => |lamSeq k - lamLim|) atTop (𝓝 0) := by
        have h := hlim.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => lamLim) atTop (𝓝 lamLim))
        simpa using h.abs
      have hsum : Tendsto (fun k => (1 : ℝ) / (k + 1) + |lamSeq k - lamLim| * (1 + 1 / (k + 1)))
          atTop (𝓝 (0 + 0 * (1 + 0))) :=
        ha.add (hb.mul ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add ha))
      simpa using hsum
    exact squeeze_zero (fun k => norm_nonneg _) hbnd hrhs

end QuantumMechanics.Essential
