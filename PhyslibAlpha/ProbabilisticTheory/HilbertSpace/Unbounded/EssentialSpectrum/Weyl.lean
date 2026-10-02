/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem, Adam Bornemann
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.EssentialSpectrum.Defs
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.EssentialSpectrum.WeakCompact

/-!

# Weyl's theorem on the essential spectrum

## i. Overview

If the resolvents at `i` of two self-adjoint operators differ by a compact operator, the operators
have the same essential spectrum. The resolvents enter as bounded operators satisfying the defining
properties of the resolvent, `IsResolventAt`. In particular a relatively compact perturbation does
not change the essential spectrum.

## ii. Key results

- `IsResolventAt` : a bounded operator is the resolvent of a self-adjoint operator at `z`.
- `essSpectrum_eq_of_isCompactOperator_resolvent_sub` : **Weyl's theorem.**
- `essSpectrum_eq_of_isCompactOperator_perturb` : the essential spectrum is stable under relatively
  compact perturbations.

## iii. Table of contents

- A. The bounded resolvent
- B. Weyl's theorem
- C. Relatively compact perturbations

## iv. References

- Adapted from `adambornemann-glitch/Spectra`, `SpectralTheory/Essential/Weyl.lean` (Apache 2.0).

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open Filter Topology Complex
open scoped InnerProductSpace

namespace QuantumMechanics.Essential

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `i` is off the real axis, the spectral parameter used throughout. -/
lemma I_im_ne_zero : (Complex.I).im ≠ 0 := by rw [Complex.I_im]; exact one_ne_zero

/-! ## A. The bounded resolvent -/

/-- `R` is the resolvent of the self-adjoint operator `A` at `z`: it maps into the domain of `A`,
and inverts `A - z` on both sides. -/
structure IsResolventAt {A : H →ₗ.[ℂ] H} (_hA : IsSelfAdjoint A) (z : ℂ)
    (R : H →L[ℂ] H) : Prop where
  mem_domain : ∀ φ, R φ ∈ A.domain
  solves : ∀ φ, A ⟨R φ, mem_domain φ⟩ - z • R φ = φ
  left_inverse : ∀ ψ : A.domain, R (A ψ - z • (ψ : H)) = (ψ : H)

/-! ## B. Weyl's theorem -/

/-- **One inclusion of Weyl's theorem.** If the resolvent difference `R_B(i) − R_A(i)` is compact,
then `essSpectrum hA ⊆ essSpectrum hB`. -/
lemma essSpectrum_subset_of_isCompactOperator_resolvent_sub
    {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {RA RB : H →L[ℂ] H} (hRA : IsResolventAt hA I RA) (hRB : IsResolventAt hB I RB)
    (hcompact : IsCompactOperator ((RB - RA : H →L[ℂ] H) : H → H)) :
    essSpectrum hA ⊆ essSpectrum hB := by
  intro lam hlam
  obtain ⟨ψ, hψ_norm, hψ_weak, hψ_eig⟩ := hlam
  -- `R_A(i)·(A − i)ψ n = ψ n`.
  have hRAinv : ∀ n, RA (A (ψ n) - I • (ψ n : H)) = (ψ n : H) :=
    fun n => hRA.left_inverse (ψ n)
  -- `R_B(i)·(A − i)ψ n = ψ n + K·(A − i)ψ n`.
  have hΦval : ∀ n, RB (A (ψ n) - I • (ψ n : H))
      = (ψ n : H) + (RB - RA) (A (ψ n) - I • (ψ n : H)) := by
    intro n
    rw [sub_apply, hRAinv n]; abel
  -- `(A − λ)ψ n → 0` as vectors.
  have hAeig : Tendsto (fun n => A (ψ n) - (lam : ℂ) • (ψ n : H)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hψ_eig
  -- `(A − i)ψ n` is weakly null.
  have hw_weak : ∀ g : H, Tendsto (fun n => ⟪g, A (ψ n) - I • (ψ n : H)⟫_ℂ) atTop (𝓝 0) := by
    intro g
    have e1 : Tendsto (fun n => ⟪g, A (ψ n) - (lam : ℂ) • (ψ n : H)⟫_ℂ) atTop (𝓝 0) := by
      have h : Tendsto (fun n => ⟪g, A (ψ n) - (lam : ℂ) • (ψ n : H)⟫_ℂ) atTop
          (𝓝 (⟪g, (0 : H)⟫_ℂ)) := Tendsto.inner tendsto_const_nhds hAeig
      simpa only [inner_zero_right] using h
    have e2 : Tendsto (fun n => ((lam : ℂ) - I) * ⟪g, (ψ n : H)⟫_ℂ) atTop (𝓝 0) := by
      simpa using (hψ_weak g).const_mul ((lam : ℂ) - I)
    have hsum := e1.add e2
    rw [add_zero] at hsum
    refine hsum.congr (fun n => ?_)
    rw [inner_sub_right, inner_smul_right, inner_sub_right, inner_smul_right]; ring
  -- `(A − i)ψ n` is bounded.
  have hw_bdd : ∃ C, ∀ n, ‖A (ψ n) - I • (ψ n : H)‖ ≤ C := by
    have hb : Tendsto (fun n => ‖A (ψ n) - (lam : ℂ) • (ψ n : H)‖
        + ‖(lam : ℂ) - I‖ * ‖(ψ n : H)‖) atTop (𝓝 (0 + ‖(lam : ℂ) - I‖ * 1)) :=
      hψ_eig.add (hψ_norm.const_mul ‖(lam : ℂ) - I‖)
    obtain ⟨C, hC⟩ := hb.bddAbove_range
    refine ⟨C, fun n => le_trans ?_ (hC (Set.mem_range_self n))⟩
    calc ‖A (ψ n) - I • (ψ n : H)‖
        = ‖(A (ψ n) - (lam : ℂ) • (ψ n : H)) + ((lam : ℂ) - I) • (ψ n : H)‖ := by
          congr 1; module
      _ ≤ ‖A (ψ n) - (lam : ℂ) • (ψ n : H)‖ + ‖((lam : ℂ) - I) • (ψ n : H)‖ := norm_add_le _ _
      _ = ‖A (ψ n) - (lam : ℂ) • (ψ n : H)‖ + ‖(lam : ℂ) - I‖ * ‖(ψ n : H)‖ := by rw [norm_smul]
  -- `K·(A − i)ψ n → 0`.
  obtain ⟨C, hC⟩ := hw_bdd
  have hKw : Tendsto (fun n => ‖(RB - RA) (A (ψ n) - I • (ψ n : H))‖) atTop (𝓝 0) :=
    IsCompactOperator.tendsto_norm_apply_of_weaklyNull hcompact hC hw_weak
  have hKw0 : Tendsto (fun n => (RB - RA) (A (ψ n) - I • (ψ n : H))) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hKw
  -- `R_B(i)·(A − i)ψ n − ψ n = K·(A − i)ψ n`.
  have hsub : ∀ n, RB (A (ψ n) - I • (ψ n : H)) - (ψ n : H)
      = (RB - RA) (A (ψ n) - I • (ψ n : H)) := fun n => by rw [hΦval n]; abel
  -- Assemble the perturbed Weyl sequence `φ n := R_B(i)·(A − i)ψ n`.
  refine mem_essSpectrum_of_seq hB lam
    (fun n => RB (A (ψ n) - I • (ψ n : H)))
    (fun n => hRB.mem_domain _) ?_ ?_ ?_
  · -- `‖φ n‖ → 1`.
    have hgtend : Tendsto (fun n => -‖(RB - RA) (A (ψ n) - I • (ψ n : H))‖) atTop (𝓝 0) := by
      simpa only [neg_zero] using hKw.neg
    have hnormdiff : Tendsto (fun n => ‖RB (A (ψ n) - I • (ψ n : H))‖ - ‖(ψ n : H)‖)
        atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hgtend hKw ?_ ?_
      · intro n
        have hb := abs_norm_sub_norm_le (RB (A (ψ n) - I • (ψ n : H))) ((ψ n : H))
        rw [hsub n] at hb
        exact (abs_le.mp hb).1
      · intro n
        have hb := abs_norm_sub_norm_le (RB (A (ψ n) - I • (ψ n : H))) ((ψ n : H))
        rw [hsub n] at hb
        exact (abs_le.mp hb).2
    have hfin := hnormdiff.add hψ_norm
    rw [zero_add] at hfin
    exact hfin.congr (fun n => by ring)
  · -- `φ` weakly null.
    intro g
    have e1 : Tendsto (fun n => ⟪g, (ψ n : H)⟫_ℂ) atTop (𝓝 0) := hψ_weak g
    have e2 : Tendsto (fun n => ⟪g, (RB - RA) (A (ψ n) - I • (ψ n : H))⟫_ℂ) atTop (𝓝 0) := by
      have h : Tendsto (fun n => ⟪g, (RB - RA) (A (ψ n) - I • (ψ n : H))⟫_ℂ) atTop
          (𝓝 (⟪g, (0 : H)⟫_ℂ)) := Tendsto.inner tendsto_const_nhds hKw0
      simpa only [inner_zero_right] using h
    have hsum := e1.add e2
    rw [add_zero] at hsum
    refine hsum.congr (fun n => ?_)
    rw [← inner_add_right, ← hΦval n]
  · -- `(B − λ)φ n → 0`.
    have hKterm : Tendsto (fun n => ((lam : ℂ) - I) • (RB - RA) (A (ψ n) - I • (ψ n : H)))
        atTop (𝓝 0) := by
      simpa only [smul_zero] using hKw0.const_smul ((lam : ℂ) - I)
    have hc_vec : Tendsto (fun n =>
        B ⟨RB (A (ψ n) - I • (ψ n : H)), hRB.mem_domain _⟩
          - (lam : ℂ) • RB (A (ψ n) - I • (ψ n : H)))
        atTop (𝓝 0) := by
      have hsum := hAeig.sub hKterm
      rw [sub_zero] at hsum
      refine hsum.congr (fun n => ?_)
      have hsolve := hRB.solves (A (ψ n) - I • (ψ n : H))
      have hBΦ : B ⟨RB (A (ψ n) - I • (ψ n : H)), hRB.mem_domain _⟩
          = (A (ψ n) - I • (ψ n : H)) + I • RB (A (ψ n) - I • (ψ n : H)) :=
        sub_eq_iff_eq_add.mp hsolve
      rw [hBΦ, hΦval n]; module
    exact tendsto_zero_iff_norm_tendsto_zero.mp hc_vec

/-- **Weyl's theorem.** If the resolvents `R_A(i)`, `R_B(i)` of two self-adjoint operators differ
by a compact operator, then `A` and `B` have the same essential spectrum. -/
lemma essSpectrum_eq_of_isCompactOperator_resolvent_sub
    {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {RA RB : H →L[ℂ] H} (hRA : IsResolventAt hA I RA) (hRB : IsResolventAt hB I RB)
    (hcompact : IsCompactOperator ((RB - RA : H →L[ℂ] H) : H → H)) :
    essSpectrum hA = essSpectrum hB := by
  apply Set.Subset.antisymm
  · exact essSpectrum_subset_of_isCompactOperator_resolvent_sub hA hB hRA hRB hcompact
  · apply essSpectrum_subset_of_isCompactOperator_resolvent_sub hB hA hRB hRA
    have hCLM : (RA - RB : H →L[ℂ] H) = -(RB - RA) := by abel
    rw [hCLM]
    exact hcompact.neg

/-! ## C. Relatively compact perturbations -/

/-- **Relatively compact perturbations.** If `B - A = W (A - i)` on the domain of `A` for a compact
`W`, then `R_B(i) - R_A(i) = -R_B(i) W` is compact. -/
lemma isCompactOperator_resolvent_sub_of_isCompactOperator_perturb
    {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {RA RB : H →L[ℂ] H} (hRA : IsResolventAt hA I RA) (hRB : IsResolventAt hB I RB)
    (hdom : A.domain = B.domain) (W : H →L[ℂ] H) (hW : IsCompactOperator (W : H → H))
    (hVW : ∀ (χ : H) (hχ : χ ∈ A.domain),
        B ⟨χ, hdom ▸ hχ⟩ - A ⟨χ, hχ⟩ = W (A ⟨χ, hχ⟩ - I • χ)) :
    IsCompactOperator ((RB - RA : H →L[ℂ] H) : H → H) := by
  have key : (RB - RA) = -(RB.comp W) := by
    ext ψ
    simp only [sub_apply, neg_apply,
      ContinuousLinearMap.comp_apply]
    set χ := RA ψ with _hχ
    have memA : χ ∈ A.domain := hRA.mem_domain ψ
    have hsolveA : A ⟨χ, memA⟩ - I • χ = ψ := hRA.solves ψ
    have hinvB : RB (B ⟨χ, hdom ▸ memA⟩ - I • χ) = χ :=
      hRB.left_inverse ⟨χ, hdom ▸ memA⟩
    have hWχ : B ⟨χ, hdom ▸ memA⟩ - A ⟨χ, memA⟩ = W ψ := by rw [hVW χ memA, hsolveA]
    have hRBψ : RB ψ = χ - RB (W ψ) := by
      have h1 : ψ = (B ⟨χ, hdom ▸ memA⟩ - I • χ) - (B ⟨χ, hdom ▸ memA⟩ - A ⟨χ, memA⟩) := by
        rw [← hsolveA]; abel
      calc RB ψ
          = RB ((B ⟨χ, hdom ▸ memA⟩ - I • χ) - (B ⟨χ, hdom ▸ memA⟩ - A ⟨χ, memA⟩)) := by rw [h1]
        _ = RB (B ⟨χ, hdom ▸ memA⟩ - I • χ) - RB (B ⟨χ, hdom ▸ memA⟩ - A ⟨χ, memA⟩) := by
            rw [map_sub]
        _ = χ - RB (W ψ) := by rw [hinvB, hWχ]
    rw [hRBψ]; abel
  rw [key]
  exact (hW.clm_comp RB).neg

/-- **Weyl's theorem for relatively compact perturbations.** If `B - A = W (A - i)` on the domain of
`A` for a compact `W`, then `A` and `B` have the same essential spectrum. -/
lemma essSpectrum_eq_of_isCompactOperator_perturb
    {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {RA RB : H →L[ℂ] H} (hRA : IsResolventAt hA I RA) (hRB : IsResolventAt hB I RB)
    (hdom : A.domain = B.domain) (W : H →L[ℂ] H) (hW : IsCompactOperator (W : H → H))
    (hVW : ∀ (χ : H) (hχ : χ ∈ A.domain),
        B ⟨χ, hdom ▸ hχ⟩ - A ⟨χ, hχ⟩ = W (A ⟨χ, hχ⟩ - I • χ)) :
    essSpectrum hA = essSpectrum hB :=
  essSpectrum_eq_of_isCompactOperator_resolvent_sub hA hB hRA hRB
    (isCompactOperator_resolvent_sub_of_isCompactOperator_perturb hA hB hRA hRB hdom W hW hVW)

end QuantumMechanics.Essential

end ProbabilisticTheory
