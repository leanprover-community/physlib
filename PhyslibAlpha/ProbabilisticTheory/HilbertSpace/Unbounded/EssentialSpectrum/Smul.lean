/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem, Adam Bornemann
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.EssentialSpectrum.Defs
public import Physlib.QuantumMechanics.Operators.SpectralTheory.Symmetric

/-!

# Scaling self-adjoint operators

Real scaling preserves self-adjointness and scales the essential spectrum.

## i. Overview

For a self-adjoint operator `A` and a real `c ≠ 0`, `c • A` is self-adjoint and its essential
spectrum is the essential spectrum of `A` scaled by `c`.

## ii. Key results

- `isSelfAdjoint_smul_real` : `c • A` is self-adjoint.
- `essSpectrum_smul_real` : the essential spectrum scales with `c`.

## iii. Table of contents

- A. L1: self-adjointness under real scaling
- B. L2: essential spectrum under real scaling

## iv. References

- Adapted from `adambornemann-glitch/Spectra`, `SpectralTheory/Essential/Smul.lean` (Apache 2.0).

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate

namespace QuantumMechanics.Essential

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## A. L1: self-adjointness under real scaling -/

omit [CompleteSpace H] in
/-- For a real scalar `c`, `c • A` is formally self-adjoint when `A` is. -/
lemma isFormalAdjoint_smul_real {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (c : ℝ) : (((c : ℂ)) • A).IsFormalAdjoint (((c : ℂ)) • A) := by
  intro x y
  rw [LinearPMap.smul_apply, LinearPMap.smul_apply, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, hsym x y]

/-- For self-adjoint `A` and `z` off the real axis, every vector is `A ψ - z ψ` for some `ψ` in the
domain of `A`. -/
lemma exists_apply_sub_smul_eq {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0)
    (φ : H) : ∃ ψ : A.domain, A ψ - z • (ψ : H) = φ := by
  have hdom : (A - z • (1 : H →ₗ.[ℂ] H)).domain = A.domain := by
    simp [LinearPMap.sub_domain, LinearPMap.smul_domain]
  obtain ⟨x, hx⟩ := LinearPMap.IsSelfAdjoint.sub_smul_surjective hA hz φ
  refine ⟨⟨(x : H), by rw [← hdom]; exact x.2⟩, ?_⟩
  rw [LinearPMap.toFun_eq_coe, LinearPMap.sub_apply] at hx
  simpa using hx

/-- Surjectivity of `c•A - w` reduces to surjectivity of `A - w/c` (real `c ≠ 0`). -/
lemma smul_surjective_sub_smul {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (c : ℝ) (hc : c ≠ 0) (w : ℂ) (hw : w.im ≠ 0) :
    ∀ φ : H, ∃ ψ : ((c : ℂ) • A).domain, ((c : ℂ) • A) ψ - w • (ψ : H) = φ := by
  intro φ
  have hcℂ : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hwc : (w / (c : ℂ)).im ≠ 0 := by
    rw [Complex.div_ofReal_im]
    exact div_ne_zero hw hc
  obtain ⟨ψ, hψ⟩ := exists_apply_sub_smul_eq hA hwc ((c : ℂ)⁻¹ • φ)
  have hdomeq : ((c : ℂ) • A).domain = A.domain := LinearPMap.smul_domain (c : ℂ) A
  have hψmem : (ψ : H) ∈ ((c : ℂ) • A).domain := by rw [hdomeq]; exact ψ.2
  refine ⟨⟨(ψ : H), hψmem⟩, ?_⟩
  rw [LinearPMap.smul_apply]
  have hAeq : A ⟨(ψ : H), hψmem⟩ = A ψ := by congr
  rw [hAeq]
  have hkey : (c : ℂ) • (A ψ - (w / (c : ℂ)) • (ψ : H)) = (c : ℂ) • ((c : ℂ)⁻¹ • φ) :=
    congrArg (fun v => (c : ℂ) • v) hψ
  rw [smul_sub, smul_smul, smul_smul] at hkey
  rw [mul_div_cancel₀ _ hcℂ, mul_inv_cancel₀ hcℂ, one_smul] at hkey
  exact hkey

/-- **L1.** If `A` is self-adjoint and `c : ℝ` is nonzero, then `(c : ℂ) • A` is self-adjoint. -/
lemma isSelfAdjoint_smul_real {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (c : ℝ) (hc : c ≠ 0) : IsSelfAdjoint ((c : ℂ) • A) := by
  have hsymA : A.IsFormalAdjoint A := LinearPMap.IsSelfAdjoint.isSymmetric hA
  have hsym : ((c : ℂ) • A).IsFormalAdjoint ((c : ℂ) • A) := isFormalAdjoint_smul_real hsymA c
  have hdense : Dense (((c : ℂ) • A).domain : Set H) := by
    rw [LinearPMap.smul_domain]; exact hA.dense_domain
  have hplusRaw : ∀ φ : H, ∃ ψ : ((c : ℂ) • A).domain, ((c : ℂ) • A) ψ + I • (ψ : H) = φ := by
    intro φ
    obtain ⟨ψ, hψ⟩ := smul_surjective_sub_smul hA c hc (-I) (by simp) φ
    exact ⟨ψ, by rw [← hψ, neg_smul, sub_neg_eq_add]⟩
  have hminusRaw : ∀ φ : H, ∃ ψ : ((c : ℂ) • A).domain, ((c : ℂ) • A) ψ - I • (ψ : H) = φ :=
    smul_surjective_sub_smul hA c hc I (by simp)
  have hplus : Function.Surjective (((c : ℂ) • A) + I • (1 : H →ₗ.[ℂ] H)).toFun := by
    intro φ
    obtain ⟨ψ, hψ⟩ := hplusRaw φ
    refine ⟨⟨(ψ : H), by simp [LinearPMap.add_domain, LinearPMap.smul_domain]⟩, ?_⟩
    rw [LinearPMap.toFun_eq_coe, LinearPMap.add_apply]
    simpa using hψ
  have hminus : Function.Surjective (((c : ℂ) • A) - I • (1 : H →ₗ.[ℂ] H)).toFun := by
    intro φ
    obtain ⟨ψ, hψ⟩ := hminusRaw φ
    refine ⟨⟨(ψ : H), by simp [LinearPMap.sub_domain, LinearPMap.smul_domain]⟩, ?_⟩
    rw [LinearPMap.toFun_eq_coe, LinearPMap.sub_apply]
    simpa using hψ
  exact LinearPMap.IsSymmetric.isSelfAdjoint_of_range_eq_top hsym hdense
    (LinearMap.range_eq_top.mpr hplus) (LinearMap.range_eq_top.mpr hminus)

/-! ## B. L2: essential spectrum under real scaling -/

/-- A Weyl sequence for `A` at `λ` is a Weyl sequence for `c • A` at `c·λ` (real `c`). -/
lemma mem_essSpectrum_smul_real {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (c : ℝ) (hc : c ≠ 0) {lam : ℝ} (hlam : lam ∈ essSpectrum hA) :
    c * lam ∈ essSpectrum (isSelfAdjoint_smul_real hA c hc) := by
  obtain ⟨ψ, hnorm, hweak, heig⟩ := hlam
  have hmem : ∀ n, (ψ n : H) ∈ ((c : ℂ) • A).domain := by
    intro n; rw [LinearPMap.smul_domain]; exact (ψ n).2
  refine mem_essSpectrum_of_seq (isSelfAdjoint_smul_real hA c hc) (c * lam)
    (fun n => (ψ n : H)) hmem hnorm hweak ?_
  have hrw : ∀ n,
      ‖((c : ℂ) • A) ⟨(ψ n : H), hmem n⟩ - ((c * lam : ℝ) : ℂ) • (ψ n : H)‖
        = |c| * ‖A (ψ n) - (lam : ℂ) • (ψ n : H)‖ := by
    intro n
    rw [LinearPMap.smul_apply]
    have hAeq : A ⟨(ψ n : H), hmem n⟩ = A (ψ n) := by congr
    rw [hAeq]
    have hsm : (c : ℂ) • A (ψ n) - ((c * lam : ℝ) : ℂ) • (ψ n : H)
        = (c : ℂ) • (A (ψ n) - (lam : ℂ) • (ψ n : H)) := by
      rw [smul_sub, smul_smul]; push_cast; ring_nf
    rw [hsm, norm_smul]
    congr 1
    exact RCLike.norm_ofReal c
  rw [show (𝓝 (0 : ℝ)) = 𝓝 (|c| * 0) by rw [mul_zero]]
  simp_rw [hrw]
  exact heig.const_mul |c|

/-- `essSpectrum` depends only on the operator, not on the self-adjointness witness. -/
lemma essSpectrum_congr_op {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (h : A = B) : essSpectrum hA = essSpectrum hB := by
  subst h; rfl

omit [CompleteSpace H] in
/-- Scaling by `c` then by `c⁻¹` is the identity operator (real `c ≠ 0`). -/
lemma smul_inv_smul_pmap {A : H →ₗ.[ℂ] H} (c : ℝ) (hc : c ≠ 0) :
    ((c⁻¹ : ℝ) : ℂ) • (((c : ℂ)) • A) = A := by
  have hcℂ : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [smul_smul]
  rw [show (((c⁻¹ : ℝ) : ℂ)) * (c : ℂ) = 1 by push_cast; field_simp]
  exact one_smul _ A

/-- **L2.** The essential spectrum scales by a real nonzero `c`:
`essSpectrum (c • A) = (· * c) '' essSpectrum A`. -/
lemma essSpectrum_smul_real {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (c : ℝ) (hc : c ≠ 0) :
    essSpectrum (isSelfAdjoint_smul_real hA c hc) = (fun μ => c * μ) '' essSpectrum hA := by
  apply Set.eq_of_subset_of_subset
  · intro μ hμ
    have _hcℂ : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    have hcA_SA : IsSelfAdjoint ((c : ℂ) • A) := isSelfAdjoint_smul_real hA c hc
    have hstep := mem_essSpectrum_smul_real hcA_SA c⁻¹ (inv_ne_zero hc) hμ
    have hop : ((c⁻¹ : ℝ) : ℂ) • (((c : ℂ)) • A) = A := smul_inv_smul_pmap c hc
    refine ⟨c⁻¹ * μ, ?_, by field_simp⟩
    have hess : essSpectrum (isSelfAdjoint_smul_real hcA_SA c⁻¹ (inv_ne_zero hc))
        = essSpectrum hA :=
      essSpectrum_congr_op _ hA hop
    rw [hess] at hstep
    exact hstep
  · rintro μ ⟨lam, hlam, rfl⟩
    exact mem_essSpectrum_smul_real hA c hc hlam

end QuantumMechanics.Essential

end ProbabilisticTheory
