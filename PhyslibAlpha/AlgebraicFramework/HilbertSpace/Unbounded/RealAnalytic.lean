/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Operators.Unbounded
public import Physlib.QuantumMechanics.Operators.SpectralTheory.Symmetric
public import Physlib.QuantumMechanics.Operators.SpectralTheory.SelfAdjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Reusable real-analytic certificates for unbounded observables

Contains only the represented operator facts needed to identify a self-adjoint (or essentially
self-adjoint) `LinearPMap`: density, symmetry, defect indices, and the canonical closed extension.
Keeping these certificates separate lets multiplication, Schrödinger, and oscillator models share
the same analytic pipeline.

## Main definitions

- `DefectIndexCertificate` / `DefectIndexCertificate.essentiallySelfAdjoint` : the von Neumann
    defect-index criterion for essential self-adjointness.
- `isEssentiallySelfAdjoint_of_hilbertBasis_eigenvectors` : a symmetric operator whose domain is
    exactly the span of a Hilbert basis of eigenvectors with real eigenvalues is essentially
    self-adjoint (the "eigenbasis density" criterion).
-/

@[expose] public section

namespace QuantumMechanics

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Von Neumann's defect criterion -/

/-- A checkable certificate that a symmetric represented operator has self-adjoint closure.

The two defect-number equalities are the analytic input. The conclusion is deliberately stored
as a theorem rather than as an axiom or an unproved declaration; `LinearPMap` supplies the von
Neumann criterion used in the proof. -/
structure DefectIndexCertificate (T : H →ₗ.[ℂ] H) where
  symmetric : T.IsSymmetric
  dense : T.HasDenseDomain
  plus : T.defectNumber Complex.I = 0
  minus : T.defectNumber (-Complex.I) = 0

lemma DefectIndexCertificate.essentiallySelfAdjoint
    {T : H →ₗ.[ℂ] H} (C : DefectIndexCertificate T) :
    T.IsEssentiallySelfAdjoint :=
  C.symmetric.isEssentiallySelfAdjoint_of_defectNumber_eq_zero C.dense C.plus C.minus

lemma DefectIndexCertificate.closure_isSelfAdjoint
    {T : H →ₗ.[ℂ] H} (C : DefectIndexCertificate T) :
    IsSelfAdjoint T.closure :=
  C.essentiallySelfAdjoint

/-- A self-adjoint operator is automatically an essentially self-adjoint core for itself. -/
lemma ofSelfAdjoint_isEssentiallySelfAdjoint
    {T : H →ₗ.[ℂ] H} (hT : IsSelfAdjoint T) : T.IsEssentiallySelfAdjoint :=
  LinearPMap.IsSelfAdjoint.isEssentiallySelfAdjoint hT

/-! ## Essential self-adjointness from a Hilbert basis of eigenvectors

A symmetric operator whose domain is *exactly* the (algebraic) span of a Hilbert basis of
eigenvectors with real eigenvalues is essentially self-adjoint. This is the standard "eigenbasis
density" criterion for essential self-adjointness (see e.g. Reed–Simon, *Methods of Modern
Mathematical Physics I: Functional Analysis*, Theorem VIII.3): reality of the eigenvalues makes
`T ∓ i` bounded below by `1` on the eigenbasis span, and the Hilbert-basis expansion of an
arbitrary `y : H` (with coefficients divided by `λ - z`) produces, in the limit of its partial
sums, an explicit preimage of `y` under `T.closure ∓ i`.
-/

section HilbertBasisCriterion

open Finsupp Filter Complex LinearPMap
open scoped ENNReal Topology

variable {ι : Type*}

/-- **Essential self-adjointness from a Hilbert basis of eigenvectors.** If `T`'s domain is exactly
the (algebraic) span of a Hilbert basis `e`, and each basis vector `e i` is an eigenvector of `T`
with *real* eigenvalue `lam i`, then `T` is essentially self-adjoint. -/
theorem isEssentiallySelfAdjoint_of_hilbertBasis_eigenvectors
    (e : HilbertBasis ι ℂ H) (T : H →ₗ.[ℂ] H) (lam : ι → ℝ)
    (hdom : T.domain = Submodule.span ℂ (Set.range e))
    (heig : ∀ i, T ⟨e i, hdom ▸ Submodule.subset_span ⟨i, rfl⟩⟩ = (lam i : ℂ) • e i) :
    T.IsEssentiallySelfAdjoint := by
  classical
  have hmem : ∀ i, e i ∈ T.domain := fun i ↦ hdom ▸ Submodule.subset_span ⟨i, rfl⟩
  set v : ι → T.domain := fun i ↦ (⟨e i, hmem i⟩ : T.domain) with hv_def
  set w : ι → H := fun i ↦ (lam i : ℂ) • e i with hw_def
  -- `Finsupp.linearCombination` computes `T` on finite eigenbasis combinations.
  have hcomp : (T.domain.subtype : T.domain →ₗ[ℂ] H) ∘ v = (⇑e) := by
    funext i; simp [hv_def]
  have hcomp2 : (T.toFun : T.domain →ₗ[ℂ] H) ∘ v = w := by
    funext i; simp only [Function.comp_apply, hv_def]; exact heig i
  have hv_coe : ∀ l : ι →₀ ℂ,
      ((Finsupp.linearCombination ℂ v l : T.domain) : H) = Finsupp.linearCombination ℂ (⇑e) l := by
    intro l
    have h := Finsupp.apply_linearCombination ℂ T.domain.subtype v l
    rw [hcomp] at h
    exact h
  have hTapply : ∀ l : ι →₀ ℂ,
      T (Finsupp.linearCombination ℂ v l) = Finsupp.linearCombination ℂ w l := by
    intro l
    rw [← toFun_eq_coe]
    have h := Finsupp.apply_linearCombination ℂ T.toFun v l
    rw [hcomp2] at h
    exact h
  have hspan : ∀ x : T.domain, ∃ l : ι →₀ ℂ, Finsupp.linearCombination ℂ v l = x := by
    intro x
    have hx : (x : H) ∈ Submodule.span ℂ (Set.range e) := hdom ▸ x.2
    rw [← Finsupp.range_linearCombination] at hx
    obtain ⟨l, hl⟩ := LinearMap.mem_range.mp hx
    exact ⟨l, Subtype.ext (by rw [hv_coe, hl])⟩
  -- Symmetry: on eigenbasis combinations `⟪T x, x⟫` reduces to a manifestly real sum.
  have hsym : T.IsSymmetric := by
    rw [LinearPMap.isSymmetric_iff_inner_map_self_real]
    intro x
    obtain ⟨l, hl⟩ := hspan x
    have hlH : (x : H) = Finsupp.linearCombination ℂ (⇑e) l := by rw [← hv_coe l, hl]
    have hTx : T x = Finsupp.linearCombination ℂ w l := hl ▸ hTapply l
    have hTx' : Finsupp.linearCombination ℂ w l
        = ∑ i ∈ l.support, (l i * (lam i : ℂ)) • e i := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hw_def, smul_smul]
    have hlH' : Finsupp.linearCombination ℂ (⇑e) l = ∑ i ∈ l.support, l i • e i := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
    rw [hTx, hlH, hTx', hlH', e.orthonormal.inner_sum (fun i ↦ l i * (lam i : ℂ)) (fun i ↦ l i)
      l.support, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  have hdense : T.HasDenseDomain := by
    rw [LinearPMap.hasDenseDomain_def, hdom, dense_iff_closure_eq,
      ← Submodule.topologicalClosure_coe, e.dense_span, Submodule.top_coe]
  have hTclosable : T.IsClosable := hsym.isClosable hdense
  have hTclosure_sym : T.closure.IsSymmetric := hsym.closure hdense
  have hTclosure_dense : T.closure.HasDenseDomain := hdense.closure
  -- For `ζ = ± I`, real eigenvalues satisfy `|lam i - ζ| ≥ 1`.
  have hbound : ∀ {ζ : ℂ}, ζ.re = 0 → normSq ζ = 1 → ∀ r : ℝ, 1 ≤ ‖(r : ℂ) - ζ‖ := by
    intro ζ hre hsq r
    have hns : (1 : ℝ) ≤ normSq ((r : ℂ) - ζ) := by
      have h1 : ((r : ℂ) - ζ).re = r := by simp [hre]
      have h2 : ((r : ℂ) - ζ).im = -ζ.im := by simp
      rw [normSq_apply, h1, h2]
      nlinarith [sq_nonneg r, normSq_apply ζ, hsq, hre]
    calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
      _ ≤ Real.sqrt (normSq ((r : ℂ) - ζ)) := Real.sqrt_le_sqrt hns
      _ = ‖(r : ℂ) - ζ‖ := (Complex.norm_def _).symm
  have hne : ∀ {ζ : ℂ}, ζ.re = 0 → normSq ζ = 1 → ∀ i, (lam i : ℂ) - ζ ≠ 0 := by
    intro ζ hre hsq i h
    have := hbound hre hsq (lam i)
    rw [h, norm_zero] at this
    linarith
  -- The core surjectivity fact: `(T.closure - ζ • 1).range = ⊤` for `ζ = ± I`.
  have hrange : ∀ {ζ : ℂ}, ζ.re = 0 → normSq ζ = 1 →
      (T.closure - ζ • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤ := by
    intro ζ hre hsq
    rw [LinearMap.range_eq_top]
    intro y
    set c : ι → ℂ := fun i ↦ (inner (𝕜 := ℂ) (e i) y) with hc_def
    have hy_sum : HasSum (fun i ↦ c i • e i) y := by
      have h := e.hasSum_repr y
      simpa [hc_def, HilbertBasis.repr_apply_apply] using h
    have hc_summable : Summable fun i ↦ ‖c i‖ ^ 2 := e.orthonormal.inner_products_summable y
    set g : ι → ℂ := fun i ↦ c i / ((lam i : ℂ) - ζ) with hg_def
    have hg_le : ∀ i, ‖g i‖ ≤ ‖c i‖ := fun i ↦ by
      rw [hg_def, Complex.norm_div]
      exact div_le_self (norm_nonneg _) (hbound hre hsq (lam i))
    have hg_summable : Summable fun i ↦ ‖g i‖ ^ 2 :=
      Summable.of_nonneg_of_le (fun i ↦ sq_nonneg _)
        (fun i ↦ pow_le_pow_left₀ (norm_nonneg _) (hg_le i) 2) hc_summable
    have hg_mem : Memℓp g 2 := by
      apply memℓp_gen
      have hp2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
      rw [hp2]
      simpa [Real.rpow_natCast] using hg_summable
    set z : H := e.repr.symm ⟨g, hg_mem⟩ with hz_def
    have hz_sum : HasSum (fun i ↦ g i • e i) z := e.hasSum_repr_symm ⟨g, hg_mem⟩
    have hterm : ∀ i, g i * (lam i : ℂ) = c i + ζ * g i := fun i ↦ by
      have hdiv : g i * ((lam i : ℂ) - ζ) = c i := by
        rw [hg_def]; exact div_mul_cancel₀ (c i) (hne hre hsq i)
      ring_nf
      ring_nf at hdiv
      linear_combination hdiv
    -- Each single eigenbasis term already lies in `T`'s graph.
    have hmem_graph_single :
        ∀ i, ((g i • e i : H), (c i • e i + ζ • (g i • e i) : H)) ∈ T.graph := by
      intro i
      have hTvi : T (v i) = (lam i : ℂ) • e i := heig i
      have hTe : T (g i • v i) = c i • e i + ζ • (g i • e i) := by
        rw [LinearPMap.map_smul, hTvi, smul_smul, hterm i, add_smul, smul_smul]
      have hco : ((g i • v i : T.domain) : H) = g i • e i := by
        rw [SetLike.val_smul, hv_def]
      simpa [hco, hTe] using T.mem_graph (g i • v i)
    have hu := hz_sum.prodMk (hy_sum.add (hz_sum.const_smul ζ))
    have hgraph_closure : (z, y + ζ • z) ∈ T.graph.topologicalClosure := by
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
      refine mem_closure_of_tendsto hu (Eventually.of_forall fun s ↦ ?_)
      exact Submodule.sum_mem _ fun i _ ↦ hmem_graph_single i
    rw [hTclosable.graph_closure_eq_closure_graph] at hgraph_closure
    have hzdom : z ∈ T.closure.domain := mem_domain_of_mem_graph hgraph_closure
    have hTz : T.closure ⟨z, hzdom⟩ = y + ζ • z :=
      ((image_iff hzdom).mpr hgraph_closure).symm
    have hzdom' : z ∈ (T.closure - ζ • (1 : H →ₗ.[ℂ] H)).domain := by
      rw [LinearPMap.sub_domain, LinearPMap.smul_domain, LinearPMap.one_domain, inf_top_eq]
      exact hzdom
    refine ⟨⟨z, hzdom'⟩, ?_⟩
    show (T.closure - ζ • (1 : H →ₗ.[ℂ] H)) ⟨z, hzdom'⟩ = y
    rw [LinearPMap.sub_apply, LinearPMap.smul_apply]
    have h1 : (1 : H →ₗ.[ℂ] H) ⟨z, (Submodule.mem_inf.mp hzdom').2⟩ = z := rfl
    rw [h1, show T.closure ⟨z, (Submodule.mem_inf.mp hzdom').1⟩ = T.closure ⟨z, hzdom⟩ from rfl,
        hTz]
    abel
  refine hTclosure_sym.isSelfAdjoint_of_range_eq_top hTclosure_dense ?_ ?_
  · have hI : T.closure + I • (1 : H →ₗ.[ℂ] H) = T.closure - (-I) • (1 : H →ₗ.[ℂ] H) :=
      LinearPMap.ext rfl fun x hf hg ↦ by
        simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply, sub_neg_eq_add]
    rw [hI]
    exact hrange (by simp) (by simp [normSq_apply])
  · exact hrange (by simp) (by simp [normSq_apply])

end HilbertBasisCriterion

end

end QuantumMechanics
