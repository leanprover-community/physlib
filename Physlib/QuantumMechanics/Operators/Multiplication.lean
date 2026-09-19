/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.Unbounded
public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.SchwartzSubmodule
/-!

# Multiplication operators on `SpaceDHilbertSpace`

## i. Overview

In this module we define and develop the properties of multiplication operators.
Given a measure `μ` on `Space d` and any function `f : Space d → ℂ`, the multiplication operator
`𝓜 μ f` is the partial linear map on `SpaceDHilbertSpace d μ` with domain
`{ψ : SpaceDHilbertSpace d μ | MemHS (f • ψ) μ}` and mapping `ψ` to `f • ψ`.
Prime examples of multiplication operators are the position operators which multiply by `xᵢ` and
the potential operators which multiply by the potential function `V(x)` of a quantum system.

Although the domain of `𝓜 μ f` is defined implicitly through `MemHS`, simple assumptions on `f`
allow one to nail down some of its properties. For example, when `f` is `μ`-a.e. strongly measurable
then the corresponding multiplication operator is densely defined, if `f` is `μ`-a.e. bounded then
the domain is `⊤` and if `f` has temperate growth then the domain contains the Schwartz submodule.

Multiplication operators also form the backbone for derivative operators, which are defined
through multiplication in the Fourier domain: see `Operators/Derivative.lean`.

## ii. Key results

- `mulOperator μ f` (notation `𝓜 μ f`) : The operator defined by `ψ ↦ f • ψ`
    with maximal domain `{ψ : SpaceDHilbertSpace d μ | MemHS (f • ψ) μ}`.
- `mulOperator_adjoint_eq_conj` : The adjoint of `𝓜 μ f` is the multiplication operator
    defined by the conjugate of `f`.
- `mulOperator_isSelfAdjoint` : The multiplication operator of a real function is self-adjoint.
- `mulOperator_isUnbounded` : Multiplication operators with maximal domain are unbounded
    (i.e. densely defined and closable).
- `mulOperator_isClosed` : Multiplication operators with maximal domain are closed.
- `mulOperator_const_smul_eq` : `𝓜 μ (c • f) = c • 𝓜 μ f` for non-zero `c`.
- `mulOperator_add_ge` / `mulOperator_sub_ge` : `𝓜 μ (f ± g)` is an extension of `𝓜 μ f ± 𝓜 μ g`.
- `mulOperator_smul_ge` : `𝓜 μ (f • g)` is an extension of `𝓜 μ f * 𝓜 μ g`.

## iii. Table of contents

- A. Definition
- B. Domain
- C. Adjoint
  - C.1. Self-adjoint
- D. Closed & unbounded
- E. Basic properties
  - E.1. Smul & neg
  - E.2. Add & sub
  - E.3. Composition
- F. Spectrum

## iv. References

* Konrad Schmüdgen, Unbounded Self-Adjoint Operators on Hilbert Space, examples 1.3 and 3.8.
  [ref: Schmudgen2012]
-/

@[expose] public section

namespace QuantumMechanics
namespace SpaceDHilbertSpace
noncomputable section

open LinearPMap
open MeasureTheory
open Filter
open ComplexConjugate

variable {d : ℕ}

/-!
## A. Definition
-/

/-- The multiplication operator which maps `ψ` to the equivalence class of `f • ψ`
  with maximal domain `{ψ : SpaceDHilbertspace d μ | MemHS (f • ψ) μ}`. -/
def mulOperator (μ : Measure (Space d)) (f : Space d → ℂ) :
    SpaceDHilbertSpace d μ →ₗ.[ℂ] SpaceDHilbertSpace d μ where
  domain := {
    carrier := {ψ : SpaceDHilbertSpace d μ | MemHS (f • ⇑ψ) μ}
    add_mem' {ψ φ} hψ hφ := by
      refine (hψ.add hφ).ae_eq ?_
      filter_upwards [coeFn_add ψ φ]
      simp_all [mul_add]
    zero_mem' := by
      refine MemHS.zero.ae_eq ?_
      filter_upwards [coeFn_zero]
      simp_all
    smul_mem' c ψ hψ := by
      refine (hψ.const_smul c).ae_eq ?_
      filter_upwards [coeFn_smul c ψ]
      simp_all [mul_left_comm]
  }
  toFun := {
    toFun ψ := mk ψ.prop
    map_add' ψ φ := by
      rw [← mk_add, mk_eq_iff]
      filter_upwards [coeFn_add ψ φ]
      simp_all [mul_add]
    map_smul' c ψ := by
      rw [← mk_const_smul, mk_eq_iff]
      filter_upwards [coeFn_smul c ψ]
      simp_all [mul_left_comm]
  }

@[inherit_doc mulOperator]
notation "𝓜" => mulOperator

/-- The multiplication operator `𝓜 μ f` has maximal domain: `ψ` is in the domain exactly
  when multiplying by `f` gives an element of the Hilbert space. -/
lemma mem_mulOperator_domain_iff
    {μ : Measure (Space d)} {f : Space d → ℂ} {ψ : SpaceDHilbertSpace d μ} :
    ψ ∈ (𝓜 μ f).domain ↔ MemHS (f • ⇑ψ) μ :=
  Iff.rfl

/-- The defining property of a multiplication operator: `ψ` is mapped to `f • ψ`. -/
lemma mulOperator_apply_ae {μ : Measure (Space d)} {f : Space d → ℂ} (ψ : (𝓜 μ f).domain) :
    𝓜 μ f ψ =ᵐ[μ] f • ψ :=
  coeFn_mk ψ.prop

/-!
## B. Domain
-/

/-- The multiplication operator of a `μ`-a.e. bounded function has full domain. -/
lemma mulOperator_domain_eq_top {μ : Measure (Space d)}
    {f : Space d → ℂ} (hf : AEStronglyMeasurable f μ) {c : ℝ} (hfc : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) :
    (𝓜 μ f).domain = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun ψ ↦ ?_
  refine ((memHS_coe ψ).const_smul c).mono (by fun_prop) ?_
  filter_upwards [hfc] with x h
  simp only [smul_eq_mul, norm_mul, Pi.smul_apply, Pi.smul_apply']
  exact mul_le_mul_of_nonneg_right (h.trans <| by simp [le_abs_self]) (norm_nonneg _)

/-- The domains of multiplication operators shrink with increasing function norm. -/
lemma mulOperator_domain_antitone {μ : Measure (Space d)}
    {f g : Space d → ℂ} (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖f x‖) :
    (𝓜 μ f).domain ≤ (𝓜 μ g).domain := by
  intro ψ hψ
  refine hψ.mono (by fun_prop) ?_
  filter_upwards [h]
  simp_all [mul_le_mul_of_nonneg_right]

/-- The multiplication operators corresponding to functions
  of `μ`-a.e. equal norm have the same domain. -/
lemma mulOperator_domain_eq_of_congr_norm {μ : Measure (Space d)} {f g : Space d → ℂ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ x ∂μ, ‖f x‖ = ‖g x‖) :
    (𝓜 μ f).domain = (𝓜 μ g).domain := by
  ext ψ
  refine memHS_congr_norm (by fun_prop) (by fun_prop) ?_
  filter_upwards [h]
  simp_all

/-- The multiplication operators corresponding to a function
  and its conjugate have the same domain. -/
lemma mulOperator_conj_domain
    {μ : Measure (Space d)} {f : Space d → ℂ} (hf : AEStronglyMeasurable f μ) :
    (𝓜 μ (conj ∘ f)).domain = (𝓜 μ f).domain :=
  mulOperator_domain_eq_of_congr_norm (by fun_prop) hf (by simp)

/-- The multiplication operator corresponding to a `μ`-a.e. strongly measurable function
  is densely defined. -/
lemma mulOperator_hasDenseDomain
    {μ : Measure (Space d)} {f : Space d → ℂ} (hf : AEStronglyMeasurable f μ) :
    (𝓜 μ f).HasDenseDomain := by
  intro ψ
  apply mem_closure_iff_seq_limit.mpr
  obtain ⟨u, hu, hfu⟩ := hf.aemeasurable
  let s : ℕ → Set (Space d) := fun n ↦ u ⁻¹' (Metric.closedBall 0 n)
  let φ : ℕ → SpaceDHilbertSpace d μ := fun n ↦
    mk ((memHS_coe ψ).indicator (Ω := s n) (by measurability))
  have hφ : ∀ n, φ n =ᵐ[μ] (s n).indicator ψ := fun n ↦ coeFn_mk _
  use φ
  constructor
  · intro n
    refine memHS_iff.mpr ⟨by measurability, by measurability, ?_⟩
    refine HasFiniteIntegral.mono (memHS_iff.mp <| memHS_coe (n • φ n)).2.2 ?_
    filter_upwards [hfu, coeFn_smul n (φ n), hφ n] with x h₁ h₂ h₃
    by_cases hx : x ∈ s n
    · simp_rw [norm_pow, norm_norm, sq_le_sq, abs_norm]
      calc
        _ = ‖u x‖ * ‖φ n x‖ := by simp [h₁]
        _ ≤ n * ‖φ n x‖ := mul_le_mul_of_nonneg_right (by simp_all [s]) (norm_nonneg _)
        _ = ‖(n • φ n) x‖ := by simp [h₂, ← Nat.cast_smul_eq_nsmul ℂ]
    · simp [h₃, hx]
  · apply tendsto_sub_nhds_zero_iff.mp
    apply tendsto_zero_iff_tendsto_zero_lintegral_enorm_sq.mpr
    have h : ∀ n, ∫⁻ x, ‖(φ n - ψ) x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(s n)ᶜ.indicator ψ x‖ₑ ^ 2 ∂μ := by
      intro n
      refine lintegral_congr_ae ?_
      filter_upwards [coeFn_sub (φ n) ψ, hφ n] with x h₁ h₂
      by_cases hx : x ∈ s n <;> simp [hx, h₁, h₂]
    simp_rw [h]
    rw [← MeasureTheory.lintegral_zero (α := Space d) (μ := μ)]
    refine tendsto_lintegral_of_dominated_convergence' (fun x ↦ ‖ψ x‖ₑ ^ 2) ?_ ?_ ?_ ?_
    · measurability
    · intro n
      filter_upwards with x
      by_cases hx : x ∈ s n <;> simp [hx]
    · have : ∫⁻ x, ‖‖ψ x‖ ^ 2‖ₑ ∂μ ≠ ⊤ := (memHS_iff.mp <| memHS_coe ψ).2.2.ne
      simp_all
    · filter_upwards with x
      rw [← zero_pow two_ne_zero, ← enorm_zero (E := ℂ)]
      refine ENNReal.Tendsto.pow (Tendsto.enorm (tendsto_nhds_of_eventually_eq ?_))
      refine eventually_atTop.mpr ⟨⌈‖u x‖⌉₊, fun n hn ↦ ?_⟩
      suffices ‖u x‖ ≤ n by simp [s, this]
      exact (Nat.le_ceil _).trans (by exact_mod_cast hn)

open SchwartzMap SchwartzSubmodule in
/-- The multiplication operator corresponding to a function of temperate growth
  contains all Schwartz maps in its domain. -/
lemma mulOperator_domain_ge_of_hasTemperateGrowth {f : Space d → ℂ} (hf : f.HasTemperateGrowth)
    (μ : Measure (Space d)) [μ.HasTemperateGrowth] [μ.IsOpenPosMeasure] :
    SchwartzSubmodule d μ ≤ (𝓜 μ f).domain := by
  intro ψ hψ
  obtain ⟨g, hg⟩ := (schwartzEquiv μ).surjective ⟨ψ, hψ⟩
  let w : 𝓢(Space d, ℂ) := smulLeftCLM ℂ f g
  refine (memHS_coe <| schwartzEquiv μ w).ae_eq ?_
  filter_upwards [schwartzEquiv_coe_ae w, schwartzEquiv_coe_ae g]
  simp_all [w, smulLeftCLM_apply_apply hf]

/-!
## C. Adjoint
-/

private lemma exists_monotone_sets_hasFiniteIntegral
    {μ : Measure (Space d)} [IsFiniteMeasureOnCompacts μ]
    (f g : Space d → ℂ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    ∃ s : ℕ → Set (Space d), Monotone s ∧ ⋃ n, s n = Set.univ ∧ (∀ n, MeasurableSet (s n))
      ∧ ∀ k, k = 1 ∨ k = 2 →
        ∀ n, HasFiniteIntegral (fun x ↦ ‖f x ^ k * g x‖ ^ 2) (μ.restrict (s n)) := by
  obtain ⟨w₁, hw₁, hw₁'⟩ : AEStronglyMeasurable (fun x ↦ f x * g x) μ := by measurability
  obtain ⟨w₂, hw₂, hw₂'⟩ : AEStronglyMeasurable (fun x ↦ f x ^ 2 * g x) μ := by measurability
  let s : ℕ → Set (Space d) :=
    fun n ↦ Metric.closedBall 0 n ∩ (w₁ ⁻¹' Metric.closedBall 0 n ∩ w₂ ⁻¹' Metric.closedBall 0 n)
  refine ⟨s, ?_, ?_, by measurability, ?_⟩
  · exact fun _ _ hmn _ hx ↦
      ⟨Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hmn) hx.1,
        Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hmn) hx.2.1,
        Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hmn) hx.2.2⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    use max ⌈‖x‖⌉.toNat (max ⌈‖w₁ x‖⌉.toNat ⌈‖w₂ x‖⌉.toNat)
    suffices ∀ r : ℝ, r ≤ ⌈r⌉.toNat by simp [s, this]
    exact fun r ↦ (Int.le_ceil r).trans (by exact_mod_cast Int.self_le_toNat _)
  · intro k hk n
    refine lt_of_le_of_lt (b := ‖(n : ℝ) ^ 2‖ₑ * μ (s n)) ?_ ?_
    · rw [← setLIntegral_const]
      refine setLIntegral_mono_ae' (by measurability) ?_
      filter_upwards [hw₁', hw₂'] with x h₁ h₂ ⟨h₃, h₃'⟩
      apply enorm_le_iff_norm_le.mpr
      simp_rw [norm_pow, norm_norm, RCLike.norm_natCast]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      rcases hk <;> simp_all
    · refine ENNReal.mul_lt_top (by norm_num) ?_
      exact measure_inter_lt_top_of_left_ne_top measure_closedBall_lt_top.ne

open Complex InnerProductSpace in
private lemma mulOperator_adjoint_domain_le
    {μ : Measure (Space d)} [IsFiniteMeasureOnCompacts μ]
    {f : Space d → ℂ} (hf : AEStronglyMeasurable f μ) :
    (𝓜 μ f)†.domain ≤ (𝓜 μ (conj ∘ f)).domain := by
  intro ψ hψ
  let ξ : SpaceDHilbertSpace d μ := (𝓜 μ f)† ⟨ψ, hψ⟩
  obtain ⟨s, hs_mono, hs_univ, hs_meas, hs_int⟩ :=
    exists_monotone_sets_hasFiniteIntegral (conj ∘ f) ψ (by fun_prop) ψ.val.aestronglyMeasurable
  let w : ℕ → Space d → ℂ := fun n ↦ (s n).indicator ((conj ∘ f) • ψ)
  have hw : ∀ n, MemHS (w n) μ := by
    intro n
    refine memHS_iff.mpr ⟨by measurability, by measurability, ?_⟩
    refine lt_of_eq_of_lt ?_ (hs_int 1 (Or.inl rfl) n)
    trans ∫⁻ x in s n, ‖‖w n x‖ ^ 2‖ₑ ∂μ
    · exact (setLIntegral_eq_of_support_subset fun x hx ↦ by simp_all [w]).symm
    exact setLIntegral_congr_fun (hs_meas n) fun x hx ↦ by simp [w, hx, mul_pow]
  let φ : ℕ → SpaceDHilbertSpace d μ := fun n ↦ mk (hw n)
  have hφ : ∀ n, φ n ∈ (𝓜 μ f).domain := by
    intro n
    apply memHS_iff.mpr ⟨by measurability, by measurability, ?_⟩
    refine lt_of_eq_of_lt ?_ (hs_int 2 (Or.inr rfl) n)
    calc
      _ = ∫⁻ x, ‖‖(f • w n) x‖ ^ 2‖ₑ ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [coeFn_mk (hw n)] with _ h
        simp [φ, h]
      _ = ∫⁻ x in s n, ‖‖(f • w n) x‖ ^ 2‖ₑ ∂μ :=
        (setLIntegral_eq_of_support_subset fun x hx ↦ by simp_all [w]).symm
    exact setLIntegral_congr_fun (hs_meas n) fun x hx ↦ by simp [w, hx, ← mul_assoc, ← pow_two]
  suffices ∀ n, ∫⁻ x in s n, ‖‖f x‖ ^ 2 * ‖ψ x‖ ^ 2‖ₑ ∂μ ≤ ∫⁻ x, ‖‖ξ x‖ ^ 2‖ₑ ∂μ by
    refine memHS_iff.mpr ⟨by measurability, by measurability, ?_⟩
    refine lt_of_le_of_lt ?_ (memHS_iff.mp <| memHS_coe ξ).2.2
    trans ⨆ n, ∫⁻ x in s n, ‖‖f x‖ ^ 2 * ‖ψ x‖ ^ 2‖ₑ ∂μ
    · rw [← setLIntegral_univ, ← hs_univ,
        setLIntegral_iUnion_of_directed _ (directed_of_isDirected_le hs_mono)]
      simp [mul_pow]
    exact iSup_le this
  intro n
  suffices ‖φ n‖ ^ 2 ≤ ‖ξ‖ ^ 2 by
    refine le_of_eq_of_le (b := ∫⁻ x, ‖‖φ n x‖ ^ 2‖ₑ ∂μ) ?_ ((ENNReal.toReal_le_toReal ?_ ?_).mp ?_)
    · calc
        _ = ∫⁻ x in s n, ‖‖w n x‖ ^ 2‖ₑ ∂μ :=
          setLIntegral_congr_fun (hs_meas n) fun x hx ↦ by simp [w, hx, mul_pow]
        _ = ∫⁻ x, ‖‖w n x‖ ^ 2‖ₑ ∂μ :=
          setLIntegral_eq_of_support_subset fun x hx ↦ by simp_all [w]
        _ = ∫⁻ x, ‖‖φ n x‖ ^ 2‖ₑ ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [coeFn_mk (hw n)] with x h₁
          simp [φ, h₁]
    · exact (memHS_iff.mp <| memHS_coe (φ n)).2.2.ne
    · exact (memHS_iff.mp <| memHS_coe ξ).2.2.ne
    · suffices h : ∀ ψ : SpaceDHilbertSpace d μ, ‖ψ‖ ^ 2 = (∫⁻ x, ‖‖ψ x‖ ^ 2‖ₑ ∂μ).toReal by
        simp only [← h, this]
      intro ψ
      rw [Lp.norm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
        (Lp.aestronglyMeasurable ψ)]
      simp [← ENNReal.toReal_pow, ← ENNReal.rpow_mul_natCast]
  suffices ‖φ n‖ ^ 2 ≤ ‖ξ‖ * ‖φ n‖ by
    nlinarith [this, sq_nonneg (‖ξ‖ - ‖φ n‖)]
  calc
    _ = ‖⟪φ n, φ n⟫_ℂ‖ := by simp
    _ = ‖⟪ψ, 𝓜 μ f ⟨φ n, hφ n⟩⟫_ℂ‖ := by
      refine congrArg norm ?_
      refine integral_congr_ae ?_
      filter_upwards [coeFn_mk (hw n), mulOperator_apply_ae ⟨φ n, hφ n⟩] with x h₁ h₂
      by_cases hx : x ∈ s n
      · simp only [φ, h₁, h₂, inner_self_eq_norm_sq_to_K, coe_algebraMap, RCLike.inner_apply,
          Pi.smul_apply', smul_eq_mul]
        calc
          _ = ofReal (‖f x‖ ^ 2 * ‖ψ x‖ ^ 2) := by simp [w, hx, mul_pow]
          _ = (f x * conj (f x)) * (ψ x * conj (ψ x)) := by
            simp_rw [← normSq_eq_norm_sq, Complex.ofReal_mul, normSq_eq_conj_mul_self, mul_comm]
          _ = f x * w n x * conj (ψ x) := by simp [w, hx, mul_assoc]
      · simp [φ, h₁, h₂, w, hx]
    _ = ‖⟪ξ, φ n⟫_ℂ‖ := by
      rw [(adjoint_isFormalAdjoint (mulOperator_hasDenseDomain hf) ⟨ψ, hψ⟩ ⟨φ n, hφ n⟩).symm]
    _ ≤ ‖ξ‖ * ‖φ n‖ := norm_inner_le_norm ξ (φ n)

/-- The adjoint of a multiplication operator is again a multiplication operator. -/
lemma mulOperator_adjoint_eq_conj {μ : Measure (Space d)} [IsFiniteMeasureOnCompacts μ]
    {f : Space d → ℂ} (hf : AEStronglyMeasurable f μ) :
    (𝓜 μ f)† = 𝓜 μ (conj ∘ f) := by
  have hFA : (𝓜 μ f).IsFormalAdjoint (𝓜 μ (conj ∘ f)) := by
    intro ψ φ
    refine integral_congr_ae ?_
    filter_upwards [mulOperator_apply_ae ψ, mulOperator_apply_ae φ] with x h₁ h₂
    simp [h₁, h₂, mul_assoc, mul_left_comm]
  refine eq_of_le_of_ge ?_ (hFA.le_adjoint <| mulOperator_hasDenseDomain hf)
  refine ⟨mulOperator_adjoint_domain_le hf, fun ψ ψ' hψ ↦ ?_⟩
  refine adjoint_apply_eq (mulOperator_hasDenseDomain hf) ψ fun φ ↦ ?_
  rw [← inner_conj_symm, hψ, (hFA φ ψ').symm, inner_conj_symm]

/-!
### C.1. Self-adjoint
-/

/-- The multiplication operator corresponding to a real function is self-adjoint. -/
lemma mulOperator_isSelfAdjoint_ofReal {μ : Measure (Space d)} [IsFiniteMeasureOnCompacts μ]
    {f : Space d → ℂ} (hf : AEStronglyMeasurable f μ) (hf' : conj ∘ f = f) :
    IsSelfAdjoint (𝓜 μ f) := by
  rw [isSelfAdjoint_def, mulOperator_adjoint_eq_conj hf, hf']

/-!
## D. Closed & unbounded
-/

/-- Multiplication operators of `μ`-a.e. strongly measurable functions are closable. -/
lemma mulOperator_isClosable {μ : Measure (Space d)} [IsFiniteMeasureOnCompacts μ]
    {f : Space d → ℂ} (hf : AEStronglyMeasurable f μ) :
    (𝓜 μ f).IsClosable := by
  refine isClosable_of_exists_dense_formalAdjoint (mulOperator_hasDenseDomain hf) ?_
  exact ⟨𝓜 μ (conj ∘ f), mulOperator_hasDenseDomain (by measurability),
    mulOperator_adjoint_eq_conj hf ▸ adjoint_isFormalAdjoint (mulOperator_hasDenseDomain hf)⟩

/-- Multiplication operators of `μ`-a.e. strongly measurable functions are unbounded. -/
lemma mulOperator_isUnbounded {μ : Measure (Space d)} [IsFiniteMeasureOnCompacts μ]
    {f : Space d → ℂ} (hf : AEStronglyMeasurable f μ) :
    (𝓜 μ f).IsUnbounded :=
  ⟨mulOperator_hasDenseDomain hf, mulOperator_isClosable hf⟩

/-- Multiplication operators of `μ`-a.e. strongly measurable functions are closed. -/
lemma mulOperator_isClosed {μ : Measure (Space d)} [IsFiniteMeasureOnCompacts μ]
    {f : Space d → ℂ} (hf : AEStronglyMeasurable f μ) :
    (𝓜 μ f).IsClosed := by
  apply (mulOperator_isUnbounded hf).isClosed_iff.mpr
  rw [mulOperator_adjoint_eq_conj hf, mulOperator_adjoint_eq_conj (by fun_prop)]
  congr 1; ext; simp

/-!
## E. Basic properties
-/

/-- The multiplication operator of the zero function is the zero operator (domain `⊤`). -/
@[simp]
lemma mulOperator_zero (μ : Measure (Space d)) : 𝓜 μ 0 = 0 := by
  ext ψ hψ hψ'
  · simp [mem_mulOperator_domain_iff]
  · refine (mulOperator_apply_ae ⟨ψ, hψ⟩).trans ?_
    simpa using coeFn_zero.symm

/-- `μ`-a.e. equal functions give rise to the same multiplication operator. -/
lemma mulOperator_eq_of_congr_ae {μ : Measure (Space d)} {f g : Space d → ℂ} (h : f =ᵐ[μ] g) :
    𝓜 μ f = 𝓜 μ g := by
  ext ψ hψ hψ'
  · exact memHS_congr_ae <| h.smul (ext_iff.mp rfl)
  · filter_upwards [h, mulOperator_apply_ae ⟨ψ, hψ⟩, mulOperator_apply_ae ⟨ψ, hψ'⟩]
    simp_all

TODO "Upgrade mulOperator_eq_of_congr_ae to an iff : 𝓜 μ f = 𝓜 μ g ↔ f =ᵐ[μ] g."

/-!
### E.1. Smul & neg
-/

/-- Scalar multiplication and `mulOperator` commute except possibly for `c = 0`
  where the domains of `0 • 𝓜 μ f` and `𝓜 μ 0 = 0` may not agree.

  See `mulOperator_const_smul_eq` for equality when `c ≠ 0`. -/
lemma mulOperator_const_smul_ge (μ : Measure (Space d)) (f : Space d → ℂ) (c : ℂ) :
    c • 𝓜 μ f ≤ 𝓜 μ (c • f) := by
  refine le_of_le_graph fun u h ↦ ?_
  rw [mem_graph_iff] at *
  obtain ⟨⟨v, hv⟩, hvu, hvu'⟩ := h
  have hv' : v ∈ (𝓜 μ (c • f)).domain := by
    rw [smul_domain, mem_mulOperator_domain_iff] at *
    simpa using hv.const_smul c
  refine ⟨⟨v, hv'⟩, hvu, ?_⟩
  rw [← hvu', ext_iff]
  filter_upwards [mulOperator_apply_ae ⟨v, hv⟩, mulOperator_apply_ae ⟨v, hv'⟩,
    coeFn_smul c (𝓜 μ f ⟨v, hv⟩)]
  simp_all [mul_assoc]

/-- Scalar multiplication and `mulOperator` commute for `c ≠ 0`. -/
@[simp]
lemma mulOperator_const_smul_eq (μ : Measure (Space d)) (f : Space d → ℂ) {c : ℂ} (hc : c ≠ 0) :
    𝓜 μ (c • f) = c • 𝓜 μ f := by
  refine (eq_of_le_of_domain_eq (mulOperator_const_smul_ge μ f c) ?_).symm
  ext
  simp [mem_mulOperator_domain_iff, memHS_const_smul_iff hc]

/-- Negation and `mulOperator` commute. -/
@[simp]
lemma mulOperator_neg (μ : Measure (Space d)) (f : Space d → ℂ) : 𝓜 μ (-f) = -𝓜 μ f := by
  rw [← neg_one_smul ℂ f, mulOperator_const_smul_eq μ f (by norm_num), neg_eq_neg_one_smul]

/-!
### E.2. Add & sub
-/

/-- `𝓜 μ (f + g)` extends `𝓜 μ f + 𝓜 μ g`.

  In general the domains do not match: `ψ ∈ (𝓜 μ f + 𝓜 μ g).domain` amounts to `MemHS (f • ψ) μ`
  _and_ `MemHS (g • ψ) μ` whereas `ψ ∈ (𝓜 μ (f + g)).domain` is equivalent to the weaker condition
  `MemHS ((f + g) • ψ) μ`.

  See `mulOperator_add_eq` and `mulOperator_add_eq'` for sufficient conditions
  to ensure equality. -/
lemma mulOperator_add_ge (μ : Measure (Space d)) (f g : Space d → ℂ) :
    𝓜 μ f + 𝓜 μ g ≤ 𝓜 μ (f + g) := by
  refine le_of_le_graph fun u h ↦ ?_
  rw [mem_graph_iff] at *
  obtain ⟨⟨v, hv⟩, hvu, hvu'⟩ := h
  have hv' : v ∈ (𝓜 μ (f + g)).domain := by
    rw [add_domain, Submodule.mem_inf] at hv
    simpa [add_mul, mem_mulOperator_domain_iff] using hv.1.add hv.2
  refine ⟨⟨v, hv'⟩, hvu, ?_⟩
  rw [← hvu', ext_iff]
  change _ =ᵐ[μ] 𝓜 μ f ⟨v, hv.1⟩ + 𝓜 μ g ⟨v, hv.2⟩
  filter_upwards [mulOperator_apply_ae ⟨v, hv.1⟩, mulOperator_apply_ae ⟨v, hv.2⟩,
    mulOperator_apply_ae ⟨v, hv'⟩, coeFn_add (𝓜 μ f ⟨v, hv.1⟩) (𝓜 μ g ⟨v, hv.2⟩)]
  simp_all [add_mul]

/-- `(𝓜 μ g).domain = ⊤` is a sufficient condition to ensure equality in `mulOperator_add_ge`. -/
@[simp]
lemma mulOperator_add_eq
    {μ : Measure (Space d)} (f : Space d → ℂ) {g : Space d → ℂ} (h : (𝓜 μ g).domain = ⊤) :
    𝓜 μ (f + g) = 𝓜 μ f + 𝓜 μ g := by
  have hle := mulOperator_add_ge μ f g
  refine (eq_of_le_of_domain_eq hle ?_).symm
  refine eq_of_le_of_ge hle.1 fun ψ hψ ↦ ?_
  have hg : ψ ∈ (𝓜 μ g).domain := by simp [h]
  simp only [add_domain, Submodule.mem_inf, mem_mulOperator_domain_iff] at *
  exact ⟨by simpa [add_mul] using hψ.sub hg, hg⟩

/-- Having both `‖f x‖ ≤ c * ‖f x + g x‖` and `‖g x‖ ≤ c' * ‖f x + g x‖` `μ`-a.e. is a sufficient
  condition to ensure equality in `mulOperator_add_ge`. -/
lemma mulOperator_add_eq' {μ : Measure (Space d)}
    {f g : Space d → ℂ} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (c c' : ℝ) (hf' : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖f x + g x‖) (hg' : ∀ᵐ x ∂μ, ‖g x‖ ≤ c' * ‖f x + g x‖) :
    𝓜 μ (f + g) = 𝓜 μ f + 𝓜 μ g := by
  have hle := mulOperator_add_ge μ f g
  refine (eq_of_le_of_domain_eq hle ?_).symm
  refine eq_of_le_of_ge hle.1 fun ψ hψ ↦ ⟨?_, ?_⟩
  · refine (hψ.const_smul c).mono (by fun_prop) ?_
    filter_upwards [hf'] with x h
    refine le_trans (b := c * (‖f x + g x‖ * ‖ψ x‖)) ?_ ?_
    · simp [← mul_assoc, mul_le_mul_of_nonneg_right h]
    · exact le_of_le_of_eq (mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)) (by simp)
  · refine (hψ.const_smul c').mono (by fun_prop) ?_
    filter_upwards [hg'] with x h
    refine le_trans (b := c' * (‖f x + g x‖ * ‖ψ x‖)) ?_ ?_
    · simp [← mul_assoc, mul_le_mul_of_nonneg_right h]
    · exact le_of_le_of_eq (mul_le_mul_of_nonneg_right (le_abs_self c') (by positivity)) (by simp)

/-- `𝓜 μ (f - g)` extends `𝓜 μ f - 𝓜 μ g`.

  In general the domains do not match: `ψ ∈ (𝓜 μ f - 𝓜 μ g).domain` amounts to `MemHS (f • ψ) μ`
  _and_ `MemHS (g • ψ) μ` whereas `ψ ∈ (𝓜 μ (f - g)).domain` is equivalent to the weaker condition
  `MemHS ((f - g) • ψ) μ`.

  See `mulOperator_sub_eq` and `mulOperator_sub_eq'` for sufficient conditions
  to ensure equality. -/
lemma mulOperator_sub_ge (μ : Measure (Space d)) (f g : Space d → ℂ) :
    𝓜 μ f - 𝓜 μ g ≤ 𝓜 μ (f - g) :=
  le_of_eq_of_le (by simp [sub_eq_add_neg]) (mulOperator_add_ge μ f (-g))

/-- `(𝓜 μ g).domain = ⊤` is a sufficient condition to ensure equality in `mulOperator_sub_ge`. -/
@[simp]
lemma mulOperator_sub_eq
    {μ : Measure (Space d)} (f : Space d → ℂ) {g : Space d → ℂ} (h : (𝓜 μ g).domain = ⊤) :
    𝓜 μ (f - g) = 𝓜 μ f - 𝓜 μ g := by
  simp [sub_eq_add_neg, mulOperator_add_eq, h]

/-- Having both `‖f x‖ ≤ c * ‖f x - g x‖` and `‖g x‖ ≤ c' * ‖f x - g x‖` `μ`-a.e. is a sufficient
  condition to ensure equality in `mulOperator_sub_ge`. -/
lemma mulOperator_sub_eq' {μ : Measure (Space d)}
    {f g : Space d → ℂ} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (c c' : ℝ) (hf' : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖f x - g x‖) (hg' : ∀ᵐ x ∂μ, ‖g x‖ ≤ c' * ‖f x - g x‖) :
    𝓜 μ (f - g) = 𝓜 μ f - 𝓜 μ g := by
  simp only [sub_eq_add_neg, ← mulOperator_neg]
  exact mulOperator_add_eq' hf hg.neg c c' (by simpa) (by simpa)

TODO "Add to the sufficient conditions which ensure `𝓜 μ (f ± g) = 𝓜 μ f ± 𝓜 μ g`."

/-!
### E.3. Composition
-/

/-- `𝓜 μ (f • g)` extends `𝓜 μ f * 𝓜 μ g`.

  In general the domains do not match: `ψ ∈ (𝓜 μ f * 𝓜 μ g).domain`
  amounts to `MemHS (g • ψ) μ` _and_ `MemHS (f • g • ψ) μ` whereas
  `ψ ∈ (𝓜 μ (f • g)).domain` only requires `MemHS (f • g • ψ) μ`.

  See `mulOperator_smul_eq` for a sufficient condition to ensure equality. -/
lemma mulOperator_smul_ge (μ : Measure (Space d)) (f g : Space d → ℂ) :
    𝓜 μ f ∘ᵣ 𝓜 μ g ≤ 𝓜 μ (f • g) := by
  constructor
  · intro ψ hψ
    obtain ⟨hψ, hgψ⟩ := mem_compRestricted_domain_iff.mp hψ
    refine (mem_mulOperator_domain_iff.mp hgψ).ae_eq ?_
    filter_upwards [mulOperator_apply_ae ⟨ψ, hψ⟩]
    simp_all [mul_assoc]
  · intro ψ φ hψφ
    apply ext_iff.mpr
    obtain ⟨hψ, hgψ⟩ := mem_compRestricted_domain_iff.mp ψ.2
    filter_upwards [mulOperator_apply_ae φ, mulOperator_apply_ae ⟨ψ, hψ⟩,
      mulOperator_apply_ae ⟨𝓜 μ g ⟨ψ, hψ⟩, hgψ⟩]
    simp_all [mul_assoc]

/-- `(𝓜 μ g).domain = ⊤` is a sufficient condition to ensure equality in `mulOperator_smul_ge`. -/
lemma mulOperator_smul_eq
    {μ : Measure (Space d)} (f : Space d → ℂ) {g : Space d → ℂ} (h : (𝓜 μ g).domain = ⊤) :
    𝓜 μ f ∘ᵣ 𝓜 μ g = 𝓜 μ (f • g) := by
  have hle := mulOperator_smul_ge μ f g
  refine eq_of_le_of_domain_eq hle ?_
  refine eq_of_le_of_ge hle.1 fun ψ hψ ↦ ?_
  refine mem_compRestricted_domain_iff.mpr ⟨h ▸ Submodule.mem_top, ?_⟩
  refine (mem_mulOperator_domain_iff.mp hψ).ae_eq ?_
  filter_upwards [mulOperator_apply_ae ⟨ψ, h ▸ Submodule.mem_top⟩]
  simp_all [mul_assoc]

TODO "`mulOperator_smul_eq` has the strong assumption `(𝓜 μ g).domain = ⊤`. Weaken this assumption
  and/or find other sufficient conditions to ensure the equality `𝓜 μ (f • g) = 𝓜 μ f * 𝓜 μ g`."

/-!
## F. Spectrum
-/

TODO "Prove that the spectrum of the multiplication operator `𝓜 μ f`
  is the 'μ-essential range' of `f`."

TODO "Prove that the spectrum of the multiplication operator `𝓜 μ f`
  is the closure of `f.range` for continuous `f`."

end
end SpaceDHilbertSpace
end QuantumMechanics
