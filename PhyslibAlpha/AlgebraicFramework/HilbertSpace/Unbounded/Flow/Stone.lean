/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.SelfAdjointSpectralTheorem
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Stone

/-!
# Stone generator of a domain-aware spectral theorem

This file is the operator-level hand-off from the real spectral integral to Stone's theorem.
The scalar and Hilbert-space limit is proved in `Stone`; the theorem below uses the domain
equality and self-adjoint uniqueness package from `SelfAdjointSpectralTheorem` to identify the
maximal spectral integral with the given unbounded operator.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology InnerProductSpace Function
open QuantumMechanics.WOTSpectralMeasure

namespace QuantumMechanics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →ₗ.[ℂ] H}
variable {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}

namespace DomainAwareSelfAdjointSpectralTheorem

/-- The spectral unitary group has strong derivative `iT` on the domain of its self-adjoint
generator.  This is the usable unbounded Stone theorem for a domain-aware spectral theorem.

The sign convention is the one used by `expIntegral`: the group is `exp (itT)`, so its generator
as a real-time derivative is `iT`. -/
theorem expUnitaryGroup_strong_slope_tendsto
    (D : DomainAwareSelfAdjointSpectralTheorem T μS) (x : T.domain) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (D.expUnitaryGroup t x - x))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (Complex.I • T x)) := by
  have hdom : ∀ y : T.domain, (y : H) ∈ spectralSquareMomentDomain μS := by
    intro y
    have hy : (y : H) ∈ (T.domain : Set H) := y.property
    rw [D.domain_eq_squareMoment] at hy
    exact hy
  have heq : maximalSpectralIntegral μS = T :=
    maximalSpectralIntegral_eq_of_isSelfAdjoint_of_isWeakSpectralResolution
      T D.isSelfAdjoint_of D.reconstruction_of hdom
  have hxmax : (x : H) ∈
      (QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral μS).domain := by
    rw [heq]
    exact x.property
  have hstrong :=
    QuantumMechanics.WOTSpectralMeasure.expIntegral_strong_slope_tendsto μS (x : H) hxmax
  change Filter.Tendsto
      (fun t : ℝ => t⁻¹ •
        (QuantumMechanics.WOTSpectralMeasure.expIntegral μS t (x : H) - (x : H)))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (Complex.I • T x))
  have hval :
      (QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral μS)
          ⟨(x : H), hxmax⟩ = T x := by
    cases heq
    rfl
  rw [hval] at hstrong
  exact hstrong

theorem expUnitaryGroup_hasDerivAt_zero
    (D : DomainAwareSelfAdjointSpectralTheorem T μS) (x : T.domain) :
    HasDerivAt (fun t : ℝ => D.expUnitaryGroup t (x : H))
      (Complex.I • T x) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  convert D.expUnitaryGroup_strong_slope_tendsto x using 1
  funext t
  simp [slope, D.expUnitaryGroup_zero]

/-- The Stone derivative at every time, not just at the identity.

The proof uses only the group law and the zero-time derivative.  In particular, no invariance
of the unbounded domain under the unitary group is needed: the translated difference quotient is
`U(s)` applied to the zero-time difference quotient of the original vector. -/
theorem expUnitaryGroup_hasDerivAt
    (D : DomainAwareSelfAdjointSpectralTheorem T μS) (x : T.domain) (s : ℝ) :
    HasDerivAt (fun t : ℝ => D.expUnitaryGroup t (x : H))
      (D.expUnitaryGroup s (Complex.I • T x)) s := by
  let U : H →L[ℂ] H :=
    ContinuousLinearMapWOT.toCLM
      (D.expUnitaryGroup s)
  have hzero : HasDerivAt
      (fun t : ℝ => D.expUnitaryGroup t (x : H))
      (Complex.I • T x) 0 := D.expUnitaryGroup_hasDerivAt_zero x
  have hshift : HasDerivAt
      (fun t : ℝ => D.expUnitaryGroup (t - s) (x : H))
      (Complex.I • T x) s := by
    have hsub : HasDerivAt (fun t : ℝ => t - s) 1 s := by
      simpa using (hasDerivAt_id' (𝕜 := ℝ) s).sub_const s
    simpa [Function.comp_def] using hzero.scomp_of_eq s hsub (by ring)
  let U' : H →L[ℝ] H := U.restrictScalars ℝ
  have hconst : HasDerivAt (fun _ : ℝ => U') 0 s := hasDerivAt_const s U'
  have happly := hconst.clm_apply hshift
  have happly' : HasDerivAt
      (fun t : ℝ => U' (D.expUnitaryGroup (t - s) (x : H)))
      (D.expUnitaryGroup s (Complex.I • T x)) s := by
    simpa [U', U] using happly
  apply happly'.congr_of_eventuallyEq
  filter_upwards [] with t
  have hgroup := D.expUnitaryGroup_add s (t - s)
  calc
    D.expUnitaryGroup t (x : H) = D.expUnitaryGroup (s + (t - s)) (x : H) := by
      exact congrArg (fun r : ℝ => D.expUnitaryGroup r (x : H)) (by ring)
    _ = (D.expUnitaryGroup s * D.expUnitaryGroup (t - s)) (x : H) := by
      rw [hgroup]
    _ = U' (D.expUnitaryGroup (t - s) (x : H)) := by
      rfl

theorem mem_domain_iff_expUnitaryGroup_strong_slope
    (D : DomainAwareSelfAdjointSpectralTheorem T μS) (x : H) :
    x ∈ T.domain ↔
      ∃ y : H, Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (D.expUnitaryGroup t x - x))
        (𝓝[≠] (0 : ℝ)) (𝓝 y) := by
  constructor
  · intro hx
    let x' : T.domain := ⟨x, hx⟩
    refine ⟨Complex.I • T x', ?_⟩
    exact D.expUnitaryGroup_strong_slope_tendsto x'
  · rintro ⟨y, hlim⟩
    change Filter.Tendsto
      (fun t : ℝ => t⁻¹ •
        (QuantumMechanics.WOTSpectralMeasure.expIntegral μS t x - x))
      (𝓝[≠] (0 : ℝ)) (𝓝 y) at hlim
    let τ : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)⁻¹
    have hτ0 : Filter.Tendsto τ Filter.atTop (𝓝 (0 : ℝ)) := by
      dsimp [τ]
      have hnat : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ))
          Filter.atTop Filter.atTop :=
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
      exact tendsto_inv_atTop_zero.comp hnat
    have hτ : Filter.Tendsto τ Filter.atTop (𝓝[≠] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hτ0, ?_⟩
      filter_upwards [] with n
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      dsimp [τ]
      positivity
    let F : ℕ → ℝ → ENNReal := fun n r =>
      ENNReal.ofReal (‖expSlope (τ n) r‖ ^ 2)
    have hF_meas : ∀ n, Measurable (F n) := by
      intro n
      exact ENNReal.continuous_ofReal.measurable.comp
        ((expSlope_measurable (τ n)).norm.pow_const 2)
    have hpoint : ∀ r : ℝ,
        Filter.Tendsto (fun n => ‖expSlope (τ n) r‖ ^ 2)
          Filter.atTop (𝓝 (r ^ 2)) := by
      intro r
      have h := (expSlope_tendsto r).comp hτ
      have h' := h.norm.mul h.norm
      simpa [Complex.norm_real, Real.norm_eq_abs, pow_two] using h'
    have hF_lim : ∀ r : ℝ,
        Filter.Tendsto (fun n => F n r) Filter.atTop
          (𝓝 (ENNReal.ofReal (r ^ 2))) := by
      intro r
      exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hpoint r)
    have hfatou :
        (∫⁻ r, Filter.liminf (fun n => F n r) Filter.atTop ∂μS.diagonalMeasure x) ≤
          Filter.liminf (fun n => ∫⁻ r, F n r ∂μS.diagonalMeasure x) Filter.atTop :=
      MeasureTheory.lintegral_liminf_le (μ := μS.diagonalMeasure x) hF_meas
    have hleft :
        (∫⁻ r, ENNReal.ofReal (r ^ 2) ∂μS.diagonalMeasure x) ≤
          Filter.liminf (fun n => ∫⁻ r, F n r ∂μS.diagonalMeasure x) Filter.atTop := by
      calc
        (∫⁻ r, ENNReal.ofReal (r ^ 2) ∂μS.diagonalMeasure x) =
            ∫⁻ r, Filter.liminf (fun n => F n r) Filter.atTop ∂μS.diagonalMeasure x := by
          apply MeasureTheory.lintegral_congr_ae
          filter_upwards [] with r
          exact (hF_lim r).liminf_eq.symm
        _ ≤ _ := hfatou
    have hgb : ∀ n, ∃ C : ℝ, ∀ r, ‖expSlope (τ n) r‖ ≤ C := by
      intro n
      refine ⟨2 * |τ n|⁻¹, fun r => ?_⟩
      rw [expSlope, norm_smul, Real.norm_eq_abs, abs_inv]
      calc
        |τ n|⁻¹ * ‖expFunction (τ n) r - 1‖ ≤ |τ n|⁻¹ * 2 :=
          mul_le_mul_of_nonneg_left
            (by
              calc
                ‖expFunction (τ n) r - 1‖ ≤
                    ‖expFunction (τ n) r‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
                _ = 2 := by rw [expFunction_modulus]; norm_num)
            (by positivity)
        _ = 2 * |τ n|⁻¹ := by ring
    have hF_norm_sq : ∀ n,
        ∫⁻ r, F n r ∂μS.diagonalMeasure x =
          ENNReal.ofReal (‖(τ n)⁻¹ •
            (QuantumMechanics.WOTSpectralMeasure.expIntegral μS (τ n) x - x)‖ ^ 2) := by
      intro n
      have hnorm := QuantumMechanics.WOTSpectralMeasure.boundedIntegral_norm_sq μS
        (expSlope_measurable (τ n)) (hgb n) x
      have hq := QuantumMechanics.WOTSpectralMeasure.expIntegral_slope_eq_boundedIntegral
        μS (τ n) x (hgb n)
      calc
        ∫⁻ r, F n r ∂μS.diagonalMeasure x =
            ∫⁻ r, ENNReal.ofReal (‖expSlope (τ n) r‖ ^ 2)
              ∂μS.diagonalMeasure x := by rfl
        _ = ENNReal.ofReal (‖QuantumMechanics.WOTSpectralMeasure.boundedIntegral μS
              (expSlope (τ n)) (expSlope_measurable (τ n)) (hgb n) x‖ ^ 2) :=
          hnorm.symm
        _ = ENNReal.ofReal (‖(τ n)⁻¹ •
              (QuantumMechanics.WOTSpectralMeasure.expIntegral μS (τ n) x - x)‖ ^ 2) := by
          rw [← hq]
    have hq_lim : Filter.Tendsto
        (fun n : ℕ => (τ n)⁻¹ •
          (QuantumMechanics.WOTSpectralMeasure.expIntegral μS (τ n) x - x))
        Filter.atTop (𝓝 y) := hlim.comp hτ
    have hq_norm_lim := hq_lim.norm.mul hq_lim.norm
    have hq_ennreal_lim : Filter.Tendsto
        (fun n : ℕ => ENNReal.ofReal (‖(τ n)⁻¹ •
          (QuantumMechanics.WOTSpectralMeasure.expIntegral μS (τ n) x - x)‖ ^ 2))
        Filter.atTop (𝓝 (ENNReal.ofReal (‖y‖ ^ 2))) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (by simpa [pow_two] using hq_norm_lim)
    have hright :
        Filter.liminf (fun n => ∫⁻ r, F n r ∂μS.diagonalMeasure x) Filter.atTop ≠ ⊤ := by
      rw [show (fun n => ∫⁻ r, F n r ∂μS.diagonalMeasure x) =
          (fun n => ENNReal.ofReal (‖(τ n)⁻¹ •
            (QuantumMechanics.WOTSpectralMeasure.expIntegral μS (τ n) x - x)‖ ^ 2))
        from funext hF_norm_sq]
      rw [hq_ennreal_lim.liminf_eq]
      exact ENNReal.ofReal_ne_top
    have hfinite :
        (∫⁻ r, ENNReal.ofReal (r ^ 2) ∂μS.diagonalMeasure x) < ⊤ :=
      lt_of_le_of_lt hleft (lt_top_iff_ne_top.mpr hright)
    have hxspec : x ∈ spectralSquareMomentDomain μS := by
      rw [mem_spectralSquareMomentDomain_iff]
      refine ⟨(measurable_id.pow_const 2).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      convert hfinite using 1
      apply MeasureTheory.lintegral_congr
      intro r
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg r)]
    exact (D.mem_domain_iff x).2 hxspec

theorem mem_domain_iff_expUnitaryGroup_hasDerivAt_zero
    (D : DomainAwareSelfAdjointSpectralTheorem T μS) (x : H) :
    x ∈ T.domain ↔
      ∃ y : H, HasDerivAt (fun t : ℝ => D.expUnitaryGroup t x) y 0 := by
  constructor
  · intro hx
    let x' : T.domain := ⟨x, hx⟩
    exact ⟨Complex.I • T x', D.expUnitaryGroup_hasDerivAt_zero x'⟩
  · rintro ⟨y, hy⟩
    apply (D.mem_domain_iff_expUnitaryGroup_strong_slope x).2
    rw [hasDerivAt_iff_tendsto_slope] at hy
    refine ⟨y, ?_⟩
    convert hy using 1
    funext t
    simp [slope, D.expUnitaryGroup_zero]

/-- The Stone unitary group satisfies the star/inverse law: the adjoint of `expUnitaryGroup t` is
`expUnitaryGroup (-t)`.  Both `star` and `⁻¹` agree here because every value lies in
`unitary (H →WOT[ℂ] H)`; this is the exact `WOT`-level identity `expIntegral_star` transported to
the domain-aware group. -/
theorem expUnitaryGroup_star (D : DomainAwareSelfAdjointSpectralTheorem T μS) (t : ℝ) :
    star (D.expUnitaryGroup t) = D.expUnitaryGroup (-t) :=
  QuantumMechanics.WOTSpectralMeasure.expIntegral_star μS t

end DomainAwareSelfAdjointSpectralTheorem

end QuantumMechanics

end
