/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.SpectralIntegral.Construction

/-!
# Canonical unbounded spectral integrals: the self-adjoint spectral theorem

Continues `SpectralIntegral/Construction.lean`: shows the maximal spectral integral has full
resolvent range off the real axis and is therefore self-adjoint (not merely essentially so), then
assembles `domainAwareSelfAdjointSpectralTheorem_of_isWeakSpectralResolution`, identifying the
operator's domain with the square-moment domain of its spectral measure.
-/

@[expose] public section

noncomputable section

open scoped Topology InnerProductSpace Function
open ContinuousLinearMap ContinuousLinearMapWOT MeasureTheory Set
open QuantumMechanics.WOTSpectralMeasure

namespace QuantumMechanics.WOTSpectralMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Weighted diagonal measures

Applying a bounded spectral multiplier changes the vector spectral measure by the squared
multiplier.  This is the measure-level statement that turns bounded resolvents into vectors in the
maximal square-moment domain.
-/

lemma diagonalMeasure_boundedIntegral_eq_withDensity
    {α : Type*} [MeasurableSpace α] [Nonempty α]
    (μS : WOTSpectralMeasure α H) {g : α → ℂ} (hg : Measurable g)
    (hgb : ∃ C : ℝ, ∀ a, ‖g a‖ ≤ C) (x : H) :
    μS.diagonalMeasure (boundedIntegral μS g hg hgb x) =
      Measure.withDensity (μS.diagonalMeasure x)
        (fun a => ENNReal.ofReal (‖g a‖ ^ 2)) := by
  apply Measure.ext
  intro S hS
  rw [μS.diagonalMeasure_apply_eq_norm_sq _ _ hS]
  let iS : α → ℂ := S.indicator (fun _ => (1 : ℂ))
  have hiS : Measurable iS := measurable_const.indicator hS
  have hiSb : ∃ C : ℝ, ∀ a, ‖iS a‖ ≤ C := by
    refine ⟨1, fun a => ?_⟩
    by_cases ha : a ∈ S <;> simp [iS, ha]
  have hmul := boundedIntegral_mul μS hiS hg hiSb hgb
  have hind := boundedIntegral_indicator μS hS
  have happly : μS S (boundedIntegral μS g hg hgb x) =
      boundedIntegral μS (iS * g) (hiS.mul hg)
        (by
          rcases hiSb with ⟨Ci, hCi⟩
          rcases hgb with ⟨Cg, hCg⟩
          refine ⟨Ci * Cg, fun a => ?_⟩
          rw [Pi.mul_apply, norm_mul]
          exact mul_le_mul (hCi a) (hCg a) (norm_nonneg _) (by
            exact (norm_nonneg (iS (Classical.choice (inferInstance : Nonempty α)))).trans
              (hCi _))) x := by
    rw [← hind]
    have h := congrArg (fun A : H →WOT[ℂ] H => A x) hmul
    simpa [ContinuousLinearMapWOT.mul_apply, iS] using h.symm
  rw [happly]
  rw [boundedIntegral_norm_sq μS (hiS.mul hg) _ x]
  rw [MeasureTheory.withDensity_apply _ hS]
  rw [← lintegral_indicator hS]
  congr 1
  funext a
  by_cases ha : a ∈ S
  · simp [iS, ha]
  · simp [iS, ha]

lemma expIntegral_mem_spectralSquareMomentDomain
    (μS : WOTSpectralMeasure ℝ H) (t : ℝ) (x : H)
    (hx : x ∈ spectralSquareMomentDomain μS) :
    expIntegral μS t x ∈ spectralSquareMomentDomain μS := by
  rw [mem_spectralSquareMomentDomain_iff] at hx ⊢
  have hmeasure : μS.diagonalMeasure (expIntegral μS t x) = μS.diagonalMeasure x := by
    rw [show expIntegral μS t x =
        boundedIntegral μS (expFunction t) (expFunction_measurable t)
          (expFunction_bounded t) x by rfl]
    rw [diagonalMeasure_boundedIntegral_eq_withDensity μS
      (expFunction_measurable t) (expFunction_bounded t) x]
    apply Measure.ext
    intro S hS
    rw [MeasureTheory.withDensity_apply _ hS]
    simp only [expFunction_modulus]
    norm_num [MeasureTheory.setLIntegral_one]
  rw [hmeasure]
  exact hx
@[nolint unusedArguments]

lemma boundedMultiplier_mem_spectralSquareMomentDomain
    {α : Type*} [MeasurableSpace α] [Nonempty α]
    (μS : WOTSpectralMeasure ℝ H) {g : ℝ → ℂ} (hg : Measurable g)
    (hgb : ∃ C : ℝ, ∀ a, ‖g a‖ ≤ C)
    (hcoord : ∀ a : ℝ, ‖(a : ℂ) * g a‖ ≤ 1) (x : H) :
    boundedIntegral μS g hg hgb x ∈ spectralSquareMomentDomain μS := by
  rw [mem_spectralSquareMomentDomain_iff]
  rw [diagonalMeasure_boundedIntegral_eq_withDensity μS hg hgb x]
  let d : ℝ → ENNReal := fun a => ENNReal.ofReal (‖g a‖ ^ 2)
  have hd : Measurable d := ENNReal.continuous_ofReal.measurable.comp
    (hg.norm.pow_const 2)
  have hd_top : ∀ᵐ a ∂μS.diagonalMeasure x, d a < (⊤ : ENNReal) := by
    filter_upwards [] with a
    exact (lt_top_iff_ne_top).2 (ENNReal.ofReal_ne_top)
  apply (integrable_withDensity_iff_integrable_smul₀' hd.aemeasurable hd_top).2
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [] with a
  have hsq : ‖(a : ℂ) * g a‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr (hcoord a)
  rw [show d a = ENNReal.ofReal (‖g a‖ ^ 2) by rfl]
  rw [ENNReal.toReal_ofReal (sq_nonneg (‖g a‖))]
  simp only [smul_eq_mul]
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (sq_nonneg (‖g a‖)) (sq_nonneg a))]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hsq
  nlinarith [sq_abs a]

/-! The unit bound used by the first resolvent construction is convenient, but it is not
mathematically essential.  Keeping the finite-bound version separate makes the later general
resolvent API usable at arbitrary non-real parameters without weakening any of the existing
callers. -/
@[nolint unusedArguments]

lemma boundedMultiplier_mem_spectralSquareMomentDomain_of_bound
    {α : Type*} [MeasurableSpace α] [Nonempty α]
    (μS : WOTSpectralMeasure ℝ H) {g : ℝ → ℂ} (hg : Measurable g)
    (hgb : ∃ C : ℝ, ∀ a, ‖g a‖ ≤ C)
    (hcoord : ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, ‖(a : ℂ) * g a‖ ≤ C) (x : H) :
    boundedIntegral μS g hg hgb x ∈ spectralSquareMomentDomain μS := by
  rw [mem_spectralSquareMomentDomain_iff]
  rw [diagonalMeasure_boundedIntegral_eq_withDensity μS hg hgb x]
  let d : ℝ → ENNReal := fun a => ENNReal.ofReal (‖g a‖ ^ 2)
  have hd : Measurable d := ENNReal.continuous_ofReal.measurable.comp
    (hg.norm.pow_const 2)
  have hd_top : ∀ᵐ a ∂μS.diagonalMeasure x, d a < (⊤ : ENNReal) := by
    filter_upwards [] with a
    exact (lt_top_iff_ne_top).2 (ENNReal.ofReal_ne_top)
  apply (integrable_withDensity_iff_integrable_smul₀' hd.aemeasurable hd_top).2
  rcases hcoord with ⟨C, hC0, hC⟩
  apply Integrable.of_bound (by fun_prop) (C ^ 2)
  filter_upwards [] with a
  have hsq : ‖(a : ℂ) * g a‖ ^ 2 ≤ C ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) hC0).mpr (hC a)
  rw [show d a = ENNReal.ofReal (‖g a‖ ^ 2) by rfl]
  rw [ENNReal.toReal_ofReal (sq_nonneg (‖g a‖))]
  simp only [smul_eq_mul]
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (sq_nonneg (‖g a‖)) (sq_nonneg a))]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hsq
  nlinarith [sq_abs a]

lemma maximalSpectralIntegral_apply_boundedMultiplier
    (μS : WOTSpectralMeasure ℝ H) {g : ℝ → ℂ} (hg : Measurable g)
    (hgb : ∃ C : ℝ, ∀ a, ‖g a‖ ≤ C)
    (hcoord : ∀ a : ℝ, ‖(a : ℂ) * g a‖ ≤ 1)
    (hcoord_meas : Measurable (fun a : ℝ => (a : ℂ) * g a))
    (x : H) :
    (maximalSpectralIntegral μS)
        ⟨boundedIntegral μS g hg hgb x,
          boundedMultiplier_mem_spectralSquareMomentDomain (α := ℝ) μS hg hgb hcoord x⟩ =
      boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a) hcoord_meas
        ⟨1, hcoord⟩ x := by
  let y : H := boundedIntegral μS g hg hgb x
  have hy : y ∈ spectralSquareMomentDomain μS :=
    boundedMultiplier_mem_spectralSquareMomentDomain (α := ℝ) μS hg hgb hcoord x
  let fn : ℕ → ℝ → ℂ := fun n a => truncationFunction n a * g a
  have hfn : ∀ n, Measurable (fn n) := by
    intro n
    exact (truncationFunction_measurable n).mul hg
  have hfn_bound_one : ∀ n a, ‖fn n a‖ ≤ (1 : ℝ) := by
    intro n a
    change ‖truncationFunction n a * g a‖ ≤ 1
    by_cases ha : a ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
    · rw [show truncationFunction n a = (a : ℂ) by
        simp [truncationFunction, Set.indicator_of_mem ha]]
      exact hcoord a
    · simp [truncationFunction, ha]
  have hfn_bound : ∀ n, ∃ C : ℝ, ∀ a, ‖fn n a‖ ≤ C := by
    intro n
    exact ⟨1, hfn_bound_one n⟩
  have hfn_lim : ∀ a : ℝ, Filter.Tendsto (fun n : ℕ => fn n a)
      Filter.atTop (𝓝 ((a : ℂ) * g a)) := by
    intro a
    have htrunc := truncationFunction_tendsto a
    exact htrunc.mul (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => g a) Filter.atTop (𝓝 (g a)))
  have hconv : Filter.Tendsto
      (fun n : ℕ => boundedIntegral μS (fn n) (hfn n) (hfn_bound n) x)
      Filter.atTop
      (𝓝 (boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a)
        hcoord_meas ⟨1, hcoord⟩ x)) :=
    boundedIntegral_tendsto_of_pointwise_tendsto_of_bound μS x hcoord_meas hfn
      ⟨1, hcoord⟩ ⟨1, hfn_bound_one⟩ hfn_lim
  have htrunc : Filter.Tendsto
      (fun n : ℕ => truncationIntegral μS n y) Filter.atTop (𝓝 (truncationLimit μS ⟨y, hy⟩)) :=
    truncationLimit_tendsto μS ⟨y, hy⟩
  have heq : ∀ n, truncationIntegral μS n y = boundedIntegral μS (fn n)
      (hfn n) (hfn_bound n) x := by
    intro n
    have hmul := boundedIntegral_mul μS (truncationFunction_measurable n) hg
      (truncationFunction_bounded n) hgb
    have happly := congrArg (fun A : H →WOT[ℂ] H => A x) hmul
    change truncationIntegral μS n (boundedIntegral μS g hg hgb x) = _
    change truncationIntegral μS n (boundedIntegral μS g hg hgb x) =
      boundedIntegral μS (truncationFunction n * g) (hfn n) (hfn_bound n) x
    convert happly.symm using 1;
      simp [truncationIntegral, ContinuousLinearMapWOT.mul_apply]
  have htrunc' : Filter.Tendsto
      (fun n : ℕ => boundedIntegral μS (fn n) (hfn n) (hfn_bound n) x) Filter.atTop
      (𝓝 (maximalSpectralIntegral μS ⟨y, hy⟩)) := by
    change Filter.Tendsto
      (fun n : ℕ => boundedIntegral μS (fn n) (hfn n) (hfn_bound n) x) Filter.atTop
      (𝓝 (truncationLimit μS ⟨y, hy⟩))
    exact htrunc.congr' (Filter.Eventually.of_forall fun n => heq n)
  exact tendsto_nhds_unique htrunc' hconv

lemma maximalSpectralIntegral_apply_boundedMultiplier_of_bound
    (μS : WOTSpectralMeasure ℝ H) {g : ℝ → ℂ} (hg : Measurable g)
    (hgb : ∃ C : ℝ, ∀ a, ‖g a‖ ≤ C)
    (hcoord : ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, ‖(a : ℂ) * g a‖ ≤ C)
    (hcoord_meas : Measurable (fun a : ℝ => (a : ℂ) * g a))
    (x : H) :
    (maximalSpectralIntegral μS)
        ⟨boundedIntegral μS g hg hgb x,
          boundedMultiplier_mem_spectralSquareMomentDomain_of_bound
            (α := ℝ) μS hg hgb hcoord x⟩ =
      boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a) hcoord_meas
        (by
          rcases hcoord with ⟨C, _hC0, hC⟩
          exact ⟨C, hC⟩) x := by
  rcases hcoord with ⟨C, hC0, hcoord⟩
  let y : H := boundedIntegral μS g hg hgb x
  have hy : y ∈ spectralSquareMomentDomain μS :=
    boundedMultiplier_mem_spectralSquareMomentDomain_of_bound (α := ℝ) μS hg hgb
      ⟨C, hC0, hcoord⟩ x
  let fn : ℕ → ℝ → ℂ := fun n a => truncationFunction n a * g a
  have hfn : ∀ n, Measurable (fn n) := by
    intro n
    exact (truncationFunction_measurable n).mul hg
  have hfn_bound_C : ∀ n a, ‖fn n a‖ ≤ C := by
    intro n a
    change ‖truncationFunction n a * g a‖ ≤ C
    by_cases ha : a ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
    · rw [show truncationFunction n a = (a : ℂ) by
        simp [truncationFunction, Set.indicator_of_mem ha]]
      exact hcoord a
    · simp [truncationFunction, ha, hC0]
  have hfn_bound : ∀ n, ∃ C' : ℝ, ∀ a, ‖fn n a‖ ≤ C' := by
    intro n
    exact ⟨C, hfn_bound_C n⟩
  have hfn_lim : ∀ a : ℝ, Filter.Tendsto (fun n : ℕ => fn n a)
      Filter.atTop (𝓝 ((a : ℂ) * g a)) := by
    intro a
    have htrunc := truncationFunction_tendsto a
    exact htrunc.mul (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => g a) Filter.atTop (𝓝 (g a)))
  have hconv : Filter.Tendsto
      (fun n : ℕ => boundedIntegral μS (fn n) (hfn n) (hfn_bound n) x)
      Filter.atTop
      (𝓝 (boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a) hcoord_meas
        ⟨C, hcoord⟩ x)) :=
    boundedIntegral_tendsto_of_pointwise_tendsto_of_bound μS x hcoord_meas hfn
      ⟨C, hcoord⟩ ⟨C, hfn_bound_C⟩ hfn_lim
  have htrunc : Filter.Tendsto
      (fun n : ℕ => truncationIntegral μS n y) Filter.atTop
      (𝓝 (truncationLimit μS ⟨y, hy⟩)) :=
    truncationLimit_tendsto μS ⟨y, hy⟩
  have heq : ∀ n, truncationIntegral μS n y = boundedIntegral μS (fn n)
      (hfn n) (hfn_bound n) x := by
    intro n
    have hmul := boundedIntegral_mul μS (truncationFunction_measurable n) hg
      (truncationFunction_bounded n) hgb
    have happly := congrArg (fun A : H →WOT[ℂ] H => A x) hmul
    change truncationIntegral μS n (boundedIntegral μS g hg hgb x) = _
    change truncationIntegral μS n (boundedIntegral μS g hg hgb x) =
      boundedIntegral μS (truncationFunction n * g) (hfn n) (hfn_bound n) x
    convert happly.symm using 1;
      simp [truncationIntegral, ContinuousLinearMapWOT.mul_apply]
  have htrunc' : Filter.Tendsto
      (fun n : ℕ => boundedIntegral μS (fn n) (hfn n) (hfn_bound n) x) Filter.atTop
      (𝓝 (maximalSpectralIntegral μS ⟨y, hy⟩)) := by
    change Filter.Tendsto
      (fun n : ℕ => boundedIntegral μS (fn n) (hfn n) (hfn_bound n) x) Filter.atTop
      (𝓝 (truncationLimit μS ⟨y, hy⟩))
    exact htrunc.congr' (Filter.Eventually.of_forall fun n => heq n)
  exact tendsto_nhds_unique htrunc' hconv

/-! ### The two Cayley resolvents

These are the bounded multipliers which realize the inverse of the shifts by `± i`.  Their
construction is independent of any pre-existing self-adjoint operator; it is purely the real PVM
calculus applied to the scalar functions `(r ± i)⁻¹`.
-/

/-- The scalar multiplier `r ↦ (r + i)⁻¹`. -/
def plusResolventMultiplier (r : ℝ) : ℂ := ((r : ℂ) + Complex.I)⁻¹

/-- The scalar multiplier `r ↦ (r - i)⁻¹`. -/
def minusResolventMultiplier (r : ℝ) : ℂ := ((r : ℂ) - Complex.I)⁻¹

/-- The scalar resolvent multiplier at an arbitrary non-real parameter. -/
def resolventMultiplier (z : ℂ) (r : ℝ) : ℂ := ((r : ℂ) - z)⁻¹

lemma resolventMultiplier_measurable (z : ℂ) :
    Measurable (resolventMultiplier z) := by
  unfold resolventMultiplier
  fun_prop

lemma resolventMultiplier_denom_ne_zero {z : ℂ} (hz : z.im ≠ 0) (r : ℝ) :
    (r : ℂ) - z ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  exact hz (by simpa using hi)

lemma resolventMultiplier_bounded {z : ℂ} (hz : z.im ≠ 0) :
    ∃ C : ℝ, ∀ r, ‖resolventMultiplier z r‖ ≤ C := by
  let d : ℝ := ‖(z.im : ℂ)‖
  have hd : 0 < d := by
    dsimp [d]
    exact norm_pos_iff.mpr (Complex.ofReal_ne_zero.mpr hz)
  refine ⟨d⁻¹, fun r => ?_⟩
  have hden : d ≤ ‖(r : ℂ) - z‖ := by
    dsimp [d]
    simpa [Complex.norm_real, abs_neg] using
      (Complex.abs_im_le_norm ((r : ℂ) - z))
  rw [resolventMultiplier, norm_inv]
  exact (inv_le_inv₀ (norm_pos_iff.mpr (resolventMultiplier_denom_ne_zero hz r)) hd).2 hden

lemma resolventMultiplier_coordinate_bounded {z : ℂ} (hz : z.im ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
      ‖(r : ℂ) * resolventMultiplier z r‖ ≤ C := by
  let d : ℝ := ‖(z.im : ℂ)‖
  have hd : 0 < d := by
    dsimp [d]
    exact norm_pos_iff.mpr (Complex.ofReal_ne_zero.mpr hz)
  refine ⟨1 + ‖z‖ * d⁻¹, by positivity, fun r => ?_⟩
  have hdenpos : 0 < ‖(r : ℂ) - z‖ :=
    norm_pos_iff.mpr (resolventMultiplier_denom_ne_zero hz r)
  have hden : d ≤ ‖(r : ℂ) - z‖ := by
    dsimp [d]
    simpa [Complex.norm_real, abs_neg] using
      (Complex.abs_im_le_norm ((r : ℂ) - z))
  have hr : ‖(r : ℂ)‖ ≤ ‖(r : ℂ) - z‖ + ‖z‖ := by
    calc
      ‖(r : ℂ)‖ = ‖((r : ℂ) - z) + z‖ := by congr 1; ring
      _ ≤ ‖(r : ℂ) - z‖ + ‖z‖ := norm_add_le _ _
  rw [resolventMultiplier, norm_mul, norm_inv]
  calc
    ‖(r : ℂ)‖ * ‖(↑r - z)‖⁻¹ ≤
        (‖(r : ℂ) - z‖ + ‖z‖) * ‖(↑r - z)‖⁻¹ :=
      mul_le_mul_of_nonneg_right hr (inv_nonneg.mpr (le_of_lt hdenpos))
    _ = 1 + ‖z‖ / ‖(r : ℂ) - z‖ := by
      field_simp
    _ ≤ 1 + ‖z‖ * d⁻¹ := by
      have hterm : ‖z‖ * ‖(r : ℂ) - z‖⁻¹ ≤ ‖z‖ * d⁻¹ :=
        mul_le_mul_of_nonneg_left ((inv_le_inv₀ hdenpos hd).2 hden)
          (norm_nonneg z)
      simpa [div_eq_mul_inv] using add_le_add_left hterm 1

lemma resolventMultiplier_coordinate_measurable (z : ℂ) :
    Measurable (fun r : ℝ => (r : ℂ) * resolventMultiplier z r) := by
  unfold resolventMultiplier
  fun_prop

lemma resolventMultiplier_identity {z : ℂ} (hz : z.im ≠ 0) (r : ℝ) :
    (r : ℂ) * resolventMultiplier z r - z * resolventMultiplier z r = 1 := by
  unfold resolventMultiplier
  rw [← sub_mul]
  have hne := resolventMultiplier_denom_ne_zero hz r
  exact mul_inv_cancel₀ hne

lemma plusResolventMultiplier_measurable :
    Measurable plusResolventMultiplier := by
  unfold plusResolventMultiplier
  fun_prop

lemma minusResolventMultiplier_measurable :
    Measurable minusResolventMultiplier := by
  unfold minusResolventMultiplier
  fun_prop

lemma plusResolventMultiplier_bounded :
    ∃ C : ℝ, ∀ r, ‖plusResolventMultiplier r‖ ≤ C := by
  refine ⟨1, fun r => ?_⟩
  have hne : (r : ℂ) + Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hpos : 0 < ‖(r : ℂ) + Complex.I‖ := norm_pos_iff.mpr hne
  have hden : (1 : ℝ) ≤ ‖(r : ℂ) + Complex.I‖ := by
    simpa using Complex.abs_im_le_norm ((r : ℂ) + Complex.I)
  rw [plusResolventMultiplier, norm_inv]
  exact (inv_le_one₀ hpos).2 hden

lemma minusResolventMultiplier_bounded :
    ∃ C : ℝ, ∀ r, ‖minusResolventMultiplier r‖ ≤ C := by
  refine ⟨1, fun r => ?_⟩
  have hne : (r : ℂ) - Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hpos : 0 < ‖(r : ℂ) - Complex.I‖ := norm_pos_iff.mpr hne
  have hden : (1 : ℝ) ≤ ‖(r : ℂ) - Complex.I‖ := by
    simpa using Complex.abs_im_le_norm ((r : ℂ) - Complex.I)
  rw [minusResolventMultiplier, norm_inv]
  exact (inv_le_one₀ hpos).2 hden

lemma plusResolventMultiplier_coordinate_bounded :
    ∀ r : ℝ, ‖(r : ℂ) * plusResolventMultiplier r‖ ≤ 1 := by
  intro r
  have hne : (r : ℂ) + Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hpos : 0 < ‖(r : ℂ) + Complex.I‖ := norm_pos_iff.mpr hne
  have hden : ‖(r : ℂ)‖ ≤ ‖(r : ℂ) + Complex.I‖ := by
    simpa using Complex.abs_re_le_norm ((r : ℂ) + Complex.I)
  rw [plusResolventMultiplier, norm_mul, norm_inv]
  apply (div_le_one hpos).2
  exact hden

lemma minusResolventMultiplier_coordinate_bounded :
    ∀ r : ℝ, ‖(r : ℂ) * minusResolventMultiplier r‖ ≤ 1 := by
  intro r
  have hne : (r : ℂ) - Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hpos : 0 < ‖(r : ℂ) - Complex.I‖ := norm_pos_iff.mpr hne
  have hden : ‖(r : ℂ)‖ ≤ ‖(r : ℂ) - Complex.I‖ := by
    simpa using Complex.abs_re_le_norm ((r : ℂ) - Complex.I)
  rw [minusResolventMultiplier, norm_mul, norm_inv]
  apply (div_le_one hpos).2
  exact hden

lemma plusResolventMultiplier_coordinate_measurable :
    Measurable (fun r : ℝ => (r : ℂ) * plusResolventMultiplier r) := by
  unfold plusResolventMultiplier
  fun_prop

lemma minusResolventMultiplier_coordinate_measurable :
    Measurable (fun r : ℝ => (r : ℂ) * minusResolventMultiplier r) := by
  unfold minusResolventMultiplier
  fun_prop

lemma maximalSpectralIntegral_shift_range_of_multiplier
    (μS : WOTSpectralMeasure ℝ H) (c : ℂ) {g : ℝ → ℂ} (hg : Measurable g)
    (hgb : ∃ C : ℝ, ∀ a, ‖g a‖ ≤ C)
    (hcoord : ∀ a : ℝ, ‖(a : ℂ) * g a‖ ≤ 1)
    (hcoord_meas : Measurable (fun a : ℝ => (a : ℂ) * g a))
    (hidentity : ∀ a : ℝ, (a : ℂ) * g a + c * g a = 1) :
    (maximalSpectralIntegral μS + c • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro x
  let y : H := boundedIntegral μS g hg hgb x
  have hy : y ∈ spectralSquareMomentDomain μS :=
    boundedMultiplier_mem_spectralSquareMomentDomain (α := ℝ) μS hg hgb hcoord x
  have haction := maximalSpectralIntegral_apply_boundedMultiplier μS hg hgb hcoord
    hcoord_meas x
  have hgbc : ∃ C : ℝ, ∀ a, ‖c * g a‖ ≤ C := by
    rcases hgb with ⟨C, hC⟩
    refine ⟨‖c‖ * C, fun a => ?_⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC a) (norm_nonneg c)
  have hg_c : Measurable (fun a : ℝ => c * g a) := measurable_const.mul hg
  have hadd := boundedIntegral_add μS hcoord_meas hg_c
    (⟨1, hcoord⟩) hgbc
  have hsmul := boundedIntegral_smul μS c hg hgb
  have hsum_bound : ∃ C : ℝ, ∀ a : ℝ, ‖(a : ℂ) * g a + c * g a‖ ≤ C := by
    rcases hgbc with ⟨C, hC⟩
    refine ⟨1 + C, fun a => ?_⟩
    exact (norm_add_le _ _).trans (add_le_add (hcoord a) (hC a))
  have hsum : boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a)
      hcoord_meas ⟨1, hcoord⟩ x + c • y = x := by
    calc
      _ = boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a)
          hcoord_meas ⟨1, hcoord⟩ x +
          boundedIntegral μS (fun a : ℝ => c * g a) hg_c hgbc x := by
        rw [hsmul]
        simp [y, ContinuousLinearMapWOT.smul_apply]
      _ = boundedIntegral μS
          ((fun a : ℝ => (a : ℂ) * g a) + (fun a : ℝ => c * g a))
          (hcoord_meas.add hg_c) _ x := by
        rw [hadd]
        simp [ContinuousLinearMapWOT.add_apply]
      _ = boundedIntegral μS (fun _ : ℝ => (1 : ℂ)) measurable_const
          (⟨1, fun _ => by simp⟩) x := by
        have hcongr := boundedIntegral_congr μS (hcoord_meas.add hg_c) measurable_const
          hsum_bound (⟨1, fun _ => norm_one.le⟩)
          (fun a => by simp only [Pi.add_apply]; exact hidentity a)
        exact congrArg (fun A : H →WOT[ℂ] H => A x) hcongr
      _ = x := by
        rw [boundedIntegral_const]
        simp [ContinuousLinearMapWOT.one_apply]
  let yz : (maximalSpectralIntegral μS + c • (1 : H →ₗ.[ℂ] H)).domain :=
    ⟨y, Submodule.mem_inf.mpr ⟨hy, Submodule.mem_top⟩⟩
  refine ⟨yz, ?_⟩
  change (maximalSpectralIntegral μS) ⟨y, hy⟩ + c • y = x
  rw [haction]
  exact hsum

lemma maximalSpectralIntegral_shift_range_of_multiplier_of_bound
    (μS : WOTSpectralMeasure ℝ H) (c : ℂ) {g : ℝ → ℂ} (hg : Measurable g)
    (hgb : ∃ C : ℝ, ∀ a, ‖g a‖ ≤ C)
    (hcoord : ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, ‖(a : ℂ) * g a‖ ≤ C)
    (hcoord_meas : Measurable (fun a : ℝ => (a : ℂ) * g a))
    (hidentity : ∀ a : ℝ, (a : ℂ) * g a + c * g a = 1) :
    (maximalSpectralIntegral μS + c • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤ := by
  rcases hcoord with ⟨C, hC0, hcoord⟩
  rw [LinearMap.range_eq_top]
  intro x
  let y : H := boundedIntegral μS g hg hgb x
  have hy : y ∈ spectralSquareMomentDomain μS :=
    boundedMultiplier_mem_spectralSquareMomentDomain_of_bound (α := ℝ) μS hg hgb
      ⟨C, hC0, hcoord⟩ x
  have haction := maximalSpectralIntegral_apply_boundedMultiplier_of_bound μS hg hgb
    ⟨C, hC0, hcoord⟩ hcoord_meas x
  have hgbc : ∃ C' : ℝ, ∀ a, ‖c * g a‖ ≤ C' := by
    rcases hgb with ⟨Cg, hCg⟩
    refine ⟨‖c‖ * Cg, fun a => ?_⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hCg a) (norm_nonneg c)
  have hg_c : Measurable (fun a : ℝ => c * g a) := measurable_const.mul hg
  have hadd := boundedIntegral_add μS hcoord_meas hg_c
    (⟨C, hcoord⟩) hgbc
  have hsmul := boundedIntegral_smul μS c hg hgb
  have hsum_bound : ∃ C' : ℝ, ∀ a : ℝ,
      ‖(a : ℂ) * g a + c * g a‖ ≤ C' := by
    rcases hgbc with ⟨Cc, hCc⟩
    refine ⟨C + Cc, fun a => ?_⟩
    exact (norm_add_le _ _).trans (add_le_add (hcoord a) (hCc a))
  have hsum : boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a)
      hcoord_meas ⟨C, hcoord⟩ x + c • y = x := by
    calc
      _ = boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a)
          hcoord_meas ⟨C, hcoord⟩ x +
          boundedIntegral μS (fun a : ℝ => c * g a) hg_c hgbc x := by
        rw [hsmul]
        simp [y, ContinuousLinearMapWOT.smul_apply]
      _ = boundedIntegral μS
          ((fun a : ℝ => (a : ℂ) * g a) + (fun a : ℝ => c * g a))
          (hcoord_meas.add hg_c) _ x := by
        rw [hadd]
        simp [ContinuousLinearMapWOT.add_apply]
      _ = boundedIntegral μS (fun _ : ℝ => (1 : ℂ)) measurable_const
          (⟨1, fun _ => by simp⟩) x := by
        have hcongr := boundedIntegral_congr μS (hcoord_meas.add hg_c) measurable_const
          hsum_bound (⟨1, fun _ => norm_one.le⟩)
          (fun a => by simp only [Pi.add_apply]; exact hidentity a)
        exact congrArg (fun A : H →WOT[ℂ] H => A x) hcongr
      _ = x := by
        rw [boundedIntegral_const]
        simp [ContinuousLinearMapWOT.one_apply]
  let yz : (maximalSpectralIntegral μS + c • (1 : H →ₗ.[ℂ] H)).domain :=
    ⟨y, Submodule.mem_inf.mpr ⟨hy, Submodule.mem_top⟩⟩
  refine ⟨yz, ?_⟩
  change (maximalSpectralIntegral μS) ⟨y, hy⟩ + c • y = x
  rw [haction]
  exact hsum

/-- Every non-real shift of the canonical spectral integral is onto.  This is the concrete range
form of the resolvent theorem, proved directly from the bounded scalar multiplier
`r ↦ (r - z)⁻¹`. -/
lemma maximalSpectralIntegral_resolvent_range {z : ℂ} (hz : z.im ≠ 0) :
    (maximalSpectralIntegral μS - z • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤ := by
  have hidentity : ∀ r : ℝ,
      (r : ℂ) * resolventMultiplier z r + (-z) * resolventMultiplier z r = 1 := by
    intro r
    simpa [neg_mul, sub_eq_add_neg] using resolventMultiplier_identity hz r
  have hplus : (maximalSpectralIntegral μS + (-z) • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤ :=
    maximalSpectralIntegral_shift_range_of_multiplier_of_bound μS (-z)
      (resolventMultiplier_measurable z) (resolventMultiplier_bounded hz)
      (resolventMultiplier_coordinate_bounded hz)
      (resolventMultiplier_coordinate_measurable z) hidentity
  have heq : maximalSpectralIntegral μS - z • (1 : H →ₗ.[ℂ] H) =
      maximalSpectralIntegral μS + (-z) • (1 : H →ₗ.[ℂ] H) := by
    exact LinearPMap.ext rfl fun x hx₁ hx₂ => by
      simp only [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply,
        neg_smul]
      module
  rw [heq]
  exact hplus

/-- The value of the inverse of a general non-real shift is the corresponding bounded spectral
multiplier.  This is the operator-level resolvent formula, including its domain proof. -/
lemma maximalSpectralIntegral_resolvent_inverse_apply {z : ℂ} (hz : z.im ≠ 0) (x : H) :
    (maximalSpectralIntegral μS - z • (1 : H →ₗ.[ℂ] H)).inverse
        ⟨x, by
          rw [LinearPMap.inverse_domain, maximalSpectralIntegral_resolvent_range hz]
          exact Submodule.mem_top⟩ =
      boundedIntegral μS (resolventMultiplier z) (resolventMultiplier_measurable z)
        (resolventMultiplier_bounded hz) x := by
  let M := maximalSpectralIntegral μS
  let g := resolventMultiplier z
  have htarget := maximalSpectralIntegral_resolvent_range (μS := μS) hz
  have hself : IsSelfAdjoint M := by
    apply maximalSpectralIntegral_isSelfAdjoint_of_range_eq_top μS
    · have h := maximalSpectralIntegral_resolvent_range
          (μS := μS) (z := -Complex.I) (by norm_num)
      have heq : M + Complex.I • (1 : H →ₗ.[ℂ] H) =
          M - (-Complex.I) • (1 : H →ₗ.[ℂ] H) := by
        exact LinearPMap.ext rfl fun y hy₁ hy₂ => by
          simp only [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply,
            neg_smul]
          module
      change (M + Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤
      rw [heq]
      exact h
    · simpa [M] using (maximalSpectralIntegral_resolvent_range
        (μS := μS) (z := Complex.I) (by norm_num))
  have hker : (M - z • (1 : H →ₗ.[ℂ] H)).toFun.ker = ⊥ := by
    have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero
      hself hz
    exact hres.1
  have hcoord := resolventMultiplier_coordinate_bounded hz
  have hy : boundedIntegral μS g (resolventMultiplier_measurable z)
      (resolventMultiplier_bounded hz) x ∈
        spectralSquareMomentDomain μS :=
    boundedMultiplier_mem_spectralSquareMomentDomain_of_bound (α := ℝ) μS
      (resolventMultiplier_measurable z) (resolventMultiplier_bounded hz) hcoord x
  let yM : M.domain :=
    ⟨boundedIntegral μS g (resolventMultiplier_measurable z)
      (resolventMultiplier_bounded hz) x, by
        change boundedIntegral μS g (resolventMultiplier_measurable z)
          (resolventMultiplier_bounded hz) x ∈
            spectralSquareMomentDomain μS
        exact hy⟩
  let y : (M - z • (1 : H →ₗ.[ℂ] H)).domain :=
    ⟨(yM : H), Submodule.mem_inf.mpr ⟨hy, Submodule.mem_top⟩⟩
  have haction := maximalSpectralIntegral_apply_boundedMultiplier_of_bound μS
    (resolventMultiplier_measurable z) (resolventMultiplier_bounded hz) hcoord
    (resolventMultiplier_coordinate_measurable z) x
  have hzg_bound : ∃ C : ℝ, ∀ r : ℝ,
      ‖z * g r‖ ≤ C := by
    rcases resolventMultiplier_bounded hz with ⟨C, hC⟩
    refine ⟨‖z‖ * C, fun r => ?_⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC r) (norm_nonneg z)
  have hsum : (M - z • (1 : H →ₗ.[ℂ] H)) y = x := by
    change M yM - z • (y : H) = x
    have hscaled : z • (y : H) =
        boundedIntegral μS (fun r : ℝ => z * g r)
          (measurable_const.mul (resolventMultiplier_measurable z)) hzg_bound x := by
      have h := congrArg (fun A : H →WOT[ℂ] H => A x)
        (boundedIntegral_smul μS z (resolventMultiplier_measurable z)
          (resolventMultiplier_bounded hz))
      simpa [y, yM, Pi.mul_apply] using h.symm
    rw [haction, hscaled]
    have hsub := boundedIntegral_sub μS
      (f := fun r : ℝ => (r : ℂ) * g r)
      (g := fun r : ℝ => z * g r)
      (resolventMultiplier_coordinate_measurable z)
      (measurable_const.mul (resolventMultiplier_measurable z))
      (by rcases hcoord with ⟨C, hC0, hC⟩; exact ⟨C, hC⟩) hzg_bound
    have hsubx := congrArg (fun A : H →WOT[ℂ] H => A x) hsub
    rw [← ContinuousLinearMapWOT.sub_apply, ← hsubx]
    have hcongr : ∀ r : ℝ,
        (r : ℂ) * g r - z * g r = (1 : ℂ) := by
      intro r
      exact resolventMultiplier_identity hz r
    have hfunit : Measurable (fun r : ℝ => (r : ℂ) * g r - z * g r) := by
      exact (resolventMultiplier_coordinate_measurable z).sub
        (measurable_const.mul (resolventMultiplier_measurable z))
    have hbunit : ∃ C : ℝ, ∀ r : ℝ,
        ‖(r : ℂ) * g r - z * g r‖ ≤ C := by
      rcases hcoord with ⟨C, hC0, hC⟩
      rcases hzg_bound with ⟨Cz, hCz⟩
      refine ⟨C + Cz, fun r => ?_⟩
      exact (norm_sub_le _ _).trans (add_le_add (hC r) (hCz r))
    have hunit : boundedIntegral μS
        ((fun r : ℝ => (r : ℂ) * g r) - (fun r : ℝ => z * g r))
        ((resolventMultiplier_coordinate_measurable z).sub
          (measurable_const.mul (resolventMultiplier_measurable z))) hbunit =
        boundedIntegral μS (fun _ : ℝ => (1 : ℂ)) measurable_const
          ⟨1, fun _ => by simp⟩ := by
      apply boundedIntegral_congr
      intro r
      simpa [Pi.sub_apply] using hcongr r
    have hunitx := congrArg (fun A : H →WOT[ℂ] H => A x) hunit
    convert hunitx using 1
    simp only [boundedIntegral_const]
    simp only [one_smul, ContinuousLinearMapWOT.one_apply]
  let x' : (M - z • (1 : H →ₗ.[ℂ] H)).inverse.domain :=
    ⟨x, by
      rw [LinearPMap.inverse_domain, htarget]
      exact Submodule.mem_top⟩
  have hxy : (M - z • (1 : H →ₗ.[ℂ] H)) y = x' := by
    simpa [x'] using hsum
  exact LinearPMap.inverse_apply_eq hker hxy

lemma maximalSpectralIntegral_plus_resolvent_range :
    (maximalSpectralIntegral μS + Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤ := by
  have hidentity : ∀ a : ℝ,
      (a : ℂ) * plusResolventMultiplier a + Complex.I * plusResolventMultiplier a = 1 := by
    intro a
    unfold plusResolventMultiplier
    have hne : (a : ℂ) + Complex.I ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      norm_num at hi
    calc
      (a : ℂ) * ((a : ℂ) + Complex.I)⁻¹ + Complex.I *
          ((a : ℂ) + Complex.I)⁻¹ =
          ((a : ℂ) + Complex.I) * ((a : ℂ) + Complex.I)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ hne
  exact maximalSpectralIntegral_shift_range_of_multiplier μS Complex.I
    plusResolventMultiplier_measurable plusResolventMultiplier_bounded
    plusResolventMultiplier_coordinate_bounded
    plusResolventMultiplier_coordinate_measurable hidentity

lemma maximalSpectralIntegral_minus_resolvent_range :
    (maximalSpectralIntegral μS - Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤ := by
  have hidentity : ∀ a : ℝ,
      (a : ℂ) * minusResolventMultiplier a + (-Complex.I) * minusResolventMultiplier a = 1 := by
    intro a
    unfold minusResolventMultiplier
    have hne : (a : ℂ) - Complex.I ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      norm_num at hi
    calc
      (a : ℂ) * ((a : ℂ) - Complex.I)⁻¹ + (-Complex.I) *
          ((a : ℂ) - Complex.I)⁻¹ =
          ((a : ℂ) - Complex.I) * ((a : ℂ) - Complex.I)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ hne
  have hplus : (maximalSpectralIntegral μS + (-Complex.I) •
      (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤ :=
    maximalSpectralIntegral_shift_range_of_multiplier μS (-Complex.I)
      minusResolventMultiplier_measurable minusResolventMultiplier_bounded
      minusResolventMultiplier_coordinate_bounded
      minusResolventMultiplier_coordinate_measurable hidentity
  have heq : maximalSpectralIntegral μS - Complex.I • (1 : H →ₗ.[ℂ] H) =
      maximalSpectralIntegral μS + (-Complex.I) • (1 : H →ₗ.[ℂ] H) := by
    exact LinearPMap.ext rfl fun x hx₁ hx₂ => by
      simp only [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply,
        neg_smul]
      module
  rw [heq]
  exact hplus

/-! ### Resolvent values of the maximal realization

The range statements above show that the two shifted maximal realizations are onto.  The
following sharpen them to an actual value formula for their partial inverses.  This is the
operator-level form of the bounded Borel identities

`(λ + i)⁻¹ (λ + i) = 1` and `(λ - i)⁻¹ (λ - i) = 1`.

These lemmas are intentionally stated for `LinearPMap.inverse`: they do not introduce a second
unbounded-operator hierarchy, and they are exactly what the Cayley adapter needs when converting
between a self-adjoint operator and its bounded unitary transform. -/

lemma maximalSpectralIntegral_plus_resolvent_inverse_apply (x : H) :
    (maximalSpectralIntegral μS + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse
        ⟨x, by
          rw [LinearPMap.inverse_domain, maximalSpectralIntegral_plus_resolvent_range]
          exact Submodule.mem_top⟩ =
      boundedIntegral μS plusResolventMultiplier plusResolventMultiplier_measurable
        plusResolventMultiplier_bounded x := by
  let M := maximalSpectralIntegral μS
  let g := plusResolventMultiplier
  have hker : (M + Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.ker = ⊥ := by
    have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero
      (maximalSpectralIntegral_isSelfAdjoint_of_range_eq_top μS
        (maximalSpectralIntegral_plus_resolvent_range (μS := μS))
        (maximalSpectralIntegral_minus_resolvent_range (μS := μS)))
      (z := -Complex.I) (by norm_num)
    have heq : M - (-Complex.I) • (1 : H →ₗ.[ℂ] H) =
        M + Complex.I • (1 : H →ₗ.[ℂ] H) := by
      exact LinearPMap.ext rfl fun y hy₁ hy₂ => by
        simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply,
          neg_smul]
    rw [← heq]
    exact hres.1
  have hy : boundedIntegral μS g plusResolventMultiplier_measurable
      plusResolventMultiplier_bounded x ∈
        spectralSquareMomentDomain μS :=
    boundedMultiplier_mem_spectralSquareMomentDomain (α := ℝ) μS
      plusResolventMultiplier_measurable plusResolventMultiplier_bounded
      plusResolventMultiplier_coordinate_bounded x
  let yM : M.domain := ⟨boundedIntegral μS g plusResolventMultiplier_measurable
    plusResolventMultiplier_bounded x, hy⟩
  let y : (M + Complex.I • (1 : H →ₗ.[ℂ] H)).domain :=
    ⟨(yM : H), Submodule.mem_inf.mpr ⟨hy, Submodule.mem_top⟩⟩
  have haction := maximalSpectralIntegral_apply_boundedMultiplier μS
    plusResolventMultiplier_measurable plusResolventMultiplier_bounded
    plusResolventMultiplier_coordinate_bounded
    plusResolventMultiplier_coordinate_measurable x
  have hIbound : ∃ C : ℝ, ∀ a : ℝ, ‖Complex.I * g a‖ ≤ C := by
    rcases plusResolventMultiplier_bounded with ⟨C, hC⟩
    refine ⟨C, fun a => ?_⟩
    simpa [norm_mul] using hC a
  have hsum : (M + Complex.I • (1 : H →ₗ.[ℂ] H)) y = x := by
    change M yM + Complex.I • (y : H) = x
    have hscaled : Complex.I • (y : H) =
        boundedIntegral μS (fun a : ℝ => Complex.I * g a)
          (measurable_const.mul plusResolventMultiplier_measurable) hIbound x := by
      have h := congrArg (fun A : H →WOT[ℂ] H => A x)
        (boundedIntegral_smul μS Complex.I plusResolventMultiplier_measurable
          plusResolventMultiplier_bounded)
      simpa [y, yM, Pi.mul_apply] using h.symm
    rw [haction, hscaled]
    have hadd := boundedIntegral_add μS
      (f := fun a : ℝ => (a : ℂ) * g a)
      (g := fun a : ℝ => Complex.I * g a)
      plusResolventMultiplier_coordinate_measurable
      (measurable_const.mul plusResolventMultiplier_measurable)
      (⟨1, plusResolventMultiplier_coordinate_bounded⟩) hIbound
    have haddx := congrArg (fun A : H →WOT[ℂ] H => A x) hadd
    rw [← ContinuousLinearMapWOT.add_apply, ← haddx]
    have hcongr : ∀ a : ℝ, (a : ℂ) * g a + Complex.I * g a = (1 : ℂ) := by
      intro a
      unfold g plusResolventMultiplier
      have hne : (a : ℂ) + Complex.I ≠ 0 := by
        intro h
        have hi := congrArg Complex.im h
        norm_num at hi
      field_simp [hne]
    have hfunit : Measurable (fun a : ℝ => (a : ℂ) * g a + Complex.I * g a) := by
      have heqfun :
          ((fun a : ℝ => (a : ℂ) * plusResolventMultiplier a) +
              (fun a : ℝ => Complex.I * plusResolventMultiplier a)) =
            (fun a : ℝ => (a : ℂ) * plusResolventMultiplier a +
              Complex.I * plusResolventMultiplier a) := by
        funext a
        rfl
      change Measurable (fun a : ℝ => (a : ℂ) * plusResolventMultiplier a +
        Complex.I * plusResolventMultiplier a)
      rw [← heqfun]
      exact plusResolventMultiplier_coordinate_measurable.add
        (measurable_const.mul plusResolventMultiplier_measurable)
    have hbunit : ∃ C : ℝ, ∀ a : ℝ,
        ‖(fun a : ℝ => (a : ℂ) * g a + Complex.I * g a) a‖ ≤ C := by
      rcases plusResolventMultiplier_bounded with ⟨C, hC⟩
      refine ⟨1 + C, fun a => ?_⟩
      exact (norm_add_le _ _).trans (add_le_add
        (by simpa [g] using plusResolventMultiplier_coordinate_bounded a)
        (by simpa [g, norm_mul] using hC a))
    have hunit :
        boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a + Complex.I * g a)
            hfunit hbunit =
          boundedIntegral μS (fun _ : ℝ => (1 : ℂ)) measurable_const
            ⟨1, fun _ => by simp⟩ := by
      apply boundedIntegral_congr
      exact fun a => hcongr a
    have hsumfun :
        (fun a : ℝ => (a : ℂ) * g a) + (fun a : ℝ => Complex.I * g a) =
          (fun a : ℝ => (a : ℂ) * g a + Complex.I * g a) := by
      funext a
      simp [Pi.add_apply]
    have hunitx := congrArg (fun A : H →WOT[ℂ] H => A x) hunit
    convert hunitx using 1 <;>
      simp only [hsumfun, boundedIntegral_const]
    simp [ContinuousLinearMapWOT.one_apply]
  let x' : (M + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse.domain :=
    ⟨x, by
      rw [LinearPMap.inverse_domain, maximalSpectralIntegral_plus_resolvent_range]
      exact Submodule.mem_top⟩
  have hxy : (M + Complex.I • (1 : H →ₗ.[ℂ] H)) y = x' := by
    simpa [x'] using hsum
  exact LinearPMap.inverse_apply_eq hker hxy

lemma maximalSpectralIntegral_minus_resolvent_inverse_apply (x : H) :
    (maximalSpectralIntegral μS - Complex.I • (1 : H →ₗ.[ℂ] H)).inverse
        ⟨x, by
          rw [LinearPMap.inverse_domain, maximalSpectralIntegral_minus_resolvent_range]
          exact Submodule.mem_top⟩ =
      boundedIntegral μS minusResolventMultiplier minusResolventMultiplier_measurable
        minusResolventMultiplier_bounded x := by
  let M := maximalSpectralIntegral μS
  let g := minusResolventMultiplier
  have hker : (M - Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.ker = ⊥ := by
    have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero
      (maximalSpectralIntegral_isSelfAdjoint_of_range_eq_top μS
        (maximalSpectralIntegral_plus_resolvent_range (μS := μS))
        (maximalSpectralIntegral_minus_resolvent_range (μS := μS)))
      (z := Complex.I) (by norm_num)
    exact hres.1
  have hy : boundedIntegral μS g minusResolventMultiplier_measurable
      minusResolventMultiplier_bounded x ∈
        spectralSquareMomentDomain μS :=
    boundedMultiplier_mem_spectralSquareMomentDomain (α := ℝ) μS
      minusResolventMultiplier_measurable minusResolventMultiplier_bounded
      minusResolventMultiplier_coordinate_bounded x
  let yM : M.domain := ⟨boundedIntegral μS g minusResolventMultiplier_measurable
    minusResolventMultiplier_bounded x, hy⟩
  let y : (M - Complex.I • (1 : H →ₗ.[ℂ] H)).domain :=
    ⟨(yM : H), Submodule.mem_inf.mpr ⟨hy, Submodule.mem_top⟩⟩
  have haction := maximalSpectralIntegral_apply_boundedMultiplier μS
    minusResolventMultiplier_measurable minusResolventMultiplier_bounded
    minusResolventMultiplier_coordinate_bounded
    minusResolventMultiplier_coordinate_measurable x
  have hIbound : ∃ C : ℝ, ∀ a : ℝ, ‖Complex.I * g a‖ ≤ C := by
    rcases minusResolventMultiplier_bounded with ⟨C, hC⟩
    refine ⟨C, fun a => ?_⟩
    simpa [norm_mul] using hC a
  have hsum : (M - Complex.I • (1 : H →ₗ.[ℂ] H)) y = x := by
    change M yM - Complex.I • (y : H) = x
    have hscaled : Complex.I • (y : H) =
        boundedIntegral μS (fun a : ℝ => Complex.I * g a)
          (measurable_const.mul minusResolventMultiplier_measurable) hIbound x := by
      have h := congrArg (fun A : H →WOT[ℂ] H => A x)
        (boundedIntegral_smul μS Complex.I minusResolventMultiplier_measurable
          minusResolventMultiplier_bounded)
      simpa [y, yM, Pi.mul_apply] using h.symm
    rw [haction, hscaled]
    have hadd := boundedIntegral_sub μS
      (f := fun a : ℝ => (a : ℂ) * g a)
      (g := fun a : ℝ => Complex.I * g a)
      minusResolventMultiplier_coordinate_measurable
      (measurable_const.mul minusResolventMultiplier_measurable)
      (⟨1, minusResolventMultiplier_coordinate_bounded⟩) hIbound
    have haddx := congrArg (fun A : H →WOT[ℂ] H => A x) hadd
    rw [← ContinuousLinearMapWOT.sub_apply, ← haddx]
    have hcongr : ∀ a : ℝ, (a : ℂ) * g a - Complex.I * g a = (1 : ℂ) := by
      intro a
      unfold g minusResolventMultiplier
      have hne : (a : ℂ) - Complex.I ≠ 0 := by
        intro h
        have hi := congrArg Complex.im h
        norm_num at hi
      field_simp [hne]
    have hfunit : Measurable (fun a : ℝ => (a : ℂ) * g a - Complex.I * g a) := by
      have heqfun :
          ((fun a : ℝ => (a : ℂ) * minusResolventMultiplier a) -
              (fun a : ℝ => Complex.I * minusResolventMultiplier a)) =
            (fun a : ℝ => (a : ℂ) * minusResolventMultiplier a -
              Complex.I * minusResolventMultiplier a) := by
        funext a
        rfl
      change Measurable (fun a : ℝ => (a : ℂ) * minusResolventMultiplier a -
        Complex.I * minusResolventMultiplier a)
      rw [← heqfun]
      exact minusResolventMultiplier_coordinate_measurable.sub
        (measurable_const.mul minusResolventMultiplier_measurable)
    have hbunit : ∃ C : ℝ, ∀ a : ℝ,
        ‖(fun a : ℝ => (a : ℂ) * g a - Complex.I * g a) a‖ ≤ C := by
      rcases minusResolventMultiplier_bounded with ⟨C, hC⟩
      refine ⟨1 + C, fun a => ?_⟩
      exact (norm_sub_le _ _).trans (add_le_add
        (by simpa [g] using minusResolventMultiplier_coordinate_bounded a)
        (by simpa [g, norm_mul] using hC a))
    have hunit :
        boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a - Complex.I * g a)
            hfunit hbunit =
          boundedIntegral μS (fun _ : ℝ => (1 : ℂ)) measurable_const
            ⟨1, fun _ => by simp⟩ := by
      apply boundedIntegral_congr
      exact fun a => hcongr a
    have hsubfun :
        (fun a : ℝ => (a : ℂ) * g a) - (fun a : ℝ => Complex.I * g a) =
          (fun a : ℝ => (a : ℂ) * g a - Complex.I * g a) := by
      funext a
      simp [Pi.sub_apply]
    have hunitx := congrArg (fun A : H →WOT[ℂ] H => A x) hunit
    convert hunitx using 1 <;>
      simp only [hsubfun, boundedIntegral_const]
    simp [ContinuousLinearMapWOT.one_apply]
  let x' : (M - Complex.I • (1 : H →ₗ.[ℂ] H)).inverse.domain :=
    ⟨x, by
      rw [LinearPMap.inverse_domain, maximalSpectralIntegral_minus_resolvent_range]
      exact Submodule.mem_top⟩
  have hxy : (M - Complex.I • (1 : H →ₗ.[ℂ] H)) y = x' := by
    simpa [x'] using hsum
  exact LinearPMap.inverse_apply_eq hker hxy

/-! ### The canonical self-adjoint realization

The preceding two range lemmas are the concrete Cayley-resolvent calculation.  They are worth
keeping separate from the abstract range criterion: this theorem is the point at which a real PVM
itself produces a self-adjoint (closed) unbounded operator, with no prior operator or domain datum.
-/

lemma maximalSpectralIntegral_isSelfAdjoint (μS : WOTSpectralMeasure ℝ H) :
    IsSelfAdjoint (maximalSpectralIntegral μS) := by
  apply maximalSpectralIntegral_isSelfAdjoint_of_range_eq_top μS
  · exact maximalSpectralIntegral_plus_resolvent_range (μS := μS)
  · exact maximalSpectralIntegral_minus_resolvent_range (μS := μS)

/-- The canonical maximal realization has a surjective shifted operator at every non-real
spectral parameter.  The preceding explicit `± Complex.I` calculations establish
self-adjointness; this general form then follows from the self-adjoint resolvent theorem. -/
lemma maximalSpectralIntegral_sub_smul_surjective
    (μS : WOTSpectralMeasure ℝ H) {z : ℂ} (hz : z.im ≠ 0) :
    Function.Surjective
      (maximalSpectralIntegral μS - z • (1 : H →ₗ.[ℂ] H)).toFun :=
  LinearPMap.IsSelfAdjoint.sub_smul_surjective
    (maximalSpectralIntegral_isSelfAdjoint μS) hz

/-- Every non-real point belongs to the resolvent set of the canonical maximal spectral
integral.  This is the public `resolventSet` form of the preceding range theorem and the
self-adjoint resolvent criterion; downstream users can therefore use the ordinary resolvent API
without unpacking the Cayley shifts or the spectral multiplier construction. -/
lemma maximalSpectralIntegral_mem_resolventSet
    (μS : WOTSpectralMeasure ℝ H) {z : ℂ} (hz : z.im ≠ 0) :
    z ∈ LinearPMap.resolventSet (maximalSpectralIntegral μS) :=
  LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero
    (maximalSpectralIntegral_isSelfAdjoint μS) hz

/-- Resolvent notation for the canonical spectral integral is exactly the bounded spectral
multiplier `λ ↦ (λ - z)⁻¹`.  The subtype in the left-hand side is the canonical full-domain
element supplied by the resolvent theorem. -/
lemma maximalSpectralIntegral_resolvent_apply {z : ℂ} (hz : z.im ≠ 0) (x : H) :
    LinearPMap.resolvent (maximalSpectralIntegral μS) z
        ⟨x, by
          rw [LinearPMap.inverse_domain, maximalSpectralIntegral_resolvent_range hz]
          exact Submodule.mem_top⟩ =
      boundedIntegral μS (resolventMultiplier z) (resolventMultiplier_measurable z)
        (resolventMultiplier_bounded hz) x :=
  maximalSpectralIntegral_resolvent_inverse_apply hz x

lemma maximalSpectralIntegral_closure_eq_self_adjoint (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).closure = maximalSpectralIntegral μS := by
  exact (maximalSpectralIntegral_isSelfAdjoint μS).isClosed.closure_eq

lemma maximalSpectralIntegral_isEssentiallySelfAdjoint (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).IsEssentiallySelfAdjoint := by
  rw [maximalSpectralIntegral_isEssentiallySelfAdjoint_iff]
  rw [maximalSpectralIntegral_closure_eq_self_adjoint μS]
  exact maximalSpectralIntegral_isSelfAdjoint μS

lemma measurableSpectralIntegral_isSelfAdjoint
    (μS : WOTSpectralMeasure ℝ H) (f : ℝ → ℝ) (hf : Measurable f) :
    _root_.IsSelfAdjoint (measurableSpectralIntegral μS f hf) := by
  exact maximalSpectralIntegral_isSelfAdjoint (μS.map f hf)

lemma measurableSpectralIntegral_closure_eq_self
    (μS : WOTSpectralMeasure ℝ H) (f : ℝ → ℝ) (hf : Measurable f) :
    (measurableSpectralIntegral μS f hf).closure =
      measurableSpectralIntegral μS f hf := by
  exact (measurableSpectralIntegral_isSelfAdjoint μS f hf).isClosed.closure_eq

lemma measurableSpectralIntegral_isEssentiallySelfAdjoint
    (μS : WOTSpectralMeasure ℝ H) (f : ℝ → ℝ) (hf : Measurable f) :
    (measurableSpectralIntegral μS f hf).IsEssentiallySelfAdjoint := by
  exact maximalSpectralIntegral_isEssentiallySelfAdjoint (μS.map f hf)

lemma measurableSpectralIntegral_norm_sq
    (μS : WOTSpectralMeasure ℝ H) (f : ℝ → ℝ) (hf : Measurable f)
    (x : H) (hx : x ∈ (measurableSpectralIntegral μS f hf).domain) :
    ENNReal.ofReal
        (‖(measurableSpectralIntegral μS f hf) ⟨x, hx⟩‖ ^ 2) =
      ∫⁻ r, ENNReal.ofReal ((f r) ^ 2) ∂μS.diagonalMeasure x := by
  have h := maximalSpectralIntegral_norm_sq (μS.map f hf) x hx
  rw [μS.diagonalMeasure_map f hf] at h
  calc
    ENNReal.ofReal
        (‖(measurableSpectralIntegral μS f hf) ⟨x, hx⟩‖ ^ 2) =
        ∫⁻ r, ENNReal.ofReal (r ^ 2) ∂Measure.map f (μS.diagonalMeasure x) := h
    _ = ∫⁻ r, ENNReal.ofReal ((f r) ^ 2) ∂μS.diagonalMeasure x := by
      simpa [Function.comp_def] using
        (lintegral_map (μ := μS.diagonalMeasure x)
          (ENNReal.continuous_ofReal.measurable.comp (measurable_id.pow_const 2)) hf)

lemma measurableSpectralIntegral_norm_sq_eq_integral
    (μS : WOTSpectralMeasure ℝ H) (f : ℝ → ℝ) (hf : Measurable f)
    (x : H) (hx : x ∈ (measurableSpectralIntegral μS f hf).domain) :
    ‖(measurableSpectralIntegral μS f hf) ⟨x, hx⟩‖ ^ 2 =
      ∫ r, f r ^ 2 ∂μS.diagonalMeasure x := by
  have hfi : Integrable (fun r : ℝ => f r ^ 2) (μS.diagonalMeasure x) := by
    exact (mem_measurableSpectralIntegral_domain_iff μS f hf x).mp hx
  have hpos : 0 ≤ᵐ[μS.diagonalMeasure x] (fun r : ℝ => f r ^ 2) :=
    Filter.Eventually.of_forall (fun r => sq_nonneg (f r))
  have hconvert : ENNReal.ofReal (∫ r, f r ^ 2 ∂μS.diagonalMeasure x) =
      ∫⁻ r, ENNReal.ofReal (f r ^ 2) ∂μS.diagonalMeasure x :=
    ofReal_integral_eq_lintegral_ofReal hfi hpos
  have hmain := measurableSpectralIntegral_norm_sq μS f hf x hx
  rw [← hconvert] at hmain
  exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _)
    (integral_nonneg (fun r => sq_nonneg (f r)))).mp hmain

/-! ### Uniqueness of the domain-aware realization

The next theorem is the reusable endpoint of the PVM layer.  It says that a self-adjoint partial
operator whose matrix elements are reconstructed by a real PVM is necessarily the canonical
square-moment realization of that PVM.  The proof is deliberately here, rather than in a Cayley
adapter: Cayley, multiplication operators, and later concrete models can all use the same
domain-identification theorem.
-/

theorem maximalSpectralIntegral_eq_of_isSelfAdjoint_of_isWeakSpectralResolution
    (T : H →ₗ.[ℂ] H) (hT : _root_.IsSelfAdjoint T)
    (hres : IsWeakSpectralResolution T μS)
    (hdom : ∀ x : T.domain,
      (x : H) ∈ spectralSquareMomentDomain μS) :
    maximalSpectralIntegral μS = T := by
  let M := maximalSpectralIntegral μS
  have hle : T ≤ M := by
    refine ⟨?_, ?_⟩
    · intro x hx
      exact hdom ⟨x, hx⟩
    · intro x z hxz
      have hxM : (x : H) ∈ M.domain := by
        change (x : H) ∈ spectralSquareMomentDomain μS
        exact hdom x
      let z₀ : M.domain := ⟨(x : H), hxM⟩
      have hz : z = z₀ := by
        apply Subtype.ext
        exact hxz.symm
      apply ext_inner_left ℂ
      intro y
      have hfi : (μS.scalarMeasure (x : H) y).Integrable id := (hres ⟨x, x.property⟩).1 y
      let := scalarMeasure_isFiniteVariation μS (x : H) y
      have hweak := truncationIntegral_inner_tendsto_weakIntegral μS (x : H) y hfi
      have hcomplex : Filter.Tendsto
          (fun n : ℕ => ∫ᵛ r, truncationFunction n r ∂[
            ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); μS.scalarMeasure (x : H) y])
          Filter.atTop (𝓝 (μS.weakIntegral id (x : H) y)) := by
        apply hweak.congr'
        filter_upwards [] with n
        have htrunc : (μS.scalarMeasure (x : H) y).Integrable (realTruncationFunction n) := by
          rcases realTruncationFunction_bounded n with ⟨C, hC⟩
          apply Integrable.of_bound (realTruncationFunction_measurable n).aestronglyMeasurable C
          filter_upwards [] with r
          simpa [Real.norm_eq_abs] using hC r
        have hreal := integral_real_eq_complex (μS.scalarMeasure (x : H) y) htrunc
        have hfun : (fun r => truncationFunction n r) =
            (fun r => Complex.ofRealCLM (realTruncationFunction n r)) := by
          funext r
          simpa [Complex.ofRealCLM_apply] using congrFun
            (realTruncationFunction_complex_eq n).symm r
        calc
          ∫ᵛ r, realTruncationFunction n r ∂[
              ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); μS.scalarMeasure (x : H) y] =
              ∫ᵛ r, Complex.ofRealCLM (realTruncationFunction n r) ∂[
                ContinuousLinearMap.lsmul ℝ ℂ; μS.scalarMeasure (x : H) y] := hreal
          _ = ∫ᵛ r, truncationFunction n r ∂[
              ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); μS.scalarMeasure (x : H) y] :=
            congrArg (fun f : ℝ → ℂ => ∫ᵛ r, f r ∂[
              ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); μS.scalarMeasure (x : H) y]) hfun.symm
      have hmax := maximalSpectralIntegral_weak_truncation_reconstruction μS (x : H) hxM y
      have hinner : ⟪y, M z₀⟫_ℂ = μS.weakIntegral id (x : H) y :=
        tendsto_nhds_unique hmax hcomplex
      calc
        ⟪y, T x⟫_ℂ = μS.weakIntegral id (x : H) y := (hres ⟨x, x.property⟩).2 y
        _ = ⟪y, M z₀⟫_ℂ := hinner.symm
        _ = ⟪y, M z⟫_ℂ := by rw [hz]
  have hmax := maximalSpectralIntegral_isSelfAdjoint μS
  have hTesa : T.IsEssentiallySelfAdjoint :=
    _root_.LinearPMap.IsSelfAdjoint.isEssentiallySelfAdjoint hT
  have hclosure := LinearPMap.IsEssentiallySelfAdjoint.unique_self_adjoint_extension
    hTesa hle hmax
  rw [hT.isClosed.closure_eq] at hclosure
  exact hclosure

/-- Package the reusable PVM realization theorem together with its exact domain statement.

The only model-specific input is the inclusion of the model domain into the square-moment domain;
the reverse inclusion is forced by self-adjoint uniqueness after the canonical maximal realization
has been constructed. -/
theorem domainAwareSelfAdjointSpectralTheorem_of_isWeakSpectralResolution
    (T : H →ₗ.[ℂ] H) (hT : _root_.IsSelfAdjoint T)
    (hres : IsWeakSpectralResolution T μS)
    (hdom : ∀ x : T.domain,
      (x : H) ∈ spectralSquareMomentDomain μS) :
    DomainAwareSelfAdjointSpectralTheorem T μS := by
  have heq := maximalSpectralIntegral_eq_of_isSelfAdjoint_of_isWeakSpectralResolution
    T hT hres hdom
  refine
    { toSelfAdjointSpectralTheorem :=
        { isSelfAdjoint := hT
          reconstruction := hres }
      domain_eq_squareMoment := ?_ }
  have hdomains : (T.domain : Set H) =
      ((maximalSpectralIntegral μS).domain : Set H) :=
    congrArg (fun D : Submodule ℂ H => (D : Set H))
      (congrArg LinearPMap.domain heq).symm
  calc
    (T.domain : Set H) = (maximalSpectralIntegral μS).domain := hdomains
    _ = spectralSquareMomentDomain μS := by
      exact congrArg (fun D : Submodule ℂ H => (D : Set H))
        (maximalSpectralIntegral_domain μS)

end QuantumMechanics.WOTSpectralMeasure

namespace QuantumMechanics

namespace DomainAwareSelfAdjointSpectralTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →ₗ.[ℂ] H}
variable {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}

/-! ### The canonical operator equality

The domain-aware certificate contains exactly the extra hypothesis needed by the uniqueness
theorem: its operator domain is the square-moment domain of its PVM.  Exposing this equality as a
method keeps later Cayley and representation proofs from reconstructing the same argument. -/

theorem maximal_eq (D : DomainAwareSelfAdjointSpectralTheorem T μS) :
    maximalSpectralIntegral μS = T := by
  exact maximalSpectralIntegral_eq_of_isSelfAdjoint_of_isWeakSpectralResolution
    T D.isSelfAdjoint D.reconstruction_of
    (fun z => D.mem_domain_iff z |>.mp z.property)

end DomainAwareSelfAdjointSpectralTheorem

namespace SelfAdjointSpectralTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →ₗ.[ℂ] H}
variable {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}

/- The weak reconstruction certificate becomes an actual operator equality as soon as the model
supplies the one missing domain inclusion.  This is the thin, non-domain-aware entry point used
by Cayley and model-specific closures. -/
theorem maximal_eq_of_domain_inclusion
    (D : SelfAdjointSpectralTheorem T μS)
    (hdom : ∀ x : T.domain,
      (x : H) ∈ spectralSquareMomentDomain μS) :
    maximalSpectralIntegral μS = T := by
  exact maximalSpectralIntegral_eq_of_isSelfAdjoint_of_isWeakSpectralResolution
    T D.isSelfAdjoint D.reconstruction hdom

end SelfAdjointSpectralTheorem

end QuantumMechanics
