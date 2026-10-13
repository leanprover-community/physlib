/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube
public import PhyslibAlpha.CondensedMatter.TightBindingChain.Saturation
public import PhyslibAlpha.CondensedMatter.TightBindingChain.SpeedLimit
/-!

# The velocity band of forced uncertainty

## i. Overview

A unit vector has minimum uncertainty when the energy–position uncertainty relation is an
equality, that is when the centered Gram defect of `H` and `X` vanishes. These vectors form a
compact set, so among them some moves fastest: the threshold `v*` is attained. Every vector
moving faster, with `v* < |⟨J⟩| ≤ maxCurrent`, carries a positive defect. This is the velocity
band `Ϙ = (v*, maxCurrent]`. For `N = 2, 3` the maximal current state has minimum uncertainty,
so the band is empty.

On the cube the band forces the defect axis by axis, for every state and not only for products:
a state of the cube with minimum uncertainty along `x` has minimum uncertainty slice by slice, and
its speed along `x` is an average of the speeds of the slices, all at most `v*`. So a speed along
`x` in the band of `Tx` forces a positive defect along `x`, and likewise along `y` and `z`.

## ii. Key results

- `defectOf` : the centered Gram defect of `H` and `X` in a vector.
- `minUncertainty` : the unit vectors of minimum uncertainty, a compact set.
- `threshold` : the largest speed `|⟨J⟩|` of a vector of minimum uncertainty, attained by
  `exists_threshold`.
- `velocityBand` : the band `Ϙ = (threshold, maxCurrent]`.
- `defectOf_pos_of_mem_velocityBand` : in the band, the defect is forced.
- `velocityBand_eq_empty` : for `N = 2, 3` the band is empty.
- `centeredGramDefect_alongX_pos` (and `Y`, `Z`) : on the cube, a speed in the band of an axis
  forces the defect of that axis, for every state.
- `nava_robertson_schrodinger_cube_of_mem_velocityBand` : speeds in the three bands force the
  defects of the three axes.

## iii. Table of contents

- A. Uncertainty in a vector
- B. The threshold
- C. The band
- D. The band on the cube

## iv. References

* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]
-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open scoped ComplexOrder selfAdjoint
open ProbabilisticTheory
open InnerProductSpace UnitalPositiveLinearMap QuantumMechanics.FiniteHilbertSpace
variable (T : TightBindingChain)

/-!

## A. Uncertainty in a vector

-/

/-- The mean `re ⟨ψ|A|ψ⟩` of an operator in a vector. -/
noncomputable def meanOf (A : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace) (ψ : T.HilbertSpace) : ℝ :=
  (⟪ψ, A ψ⟫_ℂ).re

/-- The fluctuation `A ψ - ⟨A⟩ ψ` of an operator in a vector. -/
noncomputable def flucOf (A : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace) (ψ : T.HilbertSpace) :
    T.HilbertSpace :=
  A ψ - T.meanOf A ψ • ψ

/-- The centered Gram defect `‖u‖² ‖w‖² - |⟪u, w⟫|²` of `H` and `X` in a vector. -/
noncomputable def defectOf (ψ : T.HilbertSpace) : ℝ :=
  ‖T.flucOf T.openHamiltonian ψ‖ ^ 2 * ‖T.flucOf T.position ψ‖ ^ 2 -
    ‖⟪T.flucOf T.openHamiltonian ψ, T.flucOf T.position ψ⟫_ℂ‖ ^ 2

lemma continuous_meanOf (A : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace) : Continuous (T.meanOf A) :=
  Complex.continuous_re.comp (continuous_id.inner A.continuous_of_finiteDimensional)

lemma continuous_defectOf : Continuous T.defectOf := by
  have hf (A : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace) : Continuous (T.flucOf A) :=
    A.continuous_of_finiteDimensional.sub ((T.continuous_meanOf A).smul continuous_id)
  unfold defectOf
  fun_prop

lemma defectOf_nonneg (ψ : T.HilbertSpace) : 0 ≤ T.defectOf ψ := by
  rw [defectOf, sub_nonneg, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2

/-- In a unit vector, the mean is the expectation of the vector state. -/
lemma expectation_ofVec {ψ : T.HilbertSpace} (h : ‖ψ‖ = 1)
    (A : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace) (hA : A.IsSymmetric) :
    (ofVec h)⟨T.toObservable A hA⟩ = T.meanOf A ψ := by
  rw [meanOf, ← Complex.ofReal_re ((ofVec h)⟨_⟩), ← apply_observable_eq_expectation, ofVec_apply]
  rfl

/-- In a unit vector, `defectOf` is the centered Gram defect of the vector state. -/
lemma centeredGramDefect_ofVec_eq {ψ : T.HilbertSpace} (h : ‖ψ‖ = 1) :
    centeredGramDefect (ofVec h) T.openHamiltonianObservable T.positionObservable =
      T.defectOf ψ := by
  rw [centeredGramDefect_ofVec,
    show (ofVec h)⟨T.openHamiltonianObservable⟩ = T.meanOf T.openHamiltonian ψ from
      T.expectation_ofVec h _ _,
    show (ofVec h)⟨T.positionObservable⟩ = T.meanOf T.position ψ from T.expectation_ofVec h _ _]
  rfl

/-!

## B. The threshold

-/

/-- The unit vectors of minimum uncertainty. -/
def minUncertainty : Set T.HilbertSpace := Metric.sphere 0 1 ∩ T.defectOf ⁻¹' {0}

lemma isCompact_minUncertainty : IsCompact T.minUncertainty :=
  haveI := FiniteDimensional.proper ℂ T.HilbertSpace
  (isCompact_sphere 0 1).inter_right (isClosed_singleton.preimage T.continuous_defectOf)

/-- A localized electron has minimum uncertainty: its position is sharp. -/
lemma localizedState_mem_minUncertainty (n : Fin T.N) : (|n⟩ : T.HilbertSpace) ∈
    T.minUncertainty := by
  have hX : T.flucOf T.position |n⟩ = 0 := by
    rw [flucOf, meanOf, position_apply_localizedState, inner_smul_right,
      T.localizedState_orthonormal_eq_ite, ite_eq_left rfl, mul_one, Complex.ofReal_re,
      ← Complex.coe_smul, sub_self]
  refine ⟨by simp [(localizedState (T := T)).orthonormal.1 n], ?_⟩
  simp [defectOf, hX]

/-- The largest speed `|⟨J⟩|` of a vector of minimum uncertainty. -/
noncomputable def threshold : ℝ := sSup ((fun ψ => |T.meanOf T.current ψ|) '' T.minUncertainty)

/-- The threshold is attained by a vector of minimum uncertainty. -/
lemma exists_threshold :
    ∃ ψ ∈ T.minUncertainty, |T.meanOf T.current ψ| = T.threshold := by
  have hK := T.isCompact_minUncertainty.image (continuous_abs.comp (T.continuous_meanOf T.current))
  exact hK.sSup_mem ((Set.nonempty_of_mem (T.localizedState_mem_minUncertainty 0)).image _)

lemma le_threshold {ψ : T.HilbertSpace} (hψ : ψ ∈ T.minUncertainty) :
    |T.meanOf T.current ψ| ≤ T.threshold :=
  le_csSup ((T.isCompact_minUncertainty.image (continuous_abs.comp
    (T.continuous_meanOf T.current))).bddAbove) (Set.mem_image_of_mem _ hψ)

lemma threshold_le_maxCurrent (ht : T.t ≠ 0) : T.threshold ≤ T.maxCurrent := by
  obtain ⟨ψ, ⟨hψ, -⟩, h⟩ := T.exists_threshold
  have := T.abs_re_inner_current_le ht ψ
  rw [mem_sphere_zero_iff_norm.mp hψ, one_pow, mul_one] at this
  exact h ▸ this

/-!

## C. The band

-/

/-- The velocity band `Ϙ = (threshold, maxCurrent]` of forced uncertainty. -/
def velocityBand : Set ℝ := Set.Ioc T.threshold T.maxCurrent

/-- In the velocity band, the uncertainty defect is forced. -/
lemma defectOf_pos_of_mem_velocityBand {ψ : T.HilbertSpace} (hψ : ‖ψ‖ = 1)
    (hv : |T.meanOf T.current ψ| ∈ T.velocityBand) : 0 < T.defectOf ψ :=
  (T.defectOf_nonneg ψ).lt_of_ne fun h =>
    (hv.1.trans_le (T.le_threshold ⟨mem_sphere_zero_iff_norm.mpr hψ, h.symm⟩)).false

/-- For `N = 2, 3` the maximal current state has minimum uncertainty: the band is empty. -/
lemma velocityBand_eq_empty (ht : T.t ≠ 0) (hN : T.N = 2 ∨ T.N = 3) :
    T.velocityBand = ∅ := by
  have hmin : T.maxCurrentState ∈ T.minUncertainty := ⟨mem_sphere_zero_iff_norm.mpr
    T.norm_maxCurrentState, by
      rw [Set.mem_preimage, ← T.centeredGramDefect_ofVec_eq T.norm_maxCurrentState]
      exact (T.centeredGramDefect_maxCurrentState_eq_zero_iff ht (by omega)).mpr hN⟩
  have h := T.le_threshold hmin
  rw [← T.expectation_ofVec T.norm_maxCurrentState _ T.current_hermitian,
    T.abs_expectation_current_maxCurrentState] at h
  exact Set.Ioc_eq_empty (not_lt.mpr h)

/-!

## D. The band on the cube

-/

/-- A vector of minimum uncertainty moves no faster than the threshold. -/
lemma abs_expectation_current_le_threshold {ψ : T.HilbertSpace} (hψ : ‖ψ‖ = 1)
    (h : centeredGramDefect (ofVec hψ) T.openHamiltonianObservable T.positionObservable = 0) :
    |(ofVec hψ)⟨T.currentObservable⟩| ≤ T.threshold := by
  rw [T.expectation_ofVec hψ _ T.current_hermitian]
  exact T.le_threshold ⟨mem_sphere_zero_iff_norm.mpr hψ, by
    rw [Set.mem_preimage, ← T.centeredGramDefect_ofVec_eq hψ, h, Set.mem_singleton_iff]⟩

variable (Tx Ty Tz : TightBindingChain) {Ψ : Tx.CubeHilbertSpace Ty Tz} (hΨ : ‖Ψ‖ = 1)

/-- **Forced uncertainty along `x`.** Every state of the cube whose speed along `x` lies in the
band of `Tx` carries a positive uncertainty defect along `x`, product state or not. -/
lemma centeredGramDefect_alongX_pos
    (hv : |(ofVec hΨ)⟨Tx.alongX Ty Tz Tx.currentObservable⟩| ∈ Tx.velocityBand) :
    0 < centeredGramDefect (ofVec hΨ) (Tx.alongX Ty Tz Tx.openHamiltonianObservable)
      (Tx.alongX Ty Tz Tx.positionObservable) :=
  (centeredGramDefect_nonneg _ _ _).lt_of_ne fun h => (hv.1.trans_le
    (abs_expectation_onFstObservable_le (fun _ hu => Tx.abs_expectation_current_le_threshold hu)
      hΨ h.symm)).false

/-- **Forced uncertainty along `y`.** Every state of the cube whose speed along `y` lies in the
band of `Ty` carries a positive uncertainty defect along `y`. -/
lemma centeredGramDefect_alongY_pos
    (hv : |(ofVec hΨ)⟨Tx.alongY Ty Tz Ty.currentObservable⟩| ∈ Ty.velocityBand) :
    0 < centeredGramDefect (ofVec hΨ) (Tx.alongY Ty Tz Ty.openHamiltonianObservable)
      (Tx.alongY Ty Tz Ty.positionObservable) :=
  (centeredGramDefect_nonneg _ _ _).lt_of_ne fun h => (hv.1.trans_le
    (abs_expectation_onSndObservable_le (fun _ hu h' => abs_expectation_onFstObservable_le
      (fun _ hu' => Ty.abs_expectation_current_le_threshold hu') hu h') hΨ h.symm)).false

/-- **Forced uncertainty along `z`.** Every state of the cube whose speed along `z` lies in the
band of `Tz` carries a positive uncertainty defect along `z`. -/
lemma centeredGramDefect_alongZ_pos
    (hv : |(ofVec hΨ)⟨Tx.alongZ Ty Tz Tz.currentObservable⟩| ∈ Tz.velocityBand) :
    0 < centeredGramDefect (ofVec hΨ) (Tx.alongZ Ty Tz Tz.openHamiltonianObservable)
      (Tx.alongZ Ty Tz Tz.positionObservable) :=
  (centeredGramDefect_nonneg _ _ _).lt_of_ne fun h => (hv.1.trans_le
    (abs_expectation_onSndObservable_le (fun _ hu h' => abs_expectation_onSndObservable_le
      (fun _ hu' => Tz.abs_expectation_current_le_threshold hu') hu h') hΨ h.symm)).false

/-- **Nava–Robertson–Schrödinger on the cube, in the band.** Every state of the cube whose speeds
along `x`, `y`, `z` lie in the bands of `Tx`, `Ty`, `Tz` carries a positive uncertainty defect on
the three axes at once. -/
lemma nava_robertson_schrodinger_cube_of_mem_velocityBand
    (hx : |(ofVec hΨ)⟨Tx.alongX Ty Tz Tx.currentObservable⟩| ∈ Tx.velocityBand)
    (hy : |(ofVec hΨ)⟨Tx.alongY Ty Tz Ty.currentObservable⟩| ∈ Ty.velocityBand)
    (hz : |(ofVec hΨ)⟨Tx.alongZ Ty Tz Tz.currentObservable⟩| ∈ Tz.velocityBand) :
    0 < centeredGramDefect (ofVec hΨ) (Tx.alongX Ty Tz Tx.openHamiltonianObservable)
        (Tx.alongX Ty Tz Tx.positionObservable) ∧
      0 < centeredGramDefect (ofVec hΨ) (Tx.alongY Ty Tz Ty.openHamiltonianObservable)
        (Tx.alongY Ty Tz Ty.positionObservable) ∧
      0 < centeredGramDefect (ofVec hΨ) (Tx.alongZ Ty Tz Tz.openHamiltonianObservable)
        (Tx.alongZ Ty Tz Tz.positionObservable) :=
  ⟨Tx.centeredGramDefect_alongX_pos Ty Tz hΨ hx, Tx.centeredGramDefect_alongY_pos Ty Tz hΨ hy,
    Tx.centeredGramDefect_alongZ_pos Ty Tz hΨ hz⟩

end TightBindingChain
end CondensedMatter
