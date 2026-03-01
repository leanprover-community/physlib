/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
import PhysLean.Mathematics.Calculus.Divergence
/-!

# Test functions

Definition of test function, smooth and compactly supported function, and theorems about them.
-/
open Module
section IsTestFunction
variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {U} [NormedAddCommGroup U] [NormedSpace ℝ U]
  {V} [NormedAddCommGroup V] [NormedSpace ℝ V] -- [InnerProductSpace' ℝ V]

open ContDiff InnerProductSpace MeasureTheory
/-- A test function is a smooth function with compact support. -/
@[fun_prop]
structure IsTestFunction (f : X → U) where
  smooth : ContDiff ℝ ∞ f
  supp : HasCompactSupport f

/-- A compactly supported continuous map from a test function. -/
def IsTestFunction.toCompactlySupportedContinuousMap {f : X → U}
    (hf : IsTestFunction f) : CompactlySupportedContinuousMap X U where
  toFun := f
  hasCompactSupport' := hf.supp
  continuous_toFun := hf.smooth.continuous

lemma IsTestFunction.of_compactlySupportedContinuousMap {f : CompactlySupportedContinuousMap X U}
    (hf : ContDiff ℝ ∞ f) :
    IsTestFunction f.toFun where
  smooth := hf
  supp := f.hasCompactSupport'

@[fun_prop]
lemma IsTestFunction.integrable [MeasurableSpace X] [OpensMeasurableSpace X]
    {f : X → U} (hf : IsTestFunction f)
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] :
    MeasureTheory.Integrable f μ :=
  Continuous.integrable_of_hasCompactSupport (continuous hf.smooth) hf.supp

@[fun_prop]
lemma IsTestFunction.differentiable {f : X → U} (hf : IsTestFunction f) :
    Differentiable ℝ f := hf.1.differentiable (by simp)

@[fun_prop]
lemma IsTestFunction.contDiff {f : X → U} (hf : IsTestFunction f) :
    ContDiff ℝ ∞ f := hf.1

@[fun_prop]
lemma IsTestFunction.zero :
    IsTestFunction (fun _ : X => (0 : U)) where
  smooth := by fun_prop
  supp := HasCompactSupport.zero

@[fun_prop]
lemma IsTestFunction.comp_left {f : X → V} (hf : IsTestFunction f)
    {g : V → U} (hg1 : g 0 = 0) (hg : ContDiff ℝ ∞ g) :
    IsTestFunction (fun x => g (f x)) where
  smooth := ContDiff.comp hg hf.smooth
  supp := by
    obtain ⟨K, cK, hK⟩ := exists_compact_iff_hasCompactSupport.mpr hf.supp
    refine exists_compact_iff_hasCompactSupport.mp ⟨K, cK, fun x hx => ?_⟩
    rw [hK x hx]
    exact hg1

@[fun_prop]
lemma IsTestFunction.pi {ι} [Fintype ι] {φ : X → ι → U} (hφ : ∀ i, IsTestFunction (φ · i)) :
    IsTestFunction (fun x i => φ x i) where
  smooth := contDiff_pi' (fun i => (hφ i).smooth)
  supp := by
    let K : ι → Set X := fun i =>
      Classical.choose (exists_compact_iff_hasCompactSupport.mpr (hφ i).supp)
    have hK (i : ι) := Classical.choose_spec (exists_compact_iff_hasCompactSupport.mpr (hφ i).supp)
    refine exists_compact_iff_hasCompactSupport.mp
      ⟨⋃ i, K i, isCompact_iUnion (fun i => (hK i).1), fun x hx => ?_⟩
    simp at hx
    conv_lhs =>
      enter [i]
      rw [(hK i).2 x (hx i)]
    rfl

lemma IsTestFunction.space_component {φ : X → Space d} (hφ : IsTestFunction φ) :
    IsTestFunction (fun x => φ x i) where
  smooth := by
    have hφ := hφ.smooth
    fun_prop
  supp := by
    obtain ⟨K, cK, hK⟩ := exists_compact_iff_hasCompactSupport.mpr hφ.supp
    refine exists_compact_iff_hasCompactSupport.mp ⟨K, cK, fun x hx => ?_⟩
    rw [hK x hx]
    simp

@[fun_prop]
lemma IsTestFunction.prodMk {f : X → U} {g : X → V}
    (hf : IsTestFunction f) (hg : IsTestFunction g) :
    IsTestFunction (fun x => (f x, g x)) where
  smooth := by fun_prop
  supp := by
    obtain ⟨Kf, cKf, hKf⟩ := exists_compact_iff_hasCompactSupport.mpr hf.supp
    obtain ⟨Kg, cKg, hKg⟩ := exists_compact_iff_hasCompactSupport.mpr hg.supp
    refine exists_compact_iff_hasCompactSupport.mp
      ⟨Kf ∪ Kg, IsCompact.union cKf cKg, fun x hx => ?_⟩
    simp at hx
    simp [hKf x hx.1, hKg x hx.2]

@[fun_prop]
lemma IsTestFunction.prod_fst {f : X → U × V} (hf : IsTestFunction f) :
    IsTestFunction (fun x => (f x).1) := by fun_prop (disch:=simp)

@[fun_prop]
lemma IsTestFunction.prod_snd {f : X → U × V} (hf : IsTestFunction f) :
    IsTestFunction (fun x => (f x).2) := by fun_prop (disch:=simp)

@[fun_prop]
lemma IsTestFunction.neg {f : X → U} (hf : IsTestFunction f) :
    IsTestFunction (fun x => - f x) := by fun_prop (disch:=simp)

@[fun_prop]
lemma IsTestFunction.add {f g : X → U} (hf : IsTestFunction f) (hg : IsTestFunction g) :
    IsTestFunction (fun x => f x + g x) := by fun_prop (disch:=simp)

@[fun_prop]
lemma IsTestFunction.sub {f g : X → U} (hf : IsTestFunction f) (hg : IsTestFunction g) :
    IsTestFunction (fun x => f x - g x) := by fun_prop (disch:=simp)

@[fun_prop]
lemma IsTestFunction.mul {f g : X → ℝ} (hf : IsTestFunction f) (hg : IsTestFunction g) :
    IsTestFunction (fun x => f x * g x) := by fun_prop (disch:=simp)

@[fun_prop]
lemma IsTestFunction.mul_left {f g : X → ℝ} (hf : ContDiff ℝ ∞ f) (hg : IsTestFunction g) :
    IsTestFunction (fun x => f x * g x) where
  smooth := ContDiff.mul hf hg.smooth
  supp := HasCompactSupport.mul_left hg.supp

@[fun_prop]
lemma IsTestFunction.mul_right {f g : X → ℝ} (hf : IsTestFunction f) (hg : ContDiff ℝ ∞ g) :
    IsTestFunction (fun x => f x * g x) where
  smooth := ContDiff.mul hf.smooth hg
  supp := HasCompactSupport.mul_right hf.supp

@[fun_prop]
lemma IsTestFunction.inner [InnerProductSpace' ℝ V]
    {f g : X → V} (hf : IsTestFunction f) (hg : IsTestFunction g) :
    IsTestFunction (fun x => ⟪f x, g x⟫_ℝ) := by fun_prop (disch:=simp)

@[fun_prop]
lemma IsTestFunction.inner_left [InnerProductSpace' ℝ V]
    {f : X → V} {g : X → V} (hf : ContDiff ℝ ∞ f) (hg : IsTestFunction g) :
    IsTestFunction (fun x => ⟪f x, g x⟫_ℝ) where
  smooth := ContDiff.inner' hf hg.smooth
  supp := by
    obtain ⟨K, cK, hK⟩ := exists_compact_iff_hasCompactSupport.mpr hg.supp
    exact exists_compact_iff_hasCompactSupport.mp ⟨K, cK, fun x hx => by simp [hK x hx]⟩
    -- HasCompactSupport.inner_left hf hg.supp

@[fun_prop]
lemma IsTestFunction.inner_right [InnerProductSpace' ℝ V]
    {f : X → V} {g : X → V} (hf : IsTestFunction f) (hg : ContDiff ℝ ∞ g) :
    IsTestFunction (fun x => ⟪f x, g x⟫_ℝ) where
  smooth := ContDiff.inner' hf.smooth hg
  supp := by
    obtain ⟨K, cK, hK⟩ := exists_compact_iff_hasCompactSupport.mpr hf.supp
    exact exists_compact_iff_hasCompactSupport.mp ⟨K, cK, fun x hx => by simp [hK x hx]⟩
    -- HasCompactSupport.inner_right hf.supp hg

@[fun_prop]
lemma IsTestFunction.smul {f : X → ℝ} {g : X → U} (hf : IsTestFunction f) (hg : IsTestFunction g) :
    IsTestFunction (fun x => f x • g x) := by fun_prop (disch:=simp)

@[fun_prop]
lemma IsTestFunction.smul_left {f : X → ℝ} {g : X → U}
    (hf : ContDiff ℝ ∞ f) (hg : IsTestFunction g) : IsTestFunction (fun x => f x • g x) where
  smooth := ContDiff.smul hf hg.smooth
  supp := HasCompactSupport.smul_left hg.supp

@[fun_prop]
lemma IsTestFunction.smul_right {f : X → ℝ} {g : X → U}
    (hf : IsTestFunction f) (hg : ContDiff ℝ ∞ g) : IsTestFunction (fun x => f x • g x) where
  smooth := ContDiff.smul hf.smooth hg
  supp := HasCompactSupport.smul_right hf.supp

@[fun_prop]
lemma IsTestFunction.sum {ι} [Fintype ι] {φ : X → ι → U} {hφ : ∀ i, IsTestFunction (φ · i)} :
    IsTestFunction (fun x => ∑ i, φ x i) := by fun_prop (disch:=simp)

@[fun_prop]
lemma IsTestFunction.coord {φ : X → Space d} (hφ : IsTestFunction φ) (i : Fin d) :
    IsTestFunction (fun x => (φ x).coord i) := by fun_prop (disch:=simp[Space.coord])

@[fun_prop]
lemma IsTestFunction.linearMap_comp {f : X → V} (hf : IsTestFunction f)
    {g : V →ₗ[ℝ] U} (hg : ContDiff ℝ ∞ g) :
    IsTestFunction (fun x => g (f x)) := by fun_prop (disch:=simp)

@[fun_prop]
lemma IsTestFunction.family_linearMap_comp {f : X → V} (hf : IsTestFunction f)
    {g : X → V →L[ℝ] U} (hg : ContDiff ℝ ∞ g) :
    IsTestFunction (fun x => g x (f x)) where
  smooth := by
    fun_prop
  supp := by
    have hf' := hf.supp
    rw [← exists_compact_iff_hasCompactSupport] at hf' ⊢
    obtain ⟨K, cK, hK⟩ := hf'
    refine ⟨K, cK, fun x hx => ?_⟩
    rw [hK x hx]
    simp

@[fun_prop]
lemma IsTestFunction.deriv {f : ℝ → U} (hf : IsTestFunction f) :
    IsTestFunction (fun x => deriv f x) where
  smooth := deriv' hf.smooth
  supp := HasCompactSupport.deriv hf.supp

@[fun_prop]
lemma IsTestFunction.of_fderiv {f : X → U} (hf : IsTestFunction f) :
    IsTestFunction (fderiv ℝ f ·) where
  smooth := by
    apply ContDiff.fderiv (m := ∞)
    · fun_prop
    · fun_prop
    · exact Preorder.le_refl (∞ + 1)
  supp := by
    apply HasCompactSupport.fderiv
    exact hf.supp

@[fun_prop]
lemma IsTestFunction.fderiv_apply {f : X → U} (hf : IsTestFunction f) (δx : X) :
    IsTestFunction (fderiv ℝ f · δx) where
  smooth := by
    apply ContDiff.fderiv_apply (m := ∞)
    · fun_prop
    · fun_prop
    · fun_prop
    · exact Preorder.le_refl (∞ + 1)
  supp := by
    apply HasCompactSupport.fderiv_apply
    exact hf.supp

open InnerProductSpace' in
@[fun_prop]
lemma IsTestFunction.adjFDeriv {f : X → U} [InnerProductSpace' ℝ X]
    [InnerProductSpace' ℝ U] [CompleteSpace X]
    [CompleteSpace U] (dy : U) (hf : IsTestFunction f) :
    IsTestFunction (fun x => adjFDeriv ℝ f x dy) := by
  unfold _root_.adjFDeriv
  conv =>
    enter [1, x]
    rw [adjoint_eq_clm_adjoint]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  apply IsTestFunction.comp_left
  · constructor
    · apply ContDiff.clm_apply
      · apply ContDiff.comp
        · apply LinearIsometryEquiv.contDiff
        · fun_prop
      · fun_prop
    have hf : HasCompactSupport (fun x => fderiv ℝ f x) :=
      (IsTestFunction.of_fderiv hf).supp
    rw [← exists_compact_iff_hasCompactSupport] at hf ⊢
    obtain ⟨K, cK, hK⟩ := hf
    refine ⟨K, cK, fun x hx => ?_⟩
    rw [hK x hx]
    simp
  · simp
  · fun_prop

@[fun_prop]
lemma IsTestFunction.divergence {f : X → X} [FiniteDimensional ℝ X] (hf : IsTestFunction f) :
    IsTestFunction (fun x => divergence ℝ f x) := by
  obtain ⟨s, ⟨bX⟩⟩ := Basis.exists_basis ℝ X
  haveI : Fintype s := FiniteDimensional.fintypeBasisIndex bX
  conv_rhs =>
    enter [x]
    rw [divergence_eq_sum_fderiv' bX]
  apply IsTestFunction.sum
  intro i
  let f : X →ₗ[ℝ] ℝ := {
      toFun := (bX.repr · i)
      map_add' := by simp
      map_smul' := by simp

    }
  let f' : X →L[ℝ] ℝ := (f).toContinuousLinearMap
  change IsTestFunction (fun x => f' _)
  apply IsTestFunction.comp_left
  fun_prop
  simp only [map_zero]
  fun_prop
  /-unfold _root_.divergence
  apply IsTestFunction.comp_left
    (f:=fun x : X => (fderiv ℝ f x)) (g:=fun f : X →L[ℝ] X => LinearMap.trace _ _ f.toLinearMap)
  · fun_prop
  · simp
  · sorry -- missing mathlib API-/

@[fun_prop]
lemma IsTestFunction.gradient {d : ℕ} (φ : Space d → ℝ)
    (hφ : IsTestFunction φ) :
    IsTestFunction (gradient φ) := by
  have h := fun x => gradient_eq_adjFDeriv (hφ.differentiable x)
  eta_expand; simp[h]
  fun_prop

@[fun_prop]
lemma IsTestFunction.of_div {d : ℕ} (φ : Space d → EuclideanSpace ℝ (Fin d))
    (hφ : IsTestFunction φ) :
    IsTestFunction (Space.div φ) := by
  unfold Space.div Space.deriv; dsimp; fun_prop (disch:=simp)

end IsTestFunction
