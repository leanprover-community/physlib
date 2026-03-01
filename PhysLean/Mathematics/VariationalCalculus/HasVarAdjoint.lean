/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
import PhysLean.Mathematics.VariationalCalculus.IsLocalizedfunctionTransform
/-!
# Variational adjoint

Definition of adjoint of linear function between function spaces. It is inspired by the definition
of distributional adjoint of linear maps between test functions as described here:
https://en.wikipedia.org/wiki/Distribution_(mathematics) under 'Preliminaries: Transpose of a linear
operator' but we require that the adjoint is function between test functions too.

The key results are:
  - variational adjoint is unique on test functions
  - variational adjoint of identity is identity, `HasVarAdjoint.id`
  - variational adjoint of composition is composition of adjoint in reverse order,
    `HasVarAdjoint.comp`
  - variational adjoint of deriv is `- deriv`, `HasVarAdjoint.deriv`
  - variational adjoint of algebraic operations is algebraic operation of adjoints,
    `HasVarAdjoint.neg`, `HasVarAdjoint.add`, `HasVarAdjoint.sub`, `HasVarAdjoint.mul_left`,
    `HasVarAdjoint.mul_right`, `HasVarAdjoint.smul_left`, `HasVarAdjoint.smul_right`
-/

open Module InnerProductSpace MeasureTheory ContDiff

variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasureSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasureSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasureSpace Z]
  {U} [NormedAddCommGroup U] [NormedSpace ℝ U] [InnerProductSpace' ℝ U]
  {V} [NormedAddCommGroup V] [NormedSpace ℝ V] [InnerProductSpace' ℝ V]
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [InnerProductSpace' ℝ W]

/-- Map `F` from `(X → U)` to `(X → V)` has a variational adjoint `F'` if it preserves
test functions and satisfies the adjoint relation `⟪F φ, ψ⟫ = ⟪φ, F' ψ⟫`for all test functions
`φ` and `ψ` for `⟪φ, ψ⟫ = ∫ x, ⟪φ x, ψ x⟫_ℝ ∂μ`.

The canonical example is the function `F = deriv` that has adjoint `F' = - deriv`.

This notion of adjoint allows us to do formally variational calculus as often encountered in physics
textbooks. In mathematical literature, the adjoint is often defined for unbounded operators, but
such formal treatment is unnecessarily complicated for physics applications.
-/
structure HasVarAdjoint
    (F : (X → U) → (Y → V)) (F' : (Y → V) → (X → U)) where
  test_fun_preserving : ∀ φ, IsTestFunction φ → IsTestFunction (F φ)
  test_fun_preserving' : ∀ φ, IsTestFunction φ → IsTestFunction (F' φ)
  adjoint : ∀ φ ψ, IsTestFunction φ → IsTestFunction ψ →
    ∫ y, ⟪F φ y, ψ y⟫_ℝ = ∫ x, ⟪φ x, F' ψ x⟫_ℝ
  ext' : IsLocalizedFunctionTransform F'

namespace HasVarAdjoint

@[symm]
lemma symm {F : (X → U) → (Y → V)} {F' : (Y → V) → (X → U)}
    (hF : HasVarAdjoint F F') (h : IsLocalizedFunctionTransform F) :
    HasVarAdjoint F' F where
  test_fun_preserving φ hφ := hF.test_fun_preserving' φ hφ
  test_fun_preserving' φ hφ := hF.test_fun_preserving φ hφ
  adjoint φ ψ hφ hψ := by
    conv_lhs =>
      enter [2, y]
      rw [real_inner_comm']
    rw [← hF.adjoint _ _ hψ hφ]
    congr
    funext x
    rw [real_inner_comm']
  ext' := h

lemma id : HasVarAdjoint (fun φ : X → U => φ) (fun φ => φ) where
  test_fun_preserving _ hφ := hφ
  test_fun_preserving' _ hφ := hφ
  adjoint _ _ _ _ := rfl
  ext' := IsLocalizedFunctionTransform.id

lemma zero : HasVarAdjoint (fun (_ : X → U) (_ : Y) => (0 : V)) (fun _ _ => 0) where
  test_fun_preserving _ hφ := by fun_prop
  test_fun_preserving' _ hφ := by fun_prop
  adjoint _ _ _ _ := by simp
  ext' := fun K cK => ⟨∅,isCompact_empty,fun _ _ h _ _ => rfl⟩

lemma comp {F : (Y → V) → (Z → W)} {G : (X → U) → (Y → V)} {F' G'}
    (hF : HasVarAdjoint F F') (hG : HasVarAdjoint G G') :
    HasVarAdjoint (fun φ => F (G φ)) (fun φ => G' (F' φ)) where
  test_fun_preserving _ hφ := hF.test_fun_preserving _ (hG.test_fun_preserving _ hφ)
  test_fun_preserving' _ hφ := hG.test_fun_preserving' _ (hF.test_fun_preserving' _ hφ)
  adjoint φ ψ hφ hψ := by
    rw [hF.adjoint _ _ (hG.test_fun_preserving φ hφ) hψ]
    rw [hG.adjoint _ _ hφ (hF.test_fun_preserving' _ hψ)]
  ext' := IsLocalizedFunctionTransform.fun_comp hG.ext' hF.ext'

lemma congr_fun {F G : (X → U) → (Y → V)} {F' : (Y → V) → (X → U)}
    (h : HasVarAdjoint G F') (h' : ∀ φ, IsTestFunction φ → F φ = G φ) :
    HasVarAdjoint F F' where
  test_fun_preserving φ hφ := by
    rw[h' _ hφ]
    exact h.test_fun_preserving φ hφ
  test_fun_preserving' φ hφ := h.test_fun_preserving' φ hφ
  adjoint φ ψ hφ hψ := by
    rw [h' φ hφ]
    exact h.adjoint φ ψ hφ hψ
  ext' := h.ext'

lemma of_eq {F : (X → U) → (Y → V)} {F' G' : (Y → V) → (X → U)}
    (hF' : HasVarAdjoint F F') (h : ∀ φ, IsTestFunction φ → F' φ = G' φ)
    (hlin : IsLocalizedFunctionTransform G') :
    HasVarAdjoint F G' where
  test_fun_preserving φ hφ := hF'.test_fun_preserving φ hφ
  test_fun_preserving' φ hφ := by
    rw [← h φ hφ]
    exact hF'.test_fun_preserving' φ hφ
  adjoint φ ψ hφ hψ := by
    rw [← h ψ hψ]
    exact hF'.adjoint φ ψ hφ hψ
  ext' := hlin

/-- Variational adjoint is unique only when applied to test functions. -/
lemma unique_on_test_functions {F : (X → U) → (Y → V)} {F' G' : (Y → V) → (X → U)}
    [IsFiniteMeasureOnCompacts (@volume X _)] [(@volume X _).IsOpenPosMeasure]
    [OpensMeasurableSpace X] (hF' : HasVarAdjoint F F') (hG' : HasVarAdjoint F G') :
    ∀ φ, IsTestFunction φ → F' φ = G' φ := by
  obtain ⟨F_preserve_test, F'_preserve_test, F'_adjoint⟩ := hF'
  obtain ⟨F_preserve_test, G'_preserve_test, G'_adjoint⟩ := hG'
  intro φ hφ
  rw [← zero_add (G' φ)]
  rw [← sub_eq_iff_eq_add]
  change (F' - G') φ = 0
  apply fundamental_theorem_of_variational_calculus (@volume X _)
  · simp
    apply IsTestFunction.sub
    · exact F'_preserve_test φ hφ
    · exact G'_preserve_test φ hφ
  · intro ψ hψ
    simp [inner_sub_left']
    rw [MeasureTheory.integral_sub]
    · conv_lhs =>
        enter [2, 2, a]
        rw [← inner_conj_symm']
      conv_lhs =>
        enter [1, 2, a]
        rw [← inner_conj_symm']
      simp[← F'_adjoint ψ φ hψ hφ,G'_adjoint ψ φ hψ hφ]
    · apply IsTestFunction.integrable
      apply IsTestFunction.inner
      · exact F'_preserve_test φ hφ
      · exact hψ
    · apply IsTestFunction.integrable
      apply IsTestFunction.inner
      · exact G'_preserve_test φ hφ
      · exact hψ

/-- Variational adjoint is unique only when applied to smooth functions. -/
lemma unique
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [MeasureSpace X] [OpensMeasurableSpace X]
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [FiniteDimensional ℝ Y] [MeasureSpace Y]
    {F : (X → U) → (Y → V)} {F' G' : (Y → V) → (X → U)}
    [IsFiniteMeasureOnCompacts (@volume X _)] [(@volume X _).IsOpenPosMeasure]
    (hF : HasVarAdjoint F F') (hG : HasVarAdjoint F G') :
    ∀ f, ContDiff ℝ ∞ f → F' f = G' f := by

  intro f hf; funext x

  obtain ⟨K, cK, hK⟩ := hF.ext' {x} (isCompact_singleton)
  obtain ⟨L, cL, hL⟩ := hG.ext' {x} (isCompact_singleton)
  -- have hK : x ∈ {x} K := by
  -- exact? Set.mem_singleton x
  have hnonempty : Set.Nonempty ({0} ∪ (K ∪ L)) := by simp

  -- prepare test function that is one on `D ∪ D'`
  let r := sSup ((fun x => ‖x‖) '' ({0} ∪ (K ∪ L)))
  have : 0 ≤ r := by
    obtain ⟨x, h1, h2, h3⟩ := IsCompact.exists_sSup_image_eq_and_ge (s := {0} ∪ (K ∪ L))
      (IsCompact.union (by simp) (IsCompact.union cK cL)) hnonempty
      (f := fun x => ‖x‖) (by fun_prop)
    unfold r
    apply le_of_le_of_eq (b := ‖x‖)
    · exact norm_nonneg x
    · rw [← h2]

  let φ : ContDiffBump (0 : Y) := {
    rIn := r + 1,
    rOut := r + 2,
    rIn_pos := by linarith,
    rIn_lt_rOut := by linarith}

  -- few properties about `φ`
  let φ' := fun x => φ.toFun x
  have hφ : IsTestFunction (fun x : Y => φ x) := by
    constructor
    apply ContDiffBump.contDiff
    apply ContDiffBump.hasCompactSupport
  have hφ' : ∀ x, x ∈ K ∪ L → x ∈ Metric.closedBall 0 φ.rIn := by
    intro x hx
    simp [φ, r, -Set.singleton_union]
    obtain ⟨y, h1, h2, h3⟩ := IsCompact.exists_sSup_image_eq_and_ge (s := {0} ∪ (K ∪ L))
      (IsCompact.union (by simp) (IsCompact.union cK cL)) hnonempty
      (f := fun x => ‖x‖) (by fun_prop)
    rw [h2]
    have h3' := h3 x (by simp[hx])
    apply le_trans h3'
    simp

  let ψ := fun x => φ x • f x
  have hψ : IsTestFunction (fun x : Y => ψ x) := by fun_prop
  have hψK : ∀ x ∈ K, f x = ψ x := by
    intros x hx; unfold ψ
    rw[ContDiffBump.one_of_mem_closedBall]
    · simp
    · apply hφ'; simp [hx]
  have hψL : ∀ x ∈ L, f x = ψ x := by
    intros x hx; unfold ψ
    rw[ContDiffBump.one_of_mem_closedBall]
    · simp
    · apply hφ'; simp [hx]

  simp only [hK f ψ hψK x rfl, hL f ψ hψL x rfl, unique_on_test_functions hF hG ψ hψ]

lemma neg {F : (X → U) → (X → V)} {F' : (X → V) → (X → U)}
    (hF : HasVarAdjoint F F') :
    HasVarAdjoint (fun φ x => - F φ x) (fun φ x => - F' φ x) where
  test_fun_preserving _ hφ := by
    have := hF.test_fun_preserving _ hφ
    fun_prop
  test_fun_preserving' _ hφ := by
    have := hF.test_fun_preserving' _ hφ
    fun_prop
  adjoint _ _ _ _ := by
    simp [integral_neg]
    rw[hF.adjoint _ _ (by assumption) (by assumption)]
  ext' := IsLocalizedFunctionTransform.neg hF.ext'
  -- ext := IsLocalizedFunctionTransform.neg hF.ext

lemma of_neg {F : (X → U) → (X → V)} {F' : (X → V) → (X → U)}
    (hF : HasVarAdjoint (fun φ x => - F φ x) (fun φ x => - F' φ x)) :
    HasVarAdjoint F F' := by
  have hF : F = (fun φ x => - - F φ x) := by simp
  have hF' : F' = (fun φ x => - - F' φ x) := by simp
  rw [hF, hF']
  (expose_names; exact neg hF_1)

section OnFiniteMeasures

variable
    [OpensMeasurableSpace X]
    [IsFiniteMeasureOnCompacts (@volume X _)]

lemma add {F G : (X → U) → (X → V)} {F' G' : (X → V) → (X → U)}
    (hF : HasVarAdjoint F F') (hG : HasVarAdjoint G G') :
    HasVarAdjoint (fun φ x => F φ x + G φ x) (fun φ x => F' φ x + G' φ x) where
  test_fun_preserving _ hφ := by
    have := hF.test_fun_preserving _ hφ
    have := hG.test_fun_preserving _ hφ
    fun_prop
  test_fun_preserving' _ hφ := by
    have := hF.test_fun_preserving' _ hφ
    have := hG.test_fun_preserving' _ hφ
    fun_prop
  adjoint _ _ _ _ := by
    simp[inner_add_left',inner_add_right']
    rw[MeasureTheory.integral_add]
    rw[MeasureTheory.integral_add]
    rw[hF.adjoint _ _ (by assumption) (by assumption)]
    rw[hG.adjoint _ _ (by assumption) (by assumption)]
    · apply IsTestFunction.integrable
      apply IsTestFunction.inner
      · (expose_names; exact h)
      · (expose_names; exact hF.test_fun_preserving' x_1 h_1)
    · apply IsTestFunction.integrable
      apply IsTestFunction.inner
      · (expose_names; exact h)
      · (expose_names; exact hG.test_fun_preserving' x_1 h_1)
    · apply IsTestFunction.integrable
      apply IsTestFunction.inner
      · (expose_names; exact hF.test_fun_preserving x h)
      · (expose_names; exact h_1)
    · apply IsTestFunction.integrable
      apply IsTestFunction.inner
      · (expose_names; exact hG.test_fun_preserving x h)
      · (expose_names; exact h_1)
  ext' := IsLocalizedFunctionTransform.add hF.ext' hG.ext'
  -- ext := IsLocalizedFunctionTransform.add hF.ext hG.ext

lemma sum {ι : Type} [Fintype ι] {F : ι → (X → U) → (X → V)} {F' : ι → (X → V) → (X → U)}
    (hF : ∀ i, HasVarAdjoint (F i) (F' i)) :
    HasVarAdjoint (fun φ x => ∑ i, F i φ x) (fun φ x => ∑ i, F' i φ x) := by
  let P (ι : Type) [Fintype ι] : Prop :=
    ∀ (F : ι → (X → U) → (X → V)) (F' : ι → (X → V) → (X → U))
      (hF : ∀ i, HasVarAdjoint (F i) (F' i)),
      HasVarAdjoint (fun φ x => ∑ i, F i φ x) (fun φ x => ∑ i, F' i φ x)
  have h1 : P ι := by
    apply Fintype.induction_empty_option
    · intro ι1 ι2 _ e h F F' hF
      convert h (fun i => F (e i)) (fun i => F' (e i)) fun i => hF (e i)
      rw [← @e.sum_comp _ _ _ (Fintype.ofEquiv ι2 e.symm)]
      rw [← @e.sum_comp _ _ _ (Fintype.ofEquiv ι2 e.symm)]
    · simp [P]
      exact zero
    · intro ι _ h
      simp [P]
      intro F F' hF
      apply add
      · exact hF none
      · exact h (fun i => F (some i)) (fun i => F' (some i)) fun i => hF (some i)
  exact h1 F F' hF

lemma sub {F G : (X → U) → (X → V)} {F' G' : (X → V) → (X → U)}
    (hF : HasVarAdjoint F F') (hG : HasVarAdjoint G G') :
    HasVarAdjoint (fun φ x => F φ x - G φ x) (fun φ x => F' φ x - G' φ x) := by
  simp [sub_eq_add_neg]
  apply add hF (neg hG)

end OnFiniteMeasures

lemma mul_left {F : (X → U) → (X → ℝ)} {ψ : X → ℝ} {F' : (X → ℝ) → (X → U)}
    (hF : HasVarAdjoint F F') (hψ : ContDiff ℝ ∞ ψ) :
    HasVarAdjoint (fun φ x => ψ x * F φ x) (fun φ x => F' (fun x => ψ x * φ x) x) where
  test_fun_preserving φ hφ := by
    have := hF.test_fun_preserving _ hφ
    fun_prop
  test_fun_preserving' φ hφ := by
    apply hF.test_fun_preserving'
    fun_prop
  adjoint φ ψ' hφ hψ' := by
    rw [← hF.adjoint]
    · congr; funext x; simp; ring
    · exact hφ
    · apply IsTestFunction.mul_left
      · exact hψ
      · exact hψ'
  ext' := by
    intro K cK
    obtain ⟨L,cL,h⟩ := hF.ext' K cK
    exact ⟨L,cL,by intro _ _ hφ _ _; apply h <;> simp_all⟩
  -- ext := IsLocalizedFunctionTransform.mul_left hF.ext

lemma mul_right {F : (X → U) → (X → ℝ)} {ψ : X → ℝ} {F' : (X → ℝ) → (X → U)}
    (hF : HasVarAdjoint F F') (hψ : ContDiff ℝ ∞ ψ) :
    HasVarAdjoint (fun φ x => F φ x * ψ x) (fun φ x => F' (fun x => φ x * ψ x) x) where
  test_fun_preserving φ hφ := by
    have := hF.test_fun_preserving _ hφ
    fun_prop
  test_fun_preserving' φ hφ := by
    apply hF.test_fun_preserving'
    fun_prop
  adjoint φ ψ' hφ hψ' := by
    rw [← hF.adjoint]
    · congr; funext x; simp; ring
    · exact hφ
    · apply IsTestFunction.mul_right
      · exact hψ'
      · exact hψ
  ext' := by
    intro K cK
    obtain ⟨L,cL,h⟩ := hF.ext' K cK
    exact ⟨L,cL,by intro _ _ hφ _ _; apply h <;> simp_all⟩
  -- ext := IsLocalizedFunctionTransform.mul_right hF.ext

lemma smul_left {F : (X → U) → (X → V)} {ψ : X → ℝ} {F' : (X → V) → (X → U)}
    (hF : HasVarAdjoint F F') (hψ : ContDiff ℝ ∞ ψ) :
    HasVarAdjoint (fun φ x => ψ x • F φ x) (fun φ x => F' (fun x' => ψ x' • φ x') x) where
  test_fun_preserving φ hφ := by
    have := hF.test_fun_preserving φ hφ
    fun_prop
  test_fun_preserving' φ hφ := by
    apply hF.test_fun_preserving' _ _
    fun_prop
  adjoint φ ψ hφ hψ := by
    simp_rw[inner_smul_left', ← inner_smul_right']
    rw [hF.adjoint]
    · rfl
    · exact hφ
    · simp; fun_prop
  ext' := by
    intro K cK
    obtain ⟨L,cL,h⟩ := hF.ext' K cK
    exact ⟨L,cL,by intro _ _ hφ _ _; apply h <;> simp_all⟩
  -- ext := IsLocalizedFunctionTransform.smul_left hF.ext

lemma smul_right {F : (X → U) → (X → V)} {ψ : X → ℝ} {F' : (X → V) → (X → U)}
    (hF : HasVarAdjoint F F') (hψ : ContDiff ℝ ∞ ψ) :
    HasVarAdjoint (fun φ x => ψ x • F φ x) (fun φ x => F' (fun x' => ψ x' • φ x') x) where
  test_fun_preserving φ hφ := by
    have := hF.test_fun_preserving φ hφ
    fun_prop
  test_fun_preserving' φ hφ := by
    apply hF.test_fun_preserving' _ _
    fun_prop
  adjoint φ ψ hφ hψ := by
    simp_rw[inner_smul_left', ← inner_smul_right']
    rw [hF.adjoint]
    · rfl
    · exact hφ
    · simp; fun_prop
  ext' := by
    intro K cK
    obtain ⟨L,cL,h⟩ := hF.ext' K cK
    exact ⟨L,cL,by intro _ _ hφ _ _; apply h <;> simp_all⟩
  -- ext := IsLocalizedFunctionTransform.smul_left hF.ext

attribute [fun_prop] LinearIsometryEquiv.contDiff

open InnerProductSpace' in
lemma clm_apply
    [CompleteSpace U] [CompleteSpace V] (f : X → (U →L[ℝ] V))
    (hf : ContDiff ℝ ∞ f) :
    HasVarAdjoint (fun (φ : X → U) x => f x (φ x)) (fun ψ x => _root_.adjoint ℝ (f x) (ψ x)) where
  test_fun_preserving φ hφ := by
    apply IsTestFunction.family_linearMap_comp
    · exact hφ
    · exact hf
  test_fun_preserving' φ hφ := by
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
      have hf : HasCompactSupport (fun x => φ x) :=
        hφ.supp
      rw [← exists_compact_iff_hasCompactSupport] at hf ⊢
      obtain ⟨K, cK, hK⟩ := hf
      refine ⟨K, cK, fun x hx => ?_⟩
      rw [hK x hx]
      simp
    · simp
    · fun_prop
  adjoint φ ψ hφ hψ := by
    congr; funext x
    symm; apply HasAdjoint.adjoint_inner_right
    apply HasAdjoint.congr_adj
    apply ContinuousLinearMap.hasAdjoint
    funext y; simp[adjoint_eq_clm_adjoint]
  ext' := by
    intro K cK
    exact ⟨K, cK, by intro _ _ hφ _ _; simp_all⟩
  -- ext := IsLocalizedFunctionTransform.clm_apply _

protected lemma deriv :
    HasVarAdjoint (fun φ : ℝ → U => deriv φ) (fun φ x => - deriv φ x) where
  test_fun_preserving _ hφ := by
    have ⟨h,h'⟩ := hφ
    constructor
    · fun_prop
    · exact HasCompactSupport.deriv h'
  test_fun_preserving' _ hφ := by
    have ⟨h,h'⟩ := hφ
    constructor
    · fun_prop
    · apply HasCompactSupport.neg
      apply HasCompactSupport.deriv h'
  adjoint φ ψ hφ hψ := by
    trans ∫ (x : ℝ), ⟪deriv φ x, ψ x⟫_ℝ
    · congr
    suffices ∫ (x : ℝ), deriv (fun x' => ⟪φ x', ψ x'⟫_ℝ) x = 0 by
      rw [← sub_eq_zero, ← integral_sub, ← this]
      congr
      funext a
      rw [deriv_inner_apply']
      simp only [inner_neg_right', sub_neg_eq_add]
      ring
      · exact hφ.differentiable a
      · exact hψ.differentiable a
      · apply IsTestFunction.integrable
        fun_prop
      · apply IsTestFunction.integrable
        fun_prop
    apply MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable
      (f:=(fun x' => ⟪φ x', ψ x'⟫_ℝ))
    · intro x
      rw [hasDerivAt_deriv_iff]
      exact (hφ.differentiable x).inner' (hψ.differentiable x)
    · fun_prop
    · apply IsTestFunction.integrable (hφ.inner hψ)
  ext' := by
    apply IsLocalizedFunctionTransform.neg
    apply IsLocalizedFunctionTransform.deriv
  -- ext := IsLocalizedFunctionTransform.deriv

lemma fderiv_apply {dx}
    [ProperSpace X] [BorelSpace X]
    [FiniteDimensional ℝ X] [(@volume X _).IsAddHaarMeasure] :
    HasVarAdjoint (fun φ : X → U => (fderiv ℝ φ · dx)) (fun φ x => - fderiv ℝ φ x dx) where
  test_fun_preserving φ hφ := by fun_prop
  test_fun_preserving' φ hφ := by fun_prop
  ext' := by
    apply IsLocalizedFunctionTransform.neg
    apply IsLocalizedFunctionTransform.fderiv
  adjoint φ ψ hφ hψ := by
    rw [← sub_eq_zero]
    rw [← integral_sub]
    · trans ∫ (a : X), fderiv ℝ (fun a => ⟪φ a, ψ a⟫_ℝ) a dx
      · congr
        funext a
        simp only [inner_neg_right', sub_neg_eq_add]
        rw [fderiv_inner_apply']
        rw [add_comm]
        · exact hφ.differentiable a
        · exact hψ.differentiable a
      · have h1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := fun a => 1)
          (g := (fun a => ⟪φ a, ψ a⟫_ℝ)) (v := dx) (by simp) (by
            simp only [one_mul]
            apply IsTestFunction.integrable _ (@volume X _)
            fun_prop)
          (by
            simp only [one_mul]
            apply IsTestFunction.integrable
            fun_prop) (by fun_prop) (IsTestFunction.differentiable (by fun_prop))
        simpa using h1
    · apply IsTestFunction.integrable
      fun_prop
    · apply IsTestFunction.integrable
      fun_prop
  -- ext := IsLocalizedFunctionTransform.fderiv

omit [MeasureSpace Y] in
lemma adjFDeriv_apply
    [InnerProductSpace' ℝ X] [InnerProductSpace' ℝ Y]
    [ProperSpace X] [BorelSpace X] [FiniteDimensional ℝ X]
    [CompleteSpace Y] [(@volume X _).IsAddHaarMeasure] {dy} :
    HasVarAdjoint (fun φ : X → Y => (adjFDeriv ℝ φ · dy)) (fun ψ x => - divergence ℝ ψ x • dy) where
  test_fun_preserving φ hφ := IsTestFunction.adjFDeriv dy hφ
  test_fun_preserving' φ hφ := by fun_prop
  ext' := by
    intro K cK
    use (Metric.cthickening 1 K)
    constructor
    · exact IsCompact.cthickening cK
    · intro φ φ' hφ
      have h : ∀ x ∈ K, φ =ᶠ[nhds x] φ' := by
        intro x hx
        apply Filter.eventuallyEq_of_mem (s := Metric.thickening 1 K)
        refine mem_interior_iff_mem_nhds.mp ?_
        rw [@mem_interior]
        use Metric.thickening 1 K
        simp only [subset_refl, true_and]
        apply And.intro
        · exact Metric.isOpen_thickening
        · rw [@Metric.mem_thickening_iff_exists_edist_lt]
          use x
          simpa using hx
        · intro x hx
          have hx' : x ∈ Metric.cthickening 1 K := Metric.thickening_subset_cthickening 1 K hx
          exact hφ x hx'
      intro x hx; dsimp[divergence]; congr 4
      rw [Filter.EventuallyEq.fderiv_eq (h x hx)]
  adjoint φ ψ hφ hψ := by
    obtain ⟨s, ⟨bX⟩⟩ := Basis.exists_basis ℝ X
    haveI : Fintype s := FiniteDimensional.fintypeBasisIndex bX
    let f (i : s) : X →ₗ[ℝ] ℝ := {
      toFun := (bX.repr · i)
      map_add' := by simp
      map_smul' := by simp

    }
    let f' (i : s) : X →L[ℝ] ℝ := (f i).toContinuousLinearMap
    calc _ = ∫ (y : X), ⟪dy, fderiv ℝ φ y (ψ y)⟫_ℝ := by
            congr
            funext y
            have h1 := DifferentiableAt.hasAdjFDerivAt (hφ.differentiable y)
            rw [h1.hasAdjoint_fderiv.adjoint_inner_left]
        _ = ∑ i, ∫ (y : X), bX.repr (ψ y) i * fderiv ℝ (fun y' => ⟪dy, φ y' ⟫_ℝ) y (bX i) := by
            have h (y : X) : ψ y = ∑ i, bX.repr (ψ y) i • bX i := by
              exact Eq.symm (Basis.sum_equivFun bX (ψ y))
            conv_lhs =>
              enter [2, y]
              rw [h]
              simp only [map_sum, map_smul, inner_sum']
            rw [MeasureTheory.integral_finset_sum]
            congr
            funext i
            congr
            funext y
            simp [inner_smul_right']
            left
            rw [fderiv_inner_apply']
            simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply,
              inner_zero_left', add_zero]
            · fun_prop
            · exact hφ.differentiable y
            · intro i hi
              apply IsTestFunction.integrable
              simp [inner_smul_right']
              apply IsTestFunction.mul_right
              · change IsTestFunction fun x => f' i (ψ x)
                apply IsTestFunction.comp_left
                · exact hψ
                · simp
                · fun_prop
              · fun_prop
        _ = ∑ i, ∫ (y : X), - fderiv ℝ (fun y' => bX.repr (ψ y') i) y (bX i) * ⟪dy, φ y⟫_ℝ := by
            congr; funext i
            rw[integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable]
            · simp[integral_neg]
            · apply IsTestFunction.integrable
              apply IsTestFunction.mul_left
              · apply IsTestFunction.smooth
                apply IsTestFunction.fderiv_apply
                change IsTestFunction fun y => f' i (ψ y)
                apply IsTestFunction.comp_left
                · exact hψ
                · simp
                · fun_prop
              · apply IsTestFunction.inner_left
                · fun_prop
                · exact hφ
            · apply IsTestFunction.integrable
              apply IsTestFunction.mul_left
              · apply IsTestFunction.smooth
                change IsTestFunction fun y => f' i (ψ y)
                apply IsTestFunction.comp_left
                · exact hψ
                · simp
                · fun_prop
              · apply IsTestFunction.fderiv_apply
                apply IsTestFunction.comp_left
                · exact hφ
                · simp
                · fun_prop
            · apply IsTestFunction.integrable
              apply IsTestFunction.mul_left
              · apply IsTestFunction.smooth
                change IsTestFunction fun y => f' i (ψ y)
                apply IsTestFunction.comp_left
                · exact hψ
                · simp
                · fun_prop
              · apply IsTestFunction.inner_left
                · fun_prop
                · exact hφ
            · change Differentiable ℝ fun y => f' i (ψ y)
              fun_prop
            · fun_prop
        _ = ∫ (y : X), - (∑ i, fderiv ℝ (fun y' => bX.repr (ψ y') i) y (bX i)) * ⟪dy, φ y⟫_ℝ := by
            rw [← MeasureTheory.integral_finset_sum]
            · congr
              funext y
              simp [Finset.sum_mul]
            · intro i _
              apply IsTestFunction.integrable
              apply IsTestFunction.mul_left
              · apply IsTestFunction.smooth
                apply IsTestFunction.neg
                apply IsTestFunction.fderiv_apply
                change IsTestFunction fun y => f' i (ψ y)
                apply IsTestFunction.comp_left
                · exact hψ
                · simp
                · fun_prop
              · apply IsTestFunction.inner_left
                · fun_prop
                · exact hφ
        _ = _ := by
            congr
            funext y
            rw [divergence_eq_sum_fderiv' bX]
            simp only [neg_mul, neg_smul, inner_neg_right', neg_inj]
            rw [inner_smul_right']
            congr 1
            congr 1
            funext i
            trans (fderiv ℝ (f' i ∘ ψ) y) (bX i)
            · rfl
            rw [fderiv_comp]
            simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp',
              Function.comp_apply]
            simp [f',f]
            · exact ContinuousLinearMap.differentiableAt _
            · exact hψ.differentiable y
            · exact real_inner_comm' (φ y) dy
  -- ext := IsLocalizedFunctionTransform.adjFDeriv

protected lemma gradient {d} :
    HasVarAdjoint (fun φ : Space d → ℝ => gradient φ)
    (fun φ x => - Space.div (Space.basis.repr ∘ φ) x) := by
  apply HasVarAdjoint.congr_fun (G := (fun φ => (adjFDeriv ℝ φ · 1)))
  · apply of_eq adjFDeriv_apply
    · intro φ hφ
      funext x
      rw [divergence_eq_space_div]
      simp only [smul_eq_mul, mul_one]
      exact hφ.differentiable
    · apply IsLocalizedFunctionTransform.neg

      apply IsLocalizedFunctionTransform.div_comp_repr
  · intro φ hφ
    funext x
    rw [gradient_eq_adjFDeriv]
    apply hφ.differentiable x

lemma grad {d} : HasVarAdjoint (fun (φ : Space d → ℝ) x => Space.grad φ x)
    (fun ψ x => - Space.div ψ x) := by
  let f : Space d → Space d →L[ℝ] EuclideanSpace ℝ (Fin d) := fun x =>
    Space.basis.repr.toContinuousLinearMap
  have h1 := clm_apply f (by fun_prop)
  simp [f] at h1
  have hx : (_root_.adjoint ℝ (⇑Space.basis.repr)) = (Space.basis (d := d)).repr.symm := by
    refine HasAdjoint.adjoint ?_
    refine { adjoint_inner_left := ?_ }
    intro x y
    rw [real_inner_comm, ← Space.basis_repr_inner_eq, real_inner_comm]
  simp [hx] at h1
  have h2 := HasVarAdjoint.comp h1 (HasVarAdjoint.gradient (d := d))
  convert h2 using 1
  · funext x t
    rw [Space.grad_eq_gradiant]
    simp

lemma div {d} : HasVarAdjoint (fun (φ : Space d → EuclideanSpace ℝ (Fin d)) x => Space.div φ x)
    (fun ψ x => - Space.grad ψ x) := by
  apply HasVarAdjoint.of_neg
  apply HasVarAdjoint.symm
  simp only [neg_neg]
  exact HasVarAdjoint.grad
  simp only [neg_neg]
  exact IsLocalizedFunctionTransform.grad

lemma prod
    [IsFiniteMeasureOnCompacts (@volume X _)] [OpensMeasurableSpace X]
    {F : (X → U) → (X → V)} {G : (X → U) → (X → W)} {F' G'}
    (hF : HasVarAdjoint F F') (hG : HasVarAdjoint G G') :
    HasVarAdjoint
      (fun φ x => (F φ x, G φ x))
      (fun φ x => F' (fun x' => (φ x').1) x + G' (fun x' => (φ x').2) x) where
  test_fun_preserving _ hφ := by
    have := hF.test_fun_preserving _ hφ
    have := hG.test_fun_preserving _ hφ
    fun_prop
  test_fun_preserving' y hφ := by
    have := hF.test_fun_preserving' (fun x => (y x).1) (by fun_prop)
    have := hG.test_fun_preserving' (fun x => (y x).2) (by fun_prop)
    fun_prop
  adjoint φ ψ hφ hψ := by
    have := hF.test_fun_preserving _ hφ
    have := hG.test_fun_preserving _ hφ
    have := hF.test_fun_preserving' (fun y => (ψ y).1) (by fun_prop)
    have := hG.test_fun_preserving' (fun y => (ψ y).2) (by fun_prop)
    calc _ = (∫ (y : X), ⟪F φ y, (ψ y).1⟫_ℝ) + ∫ (y : X), ⟪G φ y, (ψ y).2⟫_ℝ := by
          simp only [prod_inner_apply']
          rw[integral_add]
          · apply IsTestFunction.integrable; fun_prop
          · apply IsTestFunction.integrable; fun_prop
        _ = (∫ (y : X), ⟪φ y, F' (fun y' => (ψ y').1) y⟫_ℝ) +
              (∫ (y : X), ⟪φ y, G' (fun y' => (ψ y').2) y⟫_ℝ) := by
          rw[hF.adjoint,hG.adjoint] <;> fun_prop
        _ = _ := by
          simp[inner_add_right']
          rw[integral_add]
          · apply IsTestFunction.integrable; fun_prop
          · apply IsTestFunction.integrable; fun_prop
  ext' := by
    intro K cK
    obtain ⟨A,cA,hF⟩ := hF.ext' K cK
    obtain ⟨B,cB,hG⟩ := hG.ext' K cK
    use A ∪ B
    constructor
    · exact cA.union cB
    · intro φ φ' h x hx; dsimp
      rw[hF,hG] <;> simp_all
  -- ext := IsLocalizedFunctionTransform.prod hF.ext hG.ext

lemma fst {F'} {F : (X → U) → (X → W×V)}
    (hF : HasVarAdjoint F F') :
    HasVarAdjoint
      (fun φ x => (F φ x).1)
      (fun φ x => F' (fun x' => (φ x', 0)) x) where
  test_fun_preserving _ hφ := by
    apply IsTestFunction.prod_fst
    exact hF.test_fun_preserving _ hφ
  test_fun_preserving' y hφ := by
    apply hF.test_fun_preserving'
    fun_prop
  adjoint φ ψ hφ hψ := by
    calc _ = ∫ (y : X), ⟪F φ y, (ψ y, 0)⟫_ℝ := by simp
        _ = ∫ (y : X), ⟪φ y, F' (fun y => (ψ y, 0)) y⟫_ℝ := hF.adjoint _ _ hφ (by fun_prop)
        _ = _ := by simp
  ext' := by
    intro K cK
    obtain ⟨A,cA,hF⟩ := hF.ext' K cK
    use A
    constructor
    · exact cA
    · intro φ φ' h x hx; dsimp
      rw[hF] <;> simp_all
  -- ext := IsLocalizedFunctionTransform.fst hF.ext

lemma snd {F'} {F : (X → U) → (X → W×V)}
    (hF : HasVarAdjoint F F') :
    HasVarAdjoint
      (fun φ x => (F φ x).2)
      (fun φ x => F' (fun x' => (0, φ x')) x) where
  test_fun_preserving _ hφ := by
    apply IsTestFunction.prod_snd
    exact hF.test_fun_preserving _ hφ
  test_fun_preserving' y hφ := by
    apply hF.test_fun_preserving' _
    fun_prop
  adjoint φ ψ hφ hψ := by
    calc _ = ∫ (y : X), ⟪F φ y, (0, ψ y)⟫_ℝ := by simp
        _ = ∫ (y : X), ⟪φ y, F' (fun y => (0, ψ y)) y⟫_ℝ := hF.adjoint _ _ hφ (by fun_prop)
        _ = _ := by simp
  ext' := by
    intro K cK
    obtain ⟨A,cA,hF⟩ := hF.ext' K cK
    use A
    constructor
    · exact cA
    · intro φ φ' h x hx; dsimp
      rw[hF] <;> simp_all
  -- ext := IsLocalizedFunctionTransform.snd hF.ext
