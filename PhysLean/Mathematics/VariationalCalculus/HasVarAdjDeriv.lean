/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
import PhysLean.Mathematics.VariationalCalculus.HasVarAdjoint
/-!
# Variational adjoint derivative

Variational adjoint derivative of `F` at `u` is a generalization of `(fderiv ℝ F u).adjoint`
to function spaces. In particular, variational gradient is an analog of
`gradient F u := (fderiv ℝ F u).adjoint 1`.

The definition of `HasVarAdjDerivAt` is constructed exactly such that we can prove composition
theorem saying
```
  HasVarAdjDerivAt F F' (G u)) → HasVarAdjDerivAt G G' u →
    HasVarAdjDerivAt (F ∘ G) (G' ∘ F') u
```
This theorem is the main tool to mechanistically compute variational gradient.
-/

open MeasureTheory ContDiff InnerProductSpace

variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasureSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasureSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasureSpace Z]
  {U} [NormedAddCommGroup U] [NormedSpace ℝ U] [InnerProductSpace' ℝ U]
  {V} [NormedAddCommGroup V] [NormedSpace ℝ V] [InnerProductSpace' ℝ V]
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [InnerProductSpace' ℝ W]

/-- This is analogue of saying `F' = (fderiv ℝ F u).adjoint`.

This definition is useful as we can prove composition theorem for it and `HasVarGradient F grad u`
can be computed by `grad := F' (fun _ => 1)`. -/
structure HasVarAdjDerivAt (F : (X → U) → (Y → V)) (F' : (Y → V) → (X → U)) (u : X → U) : Prop
    where
  smooth_at : ContDiff ℝ ∞ u
  diff : ∀ (φ : ℝ → X → U), ContDiff ℝ ∞ ↿φ →
    ContDiff ℝ ∞ (fun sx : ℝ×Y => F (φ sx.1) sx.2)
  linearize :
    ∀ (φ : ℝ → X → U), ContDiff ℝ ∞ ↿φ →
      ∀ x,
        deriv (fun s' : ℝ => F (φ s') x) 0
        =
        deriv (fun s' : ℝ => F (fun x => φ 0 x + s' • deriv (φ · x) 0) x) 0
  adjoint : HasVarAdjoint (fun δu x => deriv (fun s : ℝ => F (fun x' => u x' + s • δu x') x) 0) F'

namespace HasVarAdjDerivAt

variable {μ : Measure X}

lemma apply_smooth_of_smooth {F : (X → U) → (X → V)} {F' : (X → V) → (X → U)} {u v : X → U}
    (h : HasVarAdjDerivAt F F' u) (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ (F v) := by
  have h1 := h.diff (fun _ => v) (by fun_prop)
  simp at h1
  have hf : F v = (fun (sx : ℝ × X) => F v sx.2) ∘ fun x => (0, x) := by
    funext x
    simp
  rw [hf]
  apply ContDiff.comp h1
  fun_prop

lemma apply_smooth_self {F : (X → U) → (X → V)} {F' : (X → V) → (X → U)} {u : X → U}
    (h : HasVarAdjDerivAt F F' u) : ContDiff ℝ ∞ (F u) := by
  exact h.apply_smooth_of_smooth (h.smooth_at)

lemma smooth_R {F : (X → U) → (X → V)} {F' : (X → V) → (X → U)} {u : X → U}
    (h : HasVarAdjDerivAt F F' u) {φ : ℝ → X → U} (hφ : ContDiff ℝ ∞ ↿φ) (x : X) :
    ContDiff ℝ ∞ (fun s : ℝ => F (fun x' => φ s x') x) :=
  (h.diff (fun s x => φ s x) hφ).comp (by fun_prop : ContDiff ℝ ∞ fun s => (s,x))

lemma smooth_linear {F : (X → U) → (X → V)} {F' : (X → V) → (X → U)} {u : X → U}
    (h : HasVarAdjDerivAt F F' u) {φ : ℝ → X → U} (hφ : ContDiff ℝ ∞ ↿φ) :
    ContDiff ℝ ∞ (fun s' : ℝ => F (fun x => φ 0 x + s' • deriv (φ · x) 0) x) := by
  apply h.smooth_R (φ := (fun s' x => φ 0 x + s' • deriv (φ · x) 0))
  fun_prop [deriv]

lemma smooth_adjoint {F : (X → U) → (X → V)} {F' : (X → V) → (X → U)} {u : X → U}
    (h : HasVarAdjDerivAt F F' u) {δu : X → U} (h' : ContDiff ℝ ∞ δu) (x : X) :
    ContDiff (E:= ℝ) (F := V) ℝ ∞ ((fun s : ℝ => F (fun x' => u x' + s • δu x') x)) := by
  have h1 : ((fun s : ℝ => F (fun x' => u x' + s • δu x') x))
      = (fun sx : ℝ × X => F ((fun r x' => u x' + r • δu x') sx.1) sx.2) ∘ (·, x) := by
    funext x
    simp
  rw [h1]
  apply ContDiff.comp
  · apply h.diff (φ := (fun r x' => u x' + r • δu x'))
    have hx := h.smooth_at
    fun_prop
  · fun_prop

lemma differentiable_linear {F : (X → U) → (X → V)} {F' : (X → V) → (X → U)} {u : X → U}
    (h : HasVarAdjDerivAt F F' u) {φ : ℝ → X → U} (hφ : ContDiff ℝ ∞ ↿φ) (x : X) :
    Differentiable ℝ (fun s' : ℝ => F (fun x => φ 0 x + s' • deriv (φ · x) 0) x) := by
  exact fun x => (h.smooth_linear hφ).differentiable (by simp) x

omit [MeasureSpace X] [InnerProductSpace' ℝ U] [InnerProductSpace' ℝ V] in
lemma linearize_of_linear {F : (X → U) → (X → V)}
    (add : ∀ φ1 φ2 : X → U,
    ContDiff ℝ ∞ φ1 → ContDiff ℝ ∞ φ2 → F (φ1 + φ2) = F φ1 + F φ2)
    (smul : ∀ (c : ℝ) (φ : X → U), ContDiff ℝ ∞ φ → F (c • φ) = c • F φ)
    (deriv_comm : ∀ {φ : ℝ → X → U} (_ : ContDiff ℝ ∞ ↿φ) (x : X),
      deriv (fun s' => F (φ s') x) 0 = F (fun x' => deriv (fun x => φ x x') 0) x)
    {φ : ℝ → X → U}
    (hφ : ContDiff ℝ ∞ ↿φ) (x : X) :
    deriv (fun s' : ℝ => F (φ s') x) 0
    =
    deriv (fun s' : ℝ => F (fun x' => φ 0 x' + s' • deriv (φ · x') 0) x) 0 := by
  have h1 (s' : ℝ) : F (fun x' => φ 0 x' + s' • deriv (φ · x') 0) =
    F (fun x' => φ 0 x') + s' • F (fun x' => deriv (φ · x') 0) := by
    rw [← smul, ← add]
    rfl
    · fun_prop
    · apply ContDiff.smul
      fun_prop
      conv =>
        enter [3, x]
        rw [← fderiv_apply_one_eq_deriv]
      apply ContDiff.fderiv_apply (n := ∞) (m := ∞)
      fun_prop
      fun_prop
      fun_prop
      simp
    · conv =>
        enter [3, x]
        rw [← fderiv_apply_one_eq_deriv]
      apply ContDiff.fderiv_apply (n := ∞) (m := ∞)
      repeat fun_prop
      simp
  conv_rhs =>
    enter [1, s]
    rw [h1]
  simp only [Pi.add_apply, Pi.smul_apply, differentiableAt_const, differentiableAt_fun_id,
    DifferentiableAt.fun_smul, deriv_fun_add, deriv_const', zero_add]
  rw [deriv_smul_const]
  simp only [deriv_id'', one_smul]
  rw [deriv_comm hφ x]
  fun_prop

lemma deriv_adjoint_of_linear {F'} {F : (X → U) → (X → V)}
    (add : ∀ φ1 φ2 : X → U,
    ContDiff ℝ ∞ φ1 → ContDiff ℝ ∞ φ2 → F (φ1 + φ2) = F φ1 + F φ2)
    (smul : ∀ (c : ℝ) (φ : X → U), ContDiff ℝ ∞ φ → F (c • φ) = c • F φ)
    (u : X → U) (smooth : ContDiff ℝ ∞ u)
    (h : HasVarAdjoint F F') :
    HasVarAdjoint (fun δu x => deriv (fun s : ℝ => F (fun x' => u x' + s • δu x') x) 0) F' := by
  apply HasVarAdjoint.congr_fun h
  intro φ hφ
  funext x
  have h1 (s : ℝ) : F (fun x' => u x' + s • φ x')
    = F u + s • F φ := by
    rw [← smul, ← add]
    rfl
    · fun_prop
    · apply ContDiff.smul
      fun_prop
      exact IsTestFunction.contDiff hφ
    · exact IsTestFunction.contDiff hφ
  conv_lhs =>
    enter [1, s]
    rw [h1]
  simp only [Pi.add_apply, Pi.smul_apply, differentiableAt_const, differentiableAt_fun_id,
    DifferentiableAt.fun_smul, deriv_fun_add, deriv_const', zero_add]
  rw [deriv_smul_const]
  simp only [deriv_id'', one_smul]
  fun_prop

lemma hasVarAdjDerivAt_of_hasVarAdjoint_of_linear
    {F'} {F : (X → U) → (X → V)}
    (diff : ∀ (φ : ℝ → X → U), ContDiff ℝ ∞ ↿φ →
      ContDiff ℝ ∞ (fun sx : ℝ×X => F (φ sx.1) sx.2))

    (add : ∀ φ1 φ2 : X → U,
    ContDiff ℝ ∞ φ1 → ContDiff ℝ ∞ φ2 → F (φ1 + φ2) = F φ1 + F φ2)
    (smul : ∀ (c : ℝ) (φ : X → U), ContDiff ℝ ∞ φ → F (c • φ) = c • F φ)
    (deriv_comm : ∀ {φ : ℝ → X → U} (_ : ContDiff ℝ ∞ ↿φ) (x : X),
      deriv (fun s' => F (φ s') x) 0 = F (fun x' => deriv (fun x => φ x x') 0) x)
    (u : X → U) (smooth : ContDiff ℝ ∞ u)
    (h : HasVarAdjoint F F') :
    HasVarAdjDerivAt F F' u where
  smooth_at := smooth
  diff := diff
  linearize := fun _ a x => linearize_of_linear add smul deriv_comm a x
  adjoint := deriv_adjoint_of_linear add smul u smooth h

lemma id (u) (hu : ContDiff ℝ ∞ u) : HasVarAdjDerivAt (fun φ : X → U => φ) (fun ψ => ψ) u where
  smooth_at := hu
  diff := by intros; fun_prop
  linearize := by intro φ hφ x; simp [deriv_smul_const]
  adjoint := by simp [deriv_smul_const]; apply HasVarAdjoint.id

lemma const (u : X → U) (v : X → V) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    HasVarAdjDerivAt (fun _ : X → U => v) (fun _ => 0) u where

  smooth_at := hu
  diff := by intros; fun_prop
  linearize := by simp
  adjoint := by simp; exact HasVarAdjoint.zero

lemma comp {F : (Y → V) → (Z → W)} {G : (X → U) → (Y → V)} {u : X → U}
    {F' G'} (hF : HasVarAdjDerivAt F F' (G u)) (hG : HasVarAdjDerivAt G G' u) :
    HasVarAdjDerivAt (fun u => F (G u)) (fun ψ => G' (F' ψ)) u where
  smooth_at := hG.smooth_at
  diff := by
    intro φ hφ
    apply hF.diff (φ := fun t x => G (φ t) x)
    exact hG.diff φ hφ
  linearize := by
    intro φ hφ x
    rw[hF.linearize (fun t x => G (φ t) x) (hG.diff φ hφ)]
    rw[hF.linearize (fun s' => G fun x => φ 0 x + s' • deriv (fun x_1 => φ x_1 x) 0)]
    simp[hG.linearize φ hφ]
    eta_expand; simp[Function.HasUncurry.uncurry]
    apply hG.diff (φ := fun a x => φ 0 x + a • deriv (fun x_1 => φ x_1 x) 0)
    fun_prop [deriv]
  adjoint := by
    have : ContDiff ℝ ∞ u := hG.smooth_at
    have h := hF.adjoint.comp hG.adjoint
    apply h.congr_fun
    intro φ hφ; funext x
    rw[hF.linearize]
    · simp
    · simp [Function.HasUncurry.uncurry];
      apply hG.diff (φ := (fun s x => u x + s • φ x))
      fun_prop

lemma congr {F G : (X → U) → (Y → V)} {F' } {u : X → U}
    (hF : HasVarAdjDerivAt F F' u) (h : ∀ φ, ContDiff ℝ ∞ φ → F φ = G φ) :
    HasVarAdjDerivAt G F' u where
  smooth_at := hF.smooth_at
  diff := by
    intro φ hφ
    conv => enter [3, s]; rw [← h (φ s.1) (by fun_prop)]
    exact hF.diff φ hφ
  linearize := by
    intro φ hφ x
    convert hF.linearize φ hφ x using 1
    · congr
      funext s
      rw [h (φ s) (by fun_prop)]
    · congr
      funext s
      rw [h]
      apply ContDiff.add
      · fun_prop
      · apply ContDiff.smul
        fun_prop
        conv =>
          enter [3, x];
          rw [← fderiv_apply_one_eq_deriv]
          erw [fderiv_uncurry_comp_fst _ _ (hφ.differentiable (by simp))]
          simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_eq_smul_deriv,
            one_smul]
          rw [← fderiv_apply_one_eq_deriv]
          rw [DifferentiableAt.fderiv_prodMk (by fun_prop) (by fun_prop)]
        simp only [fderiv_id', fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.prod_apply,
          ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.zero_apply]
        fun_prop
  adjoint := by
    apply HasVarAdjoint.congr_fun hF.adjoint
    intro φ hφ
    funext x
    congr
    funext s
    rw [h]
    have : ContDiff ℝ ∞ u := hF.smooth_at
    fun_prop

lemma unique_on_test_functions
    [IsFiniteMeasureOnCompacts (@volume X _)] [(@volume X _).IsOpenPosMeasure]
    [OpensMeasurableSpace X]
    (F : (X → U) → (Y → V)) (u : X → U)
    (F' G') (hF : HasVarAdjDerivAt F F' u) (hG : HasVarAdjDerivAt F G' u)
    (φ : Y → V) (hφ : IsTestFunction φ) :
    F' φ = G' φ := HasVarAdjoint.unique_on_test_functions hF.adjoint hG.adjoint φ hφ

lemma unique {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [MeasureSpace X] [OpensMeasurableSpace X]
    [IsFiniteMeasureOnCompacts (@volume X _)] [(@volume X _).IsOpenPosMeasure]
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [FiniteDimensional ℝ Y] [MeasureSpace Y]
    {F : (X → U) → (Y → V)} {u : X → U}
    {F' G'} (hF : HasVarAdjDerivAt F F' u) (hG : HasVarAdjDerivAt F G' u)
    (φ : Y → V) (hφ : ContDiff ℝ ∞ φ) :
    F' φ = G' φ :=
  HasVarAdjoint.unique hF.adjoint hG.adjoint φ hφ

lemma prod [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts (volume (α := X))]
    {F : (X → U) → (X → V)} {G : (X → U) → (X → W)} {F' G'}
    (hF : HasVarAdjDerivAt F F' u) (hG : HasVarAdjDerivAt G G' u) :
    HasVarAdjDerivAt
      (fun φ x => (F φ x, G φ x))
      (fun φ x => F' (fun x' => (φ x').1) x + G' (fun x' => (φ x').2) x) u where
  smooth_at := hF.smooth_at
  diff := by
    intro φ hφ
    have hF' := hF.diff φ hφ
    have hG' := hG.diff φ hφ
    apply ContDiff.prodMk hF' hG'
  linearize := by
    intro φ hφ x
    rw [@Prod.eq_iff_fst_eq_snd_eq]
    constructor
    · rw [← fderiv_apply_one_eq_deriv, ← fderiv_apply_one_eq_deriv, DifferentiableAt.fderiv_prodMk,
        DifferentiableAt.fderiv_prodMk]
      simp only [ContinuousLinearMap.prod_apply, fderiv_eq_smul_deriv, one_smul]
      rw [hF.linearize]
      · exact hφ
      · apply ContDiff.differentiable (n := ∞) _ (by simp)
        apply hF.smooth_R _ x
        conv => enter [3, 1, x, y]; rw [← fderiv_apply_one_eq_deriv]
        fun_prop
      · apply ContDiff.differentiable (n := ∞) _ (by simp)
        apply hG.smooth_R _ x
        conv => enter [3, 1, x, y]; rw [← fderiv_apply_one_eq_deriv]
        fun_prop
      · apply ContDiff.differentiable (n := ∞) _ (by simp)
        exact smooth_R hF hφ x
      · apply ContDiff.differentiable (n := ∞) _ (by simp)
        exact smooth_R hG hφ x
    · rw [← fderiv_apply_one_eq_deriv, ← fderiv_apply_one_eq_deriv, DifferentiableAt.fderiv_prodMk,
        DifferentiableAt.fderiv_prodMk]
      simp only [ContinuousLinearMap.prod_apply, fderiv_eq_smul_deriv, one_smul]
      rw [hG.linearize]
      · exact hφ
      · apply ContDiff.differentiable (n := ∞) _ (by simp)
        exact hF.smooth_linear hφ
      · apply ContDiff.differentiable (n := ∞) _ (by simp)
        exact hG.smooth_linear hφ
      · apply ContDiff.differentiable (n := ∞) _ (by simp)
        exact smooth_R hF hφ x
      · apply ContDiff.differentiable (n := ∞) _ (by simp)
        exact smooth_R hG hφ x
  adjoint := by
    apply HasVarAdjoint.congr_fun
      (G := fun δu x => (deriv (fun s => F (fun x' => u x' + s • δu x') x) (0 : ℝ),
        deriv (fun s => G (fun x' => u x' + s • δu x') x) (0 : ℝ)))
    apply HasVarAdjoint.prod
    · exact hF.adjoint
    · exact hG.adjoint
    intro φ hφ
    funext x
    rw [← fderiv_apply_one_eq_deriv, ← fderiv_apply_one_eq_deriv, DifferentiableAt.fderiv_prodMk]
    simp only [ContinuousLinearMap.prod_apply, fderiv_eq_smul_deriv, one_smul]
    · apply ContDiff.differentiable (n := ∞) _ (by simp)
      apply hF.smooth_adjoint
      exact hφ.contDiff
    · apply ContDiff.differentiable (n := ∞) _ (by simp)
      apply hG.smooth_adjoint
      exact IsTestFunction.contDiff hφ

lemma fst {F : (X → U) → (X → W×V)}
    (hF : HasVarAdjDerivAt F F' u) :
    HasVarAdjDerivAt
      (fun φ x => (F φ x).1)
      (fun φ x => F' (fun x' => (φ x', 0)) x) u where
  smooth_at := hF.smooth_at
  diff := fun φ _ => ContDiff.comp contDiff_fst (hF.diff φ (by fun_prop))
  linearize := by
    intro φ hφ x
    have h1 := hF.linearize φ hφ x
    rw [← fderiv_apply_one_eq_deriv, fderiv_comp']
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_eq_smul_deriv, one_smul]
    rw [h1, fderiv_fst]
    simp only [ContinuousLinearMap.coe_fst']
    conv_rhs =>
      rw [← fderiv_apply_one_eq_deriv]
    rw [fderiv_comp' _ (by fun_prop)]
    simp [fderiv_fst]
    · apply ContDiff.differentiable (n := ∞) (hF.smooth_linear hφ) (by simp)
    · fun_prop
    · apply ContDiff.differentiable (n := ∞) (hF.smooth_R hφ x) (by simp)
  adjoint := by
    apply HasVarAdjoint.congr_fun
      (G := (fun δu x => (deriv (fun s => (F (fun x' => u x' + s • δu x') x)) (0 :ℝ)).1))
    · exact HasVarAdjoint.fst hF.adjoint
    · intro φ hφ
      funext x
      rw [← fderiv_apply_one_eq_deriv, fderiv_comp', fderiv_fst]
      simp only [ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_fst', Function.comp_apply,
        fderiv_eq_smul_deriv, one_smul]
      fun_prop
      · apply ContDiff.differentiable (n := ∞) _ (by simp)
        apply hF.smooth_adjoint
        exact IsTestFunction.contDiff hφ

lemma snd {F : (X → U) → (X → W×V)}
    (hF : HasVarAdjDerivAt F F' u) :
    HasVarAdjDerivAt
      (fun φ x => (F φ x).2)
      (fun φ x => F' (fun x' => (0, φ x')) x) u where
  smooth_at := hF.smooth_at
  diff := fun φ _ => ContDiff.comp contDiff_snd (hF.diff φ (by fun_prop))
  linearize := by
    intro φ hφ x
    have h1 := hF.linearize φ hφ x
    rw [← fderiv_apply_one_eq_deriv, fderiv_comp']
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_eq_smul_deriv, one_smul]
    rw [h1, fderiv_snd]
    simp only [ContinuousLinearMap.coe_snd']
    conv_rhs =>
      rw [← fderiv_apply_one_eq_deriv]
    rw [fderiv_comp' _ (by fun_prop)]
    simp [fderiv_snd]
    · apply ContDiff.differentiable (n := ∞) (hF.smooth_linear hφ) (by simp)
    · fun_prop
    · apply ContDiff.differentiable (n := ∞) (hF.smooth_R hφ x) (by simp)
  adjoint := by
    apply HasVarAdjoint.congr_fun
      (G := (fun δu x => (deriv (fun s => (F (fun x' => u x' + s • δu x') x)) (0 :ℝ)).2))
    · exact HasVarAdjoint.snd hF.adjoint
    · intro φ hφ
      funext x
      rw [← fderiv_apply_one_eq_deriv, fderiv_comp', fderiv_snd]
      simp only [ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_snd', Function.comp_apply,
        fderiv_eq_smul_deriv, one_smul]
      fun_prop
      · apply ContDiff.differentiable (n := ∞) _ (by simp)
        apply hF.smooth_adjoint
        exact IsTestFunction.contDiff hφ

lemma deriv' (u : ℝ → U) (hu : ContDiff ℝ ∞ u) :
    HasVarAdjDerivAt (fun φ : ℝ → U => deriv φ) (fun φ x => - deriv φ x) u where
  smooth_at := hu
  diff := by intros; fun_prop [deriv]
  linearize := by
    intro φ hφ x
    conv_rhs =>
      enter [1, s']
      rw [deriv_fun_add (by
        apply function_differentiableAt_snd
        exact hφ.differentiable (by simp)) (by
        apply Differentiable.const_smul
        conv =>
          enter [2, x]
          rw [← fderiv_apply_one_eq_deriv]
        apply fderiv_uncurry_differentiable_fst_comp_snd_apply
        exact hφ.of_le ENat.LEInfty.out)]
      rw [deriv_fun_const_smul _ (by
        conv =>
          enter [2, x]
          rw [← fderiv_apply_one_eq_deriv]
        apply Differentiable.differentiableAt
        apply fderiv_uncurry_differentiable_fst_comp_snd_apply
        exact hφ.of_le ENat.LEInfty.out)]
    simp only [differentiableAt_const, differentiableAt_fun_id, DifferentiableAt.fun_smul,
      deriv_fun_add, deriv_const', zero_add]
    rw [deriv_smul_const]
    simp only [deriv_id'', one_smul]
    rw [← fderiv_apply_one_eq_deriv]
    conv_lhs =>
      enter [1, 2, s]
      rw [← fderiv_apply_one_eq_deriv]
    rw [fderiv_swap]
    simp only [fderiv_eq_smul_deriv, one_smul]
    · apply ContDiff.of_le hφ
      exact ENat.LEInfty.out
    · exact differentiableAt_id
  adjoint := by
    apply HasVarAdjoint.congr_fun (G := (fun δu x => deriv (fun x' => δu x') x))
    · exact HasVarAdjoint.deriv
    · intro φ hφ
      funext x
      have := hφ.smooth.differentiable (by simp)
      have := hu.differentiable (by simp)
      simp (disch:=fun_prop)
      conv_lhs =>
        enter [1, x]
        rw [deriv_fun_const_smul _ (by fun_prop)]
      rw [deriv_smul_const]
      simp only [deriv_id'', one_smul]
      fun_prop

protected lemma deriv (F : (ℝ → U) → (ℝ → V)) (F') (u) (hF : HasVarAdjDerivAt F F' u) :
    HasVarAdjDerivAt (fun φ : ℝ → U => deriv (F φ))
    (fun ψ x => F' (fun x' => - deriv ψ x') x) u :=
  comp (F:=deriv) (G:=F) (hF := deriv' (F u) hF.apply_smooth_self) (hG := hF)

lemma fmap
    {U} [NormedAddCommGroup U] [NormedSpace ℝ U] [InnerProductSpace' ℝ U]
    {V} [NormedAddCommGroup V] [NormedSpace ℝ V] [InnerProductSpace' ℝ V]
    [CompleteSpace U] [CompleteSpace V]
    (f : X → U → V) {f' : X → U → _ }
    (u : X → U) (hu : ContDiff ℝ ∞ u)
    (hf' : ContDiff ℝ ∞ ↿f) (hf : ∀ x u, HasAdjFDerivAt ℝ (f x) (f' x u) u) :
    HasVarAdjDerivAt (fun (φ : X → U) x => f x (φ x)) (fun ψ x => f' x (u x) (ψ x)) u where
  smooth_at := hu
  diff := by fun_prop
  linearize := by
    intro φ hφ x
    unfold deriv
    conv => lhs; rw[fderiv_comp' (𝕜:=ℝ) (g:=(fun u : U => f _ u)) _
            (by fun_prop (config:={maxTransitionDepth:=3}) (disch:=aesop))
            (by fun_prop (config:={maxTransitionDepth:=3}) (disch:=aesop))]
    conv => rhs; rw[fderiv_comp' (𝕜:=ℝ) (g:=(fun u : U => f _ u)) _
            (by fun_prop (config:={maxTransitionDepth:=3}) (disch:=aesop)) (by fun_prop)]
    simp [deriv_fun_smul]
  adjoint := by
    apply HasVarAdjoint.congr_fun
    case h' =>
      intro φ hφ; funext x
      unfold deriv
      conv =>
        lhs
        rw[fderiv_comp' (𝕜:=ℝ) (g:=_) (f:=fun s : ℝ => u x + s • φ x) _
          (by fun_prop (config:={maxTransitionDepth:=3}) (disch:=aesop)) (by fun_prop)]
        simp[deriv_fun_smul]
    case h =>
      constructor
      · intros;
        constructor
        · fun_prop
        · expose_names
          rw [← exists_compact_iff_hasCompactSupport]
          have h1 := h.supp
          rw [← exists_compact_iff_hasCompactSupport] at h1
          obtain ⟨K, cK, hK⟩ := h1
          refine ⟨K, cK, ?_⟩
          intro x hx
          rw [hK x hx]
          simp
      · intro φ hφ
        constructor
        · apply ContDiff.fun_comp
            (g:= fun x : X×U×V => f' x.1 x.2.1 x.2.2)
            (f:= fun x => (x, u x, φ x))
          · apply HasAdjFDerivAt.contDiffAt_deriv <;> assumption
          · fun_prop
        · rw [← exists_compact_iff_hasCompactSupport]
          have h1 := hφ.supp
          rw [← exists_compact_iff_hasCompactSupport] at h1
          obtain ⟨K, cK, hK⟩ := h1
          refine ⟨K, cK, ?_⟩
          intro x hx
          rw [hK x hx]
          have hfx := (hf x (u x)).hasAdjoint_fderiv
          exact HasAdjoint.adjoint_apply_zero hfx
      · intros
        congr 1; funext x
        rw[← PreInnerProductSpace.Core.conj_inner_symm]
        rw[← (hf x (u x)).hasAdjoint_fderiv.adjoint_inner_left]
        rw[PreInnerProductSpace.Core.conj_inner_symm]
      · intros K cK; use K; simp_all

lemma neg (F : (X → U) → (X → V)) (F') (u) (hF : HasVarAdjDerivAt F F' u) :
    HasVarAdjDerivAt (fun φ x => -F φ x) (fun ψ x => - F' ψ x) u where
  smooth_at := hF.smooth_at
  diff := by intro φ hφ; apply ContDiff.neg; apply hF.diff; assumption
  linearize := by
    intros
    rw[deriv.fun_neg]
    simp only [deriv.fun_neg, neg_inj]
    rw[hF.linearize]
    assumption
  adjoint := by
    apply HasVarAdjoint.congr_fun
    case h' =>
      intro φ hφ; funext x
      have := hφ.smooth; have := hF.smooth_at
      conv =>
        lhs
        rw[deriv.fun_neg]
        simp [hF.linearize (fun s x' => u x' + s • φ x') (by fun_prop)]
        simp[deriv_smul_const]
    case h =>
      apply HasVarAdjoint.neg
      apply hF.adjoint

section OnFiniteMeasures

variable [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts (@volume X _)]

lemma add
    (F G : (X → U) → (X → V)) (F' G') (u)
    (hF : HasVarAdjDerivAt F F' u) (hG : HasVarAdjDerivAt G G' u) :
    HasVarAdjDerivAt (fun φ x => F φ x + G φ x) (fun ψ x => F' ψ x + G' ψ x) u where
  smooth_at := hF.smooth_at
  diff := by
    intro φ hφ
    apply ContDiff.add
    · apply hF.diff; assumption
    · apply hG.diff; assumption
  linearize := by
    intro φ hφ x; rw[deriv_fun_add]; rw[deriv_fun_add]; rw[hF.linearize _ hφ, hG.linearize _ hφ]
    · exact hF.differentiable_linear hφ x 0
    · exact hG.differentiable_linear hφ x 0
    · change DifferentiableAt ℝ ((fun sx : ℝ × X => F (φ sx.1) sx.2) ∘ fun s' => (s', x)) 0
      apply DifferentiableAt.comp
      · have hf := hF.diff φ hφ
        apply ContDiff.differentiable hf (by simp)
      · fun_prop
    · change DifferentiableAt ℝ ((fun sx : ℝ × X => G (φ sx.1) sx.2) ∘ fun s' => (s', x)) 0
      apply DifferentiableAt.comp
      · have hg := hG.diff φ hφ
        apply ContDiff.differentiable hg (by simp)
      · fun_prop
  adjoint := by
    apply HasVarAdjoint.congr_fun
    case h' =>
      intro φ hφ; funext x
      have := hφ.smooth; have := hF.smooth_at
      have h1 : DifferentiableAt ℝ (fun s => F (fun x' => u x' + s • φ x') x) (0 : ℝ) :=
        (hF.smooth_R (φ:=fun s x' => u x' + s • φ x') (by fun_prop) x)
          |>.differentiable (by simp) 0
      have h2 : DifferentiableAt ℝ (fun s => G (fun x' => u x' + s • φ x') x) (0 : ℝ) :=
        (hG.smooth_R (φ:=fun s x' => u x' + s • φ x') (by fun_prop) x)
          |>.differentiable (by simp) 0
      conv =>
        lhs
        rw[deriv_fun_add h1 h2]
        simp [hF.linearize (fun s x' => u x' + s • φ x') (by fun_prop)]
        simp [hG.linearize (fun s x' => u x' + s • φ x') (by fun_prop)]
        simp[deriv_smul_const]
    case h =>
      apply HasVarAdjoint.add
      apply hF.adjoint
      apply hG.adjoint

lemma sum {ι : Type} [Fintype ι]
    (F : ι → (X → U) → (X → V)) (F' : ι → (X → V) → X → U) (u)
    (hu : ContDiff ℝ ∞ u)
    (hF : ∀ i, HasVarAdjDerivAt (F i) (F' i) u) :
    HasVarAdjDerivAt (fun φ x => ∑ i, F i φ x) (fun ψ x => ∑ i, F' i ψ x) u := by
  let P (ι : Type) [Fintype ι] : Prop :=
    ∀ (F : ι → (X → U) → (X → V)), ∀ (F' : ι → (X → V) → X → U), ∀ u, ∀ (hu : ContDiff ℝ ∞ u),
    ∀ (hF : ∀ i, HasVarAdjDerivAt (F i) (F' i) u),
    HasVarAdjDerivAt (fun φ x => ∑ i, F i φ x) (fun ψ x => ∑ i, F' i ψ x) u
  have hp : P ι := by
    apply Fintype.induction_empty_option
    · intro ι ι' inst e hp F F' u hu ih
      convert hp (fun i => F (e i)) (fun i => F' (e i)) u hu (by
        intro i
        simpa using ih (e i))
      rw [← @e.sum_comp]
      rw [← @e.sum_comp]
    · intro i ι' u hu ih
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      apply HasVarAdjDerivAt.const
      fun_prop
      fun_prop
    · intro i ι' hp F F' u hu ih
      simp only [Fintype.sum_option]
      apply HasVarAdjDerivAt.add
      exact ih none
      exact hp (fun i_1 => F (some i_1)) (fun i_1 => F' (some i_1)) u hu fun i_1 => ih (some i_1)
  exact hp F F' u hu hF

lemma mul
    (F G : (X → U) → (X → ℝ)) (F' G') (u)
    (hF : HasVarAdjDerivAt F F' u) (hG : HasVarAdjDerivAt G G' u) :
    HasVarAdjDerivAt (fun φ x => F φ x * G φ x)
      (fun ψ x => F' (fun x' => ψ x' * G u x') x + G' (fun x' => F u x' * ψ x') x) u where
  smooth_at := hF.smooth_at
  diff := by
    intro φ hφ
    apply ContDiff.mul
    · apply hF.diff; assumption
    · apply hG.diff; assumption
  linearize := by
    intro φ hφ x
    rw [deriv_fun_mul, deriv_fun_mul]
    rw [hF.linearize _ hφ, hG.linearize _ hφ]
    · simp
    · exact hF.differentiable_linear hφ x 0
    · exact hG.differentiable_linear hφ x 0
    · change DifferentiableAt ℝ ((fun sx : ℝ × X => F (φ sx.1) sx.2) ∘ fun s' => (s', x)) 0
      apply DifferentiableAt.comp
      · have hf := hF.diff φ hφ
        apply ContDiff.differentiable hf (by simp)
      · fun_prop
    · change DifferentiableAt ℝ ((fun sx : ℝ × X => G (φ sx.1) sx.2) ∘ fun s' => (s', x)) 0
      apply DifferentiableAt.comp
      · have hg := hG.diff φ hφ
        apply ContDiff.differentiable hg (by simp)
      · fun_prop
  adjoint := by
    apply HasVarAdjoint.congr_fun
    case h' =>
      intro φ hφ; funext x
      have := hφ.smooth; have := hF.smooth_at
      -- Same two results as the `add` case
      have h1 : DifferentiableAt ℝ (fun s => F (fun x' => u x' + s • φ x') x) (0 : ℝ) :=
        (hF.smooth_R (φ:=fun s x' => u x' + s • φ x') (by fun_prop) x)
          |>.differentiable (by simp) 0
      have h2 : DifferentiableAt ℝ (fun s => G (fun x' => u x' + s • φ x') x) (0 : ℝ) :=
        (hG.smooth_R (φ:=fun s x' => u x' + s • φ x') (by fun_prop) x)
          |>.differentiable (by simp) 0
      conv =>
        lhs
        rw[deriv_fun_mul h1 h2]
        simp [hF.linearize (fun s x' => u x' + s • φ x') (by fun_prop)]
        simp [hG.linearize (fun s x' => u x' + s • φ x') (by fun_prop)]
    case h =>
      apply HasVarAdjoint.add
      · apply HasVarAdjoint.mul_right
        · convert hF.adjoint
          rw [deriv_smul_const, deriv_id'', one_smul]
          fun_prop
        · exact apply_smooth_self hG
      · apply HasVarAdjoint.mul_left
        · convert hG.adjoint
          rw [deriv_smul_const, deriv_id'', one_smul]
          fun_prop
        · exact apply_smooth_self hF

lemma const_mul
    (F : (X → U) → (X → ℝ)) (F') (u)
    (hF : HasVarAdjDerivAt F F' u) (c : ℝ) :
    HasVarAdjDerivAt (fun φ x => c * F φ x) (fun ψ x => F' (fun x' => c * ψ x') x) u := by
  have h1 : HasVarAdjDerivAt (fun φ x => c) (fun x => 0) u := {
    smooth_at := hF.smooth_at
    diff := by intros; fun_prop
    linearize := by simp
    adjoint := {
      test_fun_preserving _ hφ := by simp; exact IsTestFunction.zero (U := ℝ) (X := X)
      test_fun_preserving' _ hφ := by exact IsTestFunction.zero (U := U) (X := X)
      adjoint _ _ _ _ := by simp
      ext' := fun K cK => ⟨∅,isCompact_empty,fun _ _ h _ _ => rfl⟩
    }
  }
  convert mul (fun φ x => c) F (fun _ => 0) F' u h1 hF
  simp

lemma fun_mul {f : X → ℝ} (hf : ContDiff ℝ ∞ f)
    (F : (X → U) → (X → ℝ)) (F') (u)
    (hF : HasVarAdjDerivAt F F' u) :
    HasVarAdjDerivAt (fun φ x => f x * F φ x) (fun ψ x => F' (fun x' => f x' * ψ x') x) u := by
  have h1 : HasVarAdjDerivAt (fun φ x => f x) (fun ψ x => 0) u := {
    smooth_at := hF.smooth_at
    diff := by intros; fun_prop
    linearize := by simp
    adjoint := {
      test_fun_preserving _ hφ := by simp; exact IsTestFunction.zero (U := ℝ) (X := X)
      test_fun_preserving' _ hφ := by exact IsTestFunction.zero
      adjoint _ _ _ _ := by simp
      ext' := fun K cK => ⟨∅,isCompact_empty,fun _ _ h _ _ => rfl⟩
    }
  }
  convert mul (fun φ x => f x) F (fun _ => 0) F' u h1 hF
  simp

omit [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts (@volume X _)] in
protected lemma fderiv (u : X → U) (dx : X) (hu : ContDiff ℝ ∞ u)
    [ProperSpace X] [BorelSpace X]
    [FiniteDimensional ℝ X] [(@volume X _).IsAddHaarMeasure]:
    HasVarAdjDerivAt
      (fun (φ : X → U) x => fderiv ℝ φ x dx)
      (fun ψ x => - fderiv ℝ ψ x dx) u := by
  apply hasVarAdjDerivAt_of_hasVarAdjoint_of_linear
  · intros; fun_prop [fderiv]
  · intro φ1 φ2 h1 h2
    funext x
    simp only [Pi.add_apply]
    erw [fderiv_add]
    simp only [ContinuousLinearMap.add_apply]
    · exact (h1.differentiable (by simp)).differentiableAt
    · exact (h2.differentiable (by simp)).differentiableAt
  · intro c φ hφ
    funext x
    simp only [Pi.smul_apply]
    erw [fderiv_const_smul]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply]
    exact (hφ.differentiable (by simp)).differentiableAt
  · intro φ hφ x
    rw [← fderiv_apply_one_eq_deriv]
    rw [fderiv_swap]
    simp only [fderiv_eq_smul_deriv, one_smul]
    · apply ContDiff.of_le hφ
      exact ENat.LEInfty.out
  · exact hu
  · exact HasVarAdjoint.fderiv_apply

omit [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts (@volume X _)] in
protected lemma fderiv' (F : (X → U) → (X → V)) (F') (u) (dx : X)
    (hF : HasVarAdjDerivAt F F' u)[ProperSpace X] [BorelSpace X]
    [FiniteDimensional ℝ X] [(@volume X _).IsAddHaarMeasure] :
    HasVarAdjDerivAt (fun φ : X → U => fun x => fderiv ℝ (F φ) x dx)
    (fun ψ x => F' (fun x' => - fderiv ℝ ψ x' dx) x) u := by
  have hG := HasVarAdjDerivAt.fderiv (F u) dx (hF.apply_smooth_self)
  exact comp hG hF

protected lemma gradient {d} (u : Space d → ℝ) (hu : ContDiff ℝ ∞ u) :
    HasVarAdjDerivAt
      (fun (φ : Space d → ℝ) x => gradient φ x)
      (fun ψ x => - Space.div (Space.basis.repr ∘ ψ) x) u := by
  apply hasVarAdjDerivAt_of_hasVarAdjoint_of_linear
  · intro φ hφ
    simp [Space.gradient_eq_sum]
    apply ContDiff.sum
    intro i _
    simp only [Space.deriv]
    fun_prop
  · intro φ1 φ2 h1 h2
    rw [Space.gradient_eq_grad]
    rw [Space.grad_add, Space.grad_eq_gradiant, Space.grad_eq_gradiant]
    simp
    rfl
    · exact h1.differentiable (by simp)
    · exact h2.differentiable (by simp)
  · intro c φ hφ
    rw [Space.gradient_eq_grad]
    rw [Space.grad_smul, Space.grad_eq_gradiant]
    simp
    rfl
    exact hφ.differentiable (by simp)
  · intro φ hφ x
    rw [Space.gradient_eq_sum]
    conv_lhs => enter [1, x]; rw [Space.gradient_eq_sum]
    rw [deriv_fun_sum]
    congr
    funext i
    rw [deriv_smul_const]
    congr
    simp [Space.deriv]
    rw [← fderiv_apply_one_eq_deriv]
    rw [fderiv_swap]
    simp only [fderiv_eq_smul_deriv, smul_eq_mul, one_mul]
    · apply ContDiff.of_le hφ
      exact ENat.LEInfty.out
    · simp [Space.deriv]
      apply Differentiable.differentiableAt
      apply fderiv_uncurry_differentiable_snd_comp_fst_apply
      exact hφ.of_le ENat.LEInfty.out
    · intro i _
      apply Differentiable.differentiableAt
      apply Differentiable.smul_const
      simp [Space.deriv]
      apply fderiv_uncurry_differentiable_snd_comp_fst_apply
      exact hφ.of_le ENat.LEInfty.out
  · exact hu
  · exact HasVarAdjoint.gradient

protected lemma grad {d} (u : Space d → ℝ) (hu : ContDiff ℝ ∞ u) :
    HasVarAdjDerivAt
      (fun (φ : Space d → ℝ) x => Space.grad φ x)
      (fun ψ x => - Space.div ψ x) u := by
  apply hasVarAdjDerivAt_of_hasVarAdjoint_of_linear
  · intro φ hφ
    simp [Space.grad_eq_sum]
    apply ContDiff.sum
    intro i _
    simp only [Space.deriv]
    fun_prop
  · intro φ1 φ2 h1 h2
    rw [Space.grad_add]
    · exact h1.differentiable (by simp)
    · exact h2.differentiable (by simp)
  · intro c φ hφ
    rw [Space.grad_smul]
    exact hφ.differentiable (by simp)
  · intro φ hφ x
    rw [Space.grad_eq_sum]
    conv_lhs => enter [1, x]; rw [Space.grad_eq_sum]
    rw [deriv_fun_sum]
    congr
    funext i
    rw [deriv_smul_const]
    congr
    simp [Space.deriv]
    rw [← fderiv_apply_one_eq_deriv]
    rw [fderiv_swap]
    simp only [fderiv_eq_smul_deriv, smul_eq_mul, one_mul]
    · apply ContDiff.of_le hφ
      exact ENat.LEInfty.out
    · simp [Space.deriv]
      apply Differentiable.differentiableAt
      apply fderiv_uncurry_differentiable_snd_comp_fst_apply
      exact hφ.of_le ENat.LEInfty.out
    · intro i _
      apply Differentiable.differentiableAt
      apply Differentiable.smul_const
      simp [Space.deriv]
      apply fderiv_uncurry_differentiable_snd_comp_fst_apply
      exact hφ.of_le ENat.LEInfty.out
  · exact hu
  · exact HasVarAdjoint.grad
lemma div {d} (u : Space d → EuclideanSpace ℝ (Fin d)) (hu : ContDiff ℝ ∞ u) :
    HasVarAdjDerivAt
      (fun (φ : Space d → EuclideanSpace ℝ (Fin d)) x => Space.div φ x)
      (fun ψ x => - Space.grad ψ x) u := by
  apply hasVarAdjDerivAt_of_hasVarAdjoint_of_linear
  · intro φ hφ
    simp [Space.div]
    apply ContDiff.sum
    intro i _
    simp_rw [Space.deriv]
    fun_prop
  · intro φ1 φ2 h1 h2
    apply Space.div_add
    · exact h1.differentiable (by simp)
    · exact h2.differentiable (by simp)
  · intro c φ hφ
    apply Space.div_smul
    exact hφ.differentiable (by simp)
  · intro φ hφ x
    simp [Space.div]
    rw [deriv_fun_sum]
    congr
    funext i
    simp [Space.deriv]
    rw [← fderiv_apply_one_eq_deriv]
    rw [fderiv_swap]
    simp only [fderiv_eq_smul_deriv, smul_eq_mul, one_mul]
    congr
    funext y
    trans deriv (EuclideanSpace.proj i ∘ fun x' => (φ x' y)) 0
    rfl
    rw [← fderiv_apply_one_eq_deriv, fderiv_comp]
    simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp', Function.comp_apply,
      PiLp.proj_apply]
    rfl
    · fun_prop
    · apply function_differentiableAt_fst
      exact hφ.differentiable (by simp)
    · apply ContDiff.comp (g := EuclideanSpace.proj i)
      · change ContDiff ℝ 2 (EuclideanSpace.proj i)
        fun_prop
      · apply ContDiff.of_le hφ
        exact ENat.LEInfty.out
    · intro i _
      apply Differentiable.differentiableAt
      simp [Space.deriv]
      have h1 (s' : ℝ) : (fderiv ℝ (fun x => EuclideanSpace.proj i (φ s' x)) x) =
          EuclideanSpace.proj i ∘L (fderiv ℝ (fun x' => φ s' x') x) := by
        trans (fderiv ℝ (fun x => EuclideanSpace.proj i (φ s' x)) x)
        rfl
        rw [fderiv_comp']
        simp only [ContinuousLinearMap.fderiv]
        fun_prop
        apply function_differentiableAt_snd
        exact hφ.differentiable (by simp)
      conv =>
        enter [2, s]
        erw [h1]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
      apply Differentiable.comp
      · fun_prop
      apply fderiv_uncurry_differentiable_snd_comp_fst_apply
      exact hφ.of_le ENat.LEInfty.out
  · exact hu
  · exact HasVarAdjoint.div
