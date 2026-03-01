/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Mathlib.Analysis.InnerProductSpace.Trace
import PhysLean.Mathematics.Calculus.AdjFDeriv
import PhysLean.SpaceAndTime.TimeAndSpace.Basic
/-!

# Divergence

In this module we define and create an API around the divergence of a map `f : E → E`
where `E` is a normed space over a field `𝕜`.

-/
noncomputable section
open Module
open scoped InnerProductSpace

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜) in
/-- The divergence of a map `f : E → E` where `E` is a normed space over `𝕜`. -/
noncomputable def divergence (f : E → E) (x : E) : 𝕜 := (fderiv 𝕜 f x).toLinearMap.trace _ _

@[simp]
lemma divergence_zero : divergence 𝕜 (fun _ : E => 0) = fun _ => 0 := by
  unfold divergence
  simp

lemma divergence_eq_sum_fderiv {s : Finset E} (b : Basis s 𝕜 E) {f : E → E} :
    divergence 𝕜 f = fun x => ∑ i : s, b.repr (fderiv 𝕜 f x (b i)) i := by
  funext x
  unfold divergence
  rw[LinearMap.trace_eq_matrix_trace_of_finset (s:=s) _ b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  rfl

lemma divergence_eq_sum_fderiv' {ι} [Fintype ι] (b : Basis ι 𝕜 E) {f : E → E} :
    divergence 𝕜 f = fun x => ∑ i, b.repr (fderiv 𝕜 f x (b i)) i := by
  let s : Finset E := Finset.univ.map ⟨b, Basis.injective b⟩
  let f' : ι → s := fun i => ⟨b i, by simp [s]⟩
  have h : Function.Injective f' := by
    intro i j h
    simp [f'] at h
    exact Basis.injective b h
  have h' : Function.Surjective f' := by
    intro ⟨x, hx⟩
    simp [s] at hx
    obtain ⟨i, rfl⟩ := hx
    simp [f']
  let e : ι ≃ s := Equiv.ofBijective f' ⟨h, h'⟩
  let b' : Basis s 𝕜 E := b.reindex e
  rw [divergence_eq_sum_fderiv b']
  ext x
  rw [← e.symm.sum_comp]
  simp [b']

lemma divergence_eq_space_div {d} (f : Space d → Space d)
    (h : Differentiable ℝ f) : divergence ℝ f = Space.div (Space.basis.repr ∘ f) := by
  let b := (Space.basis (d:=d)).toBasis
  rw[divergence_eq_sum_fderiv' b]
  funext x
  simp +zetaDelta only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
    Space.basis_repr_apply, Space.div, Space.deriv, Function.comp_apply]
  congr
  funext i
  have h1 : (fderiv ℝ (fun x => f x i) x)
    = fderiv ℝ (Space.coordCLM i ∘ f) x := by
    congr
    ext j
    simp only [Function.comp_apply]
    rw [Space.coordCLM_apply, Space.coord_apply]
  rw [h1]
  rw [fderiv_comp]
  simp [Space.coordCLM_apply, Space.coord_apply]
  · fun_prop
  · exact h x

lemma divergence_prodMk [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    {f : E×F → E} {g : E×F → F} {xy : E×F}
    (hf : DifferentiableAt 𝕜 f xy) (hg : DifferentiableAt 𝕜 g xy) :
    divergence 𝕜 (fun xy : E×F => (f xy, g xy)) xy
    =
    divergence 𝕜 (fun x' => f (x',xy.2)) xy.1
    +
    divergence 𝕜 (fun y' => g (xy.1,y')) xy.2 := by
  obtain ⟨s, ⟨bX⟩⟩ := Basis.exists_basis 𝕜 E
  haveI : Fintype s := FiniteDimensional.fintypeBasisIndex bX
  obtain ⟨sY, ⟨bY⟩⟩ := Basis.exists_basis 𝕜 F
  haveI : Fintype sY := FiniteDimensional.fintypeBasisIndex bY
  let bXY := bX.prod bY
  rw[divergence_eq_sum_fderiv' bX]
  rw[divergence_eq_sum_fderiv' bY]
  rw[divergence_eq_sum_fderiv' bXY]
  simp[hf.fderiv_prodMk hg,bXY,fderiv_wrt_prod hf,fderiv_wrt_prod hg]

lemma divergence_add {f g : E → E} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    divergence 𝕜 (fun x => f x + g x) x
    =
    divergence 𝕜 f x + divergence 𝕜 g x := by
  unfold divergence
  simp [fderiv_fun_add hf hg]

lemma divergence_neg {f : E → E} {x : E} :
    divergence 𝕜 (fun x => -f x) x = -divergence 𝕜 f x := by
  unfold divergence
  simp

lemma divergence_sub {f g : E → E} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    divergence 𝕜 (fun x => f x - g x) x
    =
    divergence 𝕜 f x - divergence 𝕜 g x := by
  unfold divergence
  simp [fderiv_fun_sub hf hg]

lemma divergence_const_smul {f : E → E} {x : E} {c : 𝕜}
    (hf : DifferentiableAt 𝕜 f x) :
    divergence 𝕜 (fun x => c • f x) x
    =
    c * divergence 𝕜 f x := by
  unfold divergence
  simp [fderiv_fun_const_smul hf]

open InnerProductSpace' in
lemma divergence_smul [InnerProductSpace' 𝕜 E] {f : E → 𝕜} {g : E → E} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
    [FiniteDimensional 𝕜 E] :
    divergence 𝕜 (fun x => f x • g x) x
    = f x * divergence 𝕜 g x + ⟪adjFDeriv 𝕜 f x 1, g x⟫_𝕜 := by
  haveI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  simp [divergence, fderiv_fun_smul hf hg, hf.hasAdjFDerivAt.hasAdjoint_fderiv.adjoint_inner_left]
