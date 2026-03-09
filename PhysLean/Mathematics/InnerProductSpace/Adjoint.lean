/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
module

public import PhysLean.Mathematics.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
/-!

# Adjoint of a linear map

This module defines the adjoint of a linear map `f : E → F` where
`E` and `F` carry the instances of `InnerProductSpace'` over a field `𝕜`.

This is a generalization of the usual adjoint defined on `InnerProductSpace` for
continuous linear maps.

-/

@[expose] public section
variable {𝕜 : Type*} {E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [InnerProductSpace' 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [InnerProductSpace' 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [InnerProductSpace' 𝕜 G]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (𝕜) in
/-- Adjoint of a linear map `f` such that `∀ x y, ⟪adjoint 𝕜 f y, x⟫ = ⟪y, f x⟫`.

This computes adjoint of a linear map the same way as `ContinuousLinearMap.adjoint` but it is
defined over `InnerProductSpace'`, which is a generalization of `InnerProductSpace` that provides
instances for products and function types. These instances make it easier to perform computations
compared to using the standard `InnerProductSpace` class.
-/
structure HasAdjoint (f : E → F) (f' : F → E) where
  adjoint_inner_left (x : E) (y : F) : ⟪f' y, x⟫ = ⟪y, f x⟫

open Classical in
variable (𝕜) in
@[inherit_doc HasAdjoint]
noncomputable
def adjoint (f : E → F) :=
  if h : ∃ f', HasAdjoint 𝕜 f f' then
    choose h
  else 0

lemma HasAdjoint.adjoint_inner_right {f : E → F} (hf : HasAdjoint 𝕜 f f') :
    ⟪x, f' y⟫ = ⟪f x, y⟫ := by
  rw [← inner_conj_symm']
  rw [hf.adjoint_inner_left]
  rw [inner_conj_symm']

open InnerProductSpace' in
lemma ContinuousLinearMap.hasAdjoint [CompleteSpace E] [CompleteSpace F] (f : E →L[𝕜] F) :
    HasAdjoint 𝕜 f (fun y => fromL2 𝕜 (((toL2 𝕜) ∘L f ∘L (fromL2 𝕜)).adjoint (toL2 𝕜 y))) where
  adjoint_inner_left := by intros; simp[fromL2_inner_left,adjoint_inner_left]; rfl

open InnerProductSpace' in
lemma adjoint_eq_clm_adjoint [CompleteSpace E] [CompleteSpace F] (f : E →L[𝕜] F) :
    _root_.adjoint 𝕜 f = fromL2 𝕜 ∘L (toL2 𝕜 ∘L f ∘L fromL2 𝕜).adjoint ∘L (toL2 𝕜) := by
  ext y; apply ext_inner_right' 𝕜; intro x; simp
  rw [f.hasAdjoint.adjoint_inner_left]
  have h : ∃ f', HasAdjoint 𝕜 f f' := ⟨_,f.hasAdjoint⟩
  simp[_root_.adjoint,h,h.choose_spec.adjoint_inner_left]

lemma HasAdjoint.adjoint_apply_zero {f : E → F} {f' : F → E}
    (hf : HasAdjoint 𝕜 f f') : f' 0 = 0 := by
  simpa using hf.adjoint_inner_left (f' 0) 0

lemma HasAdjoint.adjoint
    {f : E → F} {f' : F → E}
    (hf : HasAdjoint 𝕜 f f') : adjoint 𝕜 f = f' := by
  funext y
  apply ext_inner_right' 𝕜
  unfold _root_.adjoint
  have h : ∃ f', HasAdjoint 𝕜 f f' := ⟨f', hf⟩
  have := h.choose_spec.adjoint_inner_left
  simp_all
  simp [hf.adjoint_inner_left]

lemma HasAdjoint.congr_adj (f : E → F) (f' g')
    (adjoint : HasAdjoint 𝕜 f g')
    (eq : g' = f') : HasAdjoint 𝕜 f f' := by simp[← eq,adjoint]

lemma hasAdjoint_id : HasAdjoint 𝕜 (fun x : E => x) (fun x => x) := by
  constructor; intros; rfl

lemma hasAdjoint_zero : HasAdjoint 𝕜 (fun _ : E => (0 : F)) (fun _ => 0) := by
  constructor; intros; simp

lemma HasAdjoint.comp {f : F → G} {g : E → F} {f' g'}
    (hf : HasAdjoint 𝕜 f f') (hg : HasAdjoint 𝕜 g g') :
    HasAdjoint 𝕜 (fun x : E => f (g x)) (fun x => g' (f' x)) := by
  constructor; intros; simp[hf.adjoint_inner_left, hg.adjoint_inner_left]

lemma HasAdjoint.prodMk {f : E → F} {g : E → G} {f' g'}
    (hf : HasAdjoint 𝕜 f f') (hg : HasAdjoint 𝕜 g g') :
    HasAdjoint 𝕜 (fun x : E => (f x, g x)) (fun yz => f' yz.1 + g' yz.2) := by
  constructor; intros
  simp [inner_add_left',
      hf.adjoint_inner_left, hg.adjoint_inner_left]

lemma HasAdjoint.fst {f : E → F×G} {f'} (hf : HasAdjoint 𝕜 f f') :
    HasAdjoint 𝕜 (fun x : E => (f x).1) (fun y => f' (y, 0)) := by
  constructor; intros
  simp[hf.adjoint_inner_left]

lemma HasAdjoint.snd {f : E → F×G} {f'} (hf : HasAdjoint 𝕜 f f') :
    HasAdjoint 𝕜 (fun x : E => (f x).2) (fun z => f' (0, z)) := by
  constructor; intros
  simp[hf.adjoint_inner_left]

lemma HasAdjoint.neg {f : E → F} {f'} (hf : HasAdjoint 𝕜 f f') :
    HasAdjoint 𝕜 (fun x : E => -f x) (fun y => -f' y) := by
  constructor; intros
  simp[hf.adjoint_inner_left]

lemma HasAdjoint.add {f g : E → F} {f' g'}
    (hf : HasAdjoint 𝕜 f f') (hg : HasAdjoint 𝕜 g g') :
    HasAdjoint 𝕜 (fun x : E => f x + g x) (fun y => f' y + g' y) := by
  constructor; intros
  simp[inner_add_left', inner_add_right',
      hf.adjoint_inner_left, hg.adjoint_inner_left]

lemma HasAdjoint.sub {f g : E → F} {f' g'}
    (hf : HasAdjoint 𝕜 f f') (hg : HasAdjoint 𝕜 g g') :
    HasAdjoint 𝕜 (fun x : E => f x - g x) (fun y => f' y - g' y) := by
  constructor; intros
  simp[sub_eq_add_neg, inner_add_left', inner_add_right',
      hf.adjoint_inner_left, hg.adjoint_inner_left]

open ComplexConjugate in
lemma HasAdjoint.smul_left {f : E → F} {f'} (c : 𝕜)
    (hf : HasAdjoint 𝕜 f f') :
    HasAdjoint 𝕜 (fun x : E => c • f x) (fun y => (conj c) • f' y) := by
  constructor; intros
  simp[inner_smul_left', inner_smul_right', hf.adjoint_inner_left]

open ComplexConjugate in
lemma HasAdjoint.smul_right {f : E → 𝕜} {f'} (v : F)
    (hf : HasAdjoint 𝕜 f f') :
    HasAdjoint 𝕜 (fun x : E => f x • v) (fun y => f' (conj ⟪y, v⟫)) := by
  constructor; intros
  simp[inner_smul_right', hf.adjoint_inner_left]
