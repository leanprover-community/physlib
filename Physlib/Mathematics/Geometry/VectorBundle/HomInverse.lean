/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Smoothness of the inverse of a bundle isomorphism

A `C^n` section of `Hom(E, E')` that is fibrewise a continuous linear equivalence has a `C^n`
inverse section of `Hom(E', E)`. Read in a local trivialization the section becomes a map into
`F →L[𝕜] F'` taking invertible values, and inversion is `C^∞` there
(`contDiffAt_map_inverse`); the only work is that `ContinuousLinearMap.inCoordinates` commutes
with inversion, which is `inCoordinates_symm_eq_inverse`.

This is a statement about vector bundles with no metric content; its upstream home is
`Mathlib.Geometry.Manifold.VectorBundle.HomInverse`.

## Main results

* `ContMDiffAt.clm_bundle_symm` and `MDifferentiableAt.clm_bundle_symm`, with their global
  variants.

## Tags

vector bundle, continuous linear equivalence, inverse, smoothness
-/

@[expose] public section

open Bundle ContinuousLinearMap Filter Set
open scoped Manifold Bundle Topology ContDiff

section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  {E' : B → Type*} [TopologicalSpace (TotalSpace F' E')]
  [∀ x, AddCommGroup (E' x)] [∀ x, Module 𝕜 (E' x)] [∀ x, TopologicalSpace (E' x)]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul 𝕜 (E x)]
  [∀ x, IsTopologicalAddGroup (E' x)] [∀ x, ContinuousSMul 𝕜 (E' x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  [FiberBundle F' E'] [VectorBundle 𝕜 F' E']

namespace ContinuousLinearMap

omit [CompleteSpace F] [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul 𝕜 (E x)]
  [∀ x, IsTopologicalAddGroup (E' x)] [∀ x, ContinuousSMul 𝕜 (E' x)] in
/-- Reading a fibrewise isomorphism in a trivialization commutes with inversion. -/
lemma inCoordinates_symm_eq_inverse (φ : ∀ x : B, E x ≃L[𝕜] E' x) {x₀ x : B}
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (hx' : x ∈ (trivializationAt F' E' x₀).baseSet) :
    inCoordinates F' E' F E x₀ x x₀ x ((φ x).symm : E' x →L[𝕜] E x)
      = ContinuousLinearMap.inverse
          (inCoordinates F E F' E' x₀ x x₀ x ((φ x) : E x →L[𝕜] E' x)) := by
  set A := (trivializationAt F' E' x₀).continuousLinearEquivAt 𝕜 x hx' with hA
  set C := (trivializationAt F E x₀).continuousLinearEquivAt 𝕜 x hx with hC
  have hfwd : inCoordinates F E F' E' x₀ x x₀ x ((φ x) : E x →L[𝕜] E' x)
      = ((C.symm.trans ((φ x).trans A) : F ≃L[𝕜] F') : F →L[𝕜] F') := by
    rw [ContinuousLinearMap.inCoordinates_eq hx hx']
    ext u
    simp [hA, hC]
  rw [hfwd, ContinuousLinearMap.inverse_equiv,
    ContinuousLinearMap.inCoordinates_eq hx' hx]
  ext u
  simp [hA, hC]

end ContinuousLinearMap

/-- A `C^n` bundle map that is fibrewise a continuous linear equivalence has a `C^n` inverse. -/
lemma ContMDiffAt.clm_bundle_symm (φ : ∀ x : B, E x ≃L[𝕜] E' x) {x₀ : B}
    (hφ : ContMDiffAt IB (IB.prod 𝓘(𝕜, F →L[𝕜] F')) n
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] F') (E := fun y ↦ E y →L[𝕜] E' y) x
        ((φ x : E x →L[𝕜] E' x))) x₀) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F' →L[𝕜] F)) n
      (fun x ↦ TotalSpace.mk' (F' →L[𝕜] F) (E := fun y ↦ E' y →L[𝕜] E y) x
        (((φ x).symm : E' x →L[𝕜] E x))) x₀ := by
  rw [contMDiffAt_section] at hφ ⊢
  have hx₀ : x₀ ∈ (trivializationAt F E x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hx₀' : x₀ ∈ (trivializationAt F' E' x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  set A₀ := (trivializationAt F' E' x₀).continuousLinearEquivAt 𝕜 x₀ hx₀' with hA₀
  set C₀ := (trivializationAt F E x₀).continuousLinearEquivAt 𝕜 x₀ hx₀ with hC₀
  have hfwd₀ : inCoordinates F E F' E' x₀ x₀ x₀ x₀ ((φ x₀) : E x₀ →L[𝕜] E' x₀)
      = ((C₀.symm.trans ((φ x₀).trans A₀) : F ≃L[𝕜] F') : F →L[𝕜] F') := by
    rw [ContinuousLinearMap.inCoordinates_eq hx₀ hx₀']; ext u; simp [hA₀, hC₀]
  have hinv : ContMDiffAt 𝓘(𝕜, F →L[𝕜] F') 𝓘(𝕜, F' →L[𝕜] F) n
      ContinuousLinearMap.inverse
      (inCoordinates F E F' E' x₀ x₀ x₀ x₀ ((φ x₀) : E x₀ →L[𝕜] E' x₀)) := by
    rw [hfwd₀]
    exact (contDiffAt_map_inverse (n := n) (C₀.symm.trans ((φ x₀).trans A₀))).contMDiffAt
  refine (hinv.comp x₀ hφ).congr_of_eventuallyEq ?_
  have hmem : (trivializationAt F E x₀).baseSet ∩ (trivializationAt F' E' x₀).baseSet ∈ 𝓝 x₀ :=
    ((trivializationAt F E x₀).open_baseSet.inter
      (trivializationAt F' E' x₀).open_baseSet).mem_nhds ⟨hx₀, hx₀'⟩
  filter_upwards [hmem] with x hx
  exact inCoordinates_symm_eq_inverse φ hx.1 hx.2

lemma ContMDiff.clm_bundle_symm (φ : ∀ x : B, E x ≃L[𝕜] E' x)
    (hφ : ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] F')) n
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] F') (E := fun y ↦ E y →L[𝕜] E' y) x
        ((φ x : E x →L[𝕜] E' x)))) :
    ContMDiff IB (IB.prod 𝓘(𝕜, F' →L[𝕜] F)) n
      (fun x ↦ TotalSpace.mk' (F' →L[𝕜] F) (E := fun y ↦ E' y →L[𝕜] E y) x
        (((φ x).symm : E' x →L[𝕜] E x))) :=
  fun x ↦ ContMDiffAt.clm_bundle_symm φ (hφ x)

lemma MDifferentiableAt.clm_bundle_symm (φ : ∀ x : B, E x ≃L[𝕜] E' x) {x₀ : B}
    (hφ : MDifferentiableAt IB (IB.prod 𝓘(𝕜, F →L[𝕜] F'))
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] F') (E := fun y ↦ E y →L[𝕜] E' y) x
        ((φ x : E x →L[𝕜] E' x))) x₀) :
    MDifferentiableAt IB (IB.prod 𝓘(𝕜, F' →L[𝕜] F))
      (fun x ↦ TotalSpace.mk' (F' →L[𝕜] F) (E := fun y ↦ E' y →L[𝕜] E y) x
        (((φ x).symm : E' x →L[𝕜] E x))) x₀ := by
  rw [mdifferentiableAt_section] at hφ ⊢
  have hx₀ : x₀ ∈ (trivializationAt F E x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hx₀' : x₀ ∈ (trivializationAt F' E' x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  set A₀ := (trivializationAt F' E' x₀).continuousLinearEquivAt 𝕜 x₀ hx₀' with hA₀
  set C₀ := (trivializationAt F E x₀).continuousLinearEquivAt 𝕜 x₀ hx₀ with hC₀
  have hfwd₀ : inCoordinates F E F' E' x₀ x₀ x₀ x₀ ((φ x₀) : E x₀ →L[𝕜] E' x₀)
      = ((C₀.symm.trans ((φ x₀).trans A₀) : F ≃L[𝕜] F') : F →L[𝕜] F') := by
    rw [ContinuousLinearMap.inCoordinates_eq hx₀ hx₀']; ext u; simp [hA₀, hC₀]
  have hinv : MDifferentiableAt 𝓘(𝕜, F →L[𝕜] F') 𝓘(𝕜, F' →L[𝕜] F)
      ContinuousLinearMap.inverse
      (inCoordinates F E F' E' x₀ x₀ x₀ x₀ ((φ x₀) : E x₀ →L[𝕜] E' x₀)) := by
    rw [hfwd₀]
    exact ((contDiffAt_map_inverse (n := 1)
      (C₀.symm.trans ((φ x₀).trans A₀))).contMDiffAt).mdifferentiableAt one_ne_zero
  refine (hinv.comp x₀ hφ).congr_of_eventuallyEq ?_
  have hmem : (trivializationAt F E x₀).baseSet ∩ (trivializationAt F' E' x₀).baseSet ∈ 𝓝 x₀ :=
    ((trivializationAt F E x₀).open_baseSet.inter
      (trivializationAt F' E' x₀).open_baseSet).mem_nhds ⟨hx₀, hx₀'⟩
  filter_upwards [hmem] with x hx
  exact inCoordinates_symm_eq_inverse φ hx.1 hx.2

lemma MDifferentiable.clm_bundle_symm (φ : ∀ x : B, E x ≃L[𝕜] E' x)
    (hφ : MDifferentiable IB (IB.prod 𝓘(𝕜, F →L[𝕜] F'))
      (fun x ↦ TotalSpace.mk' (F →L[𝕜] F') (E := fun y ↦ E y →L[𝕜] E' y) x
        ((φ x : E x →L[𝕜] E' x)))) :
    MDifferentiable IB (IB.prod 𝓘(𝕜, F' →L[𝕜] F))
      (fun x ↦ TotalSpace.mk' (F' →L[𝕜] F) (E := fun y ↦ E' y →L[𝕜] E y) x
        (((φ x).symm : E' x →L[𝕜] E x))) :=
  fun x ↦ MDifferentiableAt.clm_bundle_symm φ (hφ x)

end
