/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Matteo Cipollina
-/
module

public import Physlib.Mathematics.Geometry.VectorBundle.HomInverse
public import Physlib.Mathematics.InnerProductSpace.PseudoInnerSignature
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Pseudo-Riemannian vector bundles

A vector bundle whose fibres carry a `PseudoInnerProductSpace` is *pseudo-Riemannian* when that
form varies smoothly with the base point: the analogue of Mathlib's
`IsContMDiffRiemannianBundle`, and implied by it. Fibres need only be topological vector
spaces, so the API also serves normal, gauge and spinor bundles.

The class, its `C^n` monotonicity instances, the trivial-bundle instance and the smoothness of the
pairing follow `Mathlib.Geometry.Manifold.VectorBundle.Riemannian` by Sébastien Gouëzel statement
for statement; please keep the two in sync.

## Main definitions

* `IsContMDiffPseudoRiemannianBundle IB n F E`: the fibrewise form is `C^n`.
* `Bundle.ContMDiffPseudoRiemannianMetric IB n F E`: metric data, used to build instances.

## Main results

* `IsContMDiffRiemannianBundle.toIsContMDiffPseudoRiemannianBundle`: subsumption.
* `ContMDiffWithinAt.pseudoInner_bundle`, `flatL_bundle`, `sharpL_bundle`: pairing two smooth
  sections, and lowering or raising an index, preserve smoothness — the inputs to the Koszul
  formula. Raising is `Bundle.contMDiff_sharpL`, a corollary of `ContMDiff.clm_bundle_symm`.
* `Bundle.isLocallyConstant_index_of_continuous`: the fibrewise index is locally constant, with no
  manifold structure and no smoothness needed; `Bundle.isLocallyConstant_index` is the smooth
  corollary.

## Acknowledgements

The design follows Sébastien Gouëzel's proposal on [Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/The.20future.20of.20pseudo-Riemannian.20manifolds/with/619509253).

## Tags

pseudo-Riemannian, vector bundle, signature, index, Levi-Civita
-/

@[expose] public section

open Bundle ContinuousLinearMap ENat Filter Module Set
open scoped Manifold Bundle Topology ContDiff

section

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n n' : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, PseudoInnerProductSpace (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

variable (IB n F E) in
/-- The fibrewise pseudo-inner product depends `C^n`-smoothly on the base point.

As in `IsContMDiffRiemannianBundle`, this is phrased as the existence of a smooth family agreeing
with the fibrewise structure, keeping the class `Prop`-valued. -/
class IsContMDiffPseudoRiemannianBundle : Prop where
  exists_contMDiff : ∃ g : ∀ x : B, E x →L[ℝ] E x →L[ℝ] ℝ,
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (g b))
    ∧ ∀ (x : B) (v w : E x), pseudoInner v w = g x v w

lemma IsContMDiffPseudoRiemannianBundle.of_le
    [h : IsContMDiffPseudoRiemannianBundle IB n F E] (h' : n' ≤ n) :
    IsContMDiffPseudoRiemannianBundle IB n' F E := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  exact ⟨g, g_smooth.of_le h', hg⟩

instance {a : ℕ∞ω} [IsContMDiffPseudoRiemannianBundle IB ∞ F E] [h : LEInfty a] :
    IsContMDiffPseudoRiemannianBundle IB a F E :=
  IsContMDiffPseudoRiemannianBundle.of_le h.out

instance {a : ℕ∞ω} [IsContMDiffPseudoRiemannianBundle IB ω F E] :
    IsContMDiffPseudoRiemannianBundle IB a F E :=
  IsContMDiffPseudoRiemannianBundle.of_le le_top

instance [IsContMDiffPseudoRiemannianBundle IB 1 F E] :
    IsContMDiffPseudoRiemannianBundle IB 0 F E :=
  IsContMDiffPseudoRiemannianBundle.of_le zero_le_one

instance [IsContMDiffPseudoRiemannianBundle IB 2 F E] :
    IsContMDiffPseudoRiemannianBundle IB 1 F E :=
  IsContMDiffPseudoRiemannianBundle.of_le one_le_two

instance [IsContMDiffPseudoRiemannianBundle IB 3 F E] :
    IsContMDiffPseudoRiemannianBundle IB 2 F E :=
  IsContMDiffPseudoRiemannianBundle.of_le (n := 3) (by norm_cast)

section Trivial

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [PseudoInnerProductSpace F₁]

set_option backward.isDefEq.respectTransparency false in
/-- A trivial bundle whose model fibre is a pseudo-inner product space is pseudo-Riemannian. -/
instance : IsContMDiffPseudoRiemannianBundle IB n F₁ (Bundle.Trivial B F₁) := by
  refine ⟨fun _ ↦ PseudoInnerProductSpace.pseudoInnerSL, fun x ↦ ?_, fun _ _ _ ↦ rfl⟩
  simp only [contMDiffAt_section]
  convert! contMDiffAt_const (c := PseudoInnerProductSpace.pseudoInnerSL (E := F₁))
  ext v w
  simp [hom_trivializationAt_apply, inCoordinates]

end Trivial

end

/-! ## Riemannian bundles are pseudo-Riemannian bundles -/

section RiemannianSubsumption

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- **Subsumption.** A `C^n` Riemannian bundle is a `C^n` pseudo-Riemannian bundle, for the form
from `InnerProductSpace.toPseudoInnerProductSpace`. Everything below therefore applies to
Riemannian geometry with no adapter. -/
instance IsContMDiffRiemannianBundle.toIsContMDiffPseudoRiemannianBundle
    [h : IsContMDiffRiemannianBundle IB n F E] :
    IsContMDiffPseudoRiemannianBundle IB n F E := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  exact ⟨g, g_smooth, fun x v w ↦ hg x v w⟩

end RiemannianSubsumption

/-! ## Smoothness of the pairing -/

section Pairing

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, PseudoInnerProductSpace (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {b : M → B} {v w : ∀ x, E (b x)} {s : Set M} {x : M}

section ContMDiff

variable [h : IsContMDiffPseudoRiemannianBundle IB n F E]

/-- The pairing of two smooth maps into the fibres is smooth. -/
lemma ContMDiffWithinAt.pseudoInner_bundle
    (hv : CMDiffAt[s] n (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : CMDiffAt[s] n (fun m ↦ (w m : TotalSpace F E)) x) :
    CMDiffAt[s] n (fun m ↦ pseudoInner (v m) (w m)) x := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  have hb : CMDiffAt[s] n b x := by
    simp only [contMDiffWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have key : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ)) n
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (g (b m) (v m) (w m))) s x := by
    apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F)
    · exact ContMDiffAt.comp_contMDiffWithinAt x g_smooth.contMDiffAt hb
    · exact hv
    · exact hw
  simp only [contMDiffWithinAt_totalSpace] at key
  exact key.2

lemma ContMDiffAt.pseudoInner_bundle
    (hv : CMDiffAt n (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : CMDiffAt n (fun m ↦ (w m : TotalSpace F E)) x) :
    CMDiffAt n (fun m ↦ pseudoInner (v m) (w m)) x :=
  ContMDiffWithinAt.pseudoInner_bundle hv hw

lemma ContMDiffOn.pseudoInner_bundle
    (hv : CMDiff[s] n (fun m ↦ (v m : TotalSpace F E)))
    (hw : CMDiff[s] n (fun m ↦ (w m : TotalSpace F E))) :
    CMDiff[s] n (fun m ↦ pseudoInner (v m) (w m)) :=
  fun x hx ↦ (hv x hx).pseudoInner_bundle (hw x hx)

lemma ContMDiff.pseudoInner_bundle
    (hv : CMDiff n (fun m ↦ (v m : TotalSpace F E)))
    (hw : CMDiff n (fun m ↦ (w m : TotalSpace F E))) :
    CMDiff n (fun m ↦ pseudoInner (v m) (w m)) :=
  fun x ↦ (hv x).pseudoInner_bundle (hw x)

end ContMDiff

section MDifferentiable

variable [h : IsContMDiffPseudoRiemannianBundle IB 1 F E]

/-- The pairing of two differentiable maps into the fibres is differentiable. -/
lemma MDifferentiableWithinAt.pseudoInner_bundle
    (hv : MDiffAt[s] (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : MDiffAt[s] (fun m ↦ (w m : TotalSpace F E)) x) :
    MDiffAt[s] (fun m ↦ pseudoInner (v m) (w m)) x := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  have hb : MDiffAt[s] b x := by
    simp only [mdifferentiableWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have key : MDifferentiableWithinAt IM (IB.prod 𝓘(ℝ))
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (g (b m) (v m) (w m))) s x := by
    apply MDifferentiableWithinAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F)
    · exact MDifferentiableAt.comp_mdifferentiableWithinAt x
        (g_smooth.mdifferentiableAt one_ne_zero) hb
    · exact hv
    · exact hw
  simp only [mdifferentiableWithinAt_totalSpace] at key
  exact key.2

lemma MDifferentiableAt.pseudoInner_bundle
    (hv : MDiffAt (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : MDiffAt (fun m ↦ (w m : TotalSpace F E)) x) :
    MDiffAt (fun m ↦ pseudoInner (v m) (w m)) x :=
  MDifferentiableWithinAt.pseudoInner_bundle hv hw

lemma MDifferentiableOn.pseudoInner_bundle
    (hv : MDiff[s] (fun m ↦ (v m : TotalSpace F E)))
    (hw : MDiff[s] (fun m ↦ (w m : TotalSpace F E))) :
    MDiff[s] (fun m ↦ pseudoInner (v m) (w m)) :=
  fun x hx ↦ (hv x hx).pseudoInner_bundle (hw x hx)

lemma MDifferentiable.pseudoInner_bundle
    (hv : MDiff (fun m ↦ (v m : TotalSpace F E)))
    (hw : MDiff (fun m ↦ (w m : TotalSpace F E))) :
    MDiff (fun m ↦ pseudoInner (v m) (w m)) :=
  fun x ↦ (hv x).pseudoInner_bundle (hw x)

end MDifferentiable

end Pairing

/-! ## Smoothness of index lowering -/

section Flat

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, PseudoInnerProductSpace (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {b : M → B} {v : ∀ x, E (b x)} {s : Set M} {x : M}

variable (IB n F E) in
/-- Index lowering is a smooth section of `Hom(E, E⋆)`. -/
lemma Bundle.contMDiff_flatL [h : IsContMDiffPseudoRiemannianBundle IB n F E] :
    CMDiff n (fun y ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
      (E := fun z : B ↦ E z →L[ℝ] E z →L[ℝ] ℝ) y (PseudoInnerProductSpace.flatL (E y))) := by
  obtain ⟨g, g_smooth, hg⟩ := h.exists_contMDiff
  have hEq : ∀ y : B, PseudoInnerProductSpace.flatL (E y) = g y := fun y ↦ by
    ext w w'; exact hg y w w'
  simpa only [hEq] using g_smooth

section ContMDiff

variable [IsContMDiffPseudoRiemannianBundle IB n F E]

/-- Index lowering sends smooth sections to smooth covector fields. -/
lemma ContMDiffWithinAt.flatL_bundle
    (hv : CMDiffAt[s] n (fun m ↦ (v m : TotalSpace F E)) x) :
    CMDiffAt[s] n (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m)
      (PseudoInnerProductSpace.flatL (E (b m)) (v m))) x := by
  have hb : CMDiffAt[s] n b x := by
    simp only [contMDiffWithinAt_totalSpace] at hv
    exact hv.1
  exact ContMDiffWithinAt.clm_bundle_apply (F₁ := F) (F₂ := F →L[ℝ] ℝ)
    (ContMDiffAt.comp_contMDiffWithinAt x (Bundle.contMDiff_flatL IB n F E).contMDiffAt hb) hv

lemma ContMDiffAt.flatL_bundle
    (hv : CMDiffAt n (fun m ↦ (v m : TotalSpace F E)) x) :
    CMDiffAt n (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m)
      (PseudoInnerProductSpace.flatL (E (b m)) (v m))) x :=
  ContMDiffWithinAt.flatL_bundle hv

lemma ContMDiffOn.flatL_bundle
    (hv : CMDiff[s] n (fun m ↦ (v m : TotalSpace F E))) :
    CMDiff[s] n (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m)
      (PseudoInnerProductSpace.flatL (E (b m)) (v m))) :=
  fun x hx ↦ (hv x hx).flatL_bundle

lemma ContMDiff.flatL_bundle
    (hv : CMDiff n (fun m ↦ (v m : TotalSpace F E))) :
    CMDiff n (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m)
      (PseudoInnerProductSpace.flatL (E (b m)) (v m))) :=
  fun x ↦ (hv x).flatL_bundle

end ContMDiff

section MDifferentiable

variable [IsContMDiffPseudoRiemannianBundle IB 1 F E]

/-- Index lowering sends differentiable sections to differentiable covector fields. -/
lemma MDifferentiableWithinAt.flatL_bundle
    (hv : MDiffAt[s] (fun m ↦ (v m : TotalSpace F E)) x) :
    MDiffAt[s] (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m)
      (PseudoInnerProductSpace.flatL (E (b m)) (v m))) x := by
  have hb : MDiffAt[s] b x := by
    simp only [mdifferentiableWithinAt_totalSpace] at hv
    exact hv.1
  exact MDifferentiableWithinAt.clm_bundle_apply (F₁ := F) (F₂ := F →L[ℝ] ℝ)
    (MDifferentiableAt.comp_mdifferentiableWithinAt x
      ((Bundle.contMDiff_flatL IB 1 F E).mdifferentiableAt one_ne_zero) hb) hv

lemma MDifferentiableAt.flatL_bundle
    (hv : MDiffAt (fun m ↦ (v m : TotalSpace F E)) x) :
    MDiffAt (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m)
      (PseudoInnerProductSpace.flatL (E (b m)) (v m))) x :=
  MDifferentiableWithinAt.flatL_bundle hv

lemma MDifferentiableOn.flatL_bundle
    (hv : MDiff[s] (fun m ↦ (v m : TotalSpace F E))) :
    MDiff[s] (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m)
      (PseudoInnerProductSpace.flatL (E (b m)) (v m))) :=
  fun x hx ↦ (hv x hx).flatL_bundle

lemma MDifferentiable.flatL_bundle
    (hv : MDiff (fun m ↦ (v m : TotalSpace F E))) :
    MDiff (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m)
      (PseudoInnerProductSpace.flatL (E (b m)) (v m))) :=
  fun x ↦ (hv x).flatL_bundle

end MDifferentiable

end Flat

/-! ## Smoothness of index raising -/

section Sharp

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℝ (E x)]
  [∀ x, T2Space (E x)] [∀ x, FiniteDimensional ℝ (E x)]
  [∀ x, PseudoInnerProductSpace (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {b : M → B} {η : ∀ x, E (b x) →L[ℝ] ℝ} {s : Set M} {x : M}

variable (IB n F E) in
/-- Index raising is a smooth section of `Hom(E⋆, E)`.

This is `ContMDiff.clm_bundle_symm` applied to `♭`: no metric-specific argument is involved, only
that inverting a smooth fibrewise isomorphism is smooth. -/
lemma Bundle.contMDiff_sharpL [IsContMDiffPseudoRiemannianBundle IB n F E] :
    CMDiff n (fun y ↦ TotalSpace.mk' ((F →L[ℝ] ℝ) →L[ℝ] F)
      (E := fun z : B ↦ (E z →L[ℝ] ℝ) →L[ℝ] E z) y (PseudoInnerProductSpace.sharpL (E y))) := by
  refine ContMDiff.clm_bundle_symm (fun y ↦ PseudoInnerProductSpace.flatEquiv (E y)) ?_
  have hEq : ∀ y : B,
      ((PseudoInnerProductSpace.flatEquiv (E y) : E y ≃L[ℝ] (E y →L[ℝ] ℝ)) :
        E y →L[ℝ] (E y →L[ℝ] ℝ)) = PseudoInnerProductSpace.flatL (E y) := by
    intro y; ext v w; rfl
  simpa only [hEq] using Bundle.contMDiff_flatL IB n F E

section ContMDiff

variable [IsContMDiffPseudoRiemannianBundle IB n F E]

/-- Index raising sends smooth covector fields to smooth vector fields. -/
lemma ContMDiffWithinAt.sharpL_bundle
    (hη : CMDiffAt[s] n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m) (η m)) x) :
    CMDiffAt[s] n
      (fun m ↦ TotalSpace.mk' F (b m) (PseudoInnerProductSpace.sharpL (E (b m)) (η m))) x := by
  have hb : CMDiffAt[s] n b x := by
    simp only [contMDiffWithinAt_totalSpace] at hη
    exact hη.1
  exact ContMDiffWithinAt.clm_bundle_apply (F₁ := F →L[ℝ] ℝ) (F₂ := F)
    (E₁ := fun y : B ↦ E y →L[ℝ] ℝ) (E₂ := E)
    (ContMDiffAt.comp_contMDiffWithinAt x (Bundle.contMDiff_sharpL IB n F E).contMDiffAt hb) hη

lemma ContMDiffAt.sharpL_bundle
    (hη : CMDiffAt n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m) (η m)) x) :
    CMDiffAt n
      (fun m ↦ TotalSpace.mk' F (b m) (PseudoInnerProductSpace.sharpL (E (b m)) (η m))) x :=
  ContMDiffWithinAt.sharpL_bundle hη

lemma ContMDiffOn.sharpL_bundle
    (hη : CMDiff[s] n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m) (η m))) :
    CMDiff[s] n
      (fun m ↦ TotalSpace.mk' F (b m) (PseudoInnerProductSpace.sharpL (E (b m)) (η m))) :=
  fun x hx ↦ (hη x hx).sharpL_bundle

lemma ContMDiff.sharpL_bundle
    (hη : CMDiff n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m) (η m))) :
    CMDiff n
      (fun m ↦ TotalSpace.mk' F (b m) (PseudoInnerProductSpace.sharpL (E (b m)) (η m))) :=
  fun x ↦ (hη x).sharpL_bundle

end ContMDiff

section MDifferentiable

variable [IsContMDiffPseudoRiemannianBundle IB 1 F E]

/-- Index raising sends differentiable covector fields to differentiable vector fields. -/
lemma MDifferentiableWithinAt.sharpL_bundle
    (hη : MDiffAt[s]
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m) (η m)) x) :
    MDiffAt[s]
      (fun m ↦ TotalSpace.mk' F (b m) (PseudoInnerProductSpace.sharpL (E (b m)) (η m))) x := by
  have hb : MDiffAt[s] b x := by
    simp only [mdifferentiableWithinAt_totalSpace] at hη
    exact hη.1
  exact MDifferentiableWithinAt.clm_bundle_apply (F₁ := F →L[ℝ] ℝ) (F₂ := F)
    (E₁ := fun y : B ↦ E y →L[ℝ] ℝ) (E₂ := E)
    (MDifferentiableAt.comp_mdifferentiableWithinAt x
      ((Bundle.contMDiff_sharpL IB 1 F E).mdifferentiableAt one_ne_zero) hb) hη

lemma MDifferentiableAt.sharpL_bundle
    (hη : MDiffAt
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m) (η m)) x) :
    MDiffAt (fun m ↦ TotalSpace.mk' F (b m) (PseudoInnerProductSpace.sharpL (E (b m)) (η m))) x :=
  MDifferentiableWithinAt.sharpL_bundle hη

lemma MDifferentiableOn.sharpL_bundle
    (hη : MDiff[s]
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m) (η m))) :
    MDiff[s] (fun m ↦ TotalSpace.mk' F (b m) (PseudoInnerProductSpace.sharpL (E (b m)) (η m))) :=
  fun x hx ↦ (hη x hx).sharpL_bundle

lemma MDifferentiable.sharpL_bundle
    (hη : MDiff
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m) (η m))) :
    MDiff (fun m ↦ TotalSpace.mk' F (b m) (PseudoInnerProductSpace.sharpL (E (b m)) (η m))) :=
  fun x ↦ (hη x).sharpL_bundle

end MDifferentiable

end Sharp

namespace Bundle

/-! ## Bundled smooth pseudo-Riemannian metrics -/

section Construction

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

variable (IB n F E) in
/-- A `C^n` pseudo-Riemannian metric along a vector bundle, used to build instances via
`toPseudoInnerProductSpace`.

Unlike `Bundle.ContMDiffRiemannianMetric` there is no von Neumann boundedness field: it is needed
there only to build a norm, and an indefinite form induces none. -/
structure ContMDiffPseudoRiemannianMetric where
  /-- The fibrewise bilinear form. -/
  metric (b : B) : E b →L[ℝ] E b →L[ℝ] ℝ
  symm (b : B) (v w : E b) : metric b v w = metric b w v
  nondegenerate (b : B) (v : E b) (hv : ∀ w : E b, metric b v w = 0) : v = 0
  contMDiff : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
    (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (metric b))

namespace ContMDiffPseudoRiemannianMetric

/-- The fibrewise pseudo-inner product structure carried by a smooth pseudo-Riemannian metric. -/
@[reducible] def toPseudoInnerProductSpace (g : ContMDiffPseudoRiemannianMetric IB n F E) (b : B) :
    PseudoInnerProductSpace (E b) where
  pseudoInnerSL := g.metric b
  pseudoInner_symm := g.symm b
  pseudoInner_nondegenerate := g.nondegenerate b

instance (g : ContMDiffPseudoRiemannianMetric IB n F E) :
    letI : ∀ b : B, PseudoInnerProductSpace (E b) := g.toPseudoInnerProductSpace
    IsContMDiffPseudoRiemannianBundle IB n F E :=
  letI : ∀ b : B, PseudoInnerProductSpace (E b) := g.toPseudoInnerProductSpace
  ⟨g.metric, g.contMDiff, fun _ _ _ ↦ rfl⟩

end ContMDiffPseudoRiemannianMetric

end Construction

/-! ## The index of a pseudo-Riemannian bundle

Local constancy of the index needs no manifold structure and no smoothness: continuity of the
fibrewise form is enough. It is therefore proved here for an arbitrary topological vector bundle,
and specialized to the smooth setting afterwards. -/

section Index

variable
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, PseudoInnerProductSpace (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

omit [∀ x, PseudoInnerProductSpace (E x)] in
private lemma symm_continuousLinearEquivAt_apply {x₀ x : B}
    (hx : x ∈ (trivializationAt F E x₀).baseSet) (u : E x) :
    (trivializationAt F E x₀).symm x
      (((trivializationAt F E x₀).continuousLinearEquivAt ℝ x hx).toLinearEquiv u) = u :=
  ((trivializationAt F E x₀).continuousLinearEquivAt ℝ x hx).symm_apply_apply u

/-- Reading the fibrewise form in a local trivialization does not change its index. -/
private lemma index_eq_sigNeg_trivialization {x₀ x : B}
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (g : ∀ y : B, E y →L[ℝ] E y →L[ℝ] ℝ)
    (hg : ∀ (y : B) (v w : E y), pseudoInner v w = g y v w)
    (G : F →L[ℝ] F →L[ℝ] ℝ)
    (hG : ∀ u u' : F, G u u' =
      g x ((trivializationAt F E x₀).symm x u) ((trivializationAt F E x₀).symm x u')) :
    PseudoInnerProductSpace.index (E x) = sigNeg G.toQuadraticForm := by
  have hform : PseudoInnerProductSpace.toQuadraticForm (E x) = (g x).toQuadraticForm := by
    ext v
    simpa using hg x v v
  rw [PseudoInnerProductSpace.index, hform]
  refine ContinuousLinearMap.sigNeg_toQuadraticForm_of_congr (g x) G
    ((trivializationAt F E x₀).continuousLinearEquivAt ℝ x hx).toLinearEquiv (fun u w ↦ ?_)
  rw [hG, symm_continuousLinearEquivAt_apply hx u, symm_continuousLinearEquivAt_apply hx w]

omit [∀ x, PseudoInnerProductSpace (E x)] in
/-- The coordinate expression of the fibrewise form in the trivialization of the bundle of
bilinear forms at `x₀` is the transport of the form along the trivialization of `E`. -/
private lemma hom_trivialization_apply {x₀ x : B}
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (b : E x →L[ℝ] E x →L[ℝ] ℝ) (u u' : F) :
    ((trivializationAt (F →L[ℝ] F →L[ℝ] ℝ) (fun y : B ↦ E y →L[ℝ] E y →L[ℝ] ℝ) x₀)
        ⟨x, b⟩).2 u u' =
      b ((trivializationAt F E x₀).symm x u) ((trivializationAt F E x₀).symm x u') := by
  have hrfl : ((trivializationAt (F →L[ℝ] F →L[ℝ] ℝ) (fun y : B ↦ E y →L[ℝ] E y →L[ℝ] ℝ) x₀)
      ⟨x, b⟩).2 = inCoordinates F E (F →L[ℝ] ℝ) (fun y : B ↦ E y →L[ℝ] ℝ) x₀ x x₀ x b := rfl
  rw [hrfl, _root_.inCoordinates_apply_eq₂ (F₁ := F) (E₁ := E) (F₂ := F) (E₂ := E) (F₃ := ℝ)
    (E₃ := Bundle.Trivial B ℝ) hx hx (by simp)]
  simp

variable [FiniteDimensional ℝ F]

/-- **The index is locally constant**, for a merely continuous fibrewise form.

Sylvester's law of inertia fibrewise, transported to the model fibre by a local trivialization:
the form varies continuously and is everywhere nondegenerate, so its signature cannot jump. -/
theorem isLocallyConstant_index_of_continuous (g : ∀ x : B, E x →L[ℝ] E x →L[ℝ] ℝ)
    (hcont : Continuous fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
      (E := fun y : B ↦ E y →L[ℝ] E y →L[ℝ] ℝ) x (g x))
    (hg : ∀ (x : B) (v w : E x), pseudoInner v w = g x v w) :
    IsLocallyConstant (fun x ↦ PseudoInnerProductSpace.index (E x)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x₀
  set eh := trivializationAt (F →L[ℝ] F →L[ℝ] ℝ) (fun y : B ↦ E y →L[ℝ] E y →L[ℝ] ℝ) x₀ with heh
  set Φ : B → (F →L[ℝ] F →L[ℝ] ℝ) := fun x ↦ (eh ⟨x, g x⟩).2 with hΦ
  -- `Φ` is the form read in a local trivialization; it is continuous at `x₀`.
  have hx₀ : x₀ ∈ eh.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have hcontΦ : ContinuousAt Φ x₀ := by
    have hmaps : MapsTo (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun y : B ↦ E y →L[ℝ] E y →L[ℝ] ℝ) x (g x)) eh.baseSet eh.source :=
      fun x hx ↦ eh.mem_source.mpr hx
    have hcomp : ContinuousOn (fun x ↦ eh ⟨x, g x⟩) eh.baseSet :=
      eh.continuousOn.comp hcont.continuousOn hmaps
    exact (continuous_snd.comp_continuousOn hcomp).continuousAt
      (eh.open_baseSet.mem_nhds hx₀)
  -- On the base set of the trivialization, the index is that of the coordinate form.
  have hbase : ∀ x ∈ eh.baseSet,
      PseudoInnerProductSpace.index (E x) = sigNeg (Φ x).toQuadraticForm := by
    intro x hx
    rw [hom_trivializationAt_baseSet] at hx
    exact index_eq_sigNeg_trivialization hx.1 g hg (Φ x)
      (fun u u' ↦ hom_trivialization_apply hx.1 (g x) u u')
  -- The coordinate form at `x₀` is nondegenerate, so the signature is locally constant there.
  have hrad : (Φ x₀).toQuadraticForm.radical = ⊥ := by
    have hmem := hx₀
    rw [hom_trivializationAt_baseSet] at hmem
    have hform : PseudoInnerProductSpace.toQuadraticForm (E x₀) = (g x₀).toQuadraticForm := by
      ext v; simpa using hg x₀ v v
    refine ContinuousLinearMap.radical_toQuadraticForm_eq_bot_of_congr (g x₀) (Φ x₀)
      ((trivializationAt F E x₀).continuousLinearEquivAt ℝ x₀ hmem.1).toLinearEquiv
      (fun u w ↦ ?_) ?_
    · rw [hom_trivialization_apply hmem.1 (g x₀),
        symm_continuousLinearEquivAt_apply hmem.1 u, symm_continuousLinearEquivAt_apply hmem.1 w]
    · rw [← hform]
      exact PseudoInnerProductSpace.radical_toQuadraticForm_eq_bot (E x₀)
  filter_upwards [eh.open_baseSet.mem_nhds hx₀,
    hcontΦ (ContinuousLinearMap.eventually_sigNeg_eq hrad)] with x hx hsig
  rw [hbase x hx, hbase x₀ hx₀, hsig.2.2]

end Index

section IndexSmooth

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, PseudoInnerProductSpace (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- The index of a smooth pseudo-Riemannian bundle metric is locally constant. -/
theorem isLocallyConstant_index (n : ℕ∞ω) [h : IsContMDiffPseudoRiemannianBundle IB n F E] :
    IsLocallyConstant (fun x ↦ PseudoInnerProductSpace.index (E x)) := by
  obtain ⟨g, g_smooth, hg⟩ := h.exists_contMDiff
  exact isLocallyConstant_index_of_continuous g g_smooth.continuous hg

end IndexSmooth

end Bundle
