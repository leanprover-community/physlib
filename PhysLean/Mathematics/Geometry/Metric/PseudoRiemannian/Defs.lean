/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Topology.LocallyConstant.Basic
import PhysLean.Mathematics.Geometry.Metric.QuadraticForm.NegDim

/-!
# Pseudo-Riemannian Metrics on Smooth Manifolds

This file formalizes pseudo-Riemannian metrics on smooth manifolds and establishes their basic
properties.

A pseudo-Riemannian metric equips a manifold with a smoothly varying, non-degenerate, symmetric
bilinear form of *constant index* on each tangent space, generalizing the concept of an inner
product space to curved spaces. The index here refers to `QuadraticForm.negDim`, the dimension
of a maximal negative definite subspace.

## Main Definitions

* `PseudoRiemannianMetric E H M n I`: A structure representing a `C^n` pseudo-Riemannian metric
  on a manifold `M` modelled on `(E, H)` with model with corners `I`. It consists of a family
  of non-degenerate, symmetric, continuous bilinear forms `gₓ` on each tangent space `TₓM`,
  varying `C^n`-smoothly with `x` and having a locally constant negative dimension (`negDim`).
  The model space `E` must be finite-dimensional, and the manifold `M` must be `C^{n+1}` smooth.

* `PseudoRiemannianMetric.flatEquiv g x`: The "musical isomorphism" from the tangent space at `x`
  to its dual space, representing the canonical isomorphism induced by the metric.

* `PseudoRiemannianMetric.sharpEquiv g x`: The inverse of the flat isomorphism, mapping from
  the dual space back to the tangent space.

* `PseudoRiemannianMetric.toQuadraticForm g x`: The quadratic form `v ↦ gₓ(v, v)` associated
  with the metric at point `x`.

We show smoothness with same pattern as mathlib Riemannian API:
the metric is a section of the (vector-bundle) bundle of bilinear forms, and the smoothness
assumption is a `ContMDiff` statement for this section (instead of being phrased chartwise).

## Reference

* Barrett O'Neill, "Semi-Riemannian Geometry With Applications to Relativity" (Academic Press, 1983)
* [Discussion on Zulip about (Pseudo) Riemannian metrics] https.
leanprover.zulipchat.com/#narrow/channel/113488-general/topic/.28Pseudo.29.20Riemannian.20metric
-/

section PseudoRiemannianMetric

open Bundle Set Finset Function Filter Module Topology ContinuousLinearMap
open scoped Manifold Bundle LinearMap Dual

/-! ## Bundle-level infrastructure (Mathlib-style) -/

namespace Bundle

/-! ### Fiberwise pseudo-Riemannian structures -/

section PseudoRiemannianBundle

variable
  {B : Type*} [TopologicalSpace B]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]

/-- A pseudo-Riemannian structure on a family of fibers `E x`: a symmetric, nondegenerate bilinear
form on each fiber, expressed as a continuous bilinear map. -/
class PseudoRiemannianBundle : Type _ where
  metric : ∀ x : B, E x →L[ℝ] E x →L[ℝ] ℝ
  symm : ∀ (x : B) (v w : E x), metric x v w = metric x w v
  nondegenerate : ∀ (x : B) (v : E x), (∀ w : E x, metric x v w = 0) → v = 0

variable [PseudoRiemannianBundle (B := B) (E := E)]

/-- The metric as a family of continuous bilinear maps. -/
abbrev metric (x : B) : E x →L[ℝ] E x →L[ℝ] ℝ :=
  PseudoRiemannianBundle.metric (B := B) (E := E) x

/-- The fiberwise pseudo-inner-product \(g_x(v,w)\). -/
abbrev pseudoInner (x : B) (v w : E x) : ℝ :=
  (PseudoRiemannianBundle.metric (B := B) (E := E) x) v w

omit [TopologicalSpace B] in
@[simp] lemma pseudoInner_def (x : B) (v w : E x) :
    pseudoInner (B := B) (E := E) x v w = metric (B := B) (E := E) x v w := rfl

omit [TopologicalSpace B] in
lemma pseudoInner_symm (x : B) (v w : E x) :
    pseudoInner (B := B) (E := E) x v w = pseudoInner (B := B) (E := E) x w v := by
  simpa [pseudoInner] using (PseudoRiemannianBundle.symm (B := B) (E := E) x v w)

omit [TopologicalSpace B] in
lemma pseudoInner_nondegenerate (x : B) (v : E x) (hv : ∀ w : E x,
    pseudoInner (B := B) (E := E) x v w = 0) :
    v = 0 :=
  PseudoRiemannianBundle.nondegenerate (B := B) (E := E) x v hv

end PseudoRiemannianBundle

/-! ### Smoothness of pseudo-Riemannian structures on vector bundles -/

section ContMDiff

open scoped ENat

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n n' : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [PseudoRiemannianBundle (B := B) (E := E)]

variable (IB n F E) in
/-- A pseudo-Riemannian bundle is `C^n` if its fiberwise bilinear form depends `C^n`-smoothly on the
base point, when seen as a section of the bundle of bilinear forms. -/
class IsContMDiffPseudoRiemannianBundle : Prop where
  exists_contMDiff :
    ∃ g : Π x : B, E x →L[ℝ] E x →L[ℝ] ℝ,
      ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
        (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (g b))
      ∧ ∀ (x : B) (v w : E x), pseudoInner (B := B) (E := E) x v w = g x v w

lemma IsContMDiffPseudoRiemannianBundle.of_le
    [h : IsContMDiffPseudoRiemannianBundle (IB := IB) (n := n) (F := F) (E := E)] (h' : n' ≤ n) :
    IsContMDiffPseudoRiemannianBundle (IB := IB) (n := n') (F := F) (E := E) := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  exact ⟨g, g_smooth.of_le h', hg⟩

instance [IsContMDiffPseudoRiemannianBundle (IB := IB) (n := (1 : WithTop ℕ∞)) (F := F) (E := E)] :
    IsContMDiffPseudoRiemannianBundle (IB := IB) (n := (0 : WithTop ℕ∞)) (F := F) (E := E) :=
  IsContMDiffPseudoRiemannianBundle.of_le (IB := IB) (F := F) (E := E) zero_le_one

instance [IsContMDiffPseudoRiemannianBundle (IB := IB) (n := (2 : WithTop ℕ∞)) (F := F) (E := E)] :
    IsContMDiffPseudoRiemannianBundle (IB := IB) (n := (1 : WithTop ℕ∞)) (F := F) (E := E) :=
  IsContMDiffPseudoRiemannianBundle.of_le (IB := IB) (F := F) (E := E) one_le_two

instance [IsContMDiffPseudoRiemannianBundle (IB := IB) (n := (3 : WithTop ℕ∞)) (F := F) (E := E)] :
    IsContMDiffPseudoRiemannianBundle (IB := IB) (n := (2 : WithTop ℕ∞)) (F := F) (E := E) :=
  IsContMDiffPseudoRiemannianBundle.of_le (IB := IB) (n := (3 : WithTop ℕ∞)) (F := F) (E := E)
    (by norm_cast)

section ContMDiffPairing

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [h : IsContMDiffPseudoRiemannianBundle (IB := IB) (n := n) (F := F) (E := E)]
  {b : M → B} {v w : ∀ x, E (b x)} {s : Set M} {x : M}

/-- Given two smooth maps into the same fibers of a pseudo-Riemannian bundle, their pairing is smooth. -/
lemma ContMDiffWithinAt.pseudoInner_bundle
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) s x) :
    ContMDiffWithinAt IM 𝓘(ℝ) n (fun m ↦ pseudoInner (B := B) (E := E) (b m) (v m) (w m)) s x := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  have hb : ContMDiffWithinAt IM IB n b s x := by
    simp only [contMDiffWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ)) n
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (g (b m) (v m) (w m))) s x := by
    apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F)
    · exact ContMDiffAt.comp_contMDiffWithinAt x g_smooth.contMDiffAt hb
    · exact hv
    · exact hw
  simp only [contMDiffWithinAt_totalSpace] at this
  exact this.2

lemma ContMDiffAt.pseudoInner_bundle
    (hv : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) x) :
    ContMDiffAt IM 𝓘(ℝ) n (fun m ↦ pseudoInner (B := B) (E := E) (b m) (v m) (w m)) x :=
  ContMDiffWithinAt.pseudoInner_bundle (IB := IB) (n := n) (F := F) (E := E) hv hw

lemma ContMDiffOn.pseudoInner_bundle
    (hv : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) s) :
    ContMDiffOn IM 𝓘(ℝ) n (fun m ↦ pseudoInner (B := B) (E := E) (b m) (v m) (w m)) s :=
  fun x hx ↦ (hv x hx).pseudoInner_bundle (IB := IB) (n := n) (F := F) (E := E) (hw x hx)

lemma ContMDiff.pseudoInner_bundle
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)))
    (hw : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E))) :
    ContMDiff IM 𝓘(ℝ) n (fun m ↦ pseudoInner (B := B) (E := E) (b m) (v m) (w m)) :=
  fun x ↦ (hv x).pseudoInner_bundle (IB := IB) (n := n) (F := F) (E := E) (hw x)

end ContMDiffPairing

end ContMDiff

end Bundle

/-! ## Pseudo-Riemannian Metric -/

/-!
Constructs a `QuadraticForm` on the tangent space `TₓM` at a point `x` from the
value of a pseudo-Riemannian metric at that point.
(O'Neill, p. 47, "The function q: V → R given by q(v) = b(v,v) is the associated quadratic
form of b.")
The pseudo-Riemannian metric is given by `val`, a family of continuous bilinear forms
`gₓ: TₓM × TₓM → ℝ` for each `x : M`.
The quadratic form `Qₓ` at `x` is defined as `Qₓ(v) = gₓ(v,v)`.
The associated symmetric bilinear form required by `QuadraticForm.exists_companion'`
is `Bₓ(v,w) = gₓ(v,w) + gₓ(w,v)`. Given the symmetry `symm`, this is `2 * gₓ(v,w)`.
-/
namespace PseudoRiemannianMetric

/--
Turn a (curried) bilinear form `val` on each tangent space into the associated quadratic form
`v ↦ val x v v`.

This helper is intentionally public: it is the bridge between a bundled description of a metric
(`val` + symmetry) and quadratic-form invariants such as `QuadraticForm.negDim`.
-/
def valToQuadraticForm
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type w} [TopologicalSpace H]
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H}
    (val : ∀ (x : M), TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ))
    (symm : ∀ (x : M) (v w : TangentSpace I x), (val x v) w = (val x w) v)
    (x : M) : QuadraticForm ℝ (TangentSpace I x) where
  toFun v := val x v v
  toFun_smul a v := by
    simp only [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_smul]
  exists_companion' :=
      ⟨LinearMap.mk₂ ℝ (fun v y => val x v y + val x y v)
        (fun v₁ v₂ y => by simp only [map_add, add_apply]; ring)
        (fun a v y => by simp only [map_smul, smul_apply]; ring_nf; exact Eq.symm (smul_add ..))
        (fun v y₁ y₂ => by simp only [map_add, add_apply]; ring)
        (fun a v y => by simp only [map_smul, smul_apply]; ring_nf; exact Eq.symm (smul_add ..)),
            by
              intro v y
              simp only [LinearMap.mk₂_apply, ContinuousLinearMap.map_add,
                ContinuousLinearMap.add_apply, symm x]
              ring⟩

end PseudoRiemannianMetric

/-- A general (pseudo-)metric tensor of smoothness class `C^n` on a manifold `M`.

This is the common core shared by Riemannian and pseudo-Riemannian metrics:
a smoothly varying symmetric, nondegenerate bilinear form on each tangent space.

The pseudo-Riemannian notion will extend this with an index/signature constancy condition. -/
@[ext]
structure MetricTensor
    (E : Type v) (H : Type w) (M : Type w) (n : WithTop ℕ∞)
    [inst_norm_grp_E : NormedAddCommGroup E]
    [inst_norm_sp_E : NormedSpace ℝ E]
    [inst_top_H : TopologicalSpace H]
    [inst_top_M : TopologicalSpace M]
    [inst_chart_M : ChartedSpace H M]
    (I : ModelWithCorners ℝ E H)
    [inst_mani : IsManifold I (n + 1) M]
    [inst_mani1 : IsManifold I 1 M] :
      Type _ where
  /-- The metric tensor at each point `x : M`, represented as a continuous linear map
      `TₓM →L[ℝ] (TₓM →L[ℝ] ℝ)`. Applying it twice, `(val x v) w`, yields `gₓ(v, w)`. -/
  val : ∀ (x : M), TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)
  /-- Symmetry: `gₓ(v, w) = gₓ(w, v)`. -/
  symm : ∀ (x : M) (v w : TangentSpace I x), (val x v) w = (val x w) v
  /-- Non-degeneracy: if `gₓ(v, w) = 0` for all `w`, then `v = 0`. -/
  nondegenerate : ∀ (x : M) (v : TangentSpace I x), (∀ w : TangentSpace I x,
    (val x v) w = 0) → v = 0
  /-- Smoothness of the metric tensor as a smooth section of the bundle of bilinear forms.

  We follow the same pattern as Mathlib's Riemannian metric API, using `TotalSpace.mk'`
  for the bundled map. -/
  contMDiff : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
    (fun x ↦
      TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (val x))

namespace MetricTensor

variable {E : Type v} {H : Type w} {M : Type w} {n : WithTop ℕ∞}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H}
variable [IsManifold I (n + 1) M] [IsManifold I 1 M]

/-- Coercion from `MetricTensor` to its `val` function. -/
instance coeFunInst : CoeFun (MetricTensor E H M n I)
    (fun _ => ∀ x : M, TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)) where
  coe g := g.val

/-- The bilinear form on `TₓM` associated to a metric tensor. -/
def toBilinForm (g : MetricTensor E H M n I) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x) where
  toFun := fun v =>
    { toFun := fun w => g.val x v w
      map_add' := fun w₁ w₂ => by simp only [ContinuousLinearMap.map_add]
      map_smul' := fun c w => by simp only [map_smul, smul_eq_mul, RingHom.id_apply] }
  map_add' := fun v₁ v₂ => by
    ext w
    simp only [map_add, add_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
  map_smul' := fun c v => by
    ext w
    simp only [map_smul, coe_smul', Pi.smul_apply, smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk,
      RingHom.id_apply, LinearMap.smul_apply]

/-- The quadratic form `v ↦ gₓ(v,v)` associated to a metric tensor. -/
abbrev toQuadraticForm (g : MetricTensor E H M n I) (x : M) :
    QuadraticForm ℝ (TangentSpace I x) :=
  PseudoRiemannianMetric.valToQuadraticForm g.val g.symm x

@[simp]
lemma toBilinForm_apply (g : MetricTensor E H M n I) (x : M) (v w : TangentSpace I x) :
    toBilinForm g x v w = g.val x v w := rfl

@[simp]
lemma toQuadraticForm_apply (g : MetricTensor E H M n I) (x : M) (v : TangentSpace I x) :
    toQuadraticForm g x v = g.val x v v := rfl

@[simp]
lemma toBilinForm_isSymm (g : MetricTensor E H M n I) (x : M) :
    (toBilinForm g x).IsSymm := by
  refine { eq := ?_ }
  intro v w
  simp [toBilinForm_apply, g.symm x v w]

@[simp]
lemma toBilinForm_nondegenerate (g : MetricTensor E H M n I) (x : M) :
    (toBilinForm g x).Nondegenerate := by
  unfold LinearMap.BilinForm.Nondegenerate LinearMap.Nondegenerate
    LinearMap.SeparatingLeft LinearMap.SeparatingRight
  constructor
  · intro v hv
    simp_rw [toBilinForm_apply] at hv
    exact g.nondegenerate x v hv
  · intro v hv
    simp_rw [toBilinForm_apply] at hv
    have hw : ∀ w : TangentSpace I x, (g.val x v) w = 0 := by
      intro w
      -- symmetry gives `g(v,w)=g(w,v)=0`
      simpa [g.symm x v w] using hv w
    exact g.nondegenerate x v hw

/-- The value `gₓ(v,w)` of a metric tensor. -/
def inner (g : MetricTensor E H M n I) (x : M) (v w : TangentSpace I x) : ℝ :=
  g.val x v w

@[simp]
lemma inner_apply (g : MetricTensor E H M n I) (x : M) (v w : TangentSpace I x) :
    inner g x v w = g.val x v w := rfl

/-! ## Flat / sharp (musical isomorphisms) -/

/-- Index lowering map `v ↦ gₓ(v, -)` as a continuous linear map. -/
abbrev flatL (g : MetricTensor E H M n I) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  g.val x

/-- Index lowering map `v ↦ gₓ(v, -)` as a linear map. -/
abbrev flat (g : MetricTensor E H M n I) (x : M) :
    TangentSpace I x →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  (g.flatL x).toLinearMap

@[simp]
lemma flat_apply (g : MetricTensor E H M n I) (x : M) (v w : TangentSpace I x) :
    (flat g x v) w = g.val x v w := rfl

@[simp]
lemma flatL_apply (g : MetricTensor E H M n I) (x : M) (v w : TangentSpace I x) :
    (flatL g x v) w = g.val x v w := rfl

lemma flat_inj (g : MetricTensor E H M n I) (x : M) : Function.Injective (flat g x) := by
  rw [← LinearMap.ker_eq_bot]
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply g.nondegenerate x v
  intro w
  exact DFunLike.congr_fun hv w

lemma flatL_inj (g : MetricTensor E H M n I) (x : M) : Function.Injective (flatL g x) :=
  flat_inj g x

section FiniteDimensional

variable [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]

lemma flatL_surj (g : MetricTensor E H M n I) (x : M) : Function.Surjective (g.flatL x) := by
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inst_tangent_findim x
  have h_finrank_eq :
      finrank ℝ (TangentSpace I x) = finrank ℝ (TangentSpace I x →L[ℝ] ℝ) := by
    have h_dual_eq : finrank ℝ (TangentSpace I x →L[ℝ] ℝ) =
        finrank ℝ (Module.Dual ℝ (TangentSpace I x)) := by
      let to_dual : (TangentSpace I x →L[ℝ] ℝ) → Module.Dual ℝ (TangentSpace I x) :=
        fun f => f.toLinearMap
      let from_dual : Module.Dual ℝ (TangentSpace I x) → (TangentSpace I x →L[ℝ] ℝ) :=
        fun f => ContinuousLinearMap.mk f (by
          apply LinearMap.continuous_of_finiteDimensional)
      let equiv : (TangentSpace I x →L[ℝ] ℝ) ≃ₗ[ℝ] Module.Dual ℝ (TangentSpace I x) :=
        { toFun := to_dual
          invFun := from_dual
          map_add' := fun f g => by ext v; rfl
          map_smul' := fun c f => by ext v; rfl
          left_inv := fun f => by ext v; rfl
          right_inv := fun f => by ext v; rfl }
      exact LinearEquiv.finrank_eq equiv
    rw [h_dual_eq, ← Subspace.dual_finrank_eq]
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_finrank_eq).mp (flatL_inj g x)

/-- `flatEquiv` as a continuous linear equivalence. -/
noncomputable def flatEquiv (g : MetricTensor E H M n I) (x : M) :
    TangentSpace I x ≃L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  LinearEquiv.toContinuousLinearEquiv <|
    LinearEquiv.ofBijective (g.flatL x).toLinearMap ⟨g.flatL_inj x, g.flatL_surj x⟩

@[simp]
lemma flatEquiv_apply (g : MetricTensor E H M n I) (x : M) (v w : TangentSpace I x) :
    (g.flatEquiv x v) w = g.val x v w := rfl

/-- Index raising equivalence as the inverse of `flatEquiv`. -/
noncomputable def sharpEquiv (g : MetricTensor E H M n I) (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) ≃L[ℝ] TangentSpace I x :=
  (g.flatEquiv x).symm

noncomputable def sharpL (g : MetricTensor E H M n I) (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x :=
  (g.sharpEquiv x).toContinuousLinearMap

/-- Index raising map `sharp` as a linear map. -/
noncomputable def sharp (g : MetricTensor E H M n I) (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] TangentSpace I x :=
  (g.sharpEquiv x).toLinearEquiv.toLinearMap

@[simp]
lemma sharpL_apply_flatL (g : MetricTensor E H M n I) (x : M) (v : TangentSpace I x) :
    g.sharpL x (g.flatL x v) = v :=
  (g.flatEquiv x).left_inv v

@[simp]
lemma flatL_apply_sharpL (g : MetricTensor E H M n I) (x : M)
    (ω : TangentSpace I x →L[ℝ] ℝ) :
    g.flatL x (g.sharpL x ω) = ω :=
  (g.flatEquiv x).right_inv ω

@[simp]
lemma flat_sharp_apply (g : MetricTensor E H M n I) (x : M)
    (ω : TangentSpace I x →L[ℝ] ℝ) :
    g.flat x (g.sharp x ω) = ω := by
  ext v
  have h := congrArg (fun f : TangentSpace I x →L[ℝ] ℝ => f v) (flatL_apply_sharpL (g := g) x ω)
  simpa [flat, flatL, sharp, sharpL] using h

@[simp]
lemma sharp_flat_apply (g : MetricTensor E H M n I) (x : M) (v : TangentSpace I x) :
    g.sharp x (g.flat x v) = v := by
  have h := sharpL_apply_flatL (g := g) x v
  simpa [sharp, sharpL, flat, flatL] using h

/-- Metric evaluated at `sharp ω₁` and `sharp ω₂`. -/
@[simp]
lemma apply_sharp_sharp (g : MetricTensor E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) :
    g.val x (g.sharpL x ω₁) (g.sharpL x ω₂) = ω₁ (g.sharpL x ω₂) := by
  rw [← flatL_apply (g := g) x (g.sharpL x ω₁)]
  rw [flatL_apply_sharpL (g := g) x ω₁]

/-- Metric evaluated at `v` and `sharp ω`. -/
lemma apply_vec_sharp (g : MetricTensor E H M n I) (x : M) (v : TangentSpace I x)
    (ω : TangentSpace I x →L[ℝ] ℝ) :
    g.val x v (g.sharpL x ω) = ω v := by
  rw [g.symm x v (g.sharpL x ω)]
  rw [← flatL_apply (g := g) x (g.sharpL x ω)]
  rw [flatL_apply_sharpL (g := g) x ω]

/-! ## Cotangent metric induced by `g` -/

/-- The induced metric value on the cotangent space at `x`. -/
noncomputable def cotangentMetricVal (g : MetricTensor E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) : ℝ :=
  g.val x (g.sharpL x ω₁) (g.sharpL x ω₂)

@[simp] lemma cotangentMetricVal_eq_apply_sharp (g : MetricTensor E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) :
    cotangentMetricVal g x ω₁ ω₂ = ω₁ (g.sharpL x ω₂) := by
  simp [cotangentMetricVal]

lemma cotangentMetricVal_symm (g : MetricTensor E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) :
    cotangentMetricVal g x ω₁ ω₂ = cotangentMetricVal g x ω₂ ω₁ := by
  unfold cotangentMetricVal
  rw [g.symm x (g.sharpL x ω₁) (g.sharpL x ω₂)]

/-- The induced cotangent metric as a bilinear form. -/
noncomputable def cotangentToBilinForm (g : MetricTensor E H M n I) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x →L[ℝ] ℝ) where
  toFun ω₁ :=
    { toFun := fun ω₂ => cotangentMetricVal g x ω₁ ω₂
      map_add' := fun ω₂ ω₃ => by simp [cotangentMetricVal, ContinuousLinearMap.map_add]
      map_smul' := fun c ω₂ => by simp [cotangentMetricVal, map_smul, smul_eq_mul, RingHom.id_apply] }
  map_add' := fun ω₁ ω₂ => by
    ext ω₃
    simp [cotangentMetricVal, ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
  map_smul' := fun c ω₁ => by
    ext ω₂
    simp [cotangentMetricVal, ContinuousLinearMap.smul_apply,
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]

/-- The induced cotangent metric as a quadratic form. -/
noncomputable def cotangentToQuadraticForm (g : MetricTensor E H M n I) (x : M) :
    QuadraticForm ℝ (TangentSpace I x →L[ℝ] ℝ) where
  toFun ω := cotangentMetricVal g x ω ω
  toFun_smul a ω := by
    simp [cotangentMetricVal, ContinuousLinearMap.smul_apply]
    ring
  exists_companion' :=
    ⟨LinearMap.mk₂ ℝ (fun ω₁ ω₂ =>
        cotangentMetricVal g x ω₁ ω₂ + cotangentMetricVal g x ω₂ ω₁)
      (fun ω₁ ω₂ ω₃ => by simp [cotangentMetricVal, map_add, add_apply]; ring)
      (fun a ω₁ ω₂ => by
        simp [cotangentMetricVal, map_smul, smul_apply]
        ring_nf)
      (fun ω₁ ω₂ ω₃ => by simp [cotangentMetricVal, map_add, add_apply]; ring)
      (fun a ω₁ ω₂ => by
        simp [cotangentMetricVal, map_smul, smul_apply]
        ring_nf),
      by
        intro ω₁ ω₂
        simp [LinearMap.mk₂_apply, cotangentMetricVal, ContinuousLinearMap.map_add,
          ContinuousLinearMap.add_apply]
        ring⟩

@[simp]
lemma cotangentToBilinForm_apply (g : MetricTensor E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) :
    cotangentToBilinForm g x ω₁ ω₂ = cotangentMetricVal g x ω₁ ω₂ := rfl

@[simp]
lemma cotangentToQuadraticForm_apply (g : MetricTensor E H M n I) (x : M)
    (ω : TangentSpace I x →L[ℝ] ℝ) :
    cotangentToQuadraticForm g x ω = cotangentMetricVal g x ω ω := rfl

@[simp]
lemma cotangentToBilinForm_isSymm (g : MetricTensor E H M n I) (x : M) :
    (cotangentToBilinForm g x).IsSymm := by
  refine { eq := ?_ }
  intro ω₁ ω₂
  simpa [cotangentToBilinForm_apply] using (cotangentMetricVal_symm (g := g) x ω₁ ω₂)

/-- Nondegeneracy of the cotangent metric. -/
lemma cotangentMetricVal_nondegenerate (g : MetricTensor E H M n I) (x : M)
    (ω : TangentSpace I x →L[ℝ] ℝ)
    (h : ∀ v : TangentSpace I x →L[ℝ] ℝ, cotangentMetricVal g x ω v = 0) :
    ω = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have h_forall : ∀ w : TangentSpace I x, ω w = 0 := by
    intro w
    let ω' : TangentSpace I x →L[ℝ] ℝ := g.flatL x w
    have this : g.sharpL x ω' = w := by
      simp [ω']
    have h_apply : cotangentMetricVal g x ω ω' = 0 := h ω'
    simp [cotangentMetricVal_eq_apply_sharp] at h_apply
    simpa [this] using h_apply
  exact h_forall v

@[simp]
lemma cotangentToBilinForm_nondegenerate (g : MetricTensor E H M n I) (x : M) :
    (cotangentToBilinForm g x).Nondegenerate := by
  unfold LinearMap.BilinForm.Nondegenerate LinearMap.Nondegenerate
    LinearMap.SeparatingLeft LinearMap.SeparatingRight
  constructor
  · intro ω hω
    apply cotangentMetricVal_nondegenerate (g := g) x ω
    intro v
    exact hω v
  · intro ω hω
    apply cotangentMetricVal_nondegenerate (g := g) x ω
    intro v
    have hv : ∀ y : TangentSpace I x →L[ℝ] ℝ, ((g.cotangentToBilinForm x) ω) y = 0 := by
      intro y
      rw [LinearMap.BilinForm.isSymm_def.mp (cotangentToBilinForm_isSymm (g := g) x)]
      simp [hω]
    exact hv v

/-- The cotangent quadratic form is equivalent to the tangent quadratic form via `sharp`. -/
theorem cotangentToQuadraticForm_equivalent_toQuadraticForm (g : MetricTensor E H M n I) (x : M) :
    (g.cotangentToQuadraticForm x).Equivalent (g.toQuadraticForm x) := by
  classical
  refine ⟨?_⟩
  refine
    { toLinearEquiv := (g.sharpEquiv x).toLinearEquiv
      map_app' := fun ω => ?_ }
  simp [cotangentToQuadraticForm_apply, cotangentMetricVal, toQuadraticForm, sharpEquiv, sharpL]

/-! ## Pointwise index (finite-dimensional) -/

/-- The (negative) index of a metric tensor at a point, defined as the negative index of the
associated quadratic form `v ↦ gₓ(v,v)`.

This is a pointwise invariant; it need not be locally constant. -/
noncomputable def index (g : MetricTensor E H M n I) (x : M) : ℕ :=
  (g.toQuadraticForm x).negDim

omit inst_tangent_findim in
@[simp] lemma index_def (g : MetricTensor E H M n I) (x : M) :
    g.index x = (g.toQuadraticForm x).negDim := rfl

end FiniteDimensional

end MetricTensor

/-- A pseudo-Riemannian metric of smoothness class `C^n` on a manifold `M` modelled on `(E, H)`
with model `I`. This structure defines a smoothly varying, non-degenerate, symmetric,
continuous bilinear form `gₓ` of constant negative dimension on the tangent space `TₓM`
at each point `x`. Requires `M` to be `C^{n+1}` smooth.
This structure formalizes O'Neill's Definition 3.1 (p. 54) of a metric tensor `g` on `M`
as a "symmetric non-degenerate (0,2) tensor field on M of constant index."
Each `gₓ` is a scalar product (O'Neill, Definition 20, p. 47) on `TₓM`. -/
@[ext]
structure PseudoRiemannianMetric
    (E : Type v) (H : Type w) (M : Type w) (n : WithTop ℕ∞)
    [inst_norm_grp_E : NormedAddCommGroup E]
    [inst_norm_sp_E : NormedSpace ℝ E]
    [inst_top_H : TopologicalSpace H]
    [inst_top_M : TopologicalSpace M]
    [inst_chart_M : ChartedSpace H M]
    (I : ModelWithCorners ℝ E H)
    [inst_mani : IsManifold I (n + 1) M]
    [inst_mani1 : IsManifold I 1 M]
    [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)] :
      Type _ extends toMetricTensor : MetricTensor E H M n I where
  /-- The negative dimension (`QuadraticForm.negDim`) of the metric's quadratic form is
      locally constant. On a connected manifold, this implies it is constant globally. -/
  negDim_isLocallyConstant :
    IsLocallyConstant (fun x : M =>
      have : FiniteDimensional ℝ (TangentSpace I x) := inferInstance
      (PseudoRiemannianMetric.valToQuadraticForm val symm x).negDim)

namespace PseudoRiemannianMetric

variable {E : Type v} {H : Type w} {M : Type w} {n : WithTop ℕ∞}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H}
variable [IsManifold I (n + 1) M] [IsManifold I 1 M]
variable [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]

/-! ## Predicate typeclass: pseudo-Riemannian manifolds -/

/-- Prop-valued predicate recording existence of a `C^n` pseudo-Riemannian metric.

This is the “there exists a metric” statement, *without* making any noncanonical choice.  For
bundle-first development, the primary data is still an explicit `PseudoRiemannianMetric` (or a
`Bundle.PseudoRiemannianBundle` + smoothness instance). -/
class HasPseudoRiemannianMetric : Prop where
  out : Nonempty (PseudoRiemannianMetric E H M n I)

instance (g : PseudoRiemannianMetric E H M n I) :
    HasPseudoRiemannianMetric (E := E) (H := H) (M := M) (n := n) (I := I) :=
  ⟨⟨g⟩⟩

theorem hasPseudoRiemannianMetric_iff :
    HasPseudoRiemannianMetric (E := E) (H := H) (M := M) (n := n) (I := I) ↔
      Nonempty (PseudoRiemannianMetric E H M n I) :=
  ⟨fun h => h.out, fun h => ⟨h⟩⟩

theorem hasPseudoRiemannianMetric_iff_exists :
    HasPseudoRiemannianMetric (E := E) (H := H) (M := M) (n := n) (I := I) ↔
      ∃ _ : PseudoRiemannianMetric E H M n I, True :=
  ⟨fun h => by
      rcases h.out with ⟨g⟩
      exact ⟨g, trivial⟩,
    fun h => by
      rcases h with ⟨g, -⟩
      exact ⟨⟨g⟩⟩⟩

/-- Typeclass carrying a *chosen* pseudo-Riemannian metric (as opposed to the mere existence
predicate `HasPseudoRiemannianMetric`). This is the convenient form for downstream constructions. -/
class PseudoRiemannianManifold : Type _ where
  metric : PseudoRiemannianMetric E H M n I

/-- The chosen pseudo-Riemannian metric on a manifold typeclass. -/
abbrev pseudoRiemannianMetric [PseudoRiemannianManifold (E := E) (H := H) (M := M) (n := n) (I := I)] :
    PseudoRiemannianMetric E H M n I :=
  (PseudoRiemannianManifold.metric (E := E) (H := H) (M := M) (n := n) (I := I))

instance [PseudoRiemannianManifold (E := E) (H := H) (M := M) (n := n) (I := I)] :
    HasPseudoRiemannianMetric (E := E) (H := H) (M := M) (n := n) (I := I) :=
  ⟨⟨pseudoRiemannianMetric (E := E) (H := H) (M := M) (n := n) (I := I)⟩⟩

/-- Given a pseudo-Riemannian metric `g` on manifold `M` and a point `x : M`,
this function constructs a bilinear form on the tangent space at `x`.
For tangent vectors `u v : T_x M`, the bilinear form is given by:
`g_x(u, v) = g(x)(u, v)` -/
abbrev toBilinForm (g : PseudoRiemannianMetric E H M n I) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x) :=
  MetricTensor.toBilinForm (g := g.toMetricTensor) x

/-- Convert a pseudo-Riemannian metric at a point `x` to a quadratic form `v ↦ gₓ(v, v)`. -/
abbrev toQuadraticForm (g : PseudoRiemannianMetric E H M n I) (x : M) :
    QuadraticForm ℝ (TangentSpace I x) :=
  MetricTensor.toQuadraticForm (g := g.toMetricTensor) x

/-- Coercion from PseudoRiemannianMetric to its function representation. -/
instance coeFunInst : CoeFun (PseudoRiemannianMetric E H M n I)
        (fun _ => ∀ x : M, TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)) where
  coe g := g.val

@[simp]
lemma toBilinForm_apply (g : PseudoRiemannianMetric E H M n I) (x : M)
    (v w : TangentSpace I x) :
  toBilinForm g x v w = g.val x v w := rfl

@[simp]
lemma toQuadraticForm_apply (g : PseudoRiemannianMetric E H M n I) (x : M)
    (v : TangentSpace I x) :
  toQuadraticForm g x v = g.val x v v := rfl

/-! ## Index (negative inertia) -/

/-- The (negative) index of a pseudo-Riemannian metric at a point, defined as the negative index of
the associated quadratic form `v ↦ gₓ(v,v)`. -/
noncomputable def index (g : PseudoRiemannianMetric E H M n I) (x : M) : ℕ :=
  (g.toQuadraticForm x).negDim

@[simp]
lemma index_def (g : PseudoRiemannianMetric E H M n I) (x : M) :
  g.index x = (g.toQuadraticForm x).negDim := rfl

lemma index_isLocallyConstant (g : PseudoRiemannianMetric E H M n I) :
    IsLocallyConstant (fun x : M => g.index x) := by
  simpa [index, toQuadraticForm] using g.negDim_isLocallyConstant

lemma index_eq_of_isPreconnected (g : PseudoRiemannianMetric E H M n I) {s : Set M}
    (hs : IsPreconnected s) {x y : M} (hx : x ∈ s) (hy : y ∈ s) :
    g.index x = g.index y :=
  (index_isLocallyConstant (g := g)).apply_eq_of_isPreconnected hs hx hy

lemma index_eq_of_preconnectedSpace [PreconnectedSpace M] (g : PseudoRiemannianMetric E H M n I)
    (x y : M) :
    g.index x = g.index y :=
  (index_isLocallyConstant (g := g)).apply_eq_of_preconnectedSpace x y

lemma index_eq_of_mem_connectedComponent (g : PseudoRiemannianMetric E H M n I) (x y : M)
    (hy : y ∈ connectedComponent x) :
    g.index y = g.index x :=
  (index_isLocallyConstant (g := g)).apply_eq_of_isPreconnected
    (isConnected_connectedComponent.isPreconnected)
    hy (mem_connectedComponent : x ∈ connectedComponent x)

@[simp]
lemma toBilinForm_isSymm (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (toBilinForm g x).IsSymm := by
  refine { eq := ?_ }
  intro v w; simp only [toBilinForm_apply]; exact g.symm x v w

@[simp]
lemma toBilinForm_nondegenerate (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (toBilinForm g x).Nondegenerate := by
  unfold LinearMap.BilinForm.Nondegenerate LinearMap.Nondegenerate
    LinearMap.SeparatingLeft LinearMap.SeparatingRight
  constructor
  · intro v hv; simp_rw [toBilinForm_apply] at hv; exact g.nondegenerate x v hv
  · intro v hv; simp_rw [toBilinForm_apply] at hv;
    have hw : ∀ (w : TangentSpace I x), ((g.val x) v) w = 0 := by
      intro w
      simpa [g.symm x v w] using hv w
    exact g.nondegenerate x v hw

/-- The inner product (or scalar product) on the tangent space at point `x`
  induced by the pseudo-Riemannian metric `g`. This is `gₓ(v, w)`. -/
def inner (g : PseudoRiemannianMetric E H M n I) (x : M) (v w : TangentSpace I x) : ℝ :=
  g.val x v w

@[simp]
lemma inner_apply (g : PseudoRiemannianMetric E H M n I) (x : M) (v w : TangentSpace I x) :
  inner g x v w = g.val x v w := rfl

/-! ## Flat -/

section Flat

/-- The "musical" isomorphism (index lowering) `v ↦ gₓ(v, -)`.
The non-degeneracy of `gₓ` (O'Neill, Def 17 (3), p. 46) means its matrix representation
is invertible (O'Neill, Lemma 19, p. 47), and that this map is an isomorphism from `TₓM`
to its dual. -/
def flat (g : PseudoRiemannianMetric E H M n I) (x : M) :
    TangentSpace I x →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  MetricTensor.flat (g := g.toMetricTensor) x

@[simp]
lemma flat_apply (g : PseudoRiemannianMetric E H M n I) (x : M) (v w : TangentSpace I x) :
  (flat g x v) w = g.val x v w := by rfl

/-- The musical isomorphism as a continuous linear map. -/
abbrev flatL (g : PseudoRiemannianMetric E H M n I) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  MetricTensor.flatL (g := g.toMetricTensor) x

@[simp]
lemma flatL_apply (g : PseudoRiemannianMetric E H M n I) (x : M) (v w : TangentSpace I x) :
    (flatL g x v) w = g.val x v w := rfl

@[simp]
lemma flat_inj (g : PseudoRiemannianMetric E H M n I) (x : M) :
    Function.Injective (flat g x) := by
  rw [← LinearMap.ker_eq_bot]; apply LinearMap.ker_eq_bot'.mpr
  intro v hv; apply g.nondegenerate x v; intro w; exact DFunLike.congr_fun hv w

@[simp]
lemma flatL_inj (g : PseudoRiemannianMetric E H M n I) (x : M) :
    Function.Injective (flatL g x) :=
  flat_inj g x

@[simp]
lemma flatL_surj
    (g : PseudoRiemannianMetric E H M n I) (x : M) :
    Function.Surjective (g.flatL x) := by
  simpa [PseudoRiemannianMetric.flatL] using
    MetricTensor.flatL_surj (g := g.toMetricTensor) x

/-- The "musical" isomorphism (index lowering) from `TₓM` to its dual,
as a continuous linear equivalence. This equivalence is a direct result of `gₓ` being
a non-degenerate bilinear form (O'Neill, Def 17(3), p. 46; Lemma 19, p. 47). -/
noncomputable def flatEquiv
    (g : PseudoRiemannianMetric E H M n I)
    (x : M) :
    TangentSpace I x ≃L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  MetricTensor.flatEquiv (g := g.toMetricTensor) x

lemma coe_flatEquiv
  (g : PseudoRiemannianMetric E H M n I) (x : M) :
  (g.flatEquiv x : TangentSpace I x →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ)) = g.flatL x := rfl

@[simp]
lemma flatEquiv_apply
  (g : PseudoRiemannianMetric E H M n I) (x : M) (v w : TangentSpace I x) :
  (g.flatEquiv x v) w = g.val x v w := rfl

end Flat

/-! ## Sharp -/

section Sharp

/-- The "musical" isomorphism (index raising) from the dual of `TₓM` to `TₓM`.
This is the inverse of `flatEquiv g x`, and its existence as an isomorphism is
guaranteed by the non-degeneracy of `gₓ` (O'Neill, Lemma 19, p. 47). -/
noncomputable def sharpEquiv
    (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) ≃L[ℝ] TangentSpace I x :=
  MetricTensor.sharpEquiv (g := g.toMetricTensor) x

/-- The index raising map `sharp` as a continuous linear map. -/
noncomputable def sharpL
    (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x :=
  MetricTensor.sharpL (g := g.toMetricTensor) x

lemma sharpL_eq_toContinuousLinearMap
    (g : PseudoRiemannianMetric E H M n I) (x : M) :
  g.sharpL x = (g.sharpEquiv x).toContinuousLinearMap := rfl

lemma coe_sharpEquiv
    (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (g.sharpEquiv x : (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x) = g.sharpL x := rfl

/-- The index raising map `sharp` as a linear map. -/
noncomputable def sharp
    (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] TangentSpace I x :=
  MetricTensor.sharp (g := g.toMetricTensor) x

@[simp]
lemma sharpL_apply_flatL
    (g : PseudoRiemannianMetric E H M n I) (x : M) (v : TangentSpace I x) :
    g.sharpL x (g.flatL x v) = v := by
  simp [PseudoRiemannianMetric.sharpL, PseudoRiemannianMetric.flatL,
    MetricTensor.sharpL_apply_flatL (g := g.toMetricTensor) x v]

@[simp]
lemma flatL_apply_sharpL
    (g : PseudoRiemannianMetric E H M n I) (x : M) (ω : TangentSpace I x →L[ℝ] ℝ) :
    g.flatL x (g.sharpL x ω) = ω := by
  simp [PseudoRiemannianMetric.sharpL, PseudoRiemannianMetric.flatL,
    MetricTensor.flatL_apply_sharpL (g := g.toMetricTensor) x ω]

/-- Applying `sharp` then `flat` recovers the original covector. -/
@[simp]
lemma flat_sharp_apply
    (g : PseudoRiemannianMetric E H M n I) (x : M) (ω : TangentSpace I x →L[ℝ] ℝ) :
    g.flat x (g.sharp x ω) = ω := by
  simp [PseudoRiemannianMetric.flat, PseudoRiemannianMetric.sharp,
    MetricTensor.flat_sharp_apply (g := g.toMetricTensor) x ω]

@[simp]
lemma sharp_flat_apply
    (g : PseudoRiemannianMetric E H M n I) (x : M) (v : TangentSpace I x) :
    g.sharp x (g.flat x v) = v := by
  have h : g.sharpL x (g.flatL x v) = v :=
    PseudoRiemannianMetric.sharpL_apply_flatL (g := g) x v
  convert h using 1

/-- The metric evaluated at `sharp ω₁` and `sharp ω₂`. -/
@[simp]
lemma apply_sharp_sharp
    (g : PseudoRiemannianMetric E H M n I) (x : M) (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) :
    g.val x (g.sharpL x ω₁) (g.sharpL x ω₂) = ω₁ (g.sharpL x ω₂) := by
  simp [PseudoRiemannianMetric.sharpL]

/-- The metric evaluated at `v` and `sharp ω`. -/
lemma apply_vec_sharp
    (g : PseudoRiemannianMetric E H M n I) (x : M) (v : TangentSpace I x)
    (ω : TangentSpace I x →L[ℝ] ℝ) :
    g.val x v (g.sharpL x ω) = ω v := by
  simp [PseudoRiemannianMetric.sharpL,
    MetricTensor.apply_vec_sharp (g := g.toMetricTensor) x v ω]

end Sharp

/-! ## Cotangent -/
section Cotangent

variable {E : Type v} {H : Type w} {M : Type w} {n : WithTop ℕ∞}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H}
variable [IsManifold I (n + 1) M] [IsManifold I 1 M]
variable [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]

/-- The value of the induced metric on the cotangent space at point `x`. -/
noncomputable def cotangentMetricVal (g : PseudoRiemannianMetric E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) : ℝ :=
  g.val x (g.sharpL x ω₁) (g.sharpL x ω₂)

@[simp]
lemma cotangentMetricVal_eq_apply_sharp (g : PseudoRiemannianMetric E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) :
  cotangentMetricVal g x ω₁ ω₂ = ω₁ (g.sharpL x ω₂) := by
  rw [cotangentMetricVal, apply_sharp_sharp]

lemma cotangentMetricVal_symm (g : PseudoRiemannianMetric E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) :
  cotangentMetricVal g x ω₁ ω₂ = cotangentMetricVal g x ω₂ ω₁ := by
  unfold cotangentMetricVal
  rw [g.symm x (g.sharpL x ω₁) (g.sharpL x ω₂)]

/-- The induced metric on the cotangent space at point `x` as a bilinear form.
For covectors `ω₁` and `ω₂`, this gives `g(ω₁^#, ω₂^#)`, where `ω^#` is
the "sharp" musical isomorphism raising indices. -/
noncomputable def cotangentToBilinForm (g : PseudoRiemannianMetric E H M n I) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x →L[ℝ] ℝ) where
  toFun ω₁ := { toFun := λ ω₂ => cotangentMetricVal g x ω₁ ω₂,
                map_add' := λ ω₂ ω₃ => by
                  simp only [cotangentMetricVal,
                    ContinuousLinearMap.map_add],
                map_smul' := λ c ω₂ => by
                  simp only [cotangentMetricVal,
                    map_smul, smul_eq_mul, RingHom.id_apply] }
  map_add' := λ ω₁ ω₂ => by
    ext ω₃
    simp only [cotangentMetricVal,
      ContinuousLinearMap.map_add,
      ContinuousLinearMap.add_apply,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
  map_smul' := λ c ω₁ => by
    ext ω₂
    simp only [cotangentMetricVal,
      ContinuousLinearMap.map_smul,
      ContinuousLinearMap.smul_apply,
      LinearMap.coe_mk, AddHom.coe_mk,
      RingHom.id_apply, LinearMap.smul_apply]

/-- The cometric on the cotangent space T_x*M at `x`, expressed as a quadratic form.
It is induced by the pseudo-Riemannian metric on the tangent space T_xM. -/
noncomputable def cotangentToQuadraticForm (g : PseudoRiemannianMetric E H M n I) (x : M) :
    QuadraticForm ℝ (TangentSpace I x →L[ℝ] ℝ) where
  toFun ω := cotangentMetricVal g x ω ω
  toFun_smul a ω := by
    simp only [cotangentMetricVal,
      ContinuousLinearMap.map_smul,
      ContinuousLinearMap.smul_apply,
      smul_smul]
  exists_companion' :=
      ⟨LinearMap.mk₂ ℝ (fun ω₁ ω₂ =>
          cotangentMetricVal g x ω₁ ω₂ + cotangentMetricVal g x ω₂ ω₁)
        (fun ω₁ ω₂ ω₃ => by simp only [cotangentMetricVal, map_add, add_apply]; ring)
        (fun a ω₁ ω₂ => by
          simp only [cotangentMetricVal, map_smul, smul_apply];
          ring_nf; exact Eq.symm (smul_add ..))
        (fun ω₁ ω₂ ω₃ => by
          simp only [cotangentMetricVal, map_add, add_apply]; ring)
        (fun a ω₁ ω₂ => by
          simp only [cotangentMetricVal, map_smul, smul_apply]; ring_nf;
          exact Eq.symm (smul_add ..)),
          by
            intro ω₁ ω₂
            simp only [LinearMap.mk₂_apply, cotangentMetricVal]
            simp only [ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply]
            ring⟩

@[simp]
lemma cotangentToBilinForm_apply (g : PseudoRiemannianMetric E H M n I) (x : M)
    (ω₁ ω₂ : TangentSpace I x →L[ℝ] ℝ) :
  cotangentToBilinForm g x ω₁ ω₂ = cotangentMetricVal g x ω₁ ω₂ := rfl

@[simp]
lemma cotangentToQuadraticForm_apply (g : PseudoRiemannianMetric E H M n I) (x : M)
    (ω : TangentSpace I x →L[ℝ] ℝ) :
  cotangentToQuadraticForm g x ω = cotangentMetricVal g x ω ω := rfl

@[simp]
lemma cotangentToBilinForm_isSymm (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (cotangentToBilinForm g x).IsSymm := by
  refine { eq := ?_ }
  intro ω₁ ω₂; simp only [cotangentToBilinForm_apply]; exact cotangentMetricVal_symm g x ω₁ ω₂

/-- The cotangent metric is non-degenerate: if `cotangentMetricVal g x ω v = 0` for all `v`,
    then `ω = 0`. -/
lemma cotangentMetricVal_nondegenerate (g : PseudoRiemannianMetric E H M n I) (x : M)
    (ω : TangentSpace I x →L[ℝ] ℝ) (h : ∀ v : TangentSpace I x →L[ℝ] ℝ,
      cotangentMetricVal g x ω v = 0) :
    ω = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have h_forall : ∀ w : TangentSpace I x, ω w = 0 := by
    intro w
    let ω' : TangentSpace I x →L[ℝ] ℝ := g.flatL x w
    have this : g.sharpL x ω' = w := by
      simp only [ω', sharpL_apply_flatL]
    have h_apply : cotangentMetricVal g x ω ω' = 0 := h ω'
    simp only [cotangentMetricVal_eq_apply_sharp] at h_apply
    rw [this] at h_apply
    exact h_apply
  exact h_forall v

@[simp]
lemma cotangentToBilinForm_nondegenerate (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (cotangentToBilinForm g x).Nondegenerate := by
  unfold LinearMap.BilinForm.Nondegenerate LinearMap.Nondegenerate
    LinearMap.SeparatingLeft LinearMap.SeparatingRight
  constructor
  · intro ω hω
    apply cotangentMetricVal_nondegenerate g x ω
    intro v
    exact hω v
  · intro ω hω
    apply cotangentMetricVal_nondegenerate g x ω
    intro v
    have hv : ∀ (y : TangentSpace I x →L[ℝ] ℝ), ((g.cotangentToBilinForm x) ω) y = 0 := by
      intro y; rw [LinearMap.BilinForm.isSymm_def.mp (cotangentToBilinForm_isSymm g x)]; simp [hω]
    exact hv v

/-! ## Cotangent signature -/

/-- The cotangent quadratic form is equivalent to the tangent quadratic form via `sharp`. -/
theorem cotangentToQuadraticForm_equivalent_toQuadraticForm
    (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (g.cotangentToQuadraticForm x).Equivalent (g.toQuadraticForm x) := by
  refine ⟨?_⟩
  refine
    { toLinearEquiv := (g.sharpEquiv x).toLinearEquiv
      map_app' := fun ω => ?_ }
  have hsh : g.sharpL x ω = g.sharpEquiv x ω := rfl
  simp [cotangentToQuadraticForm_apply, cotangentMetricVal, toQuadraticForm, hsh]

theorem cotangent_signature_eq (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (g.cotangentToQuadraticForm x).signature = (g.toQuadraticForm x).signature :=
  QuadraticForm.signature_eq_of_equivalent (E := (TangentSpace I x →L[ℝ] ℝ))
    (E₂ := TangentSpace I x) (cotangentToQuadraticForm_equivalent_toQuadraticForm (g := g) x)

theorem cotangent_negDim_eq (g : PseudoRiemannianMetric E H M n I) (x : M) :
    (g.cotangentToQuadraticForm x).negDim = (g.toQuadraticForm x).negDim :=
  congrArg QuadraticForm.Signature.neg (cotangent_signature_eq (g := g) x)

end Cotangent

end PseudoRiemannianMetric
end PseudoRiemannianMetric
