/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.RepresentationTheory.TauCetiPort.Compact.Averaging
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# Convolution operators on `L²` of a compact group

For a continuous kernel `k : C(G, 𝕜)` on a compact group `G` and an `L²` function `f`, the
convolution

`(k * f) x = ∫ y, k (x * y⁻¹) * f y ∂(haarProb G)`

makes sense at *every* point `x`, not merely almost everywhere: the integral is the `L²` pairing of
`f` against the continuous function `y ↦ conj (k (x * y⁻¹))`, and that function varies continuously
with `x` in the uniform norm. Convolution therefore smooths `L²(G)` into `C(G)`, and the resulting
map `convolutionCLM k : L²(G) →L[𝕜] C(G)` is bounded by the uniform norm of the kernel.

Composing with `ContinuousMap.toLp` gives the convolution operator `convolutionOperator k` on
`L²(G)`. Its properties are proved here: it is self-adjoint when the kernel is symmetric
(`k g⁻¹ = conj (k g)`), it commutes with right translation, and it is a **compact operator**.
Together these say that the eigenspace of a symmetric convolution operator at a nonzero eigenvalue
is a *finite-dimensional* right-translation-invariant subspace of `L²(G)` all of whose elements
have continuous representatives, and that such eigenspaces exist; the eigenspaces at *all*
eigenvalues, the possibly infinite-dimensional kernel included, together span a dense subspace.
This is how the Peter-Weyl theorem manufactures finite-dimensional representations of `G` without
presupposing that any exist.

## Main definitions

* `TauCeti.convolutionCLM`: convolution against a continuous kernel, as a bounded linear map
  `Lp 𝕜 2 (haarProb G) →L[𝕜] C(G, 𝕜)`.
* `TauCeti.convolutionOperator`: the convolution operator `f ↦ k * f` on `Lp 𝕜 2 (haarProb G)`.

## Main statements

* `TauCeti.convolutionCLM_apply_apply`: the pointwise formula
  `(k * f) x = ∫ y, k (x * y⁻¹) * f y`.
* `TauCeti.convolutionCLM_toLp_apply`: the translated formula
  `(k * f) x = ∫ z, k z * f (z⁻¹ * x)` when `f` is continuous.
* `TauCeti.norm_convolutionCLM_apply_le`: `‖k * f‖_∞ ≤ ‖k‖_∞ * ‖f‖₂`, so convolution against a
  continuous kernel is bounded from `L²(G)` into the uniform norm of `C(G)`.
* `TauCeti.isSelfAdjoint_convolutionOperator`: a symmetric kernel gives a self-adjoint operator.
* `TauCeti.convolutionCLM_compMeasurePreserving_mul_right`: convolution commutes with right
  translation.
* `TauCeti.isCompactOperator_convolutionCLM` and `TauCeti.isCompactOperator_convolutionOperator`:
  convolution against a continuous kernel is a compact operator, into `C(G)` and into `L²(G)`.
* `TauCeti.finiteDimensional_eigenspace_convolutionOperator`: consequently the eigenspace of
  `convolutionOperator k` at a nonzero eigenvalue is finite-dimensional.
* `TauCeti.ae_eq_smul_convolutionCLM_of_mem_eigenspace`: an eigenvector at a nonzero eigenvalue is
  almost everywhere equal to the continuous function `μ⁻¹ • (k * f)`.
* `TauCeti.convolutionCLM_eq_zero_of_mem_eigenspace_zero`: an eigenvector at the eigenvalue `0`
  convolves to the zero function.
* `TauCeti.compMeasurePreserving_mul_right_mem_eigenspace_convolutionOperator`: the eigenspaces are
  invariant under right translation.
* `TauCeti.exists_hasEigenvalue_ne_zero_convolutionOperator`: a nonzero symmetric convolution
  operator has a nonzero eigenvalue, so such an eigenspace really exists.
* `TauCeti.orthogonalComplement_iSup_eigenspaces_convolutionOperator_eq_bot`: the eigenspaces of a
  symmetric convolution operator, at every eigenvalue, span a dense subspace of `L²(G)`.

## Implementation notes

Compactness is read off the same kernel sections, with no separate uniform-continuity argument:
the value `(k * f) x` is the `L²` pairing of `f` against the section at `x`, and the sections
depend continuously on `x` *in the uniform norm*, so the images of the unit ball are equicontinuous
by inspection. Arzelà-Ascoli (`BoundedContinuousFunction.arzela_ascoli`) then applies, in
`G →ᵇ 𝕜`, to which `C(G, 𝕜)` is isometric because `G` is compact.

Mathlib's `convolution` (`Mathlib/Analysis/Convolution.lean`) is the convolution of two functions
on an *additive* group against a bilinear pairing, and does not apply here: `G` is multiplicative,
and one of the two arguments is an `L²` class rather than a function. The kernel sections
`y ↦ conj (k (x * y⁻¹))` are assembled with `ContinuousMap.curry`, whose continuity is exactly the
statement that they depend continuously on `x`, so no uniform-continuity argument is needed.

Self-adjointness is proved by writing `convolutionOperator k H`, for a *continuous* `H`, as the
Bochner integral of the kernel sections weighted by `H`, and then extending to all of `L²(G)` by
density (`ContinuousMap.toLp_denseRange`). The more direct Fubini argument on `G × G` is not
available: the product of two Borel spaces is Borel only under a second-countability hypothesis,
which a compact group need not satisfy, whereas a continuous function on a compact space is
integrable with no such hypothesis (`TauCeti.integrable_continuousMap`).

The conjugation in the kernel sections is bookkeeping for Mathlib's convention that the inner
product is conjugate linear in its first argument; it is invisible in the pointwise formula
`convolutionCLM_apply_apply`.

## References

This is the opening of Layer 5 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), which names
`convolutionOperator`, its self-adjointness for a symmetric kernel (there spelled
`convolutionOperator_isSelfAdjoint`, renamed here to `isSelfAdjoint_convolutionOperator` for the
predicate-prefix convention), its compactness (`convolutionOperator_isCompact`) and the finite
dimensionality of its nonzero eigenspaces (`convolutionOperator_eigenspace_finiteDimensional`) as
milestones on the non-circular route to the Peter-Weyl theorem.

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC (2016), §5.2.
* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapters 3-4.
-/

public section

open MeasureTheory
open scoped BoundedContinuousFunction InnerProductSpace

namespace TauCeti

section CompactGroup

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-! ### Preliminaries on `L²` against normalized Haar measure -/

/-- Normalized Haar measure is a probability measure, so passing from the uniform norm to the `L²`
norm is a contraction. -/
private theorem norm_toLp_le (F : C(G, 𝕜)) :
    ‖ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜 F‖ ≤ ‖F‖ := by
  have hmass : measureUnivNNReal (haarProb G) = 1 :=
    ENNReal.coe_inj.1 (by simp [coe_measureUnivNNReal])
  have hop : ‖(ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜)‖ ≤ 1 := by
    simpa [hmass] using ContinuousMap.toLp_norm_le (E := 𝕜) (p := 2) (𝕜 := 𝕜) (haarProb G)
  calc ‖ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜 F‖
      ≤ ‖(ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜)‖ * ‖F‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖F‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg F)
    _ = ‖F‖ := one_mul _

/-- Mathlib's `L2.inner_def` computes an inner product in `L²` as the integral of the pointwise
inner products `⟪a, b⟫ = conj a * b`. This is its specialization to a first argument coming from a
continuous function. -/
private theorem inner_toLp_left (F : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) :
    ⟪ContinuousMap.toLp 2 (haarProb G) 𝕜 F, f⟫_𝕜
      = ∫ x, (starRingEnd 𝕜) (F x) * f x ∂(haarProb G) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (haarProb G) (𝕜 := 𝕜) F] with x hx
  rw [hx, RCLike.inner_apply]
  ring

/-! ### The kernel sections

The section of the kernel `k` at `x` is `y ↦ conj (k (x * y⁻¹))`. Currying the continuous function
`(x, y) ↦ conj (k (x * y⁻¹))` on `G × G` is exactly the statement that the section depends
continuously on `x` in the uniform norm. -/

/-- The conjugated kernel sections `x ↦ (y ↦ conj (k (x * y⁻¹)))`, as a continuous map into
`C(G, 𝕜)`. -/
private noncomputable def convSectionCM (k : C(G, 𝕜)) : C(G, C(G, 𝕜)) :=
  ContinuousMap.curry
    (star (k.comp ⟨fun p : G × G => p.1 * p.2⁻¹, continuous_fst.mul continuous_snd.inv⟩))

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem convSectionCM_apply (k : C(G, 𝕜)) (x y : G) :
    convSectionCM k x y = (starRingEnd 𝕜) (k (x * y⁻¹)) :=
  (rfl)

omit [MeasurableSpace G] [BorelSpace G] in
private theorem norm_convSectionCM_le (k : C(G, 𝕜)) (x : G) : ‖convSectionCM k x‖ ≤ ‖k‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg k)).2 fun y => by
    rw [convSectionCM_apply, RCLike.norm_conj]
    exact k.norm_coe_le_norm _

/-- The conjugated kernel sections, read in `L²(G)`. -/
private noncomputable def convSection (k : C(G, 𝕜)) : C(G, Lp 𝕜 2 (haarProb G)) :=
  ⟨fun x => ContinuousMap.toLp 2 (haarProb G) 𝕜 (convSectionCM k x),
    (ContinuousMap.toLp (E := 𝕜) 2 (haarProb G) 𝕜).continuous.comp (convSectionCM k).continuous⟩

private theorem convSection_apply (k : C(G, 𝕜)) (x : G) :
    convSection k x = ContinuousMap.toLp 2 (haarProb G) 𝕜 (convSectionCM k x) :=
  (rfl)

private theorem norm_convSection_le (k : C(G, 𝕜)) (x : G) : ‖convSection k x‖ ≤ ‖k‖ :=
  (norm_toLp_le _).trans (norm_convSectionCM_le k x)

/-! ### Convolution as a map into continuous functions -/

private noncomputable def convolutionₗ (k : C(G, 𝕜)) : Lp 𝕜 2 (haarProb G) →ₗ[𝕜] C(G, 𝕜) where
  toFun f := ⟨fun x => ⟪convSection k x, f⟫_𝕜, (convSection k).continuous.inner continuous_const⟩
  map_add' f₁ f₂ := by ext x; exact inner_add_right (convSection k x) f₁ f₂
  map_smul' c f := by ext x; exact inner_smul_right (convSection k x) f c

private theorem norm_convolutionₗ_le (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) :
    ‖convolutionₗ k f‖ ≤ ‖k‖ * ‖f‖ :=
  (ContinuousMap.norm_le _ (by positivity)).2 fun x =>
    (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_convSection_le k x) (norm_nonneg f))

/-- **Convolution against a continuous kernel**, as a bounded linear map from `L²(G)` into `C(G)`.

The value at `x` is the `L²` pairing of `f` against the kernel section at `x`, so it is defined at
every point of `G` and depends continuously on that point: convolving an `L²` class against a
continuous kernel produces a genuine continuous function, not another almost-everywhere class. -/
noncomputable def convolutionCLM (k : C(G, 𝕜)) : Lp 𝕜 2 (haarProb G) →L[𝕜] C(G, 𝕜) :=
  LinearMap.mkContinuous (convolutionₗ k) ‖k‖ (norm_convolutionₗ_le k)

private theorem convolutionCLM_apply_apply' (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) (x : G) :
    convolutionCLM k f x = ⟪convSection k x, f⟫_𝕜 :=
  (rfl)

/-- **The pointwise formula for convolution against a continuous kernel.** -/
theorem convolutionCLM_apply_apply (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) (x : G) :
    convolutionCLM k f x = ∫ y, k (x * y⁻¹) * f y ∂(haarProb G) := by
  rw [convolutionCLM_apply_apply', convSection_apply, inner_toLp_left]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [convSectionCM_apply, RCLike.conj_conj]

/-- **Convolution written by translating the function rather than the kernel**:
`(k * f) x = ∫ z, k z * f (z⁻¹ * x)`.

This form follows from `TauCeti.convolutionCLM_apply_apply` by the substitution `y = z⁻¹ * x`,
which preserves normalized Haar measure because it is inversion followed by right translation. -/
theorem convolutionCLM_toLp_apply (k f : C(G, 𝕜)) (x : G) :
    convolutionCLM k (ContinuousMap.toLp 2 (haarProb G) 𝕜 f) x
      = ∫ z, k z * f (z⁻¹ * x) ∂(haarProb G) := by
  set F : G → 𝕜 := fun y => k (x * y⁻¹) * f y with hFdef
  have hcoe : convolutionCLM k (ContinuousMap.toLp 2 (haarProb G) 𝕜 f) x
      = ∫ y, F y ∂(haarProb G) := by
    rw [convolutionCLM_apply_apply]
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (haarProb G) (𝕜 := 𝕜) f] with y hy
    rw [hy]
  rw [hcoe]
  calc ∫ y, F y ∂(haarProb G)
      = ∫ z, F (z * x) ∂(haarProb G) := (integral_mul_right_eq_self F x).symm
    _ = ∫ z, F (z⁻¹ * x) ∂(haarProb G) :=
        (integral_inv_eq_self (fun w => F (w * x)) (haarProb G)).symm
    _ = ∫ z, k z * f (z⁻¹ * x) ∂(haarProb G) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        have hz : x * (z⁻¹ * x)⁻¹ = z := by group
        rw [hFdef]
        simp only [hz]

/-- The error of an approximation of `f` by `k * f`, when the kernel `k` has unit mass: the average
against `k` of the increments of `f`. -/
theorem convolutionCLM_toLp_sub_apply (k f : C(G, 𝕜))
    (hk : ∫ g, k g ∂(haarProb G) = 1) (x : G) :
    convolutionCLM k (ContinuousMap.toLp 2 (haarProb G) 𝕜 f) x - f x
      = ∫ z, k z * (f (z⁻¹ * x) - f x) ∂(haarProb G) := by
  have h₁ : Integrable (fun z : G => k z * f (z⁻¹ * x)) (haarProb G) :=
    integrable_continuousMap G
      (⟨fun z => k z * f (z⁻¹ * x),
        k.continuous.mul (f.continuous.comp (continuous_id.inv.mul continuous_const))⟩ :
        C(G, 𝕜))
  have h₂ : Integrable (fun z : G => k z * f x) (haarProb G) :=
    (integrable_continuousMap G k).mul_const _
  rw [convolutionCLM_toLp_apply]
  have hsplit : ∫ z, k z * (f (z⁻¹ * x) - f x) ∂(haarProb G)
      = (∫ z, k z * f (z⁻¹ * x) ∂(haarProb G)) - ∫ z, k z * f x ∂(haarProb G) := by
    simp_rw [mul_sub]
    exact integral_sub h₁ h₂
  rw [hsplit, integral_mul_const, hk, one_mul]

private theorem integrable_convolution_integrand (k : C(G, 𝕜))
    (f : Lp 𝕜 2 (haarProb G)) (x : G) :
    Integrable (fun y => k (x * y⁻¹) * f y) (haarProb G) := by
  refine (L2.integrable_inner (convSection k x) f).congr ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (haarProb G) (𝕜 := 𝕜)
    (convSectionCM k x)] with y hy
  rw [convSection_apply, hy, RCLike.inner_apply, convSectionCM_apply, RCLike.conj_conj,
    mul_comm]

/-- Convolution is zero when its kernel is zero. -/
@[simp]
theorem convolutionCLM_zero :
    convolutionCLM (G := G) (0 : C(G, 𝕜)) = 0 := by
  ext f x
  simp [convolutionCLM_apply_apply]

/-- Convolution is additive in its kernel. -/
@[simp]
theorem convolutionCLM_add (k₁ k₂ : C(G, 𝕜)) :
    convolutionCLM (k₁ + k₂) = convolutionCLM k₁ + convolutionCLM k₂ := by
  ext f x
  simp only [add_apply, ContinuousMap.add_apply, convolutionCLM_apply_apply]
  rw [← integral_add (integrable_convolution_integrand k₁ f x)
    (integrable_convolution_integrand k₂ f x)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => add_mul _ _ _)

/-- Convolution is compatible with scalar multiplication of its kernel. -/
@[simp]
theorem convolutionCLM_smul (c : 𝕜) (k : C(G, 𝕜)) :
    convolutionCLM (c • k) = c • convolutionCLM k := by
  ext f x
  simp only [smul_apply, ContinuousMap.smul_apply, smul_eq_mul, convolutionCLM_apply_apply]
  rw [← integral_const_mul c]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_assoc _ _ _)

/-- **Convolution is bounded from `L²(G)` into `C(G)`:** the uniform norm of `k * f` is at most the
product of the uniform norm of the kernel and the `L²` norm of `f`. Normalized Haar measure is a
probability measure, so no measure-dependent constant appears. -/
theorem norm_convolutionCLM_apply_le (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) :
    ‖convolutionCLM k f‖ ≤ ‖k‖ * ‖f‖ :=
  norm_convolutionₗ_le k f

/-- The operator norm of convolution against `k`, as a map into the uniform norm of `C(G)`, is at
most the uniform norm of `k`. -/
theorem norm_convolutionCLM_le (k : C(G, 𝕜)) : ‖convolutionCLM (G := G) k‖ ≤ ‖k‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg k) _

/-! ### The convolution operator on `L²(G)` -/

/-- **The convolution operator** `f ↦ k * f` on `L²(G)`, for a continuous kernel `k`.

It factors through `C(G)`: `convolutionCLM` produces a continuous function, and
`ContinuousMap.toLp` reads that function back into `L²(G)`. -/
noncomputable def convolutionOperator (k : C(G, 𝕜)) :
    Lp 𝕜 2 (haarProb G) →L[𝕜] Lp 𝕜 2 (haarProb G) :=
  (ContinuousMap.toLp 2 (haarProb G) 𝕜).comp (convolutionCLM k)

/-- The convolution operator is `convolutionCLM` followed by `ContinuousMap.toLp`. -/
theorem convolutionOperator_apply (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) :
    convolutionOperator k f = ContinuousMap.toLp 2 (haarProb G) 𝕜 (convolutionCLM k f) :=
  (rfl)

/-- The convolution operator is zero when its kernel is zero. -/
@[simp]
theorem convolutionOperator_zero :
    convolutionOperator (G := G) (0 : C(G, 𝕜)) = 0 := by
  ext f
  simp [convolutionOperator_apply]

/-- The convolution operator is additive in its kernel. -/
@[simp]
theorem convolutionOperator_add (k₁ k₂ : C(G, 𝕜)) :
    convolutionOperator (k₁ + k₂) = convolutionOperator k₁ + convolutionOperator k₂ := by
  ext f
  simp [convolutionOperator_apply]

/-- The convolution operator is compatible with scalar multiplication of its kernel. -/
@[simp]
theorem convolutionOperator_smul (c : 𝕜) (k : C(G, 𝕜)) :
    convolutionOperator (c • k) = c • convolutionOperator k := by
  ext f
  simp [convolutionOperator_apply]

/-- The convolution operator is represented, almost everywhere, by the continuous function
`convolutionCLM k f`. -/
theorem coeFn_convolutionOperator (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G)) :
    convolutionOperator k f =ᵐ[haarProb G] convolutionCLM k f :=
  ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (haarProb G) (𝕜 := 𝕜) _

/-- The convolution operator on `L²(G)` has operator norm at most the uniform norm of its
kernel. -/
theorem norm_convolutionOperator_le (k : C(G, 𝕜)) : ‖convolutionOperator (G := G) k‖ ≤ ‖k‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg k) fun f => by
    rw [convolutionOperator_apply]
    exact (norm_toLp_le _).trans (norm_convolutionCLM_apply_le k f)

/-! ### Self-adjointness for a symmetric kernel

For a *continuous* weight `H` the kernel sections may be averaged against `H`, giving a Bochner
integral in `C(G)` and, after `ContinuousMap.toLp`, one in `L²(G)`. Symmetry of the kernel
identifies that average with `k * H`, which is the adjoint relation on the dense subspace of
continuous functions; the general case follows because both sides of the relation are continuous in
their second argument. -/

/-- The kernel sections weighted by a continuous function `H`. -/
private noncomputable def weightedSectionsCM (k H : C(G, 𝕜)) : C(G, C(G, 𝕜)) :=
  ⟨fun x => H x • convSectionCM k x, H.continuous.smul (convSectionCM k).continuous⟩

/-- The kernel sections weighted by a continuous function `H`, read in `L²(G)`. -/
private noncomputable def weightedSections (k H : C(G, 𝕜)) : C(G, Lp 𝕜 2 (haarProb G)) :=
  ⟨fun x => H x • convSection k x, H.continuous.smul (convSection k).continuous⟩

private theorem integrable_weightedSectionsCM (k H : C(G, 𝕜)) :
    Integrable (fun x => H x • convSectionCM k x) (haarProb G) :=
  integrable_continuousMap G (weightedSectionsCM k H)

private theorem integrable_weightedSections (k H : C(G, 𝕜)) :
    Integrable (fun x => H x • convSection k x) (haarProb G) :=
  integrable_continuousMap G (weightedSections k H)

/-- The `L²`-valued average of the weighted kernel sections is the image under
`ContinuousMap.toLp` of their `C(G)`-valued average. -/
private theorem integral_weightedSections (k H : C(G, 𝕜)) :
    ∫ x, H x • convSection k x ∂(haarProb G)
      = ContinuousMap.toLp 2 (haarProb G) 𝕜
          (∫ x, H x • convSectionCM k x ∂(haarProb G)) := by
  rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_weightedSectionsCM k H)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_smul, convSection_apply]

/-- The `C(G)`-valued average of the weighted kernel sections, evaluated at a point. -/
private theorem integral_weightedSectionsCM_apply (k H : C(G, 𝕜)) (y : G) :
    (∫ x, H x • convSectionCM k x ∂(haarProb G)) y
      = ∫ x, H x * (starRingEnd 𝕜) (k (x * y⁻¹)) ∂(haarProb G) := by
  have hcomm := (ContinuousMap.evalCLM (R := 𝕜) (M := 𝕜) y).integral_comp_comm
    (integrable_weightedSectionsCM k H)
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, convSectionCM_apply,
    smul_eq_mul] at hcomm
  exact hcomm.symm

/-- The pairing of `convolutionOperator k f` against a continuous function is the pairing of `f`
against the average of the weighted kernel sections. -/
private theorem inner_convolutionOperator_toLp (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G))
    (H : C(G, 𝕜)) :
    ⟪convolutionOperator k f, ContinuousMap.toLp 2 (haarProb G) 𝕜 H⟫_𝕜
      = ⟪f, ∫ x, H x • convSection k x ∂(haarProb G)⟫_𝕜 := by
  rw [convolutionOperator_apply, inner_toLp_left,
    ← integral_inner (integrable_weightedSections k H) f]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (haarProb G) (𝕜 := 𝕜) H] with x hx
  rw [hx, convolutionCLM_apply_apply', inner_smul_right, ← inner_conj_symm f (convSection k x),
    mul_comm]

/-- **Self-adjointness of the convolution operator for a symmetric kernel.** A kernel is symmetric
when `k g⁻¹ = conj (k g)`; the pointwise identity `conj (k (x * y⁻¹)) = k (y * x⁻¹)` it supplies is
what turns the average of the kernel sections weighted by `H` back into `k * H`. -/
theorem isSelfAdjoint_convolutionOperator (k : C(G, 𝕜))
    (hk : ∀ g : G, k g⁻¹ = (starRingEnd 𝕜) (k g)) :
    IsSelfAdjoint (convolutionOperator k) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f h
  have key : ∀ H : C(G, 𝕜),
      ⟪convolutionOperator k f, ContinuousMap.toLp 2 (haarProb G) 𝕜 H⟫_𝕜
        = ⟪f, convolutionOperator k (ContinuousMap.toLp 2 (haarProb G) 𝕜 H)⟫_𝕜 := by
    intro H
    rw [inner_convolutionOperator_toLp, integral_weightedSections, convolutionOperator_apply]
    congr 2
    ext y
    rw [integral_weightedSectionsCM_apply, convolutionCLM_apply_apply]
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (haarProb G) (𝕜 := 𝕜) H] with x hx
    have hsym : (starRingEnd 𝕜) (k (x * y⁻¹)) = k (y * x⁻¹) := by
      rw [← hk (x * y⁻¹), mul_inv_rev, inv_inv]
    rw [hx, hsym, mul_comm]
  have hcont₁ : Continuous fun u : Lp 𝕜 2 (haarProb G) => ⟪convolutionOperator k f, u⟫_𝕜 :=
    continuous_const.inner continuous_id
  have hcont₂ : Continuous fun u : Lp 𝕜 2 (haarProb G) => ⟪f, convolutionOperator k u⟫_𝕜 :=
    continuous_const.inner (convolutionOperator k).continuous
  exact congrFun
    ((ContinuousMap.toLp_denseRange (E := 𝕜) (p := 2) (haarProb G) 𝕜
      (by simp)).equalizer hcont₁ hcont₂ (funext key)) h

/-! ### Equivariance under right translation -/

/-- **Convolution commutes with right translation.** Translating `f` on the right by `g₀` and then
convolving is the same as convolving and then translating the result, because the kernel
`(x, y) ↦ k (x * y⁻¹)` is unchanged by right translation of both variables.

This is what makes every eigenspace of a convolution operator a right-translation-invariant
subspace of `L²(G)`, hence, once the eigenspace is known to be finite-dimensional, the carrier of a
finite-dimensional representation of `G`. -/
theorem convolutionCLM_compMeasurePreserving_mul_right (k : C(G, 𝕜))
    (f : Lp 𝕜 2 (haarProb G)) (g₀ x : G) :
    convolutionCLM k
        (Lp.compMeasurePreserving (· * g₀) (measurePreserving_mul_right (haarProb G) g₀) f) x
      = convolutionCLM k f (x * g₀) := by
  have hg : ∀ y : G, x * g₀ * (y * g₀)⁻¹ = x * y⁻¹ := fun y => by group
  rw [convolutionCLM_apply_apply, convolutionCLM_apply_apply,
    ← integral_mul_right_eq_self (fun y => k (x * g₀ * y⁻¹) * (f : G → 𝕜) y) g₀]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_compMeasurePreserving (E := 𝕜) (p := 2) f
    (measurePreserving_mul_right (haarProb G) g₀)] with y hy
  rw [hy, hg y]
  rfl

/-- **The convolution operator commutes with right translation on `L²(G)`.** This is
`convolutionCLM_compMeasurePreserving_mul_right` read in `L²(G)`; it is the form in which the
eigenspaces of `convolutionOperator k` are seen to be right-translation-invariant. -/
theorem convolutionOperator_compMeasurePreserving_mul_right (k : C(G, 𝕜))
    (f : Lp 𝕜 2 (haarProb G)) (g₀ : G) :
    convolutionOperator k
        (Lp.compMeasurePreserving (· * g₀) (measurePreserving_mul_right (haarProb G) g₀) f)
      = Lp.compMeasurePreserving (· * g₀) (measurePreserving_mul_right (haarProb G) g₀)
          (convolutionOperator k f) := by
  have hqmp := (measurePreserving_mul_right (haarProb G) g₀).quasiMeasurePreserving
  rw [Lp.ext_iff]
  refine (coeFn_convolutionOperator k _).trans ?_
  refine Filter.EventuallyEq.symm (((Lp.coeFn_compMeasurePreserving (E := 𝕜) (p := 2)
    (convolutionOperator k f) (measurePreserving_mul_right (haarProb G) g₀)).trans
      (hqmp.ae_eq_comp (coeFn_convolutionOperator k f))).trans ?_)
  exact Filter.Eventually.of_forall fun y =>
    (convolutionCLM_compMeasurePreserving_mul_right k f g₀ y).symm

/-! ### Compactness of the convolution operator

Convolution against a continuous kernel carries the closed unit ball of `L²(G)` to a family of
continuous functions bounded by `‖k‖` and equicontinuous: the increment of `k * f` between two
points is controlled by the distance between the corresponding kernel sections, uniformly in `f`.
The Arzelà-Ascoli theorem makes that family relatively compact in `C(G)`, hence in `L²(G)`. -/

/-- The increment of `k * f` between two points is at most the distance between the two kernel
sections, scaled by `‖f‖`. Uniformity in `f` over a bounded set is what makes the convolutions of
that set equicontinuous. -/
private theorem norm_convolutionCLM_apply_sub_apply_le (k : C(G, 𝕜)) (f : Lp 𝕜 2 (haarProb G))
    (x y : G) :
    ‖convolutionCLM k f x - convolutionCLM k f y‖
      ≤ ‖convSection k x - convSection k y‖ * ‖f‖ := by
  rw [convolutionCLM_apply_apply', convolutionCLM_apply_apply', ← inner_sub_left]
  exact norm_inner_le_norm _ _

/-- The image of the closed unit ball of `L²(G)` under convolution against `k`, carried by the
isometry `ContinuousMap.isometryEquivBoundedOfCompact` into the bounded continuous functions on
`G`, where Mathlib's Arzelà-Ascoli theorem lives. -/
private noncomputable def convolutionUnitBallImage (k : C(G, 𝕜)) : Set (G →ᵇ 𝕜) :=
  (fun f : Lp 𝕜 2 (haarProb G) =>
      ContinuousMap.isometryEquivBoundedOfCompact G 𝕜 (convolutionCLM k f)) ''
    Metric.closedBall 0 1

/-- Convolutions of the closed unit ball take values in the closed ball of radius `‖k‖`. -/
private theorem convolutionUnitBallImage_apply_mem_closedBall (k : C(G, 𝕜)) (F : G →ᵇ 𝕜) (x : G)
    (hF : F ∈ convolutionUnitBallImage k) : F x ∈ Metric.closedBall (0 : 𝕜) ‖k‖ := by
  obtain ⟨f, hf, rfl⟩ := hF
  rw [Metric.mem_closedBall, dist_zero_right] at hf ⊢
  rw [ContinuousMap.isometryEquivBoundedOfCompact_apply,
    BoundedContinuousFunction.mkOfCompact_apply]
  refine ((convolutionCLM k f).norm_coe_le_norm x).trans ?_
  calc ‖convolutionCLM k f‖ ≤ ‖k‖ * ‖f‖ := norm_convolutionCLM_apply_le k f
    _ ≤ ‖k‖ * 1 := by gcongr
    _ = ‖k‖ := mul_one _

/-- Convolutions of the closed unit ball form an equicontinuous family: the kernel sections depend
continuously on the point in the *uniform* norm, and pairing them against a vector of norm at most
one can only shrink the increment. -/
private theorem equicontinuous_convolutionUnitBallImage (k : C(G, 𝕜)) :
    Equicontinuous ((↑) : convolutionUnitBallImage k → G → 𝕜) := by
  intro x₀
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.1 ((convSection k).continuous.tendsto x₀) ε hε] with x hx
  rintro ⟨-, f, hf, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hf
  rw [dist_eq_norm] at hx ⊢
  calc ‖convolutionCLM k f x₀ - convolutionCLM k f x‖
      ≤ ‖convSection k x₀ - convSection k x‖ * ‖f‖ :=
        norm_convolutionCLM_apply_sub_apply_le k f x₀ x
    _ ≤ ‖convSection k x₀ - convSection k x‖ * 1 := by gcongr
    _ = ‖convSection k x - convSection k x₀‖ := by rw [mul_one, norm_sub_rev]
    _ < ε := hx

private theorem isCompact_closure_convolutionUnitBallImage (k : C(G, 𝕜)) :
    IsCompact (closure (convolutionUnitBallImage k)) :=
  BoundedContinuousFunction.arzela_ascoli _ (isCompact_closedBall (0 : 𝕜) ‖k‖) _
    (convolutionUnitBallImage_apply_mem_closedBall k) (equicontinuous_convolutionUnitBallImage k)

/-- **Convolution against a continuous kernel is a compact operator** from `L²(G)` to `C(G)`.

The unit ball of `L²(G)` is carried to a uniformly bounded equicontinuous family of continuous
functions, which Arzelà-Ascoli makes relatively compact for the uniform norm. -/
theorem isCompactOperator_convolutionCLM (k : C(G, 𝕜)) :
    IsCompactOperator (convolutionCLM (G := G) k) := by
  refine (isCompactOperator_iff_image_closedBall_subset_compact
    (convolutionCLM (G := G) k).toLinearMap one_pos).2
    ⟨(ContinuousMap.isometryEquivBoundedOfCompact G 𝕜).symm ''
        closure (convolutionUnitBallImage k),
      (isCompact_closure_convolutionUnitBallImage k).image
        (ContinuousMap.isometryEquivBoundedOfCompact G 𝕜).symm.continuous, ?_⟩
  rintro - ⟨f, hf, rfl⟩
  exact ⟨_, subset_closure ⟨f, hf, rfl⟩,
    (ContinuousMap.isometryEquivBoundedOfCompact G 𝕜).symm_apply_apply _⟩

/-- **The convolution operator on `L²(G)` is compact.** It factors through the uniform norm of
`C(G)`, where `isCompactOperator_convolutionCLM` already gives compactness, and reading a
continuous function back into `L²(G)` is bounded. -/
theorem isCompactOperator_convolutionOperator (k : C(G, 𝕜)) :
    IsCompactOperator (convolutionOperator (G := G) k) :=
  (isCompactOperator_convolutionCLM k).clm_comp (ContinuousMap.toLp 2 (haarProb G) 𝕜)

/-! ### The eigenspaces of a convolution operator

Compactness bounds the dimension of each nonzero eigenspace; the pointwise formula shows every
eigenvector at a nonzero eigenvalue is a continuous function; and equivariance makes the
eigenspaces right-translation invariant. Together these are the three properties that turn a
symmetric convolution operator into a source of finite-dimensional representations of `G`. The
eigenspace at `0` is the complementary case: it convolves to nothing at all. -/

/-- **A nonzero eigenspace of a convolution operator is finite-dimensional**, because the operator
is compact. -/
theorem finiteDimensional_eigenspace_convolutionOperator (k : C(G, 𝕜)) {μ : 𝕜} (hμ : μ ≠ 0) :
    FiniteDimensional 𝕜 (Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace (isCompactOperator_convolutionOperator k) μ hμ

/-- **Eigenvectors at a nonzero eigenvalue are continuous.** An eigenvector `f` is `μ⁻¹` times its
own convolution `k * f`, and the latter is a genuine continuous function on `G`, not merely an
almost-everywhere class. This supplies the continuous representatives that the later construction
of the representative ring needs; membership in that ring additionally requires realizing the
finite-dimensional invariant eigenspace as a continuous representation. -/
theorem ae_eq_smul_convolutionCLM_of_mem_eigenspace (k : C(G, 𝕜)) {μ : 𝕜} (hμ : μ ≠ 0)
    {f : Lp 𝕜 2 (haarProb G)}
    (hf : f ∈ Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :
    f =ᵐ[haarProb G] μ⁻¹ • convolutionCLM k f := by
  rw [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe] at hf
  have hfeq : f = μ⁻¹ • convolutionOperator k f := by
    rw [hf, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  nth_rewrite 1 [hfeq]
  filter_upwards [Lp.coeFn_smul μ⁻¹ (convolutionOperator k f),
    coeFn_convolutionOperator k f] with x hsmul hcoe
  rw [hsmul, Pi.smul_apply, hcoe]
  rfl

/-- **Convolving a `0`-eigenvector gives the zero function.** The convolution operator factors as
`ContinuousMap.toLp` after `convolutionCLM`, and `ContinuousMap.toLp` is injective because
normalized Haar measure is positive on nonempty open sets. This is the complement of
`ae_eq_smul_convolutionCLM_of_mem_eigenspace`, which describes the eigenvectors at a nonzero
eigenvalue. -/
theorem convolutionCLM_eq_zero_of_mem_eigenspace_zero (k : C(G, 𝕜))
    {f : Lp 𝕜 2 (haarProb G)}
    (hf : f ∈ Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap 0) :
    convolutionCLM k f = 0 := by
  rw [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, zero_smul] at hf
  refine ContinuousMap.toLp_injective (E := 𝕜) (𝕜 := 𝕜) (p := 2) (haarProb G) ?_
  rw [← convolutionOperator_apply, hf, map_zero]

/-- **The eigenspaces of a convolution operator are invariant under right translation**, because
the operator commutes with right translation. -/
theorem compMeasurePreserving_mul_right_mem_eigenspace_convolutionOperator (k : C(G, 𝕜)) (μ : 𝕜)
    (g₀ : G) {f : Lp 𝕜 2 (haarProb G)}
    (hf : f ∈ Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ) :
    Lp.compMeasurePreserving (· * g₀) (measurePreserving_mul_right (haarProb G) g₀) f ∈
      Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ := by
  rw [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe] at hf ⊢
  rw [convolutionOperator_compMeasurePreserving_mul_right, hf]
  exact (Lp.compMeasurePreservingₗ 𝕜 (· * g₀)
    (measurePreserving_mul_right (haarProb G) g₀)).map_smul μ f

/-! ### The spectral consequences for a symmetric kernel

For a symmetric kernel the convolution operator is both compact and self-adjoint, so Mathlib's
spectral theory of compact self-adjoint operators applies to it. Two consequences matter for
Peter-Weyl: unless the operator vanishes it *has* a nonzero eigenvalue, and its eigenspaces
together span a dense subspace of `L²(G)`. -/

/-- **A nonzero symmetric convolution operator has a nonzero eigenvalue.** For a compact
self-adjoint operator the spectral radius is the operator norm and every nonzero spectral value is
an eigenvalue, so a nonzero operator cannot have `0` as its only eigenvalue.

This is where finite-dimensional representations of `G` come from: by the results above, the
eigenspace at such a `μ` is a nonzero, finite-dimensional, right-translation-invariant subspace of
`L²(G)` all of whose elements are continuous. No point-separation property of `G` is used, so
nothing is smuggled in from the Peter-Weyl theorem itself. -/
theorem exists_hasEigenvalue_ne_zero_convolutionOperator (k : C(G, 𝕜))
    (hk : ∀ g : G, k g⁻¹ = (starRingEnd 𝕜) (k g)) (hne : convolutionOperator (G := G) k ≠ 0) :
    ∃ μ : 𝕜, μ ≠ 0 ∧ Module.End.HasEigenvalue (convolutionOperator (G := G) k).toLinearMap μ := by
  have h := mt ((convolutionOperator k).eq_zero_of_forall_hasEigenvalue_eq_zero
    (isCompactOperator_convolutionOperator k)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1
      (isSelfAdjoint_convolutionOperator k hk))).1 hne
  push Not at h
  obtain ⟨μ, hμ, hμ0⟩ := h
  exact ⟨μ, hμ0, hμ⟩

/-- **The spectral theorem for a symmetric convolution operator:** its eigenspaces span a dense
subspace of `L²(G)`, in the sense that their supremum has trivial orthogonal complement. Together
with `finiteDimensional_eigenspace_convolutionOperator` this says that `L²(G)` is exhausted, up to
the kernel of the operator, by finite-dimensional translation-invariant subspaces. -/
theorem orthogonalComplement_iSup_eigenspaces_convolutionOperator_eq_bot (k : C(G, 𝕜))
    (hk : ∀ g : G, k g⁻¹ = (starRingEnd 𝕜) (k g)) :
    (⨆ μ : 𝕜, Module.End.eigenspace (convolutionOperator (G := G) k).toLinearMap μ)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (isCompactOperator_convolutionOperator k)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1
      (isSelfAdjoint_convolutionOperator k hk))

end CompactGroup

end TauCeti
