/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import PhyslibAlpha.Mathematics.TauCeti.MeasureTheory.Integral.PeakFunction
public import PhyslibAlpha.Mathematics.TauCeti.Order.Filter.SmallSets
public import PhyslibAlpha.Mathematics.TauCeti.RepresentationTheory.Continuous.Unitary.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import PhyslibAlpha.Mathematics.TauCeti.MeasureTheory.Function.StronglyMeasurable.InnerRegular

/-!
# The integrated form of a strongly continuous representation

Let `π` be a representation of an additive topological group `G` (written multiplicatively, as a
`ContRepresentation` of `Multiplicative G`) on a normed space `E`, which is **strongly continuous**
(every orbit `g ↦ π g v` is continuous) and uniformly bounded, and let `μ` be a measure on `G`.

## i. Overview

Let `π` be a representation of an additive topological group `G` (written multiplicatively, as a
`ContRepresentation` of `Multiplicative G`) on a normed space `E`, which is **strongly continuous**
(every orbit `g ↦ π g v` is continuous) and uniformly bounded, and let `μ` be a measure on `G`. An
integrable weight `f` then acts on `E` by the **integrated form**

`π(f) v = ∫ g, f g • π g v ∂μ`,

a bounded operator with `‖π(f)‖ ≤ C * ‖f‖₁` when `‖π g‖ ≤ C`. This file builds the map
`f ↦ π(f)` as a continuous linear map `L¹(G, μ) →L E →L E` and proves the identities that make it a
representation of the convolution algebra `L¹(G)`: translating the weight composes with `π`,
convolution of weights becomes composition of operators, and, for a unitary `π` and an
inversion-invariant `μ`, adjoints correspond to the involution `f^*(g) = conj (f (-g))`.
For abelian `G`, the integrated operators commute for any measure; they are also normal
when `π` is unitary and `μ` is inversion-invariant.

The integrated form is how a strongly continuous representation is handled by operator algebra:
the operators `π g` themselves depend on `g` only strongly continuously, but the left translates
`π h ∘L π(f)` depend continuously on `h` in the operator norm. Applied to the GNS representation of
a continuous positive-definite function on a locally compact abelian group, the commutative
algebra of operators `π(f)` is the standard source of the representing measure in Bochner's
theorem (Folland, Chapter 4).

**Implementation notes.** The definition integrates the orbits `g ↦ f g • π g v` pointwise in `v`
and only then bundles the
result into an operator. The operator-valued map `g ↦ π g` need not be strongly measurable for the
operator norm: for the regular representation of `ℝ` on `L²(ℝ)`, distinct translations are at
operator distance `2`, so the map is not almost everywhere separably valued, and `π(f)` cannot be
written as a Bochner integral in `E →L E`. This is also why
`TauCeti.ContRepresentation.integratedOperator`, which averages a *norm*-continuous representation
of a compact group against a continuous weight, does not apply here. The strong continuity and the
uniform bound are hypotheses of the definition: they are exactly what makes the integrand
integrable, and they hold for the unitary representations that are the main application.
Measurability of the integrands `g ↦ f g • π g v` is read off from the continuity of the orbits and
the inner regularity of `μ` for compact sets
(`MeasureTheory.AEFinStronglyMeasurable.aestronglyMeasurable_smul`): an integrable weight lives on a
σ-finite set, which up to a null set is a countable union of compact sets with separable images.
The Haar measure `MeasureTheory.Measure.addHaar` of a locally compact group is regular, hence has
this property, so no second countability of `G` or separability of `E` is needed. Only the
convolution identity, which integrates over `G × G`, still asks for
`SecondCountableTopologyEither G E`.

## ii. Key results

* `ContRepresentation.integratedOperatorL1`: the integrated form `f ↦ π(f)`, as a bounded linear
  map from `L¹(G, μ)` to the bounded operators on `E`.

* `ContRepresentation.integratedOperatorL1_apply`, `ContRepresentation.integratedOperatorL1_toL1`:
  the pointwise formula `π(f) v = ∫ g, f g • π g v ∂μ`.
* `ContRepresentation.norm_integratedOperatorL1_le`: `‖π(f)‖ ≤ C * ‖f‖₁` when `‖π g‖ ≤ C`.
* `ContRepresentation.comp_integratedOperatorL1`: `π h ∘L π(f) = π(f (-h + ·))` for a
  left-invariant measure.
* `ContRepresentation.continuous_comp_integratedOperatorL1`: `h ↦ π h ∘L π(f)` is continuous in the
  operator norm.
* `ContRepresentation.integratedOperatorL1_convolution`: `π(f₁ ⋆ f₂) = π(f₁) ∘L π(f₂)` on an
  abelian group with a right-invariant measure.
* `ContRepresentation.integratedOperatorL1_commute`: integrated operators commute on an abelian
  group with any measure.
* `ContRepresentation.inner_integratedOperatorL1_apply`: the matrix coefficients
  `⟪w, π(f) v⟫ = ∫ g, f g * ⟪w, π g v⟫ ∂μ`.
* `ContRepresentation.adjoint_integratedOperatorL1`: `π(f)† = π(f^*)` for a unitary `π`.
* `ContRepresentation.isStarNormal_integratedOperatorL1`: integrated operators of a unitary
  abelian-group representation are normal for an inversion-invariant measure.
* `ContRepresentation.tendsto_integratedOperatorL1_apply`: weights of unit integral and bounded
  `L¹` norm concentrating at `0` form an approximate identity, `π(f i) v → v`.
* `ContRepresentation.mem_closure_range_integratedOperatorL1_apply`: the integrated form is
  nondegenerate, every `v` being a limit of vectors `π(f) v`.

## iii. Table of contents

- A. Development

## iv. References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §3.2.
-/

public section

/-! ## A. Development -/

open Filter MeasureTheory
open scoped InnerProductSpace Topology

namespace TauCeti

section Normed

variable {𝕜 G E : Type*} [RCLike 𝕜] [AddGroup G] [TopologicalSpace G] [MeasurableSpace G]
  [R1Space G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 E]
  {μ : Measure G} [μ.InnerRegularCompactLTTop] {π : ContRepresentation 𝕜 (Multiplicative G) E}

omit [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 E] in
/-- The integrand of the integrated form is integrable. -/
private lemma integrable_smul_apply (hcont : ∀ v, Continuous fun g : G ↦ π (.ofAdd g) v)
    {C : ℝ} (hC : ∀ g, ‖π g‖ ≤ C) {f : G → 𝕜} (hf : Integrable f μ) (v : E) :
    Integrable (fun g ↦ f g • π (.ofAdd g) v) μ := by
  refine (hf.norm.mul_const (C * ‖v‖)).mono'
    (hf.aefinStronglyMeasurable.aestronglyMeasurable_smul (hcont v)) (.of_forall fun g ↦ ?_)
  rw [norm_smul]
  gcongr
  exact (π _).le_of_opNorm_le (hC _) v

omit [TopologicalSpace G] [R1Space G] [BorelSpace G] [μ.InnerRegularCompactLTTop]
  [SMulCommClass ℝ 𝕜 E] in
/-- The integral of the integrand of the integrated form is bounded by the `L¹` norm of the
weight. -/
private lemma norm_integral_smul_apply_le {C : ℝ} (hC : ∀ g, ‖π g‖ ≤ C) {f : G → 𝕜}
    (hf : Integrable f μ) (v : E) :
    ‖∫ g, f g • π (.ofAdd g) v ∂μ‖ ≤ C * (∫ g, ‖f g‖ ∂μ) * ‖v‖ := by
  calc ‖∫ g, f g • π (.ofAdd g) v ∂μ‖ ≤ ∫ g, ‖f g‖ * (C * ‖v‖) ∂μ := by
        refine norm_integral_le_of_norm_le (hf.norm.mul_const _) (.of_forall fun g ↦ ?_)
        rw [norm_smul]
        gcongr
        exact (π _).le_of_opNorm_le (hC _) v
    _ = C * (∫ g, ‖f g‖ ∂μ) * ‖v‖ := by rw [integral_mul_const]; ring

variable (π) in
/-- The **integrated form** of a strongly continuous, uniformly bounded representation `π` of an
additive group `G` (written multiplicatively as `Multiplicative G`): the bounded operator
`π(f) = ∫ g, f g • π g ∂μ` attached to an integrable weight `f`, defined pointwise by the Bochner
integral `π(f) v = ∫ g, f g • π g v ∂μ` of the continuous orbit `g ↦ π g v`. -/
noncomputable def _root_.ContRepresentation.integratedOperatorL1
    (hcont : ∀ v, Continuous fun g : G ↦ π (.ofAdd g) v)
    (hbdd : ∃ C, ∀ g, ‖π g‖ ≤ C) (μ : Measure G) [μ.InnerRegularCompactLTTop] :
    (G →₁[μ] 𝕜) →L[𝕜] E →L[𝕜] E :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 (fun (f : G →₁[μ] 𝕜) v ↦ ∫ g, f g • π (.ofAdd g) v ∂μ)
      (fun f₁ f₂ v ↦ by
        rw [← integral_add (integrable_smul_apply hcont hbdd.choose_spec (L1.integrable_coeFn _) v)
          (integrable_smul_apply hcont hbdd.choose_spec (L1.integrable_coeFn _) v)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add f₁ f₂] with g hg
        rw [hg, Pi.add_apply, add_smul])
      (fun c f v ↦ by
        rw [← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with g hg
        rw [hg, Pi.smul_apply, smul_eq_mul, mul_smul])
      (fun f v w ↦ by
        rw [← integral_add (integrable_smul_apply hcont hbdd.choose_spec (L1.integrable_coeFn _) v)
          (integrable_smul_apply hcont hbdd.choose_spec (L1.integrable_coeFn _) w)]
        simp_rw [map_add, smul_add])
      (fun c f v ↦ by
        rw [← integral_smul]
        simp_rw [map_smul, smul_comm c]))
    hbdd.choose fun f v ↦ by
      simpa [L1.norm_eq_integral_norm] using norm_integral_smul_apply_le hbdd.choose_spec
        (L1.integrable_coeFn f) v

variable {hcont : ∀ v, Continuous fun g : G ↦ π (.ofAdd g) v} {hbdd : ∃ C, ∀ g, ‖π g‖ ≤ C}

/-- The integrated form acts on a vector by integrating its orbit against the weight. -/
lemma _root_.ContRepresentation.integratedOperatorL1_apply (f : G →₁[μ] 𝕜) (v : E) :
    π.integratedOperatorL1 hcont hbdd μ f v = ∫ g, f g • π (.ofAdd g) v ∂μ :=
  (rfl)

/-- The integrated form of the class of an integrable function. -/
@[simp]
lemma _root_.ContRepresentation.integratedOperatorL1_toL1 {f : G → 𝕜} (hf : Integrable f μ)
    (v : E) :
    π.integratedOperatorL1 hcont hbdd μ (hf.toL1 f) v = ∫ g, f g • π (.ofAdd g) v ∂μ := by
  rw [ContRepresentation.integratedOperatorL1_apply]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toL1] with g hg
  rw [hg]

/-- The integrated form is bounded by the uniform bound of the representation times the `L¹`
norm of the weight. -/
lemma _root_.ContRepresentation.norm_integratedOperatorL1_le {C : ℝ} (hC : ∀ g, ‖π g‖ ≤ C)
    (f : G →₁[μ] 𝕜) :
    ‖π.integratedOperatorL1 hcont hbdd μ f‖ ≤ C * ‖f‖ := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  simpa [ContRepresentation.integratedOperatorL1_apply, L1.norm_eq_integral_norm] using
    norm_integral_smul_apply_le hC (L1.integrable_coeFn f) v

/-- Translating the weight on the left by `h` amounts to composing the integrated form with
`π h`. -/
lemma _root_.ContRepresentation.comp_integratedOperatorL1 [CompleteSpace E] [MeasurableAdd G]
    [μ.IsAddLeftInvariant] (h : G) (f : G →₁[μ] 𝕜) :
    π (.ofAdd h) ∘L π.integratedOperatorL1 hcont hbdd μ f =
      π.integratedOperatorL1 hcont hbdd μ
        (Lp.compMeasurePreserving (fun g ↦ -h + g) (measurePreserving_add_left μ (-h)) f) := by
  ext v
  rw [ContinuousLinearMap.comp_apply, ContRepresentation.integratedOperatorL1_apply,
    ContRepresentation.integratedOperatorL1_apply,
    ← (π _).integral_comp_comm
      (integrable_smul_apply hcont hbdd.choose_spec (L1.integrable_coeFn f) v)]
  have hcomp : ∫ g, (Lp.compMeasurePreserving (fun g ↦ -h + g)
        (measurePreserving_add_left μ (-h)) f) g • π (.ofAdd g) v ∂μ =
      ∫ g, f (-h + g) • π (.ofAdd g) v ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_add_left μ (-h))]
      with g hg
    rw [hg, Function.comp_apply]
  rw [hcomp, ← integral_add_left_eq_self (fun g ↦ f (-h + g) • π (.ofAdd g) v) h]
  simp [ofAdd_add]

/-- Although `π` is only strongly continuous, `h ↦ π h ∘L π(f)` is continuous in the operator norm:
by `comp_integratedOperatorL1` it is the integrated form of the left translates of `f`, which
depend continuously on `h` in `L¹`. -/
lemma _root_.ContRepresentation.continuous_comp_integratedOperatorL1 [CompleteSpace E]
    [IsTopologicalAddGroup G] [MeasurableAdd G] [μ.IsAddLeftInvariant] [IsLocallyFiniteMeasure μ]
    (f : G →₁[μ] 𝕜) :
    Continuous fun h : G ↦ π (.ofAdd h) ∘L π.integratedOperatorL1 hcont hbdd μ f := by
  simp_rw [ContRepresentation.comp_integratedOperatorL1]
  exact (π.integratedOperatorL1 hcont hbdd μ).continuous.comp
    (continuous_const.compMeasurePreservingLp
      (ContinuousMap.curry ⟨fun p : G × G ↦ -p.1 + p.2, by fun_prop⟩).continuous
      (fun h ↦ measurePreserving_add_left μ (-h)) ENNReal.one_ne_top)

end Normed

section Commute

variable {𝕜 G E : Type*} [RCLike 𝕜] [AddCommGroup G] [TopologicalSpace G]
  [MeasurableSpace G] [R1Space G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 E]
  [CompleteSpace E]
  {μ : Measure G} [μ.InnerRegularCompactLTTop] {π : ContRepresentation 𝕜 (Multiplicative G) E}
  {hcont : ∀ v, Continuous fun g : G ↦ π (.ofAdd g) v} {hbdd : ∃ C, ∀ g, ‖π g‖ ≤ C}

/-- Every action operator of a representation of an abelian group commutes with its
integrated operators. No invariance hypothesis on the measure is needed. -/
lemma _root_.ContRepresentation.commute_integratedOperatorL1
    (g : Multiplicative G) (f : G →₁[μ] 𝕜) :
    Commute (π g) (π.integratedOperatorL1 hcont hbdd μ f) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [mul_apply_eq_comp, ContRepresentation.integratedOperatorL1_apply]
  rw [← (π g).integral_comp_comm
    (integrable_smul_apply hcont hbdd.choose_spec (L1.integrable_coeFn f) v)]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [map_smul]
  exact congrArg (fun w => f t • w)
    (congrArg (fun T : E →L[𝕜] E => T v)
      ((Commute.all g (.ofAdd t)).map π.toMonoidHom).eq)

/-- Integrated operators of an abelian-group representation commute for any measure. -/
lemma _root_.ContRepresentation.integratedOperatorL1_commute (f₁ f₂ : G →₁[μ] 𝕜) :
    Commute (π.integratedOperatorL1 hcont hbdd μ f₁)
      (π.integratedOperatorL1 hcont hbdd μ f₂) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [mul_apply_eq_comp]
  rw [π.integratedOperatorL1_apply f₂ v]
  rw [← (π.integratedOperatorL1 hcont hbdd μ f₁).integral_comp_comm
    (integrable_smul_apply hcont hbdd.choose_spec (L1.integrable_coeFn f₂) v)]
  rw [π.integratedOperatorL1_apply f₂]
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  dsimp only
  rw [map_smul]
  exact congrArg (fun w ↦ f₂ t • w)
    (congrArg (fun T : E →L[𝕜] E ↦ T v)
      (π.commute_integratedOperatorL1 (.ofAdd t) f₁).symm.eq)

end Commute

section Convolution

variable {𝕜 G E : Type*} [RCLike 𝕜] [AddCommGroup G] [TopologicalSpace G] [MeasurableSpace G]
  [R1Space G] [BorelSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 E]
  [CompleteSpace E] [SecondCountableTopologyEither G E]
  {μ : Measure G} [μ.InnerRegularCompactLTTop] [SFinite μ] [μ.IsAddRightInvariant]
  {π : ContRepresentation 𝕜 (Multiplicative G) E}
  {hcont : ∀ v, Continuous fun g : G ↦ π (.ofAdd g) v} {hbdd : ∃ C, ∀ g, ‖π g‖ ≤ C}

/-- The integrated form turns convolution of weights into composition of operators:
`π(f₁ ⋆ f₂) = π(f₁) ∘L π(f₂)`. -/
lemma _root_.ContRepresentation.integratedOperatorL1_convolution {f₁ f₂ : G → 𝕜}
    (hf₁ : Integrable f₁ μ) (hf₂ : Integrable f₂ μ) :
    π.integratedOperatorL1 hcont hbdd μ
        ((hf₁.integrable_convolution (ContinuousLinearMap.mul 𝕜 𝕜) hf₂).toL1 _) =
      π.integratedOperatorL1 hcont hbdd μ (hf₁.toL1 f₁) ∘L
        π.integratedOperatorL1 hcont hbdd μ (hf₂.toL1 f₂) := by
  obtain ⟨C, hC⟩ := hbdd
  ext v
  rw [ContinuousLinearMap.comp_apply, ContRepresentation.integratedOperatorL1_toL1,
    ContRepresentation.integratedOperatorL1_toL1, ContRepresentation.integratedOperatorL1_toL1]
  -- Push `π t` inside the inner integral and substitute `x = t + s` there.
  have hinner (t : G) : f₁ t • π (.ofAdd t) (∫ s, f₂ s • π (.ofAdd s) v ∂μ) =
      ∫ x, (f₁ t * f₂ (x - t)) • π (.ofAdd x) v ∂μ := by
    rw [← (π _).integral_comp_comm (integrable_smul_apply hcont hC hf₂ v), ← integral_smul,
      ← integral_sub_right_eq_self _ t]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    dsimp only
    rw [map_smul, ← mul_apply_eq_comp, ← map_mul, ← ofAdd_add, add_sub_cancel,
      mul_smul]
  simp_rw [hinner]
  -- Exchange the order of integration.
  have hint : Integrable (Function.uncurry fun t x ↦ (f₁ t * f₂ (x - t)) • π (.ofAdd x) v)
      (μ.prod μ) := by
    have hconv := (hf₁.convolution_integrand (ContinuousLinearMap.mul 𝕜 𝕜) hf₂).swap
    refine (hconv.norm.mul_const (C * ‖v‖)).mono'
      (hconv.aestronglyMeasurable.smul (hcont v).aestronglyMeasurable.comp_snd)
      (.of_forall fun ⟨t, x⟩ ↦ ?_)
    simp only [Function.uncurry_apply_pair, Function.comp_apply, Prod.fst_swap, Prod.snd_swap,
      ContinuousLinearMap.mul_apply', norm_smul]
    gcongr
    exact (π _).le_of_opNorm_le (hC _) v
  rw [integral_integral_swap hint]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  dsimp only
  rw [integral_smul_const, convolution_def]
  simp

end Convolution

section InnerProduct

variable {𝕜 G E : Type*} [RCLike 𝕜] [AddGroup G] [TopologicalSpace G] [MeasurableSpace G]
  [R1Space G] [BorelSpace G]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 E]
  [CompleteSpace E]
  {μ : Measure G} [μ.InnerRegularCompactLTTop] {π : ContRepresentation 𝕜 (Multiplicative G) E}
  {hcont : ∀ v, Continuous fun g : G ↦ π (.ofAdd g) v} {hbdd : ∃ C, ∀ g, ‖π g‖ ≤ C}

/-- Matrix coefficients of the integrated form are the integrals of the matrix coefficients of the
representation against the weight. -/
lemma _root_.ContRepresentation.inner_integratedOperatorL1_apply (f : G →₁[μ] 𝕜) (w v : E) :
    ⟪w, π.integratedOperatorL1 hcont hbdd μ f v⟫_𝕜 = ∫ g, f g * ⟪w, π (.ofAdd g) v⟫_𝕜 ∂μ := by
  rw [ContRepresentation.integratedOperatorL1_apply,
    ← integral_inner (integrable_smul_apply hcont hbdd.choose_spec (L1.integrable_coeFn f) v)]
  simp_rw [inner_smul_right]

/-- The adjoint of the integrated form of a unitary representation is the integrated form of the
involuted weight `g ↦ conj (f (-g))`. -/
lemma _root_.ContRepresentation.adjoint_integratedOperatorL1 [MeasurableNeg G]
    [μ.IsNegInvariant] (hπ : ContRepresentation.IsUnitary π) (f : G →₁[μ] 𝕜) :
    ContinuousLinearMap.adjoint (π.integratedOperatorL1 hcont hbdd μ f) =
      π.integratedOperatorL1 hcont hbdd μ
        (star (Lp.compMeasurePreserving Neg.neg (Measure.measurePreserving_neg μ) f)) := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun w v ↦ ?_).symm
  rw [← inner_conj_symm _ v, ContRepresentation.inner_integratedOperatorL1_apply,
    ContRepresentation.inner_integratedOperatorL1_apply, ← integral_conj,
    ← integral_neg_eq_self (fun g ↦ (f g : 𝕜) * ⟪w, π (.ofAdd g) v⟫_𝕜)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_star (Lp.compMeasurePreserving Neg.neg
      (Measure.measurePreserving_neg μ) f),
    Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg μ)] with g hstar hcomp
  rw [hstar, Pi.star_apply, hcomp, Function.comp_apply, map_mul, RCLike.star_def,
    RCLike.conj_conj, inner_conj_symm, hπ.inner_map_left, ← ofAdd_neg]

end InnerProduct

section Unitary

variable {𝕜 G E : Type*} [RCLike 𝕜] [AddCommGroup G] [TopologicalSpace G]
  [MeasurableSpace G] [R1Space G] [BorelSpace G] [MeasurableNeg G]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 E]
  [CompleteSpace E]
  {μ : Measure G} [μ.InnerRegularCompactLTTop] [μ.IsNegInvariant]
  {π : ContRepresentation 𝕜 (Multiplicative G) E}
  {hcont : ∀ v, Continuous fun g : G ↦ π (.ofAdd g) v}
  {hbdd : ∃ C, ∀ g, ‖π g‖ ≤ C}

/-- The integrated operators of a unitary abelian-group representation are normal. -/
lemma _root_.ContRepresentation.isStarNormal_integratedOperatorL1
    (hπ : ContRepresentation.IsUnitary π) (f : G →₁[μ] 𝕜) :
    IsStarNormal (π.integratedOperatorL1 hcont hbdd μ f) := by
  constructor
  rw [ContinuousLinearMap.star_eq_adjoint,
    ContRepresentation.adjoint_integratedOperatorL1 hπ]
  exact π.integratedOperatorL1_commute
    (star (Lp.compMeasurePreserving Neg.neg (Measure.measurePreserving_neg μ) f)) f

end Unitary

section ApproximateIdentity

variable {𝕜 G E : Type*} [RCLike 𝕜] [AddGroup G] [TopologicalSpace G] [MeasurableSpace G]
  [R1Space G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 E]
  [CompleteSpace E]
  {μ : Measure G} [μ.InnerRegularCompactLTTop] {π : ContRepresentation 𝕜 (Multiplicative G) E}
  {hcont : ∀ v, Continuous fun g : G ↦ π (.ofAdd g) v} {hbdd : ∃ C, ∀ g, ‖π g‖ ≤ C}

/-- **Approximate identities for the integrated form.** If the weights `f i` eventually have unit
integral and `L¹` norm at most `C`, and concentrate at `0` (for every neighbourhood `U` of `0`,
eventually `f i` vanishes almost everywhere outside `U`), then `π(f i)` tends strongly to the
identity: `π(f i) v → v` for every `v`. -/
lemma _root_.ContRepresentation.tendsto_integratedOperatorL1_apply {ι : Type*} {l : Filter ι}
    {f : ι → G →₁[μ] 𝕜} {C : ℝ} (hf : ∀ᶠ i in l, ∫ g, f i g ∂μ = 1)
    (hfC : ∀ᶠ i in l, ‖f i‖ ≤ C)
    (hf₀ : ∀ U ∈ 𝓝 (0 : G), ∀ᶠ i in l, ∀ᵐ g ∂μ, g ∉ U → f i g = 0) (v : E) :
    Tendsto (fun i ↦ π.integratedOperatorL1 hcont hbdd μ (f i) v) l (𝓝 v) := by
  simp_rw [ContRepresentation.integratedOperatorL1_apply]
  refine tendsto_integral_smul_of_tendsto hf hfC hf₀ (.of_forall fun i ↦
    (L1.integrable_coeFn (f i)).aefinStronglyMeasurable.aestronglyMeasurable_smul (hcont v)) ?_
  simpa using (hcont v).tendsto 0

/-- **The integrated form is nondegenerate.** For a measure positive on nonempty open sets and
finite on some neighbourhood of each point, such as a Haar measure on a locally compact group, every
vector `v` is a limit of vectors `π(f) v`. -/
lemma _root_.ContRepresentation.mem_closure_range_integratedOperatorL1_apply
    [μ.IsOpenPosMeasure] [IsLocallyFiniteMeasure μ] (v : E) :
    v ∈ closure (Set.range fun f : G →₁[μ] 𝕜 ↦ π.integratedOperatorL1 hcont hbdd μ f v) := by
  -- One normalized weight inside each neighbourhood of `0`, indexed as a net shrinking to `0`.
  choose f hf using fun U : {U : Set G // U ∈ 𝓝 (0 : G)} ↦
    exists_integral_eq_one_norm_eq_one 𝕜 μ U.2
  have := comap_val_smallSets_neBot (𝓝 (0 : G))
  refine mem_closure_of_tendsto (ContRepresentation.tendsto_integratedOperatorL1_apply
    (l := comap Subtype.val (𝓝 (0 : G)).smallSets) (C := 1) (.of_forall fun U ↦ (hf U).1)
    (.of_forall fun U ↦ (hf U).2.1.le) (fun V hV ↦ ?_) v)
    (.of_forall fun U ↦ Set.mem_range_self _)
  filter_upwards [(eventually_smallSets_subset.2 hV).comap Subtype.val] with U hU
  filter_upwards [(hf U).2.2] with g hg hgV using hg fun hgU ↦ hgV (hU hgU)

end ApproximateIdentity

end TauCeti
