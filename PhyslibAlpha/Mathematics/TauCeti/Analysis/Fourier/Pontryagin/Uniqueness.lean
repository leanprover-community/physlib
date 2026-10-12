/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.Mathematics.TauCeti.Analysis.Fourier.Pontryagin.Measure
public import PhyslibAlpha.Mathematics.TauCeti.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Uniqueness of Fourier--Stieltjes measures on a Pontryagin dual

On a Polish Pontryagin dual, a finite measure is determined by the integrals of the evaluation
characters.

## i. Overview

On a Polish Pontryagin dual, a finite measure is determined by the integrals of the evaluation
characters.  Equivalently, the Fourier--Stieltjes transform of a finite measure on the dual is
injective.  On the dual of an arbitrary locally compact abelian group, where the dual need be
neither metrizable nor second countable, the same holds for finite inner regular measures.  These
are the uniqueness halves of Bochner's theorem for locally compact abelian groups.

The proof packages finite linear combinations of evaluation characters as a star subalgebra of
bounded continuous functions.  Evaluation characters separate points of the dual simply because
two continuous homomorphisms that agree at every group element are equal.  Mathlib's extension
theorem for finite measures on Polish spaces, or its inner regular counterpart
`TauCeti.MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_innerRegular` on locally
compact Hausdorff spaces, then promotes equality of the character integrals to equality of the
measures.

The construction of `evalMonoidHom`, `evalAlgHom` and `evalPoly`, together with the proofs that
`evalPoly` is closed under `star` and separates points, is adapted from Jakob Stiefel's
`charMonoidHom`, `charAlgHom`, `charPoly`, `star_mem_range_charAlgHom` and
`separatesPoints_charPoly` in `Mathlib.Analysis.Fourier.BoundedContinuousFunctionChar`, which
treats characters of the form `v ↦ e (L v w)` on a real vector space.

## ii. Key results

* `PontryaginDual.evalBoundedContinuous`: evaluation at a group element, bundled as a
  bounded continuous function on the dual.
* `PontryaginDual.evalPoly`: the star subalgebra of finite linear combinations of
  evaluation characters.
* `MeasureTheory.FiniteMeasure.ext_of_forall_pontryaginMeasureTransform_eq`: finite measures on a
  Polish dual with the same Fourier--Stieltjes transform are equal.
* `MeasureTheory.FiniteMeasure.ext_of_forall_pontryaginMeasureTransform_eq_of_innerRegular`:
  finite inner regular measures on the dual of a locally compact abelian group with the same
  Fourier--Stieltjes transform are equal.

## iii. Table of contents

- A. Development

## iv. References

* W. Rudin, *Fourier Analysis on Groups*, Chapter 1.
* J. Stiefel, `Mathlib.Analysis.Fourier.BoundedContinuousFunctionChar`, Mathlib.
-/

public section

/-! ## A. Development -/

noncomputable section

open BoundedContinuousFunction MeasureTheory

namespace PontryaginDual

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G]

/-- Evaluation at `g`, as a bounded continuous complex-valued function on the Pontryagin dual.
Its values lie on the unit circle, so its norm is bounded by one. -/
def evalBoundedContinuous (g : G) :
    _root_.PontryaginDual (Multiplicative G) →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun χ => (χ (Multiplicative.ofAdd g) : ℂ))
    (TauCeti.PontryaginDual.continuous_coe_eval_const (Multiplicative.ofAdd g)) 1 fun χ => by simp

/-- Evaluation of `evalBoundedContinuous` at a character. -/
@[simp]
lemma evalBoundedContinuous_apply (g : G)
    (χ : _root_.PontryaginDual (Multiplicative G)) :
    evalBoundedContinuous g χ = (χ (Multiplicative.ofAdd g) : ℂ) :=
  (rfl)

/-- Evaluation at zero is the constant function one. -/
@[simp]
lemma evalBoundedContinuous_zero :
    evalBoundedContinuous (0 : G) = 1 := by
  ext χ
  simp

/-- Evaluation turns addition in the original group into pointwise multiplication. -/
@[simp]
lemma evalBoundedContinuous_add (g h : G) :
    evalBoundedContinuous (g + h) =
      evalBoundedContinuous g * evalBoundedContinuous h := by
  ext χ
  simp

/-- Evaluation at the negative of a group element is the pointwise star of evaluation there. -/
@[simp]
lemma evalBoundedContinuous_neg (g : G) :
    evalBoundedContinuous (-g) = star (evalBoundedContinuous g) := by
  ext χ
  simp only [evalBoundedContinuous_apply, ofAdd_neg, map_inv,
    BoundedContinuousFunction.star_apply, RCLike.star_def]
  exact Circle.coe_inv_eq_conj _

/-- Evaluation as a monoid homomorphism from the multiplicative copy of the original group. -/
def evalMonoidHom : Multiplicative G →*
    (_root_.PontryaginDual (Multiplicative G) →ᵇ ℂ) where
  toFun g := evalBoundedContinuous g.toAdd
  map_one' := evalBoundedContinuous_zero
  map_mul' g h := by
    rw [toAdd_mul, evalBoundedContinuous_add]

/-- Evaluation of `evalMonoidHom` at a character. -/
@[simp]
lemma evalMonoidHom_apply (g : Multiplicative G)
    (χ : _root_.PontryaginDual (Multiplicative G)) :
    evalMonoidHom g χ = (χ g : ℂ) := by
  simp [evalMonoidHom]

/-- The algebra homomorphism sending a formal finite linear combination of group elements to the
corresponding finite linear combination of evaluation characters. -/
def evalAlgHom : AddMonoidAlgebra ℂ G →ₐ[ℂ]
    (_root_.PontryaginDual (Multiplicative G) →ᵇ ℂ) :=
  AddMonoidAlgebra.lift ℂ _ G evalMonoidHom

/-- Evaluation of `evalAlgHom` is the corresponding finite linear combination of characters. -/
@[simp]
lemma evalAlgHom_apply (a : AddMonoidAlgebra ℂ G)
    (χ : _root_.PontryaginDual (Multiplicative G)) :
    evalAlgHom a χ = a.coeff.sum fun g c => c * (χ (Multiplicative.ofAdd g) : ℂ) := by
  rw [evalAlgHom, AddMonoidAlgebra.lift_apply]
  simp only [Finsupp.sum, BoundedContinuousFunction.coe_sum, Finset.sum_apply,
    BoundedContinuousFunction.coe_smul, evalMonoidHom_apply, smul_eq_mul]

/-- The range of `evalAlgHom` is closed under pointwise complex conjugation. -/
lemma star_mem_range_evalAlgHom
    {f : _root_.PontryaginDual (Multiplicative G) →ᵇ ℂ}
    (hf : f ∈ evalAlgHom.range) : star f ∈ evalAlgHom.range := by
  simp only [AlgHom.mem_range] at hf ⊢
  obtain ⟨a, rfl⟩ := hf
  let z := a.map (starRingEnd ℂ).toAddMonoidHom
  let e : G ↪ G := ⟨fun g => -g, neg_injective⟩
  refine ⟨AddMonoidAlgebra.ofCoeff (z.coeff.embDomain e), ?_⟩
  ext χ
  simp [evalAlgHom, evalMonoidHom, AddMonoidAlgebra.lift_apply,
    Finsupp.sum_embDomain, z, Finsupp.sum_mapRange_index, e]

/-- The star subalgebra of bounded continuous functions generated by evaluation characters. -/
def evalPoly : StarSubalgebra ℂ
    (_root_.PontryaginDual (Multiplicative G) →ᵇ ℂ) where
  toSubalgebra := evalAlgHom.range
  star_mem' := star_mem_range_evalAlgHom

/-- The underlying subalgebra of `evalPoly` is the range of `evalAlgHom`. -/
lemma evalPoly_toSubalgebra :
    (evalPoly (G := G)).toSubalgebra = evalAlgHom.range := by
  rw [evalPoly]

/-- Membership in `evalPoly` means being a finite linear combination of evaluation
characters. -/
lemma mem_evalPoly (f : _root_.PontryaginDual (Multiplicative G) →ᵇ ℂ) :
    f ∈ evalPoly ↔
      ∃ a : AddMonoidAlgebra ℂ G,
        f = a.coeff.sum fun g c => c • evalBoundedContinuous g := by
  have hsum (a : AddMonoidAlgebra ℂ G) :
      evalAlgHom a = a.coeff.sum fun g c => c • evalBoundedContinuous g := by
    ext χ
    simp only [evalAlgHom_apply, Finsupp.sum, BoundedContinuousFunction.coe_sum,
      Finset.sum_apply, BoundedContinuousFunction.coe_smul, evalBoundedContinuous_apply,
      smul_eq_mul]
  rw [← StarSubalgebra.mem_toSubalgebra, evalPoly_toSubalgebra, AlgHom.mem_range]
  simp only [hsum, eq_comm]

/-- Every evaluation character belongs to `evalPoly`. -/
lemma evalBoundedContinuous_mem_evalPoly (g : G) :
    evalBoundedContinuous g ∈ evalPoly :=
  (mem_evalPoly _).mpr ⟨AddMonoidAlgebra.single g 1, by simp⟩

/-- The evaluation-character algebra separates points of the Pontryagin dual. -/
lemma separatesPoints_evalPoly :
    ((evalPoly : StarSubalgebra ℂ
      (_root_.PontryaginDual (Multiplicative G) →ᵇ ℂ)).map
        (BoundedContinuousFunction.toContinuousMapStarₐ ℂ)).SeparatesPoints := by
  intro χ ψ hχψ
  obtain ⟨g, hg⟩ := DFunLike.ne_iff.mp hχψ
  use evalBoundedContinuous g.toAdd
  simp only [StarSubalgebra.coe_toSubalgebra, StarSubalgebra.coe_map, Set.mem_image,
    SetLike.mem_coe, exists_exists_and_eq_and, ne_eq]
  refine ⟨⟨evalBoundedContinuous g.toAdd, evalBoundedContinuous_mem_evalPoly g.toAdd, rfl⟩, ?_⟩
  simpa using Subtype.coe_ne_coe.mpr hg

end PontryaginDual

namespace TauCeti

section OpensMeasurable

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G]
  [MeasurableSpace (_root_.PontryaginDual (Multiplicative G))]
  [OpensMeasurableSpace (_root_.PontryaginDual (Multiplicative G))]

/-- Two finite measures on the dual with the same Fourier--Stieltjes transform integrate every
finite linear combination of evaluation characters equally. -/
lemma _root_.MeasureTheory.FiniteMeasure.integral_eq_of_forall_pontryaginMeasureTransform_eq
    {P Q : FiniteMeasure (_root_.PontryaginDual (Multiplicative G))}
    (h : ∀ g, P.pontryaginMeasureTransform g = Q.pontryaginMeasureTransform g)
    {f : _root_.PontryaginDual (Multiplicative G) →ᵇ ℂ} (hf : f ∈ _root_.PontryaginDual.evalPoly) :
    ∫ χ, f χ ∂P = ∫ χ, f χ ∂Q := by
  obtain ⟨a, rfl⟩ := (_root_.PontryaginDual.mem_evalPoly f).mp hf
  simp only [Finsupp.sum, BoundedContinuousFunction.coe_sum, Finset.sum_apply,
    BoundedContinuousFunction.coe_smul,
    _root_.PontryaginDual.evalBoundedContinuous_apply,
    smul_eq_mul]
  rw [integral_finsetSum, integral_finsetSum]
  · congr with g
    rw [integral_const_mul, integral_const_mul]
    rw [← P.pontryaginMeasureTransform_apply,
      ← Q.pontryaginMeasureTransform_apply]
    exact congrArg (a.coeff g * ·) (h g)
  all_goals
    intro g _
    exact (_root_.TauCeti.PontryaginDual.integrable_coe_eval
      (Multiplicative.ofAdd g)).const_mul (a.coeff g)

end OpensMeasurable

section Polish

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G]
  [MeasurableSpace (_root_.PontryaginDual (Multiplicative G))]
  [PolishSpace (_root_.PontryaginDual (Multiplicative G))]
  [BorelSpace (_root_.PontryaginDual (Multiplicative G))]

/-- **Uniqueness of Fourier--Stieltjes measures on a Polish Pontryagin dual.** Two finite measures
on the dual are equal when their transforms agree on every element of the original group. -/
lemma _root_.MeasureTheory.FiniteMeasure.ext_of_forall_pontryaginMeasureTransform_eq
    {P Q : FiniteMeasure (_root_.PontryaginDual (Multiplicative G))}
    (h : ∀ g, P.pontryaginMeasureTransform g = Q.pontryaginMeasureTransform g) :
    P = Q :=
  FiniteMeasure.toMeasure_injective <| ext_of_forall_mem_subalgebra_integral_eq_of_polish
    _root_.PontryaginDual.separatesPoints_evalPoly fun _ hf =>
      FiniteMeasure.integral_eq_of_forall_pontryaginMeasureTransform_eq h hf

/-- The Fourier--Stieltjes transform is injective on finite measures on a Polish Pontryagin
dual. -/
lemma _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_injective :
    Function.Injective
      (fun P : FiniteMeasure (_root_.PontryaginDual (Multiplicative G)) =>
        P.pontryaginMeasureTransform) := by
  intro P Q h
  exact FiniteMeasure.ext_of_forall_pontryaginMeasureTransform_eq (congrFun h)

end Polish

section LocallyCompact

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G]
  [MeasurableSpace (_root_.PontryaginDual (Multiplicative G))]
  [BorelSpace (_root_.PontryaginDual (Multiplicative G))]

/-- **Uniqueness of inner regular Fourier--Stieltjes measures.** On the Pontryagin dual of a
locally compact abelian group, two finite inner regular measures are equal when their transforms
agree on every element of the group. No countability or metrizability is assumed. -/
lemma
    _root_.MeasureTheory.FiniteMeasure.ext_of_forall_pontryaginMeasureTransform_eq_of_innerRegular
    {P Q : FiniteMeasure (_root_.PontryaginDual (Multiplicative G))}
    [P.toMeasure.InnerRegular] [Q.toMeasure.InnerRegular]
    (h : ∀ g, P.pontryaginMeasureTransform g = Q.pontryaginMeasureTransform g) :
    P = Q :=
  FiniteMeasure.toMeasure_injective <|
    MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_innerRegular
      _root_.PontryaginDual.separatesPoints_evalPoly fun _ hf =>
        FiniteMeasure.integral_eq_of_forall_pontryaginMeasureTransform_eq h hf

/-- The Fourier--Stieltjes transform is injective on finite inner regular measures on the
Pontryagin dual of a locally compact abelian group. -/
lemma _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_injOn_innerRegular :
    Set.InjOn
      (fun P : FiniteMeasure (_root_.PontryaginDual (Multiplicative G)) =>
        P.pontryaginMeasureTransform)
      {P | P.toMeasure.InnerRegular} := by
  intro P (hP : P.toMeasure.InnerRegular) Q (hQ : Q.toMeasure.InnerRegular) h
  exact FiniteMeasure.ext_of_forall_pontryaginMeasureTransform_eq_of_innerRegular (congrFun h)

end LocallyCompact

end TauCeti

end
