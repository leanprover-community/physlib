/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Analysis.RCLike.ContinuousMap
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.Lattice

/-!
# Positive functionals on commutative C⋆-algebras are measures on the character space

Let `A` be a unital commutative C⋆-algebra, with character space `Δ = characterSpace ℂ A`.

## i. Overview

Let `A` be a unital commutative C⋆-algebra, with character space `Δ = characterSpace ℂ A`. A
linear functional `f : A → ℂ` that is nonnegative on every `star a * a` is integration against a
finite inner regular positive measure on `Δ`:

`f a = ∫ ω, ω a ∂μ`.

The Gelfand transform identifies `A` with `C(Δ, ℂ)`, and under this identification
`star a * a` runs through the nonnegative functions, so `f` becomes a positive linear functional
on `C(Δ, ℝ)`. The compact space `Δ` then carries its Riesz–Markov–Kakutani measure.

This is the commutative case of the passage from positive functionals to spectral data; it turns
a cyclic commuting family of operators, such as a unitary representation of an abelian group,
into a measure on the joint spectrum.

## ii. Key results

* `LinearMap.exists_isFiniteMeasure_integral_characterSpace_eq`: a functional nonnegative on
  `star a * a` is integration against a finite inner regular measure on the character space.
* `WeakDual.CharacterSpace.integral_apply_star_mul_self`: integrating `ω ↦ ω (star a * a)`
  gives the squared `L²` norm of `ω ↦ ω a`, so a measure representing a functional `f` computes
  `f (star a * a)`.
* `StarSubalgebra.exists_isFiniteMeasure_integral_characterSpace_eq_inner`: for a closed
  commutative star algebra of operators on a Hilbert space, each positive vector functional
  `a ↦ ⟪ξ, a ξ⟫` is integration against a finite inner regular measure on the character space.
* `StarSubalgebra.integral_norm_sq_eq_norm_apply_sq`: a measure representing such a functional
  computes `‖a ξ‖²` as the squared `L²` norm of `ω ↦ ω a`.

## iii. Table of contents

- A. Development

## iv. References

* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill (1991), Theorem 11.18 and §12.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press (1990), §2.1.
-/

public section

/-! ## A. Development -/

noncomputable section

open MeasureTheory WeakDual ComplexOrder ContinuousMap
open scoped CompactlySupported

variable {A : Type*} [CommCStarAlgebra A]

namespace TauCeti.CharacterSpaceMeasure

variable (f : A →ₗ[ℂ] ℂ)

/-- Pulled back along the Gelfand transform, a functional nonnegative on `star a * a` is
nonnegative on nonnegative real functions: such a function is `star h * h` for `h = √g`. -/
private lemma nonneg_apply_symm_realToRCLike (hf : ∀ a, 0 ≤ f (star a * a))
    {g : C(characterSpace ℂ A, ℝ)} (hg : 0 ≤ g) :
    0 ≤ f ((gelfandStarTransform A).symm (g.realToRCLike ℂ)) := by
  set h : C(characterSpace ℂ A, ℝ) := ⟨fun ω ↦ √(g ω), g.continuous.sqrt⟩
  have hgh : g = star h * h := by
    ext ω
    have hgω : 0 ≤ g ω := hg ω
    simp [h, Real.mul_self_sqrt hgω]
  rw [hgh, realToRCLike_mul, realToRCLike_star, map_mul, map_star]
  exact hf _

/-- Pulled back along the Gelfand transform, a functional nonnegative on `star a * a` is real on
real functions. -/
private lemma apply_symm_realToRCLike_eq_re (hf : ∀ a, 0 ≤ f (star a * a))
    (g : C(characterSpace ℂ A, ℝ)) :
    f ((gelfandStarTransform A).symm (g.realToRCLike ℂ)) =
      (f ((gelfandStarTransform A).symm (g.realToRCLike ℂ))).re := by
  have hp := (Complex.nonneg_iff.mp (nonneg_apply_symm_realToRCLike f hf (posPart_nonneg g))).2
  have hn := (Complex.nonneg_iff.mp (nonneg_apply_symm_realToRCLike f hf (negPart_nonneg g))).2
  rw [← posPart_sub_negPart g, ← realToRCLikeStarAlgHom_apply, map_sub, map_sub, map_sub,
    realToRCLikeStarAlgHom_apply, realToRCLikeStarAlgHom_apply]
  set p := f ((gelfandStarTransform A).symm (g⁺.realToRCLike ℂ))
  set n := f ((gelfandStarTransform A).symm (g⁻.realToRCLike ℂ))
  apply Complex.ext <;> simp [← hp, ← hn]

/-- The positive linear functional on `C_c(Δ, ℝ) = C(Δ, ℝ)` induced by `f` through the Gelfand
transform. -/
private def realFunctional (hf : ∀ a, 0 ≤ f (star a * a)) :
    C_c(characterSpace ℂ A, ℝ) →ₚ[ℝ] ℝ where
  toFun g := (f ((gelfandStarTransform A).symm (g.toContinuousMap.realToRCLike ℂ))).re
  map_add' g h := by
    have : (g + h).toContinuousMap.realToRCLike ℂ =
        g.toContinuousMap.realToRCLike ℂ + h.toContinuousMap.realToRCLike ℂ := by
      ext; simp
    rw [this, map_add, map_add, Complex.add_re]
  map_smul' c g := by
    have : (c • g).toContinuousMap.realToRCLike ℂ =
        (c : ℂ) • g.toContinuousMap.realToRCLike ℂ := by
      ext; simp
    rw [this, map_smul, map_smul, smul_eq_mul, Complex.re_ofReal_mul, RingHom.id_apply,
      smul_eq_mul]
  monotone' g h hgh := by
    have hle : 0 ≤ h.toContinuousMap - g.toContinuousMap :=
      sub_nonneg.mpr fun ω ↦ hgh ω
    have := (Complex.nonneg_iff.mp (nonneg_apply_symm_realToRCLike f hf hle)).1
    rw [← realToRCLikeStarAlgHom_apply, map_sub, map_sub, map_sub, Complex.sub_re] at this
    simp only [realToRCLikeStarAlgHom_apply] at this
    linarith

private lemma realFunctional_apply (hf : ∀ a, 0 ≤ f (star a * a))
    (g : C_c(characterSpace ℂ A, ℝ)) :
    realFunctional f hf g =
      (f ((gelfandStarTransform A).symm (g.toContinuousMap.realToRCLike ℂ))).re :=
  rfl

end TauCeti.CharacterSpaceMeasure

open TauCeti.CharacterSpaceMeasure

variable [MeasurableSpace (characterSpace ℂ A)] [BorelSpace (characterSpace ℂ A)]

/-- **Positive functionals on a commutative C⋆-algebra are measures on its character space.**
A linear functional on a unital commutative C⋆-algebra that is nonnegative on every
`star a * a` is integration against a finite inner regular positive measure `μ` on the
character space: `f a = ∫ ω, ω a ∂μ`. -/
lemma LinearMap.exists_isFiniteMeasure_integral_characterSpace_eq (f : A →ₗ[ℂ] ℂ)
    (hf : ∀ a, 0 ≤ f (star a * a)) :
    ∃ μ : Measure (characterSpace ℂ A), IsFiniteMeasure μ ∧ μ.InnerRegular ∧
      ∀ a, f a = ∫ ω, ω a ∂μ := by
  set Λ := realFunctional f hf
  set μ := RealRMK.rieszMeasure Λ
  refine ⟨μ, inferInstance, inferInstance, fun a ↦ ?_⟩
  -- Split the Gelfand transform `F` of `a` into its real part `u` and imaginary part `v`.
  set F := gelfandStarTransform A a
  let u : C(characterSpace ℂ A, ℝ) := ⟨fun ω ↦ (F ω).re, Complex.continuous_re.comp F.continuous⟩
  let v : C(characterSpace ℂ A, ℝ) := ⟨fun ω ↦ (F ω).im, Complex.continuous_im.comp F.continuous⟩
  have hF : F = u.realToRCLike ℂ + Complex.I • v.realToRCLike ℂ := by
    ext ω
    simp [u, v, mul_comm Complex.I]
  -- On a real function, `f` agrees with the Riesz–Markov–Kakutani integral.
  have hreal (g : C(characterSpace ℂ A, ℝ)) :
      f ((gelfandStarTransform A).symm (g.realToRCLike ℂ)) = ((∫ ω, g ω ∂μ : ℝ) : ℂ) := by
    have h := RealRMK.integral_rieszMeasure Λ ⟨g, .of_compactSpace _⟩
    rw [realFunctional_apply, CompactlySupportedContinuousMap.coe_mk] at h
    rw [apply_symm_realToRCLike_eq_re f hf g, h]
  have hFint : Integrable F μ :=
    F.continuous.integrable_of_hasCompactSupport (.of_compactSpace _)
  calc f a = f ((gelfandStarTransform A).symm F) := by simp [F]
    _ = (∫ ω, u ω ∂μ : ℝ) + ((∫ ω, v ω ∂μ : ℝ) : ℂ) * Complex.I := by
      rw [hF, map_add, map_smul, map_add, map_smul, hreal, hreal, smul_eq_mul, mul_comm]
    _ = ∫ ω, F ω ∂μ := integral_re_add_im hFint
    _ = ∫ ω, ω a ∂μ := by simp [F]

/-- For a measure `μ` on the character space of a unital C⋆-algebra, integrating
`ω ↦ ω (star a * a) = |ω a|²` gives the squared `L²` norm of `ω ↦ ω a`. Hence if `μ` represents a
functional `f`, as in `LinearMap.exists_isFiniteMeasure_integral_characterSpace_eq`, then
`f (star a * a) = ∫ |ω a|² dμ(ω)`. -/
lemma WeakDual.CharacterSpace.integral_apply_star_mul_self {E : Type*} [CStarAlgebra E]
    [MeasurableSpace (characterSpace ℂ E)] (μ : Measure (characterSpace ℂ E)) (a : E) :
    ∫ ω, ω (star a * a) ∂μ = ((∫ ω, ‖ω a‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  simp_rw [map_mul, map_star, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow]
  exact integral_complex_ofReal

section Operator

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (B : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (B : Set (H →L[ℂ] H))]
  [MeasurableSpace (characterSpace ℂ B)]

omit [IsClosed (B : Set (H →L[ℂ] H))] [MeasurableSpace (characterSpace ℂ B)] in
/-- For a star algebra `B` of operators, the positive vector functional of `ξ` takes the value
`‖a ξ‖²` at `star a * a`. -/
private lemma inner_star_mul_self_apply (ξ : H) (a : B) :
    ⟪ξ, ((star a * a : B) : H →L[ℂ] H) ξ⟫_ℂ = ((‖(a : H →L[ℂ] H) ξ‖ ^ 2 : ℝ) : ℂ) := by
  simp only [MulMemClass.coe_mul, StarMemClass.coe_star, ContinuousLinearMap.star_eq_adjoint,
    mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- For a closed star algebra `B` of operators, if a measure `μ` on the character space
represents the positive vector functional of `ξ`, then `∫ |ω a|² dμ(ω) = ‖a ξ‖²` for every
`a ∈ B`. -/
lemma StarSubalgebra.integral_norm_sq_eq_norm_apply_sq {μ : Measure (characterSpace ℂ B)}
    {ξ : H} (hμ : ∀ a : B, ⟪ξ, (a : H →L[ℂ] H) ξ⟫_ℂ = ∫ ω, ω a ∂μ) (a : B) :
    ∫ ω, ‖ω a‖ ^ 2 ∂μ = ‖(a : H →L[ℂ] H) ξ‖ ^ 2 := by
  have h := hμ (star a * a)
  rw [inner_star_mul_self_apply, WeakDual.CharacterSpace.integral_apply_star_mul_self] at h
  exact_mod_cast h.symm

open scoped IsMulCommutative

variable [IsMulCommutative B] [BorelSpace (characterSpace ℂ B)]

/-- **Positive vector functionals are measures on the character space.** For a closed
commutative star algebra `B` of operators on a complex Hilbert space and a vector `ξ`, the
positive vector functional `a ↦ ⟪ξ, a ξ⟫` is integration against a finite inner regular positive
measure on the character space of `B`. -/
lemma StarSubalgebra.exists_isFiniteMeasure_integral_characterSpace_eq_inner (ξ : H) :
    ∃ μ : Measure (characterSpace ℂ B), IsFiniteMeasure μ ∧ μ.InnerRegular ∧
      ∀ a : B, ⟪ξ, (a : H →L[ℂ] H) ξ⟫_ℂ = ∫ ω, ω a ∂μ := by
  let f : B →ₗ[ℂ] ℂ :=
    { toFun a := ⟪ξ, (a : H →L[ℂ] H) ξ⟫_ℂ
      map_add' a b := by simp [inner_add_right]
      map_smul' c a := by simp [inner_smul_right] }
  refine f.exists_isFiniteMeasure_integral_characterSpace_eq fun a ↦ ?_
  simp only [f, LinearMap.coe_mk, AddHom.coe_mk, inner_star_mul_self_apply]
  exact Complex.zero_le_real.mpr (sq_nonneg _)

end Operator
