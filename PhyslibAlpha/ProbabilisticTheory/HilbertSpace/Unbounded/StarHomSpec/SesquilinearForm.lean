/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.UnitaryInfra.SesquilinearForm
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.RCLike.ContinuousMap
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!

# The spectral forms of a representation of continuous functions

Complex measures `⟪y, E(·) x⟫` of a unital ⋆-homomorphism `C(X, ℂ) → B(H)` and their sesquilinear
forms.

## i. Overview

For a unital ⋆-homomorphism `Φ` from the continuous functions on a compact Hausdorff space to the
bounded operators of a Hilbert space, the functional `f ↦ ⟪x, Φ f y⟫` is given, by the
Riesz–Markov–Kakutani theorem and polarization, by a complex measure. This is the construction of
`UnitaryInfra.SesquilinearForm` with the continuous functional calculus of a normal operator
replaced by an arbitrary ⋆-homomorphism, so that it applies to the joint spectral theory of
commuting families.

## ii. Key results

- `starHomScalarMeasure` : the measure representing `f ↦ ⟪x, Φ f x⟫`.
- `polarizedStarHomScalarMeasure` : the complex measure representing `f ↦ ⟪y, Φ f x⟫`.
- `starHomSesquilinearForm` : the bounded sesquilinear form of a measurable set.

## iii. Table of contents

- A. Positive scalar functionals from a ⋆-homomorphism
- B. Sesquilinearity of the polarized measure
- C. Polarization
- D. Riesz representation of the polarized measure

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open MeasureTheory Set Topology
open scoped ComplexOrder CStarAlgebra InnerProductSpace

namespace QuantumMechanics

/-! ## A. Positive scalar functionals from a ⋆-homomorphism -/

section StarHomScalar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [CompactSpace X] (Φ : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- Regard a real-valued continuous function on the spectrum of a normal operator as a complex
valued one.  Keeping this map explicit prevents the real/complex scalar changes in the Riesz
construction from being hidden in coercions. -/
noncomputable def realToComplex
    (f : CompactlySupportedContinuousMap (X) ℝ) :
    C(X, ℂ) :=
  ContinuousMap.compStarAlgHom (X) (RCLike.ofRealStarAlgHom ℂ)
    RCLike.continuous_ofReal f.toContinuousMap

omit [T2Space X] [BorelSpace X] [CompactSpace X] [MeasurableSpace X] in
omit [CompleteSpace H] in
@[simp]
lemma realToComplex_apply
    (f : CompactlySupportedContinuousMap (X) ℝ) (z : X) :
    realToComplex f z = f z := by
  rfl

omit [CompleteSpace H] [T2Space X] [BorelSpace X] [CompactSpace X] [MeasurableSpace X] in
lemma realToComplex_add
    (f g : CompactlySupportedContinuousMap (X) ℝ) :
    realToComplex (f + g) =
      realToComplex f + realToComplex g := by
  ext z
  simp

omit [CompleteSpace H] [T2Space X] [BorelSpace X] [CompactSpace X] [MeasurableSpace X] in
lemma realToComplex_smul (r : ℝ)
    (f : CompactlySupportedContinuousMap (X) ℝ) :
    realToComplex (r • f) =
      (r : ℂ) • realToComplex f := by
  ext z
  simp

/-- The operator obtained by applying the complex continuous functional calculus to a real test
function.   -/
noncomputable def starHomRealOperator
    (f : CompactlySupportedContinuousMap (X) ℝ) : H →L[ℂ] H :=
  Φ (realToComplex f)

omit [T2Space X] [BorelSpace X] [CompactSpace X] [MeasurableSpace X] in
lemma starHomRealOperator_isSelfAdjoint
    (f : CompactlySupportedContinuousMap (X) ℝ) :
    IsSelfAdjoint (starHomRealOperator Φ f) := by
  have hfstar : star (realToComplex f) =
      realToComplex f := by
    ext z
    change starRingEnd ℂ (f z : ℂ) = f z
    simp
  change star (Φ (realToComplex f)) = _
  rw [← map_star, hfstar]
  rfl

omit [T2Space X] [BorelSpace X] [CompactSpace X] [MeasurableSpace X] in
lemma starHomRealOperator_nonneg
    (f : CompactlySupportedContinuousMap (X) ℝ)
    (hf : ∀ z, 0 ≤ f z) :
    ContinuousLinearMap.IsPositive (starHomRealOperator Φ f) := by
  let gR : C(X, ℝ) :=
    ⟨fun z ↦ Real.sqrt (f z), Real.continuous_sqrt.comp f.continuous⟩
  let g : C(X, ℂ) :=
    ContinuousMap.compStarAlgHom (X) (RCLike.ofRealStarAlgHom ℂ)
      RCLike.continuous_ofReal gR
  have hsq : realToComplex f = star g * g := by
    ext z
    change (f z : ℂ) = starRingEnd ℂ (Real.sqrt (f z) : ℂ) * Real.sqrt (f z)
    simp [← Complex.ofReal_mul, Real.mul_self_sqrt (hf z)]
  change ContinuousLinearMap.IsPositive (Φ (realToComplex f))
  rw [hsq, map_mul, map_star]
  simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] using
    ContinuousLinearMap.isPositive_adjoint_comp_self (Φ g)

/-- The vector state of the continuous functional calculus, restricted to real test functions.
The positivity proof is the square-root argument above; this is the exact input required by
Riesz--Markov. -/
noncomputable def starHomScalarFunctional (x : H) :
    CompactPositiveFunctional (X := X) where
  functional := PositiveLinearMap.mk₀
    { toFun := fun f ↦ RCLike.re ⟪x, starHomRealOperator Φ f x⟫_ℂ
      map_add' := by
        intro f g
        change RCLike.re ⟪x, starHomRealOperator Φ (f + g) x⟫_ℂ = _
        rw [starHomRealOperator, realToComplex_add, map_add,
          add_apply, inner_add_right]
        simp [starHomRealOperator]
      map_smul' := by
        intro r f
        change RCLike.re ⟪x, starHomRealOperator Φ (r • f) x⟫_ℂ = _
        rw [starHomRealOperator, realToComplex_smul, map_smul,
          smul_apply, inner_smul_right]
        simp [starHomRealOperator] }
    (fun f hf ↦ (starHomRealOperator_nonneg Φ f hf).re_inner_nonneg_right x)

omit [T2Space X] [BorelSpace X] [MeasurableSpace X] in
lemma starHomScalarFunctional_apply (x : H)
    (f : CompactlySupportedContinuousMap (X) ℝ) :
    (starHomScalarFunctional Φ x).functional f =
      RCLike.re ⟪x, starHomRealOperator Φ f x⟫_ℂ := by
  rfl

/-- The scalar spectral measure supplied by Riesz--Markov for the vector state at `x`. -/
noncomputable def starHomScalarMeasure (x : H) : Measure (X) :=
  (starHomScalarFunctional Φ x).measure

instance starHomScalarMeasure_regular (x : H) : (starHomScalarMeasure Φ x).Regular := by
  dsimp [starHomScalarMeasure]
  infer_instance

instance starHomScalarMeasure_isFinite (x : H) : IsFiniteMeasure (starHomScalarMeasure Φ x) := by
  dsimp [starHomScalarMeasure, CompactPositiveFunctional.measure]
  infer_instance

lemma starHomScalarMeasure_integral (x : H)
    (f : CompactlySupportedContinuousMap (X) ℝ) :
    ∫ z, f z ∂starHomScalarMeasure Φ x =
      RCLike.re ⟪x, starHomRealOperator Φ f x⟫_ℂ := by
  exact CompactPositiveFunctional.integral (starHomScalarFunctional Φ x) f

lemma starHomScalarMeasure_integral_complex (x : H)
    (f : CompactlySupportedContinuousMap (X) ℝ) :
    ((∫ z, f z ∂starHomScalarMeasure Φ x : ℝ) : ℂ) =
      ⟪starHomRealOperator Φ f x, x⟫_ℂ := by
  rw [starHomScalarMeasure_integral]
  let A := starHomRealOperator Φ f
  have hA : IsSelfAdjoint A := starHomRealOperator_isSelfAdjoint Φ f
  have hreal :
      (RCLike.re ⟪x, A x⟫_ℂ : ℂ) = ⟪A x, x⟫_ℂ := by
    calc
      (RCLike.re ⟪x, A x⟫_ℂ : ℂ) =
          (RCLike.re ⟪A x, x⟫_ℂ : ℂ) := by
            rw [inner_re_symm]
      _ = ⟪A x, x⟫_ℂ :=
        Complex.conj_eq_iff_re.mp (hA.isSymmetric.conj_inner_sym x x)
  exact hreal

/-- The integral of a real function against the polarized measure. -/
noncomputable def polarizedStarHomRealIntegral
    (f : CompactlySupportedContinuousMap (X) ℝ) (x y : H) : ℂ :=
  ((1 / 4 : ℝ) *
      ((∫ z, f z ∂starHomScalarMeasure Φ (x + y)) -
        ∫ z, f z ∂starHomScalarMeasure Φ (x - y)) : ℂ) +
    Complex.I * ((1 / 4 : ℝ) *
      ((∫ z, f z ∂starHomScalarMeasure Φ (x + Complex.I • y)) -
        ∫ z, f z ∂starHomScalarMeasure Φ (x - Complex.I • y)) : ℂ)

lemma polarizedStarHomRealIntegral_eq_inner
    (f : CompactlySupportedContinuousMap (X) ℝ) (x y : H) :
    polarizedStarHomRealIntegral Φ f x y =
      ⟪y, starHomRealOperator Φ f x⟫_ℂ := by
  let A := starHomRealOperator Φ f
  have hdiag (v : H) :
      ((∫ z, f z ∂starHomScalarMeasure Φ v : ℝ) : ℂ) = ⟪A v, v⟫_ℂ := by
    exact starHomScalarMeasure_integral_complex Φ v f
  have hpolar := inner_map_polarization (A : H →ₗ[ℂ] H) x y
  have hsym : ⟪A y, x⟫_ℂ = ⟪y, A x⟫_ℂ :=
    (starHomRealOperator_isSelfAdjoint Φ f).isSymmetric y x
  rw [← hsym]
  simp only [polarizedStarHomRealIntegral, hdiag (x + y), hdiag (x - y),
    hdiag (x + Complex.I • y), hdiag (x - Complex.I • y)]
  calc
    _ = (⟪A (x + y), x + y⟫_ℂ - ⟪A (x - y), x - y⟫_ℂ +
      Complex.I * ⟪A (x + Complex.I • y), x + Complex.I • y⟫_ℂ -
      Complex.I * ⟪A (x - Complex.I • y), x - Complex.I • y⟫_ℂ) / 4 := by
      norm_num
      ring
    _ = _ := hpolar.symm

lemma starHomScalarMeasure_parallelogram (x y : H) :
    starHomScalarMeasure Φ (x + y) + starHomScalarMeasure Φ (x - y) =
      (starHomScalarMeasure Φ x + starHomScalarMeasure Φ x) +
        (starHomScalarMeasure Φ y + starHomScalarMeasure Φ y) := by
  apply MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hf : ∀ v : H, Integrable (f : X → ℝ) (starHomScalarMeasure Φ v) := by
    intro v
    rw [← integrableOn_univ]
    exact f.continuous.continuousOn.integrableOn_compact isCompact_univ
  have hxx : Integrable (f : X → ℝ)
      (starHomScalarMeasure Φ x + starHomScalarMeasure Φ x) :=
    integrable_add_measure.mpr ⟨hf x, hf x⟩
  have hyy : Integrable (f : X → ℝ)
      (starHomScalarMeasure Φ y + starHomScalarMeasure Φ y) :=
    integrable_add_measure.mpr ⟨hf y, hf y⟩
  rw [integral_add_measure (hf (x + y)) (hf (x - y)),
    integral_add_measure hxx hyy,
    integral_add_measure (hf x) (hf x), integral_add_measure (hf y) (hf y)]
  simp only [starHomScalarMeasure_integral]
  let A := starHomRealOperator Φ f
  have hA : IsSelfAdjoint A := starHomRealOperator_isSelfAdjoint Φ f
  change RCLike.re ⟪x + y, A (x + y)⟫_ℂ +
      RCLike.re ⟪x - y, A (x - y)⟫_ℂ =
    (RCLike.re ⟪x, A x⟫_ℂ + RCLike.re ⟪x, A x⟫_ℂ) +
      (RCLike.re ⟪y, A y⟫_ℂ + RCLike.re ⟪y, A y⟫_ℂ)
  simp only [map_add, map_neg, inner_add_left, inner_add_right, sub_eq_add_neg,
    inner_neg_left, inner_neg_right]
  ring

lemma starHomScalarMeasure_neg (x : H) :
    starHomScalarMeasure Φ (-x) = starHomScalarMeasure Φ x := by
  apply MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hfx : Integrable (f : X → ℝ) (starHomScalarMeasure Φ x) := by
    rw [← integrableOn_univ]
    exact f.continuous.continuousOn.integrableOn_compact isCompact_univ
  simp only [starHomScalarMeasure_integral]
  simp [inner_neg_left, inner_neg_right]

lemma starHomScalarMeasure_I_smul (x : H) :
    starHomScalarMeasure Φ (Complex.I • x) = starHomScalarMeasure Φ x := by
  apply MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hfx : Integrable (f : X → ℝ) (starHomScalarMeasure Φ x) := by
    rw [← integrableOn_univ]
    exact f.continuous.continuousOn.integrableOn_compact isCompact_univ
  have hix : Integrable (f : X → ℝ)
      (starHomScalarMeasure Φ (Complex.I • x)) := by
    rw [← integrableOn_univ]
    exact f.continuous.continuousOn.integrableOn_compact isCompact_univ
  simp only [starHomScalarMeasure_integral]
  simp [inner_smul_left, inner_smul_right]

/-- The complex measure `⟪y, E(·) x⟫`, obtained by polarizing the four measures `⟪v, E(·) v⟫`. -/
noncomputable def polarizedStarHomScalarMeasure (x y : H) : ComplexMeasure (X) :=
  let muPlus := (starHomScalarMeasure Φ (x + y)).toSignedMeasure
  let muMinus := (starHomScalarMeasure Φ (x - y)).toSignedMeasure
  let nuPlus := (starHomScalarMeasure Φ (x + Complex.I • y)).toSignedMeasure
  let nuMinus := (starHomScalarMeasure Φ (x - Complex.I • y)).toSignedMeasure
  ((1 / 4 : ℝ) • (muPlus - muMinus)).toComplexMeasure
  ((1 / 4 : ℝ) • (nuPlus - nuMinus))

lemma polarizedStarHomScalarMeasure_isFiniteMeasure (x y : H) :
    IsFiniteMeasure
      (polarizedStarHomScalarMeasure Φ x y).variation := by
  unfold polarizedStarHomScalarMeasure
  have hsub (a b : H) : IsFiniteMeasure
      (((1 / 4 : ℝ) • ((starHomScalarMeasure Φ a).toSignedMeasure -
        (starHomScalarMeasure Φ b).toSignedMeasure)).variation) := by
    let : IsFiniteMeasure (starHomScalarMeasure Φ a).toSignedMeasure.variation := by
      rw [Measure.variation_toSignedMeasure]
      infer_instance
    let : IsFiniteMeasure (starHomScalarMeasure Φ b).toSignedMeasure.variation := by
      rw [Measure.variation_toSignedMeasure]
      infer_instance
    apply isFiniteMeasure_of_le (starHomScalarMeasure Φ a + starHomScalarMeasure Φ b)
    rw [MeasureTheory.VectorMeasure.variation_smul]
    have hv : ((starHomScalarMeasure Φ a).toSignedMeasure -
        (starHomScalarMeasure Φ b).toSignedMeasure).variation ≤
        starHomScalarMeasure Φ a + starHomScalarMeasure Φ b := by
      simpa only [Measure.variation_toSignedMeasure] using
        (MeasureTheory.VectorMeasure.variation_sub_le
          (μ := (starHomScalarMeasure Φ a).toSignedMeasure)
          (ν := (starHomScalarMeasure Φ b).toSignedMeasure))
    calc
      ‖(1 / 4 : ℝ)‖₊ •
          ((starHomScalarMeasure Φ a).toSignedMeasure -
            (starHomScalarMeasure Φ b).toSignedMeasure).variation ≤
          (1 : ENNReal) • ((starHomScalarMeasure Φ a).toSignedMeasure -
            (starHomScalarMeasure Φ b).toSignedMeasure).variation := by
        change ((‖(1 / 4 : ℝ)‖₊ : NNReal) : ENNReal) •
          ((starHomScalarMeasure Φ a).toSignedMeasure -
            (starHomScalarMeasure Φ b).toSignedMeasure).variation ≤
          (1 : ENNReal) • ((starHomScalarMeasure Φ a).toSignedMeasure -
            (starHomScalarMeasure Φ b).toSignedMeasure).variation
        gcongr
        norm_num
      _ ≤ (1 : ENNReal) • (starHomScalarMeasure Φ a + starHomScalarMeasure Φ b) := by
        simpa only [one_smul] using hv
      _ = starHomScalarMeasure Φ a + starHomScalarMeasure Φ b := by simp
  let hplus : IsFiniteMeasure
      (((1 / 4 : ℝ) • ((starHomScalarMeasure Φ (x + y)).toSignedMeasure -
        (starHomScalarMeasure Φ (x - y)).toSignedMeasure)).variation) :=
    hsub (x + y) (x - y)
  let hminus : IsFiniteMeasure
      (((1 / 4 : ℝ) • ((starHomScalarMeasure Φ (x + Complex.I • y)).toSignedMeasure -
        (starHomScalarMeasure Φ (x - Complex.I • y)).toSignedMeasure)).variation) :=
    hsub (x + Complex.I • y) (x - Complex.I • y)
  exact isFiniteMeasure_toComplexMeasure
    (((1 / 4 : ℝ) • ((starHomScalarMeasure Φ (x + y)).toSignedMeasure -
      (starHomScalarMeasure Φ (x - y)).toSignedMeasure)))
    (((1 / 4 : ℝ) • ((starHomScalarMeasure Φ (x + Complex.I • y)).toSignedMeasure -
      (starHomScalarMeasure Φ (x - Complex.I • y)).toSignedMeasure)))

lemma polarizedStarHomScalarMeasure_complexIntegral
    (f : CompactlySupportedContinuousMap (X) ℝ) (x y : H) :
    ∫ᵛ z, (f z : ℂ) ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      polarizedStarHomScalarMeasure Φ x y] =
      polarizedStarHomRealIntegral Φ f x y := by
  let fC : X → ℂ := fun z ↦ f z
  have hfC : Continuous fC := by
    fun_prop
  have hplus : Integrable fC (starHomScalarMeasure Φ (x + y)) := by
    rw [← integrableOn_univ]
    exact hfC.continuousOn.integrableOn_compact isCompact_univ
  have hminus : Integrable fC (starHomScalarMeasure Φ (x - y)) := by
    rw [← integrableOn_univ]
    exact hfC.continuousOn.integrableOn_compact isCompact_univ
  have hip : Integrable fC
      (starHomScalarMeasure Φ (x + Complex.I • y)) := by
    rw [← integrableOn_univ]
    exact hfC.continuousOn.integrableOn_compact isCompact_univ
  have him : Integrable fC
      (starHomScalarMeasure Φ (x - Complex.I • y)) := by
    rw [← integrableOn_univ]
    exact hfC.continuousOn.integrableOn_compact isCompact_univ
  let μplus := starHomScalarMeasure Φ (x + y)
  let μminus := starHomScalarMeasure Φ (x - y)
  let νplus := starHomScalarMeasure Φ (x + Complex.I • y)
  let νminus := starHomScalarMeasure Φ (x - Complex.I • y)
  change ∫ᵛ z, fC z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      ((1 / 4 : ℝ) • (μplus.toSignedMeasure - μminus.toSignedMeasure)).toComplexMeasure
        ((1 / 4 : ℝ) • (νplus.toSignedMeasure - νminus.toSignedMeasure))] = _
  have hreal :
      (((1 / 4 : ℝ) • (μplus.toSignedMeasure - μminus.toSignedMeasure)).mapRange
        Complex.ofRealCLM.toAddMonoidHom Complex.ofRealCLM.continuous).Integrable fC := by
    rw [VectorMeasure.mapRange_smul, mapRange_sub_toSignedMeasure μplus μminus]
    exact (integrable_mapRange_ofReal_signedMeasure μplus fC hplus).sub_vectorMeasure
      (integrable_mapRange_ofReal_signedMeasure μminus fC hminus) |>.smul_vectorMeasure _
  have himag :
      (((1 / 4 : ℝ) • (νplus.toSignedMeasure - νminus.toSignedMeasure)).mapRange
        imaginaryOfRealCLM.toAddMonoidHom imaginaryOfRealCLM.continuous).Integrable fC := by
    rw [VectorMeasure.mapRange_smul, mapRange_sub_toSignedMeasure νplus νminus]
    exact (integrable_mapRange_imaginaryOfReal_signedMeasure νplus fC hip).sub_vectorMeasure
      (integrable_mapRange_imaginaryOfReal_signedMeasure νminus fC him) |>.smul_vectorMeasure _
  rw [integral_toComplexMeasure_eq_add_mapRange _ _ fC hreal himag]
  rw [integral_mapRange_ofReal_signedDifference μplus μminus (1 / 4 : ℝ) fC hplus hminus,
    integral_mapRange_imaginaryOfReal_signedDifference νplus νminus (1 / 4 : ℝ) fC hip him]
  dsimp [fC]
  simp only [integral_complex_ofReal]
  simp [polarizedStarHomRealIntegral, μplus, μminus, νplus, νminus]
  ring

lemma polarizedStarHomScalarMeasure_complexIntegral_eq_inner
    (f : CompactlySupportedContinuousMap (X) ℝ) (x y : H) :
    ∫ᵛ z, (f z : ℂ) ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      polarizedStarHomScalarMeasure Φ x y] =
      ⟪y, starHomRealOperator Φ f x⟫_ℂ := by
  rw [polarizedStarHomScalarMeasure_complexIntegral]
  exact polarizedStarHomRealIntegral_eq_inner Φ f x y

lemma polarizedStarHomScalarMeasure_apply {x y : H}
    {S : Set (X)} (hS : MeasurableSet S) :
    polarizedStarHomScalarMeasure Φ x y S =
      ((1 / 4 : ℝ) *
          ((starHomScalarMeasure Φ (x + y)).real S -
            (starHomScalarMeasure Φ (x - y)).real S) : ℂ) +
        Complex.I * ((1 / 4 : ℝ) *
          ((starHomScalarMeasure Φ (x + Complex.I • y)).real S -
            (starHomScalarMeasure Φ (x - Complex.I • y)).real S) : ℂ) := by
  simp [polarizedStarHomScalarMeasure, MeasureTheory.SignedMeasure.toComplexMeasure_apply,
    MeasureTheory.Measure.toSignedMeasure_apply_measurable hS]
  apply Complex.ext <;> simp

/-! ## B. Sesquilinearity of the polarized measure -/

/-- The real-valued version of the parallelogram law, at a fixed (not necessarily measurable)
set `S`.  This is the algebraic engine behind the sesquilinearity proofs below. -/
lemma starHomScalarMeasure_real_parallelogram (a b : H) (S : Set (X)) :
    (starHomScalarMeasure Φ (a + b)).real S + (starHomScalarMeasure Φ (a - b)).real S =
      2 * (starHomScalarMeasure Φ a).real S + 2 * (starHomScalarMeasure Φ b).real S := by
  have hS : starHomScalarMeasure Φ (a + b) S + starHomScalarMeasure Φ (a - b) S =
      starHomScalarMeasure Φ a S + starHomScalarMeasure Φ a S +
        (starHomScalarMeasure Φ b S + starHomScalarMeasure Φ b S) :=
    congrArg (fun μ : Measure (X) => μ S) (starHomScalarMeasure_parallelogram Φ a b)
  have hne : ∀ v : H, starHomScalarMeasure Φ v S ≠ ⊤ := fun v => measure_ne_top _ S
  have hreal := congrArg ENNReal.toReal hS
  rw [ENNReal.toReal_add (hne _) (hne _)] at hreal
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hne _, hne _⟩)
      (ENNReal.add_ne_top.mpr ⟨hne _, hne _⟩)] at hreal
  rw [ENNReal.toReal_add (hne _) (hne _), ENNReal.toReal_add (hne _) (hne _)] at hreal
  simpa [measureReal_def, two_mul] using hreal

lemma starHomScalarMeasure_real_neg (a : H) (S : Set (X)) :
    (starHomScalarMeasure Φ (-a)).real S = (starHomScalarMeasure Φ a).real S := by
  rw [starHomScalarMeasure_neg]

lemma starHomScalarMeasure_real_I_smul (a : H) (S : Set (X)) :
    (starHomScalarMeasure Φ (Complex.I • a)).real S = (starHomScalarMeasure Φ a).real S := by
  rw [starHomScalarMeasure_I_smul]

lemma starHomScalarMeasure_real_nonneg (a : H) (S : Set (X)) :
    0 ≤ (starHomScalarMeasure Φ a).real S := ENNReal.toReal_nonneg

/-- The Riesz measure for the vector state at `x` has total mass `‖x‖ ^ 2`: the vector-state
counterpart of `Φ 1 = 1`. -/
lemma starHomScalarMeasure_real_univ (x : H) :
    (starHomScalarMeasure Φ x).real Set.univ = ‖x‖ ^ 2 := by
  let f1 : CompactlySupportedContinuousMap (X) ℝ :=
    { toFun := fun _ => 1
      continuous_toFun := continuous_const
      hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
  have hf1val : ∀ z, f1 z = 1 := fun _ => rfl
  have hop : starHomRealOperator Φ f1 = 1 := by
    have hone : realToComplex f1 = 1 := by
      ext z
      simp [realToComplex_apply, hf1val]
    unfold starHomRealOperator
    rw [hone, map_one]
  have hint := starHomScalarMeasure_integral Φ x f1
  rw [hop] at hint
  have hint2 : ∫ z, f1 z ∂starHomScalarMeasure Φ x = (starHomScalarMeasure Φ x).real Set.univ := by
    simp only [hf1val]
    rw [MeasureTheory.integral_const]
    simp [measureReal_def]
  rw [hint2] at hint
  rw [hint, one_apply_eq_self, inner_self_eq_norm_sq]

lemma starHomScalarMeasure_real_le_univ (a : H) (S : Set (X)) :
    (starHomScalarMeasure Φ a).real S ≤ ‖a‖ ^ 2 := by
  rw [← starHomScalarMeasure_real_univ Φ a]
  apply MeasureTheory.measureReal_mono (Set.subset_univ S)

/-- The real polarization `Q(a + b) - Q(a - b)` of the diagonal measures is symmetric in `a` and
`b`. -/
lemma starHomScalarMeasure_real_polar_symm (a b : H) (S : Set (X)) :
    (starHomScalarMeasure Φ (a + b)).real S - (starHomScalarMeasure Φ (a - b)).real S =
      (starHomScalarMeasure Φ (b + a)).real S - (starHomScalarMeasure Φ (b - a)).real S := by
  have hba : b - a = -(a - b) := by abel
  rw [add_comm b a, hba, starHomScalarMeasure_real_neg]

/-- First-argument additivity of the real polarization `Q(a+b) - Q(a-b)`, established by pure
algebra from the parallelogram law (`starHomScalarMeasure_real_parallelogram`); no continuity is
needed for this step, matching the classical Jordan--von Neumann polarization argument
(`Mathlib.Analysis.InnerProductSpace.OfNorm`).   -/
lemma starHomScalarMeasure_real_polar_add_left (x y z : H) (S : Set (X)) :
    (starHomScalarMeasure Φ (x + y + z)).real S - (starHomScalarMeasure Φ (x + y - z)).real S =
      ((starHomScalarMeasure Φ (x + z)).real S - (starHomScalarMeasure Φ (x - z)).real S) +
        ((starHomScalarMeasure Φ (y + z)).real S - (starHomScalarMeasure Φ (y - z)).real S) := by
  have h1 := starHomScalarMeasure_real_parallelogram Φ (x + y + z) (x - z) S
  have h2 := starHomScalarMeasure_real_parallelogram Φ (x + y - z) (x + z) S
  have h3 := starHomScalarMeasure_real_parallelogram Φ (y + z) z S
  have h4 := starHomScalarMeasure_real_parallelogram Φ (y - z) z S
  have e1 : x + y + z + (x - z) = 2 • x + y := by abel
  have e2 : x + y + z - (x - z) = y + 2 • z := by abel
  have e3 : x + y - z + (x + z) = 2 • x + y := by abel
  have e4 : x + y - z - (x + z) = y - 2 • z := by abel
  have e5 : y + z + z = y + 2 • z := by abel
  have e6 : y + z - z = y := by abel
  have e7 : y - z + z = y := by abel
  have e8 : y - z - z = y - 2 • z := by abel
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  rw [e5, e6] at h3
  rw [e7, e8] at h4
  linarith [h1, h2, h3, h4]

/-- Second-argument additivity of the real polarization, obtained from first-argument additivity
(`starHomScalarMeasure_real_polar_add_left`)
  via the symmetry `starHomScalarMeasure_real_polar_symm`. -/
lemma starHomScalarMeasure_real_polar_add_right (a b c : H) (S : Set (X)) :
    (starHomScalarMeasure Φ (a + (b + c))).real S -
        (starHomScalarMeasure Φ (a - (b + c))).real S =
      ((starHomScalarMeasure Φ (a + b)).real S - (starHomScalarMeasure Φ (a - b)).real S) +
        ((starHomScalarMeasure Φ (a + c)).real S - (starHomScalarMeasure Φ (a - c)).real S) := by
  have hadd := starHomScalarMeasure_real_polar_add_left Φ b c a S
  have e1 : a + (b + c) = b + c + a := by abel
  have e2 : b + c - a = -(a - (b + c)) := by abel
  have e3 : b + a = a + b := by abel
  have e4 : b - a = -(a - b) := by abel
  have e5 : c + a = a + c := by abel
  have e6 : c - a = -(a - c) := by abel
  rw [← e1, e2, e3, e4, e5, e6, starHomScalarMeasure_real_neg, starHomScalarMeasure_real_neg,
    starHomScalarMeasure_real_neg] at hadd
  linarith [hadd]

/-- Additivity of the polarized measure in its second (right) vector argument, for a fixed
measurable set `S`.  This is the sesquilinearity step promised in the module docstring: it
follows from the parallelogram law by pure algebra, with no continuity or Riesz-representation
machinery required.   -/
lemma polarizedStarHomScalarMeasure_add_right (x y₁ y₂ : H) {S : Set (X)}
    (hS : MeasurableSet S) :
    polarizedStarHomScalarMeasure Φ x (y₁ + y₂) S =
      polarizedStarHomScalarMeasure Φ x y₁ S +
        polarizedStarHomScalarMeasure Φ x y₂ S := by
  rw [polarizedStarHomScalarMeasure_apply Φ hS, polarizedStarHomScalarMeasure_apply Φ hS,
    polarizedStarHomScalarMeasure_apply Φ hS]
  have hR := starHomScalarMeasure_real_polar_add_right Φ x y₁ y₂ S
  have hI : (starHomScalarMeasure Φ (x + Complex.I • (y₁ + y₂))).real S -
      (starHomScalarMeasure Φ (x - Complex.I • (y₁ + y₂))).real S =
      ((starHomScalarMeasure Φ (x + Complex.I • y₁)).real S -
          (starHomScalarMeasure Φ (x - Complex.I • y₁)).real S) +
        ((starHomScalarMeasure Φ (x + Complex.I • y₂)).real S -
          (starHomScalarMeasure Φ (x - Complex.I • y₂)).real S) := by
    have h := starHomScalarMeasure_real_polar_add_right Φ x (Complex.I • y₁) (Complex.I • y₂) S
    rwa [← smul_add] at h
  have hRc := congrArg (fun r : ℝ => (r : ℂ)) hR
  have hIc := congrArg (fun r : ℝ => (r : ℂ)) hI
  push_cast at hRc hIc
  rw [hRc, hIc]
  ring

/-- Additivity of the polarized measure in its first (left) vector argument, for a fixed
measurable set `S`. -/
lemma polarizedStarHomScalarMeasure_add_left (x₁ x₂ y : H) {S : Set (X)}
    (hS : MeasurableSet S) :
    polarizedStarHomScalarMeasure Φ (x₁ + x₂) y S =
      polarizedStarHomScalarMeasure Φ x₁ y S +
        polarizedStarHomScalarMeasure Φ x₂ y S := by
  rw [polarizedStarHomScalarMeasure_apply Φ hS, polarizedStarHomScalarMeasure_apply Φ hS,
    polarizedStarHomScalarMeasure_apply Φ hS]
  have hR := starHomScalarMeasure_real_polar_add_left Φ x₁ x₂ y S
  have hI : (starHomScalarMeasure Φ (x₁ + x₂ + Complex.I • y)).real S -
      (starHomScalarMeasure Φ (x₁ + x₂ - Complex.I • y)).real S =
      ((starHomScalarMeasure Φ (x₁ + Complex.I • y)).real S -
          (starHomScalarMeasure Φ (x₁ - Complex.I • y)).real S) +
        ((starHomScalarMeasure Φ (x₂ + Complex.I • y)).real S -
          (starHomScalarMeasure Φ (x₂ - Complex.I • y)).real S) :=
    starHomScalarMeasure_real_polar_add_left Φ x₁ x₂ (Complex.I • y) S
  have hRc := congrArg (fun r : ℝ => (r : ℂ)) hR
  have hIc := congrArg (fun r : ℝ => (r : ℂ)) hI
  push_cast at hRc hIc
  rw [hRc, hIc]
  ring

/-- Multiplying the second vector by `i` multiplies the polarized measure by `-i`. -/
lemma polarizedStarHomScalarMeasure_I_smul_right (x y : H) {S : Set (X)}
    (hS : MeasurableSet S) :
    polarizedStarHomScalarMeasure Φ x (Complex.I • y) S =
      -Complex.I * polarizedStarHomScalarMeasure Φ x y S := by
  rw [polarizedStarHomScalarMeasure_apply Φ hS, polarizedStarHomScalarMeasure_apply Φ hS]
  have e1 : Complex.I • (Complex.I • y) = -y := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [e1]
  have e2 : x + -y = x - y := by abel
  have e3 : x - -y = x + y := by abel
  rw [e2, e3]
  push_cast
  linear_combination ((1 : ℂ) / 4) *
    (((starHomScalarMeasure Φ (x + Complex.I • y)).real S : ℂ) -
      ((starHomScalarMeasure Φ (x - Complex.I • y)).real S : ℂ)) * Complex.I_sq

/-- Multiplying the first vector by `i` multiplies the polarized measure by `i`. -/
lemma polarizedStarHomScalarMeasure_I_smul_left (x y : H) {S : Set (X)}
    (hS : MeasurableSet S) :
    polarizedStarHomScalarMeasure Φ (Complex.I • x) y S =
      Complex.I * polarizedStarHomScalarMeasure Φ x y S := by
  rw [polarizedStarHomScalarMeasure_apply Φ hS, polarizedStarHomScalarMeasure_apply Φ hS]
  have e1 : Complex.I • x + y = Complex.I • (x - Complex.I • y) := by
    rw [smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul]; abel
  have e2 : Complex.I • x - y = Complex.I • (x + Complex.I • y) := by
    rw [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]; abel
  have e3 : Complex.I • x + Complex.I • y = Complex.I • (x + y) := by rw [smul_add]
  have e4 : Complex.I • x - Complex.I • y = Complex.I • (x - y) := by rw [smul_sub]
  rw [e1, e2, e3, e4, starHomScalarMeasure_real_I_smul, starHomScalarMeasure_real_I_smul,
    starHomScalarMeasure_real_I_smul, starHomScalarMeasure_real_I_smul]
  push_cast
  linear_combination ((1 : ℂ) / 4) *
    (((starHomScalarMeasure Φ (x - Complex.I • y)).real S : ℂ) -
      ((starHomScalarMeasure Φ (x + Complex.I • y)).real S : ℂ)) * Complex.I_sq

/-- A crude but sufficient bound on the polarized measure, from the parallelogram law and
`starHomScalarMeasure_real_le_univ`.
   This is enough to see `(x, y) ↦ polarizedStarHomScalarMeasure Φ
x y S` is jointly bounded, the input a Riesz-representation argument needs. -/
lemma polarizedStarHomScalarMeasure_norm_le (x y : H) {S : Set (X)}
    (hS : MeasurableSet S) :
    ‖polarizedStarHomScalarMeasure Φ x y S‖ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [polarizedStarHomScalarMeasure_apply Φ hS]
  have hbound : ∀ a b : H, |(starHomScalarMeasure Φ (a + b)).real S -
      (starHomScalarMeasure Φ (a - b)).real S| ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    intro a b
    have hpar := starHomScalarMeasure_real_parallelogram Φ a b S
    have hnn1 := starHomScalarMeasure_real_nonneg Φ (a + b) S
    have hnn2 := starHomScalarMeasure_real_nonneg Φ (a - b) S
    have hle1 := starHomScalarMeasure_real_le_univ Φ a S
    have hle2 := starHomScalarMeasure_real_le_univ Φ b S
    rw [abs_le]
    constructor <;> linarith
  have h1 := hbound x y
  have h2 := hbound x (Complex.I • y)
  rw [norm_smul] at h2
  simp only [Complex.norm_I, one_mul] at h2
  calc ‖((1 / 4 : ℝ) * ((starHomScalarMeasure Φ (x + y)).real S -
        (starHomScalarMeasure Φ (x - y)).real S) : ℂ) +
      Complex.I * ((1 / 4 : ℝ) * ((starHomScalarMeasure Φ (x + Complex.I • y)).real S -
        (starHomScalarMeasure Φ (x - Complex.I • y)).real S) : ℂ)‖
      ≤ ‖((1 / 4 : ℝ) * ((starHomScalarMeasure Φ (x + y)).real S -
          (starHomScalarMeasure Φ (x - y)).real S) : ℂ)‖ +
        ‖Complex.I * ((1 / 4 : ℝ) * ((starHomScalarMeasure Φ (x + Complex.I • y)).real S -
          (starHomScalarMeasure Φ (x - Complex.I • y)).real S) : ℂ)‖ := norm_add_le _ _
    _ = (1 / 4) * |(starHomScalarMeasure Φ (x + y)).real S -
          (starHomScalarMeasure Φ (x - y)).real S| +
        (1 / 4) * |(starHomScalarMeasure Φ (x + Complex.I • y)).real S -
          (starHomScalarMeasure Φ (x - Complex.I • y)).real S| := by
      simp [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / 4) * (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) + (1 / 4) * (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) := by
      gcongr
    _ = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by ring

/-- The polarized measure is real homogeneous in the second vector. -/
lemma polarizedStarHomScalarMeasure_real_smul_right (x y : H) (r : ℝ) {S : Set (X)}
    (hS : MeasurableSet S) :
    polarizedStarHomScalarMeasure Φ x (r • y) S =
      (r : ℂ) * polarizedStarHomScalarMeasure Φ x y S := by
  have hadd : ∀ a b : ℝ, polarizedStarHomScalarMeasure Φ x ((a + b) • y) S =
      polarizedStarHomScalarMeasure Φ x (a • y) S +
        polarizedStarHomScalarMeasure Φ x (b • y) S := by
    intro a b
    rw [add_smul]
    exact polarizedStarHomScalarMeasure_add_right Φ x (a • y) (b • y) hS
  have hbound : ∀ t : ℝ, |t| ≤ 1 →
      ‖polarizedStarHomScalarMeasure Φ x (t • y) S‖ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    intro t h
    have h := polarizedStarHomScalarMeasure_norm_le Φ x (t • y) hS
    have h2 : ‖t • y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      have hty : |t| * ‖y‖ ≤ ‖y‖ := by nlinarith [norm_nonneg y]
      gcongr
    linarith
  have h := real_linear_of_additive_bounded hadd hbound r
  rwa [one_smul] at h

/-- Real-scalar homogeneity in the left (first) argument, the counterpart of
`polarizedStarHomScalarMeasure_real_smul_right` needed for conjugate-linearity in `x` (real scalars
are self-conjugate, so the same statement serves both roles). -/
lemma polarizedStarHomScalarMeasure_real_smul_left (x y : H) (r : ℝ) {S : Set (X)}
    (hS : MeasurableSet S) :
    polarizedStarHomScalarMeasure Φ (r • x) y S =
      (r : ℂ) * polarizedStarHomScalarMeasure Φ x y S := by
  have hadd : ∀ a b : ℝ, polarizedStarHomScalarMeasure Φ ((a + b) • x) y S =
      polarizedStarHomScalarMeasure Φ (a • x) y S +
        polarizedStarHomScalarMeasure Φ (b • x) y S := by
    intro a b
    rw [add_smul]
    exact polarizedStarHomScalarMeasure_add_left Φ (a • x) (b • x) y hS
  have hbound : ∀ t : ℝ, |t| ≤ 1 →
      ‖polarizedStarHomScalarMeasure Φ (t • x) y S‖ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    intro t h
    have h := polarizedStarHomScalarMeasure_norm_le Φ (t • x) y hS
    have h2 : ‖t • x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      have htx : |t| * ‖x‖ ≤ ‖x‖ := by nlinarith [norm_nonneg x]
      gcongr
    linarith
  have h := real_linear_of_additive_bounded hadd hbound r
  rwa [one_smul] at h

/-! ## C. Polarization -/

/-- Full `ℂ`-linearity of the polarized measure in its first (left) argument. -/
lemma polarizedStarHomScalarMeasure_smul_left (c : ℂ) (x y : H) {S : Set (X)}
    (hS : MeasurableSet S) :
    polarizedStarHomScalarMeasure Φ (c • x) y S =
      c * polarizedStarHomScalarMeasure Φ x y S := by
  have hc : (c.re : ℝ) • x + (c.im : ℝ) • (Complex.I • x) = c • x := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ),
      smul_smul, ← add_smul]
    congr 1
    exact_mod_cast Complex.re_add_im c
  rw [← hc, polarizedStarHomScalarMeasure_add_left Φ _ _ y hS,
    polarizedStarHomScalarMeasure_real_smul_left Φ x y c.re hS,
    polarizedStarHomScalarMeasure_real_smul_left Φ (Complex.I • x) y c.im hS,
    polarizedStarHomScalarMeasure_I_smul_left Φ x y hS]
  have hcre : (c.re : ℂ) + (c.im : ℂ) * Complex.I = c := Complex.re_add_im c
  linear_combination (polarizedStarHomScalarMeasure Φ x y S) * hcre

/-- Full conjugate-`ℂ`-linearity of the polarized measure in its second (right) argument. -/
lemma polarizedStarHomScalarMeasure_smul_right (c : ℂ) (x y : H) {S : Set (X)}
    (hS : MeasurableSet S) :
    polarizedStarHomScalarMeasure Φ x (c • y) S =
      (starRingEnd ℂ c) * polarizedStarHomScalarMeasure Φ x y S := by
  have hc : (c.re : ℝ) • y + (c.im : ℝ) • (Complex.I • y) = c • y := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ),
      smul_smul, ← add_smul]
    congr 1
    exact_mod_cast Complex.re_add_im c
  rw [← hc, polarizedStarHomScalarMeasure_add_right Φ x _ _ hS,
    polarizedStarHomScalarMeasure_real_smul_right Φ x y c.re hS,
    polarizedStarHomScalarMeasure_real_smul_right Φ x (Complex.I • y) c.im hS,
    polarizedStarHomScalarMeasure_I_smul_right Φ x y hS]
  have hcc : (c.re : ℂ) - (c.im : ℂ) * Complex.I = starRingEnd ℂ c := by
    have h := Complex.re_add_im (starRingEnd ℂ c)
    rw [Complex.conj_re, Complex.conj_im] at h
    push_cast at h
    linear_combination h
  linear_combination (polarizedStarHomScalarMeasure Φ x y S) * hcc

lemma polarizedStarHomScalarMeasure_zero_left (y : H) {S : Set (X)}
    (hS : MeasurableSet S) : polarizedStarHomScalarMeasure Φ 0 y S = 0 := by
  have h := polarizedStarHomScalarMeasure_smul_left Φ 0 0 y hS
  simpa using h

lemma polarizedStarHomScalarMeasure_zero_right (x : H) {S : Set (X)}
    (hS : MeasurableSet S) : polarizedStarHomScalarMeasure Φ x 0 S = 0 := by
  have h := polarizedStarHomScalarMeasure_smul_right Φ 0 x 0 hS
  simpa using h

/-- The polarized measure is bounded by `‖x‖ ‖y‖`. -/
lemma polarizedStarHomScalarMeasure_norm_le_mul (x y : H) {S : Set (X)}
    (hS : MeasurableSet S) :
    ‖polarizedStarHomScalarMeasure Φ x y S‖ ≤ 2 * ‖x‖ * ‖y‖ := by
  rcases eq_or_ne x 0 with hx0 | hx0
  · simp [hx0, polarizedStarHomScalarMeasure_zero_left Φ y hS]
  rcases eq_or_ne y 0 with hy0 | hy0
  · simp [hy0, polarizedStarHomScalarMeasure_zero_right Φ x hS]
  set t : ℝ := Real.sqrt (‖y‖ / ‖x‖) with ht_def
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hypos hxpos)
  have htsq : t ^ 2 = ‖y‖ / ‖x‖ := Real.sq_sqrt (div_pos hypos hxpos).le
  have hkey : polarizedStarHomScalarMeasure Φ x y S =
      polarizedStarHomScalarMeasure Φ (t • x) (t⁻¹ • y) S := by
    rw [polarizedStarHomScalarMeasure_real_smul_left Φ x (t⁻¹ • y) t hS,
      polarizedStarHomScalarMeasure_real_smul_right Φ x y t⁻¹ hS]
    have ht1 : (t : ℂ) * ((t⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne', Complex.ofReal_one]
    rw [← mul_assoc, ht1, one_mul]
  rw [hkey]
  have hbound := polarizedStarHomScalarMeasure_norm_le Φ (t • x) (t⁻¹ • y) hS
  have h1 : ‖t • x‖ ^ 2 = t ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]; ring
  have h2 : ‖t⁻¹ • y‖ ^ 2 = t⁻¹ ^ 2 * ‖y‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]; ring
  rw [h1, h2, htsq] at hbound
  have h3 : t⁻¹ ^ 2 = ‖x‖ / ‖y‖ := by
    rw [inv_pow, htsq, inv_div]
  rw [h3] at hbound
  have e1 : ‖y‖ / ‖x‖ * ‖x‖ ^ 2 = ‖x‖ * ‖y‖ := by field_simp
  have e2 : ‖x‖ / ‖y‖ * ‖y‖ ^ 2 = ‖x‖ * ‖y‖ := by field_simp
  rw [e1, e2] at hbound
  linarith [hbound]

/-! ## D. Riesz representation of the polarized measure -/

/-- The algebraic (not-yet-continuous) sesquilinear form representing `S`, conjugate-linear in the
first argument and linear in the second — the convention Mathlib's
`InnerProductSpace.continuousLinearMapOfBilin` expects. -/
noncomputable def starHomSesquilinearFormAux (S : Set (X)) (hS : MeasurableSet S) :
    H →ₛₗ[starRingEnd ℂ] H →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun x y => starRingEnd ℂ (polarizedStarHomScalarMeasure Φ x y S))
    (fun x₁ x₂ y => by
      rw [polarizedStarHomScalarMeasure_add_left Φ x₁ x₂ y hS, map_add])
    (fun c x y => by
      simp only [smul_eq_mul]
      rw [polarizedStarHomScalarMeasure_smul_left Φ c x y hS, map_mul])
    (fun x y₁ y₂ => by
      rw [polarizedStarHomScalarMeasure_add_right Φ x y₁ y₂ hS, map_add])
    (fun c x y => by
      simp only [RingHom.id_apply, smul_eq_mul]
      rw [polarizedStarHomScalarMeasure_smul_right Φ c x y hS, map_mul, Complex.conj_conj])

lemma starHomSesquilinearFormAux_apply (S : Set (X)) (hS : MeasurableSet S) (x y : H) :
    starHomSesquilinearFormAux Φ S hS x y =
      starRingEnd ℂ (polarizedStarHomScalarMeasure Φ x y S) := rfl

/-- The continuous sesquilinear form, in the shape `InnerProductSpace.continuousLinearMapOfBilin`
consumes. -/
noncomputable def starHomSesquilinearForm (S : Set (X)) (hS : MeasurableSet S) :
    H →L⋆[ℂ] H →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂ (starHomSesquilinearFormAux Φ S hS) 2 (fun x y => by
    rw [starHomSesquilinearFormAux_apply, RCLike.norm_conj]
    exact polarizedStarHomScalarMeasure_norm_le_mul Φ x y hS)

@[simp]
lemma starHomSesquilinearForm_apply (S : Set (X)) (hS : MeasurableSet S) (x y : H) :
    starHomSesquilinearForm Φ S hS x y =
      starRingEnd ℂ (polarizedStarHomScalarMeasure Φ x y S) := rfl

end StarHomScalar

end QuantumMechanics

end ProbabilisticTheory

end
