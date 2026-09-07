/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Basic
public import Physlib.Particles.StandardModel.GaugeAlgebra.JetGaugeAlgebra
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
public import Physlib.Relativity.SL2C.Basic
public import Physlib.Mathematics.ConjModule
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Physlib.Particles.LagrangianTheory.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Physlib.Mathematics.MvPolynomialTranslation
public import Mathlib.Algebra.MvPolynomial.Derivation
/-!
# The Maurer–Cartan forms of the jet gauge group

The Maurer-Cartan form is a map
`ω : JetGaugeGroupI → (Fin 1 ⊕ Fin 3) → JetGaugeAlgebra`
defined as `ω_μ(U) := i (∂_μ U) U†`.

We will use `ω^a_ν` to denote the `a`-th component of the Maurer–Cartan form in the
basis of the jet Lie algebra, and `f^a_{b c}` to denote the structure constants of the
jet Lie algebra in that basis.

It satisfies the following properties:
- *Cocycle law*: `ω_μ(UV) = ω_μ(U) + U ω_μ(V) U†`
- *Value on the identity*: `ω_μ(1) = 0`
- *Value on constant gauge transformations*: `ω_μ(U₀) = 0`
- *Value on the inverse*: `ω_μ(U⁻¹) = -U⁻¹ ω_μ(U) U`
- *Structural equation*: `∂_μ ω^a_ν(U) − ∂_ν ω^a_μ(U) = ∑_{b c} f^a_{b c} · ω^b_μ(U) · ω^c_ν(U)`

-/

@[expose] public section
namespace StandardModel
open MvPowerSeries JetGaugeAlgebra

/-!

## The Maurer–Cartan form of the jet gauge group

-/

/-- The Maurer–Cartan form `ω_μ(U) := i (∂_μ U) U⁻¹` of the jet gauge group, valued
  in the jet gauge algebra. -/
noncomputable def maurerCartanForm (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) : JetGaugeAlgebra :=
  JetGaugeAlgebra.ofMatrixProd (Complex.I • (JetGaugeGroupI.deriv μ U * (U⁻¹).toVal))
    ⟨JetGaugeGroupI.star_deriv_mul_inv_toVal_SU3 μ U,
      JetGaugeGroupI.deriv_mul_inv_toVal_SU3_traceless μ U⟩
    ⟨JetGaugeGroupI.star_deriv_mul_inv_toVal_SU2 μ U,
      JetGaugeGroupI.deriv_mul_inv_toVal_SU2_traceless μ U⟩
    (JetGaugeGroupI.star_deriv_mul_inv_toVal_U1 μ U)

@[simp]
lemma maurerCartanForm_toSU3Matrix (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    (maurerCartanForm U μ).toSU3Matrix =
      Complex.I • (U.1.1.map (pderiv ℂ μ) * star U.1.1) := rfl

@[simp]
lemma maurerCartanForm_toSU2Matrix (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    (maurerCartanForm U μ).toSU2Matrix =
      Complex.I • (U.2.1.1.map (pderiv ℂ μ) * star U.2.1.1) := rfl

@[simp]
lemma maurerCartanForm_toU1Value (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    (maurerCartanForm U μ).toU1Value =
      Complex.I • (pderiv ℂ μ U.2.2.1 * star U.2.2.1) := rfl

@[simp]
lemma maurerCartanForm_one : maurerCartanForm (1 : JetGaugeGroupI) = 0 := by
  ext <;> simp [maurerCartanForm,JetGaugeGroupI.deriv_one]

lemma maurerCartanForm_ofConstant (U₀ : GaugeGroupI) :
    maurerCartanForm (JetGaugeGroupI.ofConstant U₀) = 0 := by
  ext <;> simp [maurerCartanForm,JetGaugeGroupI.deriv_ofConstant]

lemma maurerCartanForm_cocycle (U V : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    maurerCartanForm (U * V) μ = maurerCartanForm U μ + adjoint U (maurerCartanForm V μ) := by
  have h1 : V.toVal * (V⁻¹).toVal = 1 := by
    rw [show V.toVal * (V⁻¹).toVal = (V * V⁻¹).toVal from rfl, mul_inv_cancel]; rfl
  have key : Complex.I • (JetGaugeGroupI.deriv μ (U * V) * ((U * V)⁻¹).toVal) =
      Complex.I • (JetGaugeGroupI.deriv μ U * (U⁻¹).toVal) +
        U.toVal * (Complex.I • (JetGaugeGroupI.deriv μ V * (V⁻¹).toVal)) * (U⁻¹).toVal := by
    rw [show ((U * V)⁻¹).toVal = (V⁻¹).toVal * (U⁻¹).toVal from by rw [mul_inv_rev]; rfl,
      JetGaugeGroupI.deriv_mul, add_mul, smul_add, mul_smul_comm, smul_mul_assoc]
    congr 1
    · rw [mul_assoc (JetGaugeGroupI.deriv μ U), ← mul_assoc V.toVal, h1, one_mul]
    · simp [mul_assoc]
  refine ext_of_matrix (congrArg (fun p => p.1) key) (congrArg (fun p => p.2.1) key) ?_
  have h22 : (maurerCartanForm (U * V) μ).toU1Value =
      (maurerCartanForm U μ).toU1Value +
        U.2.2.1 * (maurerCartanForm V μ).toU1Value * star U.2.2.1 :=
    congrArg (fun p => p.2.2) key
  rw [h22, mul_comm (U.2.2.1 : JetRing) ((maurerCartanForm V μ).toU1Value), mul_assoc,
    (Unitary.mem_iff.mp U.2.2.2).2, mul_one]
  rfl

lemma maurerCartanForm_inv (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    maurerCartanForm (U⁻¹) μ = - adjoint U⁻¹ (maurerCartanForm U μ) := by
  linear_combination (norm := simp) -(maurerCartanForm_cocycle  U⁻¹ U μ)

lemma deriv_zero_of_maurerCartanForm_zero (U : JetGaugeGroupI) (h : maurerCartanForm U = 0) :
    ∀ μ, U.deriv μ = 0 := by
  intro μ
  have h1 : maurerCartanForm U μ = 0 := congrFun h μ
  -- extract the underlying value triple of the vanishing algebra element
  have h2 : Complex.I • (JetGaugeGroupI.deriv μ U * (U⁻¹).toVal) = 0 :=
    Prod.ext (congrArg (fun a => a.1.1) h1)
      (Prod.ext (congrArg (fun a => a.2.1.1) h1) (congrArg (fun a => a.2.2.1) h1))
  -- cancel the scalar `i`
  have hml : (-Complex.I) * Complex.I = 1 := by simp [neg_mul, Complex.I_mul_I]
  have h3 : JetGaugeGroupI.deriv μ U * (U⁻¹).toVal = 0 := by
    have h4 := congrArg (fun X => (-Complex.I) • X) h2
    simpa [smul_smul, hml] using h4
  -- cancel `U⁻¹` on the right
  have h5 : (U⁻¹).toVal * U.toVal = 1 := by
    rw [show (U⁻¹).toVal * U.toVal = (U⁻¹ * U).toVal from rfl, inv_mul_cancel]
    rfl
  calc JetGaugeGroupI.deriv μ U
      = JetGaugeGroupI.deriv μ U * ((U⁻¹).toVal * U.toVal) := by rw [h5, mul_one]
    _ = JetGaugeGroupI.deriv μ U * (U⁻¹).toVal * U.toVal := by rw [mul_assoc]
    _ = 0 := by rw [h3, zero_mul]

lemma maurerCartanForm_eq_zero_iff_ofConstant (U : JetGaugeGroupI) :
    maurerCartanForm U = 0 ↔ ∃ c, U = JetGaugeGroupI.ofConstant c := by
  constructor
  · intro h
    -- Step 1: all first derivatives of `U` vanish.
    have hderiv := deriv_zero_of_maurerCartanForm_zero U h
    -- Step 2: a jet with vanishing first derivatives is the constant jet of its value.
    have hconst : ∀ f : JetRing, (∀ μ, pderiv ℂ μ f = 0) → f = C (constantCoeff f) := by
      intro f hf
      refine pderiv.ext (fun i => ?_) ?_
      · rw [hf i, pderiv_C]
      · rw [constantCoeff_C]
    refine ⟨U.eval, Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))⟩
    · show U.1.1 = ((JetGaugeGroupI.ofConstant U.eval).1 : Matrix (Fin 3) (Fin 3) JetRing)
      ext i j : 1
      exact hconst (U.1.1 i j) fun μ => by
        simpa [JetGaugeGroupI.deriv, Matrix.map_apply] using
          congrArg (fun p => (p.1 : Matrix (Fin 3) (Fin 3) JetRing) i j) (hderiv μ)
    · show U.2.1.1 = ((JetGaugeGroupI.ofConstant U.eval).2.1 : Matrix (Fin 2) (Fin 2) JetRing)
      ext i j : 1
      exact hconst (U.2.1.1 i j) fun μ => by
        simpa [JetGaugeGroupI.deriv, Matrix.map_apply] using
          congrArg (fun p => (p.2.1 : Matrix (Fin 2) (Fin 2) JetRing) i j) (hderiv μ)
    · show U.2.2.1 = ((JetGaugeGroupI.ofConstant U.eval).2.2 : JetRing)
      exact hconst U.2.2.1 fun μ => congrArg (fun p => (p.2.2 : JetRing)) (hderiv μ)
  · rintro ⟨c, rfl⟩
    exact maurerCartanForm_ofConstant c

/-!

## The structural equation

-/

/-- The structural (Maurer–Cartan) equation, basis-independently: the Maurer–Cartan
  form is flat,

  `∂_μ ω_ν − ∂_ν ω_μ + ⁅ω_μ, ω_ν⁆ = 0`.

  In components with respect to a basis of the jet gauge algebra this is
  `∂_μ ω^a_ν − ∂_ν ω^a_μ = ∑_{b c} f^a_{b c} · ω^b_μ · ω^c_ν`. On each matrix
  factor the second-derivative terms cancel by symmetry of mixed partials, the
  derivative of `A†` is rewritten through the differentiated unitarity relation,
  and the surviving first-order terms form the commutator; on the abelian `U(1)`
  factor the commutator is absent and only the symmetry of mixed partials
  remains. -/
lemma maurerCartanForm_structure (U : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3) :
    deriv μ (maurerCartanForm U ν) - deriv ν (maurerCartanForm U μ) +
      ⁅maurerCartanForm U μ, maurerCartanForm U ν⁆ = 0 := by
  -- pulling the scalar `i` out of the entrywise formal derivative
  have hmap : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : Fin 1 ⊕ Fin 3) (c : ℂ)
      (M : Matrix κ κ JetRing), (c • M).map (pderiv ℂ ρ) = c • M.map (pderiv ℂ ρ) :=
    fun _ _ _ _ _ _ => Matrix.ext fun _ _ => Derivation.map_smul _ _ _
  -- the matrix-level structural identity, generic in the size of the factor
  have key : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix κ κ JetRing),
      A * star A = 1 →
      (A.map (pderiv ℂ ν) * star A).map (pderiv ℂ μ) -
        (A.map (pderiv ℂ μ) * star A).map (pderiv ℂ ν) =
      A.map (pderiv ℂ μ) * star A * (A.map (pderiv ℂ ν) * star A) -
        A.map (pderiv ℂ ν) * star A * (A.map (pderiv ℂ μ) * star A) := by
    intro κ _ _ A hU
    have hleib : ∀ (ρ : Fin 1 ⊕ Fin 3) (M N : Matrix κ κ JetRing),
        (M * N).map (pderiv ℂ ρ) = M.map (pderiv ℂ ρ) * N + M * N.map (pderiv ℂ ρ) := by
      intro ρ M N
      ext i j : 1
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
        Derivation.leibniz, smul_eq_mul]
      exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
    -- the derivative of `A†` through differentiated unitarity
    have hq : ∀ ρ : Fin 1 ⊕ Fin 3,
        (star A).map (pderiv ℂ ρ) = -(star A * A.map (pderiv ℂ ρ) * star A) := by
      intro ρ
      have h1 : A * (star A).map (pderiv ℂ ρ) = -(A.map (pderiv ℂ ρ) * star A) :=
        eq_neg_of_add_eq_zero_right (by
          rw [← hleib ρ A (star A), hU]
          exact Matrix.ext fun i j => by
            simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ℂ ρ)])
      calc (star A).map (pderiv ℂ ρ)
          = star A * A * (star A).map (pderiv ℂ ρ) := by
            rw [mul_eq_one_comm.mp hU, one_mul]
        _ = -(star A * A.map (pderiv ℂ ρ) * star A) := by
            rw [mul_assoc, h1, mul_neg, ← mul_assoc]
    rw [hleib μ (A.map (pderiv ℂ ν)) (star A), hleib ν (A.map (pderiv ℂ μ)) (star A),
      show (A.map (pderiv ℂ ν)).map (pderiv ℂ μ) = (A.map (pderiv ℂ μ)).map (pderiv ℂ ν)
        from Matrix.ext fun _ _ => JetRing.pderiv_comm μ ν _, hq μ, hq ν]
    simp only [mul_neg, ← mul_assoc]
    abel
  -- the abelian `U(1)` identity: no commutator, pure symmetry of mixed partials
  have keyU1 : pderiv ℂ μ (pderiv ℂ ν U.2.2.1 * star U.2.2.1) =
      pderiv ℂ ν (pderiv ℂ μ U.2.2.1 * star U.2.2.1) := by
    have hu : U.2.2.1 * star U.2.2.1 = 1 := (Unitary.mem_iff.mp U.2.2.2).2
    have hstar : ∀ ρ : Fin 1 ⊕ Fin 3, pderiv ℂ ρ (star U.2.2.1) =
        -(star U.2.2.1 * pderiv ℂ ρ U.2.2.1 * star U.2.2.1) := by
      intro ρ
      have h0 : pderiv ℂ ρ (U.2.2.1 * star U.2.2.1) = 0 := by rw [hu, pderiv_one]
      rw [Derivation.leibniz] at h0
      simp only [smul_eq_mul] at h0
      linear_combination star U.2.2.1 * h0 -
        pderiv ℂ ρ (star U.2.2.1) * ((mul_comm _ _).trans hu)
    simp only [Derivation.leibniz, smul_eq_mul]
    rw [hstar μ, hstar ν, JetRing.pderiv_comm μ ν]
    ring
  refine ext_of_matrix ?_ ?_ ?_ <;>
    simp only [add_toSU3Matrix, add_toSU2Matrix, add_toU1Value, sub_toSU3Matrix,
      sub_toSU2Matrix, sub_toU1Value, deriv_toSU3Matrix, deriv_toSU2Matrix,
      deriv_toU1Value, bracket_toSU3Matrix, bracket_toSU2Matrix, bracket_toU1Value,
      maurerCartanForm_toSU3Matrix, maurerCartanForm_toSU2Matrix,
      maurerCartanForm_toU1Value, zero_toSU3Matrix, zero_toSU2Matrix, zero_toU1Value,
      hmap, smul_mul_smul_comm, Complex.I_mul_I, neg_one_smul, Derivation.map_smul,
      add_zero]
  · rw [← smul_sub, ← smul_add, key _ U.1.1
      (Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.1.2).1)]
    exact smul_eq_zero_of_right _ (by abel)
  · rw [← smul_sub, ← smul_add, key _ U.2.1.1
      (Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.2.1.2).1)]
    exact smul_eq_zero_of_right _ (by abel)
  · rw [keyU1, sub_self]

/-!

## Integrating the structural equation

-/

/-- The integration step of the converse to the structural equation: a flat jet
  1-form `ω` is the logarithmic derivative of a jet of gauge transformations based
  at the identity, `∂_μ U = −i ω_μ · U` with `U(0) = 1`. Combined with unitarity
  this says `ω_μ = i (∂_μ U) U⁻¹`, i.e. `ω` is the Maurer–Cartan form of a pure
  jet; existence there is `exists_maurerCartanForm_eq_of_structure`. -/
lemma exists_deriv_eq_of_maurerCartanForm_structure
    (ω : (Fin 1 ⊕ Fin 3) → JetGaugeAlgebra)
    (hω : ∀ μ ν, deriv μ (ω ν) - deriv ν (ω μ) + ⁅ω μ, ω ν⁆ = 0) :
    ∃ U : JetGaugeGroupI, U.eval = 1 ∧ ∀ μ,
      JetGaugeGroupI.deriv μ U = (-Complex.I) • (ω μ).toVal * U.toVal := by
  -- entrywise toolkit: `pderiv` through scalars, products, stars; constancy of jets
  have hmap : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : Fin 1 ⊕ Fin 3) (c : ℂ)
      (M : Matrix κ κ JetRing), (c • M).map (pderiv ℂ ρ) = c • M.map (pderiv ℂ ρ) :=
    fun _ _ _ _ _ _ => Matrix.ext fun _ _ => Derivation.map_smul _ _ _
  have hleib : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : Fin 1 ⊕ Fin 3)
      (M N : Matrix κ κ JetRing),
      (M * N).map (pderiv ℂ ρ) = M.map (pderiv ℂ ρ) * N + M * N.map (pderiv ℂ ρ) := by
    intro κ _ _ ρ M N
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
      Derivation.leibniz, smul_eq_mul]
    exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
  have hstarmap : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : Fin 1 ⊕ Fin 3)
      (M : Matrix κ κ JetRing), (star M).map (pderiv ℂ ρ) = star (M.map (pderiv ℂ ρ)) :=
    fun _ _ _ ρ M => Matrix.ext fun i j => JetRing.pderiv_star ρ (M j i)
  have hconst : ∀ f : JetRing, (∀ μ, pderiv ℂ μ f = 0) → f = C (constantCoeff f) :=
    fun f hf => pderiv.ext (fun i => by rw [hf i, pderiv_C]) (by rw [constantCoeff_C])
  have hconstM : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (M : Matrix κ κ JetRing),
      (constantCoeff : JetRing →+* ℂ).mapMatrix M = 1 →
      (∀ μ, M.map (pderiv ℂ μ) = 0) → M = 1 := by
    intro κ _ _ M h1 hM
    ext i j
    rw [hconst (M i j) fun μ => congrArg (fun N => N i j) (hM μ),
      show constantCoeff (M i j) = (1 : Matrix κ κ ℂ) i j from congrArg (fun N => N i j) h1]
    simp [Matrix.one_apply, apply_ite (fun c : ℂ => (C c : JetRing))]
  -- generic integration: flat hermitian data has a unitary Wilson line based at `1`
  have hmain : ∀ (κ : Type) [Fintype κ] [DecidableEq κ]
      (X : (Fin 1 ⊕ Fin 3) → Matrix κ κ JetRing), (∀ μ, star (X μ) = X μ) →
      (∀ μ ν, (X ν).map (pderiv ℂ μ) - (X μ).map (pderiv ℂ ν) +
        Complex.I • (X μ * X ν - X ν * X μ) = 0) →
      ∃ F : Matrix κ κ JetRing, (constantCoeff : JetRing →+* ℂ).mapMatrix F = 1 ∧
        F * star F = 1 ∧ ∀ μ, F.map (pderiv ℂ μ) = (-Complex.I) • X μ * F := by
    intro κ _ _ X hXstar hXflat
    obtain ⟨F, hF0, hF⟩ := JetRing.exists_parallelTransport (fun μ => (-Complex.I) • X μ)
      (fun μ ν => by
        simp only [hmap, smul_mul_smul_comm]
        linear_combination (norm := module) (-Complex.I) • hXflat μ ν)
    replace hF : ∀ μ, F.map (pderiv ℂ μ) = (-Complex.I) • X μ * F := hF
    have hA : ∀ μ, star ((-Complex.I) • X μ) = -((-Complex.I) • X μ) := fun μ => by
      rw [star_smul, hXstar μ]
      simp
    refine ⟨F, hF0, mul_eq_one_comm.mp (hconstM _ _ ?_ fun μ => ?_), hF⟩
    · rw [map_mul, JetRing.mapMatrix_constantCoeff_star, hF0, star_one, one_mul]
    · rw [hleib, hstarmap, hF, star_mul, hA, mul_neg, neg_mul, mul_assoc, neg_add_cancel]
  -- the determinant of a Wilson line of traceless data is constant, hence `1`
  have hdet : ∀ (κ : Type) [Fintype κ] [DecidableEq κ]
      (X : (Fin 1 ⊕ Fin 3) → Matrix κ κ JetRing) (F : Matrix κ κ JetRing),
      (∀ (M : Matrix κ κ JetRing) (μ : Fin 1 ⊕ Fin 3),
        pderiv ℂ μ M.det = (M.map (pderiv ℂ μ) * M.adjugate).trace) →
      (∀ μ, (X μ).trace = 0) → (constantCoeff : JetRing →+* ℂ).mapMatrix F = 1 →
      (∀ μ, F.map (pderiv ℂ μ) = (-Complex.I) • X μ * F) → F.det = 1 := by
    intro κ _ _ X F hjac htr h0 hF
    rw [hconst F.det fun μ => by
        rw [hjac F μ, hF μ, Matrix.mul_assoc, Matrix.mul_adjugate, mul_smul_comm, mul_one,
          Matrix.trace_smul, Matrix.trace_smul, htr μ, smul_zero, smul_zero],
      RingHom.map_det, h0, Matrix.det_one, map_one]
  -- Jacobi's formula on each matrix factor
  have hjac3 : ∀ (M : Matrix (Fin 3) (Fin 3) JetRing) (μ : Fin 1 ⊕ Fin 3),
      pderiv ℂ μ M.det = (M.map (pderiv ℂ μ) * M.adjugate).trace := by
    intro M μ
    rw [Matrix.det_fin_three]
    simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.map_apply, Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const, Matrix.empty_val', Matrix.cons_val_fin_one,
      map_sub, map_add, Derivation.leibniz, smul_eq_mul]
    ring
  have hjac2 : ∀ (M : Matrix (Fin 2) (Fin 2) JetRing) (μ : Fin 1 ⊕ Fin 3),
      pderiv ℂ μ M.det = (M.map (pderiv ℂ μ) * M.adjugate).trace := by
    intro M μ
    rw [Matrix.det_fin_two]
    simp only [Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.mul_apply,
      Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.sum_univ_two, Matrix.cons_val_one,
      map_sub, Derivation.leibniz, smul_eq_mul]
    ring
  -- integrate each factor
  obtain ⟨F₃, hF₃0, hF₃u, hF₃⟩ := hmain (Fin 3) (fun μ => (ω μ).toSU3Matrix)
    (fun μ => show star (ω μ).toSU3Matrix = (ω μ).toSU3Matrix from (ω μ).1.2.1)
    (fun μ ν => by
      simpa only [sub_toSU3Matrix, add_toSU3Matrix, deriv_toSU3Matrix, bracket_toSU3Matrix,
        zero_toSU3Matrix] using congrArg toSU3Matrix (hω μ ν))
  obtain ⟨F₂, hF₂0, hF₂u, hF₂⟩ := hmain (Fin 2) (fun μ => (ω μ).toSU2Matrix)
    (fun μ => show star (ω μ).toSU2Matrix = (ω μ).toSU2Matrix from (ω μ).2.1.2.1)
    (fun μ ν => by
      simpa only [sub_toSU2Matrix, add_toSU2Matrix, deriv_toSU2Matrix, bracket_toSU2Matrix,
        zero_toSU2Matrix] using congrArg toSU2Matrix (hω μ ν))
  obtain ⟨F₁, hF₁0, hF₁u, hF₁⟩ := hmain (Fin 1)
    (fun μ => Matrix.of fun _ _ => (ω μ).toU1Value)
    (fun μ => Matrix.ext fun _ _ => (ω μ).2.2.2)
    (fun μ ν => by
      have h := congrArg toU1Value (hω μ ν)
      simp only [sub_toU1Value, add_toU1Value, deriv_toU1Value, bracket_toU1Value,
        zero_toU1Value, add_zero] at h
      ext i j
      simp [Matrix.mul_apply, mul_comm, h])
  have hd₃ : F₃.det = 1 := hdet (Fin 3) (fun μ => (ω μ).toSU3Matrix) F₃ hjac3
    (fun μ => show ((ω μ).toSU3Matrix).trace = 0 from (ω μ).1.2.2) hF₃0 hF₃
  have hd₂ : F₂.det = 1 := hdet (Fin 2) (fun μ => (ω μ).toSU2Matrix) F₂ hjac2
    (fun μ => show ((ω μ).toSU2Matrix).trace = 0 from (ω μ).2.1.2.2) hF₂0 hF₂
  -- extract the `U(1)` scalar
  have hu1 : F₁ 0 0 * star (F₁ 0 0) = 1 := by
    simpa [Matrix.mul_apply] using congrArg (fun M => M (0 : Fin 1) (0 : Fin 1)) hF₁u
  have hu0 : constantCoeff (F₁ 0 0) = 1 := by
    simpa using congrArg (fun M => M (0 : Fin 1) (0 : Fin 1)) hF₁0
  -- assemble the jet gauge transformation
  refine ⟨⟨⟨F₃, Matrix.mem_specialUnitaryGroup_iff.mpr
        ⟨Matrix.mem_unitaryGroup_iff.mpr hF₃u, hd₃⟩⟩,
      ⟨F₂, Matrix.mem_specialUnitaryGroup_iff.mpr
        ⟨Matrix.mem_unitaryGroup_iff.mpr hF₂u, hd₂⟩⟩,
      ⟨F₁ 0 0, Unitary.mem_iff.mpr ⟨by rw [mul_comm]; exact hu1, hu1⟩⟩⟩,
    Prod.ext (Subtype.ext hF₃0) (Prod.ext (Subtype.ext hF₂0) (Subtype.ext hu0)),
    fun μ => Prod.ext (hF₃ μ) (Prod.ext (hF₂ μ) ?_)⟩
  show pderiv ℂ μ (F₁ 0 0) = (-Complex.I) • (ω μ).toU1Value * F₁ 0 0
  simpa [Matrix.mul_apply] using congrArg (fun M => M (0 : Fin 1) (0 : Fin 1)) (hF₁ μ)

/-!

## The symmeterized Maurer–Cartan form

-/


noncomputable def symmetrizedMaurerCartanForm (U : JetGaugeGroupI)
    (r :  Multiset (Fin 1 ⊕ Fin 3)) : JetGaugeAlgebra :=
  ((1/(r.card : ℝ) : ℝ) • (r.map fun μ =>
    (iteratedDeriv (r - {μ}) (maurerCartanForm U μ))).sum)

@[simp]
lemma symmetrizedMaurerCartanForm_apply_zero (U : JetGaugeGroupI) :
    symmetrizedMaurerCartanForm U 0 = 0 := by
  simp [symmetrizedMaurerCartanForm]

@[simp]
lemma symmetrizedMaurerCartanForm_one :
    symmetrizedMaurerCartanForm (1 : JetGaugeGroupI) = 0 := by
  ext <;> simp [symmetrizedMaurerCartanForm]

@[simp]
lemma symmetrizedMaurerCartanForm_ofConstant (U₀ : GaugeGroupI) :
    symmetrizedMaurerCartanForm (JetGaugeGroupI.ofConstant U₀) = 0 := by
  ext <;> simp [symmetrizedMaurerCartanForm, maurerCartanForm_ofConstant]

@[simp]
lemma symmetrizedMaurerCartanForm_singleton (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    symmetrizedMaurerCartanForm U {μ} = (maurerCartanForm U μ) := by
  simp [symmetrizedMaurerCartanForm, iteratedDeriv_zero]

/-- The recursion for the symmetrized Maurer–Cartan form: peeling one direction off the
  multiset. -/
lemma symmetrizedMaurerCartanForm_cons (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3)
    (r : Multiset (Fin 1 ⊕ Fin 3)) : symmetrizedMaurerCartanForm U (μ ::ₘ r) =
    (1/(r.card + 1 : ℝ) : ℝ) • (iteratedDeriv r (maurerCartanForm U μ))
    + ((r.card : ℝ)/(r.card + 1 : ℝ)) • deriv μ (symmetrizedMaurerCartanForm U r) := by
  by_cases hr : r = 0
  · subst hr
    simp
  · have hn : (r.card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr fun h => hr (Multiset.card_eq_zero.mp h)
    have herase : ∀ ν ∈ r, (μ ::ₘ r).erase ν = μ ::ₘ r.erase ν := by
      intro ν hν
      rcases eq_or_ne ν μ with rfl | h
      · rw [Multiset.erase_cons_head, Multiset.cons_erase hν]
      · rw [Multiset.erase_cons_tail _ h.symm]
    rw [symmetrizedMaurerCartanForm, symmetrizedMaurerCartanForm, Multiset.map_cons,
      Multiset.sum_cons, Multiset.card_cons, Multiset.sub_singleton, Multiset.erase_cons_head,
      Multiset.map_congr rfl fun ν hν => by
        rw [Multiset.sub_singleton, herase ν hν, iteratedDeriv_cons, LinearMap.comp_apply,
          ← Multiset.sub_singleton],
      show (r.map fun ν => deriv μ (iteratedDeriv (r - {ν}) (maurerCartanForm U ν))) =
          (r.map fun ν => iteratedDeriv (r - {ν}) (maurerCartanForm U ν)).map (deriv μ) from
        (Multiset.map_map _ _ _).symm,
      ← map_multiset_sum, smul_add, map_smul, smul_smul,
      show ((r.card + 1 : ℕ) : ℝ) = (r.card : ℝ) + 1 by push_cast; ring,
      show (r.card : ℝ)/((r.card : ℝ) + 1) * (1/(r.card : ℝ)) = 1/((r.card : ℝ) + 1) by
        field_simp]

/-!

## Determination of the Maurer–Cartan form by its symmetrized coefficients

-/


/-- The symmetrization defect of the Maurer–Cartan form: an iterated derivative of
  `ω` is the corresponding symmetrized form plus an average of iterated derivatives
  of brackets of `ω` in strictly fewer directions. This is the jet-level form of the
  outline's span statement, with the structure equation already substituted. -/
lemma iteratedDeriv_maurerCartanForm_eq_symmetrized_add (U : JetGaugeGroupI)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    iteratedDeriv s (maurerCartanForm U μ) =
      symmetrizedMaurerCartanForm U (μ ::ₘ s) +
      (1/(s.card + 1 : ℝ)) • (s.map fun ν =>
        iteratedDeriv (s.erase ν) ⁅maurerCartanForm U μ, maurerCartanForm U ν⁆).sum := by
  -- each bracket term is a difference of two iterated derivatives of `ω`
  have hswap : ∀ ν ∈ s,
      iteratedDeriv (s.erase ν) ⁅maurerCartanForm U μ, maurerCartanForm U ν⁆ =
        iteratedDeriv s (maurerCartanForm U μ) -
          iteratedDeriv (μ ::ₘ s.erase ν) (maurerCartanForm U ν) := by
    intro ν hν
    have hb : ⁅maurerCartanForm U μ, maurerCartanForm U ν⁆ =
        deriv ν (maurerCartanForm U μ) - deriv μ (maurerCartanForm U ν) := by
      have h1 : deriv μ (maurerCartanForm U ν) - deriv ν (maurerCartanForm U μ) =
          -⁅maurerCartanForm U μ, maurerCartanForm U ν⁆ :=
        eq_neg_of_add_eq_zero_left (maurerCartanForm_structure U μ ν)
      rw [← neg_sub, h1, neg_neg]
    rw [hb, map_sub]
    congr 1
    · conv_rhs => rw [← Multiset.cons_erase hν]
      rw [show (ν ::ₘ s.erase ν : Multiset (Fin 1 ⊕ Fin 3)) = s.erase ν + {ν} from by
          rw [add_comm, Multiset.singleton_add],
        iteratedDeriv_add, LinearMap.comp_apply, iteratedDeriv_singleton]
    · rw [show (μ ::ₘ s.erase ν : Multiset (Fin 1 ⊕ Fin 3)) = s.erase ν + {μ} from by
          rw [add_comm, Multiset.singleton_add],
        iteratedDeriv_add, LinearMap.comp_apply, iteratedDeriv_singleton]
  have herase : ∀ ν ∈ s, (μ ::ₘ s).erase ν = μ ::ₘ s.erase ν := by
    intro ν hν
    rcases eq_or_ne ν μ with rfl | hne
    · rw [Multiset.erase_cons_head, Multiset.cons_erase hν]
    · rw [Multiset.erase_cons_tail _ hne.symm]
  rw [symmetrizedMaurerCartanForm, Multiset.map_cons, Multiset.sum_cons,
    Multiset.card_cons, Multiset.sub_singleton, Multiset.erase_cons_head,
    Multiset.map_congr rfl fun ν hν => by rw [Multiset.sub_singleton, herase ν hν],
    Multiset.map_congr rfl hswap, Multiset.sum_map_sub, Multiset.map_const',
    Multiset.sum_replicate, ← Nat.cast_smul_eq_nsmul ℝ]
  push_cast
  match_scalars <;> field_simp <;> ring


/-- The `su(3)`-entry of the evaluated symmetrized Maurer–Cartan form, as a sum of
  base-point values of iterated derivatives of the Maurer–Cartan form entries. -/
lemma eval_symmetrizedMaurerCartanForm_toSU3_apply (U : JetGaugeGroupI)
    (r : Multiset (Fin 1 ⊕ Fin 3)) (i j : Fin 3) :
    (eval (symmetrizedMaurerCartanForm U r)).toSU3Matrix i j =
      (1/(r.card : ℝ)) • (r.map fun μ => constantCoeff ((r.erase μ).foldl
        (fun f ρ => pderiv ℂ ρ f) ((maurerCartanForm U μ).toSU3Matrix i j))).sum := by
  set Φ : JetGaugeAlgebra →+ ℂ := AddMonoidHom.mk'
    (fun a => (eval a).toSU3Matrix i j)
    (fun a b => by simp [map_add, GaugeAlgebra.add_toSU3Matrix]) with hΦ
  have hΦiter : ∀ μ ∈ r, Φ (iteratedDeriv (r - {μ}) (maurerCartanForm U μ)) =
      constantCoeff ((r.erase μ).foldl (fun f ρ => pderiv ℂ ρ f)
        ((maurerCartanForm U μ).toSU3Matrix i j)) := by
    intro μ hμ
    show (eval (iteratedDeriv (r - {μ}) (maurerCartanForm U μ))).toSU3Matrix i j = _
    rw [eval_toSU3Matrix_apply, iteratedDeriv_toSU3Matrix, Matrix.map_apply,
      Multiset.sub_singleton]
  rw [symmetrizedMaurerCartanForm, map_smul, GaugeAlgebra.smul_toSU3Matrix,
    Matrix.smul_apply]
  congr 1
  rw [show (eval ((r.map fun μ =>
        iteratedDeriv (r - {μ}) (maurerCartanForm U μ)).sum)).toSU3Matrix i j
      = Φ ((r.map fun μ => iteratedDeriv (r - {μ}) (maurerCartanForm U μ)).sum) from rfl,
    map_multiset_sum, Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun μ hμ => hΦiter μ hμ)

/-- The `su(2)`-entry of the evaluated symmetrized Maurer–Cartan form. -/
lemma eval_symmetrizedMaurerCartanForm_toSU2_apply (U : JetGaugeGroupI)
    (r : Multiset (Fin 1 ⊕ Fin 3)) (i j : Fin 2) :
    (eval (symmetrizedMaurerCartanForm U r)).toSU2Matrix i j =
      (1/(r.card : ℝ)) • (r.map fun μ => constantCoeff ((r.erase μ).foldl
        (fun f ρ => pderiv ℂ ρ f) ((maurerCartanForm U μ).toSU2Matrix i j))).sum := by
  set Φ : JetGaugeAlgebra →+ ℂ := AddMonoidHom.mk'
    (fun a => (eval a).toSU2Matrix i j)
    (fun a b => by simp [map_add, GaugeAlgebra.add_toSU2Matrix]) with hΦ
  have hΦiter : ∀ μ ∈ r, Φ (iteratedDeriv (r - {μ}) (maurerCartanForm U μ)) =
      constantCoeff ((r.erase μ).foldl (fun f ρ => pderiv ℂ ρ f)
        ((maurerCartanForm U μ).toSU2Matrix i j)) := by
    intro μ hμ
    show (eval (iteratedDeriv (r - {μ}) (maurerCartanForm U μ))).toSU2Matrix i j = _
    rw [eval_toSU2Matrix_apply, iteratedDeriv_toSU2Matrix, Matrix.map_apply,
      Multiset.sub_singleton]
  rw [symmetrizedMaurerCartanForm, map_smul, GaugeAlgebra.smul_toSU2Matrix,
    Matrix.smul_apply]
  congr 1
  rw [show (eval ((r.map fun μ =>
        iteratedDeriv (r - {μ}) (maurerCartanForm U μ)).sum)).toSU2Matrix i j
      = Φ ((r.map fun μ => iteratedDeriv (r - {μ}) (maurerCartanForm U μ)).sum) from rfl,
    map_multiset_sum, Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun μ hμ => hΦiter μ hμ)

/-- The `u(1)`-value of the evaluated symmetrized Maurer–Cartan form. -/
lemma eval_symmetrizedMaurerCartanForm_toU1Value (U : JetGaugeGroupI)
    (r : Multiset (Fin 1 ⊕ Fin 3)) :
    (eval (symmetrizedMaurerCartanForm U r)).toU1Value =
      (1/(r.card : ℝ)) • (r.map fun μ => constantCoeff ((r.erase μ).foldl
        (fun f ρ => pderiv ℂ ρ f) ((maurerCartanForm U μ).toU1Value))).sum := by
  set Φ : JetGaugeAlgebra →+ ℂ := AddMonoidHom.mk'
    (fun a => (eval a).toU1Value)
    (fun a b => by simp [map_add, GaugeAlgebra.add_toU1Value]) with hΦ
  have hΦiter : ∀ μ ∈ r, Φ (iteratedDeriv (r - {μ}) (maurerCartanForm U μ)) =
      constantCoeff ((r.erase μ).foldl (fun f ρ => pderiv ℂ ρ f)
        ((maurerCartanForm U μ).toU1Value)) := by
    intro μ hμ
    show (eval (iteratedDeriv (r - {μ}) (maurerCartanForm U μ))).toU1Value = _
    rw [eval_toU1Value_eq, iteratedDeriv_toU1Value, Multiset.sub_singleton]
  rw [symmetrizedMaurerCartanForm, map_smul, GaugeAlgebra.smul_toU1Value]
  congr 1
  rw [show (eval ((r.map fun μ =>
        iteratedDeriv (r - {μ}) (maurerCartanForm U μ)).sum)).toU1Value
      = Φ ((r.map fun μ => iteratedDeriv (r - {μ}) (maurerCartanForm U μ)).sum) from rfl,
    map_multiset_sum, Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun μ hμ => hΦiter μ hμ)
/-- Determination step: if the base-point symmetrized Maurer–Cartan data of `U` and
  `V` agree, and their Maurer–Cartan Taylor data agree in fewer than `n` directions,
  then they agree in `n` directions. -/
lemma eval_iteratedDeriv_maurerCartanForm_eq_of_symmetrized_eq (U V : JetGaugeGroupI) (n : ℕ)
    (hsym : ∀ r, eval (symmetrizedMaurerCartanForm U r) =
      eval (symmetrizedMaurerCartanForm V r))
    (ih : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), s.card < n →
      eval (iteratedDeriv s (maurerCartanForm U μ)) =
        eval (iteratedDeriv s (maurerCartanForm V μ)))
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (hs : s.card = n) :
    eval (iteratedDeriv s (maurerCartanForm U μ)) =
      eval (iteratedDeriv s (maurerCartanForm V μ)) := by
  rw [iteratedDeriv_maurerCartanForm_eq_symmetrized_add U s μ,
    iteratedDeriv_maurerCartanForm_eq_symmetrized_add V s μ,
    map_add, map_add, map_smul, map_smul, hsym]
  refine congrArg (fun z => eval (symmetrizedMaurerCartanForm V (μ ::ₘ s)) +
    (1/(s.card + 1 : ℝ)) • z) ?_
  rw [map_multiset_sum, map_multiset_sum, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun ν hν => ?_)
  have hlt : ∀ p : Multiset (Fin 1 ⊕ Fin 3), p ≤ s.erase ν → p.card < n := by
    intro p hp
    have h1 := Multiset.card_le_card hp
    have h2 := Multiset.card_erase_add_one hν
    omega
  exact eval_iteratedDeriv_bracket_congr (s.erase ν) _ _ _ _
    (fun p hp => ih p μ (hlt p hp)) (fun p hp => ih p ν (hlt p hp))

/-!

## The derivative of the adjoint action

-/

/-- The constant inclusion has vanishing formal derivative: constants have no
  spacetime dependence. -/
@[simp]
lemma JetGaugeAlgebra.deriv_ofConstant (μ : Fin 1 ⊕ Fin 3) (a : GaugeAlgebra) :
    deriv μ (ofConstant a) = 0 := by
  ext <;> simp [Matrix.map_apply, pderiv_C]

/-- The formal derivative intertwines the adjoint action through the Maurer–Cartan
  form: `∂_μ (Ad_U x) = Ad_U (∂_μ x) − ⁅ω_μ(U), Ad_U x⁆`. On the matrix factors this
  is the Leibniz rule with the derivative of `U†` rewritten through the
  differentiated unitarity relation; on the abelian `u(1)` factor the adjoint action
  is trivial and the bracket is absent. -/
lemma deriv_adjointMap (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) (x : JetGaugeAlgebra) :
    deriv μ (adjointMap U x) =
      adjointMap U (deriv μ x) - ⁅maurerCartanForm U μ, adjointMap U x⁆ := by
  have hleib : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (M N : Matrix κ κ JetRing),
      (M * N).map (pderiv ℂ μ) = M.map (pderiv ℂ μ) * N + M * N.map (pderiv ℂ μ) := by
    intro κ _ _ M N
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
      Derivation.leibniz, smul_eq_mul]
    exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
  have key : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (V X : Matrix κ κ JetRing),
      V * star V = 1 →
      (V * X * star V).map (pderiv ℂ μ) =
        V * X.map (pderiv ℂ μ) * star V -
        Complex.I • (Complex.I • (V.map (pderiv ℂ μ) * star V) * (V * X * star V) -
          (V * X * star V) * (Complex.I • (V.map (pderiv ℂ μ) * star V))) := by
    intro κ _ _ V X hV
    have hVV : star V * V = 1 := mul_eq_one_comm.mp hV
    have hq : (star V).map (pderiv ℂ μ) = -(star V * V.map (pderiv ℂ μ) * star V) := by
      have h1 : V * (star V).map (pderiv ℂ μ) = -(V.map (pderiv ℂ μ) * star V) :=
        eq_neg_of_add_eq_zero_right (by
          rw [← hleib _ V (star V), hV]
          exact Matrix.ext fun i j => by
            simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ℂ μ)])
      calc (star V).map (pderiv ℂ μ)
          = star V * V * (star V).map (pderiv ℂ μ) := by rw [hVV, one_mul]
        _ = -(star V * V.map (pderiv ℂ μ) * star V) := by
            rw [mul_assoc, h1, mul_neg, ← mul_assoc]
    rw [hleib _ (V * X) (star V), hleib _ V X, hq]
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, smul_smul, Complex.I_mul_I,
      neg_one_smul, sub_neg_eq_add, add_mul, mul_neg, ← mul_assoc]
    rw [mul_assoc (V.map (pderiv ℂ μ)) (star V) V, hVV, mul_one]
    abel
  refine ext_of_matrix ?_ ?_ ?_
  · simpa only [deriv_toSU3Matrix, adjointMap_toSU3Matrix, sub_toSU3Matrix,
      bracket_toSU3Matrix, maurerCartanForm_toSU3Matrix] using
      key _ U.1.1 x.toSU3Matrix (Matrix.mem_unitaryGroup_iff.mp
        (Matrix.mem_specialUnitaryGroup_iff.mp U.1.2).1)
  · simpa only [deriv_toSU2Matrix, adjointMap_toSU2Matrix, sub_toSU2Matrix,
      bracket_toSU2Matrix, maurerCartanForm_toSU2Matrix] using
      key _ U.2.1.1 x.toSU2Matrix (Matrix.mem_unitaryGroup_iff.mp
        (Matrix.mem_specialUnitaryGroup_iff.mp U.2.1.2).1)
  · simp

end StandardModel
